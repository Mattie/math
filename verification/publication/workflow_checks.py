"""Test-only checks for the active shared dispatcher's runtime safeguards."""

import re

import yaml


class _UniqueKeyLoader(yaml.BaseLoader):
    """Preserve YAML scalars as strings and reject ambiguous mapping keys."""

    def construct_mapping(self, node, deep=False):
        mapping = {}
        for key_node, value_node in node.value:
            key = self.construct_scalar(key_node)
            if key in mapping:
                raise AssertionError(f"Duplicate workflow key: {key}")
            mapping[key] = self.construct_object(value_node, deep=deep)
        return mapping


def assert_dispatcher_guards(workflow_text, case):
    """Require this case's full budget and unconditional evidence indexing.

    Parse YAML without constructing Python objects or evaluating expressions.
    Raise AssertionError for missing, ambiguous, or unsupported active settings;
    comments and strings in unrelated fields cannot satisfy these checks.
    """
    try:
        document = yaml.load(workflow_text, Loader=_UniqueKeyLoader)
        job = document['jobs']['verify']
        timeout = job['timeout-minutes']
        steps = job['steps']
    except (yaml.YAMLError, KeyError, TypeError) as error:
        raise AssertionError("Missing or invalid jobs.verify workflow settings") from error
    if not isinstance(steps, list):
        raise AssertionError("jobs.verify.steps must be a sequence")
    evidence = [step for step in steps if isinstance(step, dict) and
                step.get('name') == 'Index exact evidence after the verifier exits']
    if len(evidence) != 1:
        raise AssertionError("Expected exactly one evidence-index step in jobs.verify")

    # Match the complete, restricted case-list expressions; never execute them.
    comparison = r"inputs\.case\s*==\s*'[a-z-]+'"
    selected = rf"inputs\.case\s*==\s*'{re.escape(case)}'"
    condition = (rf"\(\s*(?:{comparison}\s*\|\|\s*)*{selected}"
                 rf"(?:\s*\|\|\s*{comparison})*\s*\)")
    budget = rf"\$\{{\{{\s*{condition}\s*&&\s*360\s*\|\|\s*240\s*\}}\}}"
    if not isinstance(timeout, str) or not re.fullmatch(budget, timeout.strip()):
        raise AssertionError(f"jobs.verify must give {case} a 360-minute budget")
    index_if = evidence[0].get('if')
    always = rf"always\(\)\s*&&\s*{condition}"
    if not isinstance(index_if, str) or not re.fullmatch(always, index_if.strip()):
        raise AssertionError(f"Evidence indexing must use always() for {case}")
