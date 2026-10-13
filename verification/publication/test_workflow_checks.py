"""Regression examples for active dispatcher settings, without a proof run."""

from copy import deepcopy
from pathlib import Path
import unittest

import yaml

from workflow_checks import assert_dispatcher_guards


WORKFLOW = Path(__file__).resolve().parents[2] / '.github/workflows/isolated-irrationality.yml'
CASES = ('affine-cubic', 'affine-denominators')
INDEX_NAME = 'Index exact evidence after the verifier exits'


class WorkflowGuardTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text(encoding='utf-8')
        self.document = yaml.load(self.text, Loader=yaml.BaseLoader)
        self.job = self.document['jobs']['verify']
        self.evidence = next(step for step in self.job['steps'] if step.get('name') == INDEX_NAME)

    def check_cases(self, text, accepted):
        """Exercise the same example for both callers of the shared helper."""
        for case in CASES:
            with self.subTest(case=case):
                if accepted:
                    assert_dispatcher_guards(text, case)
                else:
                    with self.assertRaises(AssertionError):
                        assert_dispatcher_guards(text, case)

    def reject_document(self):
        """Serialize a deliberately broken workflow and require rejection."""
        self.check_cases(yaml.safe_dump(self.document), accepted=False)

    def test_current_workflow_and_harmless_comments(self):
        self.check_cases(self.text, accepted=True)
        self.check_cases('# timeout-minutes: 240\n# if: false\n' + self.text, accepted=True)

    def test_case_order_and_additional_cases(self):
        for cases in (CASES, tuple(reversed(CASES)), ('extra-before', *CASES, 'extra-after')):
            with self.subTest(cases=cases):
                condition = '(' + ' || '.join(f"inputs.case == '{case}'" for case in cases) + ')'
                self.job['timeout-minutes'] = '${{ ' + condition + ' && 360 || 240 }}'
                self.evidence['if'] = 'always() && ' + condition
                self.check_cases(yaml.safe_dump(self.document), accepted=True)

    def test_reduced_timeout_cannot_be_hidden_by_comment(self):
        old = next(line for line in self.text.splitlines() if 'timeout-minutes:' in line)
        text = self.text.replace(old, '    timeout-minutes: 240') + '\n# ' + old + '\n'
        self.check_cases(text, accepted=False)

    def test_disabled_evidence_cannot_be_hidden_by_comment(self):
        old = next(line for line in self.text.splitlines() if 'if: always() &&' in line)
        text = self.text.replace(old, '        if: false') + '\n# ' + old + '\n'
        self.check_cases(text, accepted=False)

    def test_correct_settings_in_another_job_do_not_count(self):
        self.document['jobs']['unrelated'] = deepcopy(self.job)
        self.job['timeout-minutes'] = '240'
        self.evidence['if'] = 'false'
        self.reject_document()

    def test_correct_condition_in_another_step_does_not_count(self):
        unrelated = deepcopy(self.evidence)
        unrelated['name'] = 'Unrelated step'
        self.job['steps'].append(unrelated)
        self.evidence['if'] = 'false'
        self.reject_document()

    def test_correct_settings_in_script_text_do_not_count(self):
        self.job['steps'].append({'name': 'Print old settings', 'run':
            'timeout-minutes: ' + self.job['timeout-minutes'] + '\nif: ' + self.evidence['if']})
        self.job['timeout-minutes'] = '240'
        self.evidence['if'] = 'false'
        self.reject_document()

    def test_missing_and_duplicate_evidence_steps(self):
        self.job['steps'].remove(self.evidence)
        self.reject_document()
        self.job['steps'].extend([self.evidence, deepcopy(self.evidence)])
        self.reject_document()

    def test_missing_required_fields(self):
        for field in ('timeout-minutes', 'steps'):
            with self.subTest(field=field):
                value = self.job.pop(field)
                self.reject_document()
                self.job[field] = value
        self.evidence.pop('if')
        self.reject_document()

    def test_duplicate_active_yaml_keys(self):
        old = next(line for line in self.text.splitlines() if 'timeout-minutes:' in line)
        self.check_cases(self.text.replace(old, '    timeout-minutes: 240\n' + old), accepted=False)
        self.check_cases(self.text.replace('jobs:\n', 'jobs: {}\njobs:\n'), accepted=False)

    def test_complete_expression_required(self):
        self.evidence['if'] += ' && false'
        self.reject_document()

    def test_selected_case_must_be_in_both_conditions(self):
        for field, container in (('timeout-minutes', self.job), ('if', self.evidence)):
            old = container[field]
            for case in CASES:
                with self.subTest(field=field, case=case):
                    container[field] = old.replace(f"'{case}'", "'unrelated'")
                    with self.assertRaises(AssertionError):
                        assert_dispatcher_guards(yaml.safe_dump(self.document), case)
            container[field] = old

    def test_invalid_workflow_shape(self):
        for text in ('jobs: [', 'null', 'jobs: {}', 'jobs: {verify: {steps: {}, timeout-minutes: 360}}'):
            with self.subTest(text=text):
                self.check_cases(text, accepted=False)


if __name__ == '__main__':
    unittest.main()
