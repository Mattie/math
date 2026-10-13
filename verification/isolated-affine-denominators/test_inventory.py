"""Inventory checks distinguish structured name collisions and target body gaps."""
import json
from pathlib import Path
import tempfile
import unittest
import inventory_export


class InventoryTests(unittest.TestCase):
    def test_structured_axioms_and_body_coverage(self):
        records = [
            {'in': 1, 'str': {'pre': 0, 'str': 'propext'}},
            {'in': 2, 'str': {'pre': 0, 'str': 'Quot'}},
            {'in': 3, 'str': {'pre': 2, 'str': 'sound'}},
            {'in': 4, 'str': {'pre': 0, 'str': 'Classical'}},
            {'in': 5, 'str': {'pre': 4, 'str': 'choice'}},
            {'in': 6, 'str': {'pre': 0, 'str': 'target'}},
            *({'axiom': {'name': n, 'type': 0}} for n in [1, 3, 5]),
            {'thm': {'name': 6, 'type': 0, 'value': 1}},
        ]
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'fixture.ndjson'

            def write():
                path.write_text(''.join(json.dumps(r) + '\n' for r in records))

            write()
            self.assertEqual(inventory_export.inspect(path, ['target'])['status'], 'passed')
            records[2] = {'in': 3, 'str': {'pre': 0, 'str': 'Quot.sound'}}
            write()
            with self.assertRaisesRegex(RuntimeError, 'structured axiom'):
                inventory_export.inspect(path, ['target'])
            records[2] = {'in': 3, 'str': {'pre': 2, 'str': 'sound'}}
            records[-1]['thm'].pop('value')
            write()
            with self.assertRaisesRegex(RuntimeError, 'no theorem body'):
                inventory_export.inspect(path, ['target'])


if __name__ == '__main__':
    unittest.main()
