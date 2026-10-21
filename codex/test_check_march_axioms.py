#!/usr/bin/env python3
"""Regression tests for the acceptance gate; no Lean build needed."""
import unittest
from check_march_axioms import check

SOURCE = "#print axioms A.first\n#print axioms second\n"
LOG = "'A.first' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'B.second' depends on axioms: [propext, Classical.choice, Quot.sound]\n"


class GateTests(unittest.TestCase):
    def test_accepts_wrapped_output_and_namespace_resolution(self):
        self.assertEqual(check(SOURCE, LOG), 2)

    def test_rejects_bad_evidence(self):
        bad_logs = ["", LOG.split("'B.second'")[0], LOG + LOG,
                    LOG.replace("Quot.sound", "sorryAx"),
                    LOG.replace("Quot.sound", "inventedAxiom"),
                    LOG.replace("Quot.sound", "Classical.choice"),
                    LOG.replace("B.second", "B.wrong"),
                    LOG.replace("Quot.sound]", "Quot.sound"),
                    LOG.replace("propext,", ""),
                    LOG + "'extra' depends on axioms: [sorryAx]\n"]
        for log in bad_logs:
            with self.subTest(log=log), self.assertRaises(ValueError):
                check(SOURCE, log)

    def test_requires_source_prints(self):
        with self.assertRaises(ValueError):
            check("", "")


if __name__ == "__main__":
    unittest.main()
