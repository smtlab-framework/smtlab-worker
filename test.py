#!/usr/bin/env python3

import unittest

from worker.main import getSMTLibData, removeCommandsFromSMTLibData, smtLibDataToString
from antlr4 import InputStream

class TestSMTTransform(unittest.TestCase):
    def remove_commands(self, input_str, commands):
        smt_data = getSMTLibData(input_str, InputStream)
        filtered_data = removeCommandsFromSMTLibData(smt_data, commands)
        flattened_data = smtLibDataToString(filtered_data)
        return flattened_data
    
    def test_remove_commands_single_expr(self):
        output = self.remove_commands("(set-logic QF_S)", ['set-logic'])
        self.assertFalse("set-logic" in output)

    def test_remove_commands_two_exprs(self):
        output = self.remove_commands("(set-logic QF_S) (set-info :status sat) (check-sat)", ["set-logic", "set-info"])
        self.assertFalse("set-logic" in output)
        self.assertFalse("set-info" in output)
        self.assertTrue("check-sat" in output)

    def test_remove_commands_no_match(self):
        output = self.remove_commands("(set-logic QF_S) (declare-const X String) (check-sat)", ["set-info"])
        self.assertFalse("set-info" in output)
        self.assertTrue("set-logic" in output)
        self.assertTrue("declare-const" in output)
        self.assertTrue("check-sat" in output)

    def test_remove_commands_multiple_occurrences(self):
        output = self.remove_commands("(set-logic QF_S) (declare-const X String) (declare-const Y String) (check-sat)", ["declare-const"])
        self.assertFalse("declare-const" in output)
        self.assertTrue("set-logic" in output)
        self.assertTrue("check-sat" in output)

if __name__ == '__main__':
    unittest.main()
