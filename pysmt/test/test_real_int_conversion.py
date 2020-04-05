#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL
from pysmt.test import TestCase, main
from pysmt.logics import QF_NIRA
from pysmt.constants import Fraction

class TestRealIntConv(TestCase):

    def test_realtoint(self):
        b = Symbol('b', INT)

        check = Equals(RealToInt(Real(Fraction(3, 2))), Int(1))
        check = And(check,
                    Equals(RealToInt(Real(Fraction(-3, 2))), Int(-2)))
        check = And(check,
                    Equals(RealToInt(Real(1)), Int(1)))
        check = And(check,
                    Equals(RealToInt(ToReal(b)), b))
        for sname in get_env().factory.all_solvers(logic=QF_NIRA):
            self.assertValid(check, solver_name=sname, logic=QF_NIRA)

    def test_ceiling(self):
        check = Equals(Ceiling(Real(Fraction(3, 2))), Int(2))
        check = And(check,
                    Equals(Ceiling(Real(Fraction(-3, 2))), Int(-1)))
        check = And(check,
                    Equals(Ceiling(Real(1)), Int(1)))
        for sname in get_env().factory.all_solvers(logic=QF_NIRA):
            self.assertValid(check, solver_name=sname, logic=QF_NIRA)

    def test_truncate(self):
        check = Equals(Truncate(Real(Fraction(3, 2))), Int(1))
        check = And(check,
                    Equals(Truncate(Real(Fraction(-3, 2))), Int(-1)))
        check = And(check,
                    Equals(Truncate(Real(1)), Int(1)))
        for sname in get_env().factory.all_solvers(logic=QF_NIRA):
            self.assertValid(check, solver_name=sname, logic=QF_NIRA)

if __name__ == '__main__':
    main()
