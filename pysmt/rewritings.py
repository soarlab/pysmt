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
"""
This module defines some rewritings for pySMT formulae.
"""
from itertools import combinations

from pysmt.walkers import DagWalker, IdentityDagWalker, handles
import pysmt.typing as types
import pysmt.operators as op


class CNFizer(DagWalker):

    THEORY_PLACEHOLDER = "__Placeholder__"

    TRUE_CNF = frozenset()
    FALSE_CNF = frozenset([frozenset()])

    def __init__(self, environment=None):
        DagWalker.__init__(self, environment)

        self.mgr = self.env.formula_manager
        self._introduced_variables = {}
        self._cnf_pieces = {}

    def _key_var(self, formula):
        if formula in self._introduced_variables:
            res = self._introduced_variables[formula]
        else:
            res = self.mgr.FreshSymbol()
            self._introduced_variables[formula] = res
        return res

    def convert(self, formula):
        """Convert formula into an Equisatisfiable CNF.

        Returns a set of clauses: a set of set of literals.
        """
        tl, _cnf = self.walk(formula)
        res = [frozenset([tl])]
        for clause in _cnf:
            if len(clause) == 0:
                return CNFizer.FALSE_CNF
            simp = []
            for lit in clause:
                if lit.is_true():
                    # Prune clauses that are trivially TRUE
                    simp = None
                    break
                elif not lit.is_false():
                    # Prune FALSE literals
                    simp.append(lit)
            if simp:
                res.append(frozenset(simp))
        return frozenset(res)

    def convert_as_formula(self, formula):
        """Convert formula into an Equisatisfiable CNF.

        Returns an FNode.
        """
        lsts = self.convert(formula)

        conj = []
        for clause in lsts:
            conj.append(self.mgr.Or(clause))
        return self.mgr.And(conj)

    def serialize(self, _cnf):
        clauses = []
        for clause in _cnf:
            clauses +=[" { " + " ".join(str(lit) for lit in clause) + "} "]
        res = ["{"] + clauses + ["}"]
        return "".join(res)

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        raise NotImplementedError("CNFizer does not support quantifiers")

    def walk_and(self, formula, args, **kwargs):
        if len(args) == 1:
            return args[0]

        k = self._key_var(formula)
        _cnf = [frozenset([k] + [self.mgr.Not(a).simplify() for a,_ in args])]
        for a,c in args:
            _cnf.append(frozenset([a, self.mgr.Not(k)]))
            for clause in c:
                _cnf.append(clause)
        return k, frozenset(_cnf)

    def walk_or(self, formula, args, **kwargs):
        if len(args) == 1:
            return args[0]
        k = self._key_var(formula)
        _cnf = [frozenset([self.mgr.Not(k)] + [a for a,_ in args])]
        for a,c in args:
            _cnf.append(frozenset([k, self.mgr.Not(a)]))
            for clause in c:
                _cnf.append(clause)
        return k, frozenset(_cnf)

    def walk_not(self, formula, args, **kwargs):
        a, _cnf = args[0]
        if a.is_true():
            return self.mgr.FALSE(), CNFizer.TRUE_CNF
        elif a.is_false():
            return self.mgr.TRUE(), CNFizer.TRUE_CNF
        else:
            k = self._key_var(formula)
            return k, _cnf | frozenset([frozenset([self.mgr.Not(k),
                                                  self.mgr.Not(a).simplify()]),
                                       frozenset([k, a])])

    def walk_implies(self, formula,  args, **kwargs):
        a, cnf_a = args[0]
        b, cnf_b = args[1]

        k = self._key_var(formula)
        not_a = self.mgr.Not(a).simplify()
        not_b = self.mgr.Not(b).simplify()
        not_k = self.mgr.Not(k)

        return k, (cnf_a | cnf_b | frozenset([frozenset([not_a, b, not_k]),
                                              frozenset([a, k]),
                                              frozenset([not_b, k])]))

    def walk_iff(self, formula, args, **kwargs):
        a, cnf_a = args[0]
        b, cnf_b = args[1]

        k = self._key_var(formula)
        not_a = self.mgr.Not(a).simplify()
        not_b = self.mgr.Not(b).simplify()
        not_k = self.mgr.Not(k)

        return k, (cnf_a | cnf_b | frozenset([frozenset([not_a, not_b, k]),
                                              frozenset([not_a, b, not_k]),
                                              frozenset([a, not_b, not_k]),
                                              frozenset([a, b, k])]))

    def walk_symbol(self, formula, **kwargs):
        if formula.is_symbol(types.BOOL):
            return formula, CNFizer.TRUE_CNF
        else:
            return CNFizer.THEORY_PLACEHOLDER

    def walk_function(self, formula, **kwargs):
        ty = formula.function_symbol().symbol_type()
        if ty.return_type.is_bool_type():
            return formula, CNFizer.TRUE_CNF
        else:
            return CNFizer.THEORY_PLACEHOLDER

    def walk_ite(self, formula, args, **kwargs):
        if any(a == CNFizer.THEORY_PLACEHOLDER for a in args):
            return CNFizer.THEORY_PLACEHOLDER
        else:
            (i,cnf_i),(t,cnf_t),(e,cnf_e) = args
            k = self._key_var(formula)
            not_i = self.mgr.Not(i).simplify()
            not_t = self.mgr.Not(t).simplify()
            not_e = self.mgr.Not(e).simplify()
            not_k = self.mgr.Not(k)

            return k, (cnf_i | cnf_t | cnf_e |
                       frozenset([frozenset([not_i, not_t, k]),
                                  frozenset([not_i, t, not_k]),
                                  frozenset([i, not_e, k]),
                                  frozenset([i, e, not_k])]))

    @handles(op.THEORY_OPERATORS)
    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return CNFizer.THEORY_PLACEHOLDER

    @handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_true():
            return formula, CNFizer.TRUE_CNF
        elif formula.is_false():
            return formula, CNFizer.TRUE_CNF
        else:
            return CNFizer.THEORY_PLACEHOLDER

    @handles(op.RELATIONS)
    def walk_theory_relation(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args)
        return formula, CNFizer.TRUE_CNF

# EOC CNFizer


class NNFizer(DagWalker):
    """Converts a formula into Negation Normal Form.

    The conversion to NNF is handled in 3 steps.

    1. The function _get_children is extended, so that for each
    expression inside a Not, it will return the effect of propagating
    the Not downwards. For example, for Not(And(a, b)), the function
    will return [Not(a), Not(b)].  For expressions that are not inside
    a Not, it is important to return the same type of arguments. See
    for example the case for Iff.

    2. The usual walk_* function is implemented to rebuild the
    expression. This is called only if the subformula was not negated.

    3. walk_not takes care of rebuilding all negated expressions. For
    example, for Not(And(a, b)), walk_not will return
    Or(Not(a), Not(b)). Notice that args in walk_not contains the
    subexpressions returned by _get_children.  In the above example,
    walk_not will be called with args=[Not(a), Not(b)]. Therefore,
    walk_not only need to change the And into a Not.

    """

    def __init__(self, environment=None):
        DagWalker.__init__(self, env=environment)
        self.mgr = self.env.formula_manager

    def convert(self, formula):
        """ Converts the given formula in NNF """
        return self.walk(formula)

    def _get_children(self, formula):
        """Returns the arguments of the node on which an hypotetical recursion
        would be made, possibly negating them.
        """
        mgr = self.mgr
        if formula.is_not():
            s = formula.arg(0)
            if s.is_not():
                return [s.arg(0)]
            elif s.is_and():
                return [mgr.Not(x) for x in s.args()]
            elif s.is_or():
                return [mgr.Not(x) for x in s.args()]
            elif s.is_implies():
                return [s.arg(0), mgr.Not(s.arg(1))]
            elif s.is_iff():
                return [s.arg(0), s.arg(1),
                        mgr.Not(s.arg(0)),
                        mgr.Not(s.arg(1))]
            elif s.is_quantifier():
                return [mgr.Not(s.arg(0))]
            else:
                return [s]

        elif formula.is_implies():
            return [mgr.Not(formula.arg(0)), formula.arg(1)]

        elif formula.is_iff():
            return [formula.arg(0), formula.arg(1),
                    mgr.Not(formula.arg(0)),
                    mgr.Not(formula.arg(1))]

        elif formula.is_and() or formula.is_or() or formula.is_quantifier():
            return formula.args()

        elif formula.is_ite():
            # This must be a boolean ITE as we do not recur within
            # theory atoms
            assert self.env.stc.get_type(formula).is_bool_type()
            i, t, e = formula.args()
            return [i, mgr.Not(i), t, e]

        else:
            assert formula.is_str_op() or \
                formula.is_symbol() or \
                formula.is_function_application() or \
                formula.is_bool_constant() or \
                formula.is_theory_relation(), str(formula)
            return []

    def walk_not(self, formula, args, **kwargs):
        s = formula.arg(0)
        if s.is_symbol():
            return self.mgr.Not(s)
        elif s.is_not():
            return args[0]
        elif s.is_and():
            return self.mgr.Or(args)
        elif s.is_or():
            return self.mgr.And(args)
        elif s.is_implies():
            return self.mgr.And(args)
        elif s.is_iff():
            a, b, na, nb = args
            return self.mgr.Or(self.mgr.And(a, nb),
                          self.mgr.And(b, na))
        elif s.is_forall():
            return self.mgr.Exists(s.quantifier_vars(), args[0])
        elif s.is_exists():
            return self.mgr.ForAll(s.quantifier_vars(), args[0])
        else:
            return self.mgr.Not(args[0])

    def walk_implies(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_iff(self, formula, args, **kwargs):
        a, b, na, nb = args
        return self.mgr.And(self.mgr.Or(na, b),
                       self.mgr.Or(nb, a))

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(args)

    def walk_or(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_ite(self, formula, args, **kwargs):
        # This must be a boolean ITE as we never add theory atoms in the stack
        # See self._get_children()
        assert self.env.stc.get_type(formula).is_bool_type()
        i, ni, t, e = args
        return self.mgr.And(self.mgr.Or(ni, t), self.mgr.Or(i, e))

    def walk_forall(self, formula, args, **kwargs):
        return self.mgr.ForAll(formula.quantifier_vars(), args[0])

    def walk_exists(self, formula, args, **kwargs):
        return self.mgr.Exists(formula.quantifier_vars(), args[0])

    def walk_symbol(self, formula, **kwargs):
        return formula

    def walk_function(self, formula, **kwargs):
        return formula

    @handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return formula

    @handles(op.RELATIONS)
    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return formula

    @handles(op.THEORY_OPERATORS)
    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

# EOC NNFizer


class PrenexNormalizer(DagWalker):
    """
    This class traverses a formula and rebuilds it in prenex normal form.
    """

    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager
        self.check_symbol = self.mgr.FreshSymbol(types.BOOL)

        # The walker returns a pair (L, m) where m is a
        # quantifier-free formula (the matrix) and L is a list of
        # pairs (Q, vars) where Q is either mgr.Exists or mgr.ForAll
        # and vars is a frozenset of variables.  The semantics is that
        # the input formula is equivalent to res computed as follows:
        # res = m
        # for Q, vars in L:
        #    res = Q(vars, res)

    def normalize(self, formula):
        quantifiers, matrix = self.walk(formula)
        res = matrix
        for Q, qvars in quantifiers:
            res = Q(qvars, res)
        return res

    def _invert_quantifier(self, Q):
        if Q == self.mgr.Exists:
            return self.mgr.ForAll
        return self.mgr.Exists

    def walk_symbol(self, formula, **kwargs):
        if formula.symbol_type().is_bool_type():
            return [], formula
        return None # Note: When returning None, we do not pack it into a tuple!

    @handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bool_constant():
            return [],formula
        return None

    @handles(op.AND, op.OR)
    def walk_conj_disj(self, formula, args, **kwargs):
        #pylint: disable=unused-argument

        # Hold the final result
        quantifiers = []
        matrix = []

        # A set of variables that are already reserved in the final
        # matrix. If we find a quantifier over a variable in this set
        # we need to alpha-rename before adding the quantifier to the
        # final list and accumulate the matrix.
        reserved = formula.get_free_variables()

        # We iterate to each argument, each could have a sequence of
        # quantifiers that we need to merge
        for sub_quantifiers, sub_matrix in args:
            # For each quantifier in the alternation
            for Q, q_vars in sub_quantifiers:
                # These are the variables that need alpha-renaming
                needs_rename = q_vars & reserved
                if len(needs_rename) > 0:
                    # we need alpha-renaming: prepare the substitution map
                    sub = dict((v,self.mgr.FreshSymbol(v.symbol_type()))
                               for v in needs_rename)
                    sub_matrix = sub_matrix.substitute(sub)

                    # The new variables for this quantifiers will be
                    # its old variables, minus the one needing
                    # renaming, that are renamed.
                    new_q_vars = (q_vars - needs_rename)
                    new_q_vars |= set(sub[x] for x in needs_rename)
                else:
                    # No need to alpha-rename this quantifier, we keep
                    # as it is the set of variables.
                    new_q_vars = set(q_vars)

                # Store this quantifier in the final result
                quantifiers.append((Q, new_q_vars))

                # The variables of this quantifier from now on are
                # reserved, if another quantifier uses any of them it
                # will need alpha-renaming even if this quantifier was
                # OK.
                reserved |= new_q_vars

            # Store the (possibly rewritten) sub_matrix
            matrix.append(sub_matrix)

        # Build and return the result
        if formula.is_and():
            return (quantifiers, self.mgr.And(matrix))
        if formula.is_or():
            return (quantifiers, self.mgr.Or(matrix))

    def walk_not(self, formula, args, **kwargs):
        quantifiers, matrix = args[0]

        nq = [(self._invert_quantifier(Q), qvars) for Q, qvars in quantifiers]
        return (nq, self.mgr.Not(matrix))

    def walk_iff(self, formula, args, **kwargs):
        a, b = formula.args()
        i1 = self.mgr.Implies(a, b)
        i2 = self.mgr.Implies(b, a)
        i1_args = self.walk_implies(i1, [args[0], args[1]])
        i2_args = self.walk_implies(i2, [args[1], args[0]])
        return self.walk_conj_disj(self.mgr.And(i1, i2), [i1_args, i2_args])

    def walk_implies(self, formula, args, **kwargs):
        a, b = formula.args()
        na = self.mgr.Not(a)
        na_arg = self.walk_not(na, [args[0]])
        return self.walk_conj_disj(self.mgr.Or(na, b), [na_arg, args[1]])

    def walk_ite(self, formula, args, **kwargs):
        if any(a is None for a in args):
            return None
        else:
            i, t, e = formula.args()
            i_args, t_args, e_args = args
            ni = self.mgr.Not(i)
            i1 = self.mgr.Implies(i, t)
            i2 = self.mgr.Implies(ni, e)
            ni_args = self.walk_not(ni, [i_args])
            i1_args = self.walk_implies(i1, [i_args, t_args])
            i2_args = self.walk_implies(i2, [ni_args, e_args])
            return self.walk_conj_disj(self.mgr.And(i1, i2), [i1_args, i2_args])

    def walk_function(self, formula, **kwargs):
        if formula.function_name().symbol_type().return_type.is_bool_type():
            return [], formula
        return None

    @handles(op.RELATIONS)
    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return [], formula

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        quantifiers, matrix = args[0]
        qvars = set(v for _, qv in quantifiers for v in qv)
        nq = set(formula.quantifier_vars()) - qvars

        # If nq is empty, it means that inner quantifiers shadow all
        # the variables of this quantifier. Hence this quantifier can
        # be removed.
        if len(nq) > 0:
            if formula.is_exists():
                return (quantifiers + [(self.mgr.Exists, nq)]), matrix
            else:
                return (quantifiers + [(self.mgr.ForAll, nq)]), matrix
        return quantifiers, matrix

    @handles(op.THEORY_OPERATORS)
    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

# EOC PrenexNormalizer



class AIGer(DagWalker):
    """Converts a formula into an And-Inverted-Graph."""

    def __init__(self, environment=None):
        DagWalker.__init__(self, env=environment)
        self.mgr = self.env.formula_manager

    def convert(self, formula):
        """ Converts the given formula in AIG """
        return self.walk(formula)

    @handles(op.RELATIONS)
    @handles(op.THEORY_OPERATORS)
    @handles(op.CONSTANTS)
    @handles(op.SYMBOL, op.FUNCTION)
    def walk_nop(self, formula, args, **kwargs):
        """We return the Theory subformulae without changes."""
        #pylint: disable=unused-argument
        return formula

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        """Recreate the quantifiers, with the rewritten subformula."""
        #pylint: disable=unused-argument
        if formula.is_exists():
            return self.mgr.Exists(formula.quantifier_vars(),
                                   args[0])
        else:
            assert formula.is_forall()
            return self.mgr.ForAll(formula.quantifier_vars(),
                                   args[0])

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(*args)

    def walk_not(self, formula, args, **kwargs):
        return self.mgr.Not(args[0])

    def walk_or(self, formula, args, **kwargs):
        """ a1 | ... | an = !( !a1 & ... & !an) """
        return self.mgr.Not(self.mgr.And(self.mgr.Not(s) for s in args))

    def walk_iff(self, formula, args, **kwargs):
        """ a <-> b =  (!a | b) & (!b | a) = !( a & !b ) & !(b & !a)"""
        lhs, rhs = args
        r1 = self.mgr.Not(self.mgr.And(lhs, self.mgr.Not(rhs)))
        r2 = self.mgr.Not(self.mgr.And(rhs, self.mgr.Not(lhs)))
        return self.mgr.And(r1,r2)

    def walk_implies(self, formula, args, **kwargs):
        """ a -> b = !(a & !b) """
        lhs, rhs = args
        return self.mgr.Not(self.mgr.And(lhs, self.mgr.Not(rhs)))

    def walk_ite(self, formula, args, **kwargs):
        """This rewrites only boolean ITE, not theory ones.

            x ? a: b  = (x -> a) & (!x -> b) = !(x & !a) & !(!x & !b)
        """
        i, t, e = args
        if self.env.stc.get_type(t).is_bool_type():
            r1 = self.mgr.Not(self.mgr.And(i, self.mgr.Not(t)))
            r2 = self.mgr.Not(self.mgr.And(self.mgr.Not(i),
                                           self.mgr.Not(e)))
            return self.mgr.And(r1, r2)
        else:
            return formula

# EOC AIGer


from itertools import product

class TimesDistributor(IdentityDagWalker):
    """Normalize the use of multiplication by pushing it into the leafs.

    E.g., (x+1)*3 -> (x*3) + 3
    """
    def __init__(self, env=None, invalidate_memoization=None):
        IdentityDagWalker.__init__(self, env=env,
                                   invalidate_memoization=invalidate_memoization)
        self.Times = self.env.formula_manager.Times
        self.Plus = self.env.formula_manager.Plus
        self.rminus_one = self.env.formula_manager.Real(-1)
        self.iminus_one = self.env.formula_manager.Int(-1)
        self.get_type = self.env.stc.get_type

    def walk_times(self, formula, args, **kwargs):
        """
           From (x + 1) * (y - 1) * p * (m + (7 - p))
           Create [[x, 1], [y, -1*1], [p], [m, 7, -1*p]]
           Compute the cartesian product (itertools.product)

        """
        # Check if there is at least one Plus to distribute over,
        # otherwise we are done. Note that walk_minus rewrites the
        # minus as a plus
        if not any(x.is_plus() for x in args):
            return self.Times(*args)

        # Create list of additions
        flat_args = []
        for a in args:
            # Flattening
            if a.is_plus():
                flat_args.append(a.args())
            else:
                flat_args.append([a])
        res = self.Plus(self.Times(p) for p in product(*flat_args))
        return res

    def walk_plus(self, formula, args, **kwargs):
        new_args = []
        for a in args:
            if a.is_plus():
                new_args += a.args()
            else:
                new_args.append(a)
        return self.Plus(new_args)

    def walk_minus(self, formula, args, **kwargs):
        expr_type = self.get_type(formula)
        if expr_type.is_real_type():
            minus_one = self.rminus_one
        else:
            assert expr_type.is_int_type()
            minus_one = self.iminus_one
        Times = self.Times
        lhs, rhs = args
        if not rhs.is_plus():
            return self.Plus(lhs, Times(minus_one, rhs))
        new_args = [lhs]
        for r in rhs.args():
            new_args.append(Times(minus_one, r))
            return self.Plus(new_args)

# EOC TimesDistributivity


class Ackermannizer(IdentityDagWalker):
    def __init__(self, environment=None):
        IdentityDagWalker.__init__(self, environment)
        # funs_to_args keeps for every function symbol f,
        # a set of lists of arguments.
        # if f(g(x),y) and f(x,g(y)) occur in a formula, then we
        # will have "f": set([g(x), y], [x, g(y)])
        self._funs_to_args = {}

        #maps the actual applications to the constants that will be
        #generated, or to the original term if it is not replaced.
        self._terms_dict = {}

    def do_ackermannization(self, formula):
        substitued_formula = self._fill_maps_and_sub(formula)
        implications = self._get_equality_implications()
        if (len(implications) == 0):
            result = substitued_formula
        else:
            function_consistency = self.mgr.And(implications)
            result = self.mgr.And(function_consistency, substitued_formula)
        return result

    def get_term_to_const_dict(self):
        return self._terms_dict

    def get_const_to_term_dict(self):
        return dict((v, k) for k, v in self._terms_dict.items())

    def _get_equality_implications(self):
        result = set([])
        for f in self._funs_to_args:
            implications = self._generate_implications(f)
            result.update(implications)
        return result

    def _generate_implications(self, f):
        result = set([])
        possible_args = self._funs_to_args[f]
        for option1, option2 in combinations(possible_args, 2):
            implication = self._generate_implication(option1, option2, f)
            result.add(implication)
        return result

    def _generate_implication(self, option1, option2, f):
        left_conjuncts = set([])
        for term1, term2 in zip(option1, option2):
            if term1.is_function_application():
                term1 = self._terms_dict[term1]
            if term2.is_function_application():
                term2 = self._terms_dict[term2]
            conjunct = self.mgr.EqualsOrIff(term1, term2)
            left_conjuncts.add(conjunct)
        left = self.mgr.And(left_conjuncts)
        app1 = self.mgr.Function(f, option1)
        app2 = self.mgr.Function(f, option2)
        app1_const = self._terms_dict[app1]
        app2_const = self._terms_dict[app2]
        right = self.mgr.EqualsOrIff(app1_const, app2_const)
        implication = self.mgr.Implies(left, right)
        return implication

    def _fill_maps_and_sub(self, formula):
        return self.walk(formula)

    def walk_function(self, formula, args, **kwargs):
        try:
            ack_symbol = self._terms_dict[formula]
        except KeyError:
            self._add_args_to_fun(formula)
            self._add_application(formula)
            ack_symbol = self._terms_dict[formula]
        return ack_symbol

    def _add_application(self, formula):
        assert formula.is_function_application()
        if formula not in self._terms_dict:
            const_type = formula.function_name().symbol_type().return_type
            sym = self.mgr.FreshSymbol(typename=const_type,
                                       template="ack%d")
            self._terms_dict[formula] = sym

    def _add_args_to_fun(self, formula):
        function_name = formula.function_name()
        args = formula.args()
        if function_name not in self._funs_to_args.keys():
            self._funs_to_args[function_name] = set([])
        self._funs_to_args[function_name].add(args)



# EOC Ackermannizer


class DisjointSet(object):
    """A simple implementation of the DisjointSet data-structure.
    
    It supports also ranking-based DisjointSet and it can be enabled
    by: 

    1. defining a binary compare function for the  to be stored in
    a DisjointSet. 

    2. Set the compare function while creating the DisjointSet object.
    """

    def __init__(self, compare_fun=None):
        self.leader = {} # maps a member to the group's leader
        self.group = {} # maps a group leader to the group (which is a set)
        self.comp = compare_fun # a binary comparison function used for ranking

    def add(self, a, b):
        """Add the pair (a,b) in the set"""
        leadera = self.leader.get(a)
        leaderb = self.leader.get(b)
        if leadera is not None:
            if leaderb is not None:
                if leadera == leaderb:
                    return # nothing to do
                groupa = self.group[leadera]
                groupb = self.group[leaderb]
                if self.comp is not None and self.comp(leadera, leaderb) > 0:
                    a, leadera, groupa, b, leaderb, groupb = b, leaderb, groupb,\
                                                             a, leadera, groupa
                groupa |= groupb
                del group[leaderb]
                for k in groupb:
                    self.leader[k] = leadera
            else:
                self.group[leadera].add(b)
                self.leader[b] = leadera
        else:
            if leaderb is not None:
                self.group[leaderb].add(a)
                self.leader[a] = leaderb
            else:
                if self.comp is not None and self.comp(a, b) > 0:
                    a, b = b, a
                self.leader[a] = self.leader[b] = a
                self.group[a] = set([a, b])

    def find(self, k):
        """Find the root of k in the set"""
        return self.leader[k]

# EOC DisjointSet

class FXPToBV(DagWalker):

    def __init__(self, environment=None):
        DagWalker.__init__(self, environment)

        self.mgr = self.env.formula_manager
        self.symbol_map = dict()
        self.st_bv = self.mgr.BV(0, 1)
        self.wp_bv = self.mgr.BV(1, 1)
        self.ru_bv = self.mgr.BV(0, 1)
        self.rd_bv = self.mgr.BV(1, 1)

    def convert(self, formula):
        return self.walk(formula)

    def bv_extend(self, bv, length, sign):
        if sign:
            return self.mgr.BVSExt(bv, length)
        else:
            return self.mgr.BVZExt(bv, length)

    def walk_ufxp_add(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        extended_width = total_width + 1
        max_value = self.mgr.BV(2**total_width - 1, total_width)
        extended_max_value = self.mgr.BV(2**total_width - 1, extended_width)
        om = args[0]
        left = args[1]
        right = args[2]
        extended_sum = self.mgr.BVAdd(
                self.bv_extend(left, 1, False),
                self.bv_extend(right, 1, False))
        wrapped_sum = self.mgr.BVAdd(left, right)
        saturated_sum = self.mgr.Ite(
                self.mgr.BVUGT(extended_sum, extended_max_value),
                max_value,
                wrapped_sum)
        return self.mgr.Ite(self.mgr.Equals(om, self.wp_bv),
                wrapped_sum,
                saturated_sum)

    def convert_sfxp_lop(self, bv_op, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        extended_width = total_width + 1
        max_value = self.mgr.SBV(2**(total_width - 1) - 1, total_width)
        extended_max_value = self.mgr.SBV(2**(total_width - 1) - 1, extended_width)
        min_value = self.mgr.SBV(-2**(total_width - 1), total_width)
        extended_min_value = self.mgr.SBV(-2**(total_width - 1), extended_width)
        om = args[0]
        left = args[1]
        right = args[2]
        extended_sum = bv_op(
                self.bv_extend(left, 1, True),
                self.bv_extend(right, 1, True))
        wrapped_sum = bv_op(left, right)
        saturated_sum = self.mgr.Ite(
                self.mgr.BVSGT(extended_sum, extended_max_value),
                max_value,
                self.mgr.Ite(
                    self.mgr.BVSLT(extended_sum, extended_min_value),
                    min_value,
                    wrapped_sum))
        return self.mgr.Ite(self.mgr.Equals(om, self.wp_bv),
                wrapped_sum,
                saturated_sum)

    def walk_sfxp_add(self, formula, args, **kwargs):
        return self.convert_sfxp_lop(self.mgr.BVAdd, formula, args, **kwargs)

    def walk_ufxp_sub(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        om = args[0]
        left = args[1]
        right = args[2]
        wrapped_sub = self.mgr.BVSub(left, right)
        saturated_sub = self.mgr.Ite(
                self.mgr.BVUGT(left, right),
                wrapped_sub,
                self.mgr.BV(0, total_width))
        return self.mgr.Ite(self.mgr.Equals(om, self.wp_bv),
                wrapped_sub,
                saturated_sub)

    def walk_sfxp_sub(self, formula, args, **kwargs):
        return self.convert_sfxp_lop(self.mgr.BVSub, formula, args, **kwargs)

    def walk_ufxp_mul(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        extended_width = total_width * 2
        frac_width = ty.frac_width

        om = args[0]
        rm = args[1]
        left = args[2]
        right = args[3]

        # sign extended to double bit-width
        extended_left = self.bv_extend(left, total_width, False)
        extended_right = self.bv_extend(right, total_width, False)

        # perform multiplication
        # the result is
        # | integral part (2*int_width) | fractional part (2* frac_width)|
        # that represents the exact result
        # x*y/2^(2*fb)
        precise_res_in_bv = self.mgr.BVMul(extended_left, extended_right)
        # do rounding
        dumped_bits = self.mgr.BVExtract(precise_res_in_bv, 0, frac_width - 1)
        rounded_res_in_bv = self.mgr.BVExtract(precise_res_in_bv, frac_width,
                extended_width - 1)
        # if rounding mode is round up and the last frac_width bits are not 0s,
        # round the left part up by 1
        # otherwise use the remaining bits
        rounded_res_in_bv = self.mgr.Ite(
                self.mgr.And(
                    self.mgr.Equals(rm, self.ru_bv),
                    self.mgr.Not(
                        self.mgr.Equals(
                            dumped_bits,
                            self.mgr.BV(0, frac_width)))),
                self.mgr.BVAdd(
                    rounded_res_in_bv,
                    self.mgr.BV(1, extended_width - frac_width)),
                rounded_res_in_bv)

        # overflow handling
        max_value_in_extended_width = self.mgr.BV(2**total_width - 1,
                extended_width - frac_width) 

        wrapped_res = self.mgr.BVExtract(rounded_res_in_bv, 0, total_width - 1)
        saturated_res = self.mgr.Ite(
                self.mgr.BVUGT(rounded_res_in_bv, max_value_in_extended_width),
                self.mgr.BV(2**total_width - 1, total_width),
                wrapped_res)

        return self.mgr.Ite(
                self.mgr.Equals(om, self.wp_bv),
                wrapped_res,
                saturated_res)

    def walk_sfxp_mul(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        extended_width = total_width * 2
        frac_width = ty.frac_width

        om = args[0]
        rm = args[1]
        left = args[2]
        right = args[3]

        # sign extended to double bit-width
        extended_left = self.bv_extend(left, total_width, True)
        extended_right = self.bv_extend(right, total_width, True)

        # perform multiplication
        # the result is
        # | integral part (2*int_width) | fractional part (2* frac_width)|
        # that represents the exact result
        # x*y/2^(2*fb)
        precise_res_in_bv = self.mgr.BVMul(extended_left, extended_right)
        # do rounding
        dumped_bits = self.mgr.BVExtract(precise_res_in_bv, 0, frac_width - 1)
        rounded_res_in_bv = self.mgr.BVExtract(precise_res_in_bv, frac_width,
                extended_width - 1)
        # if rounding mode is round up and the last frac_width bits are not 0s,
        # round the left part up by 1
        # otherwise use the remaining bits
        rounded_res_in_bv = self.mgr.Ite(
                self.mgr.And(
                    self.mgr.Equals(rm, self.ru_bv),
                    self.mgr.Not(
                        self.mgr.Equals(
                            dumped_bits,
                            self.mgr.BV(0, frac_width)))),
                self.mgr.BVAdd(
                    rounded_res_in_bv,
                    self.mgr.BV(1, extended_width - frac_width)),
                rounded_res_in_bv)

        # overflow handling
        max_value_in_extended_width = self.mgr.BV(2**(total_width - 1) - 1,
                extended_width - frac_width) 
        min_value_in_extended_width = self.mgr.BV((2**(total_width - frac_width
            + 1) - 1) << (total_width - 1), extended_width - frac_width)

        wrapped_res = self.mgr.BVExtract(rounded_res_in_bv, 0, total_width - 1)
        saturated_res = self.mgr.Ite(
                self.mgr.BVSGT(rounded_res_in_bv, max_value_in_extended_width),
                self.mgr.BV(2**(total_width - 1) - 1, total_width),
                self.mgr.Ite(
                    self.mgr.BVSLT(rounded_res_in_bv,
                        min_value_in_extended_width),
                    self.mgr.BV(1 << (total_width - 1), total_width),
                    wrapped_res))

        return self.mgr.Ite(
                self.mgr.Equals(om, self.wp_bv),
                wrapped_res,
                saturated_res)

    def walk_ufxp_div(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        frac_width = ty.frac_width
        extended_width = total_width + frac_width

        om = args[0]
        rm = args[1]
        dividend = args[2]
        divisor = args[3]

        zero = self.mgr.BV(0, total_width)
        allones = self.mgr.BV(2**total_width - 1, total_width)

        # x/y needs to rounds to z/(2^fb)
        # this amounts to (2^fb)*(x/y) rounds to z
        extended_dividend = self.mgr.BVLShl(
                self.bv_extend(dividend, frac_width, False),
                self.mgr.BV(frac_width, extended_width))
        extended_divisor = self.bv_extend(divisor, frac_width, False)
        extended_res = self.mgr.BVUDiv(extended_dividend, extended_divisor)
        remainder = self.mgr.BVURem(extended_dividend, extended_divisor)

        # do rounding
        rounded_res = self.mgr.Ite(
                self.mgr.And(
                    self.mgr.Equals(rm, self.ru_bv),
                    self.mgr.Not(
                        self.mgr.Equals(
                            remainder,
                            self.mgr.BV(0, extended_width)))),
                self.mgr.BVAdd(extended_res, self.mgr.BV(1, extended_width)),
                extended_res)

        # overflow handling
        max_value = self.mgr.BV(2**total_width - 1, total_width)
        extended_max_value = self.mgr.BV(2**total_width - 1, extended_width)
        wrapped_res = self.mgr.BVExtract(rounded_res, 0, total_width - 1)
        saturated_res = self.mgr.Ite(
                self.mgr.BVUGT(extended_res, extended_max_value),
                max_value,
                wrapped_res)

        return self.mgr.Ite(
                self.mgr.Equals(divisor, zero),
                allones,
                self.mgr.Ite(
                    self.mgr.Equals(om, self.wp_bv),
                    wrapped_res,
                    saturated_res))

    def walk_sfxp_div(self, formula, args, **kwargs):
        ty = self.env.stc.get_type(formula)
        total_width = ty.total_width
        frac_width = ty.frac_width
        # we need the additional bit as the bvsdiv may overflow
        extended_width = total_width + frac_width + 1

        om = args[0]
        rm = args[1]
        dividend = args[2]
        divisor = args[3]

        zero = self.mgr.BV(0, total_width)
        extended_zero = self.mgr.BV(0, extended_width)
        extended_one = self.mgr.BV(1, extended_width)
        allones = self.mgr.BV(2**total_width - 1, total_width)

        # x/y needs to rounds to z/(2^fb)
        # this amounts to (2^fb)*(x/y) rounds to z
        extended_dividend = self.mgr.BVLShl(
                self.bv_extend(dividend, frac_width + 1, True),
                self.mgr.BV(frac_width, extended_width))
        extended_divisor = self.bv_extend(divisor, frac_width + 1, True)
        extended_res = self.mgr.BVSDiv(extended_dividend, extended_divisor)
        remainder = self.mgr.BVSRem(extended_dividend, extended_divisor)

        # do rounding
        def get_bv_sign(bv):
            msb_pos = total_width - 1
            return self.mgr.Equals(
                    self.mgr.BVExtract(bv, msb_pos, msb_pos),
                    self.mgr.BV(1, 1))

        if_ru = self.mgr.Equals(rm, self.ru_bv)
        dividend_sign = get_bv_sign(dividend)
        divisor_sign = get_bv_sign(divisor)
        if_pos = self.mgr.Not(
                self.mgr.Xor(dividend_sign, divisor_sign))
        rounded_res = self.mgr.Ite(
                self.mgr.Or(
                    self.mgr.Xor(if_ru, if_pos),
                    self.mgr.Equals(
                        remainder,
                        extended_zero)),
                extended_res,
                self.mgr.Ite(
                    self.mgr.And(if_ru, if_pos),
                    self.mgr.BVAdd(extended_res, extended_one),
                    self.mgr.BVSub(extended_res, extended_one)))

        # overflow handling
        max_value = self.mgr.BV(2**(total_width-1) - 1, total_width)
        extended_max_value = self.mgr.BV(2**(total_width-1) - 1, extended_width)
        min_value = self.mgr.SBV(-(2**(total_width - 1)), total_width)
        extended_min_value = self.mgr.SBV(-(2**(total_width - 1)), extended_width)
        wrapped_res = self.mgr.BVExtract(rounded_res, 0, total_width - 1)
        saturated_res = self.mgr.Ite(
                self.mgr.BVSGT(extended_res, extended_max_value),
                max_value,
                self.mgr.Ite(
                    self.mgr.BVSLT(extended_res, extended_min_value),
                    min_value,
                    wrapped_res))

        return self.mgr.Ite(
                self.mgr.Equals(divisor, zero),
                allones,
                self.mgr.Ite(
                    self.mgr.Equals(dividend, zero),
                    zero,
                    self.mgr.Ite(
                        self.mgr.Equals(om, self.wp_bv),
                        wrapped_res,
                        saturated_res)))

    def walk_sfxp_neg(self, formula, args, **kwargs):
        total_width = self.env.stc.get_type(formula).total_width
        cond = self.mgr.And(self.mgr.Equals(args[1], self.mgr.SBV(-(2**(total_width-1)), total_width)),
                            self.mgr.Equals(args[0], self.st_bv))
        return self.mgr.Ite(cond, self.mgr.SBV(2**(total_width-1)-1, total_width), self.mgr.BVNeg(args[1]))

    def walk_symbol(self, formula, **kwargs):
        ty = self.env.stc.get_type(formula)
        if ty.is_fxp_type():
            if formula not in self.symbol_map:
                self.symbol_map[formula] = \
                    self.mgr.FreshSymbol(types.BVType(ty.total_width))
                return self.symbol_map[formula]
        elif ty.is_fxp_om_type() or ty.is_fxp_rm_type():
            if formula not in self.symbol_map:
                self.symbol_map[formula] = \
                    self.mgr.FreshSymbol(types.BVType(1))
                return self.symbol_map[formula]
        else:
            return formula

    def walk_st(self, formula, **kwargs):
        return self.st_bv

    def walk_wp(self, formula, **kwargs):
        return self.wp_bv

    def walk_ru(self, formula, **kwargs):
        return self.ru_bv

    def walk_rd(self, formula, **kwargs):
        return self.rd_bv

    def walk_equals(self, formula, args, **kwargs):
        left = args[0]
        right = args[1]
        return self.mgr.Equals(left, right)

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(*args)

    def walk_or(self, formula, args, **kwargs):
        return self.mgr.Or(*args)

    def walk_implies(self, formula, args, **kwargs):
        left = args[0]
        right = args[1]
        return self.mgr.Implies(left, right)

    def walk_ite(self, formula, args, **kwargs):
        return formula

    def walk_not(self, formula, args, **kwargs):
        return self.mgr.Not(args[0])

    def walk_bv_constant(self, formula, args, **kwargs):
        return formula

    def walk_ufxp_constant(self, formula, args, **kwargs):
        return formula.arg(0)

    def walk_sfxp_constant(self, formula, args, **kwargs):
        return formula.arg(0)

    def walk_ufxp_lt(self, formula, args, **kwargs):
        return self.mgr.BVULT(args[0], args[1])

    def walk_ufxp_le(self, formula, args, **kwargs):
        return self.mgr.BVULE(args[0], args[1])

    def walk_sfxp_lt(self, formula, args, **kwargs):
        return self.mgr.BVSLT(args[0], args[1])

    def walk_sfxp_le(self, formula, args, **kwargs):
        return self.mgr.BVSLE(args[0], args[1])

    def walk_bool_constant(self, formula, args, **kwargs):
        return formula

    def walk_iff(self, formula, args, **kwargs):
        left = args[0]
        right = args[1]
        return self.mgr.Iff(left, right)

def get_fp_bv_converter(environment=None):
    fp_bv_converter = FXPToBV(environment)
    return fp_bv_converter

def nnf(formula, environment=None):
    """Converts the given formula in NNF"""
    nnfizer = NNFizer(environment)
    return nnfizer.convert(formula)


def cnf(formula, environment=None):
    """Converts the given formula in CNF represented as a formula"""
    cnfizer = CNFizer(environment)
    return cnfizer.convert_as_formula(formula)


def cnf_as_set(formula, environment=None):
    """Converts the given formula in CNF represented as a set of sets"""
    cnfizer = CNFizer(environment)
    return cnfizer.convert(formula)


def prenex_normal_form(formula, environment=None):
    """Converts the given formula in Prenex Normal Form"""
    normalizer = PrenexNormalizer(environment)
    return normalizer.normalize(formula)


def aig(formula, environment=None):
    """Converts the given formula in AIG"""
    aiger = AIGer(environment)
    return aiger.convert(formula)


def conjunctive_partition(formula):
    """ Returns a generator over the top-level conjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> And(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_and():
                to_process += cur.args()
            else:
                yield cur


def disjunctive_partition(formula):
    """ Returns a generator over the top-level disjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> Or(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_or():
                to_process += cur.args()
            else:
                yield cur


def propagate_toplevel(formula, env=None, do_simplify=True, preserve_equivalence=True):
    """ Propagates the toplevel definitions and returns an equivalent formula.
    It considers three kinds of definitions:
    1) variable = constant
    2) variable = variable
    3) constant = constant
    """
    if env is None:
        import pysmt.environment
        env = pysmt.environment.get_env()
    mgr = env.formula_manager

    # comparison function for ranking
    def compare(a, b):
        if a.node_id() == b.node_id():
            return 0
        if a.is_constant() and b.is_constant():
            return a.constant_value() - b.constant_value()
        if a.is_constant():
            return -1
        if b.is_constant():
            return 1
        return a.node_id() - b.node_id()

    disjoint_set = DisjointSet(compare_fun=compare)
    relevant = set()
    
    for c in conjunctive_partition(formula):
        if c.is_equals():
            l, r = c.args()
            if l.is_array_value() or r.is_array_value():
                # skipping constant arrays
                continue
            if (l.is_symbol() or l.is_constant()) and\
               (r.is_symbol() or r.is_constant()):
                relevant.add(l)
                relevant.add(r)
                disjoint_set.add(l, r)

    # check and build the mapping
    sigma = {}
    for k in relevant:
        v = disjoint_set.find(k)
        if k.node_id() != v.node_id():
            # early detection of a conflict
            if k.is_constant() and v.is_constant() and\
               k.constant_value() != v.constant_value():
                return mgr.FALSE()
            else:
                sigma[k] = v

    res = formula.substitute(sigma)
    if preserve_equivalence:
        res = mgr.And(res, mgr.And([mgr.Equals(k, sigma[k]) for k in sigma]))
    return res.simplify() if do_simplify else res
