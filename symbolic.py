"""Symbolic automata with multiple players."""
# Copyright 2015-2017 by Ioannis Filippidis
# Copyright 2015-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy
import pprint

from dd import bdd as _bdd
from omega.logic.ast import Nodes as _Nodes
from omega.logic import bitvector as bv
from omega.logic import lexyacc
from omega.logic import syntax as stx
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import enumeration as enum
from omega.symbolic import fol as _fol
from omega.symbolic import symbolic as _sym


class Automaton(_fol.Context):
    """Multi-player game.

    You can use an (non-)interleaving representation,
    depending on your preference.
    Also, you can define a game with fixed turn order
    or not, or with partial information or not.
    What functions you call later depends on this choice.


    User-defined attributes
    =======================

    You define the attributes:

      - vars: `dict` that maps each variable name to
        a `dict` with keys:

          - `"type": "boolean" or "modwrap" or "saturating"`
          - `"dom": (min, max)`, range of integer
          - `"owner": "env" or "sys"`
          - `"init"`: has suitable `__str__` (and is optional)

      - init: initial condition
      - action: transition relation
      - win: winning condition
      - bdd: change this only if you want a different manager,
        for example CUDD.

    Each of `init, action, win` is a `dict` of the form:

      - init, action: player -> str
      - win: player -> {'<>[]': list of str,
                        '[]<>': list of str}

    Add operator names (as strings) to these lists.
    This creates a level of indirection, referring to both
    formulae as strings, as well as BDD nodes.


    Auto-generated attributes
    =========================

    The method `add_vars` adds to `vars[var]` the keys:

      - `"bitnames"`: `list`
      - `"signed"`: `True` if signed integer
      - `"width"`: `len(bitnames)`

    Optionally, `add_vars` can declare flexible variables too.
    For flexible variables, `add_vars` adds both unprimed and
    prime names to the symbol table.


    References
    ==========

    Leslie Lamport
        "The temporal logic of actions"
        ACM Transactions on Programming
        Languages and Systems (TOPLAS),
        Vol.16, No.3, pp.872--923, 1994

    Rajeev Alur, Thomas A. Henzinger, Orna Kupferman
        "Alternating-time temporal logic"
        Journal of the ACM (JACM)
        Vol.49, No.5, pp.672--713, 2002

    Klaus Schneider
        "Verification of reactive systems"
        Springer, 2004
    """

    # metalinguistic purposes served by attributes
    # stored in an `Automaton`:
    #
    # - substitution (renaming maps)
    # - grouping variables to feed quantifiers later
    # - defining operators
    #
    # It will be useful to keep the renaming maps
    # as attributes, for convenience.

    def __init__(self):
        super(Automaton, self).__init__()
        # `varlist` says which variables represent each component
        # essentially, `varlist` is Lamport's `\mu`
        self.varlist = dict()  # groups of variables for various uses
        self.owners = set()
        self.players = dict()  # player (str) -> turn (int)
        # formulae
        self.op = dict()  # operator name -> `str`
        self.op_bdd = dict()  # operator name -> bdd
        # purely metasyntactic replacements
        # for example, tuples of quantified vars
        self.meta = dict()  # meta-identifier name -> `str`
        # game-solving attributes
        # To be used by solvers. Write spec itself in TLA.
        self.init_expr = dict()  # player name -> op name
        self.action_expr = dict()  # player name -> op name
        self.win_expr = dict()  # player name -> dict
                           # with keys "[]<>" and "<>[]"
        self.init = dict()
        self.action = dict()
        self.win = dict()
        # auto-populated
        self._players = None
        self._turns = None  # inverse of `self.players`

    def __copy__(self):
        other = type(self)()
        other.vars = copy.deepcopy(self.vars)
        other.bdd = self.bdd
        other.varlist = copy.deepcopy(self.varlist)
        other.owners = copy.deepcopy(self.owners)
        other.players = copy.deepcopy(self.players)
        other.op = copy.deepcopy(self.op)
        other.op_bdd = copy.copy(self.op_bdd)
        other.meta = copy.deepcopy(self.meta)
        # strings
        other.init_expr = copy.copy(self.init_expr)
        other.action_expr = copy.copy(self.action_expr)
        other.win_expr = {
            k: copy.copy(v)
            for k, v in self.win_expr.items()}
        # BDD nodes
        other.init = copy.copy(self.init)
        other.action = copy.copy(self.action)
        other.win = {
            k: copy.copy(v)
            for k, v in self.win.items()}
        return other

    def __str__(self):
        c = list()
        s = 'Players: \n {p}'.format(p=self.players)
        c.append(s)
        s = 'Variables: \n {v}'.format(v=pprint.pformat(self.vars))
        c.append(s)
        for k, v in self.init_expr.items():
            s = '\ninit: {k}\n---\n'.format(k=k)
            c.append(s)
            c.append(v)
        for k, v in self.action_expr.items():
            s = '\naction: {k}\n---\n'.format(k=k)
            c.append(s)
            c.append(v)
        for k, d in self.win_expr.items():
            s = '\nwin: {k}\n---\n'.format(k=k)
            c.append(s)
            for k, v in d.items():
                for e in v:
                    s = '{k}({e})'.format(k=k, e=e)
                    c.append(s)
        s = '\n'.join(str(u) for u in c)
        return 'Multi-player game structure:\n' + s

    def declare_variables(self, **vrs):
        d = bv.make_symbol_table(vrs)
        self.add_vars(d, flexible=True)

    def declare_constants(self, **constants):
        d = bv.make_symbol_table(constants)
        self.add_vars(d, flexible=False)

    def add_vars(self, vrs, flexible=False):
        """Declare variables `vrs`.

        Refine integer-valued variables by
        Boolean-valued variables, and create maps for
        concrete variables (bits).

        @param flexible: if `True`, then add also variables
            with primed names. Assumes unprimed names given.
        """
        assert vrs, vrs
        assert type(flexible) == bool, flexible  # catch kw conflict
        if flexible:
            vrs = _sym.add_primed_too(vrs)
        super(Automaton, self).add_vars(vrs)

    @property
    def vars_of_all_players(self):
        """Set of variables of all players."""
        return self.vars_of_players(self.players)

    def vars_of_players(self, players):
        """Set of variables controlled by `players`."""
        gen = (
            v for k, v in self.varlist.items()
            if k in players)
        return set().union(*gen)

    def prime_vars(self, vrs):
        """Return `list` of primed variables from `vrs`."""
        return [stx.prime(var) for var in vrs]

    def unprime_vars(self, vrs):
        """Return `list` of primed variables from `vrs`."""
        return [stx.unprime(var) for var in vrs]

    def replace_with_primed(self, vrs, u):
        """Substitute primed for unprimed `vrs` in `u`.

        For example:

        ```
        u = aut.add_expr("x /\ y /\ z")
        vrs = ['x', 'y']
        v = aut.replace_with_primed(vrs, u)
        v_ = aut.add_expr("x' /\ y' /\ z")
        assert v == v_
        ```
        """
        let = {k: stx.prime(k) for k in vrs}
        return self.let(let, u)

    def replace_with_unprimed(self, vrs, u):
        """Substitute unprimed `vrs` for primed in `u`."""
        let = {stx.prime(k): k for k in vrs}
        return self.let(let, u)

    def implies_type_hints(self, u, vrs):
        """Return `True` if `u => TypeInv` for all vars.

        All declared variables and constants are taken into
        account.
        """
        # not named `assert_type_invariant` because the
        # assertion is about the state predicate `u`,
        # so a static conclusion.
        vrs = {var for var in self.vars
               if not stx.isprimed(var)}
        type_hints = _conjoin_type_hints(vrs, self)
        r = type_hints | ~ u
        return r == self.true

    def type_hint_for(self, vrs):
        """Return initial predicate using type hints for `vrs`.

        See also `self.type_action_for`.
        """
        return self._type_hints_to_formulas(vrs, action=False)

    def type_action_for(self, vrs):
        """Return action using type hints for `vrs`.

        The type action has the form:

            TypeAction == Inv /\ Inv'

        where `Inv` is a box. A box is a conjunction of integer
        intervals, one for each variable. For each integer variable,
        the interval constraint has the form:

            var \in min_value...max_value

        The implementation supports only integer variables,
        so the interval constraint is implemented as the
        conjunction of two inequalities:

            /\ min_value <= var
            /\ var <= max_value

        If we take the closure, the second conjunct will
        result from the type invariant. The above is usable
        with either approach (w/ or w/o closure).

        @return: formula as `str`
        """
        # if you want BDD, just call `add_expr`
        return self._type_hints_to_formulas(vrs, action=True)

    def _type_hints_to_formulas(self, vrs, action):
        """Return type constraint for `vrs` as `str`.

        If `action is  True` then return type invariant `Inv`,
        else the action `Inv /\ Inv'`.
        """
        r = list()
        for var in vrs:
            hints = self.vars[var]
            if hints['type'] == 'bool':
                continue
            assert hints['type'] == 'int', hints
            a, b = hints['dom']
            s = '({a} <= {var}) /\ ({var}  <= {b})'
            type_inv = s.format(a=a, b=b, var=var)
            r.append(type_inv)
            if not action:
                continue
            type_inv_primed = s.format(
                a=a, b=b, var=stx.prime(var))
            r.append(type_inv_primed)
        return stx.conj(r)

    def map_expr_to_bdd(self):
        """Use `expr_to_bdd` to map attribute `op` to `op_bdd`."""
        raise DeprecationWarning(
            'obviated by method `Context.define`.')
        self.op_bdd = {
            k: self.add_expr(v)
            for k, v in self.op.items()}

    def build(self):
        """Populate `init, action, win` with BDD nodes.

        By mapping operators from `init_expr`, `action_expr`,
        and `win_expr` to BDD nodes using `self.op_bdd`.
        """
        self.init = {
            k: self._to_bdd(v)
            for k, v in self.init_expr.items()}
        self.action = {
            k: self._to_bdd(v)
            for k, v in self.action_expr.items()}
        for k, v in self.win_expr.items():
            d = dict()
            for s, t in v.items():
                d[s] = [self._to_bdd(e) for e in t]
            self.win[k] = d

    def _to_bdd(self, e):
        """Return BDD via either `add_expr` or `op_bdd`."""
        if e in self.op_bdd:
            return self.op_bdd[e]
        return self.add_expr(e)

    def assert_consistent(self, moore=True):
        """Assert that `init` and `win` contain state predicates."""
        varlists = list(self.varlist.values())
        assert pairwise_disjoint(varlists)
        for u in self.init.values():
            assert sym_bdd.is_state_predicate(u)
        # Moore actions
        for player, action in self.action.items():
            primed = {
                stx.unprime(var)
                for var in self.support(action)
                if stx.isprimed(var)}
            # applicable only after unzip
            # assert primed.issubset(self.varlist[player]), (
            #     (player, primed))
        for d in self.win.values():
            for v in d.values():
                for u in v:
                    assert sym_bdd.is_state_predicate(u)


def conj_actions_of(players, aut):
    """Return conjunction of actions from `players`."""
    action = aut.true
    for p in players:
        action &= aut.action[p]
    return action


def _conjoin_type_hints(vrs, fol):
    """Return conjunction of type hints for `vrs` as BDD."""
    r = list()
    for var in vrs:
        hints = fol.vars[var]
        if hints['type'] == 'bool':
            # The constraint `var \in BOOLEAN` will
            # anyway dissapear at the BDD layer.
            continue
        assert hints['type'] == 'int', hints
        a, b = hints['dom']
        s = '({a} <= {var}) /\ ({var} <= {b})'
        type_hints = s.format(a=a, b=b, var=var)
        r.append(type_hints)
    u = fol.add_expr(stx.conj(r))
    return u


def print_expr(u, aut):
    """Print minimal DNF, taking into account type hints."""
    s = dumps_expr(u, aut)
    print('---- min DNF ----')
    print(s)
    print('=================')


def type_hints_for_support(u, fol):
    """Return type hints for vars in `fol.support(u)`."""
    vrs = fol.support(u)
    s = fol.type_hint_for(vrs)
    types = fol.add_expr(s)
    return types


def dumps_expr(u, fol, care=None, use_types=False):
    """Return minimal DNF, taking into account type hints."""
    types = type_hints_for_support(u, fol)
    if care is None:
        care = fol.true
    if use_types:
        types = type_hints_for_support(u, fol)
        care &= types
    s = fol.to_expr(u, care=care, show_dom=True)
    return s


def _detect_non_player_keys(aut):
    """Print warnings for rigid variables."""
    players = aut.players
    for var, d in aut.vars.items():
        owner = d['owner']
        if owner not in players:
            print((
                'found owner "{owner}" for '
                'variable "{var}", but '
                'this is not a player').format(
                    owner=owner,
                    var=var))
    for attr in (aut.init, aut.action, aut.win):
        for k in attr:
            if k not in players:
                print((
                    'found action key "{k}" '
                    'that is not a player').format(k=k))


class Nodes(_Nodes):
    """Replace metasyntactic identifiers."""

    class Var(_Nodes.Var):
        def flatten(self, meta=None, *arg, **kw):
            var = self.value
            return meta.get(var, var)


# LTL parser for meta-replacements (preprocessor).
parser = lexyacc.Parser(nodes=Nodes)


def replace_meta(s, meta):
    """Return formula after replacing metasyntactic identifiers.

    @param s: LTL formula as `str`
    @param meta: replacements as `dict`
    """
    # a preprocessor
    return parser.parse(s).flatten(meta=meta)


def pick(c):
    """Return an element from container `c`.

    If `c` is empty, return `None`.
    """
    return next(iter(c), None)


def is_primed_state_predicate(u, fol):
    """Return `True` if `u` depends only on primed variables.

    Only constant parameters (rigid variables) can appear
    unprimed in `u`. Any flexible variables in `u` should
    be primed.

    An identifier that is declared only unprimed is assumed
    to be a rigid variables. If a primed sibling is declared,
    then the identifier is assumed to be a flexible variable.
    """
    support = fol.support(u)
    primed = {
        name for name in support
        if stx.isprimed(name)}
    unprimed = support - primed
    any_flexible = False
    for name in unprimed:
        primed = stx.prime(name)
        if primed in fol.vars:
            any_flexible = True
            break
    return not any_flexible


def is_action_of_player(action, player, aut):
    """Return `True` if `action` constrains only `player`.

    The `player` is represented by the variables in
    `aut.varlist[player]`.
    """
    support = aut.support(action)
    primed = {var for var in support if stx.isprimed(var)}
    vrs = aut.vars_of_players([player])
    vrs_p = aut.prime_vars(vrs)
    r = primed.issubset(vrs_p)
    return r


def pairwise_disjoint(c):
    """Return whether elements in `c` are pairwise disjoint."""
    union = set().union(*c)
    n = sum(len(u) for u in c)
    return n == len(union)
