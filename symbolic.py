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


TURN = '_i'


def preimage(target, aut):
    """Predecessors with interleaving representation."""
    # needed to exclude extra steps
    pre = aut.false
    for p, i in aut.players.items():
        action = aut.action[p]
        # equivalent to existential quantification of `_i`
        u = next_turn(target, i, aut)
        u = aut.replace_with_primed(aut.varlist[p], u)
        # note that `action` does not mention the index `_i`
        # so, we existentially go from a set that does not
        # constrain `_i`, to the intersection with `_i = p + 1`
        # of a set that mentions `_i`.
        u &= action
        qvars = aut.prime_vars(aut.varlist[p])
        u = aut.exist(qvars, u)
        u = and_turn(u, i, aut)
        pre |= u
    return pre


def image(source, aut):
    n = len(aut.players)
    pre = aut.false
    for p, i in aut.players.items():
        assert i < n, (i, n)
        action = aut.action[p]
        u = aut.replace(source, {TURN: i})
        u &= action
        qvars = aut.varlist[p]
        u = aut.exist(qvars, u)
        u = aut.replace_with_unprimed(aut.varlist[p], u)
        ip = (i + 1) % n
        u = and_turn(u, ip, aut)
        pre |= u
    return pre


def ue_preimage(target, team, aut):
    pre = aut.false
    for p, i in aut.players.items():
        u = next_turn(target, i, aut)
        u = aut.replace_with_primed(aut.varlist[p], u)
        action = aut.action[p]
        if p not in team:
            u = ~ u
        u &= action
        qvars = aut.prime_vars(aut.varlist[p])
        u = aut.exist(qvars, u)
        if p not in team:
            u = ~ u
        u = and_turn(u, i, aut)
        pre |= u
    return pre


def next_turn(u, i, aut):
    """Replace `TURN == (i + 1) % n` in `u`."""
    assert i >= 0, i
    n = len(aut.players)
    assert i < n, (i, n)
    ip = (i + 1) % n
    return aut.replace(u, {TURN: ip})


def and_turn(u, i, aut):
    """Conjoin `u /\ (TURN = i)`."""
    assert i >= 0, i
    n = len(aut.players)
    assert i < n, (i, n)
    s = '{turn} = {i}'.format(turn=TURN, i=i)
    u &= aut.add_expr(s)
    return u


def attractor(target, team, aut):
    q = target
    qold = None
    while q != qold:
        qold = q
        q |= ue_preimage(q, team, aut)
    return q


def _trap(safe, team, aut, unless=None):
    # debug case: safe = True
    q = aut.true
    qold = None
    while q != qold:
        qold = q
        q &= ue_preimage(q, team, aut)
        q &= safe
        if unless is not None:
            q |= unless
    return q


def test_post():
    aut = Automaton()
    aut.players = dict(alice=0, bob=1)
    aut.vars = dict(x=dict(type='bool', owner='alice'),
                    _i=dict(type='saturating',
                            dom=(0, 1), owner='alice'))
    aut.action_expr['alice'] = ["x <=> ~ x'"]
    fill_blanks(aut)
    print(aut)
    aut = aut.build()
    u = aut.add_expr('x /\ (_i = 0)')
    v = image(u, aut, pre=False)
    enum.print_nodes(v, aut.vars, aut.bdd)


def test_multiplayer_automaton():
    a = Automaton()
    a.players = dict(car_a=0, car_b=1, car_c=2)
    a.vars = dict(
        a=dict(type='saturating', dom=(0, 4), owner='car_a'),
        b=dict(type='saturating', dom=(0, 5), owner='car_b'),
        c=dict(type='bool', owner='car_c'))
    fill_blanks(a)
    aut = a.build()
    print(aut)


def analyze_to_debug(aut):
    both_unblocked = unblocked_set(aut)
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    action = sys_action & env_action
    care_target = both_unblocked
    care_source = fx.ue_preimage(
        sys_action, env_action,
        care_target, aut,
        evars=aut.upvars, moore=True)
    care_source = care_source & both_unblocked
    # care_source = care_source & aut.add_expr('a=4 /\ b=5'))
    enum.dump_relation(action, aut, care_source,
                       care_target, pretty=True)


#    Relation to `omega.symbolic.symbolic.Automaton`
#    ===============================================
#
#      - uvars = varlists["env_vars"]
#      - upvars = varlists["env_vars'"]
#      - ubvars = varlists["env_all"]
#      - evars = varlists["sys_vars"]
#      - epvars = varlists["sys_vars'"]
#      - ebvars = varlists["sys_all"]
#      - uevars = varlists["env_sys"]
#      - uepvars = varlists["env_sys'"]

# - there are more than two groups of variables ("multi-player")
# - what quantifier applies to each group changes
# - priming can be applied "on the spot"
# - renaming to primed can be constructed "on the spot"

# Caching the renaming maps is a form of optimization.
# Only benchmarking can justify optimizations.


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
        # player 0 moves first (cox reverses this)
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

    # user will write "_expr" only when defining the
    # spec, and throughout algorithm code will work
    # with bdds and write less, and less cluttered.
    # The opposite (`init_bdd`) would be a worse
    # design choice.

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
    def all_player_vars(self):
        gen = (
            v for k, v in self.varlist.items()
            if k in self.players)
        return set().union(*gen)

    def prime_vars(self, vrs):
        """Return `list` of primed variables from `vrs`."""
        return [stx.prime(var) for var in vrs]

    def unprime_vars(self, vrs):
        """Return `list` of primed variables from `vrs`."""
        return [stx.unprime(var) for var in vrs]

    def replace_with_primed(self, vrs, u):
        """Substitute primed for unprimed `vrs` in `u`."""
        let = {k: stx.prime(k) for k in vrs}
        return self.replace(u, let)

    def replace_with_unprimed(self, vrs, u):
        """Substitute unprimed `vrs` for primed in `u`."""
        let = {stx.prime(k): k for k in vrs}
        return self.replace(u, let)

    # what we really need is a method called:
    # `take_closure`

    def type_hint_for(self, vrs):
        """Return initial predicate using type hints for `vrs`.

        See also `self.type_action_for`.
        """
        return self._type_hints_to_formulas(vrs, action=False)

    def type_action_for(self, vrs):
        """Return action using type hints for `vrs`.

        For each integer variable, the "type action" is:

        /\ min_value <= var <= max_value  (* type invariant *)
        /\ min_value <= var' <= max_value

        @return: formula as `str`
        """
        # if you want BDD, just call `add_expr`
        return self._type_hints_to_formulas(vrs, action=True)

    def _type_hints_to_formulas(self, vrs, action):
        """Return type invariant or action from type hints."""
        r = list()
        for var in vrs:
            hints = self.vars[var]
            if hints['type'] == 'bool':
                continue
            assert hints['type'] == 'int', hints
            a, b = hints['dom']
            s = '({a} <= {var}) /\ ({var}  <= {b})'
            type_invariant = s.format(a=a, b=b, var=var)
            r.append(type_invariant)
            if not action:
                continue
            type_action = s.format(a=a, b=b, var=stx.prime(var))
            r.append(type_action)
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

    def assert_consistent(self):
        """Assert that `init` and `win` contain state predicates."""
        for u in self.init.values():
            assert sym_bdd.is_state_predicate(u)
        # Moore actions
        for player, action in self.action.items():
            primed = {
                stx.unprime(var)
                for var in self.support(action)
                if stx.isprimed(var)}
            assert primed.issubset(self.varlist[player]), (
                (player, primed))
        for d in self.win.values():
            for v in d.values():
                for u in v:
                    assert sym_bdd.is_state_predicate(u)


# functions for bit ordering in BDD
# bring unprimed and primed bits to be adjacent in BDD


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
