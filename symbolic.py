"""Decompose GR(1) property into a contract."""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy
import pprint
from dd import bdd as _bdd
from omega.symbolic import bdd as sym_bdd
from omega.logic import bitvector as bv
from omega.symbolic import symbolic
from omega.symbolic import enumeration as enum


def preimage(target, aut):
    """Predecessors with interleaving repr."""
    bdd = aut.bdd
    n = len(aut.players)
    ivar = '_i'
    # needed to force extra steps outside
    pre = bdd.false
    for i, p in aut.turns.items():
        assert i < n, (i, n)
        assert p in aut.players, (p, aut.players)
        ip = (i + 1) % n
        u = symbolic.cofactor(target, ivar, ip, bdd, aut.vars)
        (action,) = aut.action[p]
        u = _bdd.rename(u, bdd, aut.prime[p])
        u = bdd.apply('and', action, u)
        qvars = aut.unprime[p]
        u = bdd.quantify(u, qvars, forall=False)
        s = '{ivar} = {i}'.format(ivar=ivar, i=i)
        turn = aut.add_expr(s)
        u = bdd.apply('and', turn, u)
        # TODO: revisit the index behavior
        pre = bdd.apply('or', pre, u)
    return pre


def image(source, aut):
    bdd = aut.bdd
    n = len(aut.players)
    ivar = '_i'
    pre = bdd.false
    for i, p in aut.turns.items():
        assert i < n, (i, n)
        assert p in aut.players, (p, aut.players)
        ip = (i + 1) % n
        (action,) = aut.action[p]
        qvars = aut.prime[p]
        u = symbolic.cofactor(source, ivar, i, bdd, aut.vars)
        u = bdd.apply('and', action, u)
        u = bdd.quantify(u, qvars, forall=False)
        u = _bdd.rename(u, bdd, aut.unprime[p])
        s = '{ivar} = {ip}'.format(ivar=ivar, ip=ip)
        turn = aut.add_expr(s)
        u = bdd.apply('and', turn, u)
        pre = bdd.apply('or', pre, u)
    return pre


def ue_preimage(target, team, aut):
    bdd = aut.bdd
    n = len(aut.players)
    ivar = '_i'
    pre = bdd.false
    for i, p in aut.turns.items():
        assert i < n, (i, n)
        assert p in aut.players, (p, aut.players)
        ip = (i + 1) % n
        u = symbolic.cofactor(target, ivar, ip, bdd, aut.vars)
        u = _bdd.rename(u, bdd, aut.prime[p])
        (action,) = aut.action[p]
        if p not in team:
            u = bdd.apply('not', u)
        u = bdd.apply('and', action, u)
        u = bdd.quantify(u, aut.unprime[p], forall=False)
        if p not in team:
            u = bdd.apply('not', u)
        s = '{ivar} = {i}'.format(ivar=ivar, i=i)
        turn = aut.add_expr(s)
        u = bdd.apply('and', turn, u)
        pre = bdd.apply('or', pre, u)
    return pre


def attractor(target, team, aut):
    bdd = aut.bdd
    q = target
    qold = None
    while q != qold:
        qold = q
        pre = ue_preimage(q, team, aut)
        q = bdd.apply('or', pre, qold)
    return q


def _trap(safe, team, aut, unless=None):
    bdd = aut.bdd
    q = bdd.true
    qold = None
    while q != qold:
        qold = q
        pre = ue_preimage(q, team, aut)
        q = bdd.apply('and', safe, pre)
        if unless is not None:
            q = bdd.apply('or', q, unless)
    return q


def test_post():
    aut = Automaton()
    aut.players = dict(alice=0, bob=1)
    aut.vars = dict(x=dict(type='bool', owner='alice'),
                    _i=dict(type='saturating', dom=(0, 1), owner='alice'))
    aut.action['alice'] = ["x <-> !x'"]
    fill_blanks(aut)
    print(aut)
    aut = aut.build()
    u = aut.add_expr('x & (_i = 0)')
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


class Automaton(object):
    """Turn-based multi-player game.

    Interleaving representation.
    """

    def __init__(self):
        # player 0 moves first (cox reverses this)
        self.players = dict()  # dict(str: int) maps: name -> turn
        self.vars = dict()
        # auto-populated
        self.prime = dict()
        self.unprime = dict()
        self.turns = list()
        # formulae
        self.init = dict()  # dict(key=list())
        self.action = dict()
        self.win = dict()
        # aux
        self.bdd = _bdd.BDD()

    def __copy__(self):
        a = Automaton()
        a.players = copy.deepcopy(self.players)
        a.vars = copy.deepcopy(self.vars)
        a.prime = copy.deepcopy(self.prime)
        a.unprime = copy.deepcopy(self.unprime)
        a.turns = copy.deepcopy(self.turns)
        a.init = copy.deepcopy(self.init)
        a.action = copy.deepcopy(self.action)
        a.win = copy.deepcopy(self.win)
        a.bdd = self.bdd
        return a

    def __str__(self):
        c = list()
        s = 'Players: \n {p}'.format(p=self.players)
        c.append(s)
        s = 'Variables: \n {v}'.format(v=pprint.pformat(self.vars))
        c.append(s)
        for k, v in self.init.items():
            s = '\ninit: {k}\n---\n'.format(k=k)
            c.append(s)
            c.extend(v)
        for k, v in self.action.items():
            s = '\naction: {k}\n---\n'.format(k=k)
            c.append(s)
            c.extend(v)
        for k, v in self.win.items():
            s = '\nwin: {k}\n---\n'.format(k=k)
            c.append(s)
            c.extend(v)
        s = '\n'.join(str(u) for u in c)
        return 'Multi-player game structure:\n' + s

    def build(self):
        aut = _bitblast(self)
        aut = _bitvector_to_bdd(aut)
        return aut

    def add_expr(self, e):
        """Add first-order formula."""
        t = self.vars
        s = bv.bitblast(e, t)
        u = sym_bdd.add_expr(s, self.bdd)
        return u


def _bitblast(aut):
    aut = copy.copy(aut)
    players = set(aut.players)
    players.add(None)
    t, init, action = bv.bitblast_table(aut.vars, players)
    init.pop(None)
    action.pop(None)
    for k, v in init.items():
        aut.init[k].extend(v)
    for k, v in action.items():
        aut.action[k].extend(v)
    # conjoin now, instead of later with BDDs
    for k in aut.players:
        symbolic._conj_owner(aut, k, 'infix')
    a = Automaton()
    a.players = aut.players
    a.vars = t
    _bitblast_attr(aut, a, t)
    return a


def _bitblast_attr(aut, a, t):
    def f(x):
        return bv.bitblast(x, t)
    assert aut.players == a.players
    for k in aut.players:
        if k in aut.init:
            a.init[k] = list(map(f, aut.init[k]))
        if k in aut.action:
            a.action[k] = list(map(f, aut.action[k]))
    for k in aut.win:
        a.win[k] = list(map(f, aut.win[k]))


def _bitvector_to_bdd(aut):
    players = set(aut.players)
    players.add(None)
    dvars = aut.vars
    dbits = bv.list_bits(dvars, players)
    ordbits = _pick_var_order(dbits)
    levels, prime_map = _prime_vars(ordbits)
    bdd = aut.bdd
    for var, level in levels.items():
        bdd.add_var(var, level)
    partition = _partition_vars(dbits, players)
    a = Automaton()
    a.bdd = bdd
    a.players = copy.deepcopy(aut.players)
    a.vars = copy.deepcopy(aut.vars)
    # auto-populated
    prime = dict()
    for p, pvars in partition.items():
        prime[p] = {
            k: v for k, v in prime_map.items()
            if k in pvars}
    a.prime = prime
    for p, d in a.prime.items():
        a.unprime[p] = {v: k for k, v in d.items()}
    a.turns = {v: k for k, v in aut.players.items()}
    for k in aut.init:
        u = aut.init[k]
        v = list()
        symbolic._to_bdd(u, v, bdd)
        a.init[k] = v
    for k in aut.action:
        u = aut.action[k]
        v = list()
        symbolic._to_bdd(u, v, bdd)
        a.action[k] = v
    for k in aut.win:
        u = aut.win[k]
        v = list()
        symbolic._to_bdd(u, v, bdd)
        a.win[k] = v
    return a


def _pick_var_order(bits):
    # TODO: refine, as in `omega.symbolic.symbolic`
    return list(bits)


def _prime_vars(ordvars, suffix="'"):
    """Return primed and unprimed BDD levels."""
    levels = dict()
    prime = dict()
    for i, var in enumerate(ordvars):
        j = 2 * i
        primed = var + suffix
        levels[var] = j
        levels[primed] = j + 1
        prime[var] = primed
    assert set(ordvars).issubset(levels)
    assert set(prime).issubset(levels)
    return levels, prime


def _partition_vars(dvars, players=None):
    if players is None:
        players = {d['owner'] for d in dvars.values()}
    partition = {p: set() for p in players}
    for var, d in dvars.items():
        p = d['owner']
        partition[p].add(var)
    assert 'all' not in partition, set(partition)
    partition['all'] = set(dvars)
    return partition


def fill_blanks(aut):
    true = 'True'
    # false = 'False'
    for p in aut.players:
        if p not in aut.init:
            aut.init[p] = list()
        if p not in aut.action:
            aut.action[p] = list()
    for d in (aut.init, aut.action):
        for k, v in d.items():
            if not v:
                d[k] = [true]
    # aut.win untouched
    return
