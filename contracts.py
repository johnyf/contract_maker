"""Decompose GR(1) property into a contract."""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy
import logging
import pprint
from dd import bdd as _bdd
from omega.symbolic import bdd as sym_bdd
from omega.automata import TransitionSystem
from omega.logic import bitvector as bv
from omega.symbolic.logicizer import graph_to_logic
from omega.symbolic import symbolic
from omega.symbolic import enumeration as enum


logger = logging.getLogger(__name__)
log = logging.getLogger('dd.bdd')
log.setLevel(logging.INFO)
log.addHandler(logging.StreamHandler())
log = logging.getLogger('dd.bdd.ply')
log.setLevel(logging.ERROR)


def grid_world_example():
    # robot a
    a = TransitionSystem()
    a.add_path([0, 1, 2, 3, 4, 5, 0])
    a.initial_nodes.add(4)
    n_a = len(a) - 1
    aut_a = graph_to_logic(a, 'a', ignore_initial=False, self_loops=True)
    # robot b
    b = TransitionSystem()
    b.add_path([5, 4, 3, 2, 1, 0, 5])
    b.add_path([2, 6, 2])
    b.add_path([0, 7, 0])
    b.initial_nodes.add(0)
    n_b = len(b) - 1
    aut_b = graph_to_logic(b, 'b', ignore_initial=False, self_loops=True)
    # interleaving repr
    aut = Automaton()
    aut.players = dict(car_a=0, car_b=1)
    n = len(aut.players)
    aut.vars = dict(
        a=dict(type='saturating', dom=(0, n_a), owner='car_a'),
        b=dict(type='saturating', dom=(0, n_b), owner='car_b'),
        _i=dict(type='saturating', dom=(0, n - 1), owner=None))
    aut.init['car_a'] = [aut_a.init['sys'][0]]
    aut.init['car_b'] = [aut_b.init['sys'][0]]
    aut.action['car_a'] = [aut_a.action['sys'][0]]
    aut.action['car_b'] = [aut_b.action['sys'][0]]
    # avoid collisions
    s = "(a != b) & (a' != b)"
    # & ((a = 4) -> (a' != 4))
    aut.action['car_a'].append(s)
    s = "(a != b) & (a != b')"
    # & ((a = 4) -> (b = 1))
    aut.action['car_b'].append(s)
    aut.win['car_a: []<>'] = ['(a = 4)', '(b = 1)']
    aut.win['car_b: []<>'] = ['True']
    fill_blanks(aut)
    print(aut)
    aut = aut.build()
    make_assumptions(aut)


def landing_gear_example():
    aut = Automaton()
    aut.players = dict(autopilot=0, door_module=1, gear_module=2)
    n = len(aut.players)
    aut.vars = dict(
        # 0 = landing, 1 = cruise, 2 = takeoff
        mode=dict(type='saturating', dom=(0, 2), owner='autopilot'),
        # 0 = closed, 2 = open
        door=dict(type='saturating', dom=(0, 2), owner='door_module'),
        # 0 = retracted, 3 = fully extended
        gear=dict(type='saturating', dom=(0, 2), owner='gear_module'),
        # unit: 100 meters
        height=dict(type='saturating', dom=(0, 100), owner='autopilot'),
        # unit: km/h
        speed=dict(type='saturating', dom=(0, 1000), owner='autopilot'),
        _i=dict(type='saturating', dom=(0, n - 1), owner=None))
    aut.action['autopilot'] = [
        "(gear != 2) -> (height > 3)",
        "(speed > 300) -> (door = 0)",
        "(mode = 0) -> (gear = 2)",
        "(mode = 1) -> (gear = 0)",
        "(height = 0) -> (gear = 2)"]
    aut.action['door_module'] = [
        "(speed > 300) -> (door = 0)",
        "(gear != 0) -> (door = 2)"]
    aut.action['gear_module'] = [
        "(gear != 2) -> (height > 3)",
        "(gear != 0) -> (door = 2)",
        "(mode = 0) -> (gear = 2)",
        "(mode = 1) -> (gear = 0)",
        "(height = 0) -> (gear = 2)"]
    aut.win['autopilot: []<>'] = [
        '(mode = 0)',
        '(mode = 1)',
        '(mode = 2)']
    aut.win['gear_module: []<>'] = ['True']
    aut.win['door_module: []<>'] = ['True']
    fill_blanks(aut)
    print(aut)
    aut = aut.build()
    make_assumptions(aut)


def counter_example():
    g = TransitionSystem()
    g.add_path([0, 1, 2, 3, 4])
    g.add_path([5, 6, 7, 0])
    g.add_edge(4, 5, formula="x")
    g.add_edge(4, 1, formula="!x")
    g.add_edge(1, 0)
    g.add_edge(3, 2)
    g.vars = dict(x='bool')
    g.env_vars.add('x')
    # g.dump('sys_graph_2.pdf')
    #
    aut_g = graph_to_logic(g, 'pc', ignore_initial=True)
    #
    aut = Automaton()
    aut.players = dict(alice=0, bob=1)
    aut.vars = dict(
        pc=dict(type='saturating', dom=(0, 7), owner='alice'),
        x=dict(type='bool', owner='bob'),
        _i=dict(type='saturating', dom=(0, 1), owner='alice'))
    aut.action['alice'] = [aut_g.action['sys'][0]]
    aut.win['alice: []<>'] = ['pc = 6']
    aut.win['bob: []<>'] = ['True']
    fill_blanks(aut)
    print(aut)
    aut = aut.build()
    make_assumptions(aut)


def make_assumptions(original_aut):
    aut = copy.copy(original_aut)
    z = closure(aut)
    # print('Cooperative winning set:')
    # enum.print_nodes(z, aut.vars, aut.bdd)
    assert z != aut.bdd.false, 'unsatisfiable'
    require_closure(z, aut)
    specs = nested_specs(z, aut)
    pprint.pprint(specs)
    bdd = aut.bdd
    #
    # uncomment to enumerate constructed assumptions
    #
    return
    print('------------------')
    for c in specs['car_a'][1]:
        j = c[0]
        print('nested spec for player {j}:'.format(j=j))
        print(c)
        print('P_m:')
        u = c[1]
        enum.print_nodes(u, aut.vars, bdd)
        print('Q_m:')
        v = c[2]
        enum.print_nodes(v, aut.vars, bdd)
        print('P_m & ! Q_m:')
        u = aut.bdd.apply('diff', u, v)
        enum.print_nodes(u, aut.vars, bdd)
        print('assumptions: eta = xi')
        assumptions = c[3]
        if not assumptions:
            continue
        for j, k, u in assumptions:
            enum.print_nodes(u, aut.vars, bdd)


def nested_specs(closure, aut):
    print('nested specs')
    specs = dict()
    for p in aut.players:
        print(p)
        spec = nested_spec_for_one_player(closure, p, aut)
        specs[p] = spec
    return specs


def nested_spec_for_one_player(closure, player, aut):
    bdd = aut.bdd
    spec = list()
    s = player + ': []<>'
    if s not in aut.win:
        return spec
    for goal in aut.win[s]:
        print('goal:', goal)
        goal = bdd.apply('and', closure, goal)
        uncovered = bdd.apply('diff', closure, goal)
        stack = list()
        game_stack(goal, player, uncovered, stack, aut, closure)
        # game_stack_shallow(goal, player, uncovered,
        #                    stack, aut, closure)
        spec.append(stack)
    return spec


def game_stack(goal, player, uncovered,
               stack, aut, closure):
    # remember which player should satisfy each assumption
    print('current player: {p}'.format(p=player))
    assert player in aut.players, (player, aut.players)
    n = len(aut.players)
    assert n > 1, n  # termination
    bdd = aut.bdd
    cur_goal = goal
    trap = bdd.true
    assumptions = set()
    # i = aut.players[player]
    while trap != bdd.false:
        trap = bdd.false
        for other in aut.players:
            if other == player:
                continue
            attr, trap = unconditional_assumption(
                cur_goal, player, other, aut)
            # assert
            u = bdd.apply('->', cur_goal, attr)
            assert u == bdd.true, u
            # trim win nodes outside cooperatively win set
            attr = bdd.apply('and', attr, closure)
            trap = bdd.apply('and', trap, closure)
            # update
            cur_goal = bdd.apply('or', attr, trap)
            u = bdd.apply('not', trap)
            if u != bdd.true:
                # print('assumption:', trap)
                assumptions.add((other, trap))
            if trap != bdd.false:
                break
    assert u == bdd.true, u
    assert bdd.apply('->', cur_goal, closure) == bdd.true
    assert bdd.apply('->', goal, closure) == bdd.true
    game = (player, cur_goal, goal, assumptions)
    stack.append(game)
    u = bdd.apply('not', cur_goal)
    uncovered = bdd.apply('and', uncovered, u)
    if uncovered == bdd.false:
        print('covered')
        return
    # tail-recursive
    # find someone who can help (determinacy)
    for next_player in aut.players:
        if next_player == player:
            continue
        cox = ue_preimage(cur_goal, next_player, aut)
        cox = bdd.apply('and', cox, closure)
        if bdd.apply('diff', cox, cur_goal) != bdd.false:
            break
    game_stack(cur_goal, next_player, uncovered,
               stack, aut, closure)


def unconditional_assumption(goal, player, others, aut):
    bdd = aut.bdd
    a = attractor(goal, [player], aut)
    b = attractor(a, others, aut)
    c = _trap(b, [player], aut, unless=a)
    r = bdd.apply('not', a)
    r = bdd.apply('and', b, r)
    r = bdd.apply('and', r, c)
    return a, r


def _unconditional_assumption_single(goal, player, other, aut):
    bdd = aut.bdd
    assert player in aut.players, (player, aut.players)
    a = attractor(goal, [player], aut)
    b = attractor(a, [other], aut)
    c = _trap(b, [player], aut, unless=a)
    r = bdd.apply('not', a)
    r = bdd.apply('and', b, r)
    r = bdd.apply('and', r, c)
    return a, r


def closure(aut):
    bdd = aut.bdd
    z = bdd.true
    zold = None
    while z != zold:
        zold = z
        for p in aut.players:
            zj = closure_for_one_player(zold, p, aut)
            z = bdd.apply('and', zj, z)
    return z


def closure_for_one_player(z, player, aut):
    bdd = aut.bdd
    zj = bdd.true
    zjold = None
    while zj != zjold:
        zjold = zj
        for goal in aut.win[player + ': []<>']:
            y = ancestors(zjold, goal, player, aut)
            zj = bdd.apply('and', y, zj)
        zj = bdd.apply('and', z, zj)
    return zj


def ancestors(z, goal, player, aut):
    bdd = aut.bdd
    z_pre = preimage(z, aut)
    target = bdd.apply('and', z_pre, goal)
    y = bdd.false
    yold = None
    while y != yold:
        yold = y
        y_pre = preimage(yold, aut)
        u = bdd.apply('or', y_pre, target)
        u = bdd.apply('or', yold, u)
        y = u
    return y


def preimage(target, aut):
    """Predecessors with interleaving repr."""
    bdd = aut.bdd
    n = len(aut.players)
    ivar = '_i'
    # needed to force extra steps outside
    pre = bdd.false
    for i, p in aut.turns.iteritems():
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
    for i, p in aut.turns.iteritems():
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
    for i, p in aut.turns.iteritems():
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


def require_closure(z, aut):
    bdd = aut.bdd
    for p in aut.players:
        (action,) = aut.action[p]
        zp = _bdd.rename(z, bdd, aut.prime[p])
        stay = bdd.apply('and', z, zp)
        u = bdd.apply('and', action, stay)
        aut.action[p] = [u]


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
        for k, v in self.init.iteritems():
            s = '\ninit: {k}\n---\n'.format(k=k)
            c.append(s)
            c.extend(v)
        for k, v in self.action.iteritems():
            s = '\naction: {k}\n---\n'.format(k=k)
            c.append(s)
            c.extend(v)
        for k, v in self.win.iteritems():
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
    for k, v in init.iteritems():
        aut.init[k].extend(v)
    for k, v in action.iteritems():
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
            a.init[k] = map(f, aut.init[k])
        if k in aut.action:
            a.action[k] = map(f, aut.action[k])
    for k in aut.win:
        a.win[k] = map(f, aut.win[k])


def _bitvector_to_bdd(aut):
    players = set(aut.players)
    players.add(None)
    dvars = aut.vars
    dbits = bv.list_bits(dvars, players)
    ordbits = _pick_var_order(dbits)
    levels, prime_map = _prime_vars(ordbits)
    bdd = aut.bdd
    for var, level in levels.iteritems():
        bdd.add_var(var, level)
    partition = _partition_vars(dbits, players)
    a = Automaton()
    a.bdd = bdd
    a.players = copy.deepcopy(aut.players)
    a.vars = copy.deepcopy(aut.vars)
    # auto-populated
    prime = dict()
    for p, pvars in partition.iteritems():
        prime[p] = {
            k: v for k, v in prime_map.iteritems()
            if k in pvars}
    a.prime = prime
    for p, d in a.prime.iteritems():
        a.unprime[p] = {v: k for k, v in d.iteritems()}
    a.turns = {v: k for k, v in aut.players.iteritems()}
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
        players = {d['owner'] for d in dvars.itervalues()}
    partition = {p: set() for p in players}
    for var, d in dvars.iteritems():
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
        for k, v in d.iteritems():
            if not v:
                d[k] = [true]
    # aut.win untouched
    return


def game_stack_shallow(goal, player, uncovered,
                       stack, aut, closure):
    # remember which player should satisfy each assumption
    assert player in aut.players, (player, aut.players)
    n = len(aut.players)
    assert n > 1, n  # termination
    bdd = aut.bdd
    cur_goal = goal
    trap = bdd.true
    assumptions = set()
    i = aut.players[player]
    j = i
    while trap != bdd.false:
        j = (j + 1) % n
        if j == i:
            continue
        other = aut.turns[j]
        attr, trap = unconditional_assumption(
            cur_goal, player, other, aut)
        # assert
        u = bdd.apply('->', cur_goal, attr)
        assert u == bdd.true, u
        # trim win nodes outside cooperatively win set
        attr = bdd.apply('and', attr, closure)
        # update
        cur_goal = bdd.apply('or', attr, trap)
        u = bdd.apply('not', trap)
        if u != bdd.true:
            assumptions.add(trap)
    assert u == bdd.true, u
    game = (player, cur_goal, goal, assumptions)
    # u = bdd.apply('not', cur_goal)
    # uncovered = bdd.apply('and', uncovered, u)
    # if uncovered == bdd.false:
    #     return
    # tail-recursive
    # j = (i + 1) % n
    # next_player = aut.turns[j]
    # game_stack(cur_goal, next_player, uncovered,
    #            stack, aut, closure)
    #
    # outer fixpoint reached ?
    cox_goal = ue_preimage(goal, player, aut)
    new_goal = aut.bdd.apply('and', cox_goal, cur_goal)
    if new_goal == goal:
        # print('new_goal:')
        # enum.print_nodes(new_goal, aut.vars, aut.bdd)
        stack.append(game)
        return
    # iterate \nu Z.
    game_stack_shallow(new_goal, player, uncovered,
                       stack, aut, closure)


if __name__ == '__main__':
    landing_gear_example()
