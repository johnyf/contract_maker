"""Decompose GR(1) property into a contract."""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import
import copy
import logging
import pprint
from dd import bdd as _bdd
from omega.automata import TransitionSystem
from omega.symbolic.logicizer import graph_to_logic
from omega.symbolic import enumeration as enum
import symbolic as sym


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
        print(('goal:', goal))
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


def require_closure(z, aut):
    bdd = aut.bdd
    for p in aut.players:
        (action,) = aut.action[p]
        zp = _bdd.rename(z, bdd, aut.prime[p])
        stay = bdd.apply('and', z, zp)
        u = bdd.apply('and', action, stay)
        aut.action[p] = [u]


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
