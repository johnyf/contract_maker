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
from omega.symbolic import bdd as scope
from omega.symbolic import enumeration as enum
import symbolic as sym


logger = logging.getLogger(__name__)
log = logging.getLogger('dd.bdd')
log.setLevel(logging.INFO)
log.addHandler(logging.StreamHandler())
log = logging.getLogger('dd.bdd.ply')
log.setLevel(logging.ERROR)


def gridworld_example():
    # car a
    a = TransitionSystem()
    a.add_path([0, 1, 2, 3, 4, 5, 0])
    a.initial_nodes.add(4)
    n_a = len(a) - 1
    aut_a = graph_to_logic(
        a, 'a',
        ignore_initial=False,
        self_loops=True)
    # car b
    b = TransitionSystem()
    b.add_path([5, 4, 3, 2, 1, 0, 5])
    b.add_path([2, 6, 2])
    b.add_path([0, 7, 0])
    b.initial_nodes.add(0)
    n_b = len(b) - 1
    aut_b = graph_to_logic(
        b, 'b',
        ignore_initial=False,
        self_loops=True)
    # interleaving repr
    aut = sym.Automaton()
    aut.players = dict(car_a=0, car_b=1)
    n = len(aut.players)
    table = dict(
        a=dict(type='int', dom=(0, n_a), owner='car_a'),
        b=dict(type='int', dom=(0, n_b), owner='car_b'),
        _i=dict(type='int', dom=(0, n - 1), owner='scheduler'))
    aut.add_vars(table, flexible=True)
    aut.varlist['car_a'] = ['a']
    aut.varlist['car_b'] = ['b']
    s = r'''
        InitA == ({init_a}) /\ (a \in 0 .. {n_a})
        InitB == ({init_b}) /\ (b \in 0 .. {n_b})

        NextA ==
            /\ ({action_a})
               # type invariance action
            /\ a \in 0 .. {n_a}
            /\ a' \in 0 .. {n_a}
               # avoid collisions
            /\ (a != b) /\ (a' != b)
            /\ ((a = 4) => (a' != 4))

        NextB ==
            /\ ({action_b})
               # type invariance action
            /\ b \in 0 .. {n_b}
            /\ b' \in 0 .. {n_b}
               # avoid collisions
            /\ (a != b) /\ (a != b')

        RecurA1 == (a = 4)
        RecurA2 == (b = 1)
        RecurB == True
        '''.format(
            n_a=n_a,
            n_b=n_b,
            init_a=aut_a.init['sys'][0],
            init_b=aut_b.init['sys'][0],
            action_a=aut_a.action['sys'][0],
            action_b=aut_b.action['sys'][0])
    aut.define(s)
    aut.init_expr = dict(
        car_a='InitA',
        car_b='InitB')
    aut.action_expr = dict(
        car_a='NextA',
        car_b='NextB')
    aut.win_expr = dict(
        car_a={'[]<>': ['RecurA1', 'RecurA2']},
        car_b={'[]<>': ['RecurB']})
    print(aut)
    aut.build()
    make_assumptions(aut)


def landing_gear_example():
    aut = sym.Automaton()
    aut.players = dict(autopilot=0, door_module=1, gear_module=2)
    n = len(aut.players)
    k = 10
    table = dict(
        # 0 = landing, 1 = cruise, 2 = takeoff
        mode=dict(type='int', dom=(0, 2), owner='autopilot'),
        # 0 = closed, 2 = open
        door=dict(type='int', dom=(0, 2), owner='door_module'),
        # 0 = retracted, 2 = fully extended
        gear=dict(type='int', dom=(0, 2), owner='gear_module'),
        # unit: 100 meters
        height=dict(type='int', dom=(0, k), owner='autopilot'),
        # unit: km/h
        speed=dict(type='int', dom=(0, k), owner='autopilot'),
        _i=dict(type='int', dom=(0, n - 1), owner=None))
    aut.add_vars(table, flexible=True)
    aut.varlist = dict(
        autopilot=['mode', 'height', 'speed'],
        door_module=['door'],
        gear_module=['gear'])
    s = r'''
        AutopilotInit ==
            /\ mode \in 0 .. 2
            /\ height \in 0 .. {k}
            /\ speed \in 0 .. {k}
        DoorInit == door \in 0 .. 2
        GearInit == gear \in 0 .. 2

        AutopilotNext ==
            /\ ((gear != 2) => (height > {m}))
            /\ ((speed > {m}) => (door = 0))
            /\ ((mode = 0) => (gear = 2))
            /\ ((mode = 1) => (gear = 0))
            /\ ((height = 0) => (gear = 2))
               # type invariance actions
            /\ mode \in 0 .. 2
            /\ mode' \in 0 .. 2
            /\ height \in 0 .. {k}
            /\ height' \in 0 .. {k}
            /\ speed \in 0 .. {k}
            /\ speed' \in 0 .. {k}

        DoorNext ==
            /\ ((speed > {m}) => (door = 0))
            /\ ((gear != 0) => (door = 2))
               # type invariance actions
            /\ door \in 0 .. 2
            /\ door' \in 0 .. 2

        GearNext ==
            /\ ((gear != 2) => (height > {m}))
            /\ ((gear != 0) => (door = 2))
            /\ ((mode = 0) => (gear = 2))
            /\ ((mode = 1) => (gear = 0))
            /\ ((height = 0) => (gear = 2))
               # type invariance actions
            /\ gear \in 0 .. 2
            /\ gear' \in 0 .. 2

        Recur1 == (mode = 0)
        Recur2 == (mode = 1)
        Recur3 == (mode = 2)
        '''.format(k=k, m=int(0.75 * k))
    aut.define(s)
    # this approach is similar to a TLC config file
    aut.init_expr = dict(
        autopilot='AutopilotInit',
        door_module='DoorInit',
        gear_module='GearInit')
    aut.action_expr = dict(
        autopilot='AutopilotNext',
        door_module='DoorNext',
        gear_module='GearNext')
    # if added, this inconsistent formula causes circularity
    # "(speed > 3) => (door = 0)"]
    aut.win_expr = dict(
        autopilot={'[]<>': ['Recur1', 'Recur2', 'Recur3']},
        gear_module={'[]<>': ['TRUE']},
        door_module={'[]<>': ['TRUE']})
    print(aut)
    aut.build()
    make_assumptions(aut)


def counter_example():
    g = TransitionSystem()
    g.add_path([0, 1, 2, 3, 4])
    g.add_path([5, 6, 7, 0])
    g.add_edge(4, 5, formula="x")
    g.add_edge(4, 1, formula="~ x")
    g.add_edge(1, 0)
    g.add_edge(3, 2)
    g.vars = dict(x='bool')
    g.env_vars.add('x')
    # g.dump('sys_graph_2.pdf')
    #
    aut_g = graph_to_logic(g, 'pc', ignore_initial=True)
    #
    aut = sym.Automaton()
    aut.players = dict(alice=0, bob=1)
    table = dict(
        pc=dict(type='saturating', dom=(0, 7), owner='alice'),
        x=dict(type='bool', owner='bob'),
        _i=dict(type='saturating', dom=(0, 1), owner=None))
    aut.add_vars(table, flexible=True)
    aut.varlist = dict(
        alice=['pc'],
        bob=['x'])
    aut.init_expr = dict(
        alice='TRUE',
        bob='TRUE')
    aut.action_expr = dict(
        alice=aut_g.action['sys'][0],
        bob='TRUE')
    aut.win_expr = dict(
        alice={'[]<>': ['pc = 6']},
        bob={'[]<>': ['True']})
    # TODO: sym.fill_blanks(aut)
    print(aut)
    aut.build()
    make_assumptions(aut)


def dummy_example():
    """A smaller version of `landing_gear_example`.

    This was originally written for development and debugging.
    """
    aut = sym.Automaton()
    aut.players = dict(autopilot=0, gear_module=1)
    n = len(aut.players)
    table = dict(
        mode=dict(type='bool', owner='autopilot'),
        speed=dict(type='bool', owner='autopilot'),
        door=dict(type='bool', owner='gear_module'),
        _i=dict(type='saturating', dom=(0, n - 1), owner=None))
    aut.add_vars(table, flexible=True)
    aut.varlist = dict(
        autopilot=['mode', 'speed'],
        gear_module=['door'])
    aut.init_expr = dict(
        autopilot='True',
        gear_module='True')
    s = r'''
           ((~ door) => (~ mode))
        /\ (speed => ~ door))
        '''
    aut.action_expr = dict(
        autopilot=s,
        gear_module=s)
    aut.win_expr = dict(
        autopilot={'[]<>': ['mode']},
        gear_module={'[]<>': ['True']})
    print(aut)
    aut.build()
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
    log.info('nested specs')
    specs = dict()
    for p in aut.players:
        spec = nested_spec_for_one_player(closure, p, aut)
        specs[p] = spec
    return specs


def nested_spec_for_one_player(closure, player, aut):
    log.info('nested specs for player {p}"'.format(p=player))
    spec = list()
    if '[]<>' not in aut.win[player]:
        return spec
    for goal in aut.win[player]['[]<>']:
        goal &= closure
        uncovered = closure & ~ goal
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
    cur_goal = goal
    trap = aut.true
    assumptions = set()
    # i = aut.players[player]
    while trap != aut.false:
        trap = aut.false
        for other in aut.players:
            if other == player:
                continue
            attr, trap = unconditional_assumption(
                cur_goal, player, other, aut)
            # assert
            u = ~ cur_goal | attr
            assert u == aut.true, u
            # trim win nodes outside cooperatively win set
            attr &= closure
            trap &= closure
            # update
            cur_goal = attr | trap
            u = ~ trap
            if u != aut.true:
                # print('assumption:', trap)
                assumptions.add((other, trap))
            if trap != aut.false:
                break
    assert u == aut.true, u
    assert (~ cur_goal | closure) == aut.true
    assert (~ goal | closure) == aut.true
    game = (player, cur_goal, goal, assumptions)
    stack.append(game)
    u = ~ cur_goal
    uncovered = uncovered & u
    if uncovered == aut.false:
        print('covered')
        return
    # tail-recursive
    # find someone who can help (determinacy)
    for next_player in aut.players:
        if next_player == player:
            continue
        cox = sym.ue_preimage(cur_goal, next_player, aut)
        cox &= closure
        if (cox & ~ cur_goal) != aut.false:
            break
    game_stack(cur_goal, next_player, uncovered,
               stack, aut, closure)


def unconditional_assumption(goal, player, others, aut):
    a = sym.attractor(goal, [player], aut)
    b = sym.attractor(a, others, aut)
    c = sym._trap(b, [player], aut, unless=a)
    r = ~ a
    r &= b
    r &= c
    return a, r


def _unconditional_assumption_single(goal, player, other, aut):
    assert player in aut.players, (player, aut.players)
    a = sym.attractor(goal, [player], aut)
    b = sym.attractor(a, [other], aut)
    c = sym._trap(b, [player], aut, unless=a)
    r = ~ a
    r &= b
    r &= c
    return a, r


def closure(aut):
    """Return cooperatively winning set.

    This is the non-restrictive safety assumption
    with the minimal number of edges.


    Reference
    =========

    Martin Abadi and Leslie Lamport
        "Conjoining specifications"
        TOPLAS, 1995

    Krishnendu Chatterjee, Thomas Henzinger, Barbara Jobstmann
        "Environment assumptions for synthesis"
        CONCUR, 2008
    """
    # TODO: show that correctness follows from the
    # chaotic iteration theorem of Cousot^2
    z = aut.true
    zold = None
    while z != zold:
        zold = z
        for p in aut.players:
            z &= closure_for_one_player(zold, p, aut)
    return z


def closure_for_one_player(z, player, aut):
    zj = aut.true
    zold = None
    while zj != zold:
        zold = zj
        for goal in aut.win[player]['[]<>']:
            zj &= ancestors(zold, goal, aut)
        zj &= z
    return zj


def ancestors(z, goal, aut):
    z_pre = sym.preimage(z, aut)
    target = z_pre & goal
    y = aut.false
    yold = None
    while y != yold:
        yold = y
        y_pre = sym.preimage(y, aut)
        y |= y_pre | target
    return y


def require_closure(z, aut):
    """Apply closure to both players."""
    n = len(aut.players)
    xy = aut.all_player_vars
    vrs = xy | {sym.TURN}
    assert scope.support_issubset(z, vrs, aut)
    for p, i in aut.players.items():
        xi = set(aut.varlist[p])
        ip = (i + 1) % n
        zi = aut.let({sym.TURN: i}, z)
        u = aut.replace_with_primed(xi, z)
        zi_next = aut.let({sym.TURN: ip}, u)
        stay = zi & zi_next
        aut.action[p] &= stay
        # assert
        xip = set(aut.prime_vars(xi))
        vrs = xy | xip
        assert scope.support_issubset(stay, vrs, aut)
        # redundant as extra guard
        assert sym.TURN not in aut.support(stay)


def game_stack_shallow(
        goal, player, uncovered,
        stack, aut, closure):
    # remember which player should satisfy each assumption
    assert player in aut.players, (player, aut.players)
    n = len(aut.players)
    assert n > 1, n  # termination
    cur_goal = goal
    trap = aut.true
    assumptions = set()
    i = aut.players[player]
    j = i
    while trap != aut.false:
        j = (j + 1) % n
        if j == i:
            continue
        other = aut.turns[j]
        attr, trap = unconditional_assumption(
            cur_goal, player, other, aut)
        # assert
        u = attr | ~ cur_goal
        assert u == aut.true, u
        # trim win nodes outside cooperatively win set
        attr &= closure
        # update
        cur_goal = attr | trap
        u = ~ trap
        if u != aut.true:
            assumptions.add(trap)
    assert u == aut.true, u
    game = (player, cur_goal, goal, assumptions)
    # u = ~ cur_goal
    # uncovered &= u
    # if uncovered == aut.false:
    #     return
    # tail-recursive
    # j = (i + 1) % n
    # next_player = aut.turns[j]
    # game_stack(cur_goal, next_player, uncovered,
    #            stack, aut, closure)
    #
    # outer fixpoint reached ?
    cox_goal = sym.ue_preimage(goal, player, aut)
    new_goal = cox_goal & cur_goal
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
