"""Functions relevant to closure, for the noninterleaving case."""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import copy

import ballpark
import humanize
from omega.logic import syntax as stx
from omega.symbolic import bdd as scope

import fixpoint_noninterleaving
import symbolic as sym
import utils


TURN = utils.TURN


def unzip(inv, players, aut):
    """Return new automaton with an action for each player.

    The action of player `k` is:

        ComponentNext == \E x':
            /\ Inv /\ Inv'
            /\ AssemblyNext

    `inv` is applied over the conjunction of actions of
    `players`, which are then unzipped.

    Caution: Actions of keys in `aut.players` that are not in
    `players` are omitted from the returned `new_aut.players`.
    """
    assert scope.is_state_predicate(inv), aut.support(inv)
    assembly_next = preserve_invariant(inv, players, aut)
    new_aut = copy.copy(aut)
    for player in players:
        others = set(players)
        others.remove(player)
        env_vars = aut.vars_of_players(others)
        env_vars_p = aut.prime_vars(env_vars)
        sys_next = aut.exist(env_vars_p, assembly_next)
        assert sym.is_action_of_player(sys_next, player, aut)
        new_aut.action[player] = sys_next
    assert set(new_aut.action) == set(players), (
        new_aut.action, players)
    return new_aut


def hide_vars_from_sys(vrs, inv, sys_player, aut):
    """Return new `sys_player` action, after hiding `vrs`.

    The variables `vrs` to be hidden are already selected.
    So this function is suitable for generating the component
    specifications after the parametric analysis has been
    completed.
    """
    turn_type = aut.vars[TURN]['type']
    turn_p = stx.prime(TURN)
    assert turn_type == 'int', turn_type
    turn_dom = aut.vars[TURN]['dom']
    # extract full-info actions from assembly action
    action = sym.conj_actions_of(aut.players, aut)
    inv_p = aut.replace_with_primed(
        aut.vars_of_all_players, inv)
    assembly_next = inv & inv_p & action
    others = set(aut.players)
    others.remove(sys_player)
    # notice the symmetry
    sys_vars = aut.vars_of_players([sys_player])
    sys_vars_p = aut.prime_vars(sys_vars)
    env_vars = aut.vars_of_players(others)
    env_vars_p = aut.prime_vars(env_vars)
    extracted_sys_next = aut.exist(env_vars_p, assembly_next)
    extracted_env_next = aut.exist(sys_vars_p, assembly_next)
    # decompile `SysStep`
    k = aut.players[sys_player]
    kp = increment_turn(k, turn_dom)
    u = aut.let({TURN: k}, extracted_sys_next)
    inv_proj = aut.let({TURN: k}, inv)
    v = aut.let({turn_p: kp}, inv_p)
    inv_p_proj = aut.exist(env_vars_p, v)
    care = inv_proj & inv_p_proj
    s = sym.dumps_expr(u, aut, care=care)
    print('ExtractedSysStep ==')
    print(s)
    # hide variables from `SysNext`
    sys_next = extracted_sys_next
    u = sys_next | ~ inv
    u = aut.forall(vrs, u)
    inv_h = aut.exist(vrs, inv)
    simpler_sys_next = u & inv_h
    # hide variables from `EnvNext`
    env_next = extracted_env_next
    u = env_next & inv
    vrs_p = aut.prime_vars(vrs)
    qvars = set(vrs).union(vrs_p)
    simpler_env_next = aut.exist(qvars, u)
    # decompile `inv_h`
    s = sym.dumps_expr(inv_h, aut, use_types=True)
    print('InvH == \E h:  Inv <=>')
    print(s)
    # decompile `SimplerSysNext`
    k = aut.players[sys_player]
    u = aut.let({TURN: k}, simpler_sys_next)
    inv_h_p = aut.replace_with_primed(
        aut.vars_of_all_players, inv_h)
    inv_h_p = aut.exist(env_vars_p, inv_h_p)
    assert stx.prime(TURN) not in aut.support(inv_h_p)
    inv_h_proj = aut.let({TURN: k}, inv_h)
    care = inv_h_proj & inv_h_p
    s = sym.dumps_expr(u, aut, care=inv_h, use_types=True)
    print('SimplerSysNext ==')
    print(s)
    # decompile `SimplerEnvNext`
    inv_h_p = aut.replace_with_primed(
        aut.vars_of_all_players, inv_h)
    inv_h_p = aut.exist(sys_vars_p, inv_h_p)
    for player, k in aut.players.items():
        if player == sys_player:
            continue
        if k is None:
            print('Scheduler skipped (plays concurrently)')
            continue
        inv_h_proj = aut.let({TURN: k}, inv_h)
        s = sym.dumps_expr(inv_h_proj, aut, use_types=True)
        print('InvH{player} == '.format(player=player))
        print(s)
        # use (known) scheduler action as care set
        kp = increment_turn(k, turn_dom)
        scheduler_action = {TURN: k, turn_p: kp}
        u = aut.let(scheduler_action, simpler_env_next)
        inv_h_p_proj = aut.let({turn_p: kp}, inv_h_p)
        care = inv_h_proj & inv_h_p_proj
        s = sym.dumps_expr(u, aut, care=inv_h, use_types=True)
        print('Simpler{player}Next == '.format(player=player))
        print(s)


def increment_turn(k, dom):
    a, b = dom
    assert a <= k and k <= b, (a, b, k)
    if k + 1 > b:
        kp = a
    else:
        kp = k + 1
    return kp


def enabled(action, aut):
    """Return `ENABLED action`."""
    support = aut.support(action)
    primed_vars = [var for var in support if stx.is_primed(var)]
    r = aut.exist(primed_vars, action)
    assert scope.is_state_predicate(r), aut.support(r)
    return r


def preserve_invariant(inv, players, aut):
    """Return `AssemblyNext`.

    AssemblyNext ==
        /\ Inv /\ Inv'
        /\ \A k:  ComponentAction(k)
    """
    assert scope.is_state_predicate(inv), aut.support(inv)
    action = sym.conj_actions_of(players, aut)
    assert scope.is_proper_action(action), aut.support(action)
    inv_p = aut.replace_with_primed(
        aut.vars_of_all_players, inv)
    assert sym.is_primed_state_predicate(inv_p, aut), aut.support(inv_p)
    assembly_next = inv & inv_p & action
    assert scope.is_proper_action(assembly_next), aut.support(assembly_next)
    return assembly_next


def closure(players, aut):
    """Return cooperatively winning set."""
    z = aut.true
    zold = None
    while z != zold:
        zold = z
        for p in players:
            z &= closure_for_one_player(zold, p, aut)
    return z


def closure_for_one_player(z, player, aut):
    """Closure that accounts for recurrence goals of `player`."""
    zold = None
    while z != zold:
        zold = z
        z_pre = fixpoint_noninterleaving.preimage(zold, aut)
        for goal in aut.win[player]['[]<>']:
            target = z_pre & goal
            z &= ancestors(target, aut)
    return z


def ancestors(target, aut):
    """States from where `target` is cooperatively reachable."""
    operator = fixpoint_noninterleaving.preimage
    return least_fixpoint(operator, target, aut)


def least_fixpoint(operator, target, aut):
    """Least fixpoint of `operator`, starting from `target`.

    Viewed equivalently, least fixpoint of `operator | target`,
    starting from FALSE.
    """
    y = target
    yold = None
    while y != yold:
        yold = y
        y |= operator(y, aut)
    return y


def print_state_space_statistics(inv, aut):
    """Print number of states that satisfy state predicate `inv`."""
    care_vars = aut.vars_of_all_players
    u = aut.exist([TURN], inv)
    n = aut.count(inv, care_vars=care_vars)
    care_vars.remove(TURN)
    m = aut.count(u, care_vars=care_vars)
    n = ballpark.ballpark(n)
    m = ballpark.ballpark(m)
    print((
        'number of states: {n} (with variable `i`), '
        '{m} (w/o `i`)').format(n=n, m=m))
