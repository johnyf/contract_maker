"""Contracts with hiding."""
# Copyright 2016-2017 by Ioannis Filippidis
# Copyright 2016-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
# Author: Ioannis Filippidis
import copy
from distutils.version import StrictVersion
import logging
import pprint

from dd import cudd
from omega.logic import syntax as stx
from omega.symbolic import bdd as scope
from omega.symbolic import bdd as sym_bdd
import omega
assert StrictVersion(omega.__version__) >= StrictVersion('0.1.0')

import symbolic as sym


log = logging.getLogger(__name__)
LOG = 100


def landing_gear_example():
    """Example with three components."""
    log.info('---- landing gear example ----')
    aut = Automaton()
    aut.bdd.configure(
        max_memory=2 * cudd.GB,
        max_cache_hard=2**25)
    # large
    MAX_HEIGHT = 4000
    MAX_SPEED = 1000
    DOOR_DOWN = 5
    GEAR_DOWN = 5
    # small
    # MAX_HEIGHT = 100
    # MAX_SPEED = 20
    # DOOR_DOWN = 2
    # GEAR_DOWN = 2
    # turns (otherwise `varlist` suffices to declare players)
    aut.players = dict(
        autopilot=0,
        door_module=1,
        gear_module=2)
    n = len(aut.players)
    vrs = dict(
        mode=(0, 2),
        height=(0, MAX_HEIGHT),
        speed=(0, MAX_SPEED),
        door=(0, DOOR_DOWN),
        gear=(0, GEAR_DOWN))
    constants = {
        sym.TURN: (0, n - 1)}
    aut.declare_variables(**vrs)
    aut.declare_constants(**constants)
    aut.varlist = dict(
        autopilot=['mode', 'height', 'speed'],
        door_module=['door'],
        gear_module=['gear'])
    s = r'''
        AutopilotInit ==
            /\ mode \in 0 .. 2
            /\ height \in 0 .. {max_height}
            /\ speed \in 0 .. {max_speed}
        DoorInit == door \in 0 .. {door_down}
        GearInit == gear \in 0 .. {gear_down}

        AutopilotNext ==
            /\ ((gear != {gear_down}) => (height > {threshold_height}))
            /\ ((gear != {gear_down}) => (height' > {threshold_height}))
            #
            /\ ((speed > {threshold_speed}) => (door = 0))
            /\ ((speed' > {threshold_speed}) => (door = 0))
            #
            /\ ((mode = 0) => (gear = {gear_down}))
            /\ ((mode' = 0) => (gear = {gear_down}))
            #
            /\ ((mode = 1) => (gear = 0))
            /\ ((mode' = 1) => (gear = 0))
            #
            /\ ((height = 0) => (gear = {gear_down}))
            /\ ((height' = 0) => (gear = {gear_down}))
            #
            /\ speed' - speed > -20
            /\ speed' - speed < 20
               # type invariance actions
            /\ mode \in 0 .. 2
            /\ mode' \in 0 .. 2
            /\ height \in 0 .. {max_height}
            /\ height' \in 0 .. {max_height}
            /\ speed \in 0 .. {max_speed}
            /\ speed' \in 0 .. {max_speed}
        DoorNext ==
            /\ ((speed > {threshold_speed}) => (door = 0))
            /\ ((speed > {threshold_speed}) => (door' = 0))
            #
            /\ ((gear != 0) => (door = {door_down}))
            /\ ((gear != 0) => (door' = {door_down}))
            #
            /\ door' - door >= -1
            /\ door' - door <= 1
               # type invariance actions
            /\ door \in 0 .. {door_down}
            /\ door' \in 0 .. {door_down}
        GearNext ==
            /\ ((gear != {gear_down}) => (height > {threshold_height}))
            /\ ((gear' != {gear_down}) => (height > {threshold_height}))
            #
            /\ ((gear != 0) => (door = {door_down}))
            /\ ((gear' != 0) => (door = {door_down}))
            #
            /\ ((mode = 0) => (gear = {gear_down}))
            /\ ((mode = 0) => (gear' = {gear_down}))
            #
            /\ ((mode = 1) => (gear = 0))
            /\ ((mode = 1) => (gear' = 0))
            #
            /\ ((height = 0) => (gear = {gear_down}))
            /\ ((height = 0) => (gear' = {gear_down}))
            #
            /\ gear' - gear >= -1
            /\ gear' - gear <= 1
               # type invariance actions
            /\ gear \in 0 .. {gear_down}
            /\ gear' \in 0 .. {gear_down}
        '''.format(
            max_height=MAX_HEIGHT,
            max_speed=MAX_SPEED,
            threshold_height=int(0.75 * MAX_HEIGHT),
            threshold_speed=int(0.75 * MAX_SPEED),
            door_down=DOOR_DOWN,
            gear_down=GEAR_DOWN)
    aut.define(s)
    aut.init_expr = dict(
        autopilot='AutopilotInit',
        door_module='DoorInit',
        gear_module='GearInit')
    aut.action_expr = dict(
        autopilot='AutopilotNext',
        door_module='DoorNext',
        gear_module='GearNext')
    aut.win_expr = dict(
        autopilot={
            '[]<>': ['mode = 0', 'mode = 1', 'mode = 2']},
        gear_module={'[]<>': ['TRUE']},
        door_module={'[]<>': ['TRUE']})
    aut.build()
    aut.assert_consistent()
    log.info('==== landing gear example ====\n')
    return aut


def add_masks_and_hidden_vars(aut, phase):
    """Declare mask and bound hidden vars."""
    # to allow for other lists `aut.varlist`
    player_varlists = {
        k: v for k, v in aut.varlist.items()
        if k in aut.players}
    # make aux vars
    masks, map_to_mask = make_masks(player_varlists, aut.vars, phase)
    t = make_hidden_and_let_vars(player_varlists, aut.vars)
    hidden_vars, map_to_hidden, let_vars, map_to_let = t
    # declare aux symbols
    aut.declare_constants(**masks)
    aut.declare_constants(**let_vars)
    aut.declare_variables(**hidden_vars)
    # store maps
    # all vars are keys, but "x" more readable in usage
    aut.masks_of = map_to_mask
    aut.xy_to_h = map_to_hidden
    aut.xy_to_r = map_to_let
    aut.masks.update(masks)


def make_masks(varlists, decls, phase):
    """Return dictionaries for declaring mask variables."""
    masks = dict()
    map_to_mask = dict()
    for player in varlists:
        player_masks, player_map = masks_for_player(
            player, varlists, decls, phase)
        masks.update(player_masks)
        map_to_mask[player] = player_map
        log.debug((
            'masks for player "{player}":\n'
            '{player_masks}').format(
                player=player,
                player_masks=pprint.pformat(player_masks)))
    return masks, map_to_mask


def masks_for_player(player, varlists, decls, phase):
    """Return mask bits for what `player` receives."""
    log.debug((
        '\ndeclaring mask bits for what info '
        'player "{player}" receives').format(player=player))
    masks = dict()
    map_to_mask = dict()
    for other, vrs in varlists.items():
        if other == player:
            continue
        log.debug('info from player "{other}"'.format(other=other))
        for var in vrs:
            mask = '{player}_mask_{var}_{phase}'.format(
                player=player, var=var, phase=phase)
            log.debug((
                'if mask `{mask} = TRUE`, then player '
                '{player} cannot see variable "{var}"').format(
                    mask=mask, player=player, var=var))
            masks[mask] = (0, 1)
            map_to_mask[var] = mask
    return masks, map_to_mask


def make_hidden_and_let_vars(varlists, decls):
    """Return a hidden var name for each player flexible var.

    These variables are going to be universally quantified.

    @return: declarations of hidden variables, and
        `dict` that maps each visible variable to a hidden one.
    """
    log.info('---- make hidden vars ----')
    hidden_vars = dict()
    map_to_hidden = dict()
    let_vars = dict()
    map_to_let = dict()
    for player, vrs in varlists.items():
        for var in vrs:
            dom = decls[var]['dom']
            assert len(dom) == 2, dom
            # hidden var
            hidden = '{var}_hidden'.format(var=var)
            hidden_vars[hidden] = tuple(dom)
            map_to_hidden[var] = hidden
            # let var
            let = '{var}_let'.format(var=var)
            let_vars[let] = tuple(dom)
            map_to_let[var] = let
            log.debug((
                'visible var: "{v}", '
                'hidden var: "{h}", '
                'let var: "{r}"'
                ).format(
                    v=var, h=hidden, r=let))
    log.info('==== make hidden vars ====')
    return hidden_vars, map_to_hidden, let_vars, map_to_let


def masking_predicates(player, env_vars, aut):
    """Return substitution of hidden variables."""
    masks = aut.masks_of[player]
    selector = '''
        {r} = ( IF {mask} = 1
                    THEN {h}
                    ELSE {var} )
        '''
    c = list()
    for var in env_vars:
        mask = masks[var]
        h = aut.xy_to_h[var]
        r = aut.xy_to_r[var]
        s = selector.format(
            r=r, mask=mask, h=h, var=var)
        c.append(s)
    s = stx.conj(c, op='/\\', sep='\n')
    # print('selector expression: \n {s}'.format(s=s))
    return s


def preserve_invariant(inv, aut):
    r"""Constrain each `aut.action` to preserve `inv`."""
    assert sym_bdd.is_state_predicate(inv), aut.support(inv)
    n = len(aut.players)
    xy = aut.all_player_vars
    vrs = xy | {sym.TURN}
    assert sym_bdd.support_issubset(inv, vrs, aut)
    for p, i in aut.players.items():
        xi = set(aut.varlist[p])
        ip = (i + 1) % n
        zi = aut.let({sym.TURN: i}, inv)
        u = aut.replace_with_primed(xi, inv)
        zi_next = aut.let({sym.TURN: ip}, u)
        stay = zi & zi_next
        aut.action[p] &= zi & zi_next
        # assert
        xip = set(aut.prime_vars(xi))
        vrs = xy | xip
        assert sym_bdd.support_issubset(stay, vrs, aut)
        assert sym.TURN not in aut.support(stay)


def observable_predicate(
        target, player, aut):
    """Return states that `player` can tell satisfy `target`."""
    # This allows the strategy to update memory based
    # on observations in steps that the player does not move.
    # The game is turn-based with round-robin scheduling,
    # so this does not make any difference with observing
    # only at steps that the player moves.
    assert player in aut.players, (player, aut.players)
    assert scope.is_state_predicate(target)
    assert scope.is_state_predicate(aut.inv)
    x = collect_env_vars([player], aut.players, aut)
    y = set(aut.varlist[player])
    h = {aut.xy_to_h[var] for var in x}
    r = {aut.xy_to_r[var] for var in x}
    h = _comma_join(h)
    r = _comma_join(r)
    selector = masking_predicates(player, x, aut)
    # rename
    x_to_r = {
        k: v for k, v in aut.xy_to_r.items() if k in x}
    inv_r = aut.let(x_to_r, aut.inv)
    target_r = aut.let(x_to_r, target)
    # Observable(x, y, m, i) ==
    #     \A h:
    #         LET
    #             r == Mask(m, h, x)
    #         IN
    #             \/ ~ Inv(r, y, m, i)
    #             \/ Target(r, y, m, i)
    # \equiv
    #     \A h:  \E r:
    #         /\ r = (IF m = TRUE THEN h ELSE x)
    #         /\ \/ ~ Inv(r, y, m, i)
    #            \/ Target(r, y, m, i)
    s = r'''
        \A {h}:  \E {r}:  (
            /\ {selector}
            /\ ( \/ ( ~ @{inv})
                 \/ @{target} ) )
        '''.format(
            h=h, r=r,
            selector=selector,
            inv=inv_r,
            target=target_r)
    u = aut.add_expr(s)
    vrs = aut.all_player_vars | aut.masks | {sym.TURN}
    assert scope.support_issubset(u, vrs, aut)
    return u


def project_on_observer(
        target, aut, pred=None):
    """Return `aut.observer` states that could satisfy `target`."""
    if pred is None:
        pred = aut.inv
    assert scope.is_state_predicate(target)
    assert scope.is_state_predicate(aut.inv)
    x = collect_env_vars(aut.visible, aut.players, aut)
    # y = set(aut.varlist[observer])
    h = {aut.xy_to_h[var] for var in x}
    r = {aut.xy_to_r[var] for var in x}
    h = _comma_join(h)
    r = _comma_join(r)
    selector = masking_predicates(aut.observer, x, aut)
    # rename
    x_to_r = {
        k: v for k, v in aut.xy_to_r.items() if k in x}
    inv_r = aut.let(x_to_r, pred)
    target_r = aut.let(x_to_r, target)
    # Project(x, y, m, i) ==
    #     \E h:
    #         LET
    #             r == Mask(m, h, x)
    #         IN
    #             /\ Inv(r, y, m, i)
    #             /\ Target(r, y, m, i)
    # \equiv
    #     \E h, r:
    #         /\ r = (IF m = TRUE THEN h ELSE x)
    #         /\ Inv(r, y, m, i)
    #         /\ Target(r, y, m, i)
    s = r'''
        \E {h}, {r}:  (
            /\ {selector}
            /\ @{target}
            /\ @{inv} )
        '''.format(
            h=h, r=r,
            selector=selector,
            inv=inv_r,
            target=target_r)
    u = aut.add_expr(s)
    assert scope.is_state_predicate(u)
    # vrs = aut.all_player_vars | aut.masks | {sym.TURN}
    # assert scope.support_issubset(u, vrs, aut)
    return u


def sys_pre_under_pinfo(
        target, player, aut):
    """Return CPre for `player` component as system.

    `aut.inv`: shared (invisible) invariant
    `aut.visible`: omit masks for vars of these players
    `aut.players`: all players (`dict` that maps to turns)

    @param player: this step changes vars of no other player
    """
    assert scope.is_state_predicate(target)
    assert set(aut.visible).issubset(aut.players), aut.visible
    assert player in aut.players, (player, aut.players)
    check_support_inv_target(target, aut.inv, aut)
    x = collect_env_vars(aut.visible, aut.players, aut)
    y = set(aut.varlist[player])
    log.debug('env vars: {x}'.format(x=x))
    log.debug('system vars: {y}'.format(y=y))
    # action, qvars
    sys_action = aut.action[player]
    selector = masking_predicates(aut.observer, x, aut)
    yp = aut.prime_vars(y)
    h = {aut.xy_to_h[var] for var in x}
    r = {aut.xy_to_r[var] for var in x}
    yp = _comma_join(yp)
    h = _comma_join(h)
    r = _comma_join(r)
    # turn tracking
    n = len(aut.players)
    i = aut.players[player]
    assert i >= 0, i
    assert i < n, (i, n)
    ip = (i + 1) % n
    log.debug('yp vars: {yp}'.format(yp=yp))
    log.debug('h vars: {h}'.format(h=h))
    log.debug('r vars: {r}'.format(r=r))
    log.debug('selector: ' + selector)
    # rename
    x_to_r = {
        k: v for k, v in aut.xy_to_r.items() if k in x}
    u = aut.let({sym.TURN: i}, aut.inv)
    inv_r_y = aut.let(x_to_r, u)
    u = aut.let({sym.TURN: ip}, target)
    u = aut.replace_with_primed(y, u)
    target_r_yp_m = aut.let(x_to_r, u)
    sys_action_r_y_yp = aut.let(x_to_r, sys_action)
    if h:
        h_expr = '\A {h}: '.format(h=h)
    else:
        h_expr = ''
    if r:
        r_expr = '\E {r}: '.format(r=r)
    else:
        r_expr = ''
    # SysPre(x, y, m) ==
    #     /\ \E h:
    #         LET
    #             r = (IF m = TRUE THEN h ELSE x)
    #         IN
    #             Inv(r, y)
    #     \E y':  \A h:
    #         LET
    #             r = (IF m = TRUE THEN h ELSE x)
    #         IN
    #             \/ ~ Inv(r, y)
    #             \/ /\ SysNext(r, y, y')
    #                /\ Target(r, y', m)
    # \equiv
    #     \E y':  \A h:  \E r:
    #         /\ r = IF m = TRUE THEN h ELSE x
    #         /\ \/ ~ Inv(r, y)
    #            \/ /\ SysNext(r, y, y')
    #               /\ Target(r, y', m)
    s = r'''
        \E {yp}:  {h_expr}  {r}  (
            /\ {selector}
            /\ ( \/ (~ @{inv})
                 \/ ( /\ @{sys_action}
                      /\ @{target} ) ) )
        '''.format(
            yp=yp, h_expr=h_expr, r=r_expr,
            selector=selector,
            inv=inv_r_y,
            sys_action=sys_action_r_y_yp,
            target=target_r_yp_m)
    # print('SysPre: {s}'.format(s=s))
    u = aut.add_expr(s)
    assert sym_bdd.is_state_predicate(u)
    vrs = aut.all_player_vars | aut.masks
    assert sym_bdd.support_issubset(u, vrs, aut), aut.support(u)
    # turn tracking
    u = sym.and_turn(u, i, aut)
    return u


def env_pre_under_pinfo(
        target, env_player, aut):
    """Return CPre for a single uncontrolled component."""
    assert scope.is_state_predicate(target)
    assert set(aut.visible).issubset(aut.players), aut.visible
    assert env_player in aut.players, (env_player, aut.players)
    check_support_inv_target(target, aut.inv, aut)
    x = collect_env_vars(aut.visible, aut.players, aut)
    # action, qvars
    selector = masking_predicates(aut.observer, x, aut)
    i = aut.players[env_player]
    env_action = aut.action[env_player]
    xi = set(aut.varlist[env_player])
    xip = aut.prime_vars(xi)
    h = {aut.xy_to_h[var] for var in x}
    r = {aut.xy_to_r[var] for var in x}
    xip = _comma_join(xip)
    h = _comma_join(h)
    r = _comma_join(r)
    # turn tracking
    n = len(aut.players)
    assert i >= 0, i
    assert i < n, (i, n)
    ip = (i + 1) % n
    log.debug('xip vars: {xip}'.format(xip=xip))
    log.debug('h vars: {h}'.format(h=h))
    log.debug('r vars: {r}'.format(r=r))
    # rename
    x_to_r = {
        k: v for k, v in aut.xy_to_r.items() if k in x}
    u = aut.let({sym.TURN: i}, aut.inv)
    inv_r_y = aut.let(x_to_r, u)
    u = aut.let({sym.TURN: ip}, target)
    u = aut.replace_with_primed(xi, u)
    # no xi in support, so just rename all vars in r
    target_rbari_y_xip_m = aut.let(x_to_r, u)
    env_action_r_y_xip = aut.let(x_to_r, env_action)
    # In principle, we could skip hiding here, because done
    # anyway in the team player turns, as they play and
    # observe.
    #
    # EnvPre(x, y, m) ==
    #     \A h, h', x':
    #         LET
    #             r = (IF m = TRUE THEN h ELSE x)
    #         IN
    #             \/ ~ /\ Inv(r, y)
    #                  /\ EnvNext(r, y, x_i')
    #             \/ Target(\bar{r}_i, y, x_i', m)
    # \equiv
    #     \A h, h', x':   \E r:
    #         /\ r = (IF m = TRUE THEN h ELSE x)
    #         /\ \/ ~ /\ Inv(r, y)
    #                 /\ EnvNext(r, y, x_i')
    #            \/ Target(\bar{r}_i, y, x_i', m)
    s = r'''
        \A {h}, {xip}:  \E {r}:  (
            /\ {selector}
            /\ ( \/ ( ~ ( /\ @{inv}
                          /\ @{env_action} ) )
                 \/ @{target} ) )
        '''.format(
            xip=xip, h=h, r=r,
            selector=selector,
            inv=inv_r_y,
            env_action=env_action_r_y_xip,
            target=target_rbari_y_xip_m)
    u = aut.add_expr(s)
    assert sym_bdd.is_state_predicate(u)
    vrs = aut.all_player_vars | aut.masks
    assert sym_bdd.support_issubset(u, vrs, aut), aut.support(u)
    # turn tracking
    u = sym.and_turn(u, i, aut)
    return u


def check_support_inv_target(target, inv, aut):
    """Raise `AssertionError` if any support is wrong."""
    xy = aut.all_player_vars
    # Target(x, y, m, i)
    vrs = xy | aut.masks | {sym.TURN}
    assert sym_bdd.support_issubset(target, vrs, aut)
    assert sym_bdd.is_state_predicate(target)
    # Inv(x, y, i)  top level
    # Inv(x, y, m, i)  during assumption computation
    assert sym_bdd.is_state_predicate(inv)
    vrs = xy | aut.masks | {sym.TURN}
    assert sym_bdd.support_issubset(inv, vrs, aut)


def assert_is_inductive_inv(inv, init, action, aut):
    """Assert `inv` is inductive invariant wrt `init, action`."""
    # init => inv
    assert init != aut.false, 'vacuous'
    u = inv | ~ init
    assert u == aut.true, u
    # (inv /\ action) => inv
    inv_next = sym_bdd.prime(inv)
    u = inv & action
    assert u != aut.false, 'vacuous'
    u = inv_next | ~ u
    u = aut.forall(aut.all_player_vars, u)
    assert u == aut.true, u


def diagnose_not_inductive_inv(inv, action, aut):
    """Print minimal cover for violating moves."""
    inv_next = sym_bdd.prime(inv)
    not_inv_next = ~ inv_next
    u = inv & action
    u &= not_inv_next
    i0 = aut.add_expr('i = 0')
    u &= i0
    u = aut.exist(aut.all_player_vars, u)
    # print(aut.support(u))
    print('diagnosis why not an inductive invariant:')
    s = aut.to_expr(u)
    print(s)


def assert_greatest_fixpoint(inv, action, aut):
    """Assert that outside `inv` the `action` leads to deadends.

    \A x, y:
    \E x', y':
        (~ inv /\ action) => (\A x', y': ~ action)'
    """
    inv_next = sym_bdd.prime(inv)
    not_inv_next = ~ inv_next
    all_primed = aut.prime_vars(aut.all_player_vars)
    blocked = aut.forall(all_primed, ~not_inv_next)
    blocked_next = sym_bdd.prime(blocked)
    not_inv = ~ inv
    u = not_inv & blocked
    u = blocked_next | ~ u
    u = aut.exist(all_primed, u)
    u = aut.forall(aut.all_player_vars, u)
    support = aut.support(u)
    assert not support, support
    assert u == aut.true


# essentially same with `synthesizer.contracts`
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
    zold = None
    while z != zold:
        zold = z
        for goal in aut.win[player]['[]<>']:
            z &= ancestors(zold, goal, aut)
    return z


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


def collect_env_vars(visible, players, aut):
    r"""Return union of `varlists` with key != `player`.

    The union is over `players - visible`.
    """
    gen = (
        aut.varlist[k] for k in players
        if k not in visible)
    return set().union(*gen)


def _conj(x, fol):
    if not x:
        return fol.true
    r = x[0]
    for u in x:
        r &= u
    return r


def _comma_join(vars_list):
    return ', '.join(vars_list)


def main():
    """Entry point."""
    aut = landing_gear_example()
    aut.phases = dict(
        to_cruise=1,
        to_landing=2)  # used for printing during development
    add_masks_and_hidden_vars(aut, phase=1)
    add_masks_and_hidden_vars(aut, phase=2)
    add_masks_and_hidden_vars(aut, phase=1)
    inv = closure(aut.players, aut)
    print('\nshared invariant:\n')
    print_expr(inv, aut)
    assert not (aut.support(inv) & aut.masks)
    print('{n} states satisfy the cooperative invariant'.format(
        n=aut.count(inv)))
    aut.inv = inv
    preserve_invariant(inv, aut)
    target = aut.add_expr('mode = 1')
    aut.visible = ['autopilot']
    aut.observer = 'autopilot'
    obs_target = observable_predicate(target, aut.observer, aut)
    print('\nobservable target:\n')
    print_states(obs_target, aut)
    player = 'autopilot'
    team = ['gear_module', 'door_module']
    (attr, eta_player,
     eta_team, new_aut) = make_pinfo_assumption(
        obs_target, player, team, aut)
    assert attr >= obs_target
    print('\neta team:\n')
    v = _slice(eta_team, aut)
    print_expr(v, aut)
    # print_states(eta_team, aut, LOG)
    print('\neta player:\n')
    v = _slice(eta_player, aut)
    print_expr(v, aut)
    print_states(eta_player, aut, LOG)
    new_target = eta_player | attr
    attr = pinfo_attractor(new_target, [player], aut)
    print('\nlarger attractor:\n')
    print_states(attr, aut, LOG)
    old_target = obs_target
    #
    # decompose subsystem goal
    pred = aut.inv & _slice(eta_player, aut)
    goal = ~ pred
    v = new_aut.action['autopilot']
    v = _slice(v, aut)
    new_aut.action['autopilot'] = v
    make_subsystem_specs_1(goal, pred, new_aut)
    #
    # close the outer fixpoint
    print('---- CLOSE OUTER FIXPOINT ----')
    target = attr & aut.add_expr('mode = 0')
    add_masks_and_hidden_vars(aut, phase=2)
    print_states(target, aut)
    #
    aut.visible = ['autopilot']
    aut.observer = 'autopilot'
    obs_target = observable_predicate(target, aut.observer, aut)
    print('\nobservable target:\n')
    print_states(obs_target, aut)
    player = 'autopilot'
    team = ['gear_module', 'door_module']
    (attr, eta_player,
     eta_team, new_aut) = make_pinfo_assumption(
        obs_target, player, team, aut)
    assert attr >= obs_target
    print('\neta team:\n')
    v = _slice(eta_team, aut)
    print_expr(v, aut)
    # print_states(eta_team, aut, LOG)
    print('\neta player:\n')
    v = _slice(eta_player, aut)
    print_expr(v, aut)
    # print_states(eta_player, aut, LOG)
    new_target = eta_player | attr
    attr = pinfo_attractor(new_target, [player], aut)
    print('\nlarger attractor:\n')
    print_states(attr, aut, LOG)
    #
    new_target = old_target & attr
    print('\nold target:\n')
    print_states(old_target, aut)
    print('\nnew target:\n')
    print_states(new_target, aut)
    # assert outer fixpoint closed
    assert _slice(old_target, aut) == _slice(new_target, aut)
    #
    # decompose subsystem goal
    pred = aut.inv & _slice(eta_player, aut)
    goal = ~ pred
    v = new_aut.action['autopilot']
    v = _slice(v, aut)
    new_aut.action['autopilot'] = v
    make_subsystem_specs_2(goal, pred, new_aut)


def make_subsystem_specs_1(goal, pred, aut):
    print('---- decomposing subsystem ----')
    # used for printing during development
    aut.phases = dict(
        subsystem_to_cruise=1)
    add_masks_and_hidden_vars(aut, phase=1)
    goal = observable_predicate(goal, 'gear_module', aut)
    print('gear goal')
    v = _slice(goal, aut)
    print_expr(v, aut)
    print('pred')
    v = _slice(pred, aut)
    print_expr(v, aut)
    # print_states(goal, aut, LOG)
    aut.visible = ['gear_module']
    aut.observer = 'gear_module'
    player = 'gear_module'
    team = ['door_module']
    attr, eta_player, eta_team, _ = make_pinfo_assumption(
         goal, player, team, aut, pred=pred)
    print('attr of player')
    print_states(attr, aut, LOG)
    # no asm dependency needed here
    #
    # print('\neta team:\n')
    # print_states(eta_team, aut, LOG)
    # v = _slice(attr, aut)
    # print_expr(v, aut)
    # print('\neta player:\n')
    # print_states(eta_player, aut, LOG)
    # v = _slice(eta_player, aut)
    # print_expr(v, aut)
    print('attr | eta_player')
    new_target = attr | eta_player
    print_states(new_target, aut, LOG)
    large = pinfo_attractor(new_target, [player], aut)
    print('\nlarger attractor for gear:\n')
    print_states(large, aut, LOG)
    if _slice(large & aut.inv, aut) == aut.inv:
        print('larger attractor covers inv')
    print('==== decomposing subsystem ====')


def make_subsystem_specs_2(goal, pred, aut):
    print('---- decomposing subsystem ----')
    # used for printing during development
    aut.phases = dict(
        subsystem_to_landing=1)
    add_masks_and_hidden_vars(aut, phase=1)
    goal = observable_predicate(goal, 'gear_module', aut)
    print('gear goal')
    v = _slice(goal, aut)
    print_expr(v, aut)
    print('pred')
    v = _slice(pred, aut)
    print_expr(v, aut)
    # print_states(goal, aut, LOG)
    aut.visible = ['gear_module']
    aut.observer = 'gear_module'
    player = 'gear_module'
    team = ['door_module']
    attr, eta_player, eta_team, _ = make_pinfo_assumption(
         goal, player, team, aut, pred=pred)
    print('attr of player')
    print_states(attr, aut, LOG)
    print('\neta team:\n')
    # print_states(eta_team, aut, LOG)
    v = _slice(eta_team, aut)
    print_expr(v, aut)
    print('\neta player:\n')
    # print_states(eta_player, aut, LOG)
    v = _slice(eta_player, aut)
    print_expr(v, aut)
    print('attr | eta_player')
    new_target = attr | eta_player
    print_states(new_target, aut, LOG)
    large = pinfo_attractor(new_target, [player], aut)
    print('\nlarger attractor for gear:\n')
    print_states(large, aut, LOG)
    if _slice(large & aut.inv, aut) == aut.inv:
        print('larger attractor covers inv')
    print('==== decomposing subsystem ====')


def dev_decomposing_system():
    print('decomposing subsystem')
    aut = landing_gear_example()
    # used for printing during development
    aut.phases = dict(
        subsystem=1)
    add_masks_and_hidden_vars(aut, phase=1)
    inv = closure(aut.players, aut)
    aut.inv = inv
    preserve_invariant(inv, aut)
    s = '''
        \/ ((door = 3) /\ (gear \in 0 .. 2) /\ (height \in 76 .. 100) /\ (mode = 2) /\ (speed \in 0 .. 15))
        \/ ((gear = 0) /\ (height \in 76 .. 100) /\ (mode = 2) /\ (speed \in 0 .. 15))
        '''
    pred = aut.add_expr(s)
    goal = ~ pred
    goal = observable_predicate(goal, 'gear_module', aut)
    s = '''
        /\ (mode != 1) /\ (speed <= 15)
        /\ (mode' != 1) /\ (speed' <= 15)
        '''
    aut.action['autopilot'] &= aut.add_expr(s)
    print('gear goal')
    v = _slice(goal, aut)
    print_expr(v, aut)
    print('pred')
    v = _slice(pred, aut)
    print_expr(v, aut)
    print('gear goal (states)')
    print_states(goal, aut, LOG)
    aut.visible = ['gear_module']
    aut.observer = 'gear_module'
    player = 'gear_module'
    team = ['door_module']
    attr, eta_player, eta_team, _ = make_pinfo_assumption(
         goal, player, team, aut, pred=pred)
    print('attr of player')
    # s = 'mode = 2 /\ speed <= 15 /\ height >= 76'
    # u = aut.add_expr(s)
    print_states(attr, aut, LOG)
    print('\neta team:\n')
    print_states(eta_team, aut, LOG)
    print('\neta player:\n')
    print_states(eta_player, aut, LOG)


def make_pinfo_assumption(
        goal, player, team, aut, pred=None):
    if pred is None:
        pred = aut.inv
    assert goal != aut.false
    assert player not in team, (player, team)
    assert team, team
    # print_states(goal, aut)
    print('~ goal')
    print_states(aut.inv & ~ goal, aut)
    i = aut.players[player]
    ip = (i + 1) % len(aut.players)
    # player attractor
    aut.visible = [player]
    aut.observer = player
    attr = pinfo_attractor(goal, [player], aut)
    log.debug('\nattractor to observable target (a):\n')
    print_states(attr, aut)
    # team attractor
    team_aut = copy.copy(aut)
    team_aut.visible = team
    team_aut.observer = sym.pick(team)  # choose a player
    # first try
    basin = aut.true
    r, _, basin = persistence_assumption(
        attr, basin, player, team, aut, team_aut, pred)
    log.debug('\nfirst basin (old B):\n')
    print_states(basin, aut)
    log.debug('\nfirst r:\n')
    print_states(r, aut)
    # assert False
    if r != aut.false:
        log.info('found a trap with first try')
        # return a, r, goal_team, aut
    # chase escapes
    # r = aut.false
    escape = aut.true
    # parameter assignments that reached `r != aut.false`
    converged = aut.false
    while escape != aut.false:
        out = ~ basin & aut.inv
        out = project_on_observer(out, team_aut)
        log.debug('\nout (~ basin):\n')
        print_states(out, aut)
        holes = basin & pinfo_cpre(out, team, team_aut)
        log.debug('\nholes:\n')
        print_states(holes, aut)
        escape = out & sym.image(holes & aut.inv, aut)
        log.debug('\nescape:\n')
        escape = project_on_observer(escape, team_aut)
        escape &= out
        print_states(escape, aut)
        # enlarge
        escape &= ~ converged  # keep converged ones unchanged
        basin |= escape
        # action that restricts `player`
        obs_basin = observable_predicate(basin, player, aut)
        vrs = aut.varlist[player]
        stay = aut.replace_with_primed(vrs, obs_basin)
        stay = aut.let({sym.TURN: ip}, stay)
        stay &= aut.let({sym.TURN: i}, obs_basin)
        # restrict `player` to observable basin
        new_aut = copy.copy(team_aut)
        new_aut.action[player] &= stay
        # recompute
        r, eta_team, b_team = persistence_assumption(
            attr, basin, player, team, aut, new_aut, pred)
        non_full = non_empty_slices(~ r, aut)
        non_empty = non_empty_slices(r, aut)
        assert non_empty != aut.true, 'disconnected comm too ??'
        assert non_full == aut.true
        converged |= non_empty
        assert scope.support_issubset(converged, aut.masks, aut)
        assert converged == aut.false or r != aut.false
        if converged != aut.false:
            log.info('some communication architectures '
                     'have converged')
        # very unlikely, means silent communication too
        # (means fully decoupled possible)
        assert converged != aut.true, 'all architectures converged'
    if r != aut.false:
        log.info('found a trap after catching escapes')
    assert goal <= attr
    assert r & goal == aut.false
    assert r & attr == aut.false
    obs_eta = observable_predicate(eta_team, player, aut)
    assert r <= obs_eta
    assert pinfo_trap(r, attr, [player], aut) == (r | attr)
    return attr, r, eta_team, new_aut


def persistence_assumption(
        attr, basin, player, team, aut, new_aut, pred):
    goal_team = project_on_observer(attr, new_aut, pred)
    log.debug('\ngoal_team (attr):\n')
    v = _slice(goal_team, aut)
    # print_expr(v, aut)
    b_team = pinfo_attractor(goal_team, team, new_aut)
    b_team &= basin
    log.debug('\nteam attractor within basin (b_team):\n')
    v = _slice(b_team, aut)
    # print_expr(v, aut)
    assert b_team != aut.false
    eta_team = b_team & ~ goal_team
    assert eta_team != b_team
    log.debug('\nteam eta (eta_team):\n')
    # print_states(eta_team, aut)
    v = _slice(eta_team, aut)
    # print_expr(v, aut)
    # trap by player
    obs_basin = observable_predicate(basin, player, aut)
    u = observable_predicate(eta_team, player, aut)
    u &= obs_basin
    log.debug('\nobservable eta (u):\n')
    v = _slice(u, aut)
    # print_expr(v, aut)
    print_states(u, aut)
    c = pinfo_trap(u, attr, [player], aut)
    log.debug('\ntrap (c):\n')
    print_states(c, aut)
    eta_player = c & ~ attr
    return eta_player, eta_team, b_team


def pinfo_trap(
        stay, escape, team, aut):
    """Trap under parameterized information."""
    assert scope.is_state_predicate(stay)
    assert scope.is_state_predicate(escape)
    assert set(team).issubset(aut.players), (team)
    uold = None
    u = aut.true
    while u != uold:
        uold = u
        u &= pinfo_cpre(u, team, aut)
        u &= stay
        u |= escape
        log.info('trap iteration')
    assert u <= (stay | escape)
    return u


def pinfo_attractor(
        target, team, aut):
    """Attractor under parameterized information."""
    log.info('---- attractor ----')
    log.debug('Attractor target:')
    print_states(target, aut)
    assert scope.is_state_predicate(target)
    assert set(team).issubset(aut.players), (team)
    uold = None
    u = target
    i = 1
    while u != uold:
        log.debug('attractor iteration {i}'.format(i=i))
        i += 1
        uold = u
        u |= pinfo_cpre(u, team, aut)
        log.debug('diff')
        print_states(u & ~ uold, aut)
        print('.', end='', flush=True)
    assert u >= target
    log.info('==== attractor ====')
    return u


def pinfo_cpre(
        target, team, aut):
    """Controllable predecessors under parameterized information."""
    pre = aut.false
    for player in aut.players:
        log.info("    {p}'s turn {s}".format(
            p=player, s='(team)' if player in team else ''))
        if player in team:
            pre |= sys_pre_under_pinfo(target, player, aut)
        else:
            pre |= env_pre_under_pinfo(target, player, aut)
    return pre


def print_states(u, aut, log_level=None):
    """Print safe states for communication architecture."""
    if log_level is None:
        log_level = logging.DEBUG
    if log.getEffectiveLevel() > log_level:
        return
    v = _slice(u, aut)
    v &= aut.inv
    if v == aut.false:
        print('!!! EMPTY SET OF STATES !!!')
        return
    print_expr(v, aut)


def print_expr(u, aut):
    """Print minimal DNF, taking into account type hints."""
    vrs = aut.support(u)
    s = aut.type_hint_for(vrs)
    types = aut.add_expr(s)
    u &= types
    print('---- min DNF ----')
    print(aut.to_expr(u, care=types, show_dom=True))
    print('=================')


def non_empty_slices(u, aut):
    """Return parameters that yield non-empty `u` slice."""
    support = aut.support(u)
    parameters = aut.masks
    vrs = support - parameters
    v = aut.exist(vrs, u)
    log.debug('full support: {s}'.format(s=support))
    log.debug('excluding masks: {s}'.format(s=vrs))
    return v


def _slice(u, aut):
    """Replace masks with values."""
    values = communication_schedule(aut.phases)
    v = aut.let(values, u)
    return v


def communication_schedule(phases):
    """Return assignment to indexed mask vars, as `dict`."""
    values = dict()
    for phase, j in phases.items():
        comm = communication_architecture(phase)
        for player, vrs in comm.items():
            for var, visible in vrs.items():
                s = '{player}_mask_{var}_{j}'.format(
                    player=player, var=var, j=j)
                values[s] = 1 - visible
    return values


def communication_architecture(phase):
    """Return connectivity graph.

    `dict` of `dict` of 1 (visible) or 0 (hidden)
    keys of first `dict` are players,
    of second `dict` are variables.

    Used to "slice" the parameterized contract properties.
    """
    # various connectivity graphs
    takeoff_to_cruise = dict(
        autopilot=dict(
            gear=1,
            door=0),
        door_module=dict(
            mode=0,
            height=0,
            speed=0,
            gear=0),
        gear_module=dict(
            mode=1,
            height=1,
            speed=0,
            door=0))
    takeoff_to_landing = dict(
        autopilot=dict(
            gear=1,
            door=0),
        door_module=dict(
            mode=0,
            height=0,
            speed=0,
            gear=0),
        gear_module=dict(
            door=0,
            height=0,
            speed=1,
            mode=1))
    takeoff_to_landing_2 = dict(
        autopilot=dict(
            gear=1,
            door=0),
        door_module=dict(
            mode=0,
            height=0,
            speed=1,
            gear=0),
        gear_module=dict(
            door=0,
            height=0,
            speed=0,
            mode=1))
    # full communication graph
    full = dict(
        autopilot=dict(
            gear=1,
            door=1),
        door_module=dict(
            mode=1,
            height=1,
            speed=1,
            gear=1),
        gear_module=dict(
            door=1,
            height=1,
            speed=1,
            mode=1))
    # no communication
    silence = dict(
        autopilot=dict(
            gear=0,
            door=0),
        door_module=dict(
            mode=0,
            height=0,
            speed=0,
            gear=0),
        gear_module=dict(
            door=0,
            height=0,
            speed=0,
            mode=0))
    # communication for the gear and door modules
    # towards cruise mode
    subsystem_to_cruise = dict(
        autopilot=dict(
            gear=0,
            door=1),
        door_module=dict(
            mode=0,
            height=0,
            speed=0,
            gear=1),
        gear_module=dict(
            door=0,
            height=1,
            speed=0,
            mode=1))
    # communication for the gear and door modules
    # towards landing mode
    subsystem_to_landing = dict(
        autopilot=dict(
            gear=1,
            door=0),
        door_module=dict(
            mode=0,
            height=0,
            speed=1,
            gear=0),
        gear_module=dict(
            door=1,
            height=0,
            speed=0,
            mode=1))
    if phase == 'to_cruise':
        return takeoff_to_cruise
    elif phase == 'to_landing':
        return takeoff_to_landing
    elif phase == 'full':
        return full
    elif phase == 'silence':
        return silence
    elif phase == 'subsystem_to_landing':
        return subsystem_to_landing
    elif phase == 'subsystem_to_cruise':
        return subsystem_to_cruise
    else:
        raise ValueError(
            'unknown phase {phase}'.format(phase=phase))


class Automaton(sym.Automaton):
    """Subclass to copy attributes relevant to hiding."""

    def __init__(self):
        super().__init__()
        self.masks = set()
        self.masks_of = dict()

    def __copy__(self):
        new = super().__copy__()
        new.inv = self.inv
        new.visible = self.visible
        new.observer = self.observer
        new.masks_of = self.masks_of
        new.xy_to_h = self.xy_to_h
        new.xy_to_r = self.xy_to_r
        new.masks = self.masks
        return new


if __name__ == '__main__':
    logger = logging.getLogger('omega')
    logger.setLevel(logging.ERROR)
    logger = logging.getLogger(__name__)
    logger.setLevel(logging.ERROR)
    logger.addHandler(logging.StreamHandler())
    main()
