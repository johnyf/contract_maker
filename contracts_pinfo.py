"""Contracts with hiding."""
# Copyright 2016-2017 by Ioannis Filippidis
# Copyright 2016-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
# Author: Ioannis Filippidis
import copy
import logging
import math
import pprint

from dd import autoref
from dd import cudd
from omega.logic import syntax as stx
from omega.symbolic import bdd as scope
from omega.symbolic import bdd as sym_bdd

import bdd as _bdd
import closure_noninterleaving as _closure
import cpre_noninterleaving as cpre
import fixpoint_noninterleaving as fx
import masks as _masks
import symbolic as sym
from symbolic import print_expr, dumps_expr
import utils


log = logging.getLogger(__name__)
LOG = 100
TURN = utils.TURN


def parametric_predicate(pred, aut):
    pred_r = aut.let(aut.x_to_r, pred)
    u = aut.selector & pred_r
    u = aut.exist(aut.hr, u)
    return u


def observable(target, within, inv, aut):
    """Return states that `player` can tell satisfy `target`."""
    assert scope.is_state_predicate(target)
    assert scope.is_state_predicate(within)
    assert scope.is_state_predicate(inv)
    within_r = aut.let(aut.x_to_r, within)
    inv_r = aut.let(aut.x_to_r, inv)
    target_r = aut.let(aut.x_to_r, target)
    #
    # Mask(m, v, h) == (IF m = TRUE THEN h ELSE x)
    # Selector(h, r) == r = Mask(m, v, h)
    #
    # Observable(x, y, m, Target(_, _, _)) ==
    #     /\ \E h:
    #         LET  r == Mask(m, v, h)
    #         IN  Inv(r, y)
    #     /\ \A h:
    #         LET  r == Mask(m, h, x)
    #         IN  Within(r, y, m) => Target(r, y, m)
    # <=>
    #     /\ \E h, r:
    #         /\ Selector(h, r)
    #         /\ Inv(r, y)
    #     /\ \A h:  \E r:
    #         /\ Selector(h, r)
    #         /\ Within(r, y, m) => Target(r, y, m)
    u = target_r | ~ within_r
    u &= aut.selector
    u = aut.exist(aut.r, u)
    u = aut.forall(aut.h, u)
    # \E h, r:
    #     /\ Selector(h, r)
    #     /\ Inv(r, y)
    u &= aut.exist(aut.hr, inv_r & aut.selector)
    # check support
    vrs = aut.vars_of_all_players | aut.masks
    assert scope.support_issubset(u, vrs, aut), (
        aut.support(u) - vrs)
    return u


def maybe(target, within, aut):
    """Return `aut.observer` states that could satisfy `target`.

    This function is equivalent to:

        /\ observable(target, within, aut)
        /\ param_inv
    """
    assert scope.is_state_predicate(target)
    assert scope.is_state_predicate(within)
    within_r = aut.let(aut.x_to_r, within)
    target_r = aut.let(aut.x_to_r, target)
    #
    # Project(x, y, m, i, Target) ==
    #     /\ \E h:
    #         LET
    #             r == Mask(m, h, x)
    #         IN
    #             /\ Inv(r, y, m, i)
    #             /\ Target(r, y, m, i)
    # <=>
    #     \E h, r:
    #         /\ Selector(h, r)
    #         /\ Inv(r, y, m, i)
    #         /\ Target(r, y, m, i)
    #
    # Note that:
    #
    #  Project(Target) <=> /\ ~ Observable(~ Target)
    #                      /\ \E h:  LET r == Mask(m, h, x)
    #                                IN Inv(r, y, m, i)
    # s = r'''
    #     \E {h}, {r}:  (
    #         /\ {selector}
    #         /\ @{target}
    #         /\ @{inv} )
    #     '''.format(
    #         h=h, r=r,
    #         selector=aut.selector,
    #         inv=within_r,
    #         target=target_r)
    # u = aut.add_expr(s)
    u = aut.selector & target_r & within_r
    assert scope.is_state_predicate(u)
    return aut.exist(aut.hr, u)


def main(aut):
    """Decompose specification into a contract."""
    inv = _closure.closure(aut.players, aut)
    assert not (aut.support(inv) & aut.masks)
    assert_type_invariant_implies_type_hints(inv, aut)
    fname = 'inv_bdd.pdf'
    dump_bdd_using_autoref(inv, fname)
    _closure.print_state_space_statistics(inv, aut)
    s = dumps_expr(inv, aut, use_types=True)
    print('\nshared invariant Inv:\n')
    print(s)
    # fname = 'Invariant.tla'
    # utils.dump_as_tla(s, fname)
    #
    # for charging station example
    # sys_player = 'station'
    # vrs = ['pos_x', 'pos_y']  # hide these variables
    #
    # for landing gear example
    sys_player = 'autopilot'
    vrs = ['door']
    _closure.hide_vars_from_sys(vrs, inv, sys_player, aut)
    #
    # for charging station example
    # sys_player = 'robot'
    # players = ['robot', 'station']
    #
    # for autopilot example
    sys_player = 'autopilot'
    players = ['autopilot', 'gear_module', 'door_module']
    #
    aut.global_inv = inv  # global full-info invariant
    aut_unzipped = _closure.unzip(inv, aut.players, aut)
    # configure mask parameters
    initial_phase = 0
    phase = '{i}_0'.format(i=initial_phase)
    _masks.add_masks_and_hidden_vars(aut_unzipped, phase=phase)
    aut_unzipped.observe(sys_player, [sys_player])
    # require initial condition
    param_inv = parametric_predicate(inv, aut_unzipped)
    param_z = outer_fixpoint(players, aut_unzipped)
    z = param_z[initial_phase]
    u = z | ~ param_inv
    qvars = aut.vars_of_all_players
    u = aut_unzipped.forall(qvars, u)
    # BDD stats
    stats = aut.bdd.statistics()
    s = utils.format_stats(stats)
    print(s)


def dump_bdd_using_autoref(u, fname):
    # copy from `dd.cudd` to `dd.autoref`
    b = autoref.BDD()
    cudd_bdd = u.bdd
    _bdd.copy_vars(cudd_bdd, b)
    r = _bdd.copy_bdd(u, cudd_bdd, b)
    autoref.reorder(b)
    b.dump(fname, [r])
    print('dumped BDD to file "{f}"'.format(f=fname))


def maximum_sum(u, aut):
    """Return assignment that maximizes sum of `u` support vars.

    `u` should depend only on integer-valued variables.

    For example, if `u` depends on the variables `a, b, c`
    and `values == dict(a=1, b=2, c=-1)` is returned, then the
    following properties hold:

        /\ LET a == 1
               b == 2
               c == -1
           IN u
        /\ \A i, j, k:
              (LET a == i
                   b == j
                   c == k
               IN u)
               => (a + b + c >= i + j + k)
    """
    vrs = aut.support(u)
    assert vrs.issubset(aut.masks), vrs
    vrs_sum = ' + '.join(vrs)
    # bisection
    a = 0
    b = len(vrs)
    assert a < b, (a, b)
    s = '@{u} /\ ({vrs_sum} >= {{bound}})'.format(
        u=u, vrs_sum=vrs_sum)
    fa = _eval(s, a, aut)
    fb = _eval(s, b, aut)
    assert fa, 'not feasible'
    while a != b:
        c = math.ceil((a + b) / 2)
        fc = _eval(s, c, aut)
        if fc:
            a = c
        else:
            b = c - 1
        print('bisection: {ab}'.format(ab=(a, b)))
    assert a == b, (a, b)
    bound = a
    print('Maximum:  {bound}'.format(bound=bound))
    # return a maximal satisfying assignment
    s = s.format(bound=bound)
    u = aut.add_expr(s)
    values = {var: 1 for var in aut.masks}
    values.update(aut.pick(u))
    return values


def _eval(s, bound, aut):
    """Return """
    s = s.format(bound=bound)
    u = aut.add_expr(s)
    return u != aut.false


def assert_type_invariant_implies_type_hints(inv, aut):
    """Raise `AssertionError` if `~ |= inv => type_hints`."""
    vrs = aut.vars_of_all_players
    assert aut.implies_type_hints(inv, vrs)


def outer_fixpoint(players, aut):
    player = players[0]
    n_goals = len(aut.win[player]['[]<>'])
    z = [aut.true] * n_goals
    zold = [None] * n_goals
    # effectively the greatest fixpoint Z
    while z != zold:
        zold = z
        z = iterate_recurrence_goals(z, players, aut)
        assert all(u <= v for u, v in zip(z, zold))
    return z


def iterate_recurrence_goals(z, players, aut):
    within = aut.global_inv
    player = players[0]
    k_players = len(players) - 1
    n_goals = len(aut.win[player]['[]<>'])
    for i in range(n_goals):
        for j in range(k_players):
            phase = '{i}_{j}'.format(i=i, j=j)
            _masks.add_masks_and_hidden_vars(aut, phase=phase)
    z_new = list(z)
    for i, goal in enumerate(aut.win[player]['[]<>']):
        print('recurrence goal: {i}'.format(i=i))
        # declare at top to propagate to copied automata
        # caution: overwrites parameter maps
        ij = (i, 0)
        i_next = (i + 1) % n_goals
        z_next = z[i_next]
        y = single_recurrence_goal(goal, z_next, within, players, ij, aut)
        z_new[i] &= y
    return z_new


def single_recurrence_goal(target, z_next, within, players, ij, aut):
    """Development harness for parameterized assumption construction."""
    assert 'scheduler' not in players
    print('single recurrence goal: {ij}'.format(ij=ij))
    i, j = ij
    assert i >= 0, i
    assert j >= 0, j
    phase = '{i}_{j}'.format(i=i, j=j)
    _masks.add_masks_and_hidden_vars(aut, phase=phase)
    # define players that assumptions will be generated for
    # players outside `team` are treated as the team's environment
    player, *team = players
    print('player: {p}'.format(p=player))
    print('team: {t}'.format(t=team))
    # define what the component observes
    aut.observe(player, [player])
    # eliminate hidden vars from target
    inv = aut.global_inv
    vis_z = observable(z_next, inv, inv, aut)
    vis_target = observable(target, inv, inv, aut)
    y = vis_target
    # print('vis_target')
    # print_slice(vis_target, aut)
    yold = None
    # iterate over assumption generation,
    # which is effectively the least fixpoint Y
    trap = aut.true
    etas = list()
    while y != yold:
        # print('Y iteration')
        yold = y
        # can others help as a team ?
        attr, trap, eta_team = make_pinfo_assumption(
            y, vis_z, within, player, team, aut)
        etas.append(eta_team)
        within_new = inv & trap
        z_next_new = aut.true
        ij_new = (i, j + 1)
        # decompose team
        if len(team) > 1:
            single_recurrence_goal(
                ~ eta_team, z_next_new, within_new,
                team, ij_new, aut, attr)
        y = attr | trap
    # print('Y')
    # print_slice(y, aut)
    # \A vars:  (Inv /\ ~ Target)  =>  Y
    aut.observe(player, [player])
    proj_inv = maybe(inv, inv, aut)
    u = y | ~ proj_inv
    qvars = aut.vars_of_all_players
    u = aut.forall(qvars, u)
    print('Maybe(Inv) => Y')
    print_slice(u, aut)
    u = y | target | ~ inv
    u = aut.forall(qvars, u)
    print('Inv  =>  (Y \/ Target)')
    print_slice(u, aut)
    print('end: {ij}========\n'.format(ij=ij))
    return y


def make_pinfo_assumption(
        goal, z, within, player, team, aut):
    assert goal != aut.false
    assert player not in team, (player, team)
    inv = aut.global_inv
    # player automaton
    aut.team = [player]
    aut.observe(player, [player])
    cpre.group_as_env_sys(aut.team, aut)
    cpre.parametrize_actions(aut)
    # team automaton
    team_aut = copy.copy(aut)
    team_aut.team = list(team)
    crow = team[0]
    team_aut.observe(crow, team)
    cpre.group_as_env_sys(team, team_aut)
    cpre.parametrize_actions(team_aut)
    # player attractor
    goal &= cpre.step(z, aut)
    attr = cpre.attractor(goal, aut)
    # team attractor initializes `basin`
    goal_team = observable(attr, inv, inv, team_aut)
    basin = cpre.attractor(goal_team, team_aut)
    # chase escapes
    escape = aut.true
    converged = aut.false
    while escape != aut.false:
        print('escapes iteration')
        # enlarge, following escapes
        proj_inv = maybe(inv, inv, team_aut)
        out = ~ basin & proj_inv
        # check equivalent expression
        # this equivalence holds because `basin` has as support
        # only variables visible to the team
        out_2 = ~ basin & inv
        out_2 = maybe(out_2, inv, team_aut)
        assert out_2 == out
        #
        holes = basin & cpre.step(out, team_aut)
        escape = out & fx.image(holes & inv, team_aut)  # assembly step
        escape = out & maybe(escape, inv, team_aut)
        escape &= ~ converged  # keep converged ones unchanged
        old_basin = basin
        basin |= escape
        # recompute
        eta_player, eta_team = persistence_guarantee(
            attr, basin, within, aut, team_aut)
        non_empty = non_empty_slices(eta_player, aut)
        converged |= non_empty
        # assert
        non_full = non_empty_slices(~ eta_player, aut)
        assert non_empty != aut.true, 'disconnected comm too ??'
        assert non_full == aut.true
        assert scope.support_issubset(converged, aut.masks, aut)
        assert converged == aut.false or eta_player != aut.false
        assert converged != aut.true, 'all architectures converged'
    assert goal <= attr
    assert eta_player & goal == aut.false
    assert eta_player & attr == aut.false
    print('trap')
    print_slice(eta_player, aut)
    print('eta_team')
    print_slice(eta_team, team_aut)
    return attr, eta_player, eta_team


def persistence_guarantee(
        attr, basin, within, aut, team_aut):
    """Create an assumption in presence of hiding."""
    assert attr != aut.false
    inv = team_aut.global_inv
    # attractor by team
    u = ~ basin & maybe(inv, inv, team_aut)
    goal_team = (
        observable(attr, inv, inv, team_aut)
        | u)
    b_team = basin & cpre.attractor(goal_team, team_aut)
    eta_team = b_team & ~ goal_team
    # trap by player
    assert eta_team <= basin  # => obs_basin unnecessary
    stay = observable(eta_team, inv, inv, aut)
    unless = attr
    trap = cpre.trap(stay, unless, aut)
    eta_player = trap & ~ unless
    return eta_player, eta_team


def exist_env_vars(u, aut):
    """Projection `\E env_vars:  u`."""
    qvars = aut.varlist['env']
    r = aut.exist(qvars, u)
    return r


def print_slice(u, aut, conj_types=False):
    v = _slice(u, aut)
    if v == aut.false:
        print('FALSE')
        return
    if v == aut.true:
        print('TRUE')
        return
    if conj_types:
        v &= sym.type_hints_for_support(v, aut)
    care = aut.true
    s = sym.dumps_expr(v, aut, care=care, use_types=True)
    print(s + '\n')


def _slice(u, aut):
    return _slice_landing_gear_example(u, aut)


def _slice_charging_station_example(u, aut):
    """Replace masks with values."""
    comm = dict(
        station=dict(
            req=1,
            pos_x=0,
            pos_y=0,
            occ=1,
            _i=1),
        robot=dict(
            spot_1=0,
            spot_2=0,
            free_x=1,
            free_y=0,
            free=1,
            occ=0,
            _i=1))
    phase = '0_0'
    values = connectivity_to_masks(comm, phase)
    v = aut.let(values, u)
    comm = dict(
        station=dict(
            req=1,
            pos_x=0,
            pos_y=0,
            occ=1,
            _i=1),
        robot=dict(
            spot_1=0,
            spot_2=0,
            free_x=1,
            free_y=1,
            free=1,
            occ=0,
            _i=1))
    phase = '1_0'
    values = connectivity_to_masks(comm, phase)
    v = aut.let(values, v)
    return v


def _slice_landing_gear_example(u, aut):
    """Replace masks with values."""
    # takeoff to cruise, this one only for top level
    # cruise:  mode = 1
    comm_to_cruise_1 = dict(
        autopilot=dict(
            gear=0,
            door=1,
            _i=1),
        gear_module=dict(
            mode=1,
            height=1,
            speed=0,
            _i=1))
    # landing: mode = 0
    comm_to_landing_1 = dict(
        autopilot=dict(
            gear=1,
            door=0,
            _i=1),
        gear_module=dict(
            mode=1,
            height=0,
            speed=1,
            _i=1))
    phase = '0_0'
    values_1 = connectivity_to_masks(comm_to_landing_1, phase)
    phase = '1_0'
    values_2 = connectivity_to_masks(comm_to_cruise_1, phase)
    # lower level
    # cruise:  mode = 1
    comm_to_cruise_2 = dict(
        autopilot=dict(
            gear=0,
            door=1,
            _i=1),
        door_module=dict(
            mode=0,
            height=0,
            speed=0,
            gear=1,
            _i=1),
        gear_module=dict(
            mode=1,
            height=1,
            speed=0,
            door=1,
            _i=1))
    # landing: mode = 0
    comm_to_landing_2 = dict(
        autopilot=dict(
            gear=1,
            door=0,
            _i=1),
        door_module=dict(
            mode=1,
            height=0,
            speed=1,
            gear=0,
            _i=1),
        gear_module=dict(
            mode=1,
            height=0,
            speed=1,
            door=1,
            _i=1))
    phase = '0_1'
    values_3 = connectivity_to_masks(comm_to_landing_2, phase)
    phase = '1_1'
    values_4 = connectivity_to_masks(comm_to_cruise_2, phase)
    values = values_1
    values.update(values_2)
    values.update(values_3)
    values.update(values_4)
    v = aut.let(values, u)
    return v


def non_empty_slices(u, aut):
    """Return parameters that yield non-empty `u` slice."""
    qvars = aut.vars_of_all_players
    return aut.exist(qvars, u)


def communication_schedule(aut):
    """Return assignment to indexed mask vars, as `dict`."""
    phases = aut.phases
    values = dict()
    for phase, j in phases.items():
        comm = aut.comm_arch(phase)
        for player, vrs in comm.items():
            for var, visible in vrs.items():
                s = '{player}_mask_{var}_{j}'.format(
                    player=player, var=var, j=j)
                values[s] = 1 - visible
    return values


def connectivity_to_masks(comm, j):
    values = dict()
    for player, vrs in comm.items():
        for var, visible in vrs.items():
            s = '{player}_mask_{var}_{j}'.format(
                player=player, var=var, j=j)
            values[s] = 1 - visible
    return values


class Automaton(sym.Automaton):
    """Subclass to copy attributes relevant to hiding."""

    def __init__(self):
        super().__init__()
        self.global_inv = None  # full info invariant
        self.inv = None  # InvH
        self.team = list()  # \subseteq self.players
        self.visible = list()
        self.observer = None
        self.masks = set()
        self.masks_of = dict()
        self.xy_to_h = dict()
        self.xy_to_r = dict()
        self.x_to_r = dict()
        self.h = set()
        self.r = set()
        self.hr = set()
        self.mask_to_subproblem = dict()
        self.type_invariant = None
        self.bdd.configure(
            max_memory=2 * cudd.GB,
            max_cache_hard=2**25)

    def __copy__(self):
        new = super().__copy__()
        new.global_inv = self.global_inv
        new.inv = self.inv
        new.team = list(self.team)
        new.visible = self.visible
        new.observer = self.observer
        new.masks = self.masks
        new.masks_of = self.masks_of
        new.xy_to_h = dict(self.xy_to_h)
        new.xy_to_r = dict(self.xy_to_r)
        new.x_to_r = dict(self.x_to_r)
        new.h = set(self.h)
        new.r = set(self.r)
        new.hr = set(self.hr)
        # global indexing of masks
        new.mask_to_subproblem = self.mask_to_subproblem
        new.type_invariant = self.type_invariant
        return new

    def observe(self, player, visible):
        """Set observer and """
        self.observer = player
        self.visible = visible
        x = utils.collect_env_vars(
            visible, self.players, self)
        selector = _masks.masking_predicates(
            self.observer, x, self)
        self.selector = self.add_expr(selector)
        x = utils.collect_env_vars(
            visible, self.players, self)
        self.x_to_r = {
            k: v for k, v in self.xy_to_r.items()
            if k in x}
        self.h = {self.xy_to_h[var] for var in x}
        self.r = {self.xy_to_r[var] for var in x}
        self.hr = self.h | self.r
