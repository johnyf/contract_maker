"""Noninterleaving controllable step operator and fixpoints."""
# Copyright 2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from omega.symbolic import bdd as scope

from synthesizer import symbolic as sym
from synthesizer import utils


def group_as_env_sys(team, aut):
    """Assign "env" and "sys" in `aut.action`."""
    others = set(aut.players).difference(team)
    sys_next = sym.conj_actions_of(team, aut)
    env_next = sym.conj_actions_of(others, aut)
    aut.action['sys'] = sys_next
    aut.action['env'] = env_next
    sys_vars = aut.vars_of_players(team)
    env_vars = aut.vars_of_players(others)
    aut.varlist['sys'] = sys_vars
    aut.varlist['env'] = env_vars
    aut.varlist['sys_p'] = aut.prime_vars(sys_vars)
    aut.varlist['env_p'] = aut.prime_vars(env_vars)


def parametrize_actions(aut):
    """Return parametrized actions."""
    sys_next = aut.action['sys']
    env_next = aut.action['env']
    x = utils.collect_env_vars(aut.visible, aut.players, aut)
    h = {aut.xy_to_h[var] for var in x}
    r = {aut.xy_to_r[var] for var in x}
    x_to_r = {k: v for k, v in aut.xy_to_r.items()
              if k in x}
    inv = aut.global_inv
    # substitutions
    inv_r = aut.let(x_to_r, inv)
    sys_next_r = aut.let(x_to_r, sys_next)
    env_next_r = aut.let(x_to_r, env_next)
    #
    # Selector(h, r) == r = Mask(m, v, h)
    #
    # MaskedInv(h) ==
    #     LET r == Mask(m, v, h)
    #     IN Inv(r, y)
    # <=>
    #     \E r:  /\ Selector(h, r)
    #            /\ Inv(r, y)
    u = inv_r & aut.selector
    masked_inv = aut.exist(r, u)
    #
    # ParamInv == \E h:  MaskedInv(h)
    param_inv = aut.exist(h, masked_inv)
    #
    # ParamSysNext ==
    #     /\ ParamInv
    #     /\ \A h:  LET r == Mask(m, v, h)
    #               IN Inv(r, y) => SysNext(r, y, y')
    # <=>
    #     /\ ParamInv
    #     /\ \A h:  \E r:
    #         /\ Selector(h, r)
    #         /\ Inv(r, y) => SysNext(r, y, y')
    u = sys_next_r | ~ inv_r
    u &= aut.selector
    u = aut.exist(r, u)
    u = aut.forall(h, u)
    param_sys_next = u & param_inv
    #
    # ParamEnvNext ==
    #     \E h:  /\ MaskedInv(h)
    #            /\ MaskedEnvNext(h, v', x')
    # <=>
    #     \E h:  LET r == Mask(m, v, h)
    #            IN
    #                /\ Inv(r, y)
    #                /\ EnvNext(r, y, x')
    # <=>
    #     \E h:  \E r:
    #         /\ Selector(h, r)
    #         /\ Inv(r, y)
    #         /\ EnvNext(r, y, x')
    u = aut.selector & inv_r & env_next_r
    param_env_next = aut.exist(h | r, u)
    aut.action['sys'] = param_sys_next
    aut.action['env'] = param_env_next


def trap(stay, escape, aut):
    """Greatest fixpoint, with lower bound."""
    assert scope.is_state_predicate(stay)
    assert scope.is_state_predicate(escape)
    qold = None
    q = aut.true
    while q != qold:
        qold = q
        q &= step(q, aut)
        q &= stay
        q |= escape
        assert q <= qold
    assert q <= (stay | escape)
    return q


def attractor(target, aut):
    """Least fixpoint."""
    assert scope.is_state_predicate(target)
    qold = None
    q = target
    while q != qold:
        qold = q
        q |= step(q, aut)
        assert q >= qold
    assert q >= target
    return q


def step(target, aut):
    """Return controllable predecessors."""
    vrs = aut.vars_of_all_players
    u = aut.replace_with_primed(vrs, target)
    # /\ SysNext
    # /\ EnvNext => Target'
    u |= ~ aut.action['env']
    u &= aut.action['sys']
    # \E sys_vars':  \A env_vars'
    u = aut.forall(aut.varlist['env_p'], u)
    u = aut.exist(aut.varlist['sys_p'], u)
    return u
