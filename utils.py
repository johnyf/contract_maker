"""Various useful functions."""
# Copyright 2016-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging
import os
import textwrap

import ballpark
import humanize
from omega.symbolic import bdd as sym_bdd

import symbolic as sym


TURN = '_i'


def check_support_inv_target(target, inv, aut):
    """Raise `AssertionError` if any support is wrong."""
    xy = aut.vars_of_all_players
    # Target(x, y, m, turn)
    vrs = xy | aut.masks | {sym.TURN}
    assert sym_bdd.support_issubset(target, vrs, aut)
    assert sym_bdd.is_state_predicate(target)
    # Inv(x, y, turn)  top level
    # TODO: check whether `m` really occurs
    # it should not occur.
    # Inv(x, y, m, turn)  during assumption computation
    assert sym_bdd.is_state_predicate(inv)
    # vrs = xy | aut.masks | {sym.TURN}
    vrs = xy | aut.masks
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
    u = aut.forall(aut.vars_of_all_players, u)
    assert u == aut.true, u


def diagnose_not_inductive_inv(inv, action, aut):
    """Print minimal cover for violating moves."""
    inv_next = sym_bdd.prime(inv)
    not_inv_next = ~ inv_next
    u = inv & action
    u &= not_inv_next
    i0 = aut.add_expr('i = 0')
    u &= i0
    u = aut.exist(aut.vars_of_all_players, u)
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
    all_primed = aut.prime_vars(aut.vars_of_all_players)
    blocked = aut.forall(all_primed, ~not_inv_next)
    blocked_next = sym_bdd.prime(blocked)
    not_inv = ~ inv
    u = not_inv & blocked
    u = blocked_next | ~ u
    u = aut.exist(all_primed, u)
    u = aut.forall(aut.vars_of_all_players, u)
    support = aut.support(u)
    assert not support, support
    assert u == aut.true


template = '''\
-------------------- MODULE {module} --------------------
Invariant ==
{f}
=======================================================
'''


def dump_as_tla(f, fname):
    """Dump formula `f` to module `fname`."""
    module, ext = os.path.splitext(fname)
    if not ext:
        ext = '.tla'
    assert ext == '.tla', ext
    fname = module + ext
    indent = 4 * ' '
    f = textwrap.indent(f, indent)
    s = template.format(f=f, module=module)
    with open(fname, 'w') as fout:
        fout.write(s)


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


def configure_loggers(loggers, level):
    for name in loggers:
        log = logging.getLogger(name)
        log.setLevel(level)
        h = logging.StreamHandler()
        log.addHandler(h)


def format_stats(d):
    """Return `str` of formatted BDD statistics `d`."""
    s = (
        'Manager\n'
        '    bits: {n_vars}\n'
        '    mem: {mem}\n'
        '\n'
        'Nodes\n'
        '    total: {n_nodes}\n'
        '    peak: {peak_nodes}\n'
        '    peak live: {peak_live_nodes}\n'
        '\n'
        'Reordering\n'
        '    reorderings: {n_reorderings}\n'
        '    reordering time: {reordering_time}\n'
        '\n'
        'Unique table\n'
        '    size: {unique_size}\n'
        '    used: {unique_used_fraction:1.2}\n'
        '    used (expected): {expected_unique_used_fraction:1.2}\n'
        '\n'
        'Cache\n'
        '    size: {cache_size}\n'
        '    used: {cache_used_fraction:1.2}\n'
        '    insertions: {cache_insertions}\n'
        '    lookups: {cache_lookups}\n'
        '    hits: {cache_hits}\n'
        '    collisions: {cache_collisions}\n'
        '    deletions: {cache_deletions}\n'
        '\n').format(
            n_vars=d['n_vars'],
            mem=humanize.naturalsize(2**20 * d['mem']),
            n_nodes=ballpark.ballpark(d['n_nodes']),
            peak_nodes=ballpark.ballpark(d['peak_nodes']),
            peak_live_nodes=ballpark.ballpark(d['peak_live_nodes']),
            n_reorderings=humanize.intword(d['n_reorderings']),
            reordering_time=humanize.naturaldelta(d['reordering_time']),
            unique_size=ballpark.ballpark(d['unique_size']),
            unique_used_fraction=d['unique_used_fraction'],
            expected_unique_used_fraction=d['expected_unique_used_fraction'],
            cache_size=ballpark.ballpark(d['cache_size']),
            cache_used_fraction=d['cache_used_fraction'],
            cache_insertions=ballpark.ballpark(d['cache_insertions']),
            cache_lookups=ballpark.ballpark(d['cache_lookups']),
            cache_hits=ballpark.ballpark(d['cache_hits']),
            cache_collisions=ballpark.ballpark(d['cache_collisions']),
            cache_deletions=ballpark.ballpark(d['cache_deletions']))
    return s
