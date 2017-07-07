"""Utilities for manipulating BDDs.

This is a temporary location. Eventually, move to `dd`.
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from dd import bdd as _bdd


def copy_vars(source, target):
    """Copy variables, preserving levels.

    @type source, target: `BDD`
    """
    for var in source.vars:
        level = source.level_of_var(var)
        target.add_var(var, level=level)


def copy_bdd(u, from_bdd, to_bdd):
    """Copy function of node `u` `from_bdd` `to_bdd`.

    @param u: node in `from_bdd`
    @type from_bdd, to_bdd: `BDD`
    """
    old_order = {var: from_bdd.level_of_var(var)
                 for var in from_bdd.vars}
    new_order = {var: to_bdd.level_of_var(var)
                 for var in to_bdd.vars}
    _bdd._assert_valid_ordering(old_order)
    _bdd._assert_valid_ordering(new_order)
    cache = dict()
    # umap[1] = 1
    r = _copy_bdd(u, to_bdd, cache)
    assert len(r) == len(u), (r, u)
    return r


def _copy_bdd(u, bdd, cache):
    """Recurse to copy node `u`` to `bdd`.

    @type cache: `dict`
    """
    # terminal ?
    if u == u.bdd.true:
        return bdd.true
    # could be handled below, but frequent case,
    # so more efficient here
    if u == u.bdd.false:
        return bdd.false
    # rectify
    if u.negated:
        z = ~ u
    else:
        z = u
    # non-terminal
    # memoized ?
    k = int(z)
    if k in cache:
        r = cache[k]
        assert not r.negated
        if u.negated:
            r = ~ r
        return r
    # recurse
    v = u.low
    w = u.high
    p = _copy_bdd(v, bdd, cache)
    q = _copy_bdd(w, bdd, cache)
    assert p.negated == v.negated, (p, v)
    assert not q.negated, q
    # add node
    var = u.var
    # use a `bdd` method for translating var names
    # here if needed (role of `level_map` in the past)
    g = bdd.var(var)
    r = bdd.apply('ite', g, q, p)
    assert not r.negated
    # memoize
    cache[k] = r
    # negate ?
    if u.negated:
        r = ~ r
    return r


def assert_isomorphic_bdds(old_bdd, new_bdd, umap):
    """Raise `AssertionError` if not isomorphic shared ROBDDs."""
    n = len(old_bdd)
    m = len(new_bdd)
    assert n == m, (n, m)
    level_map = {old_bdd.ordering[x]: new_bdd.ordering[x]
                 for x in old_bdd.ordering}
    # add terminal
    level_map[len(old_bdd.ordering)] = len(new_bdd.ordering)
    for u, (i, v, w) in old_bdd._succ.items():
        assert u > 0, u
        # terminal ?
        if u == 1:
            continue
        # non-terminal
        r = umap[u]
        assert r > 0, (u, r)
        j, p, q = new_bdd._succ[r]
        j_ = level_map[i]
        assert j == j_, (i, j, j_)
        assert v * p > 0, (v, p)
        assert w * q > 0, (w, q)
        a = umap[abs(v)]
        b = umap[abs(w)]
        assert abs(p) == a, (v, a, p)
        assert abs(q) == b, (w, b, q)
