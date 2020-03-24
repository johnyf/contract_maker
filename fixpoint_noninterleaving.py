"""Nontinterleaving fixpoint operators."""
import symbolic as sym


def preimage(target, aut):
    """Return predecessor states of `target`, conjoining player actions."""
    action = sym.conj_actions_of(aut.players, aut)
    vrs = aut.vars_of_all_players
    qvars = aut.prime_vars(vrs)
    # \E x', y', i'
    primed_target = aut.replace_with_primed(vrs, target)
    u = action & primed_target
    u = aut.exist(qvars, u)
    return u


def image(source, aut):
    """Return successor states of `target`, conjoining player actions."""
    action = sym.conj_actions_of(aut.players, aut)
    qvars = aut.vars_of_all_players
    u = source & action
    u = aut.exist(qvars, u)
    u = aut.replace_with_unprimed(qvars, u)
    return u
