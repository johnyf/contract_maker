"""Masking variables and predicates."""
import logging
import pprint

from omega.logic import syntax as stx


log = logging.getLogger(__name__)


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
