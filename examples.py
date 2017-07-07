"""Run contract construction and communication arch design."""
import logging

from dd import cudd

from synthesizer import contracts_pinfo as pinfo
from synthesizer import utils


TURN = utils.TURN


def landing_gear_example():
    """Example with three components."""
    log.info('---- landing gear example ----')
    aut = pinfo.Automaton()
    # large
    # MAX_HEIGHT = 1000
    # MAX_SPEED = 400
    # DOOR_DOWN = 5
    # GEAR_DOWN = 5
    # small
    MAX_HEIGHT = 100
    MAX_SPEED = 40
    DOOR_DOWN = 5
    GEAR_DOWN = 5
    # turns (otherwise `varlist` suffices to declare players)
    aut.players = dict(
        autopilot=1,
        door_module=2,
        gear_module=3,
        scheduler=None)  # the scheduler moves in
                         # a noninterleaving way
    vrs = dict(
        mode=(0, 2),  # 0 = landing, 1 = cruise, 2 = intermediate
        height=(0, MAX_HEIGHT),
        speed=(0, MAX_SPEED),
        door=(0, DOOR_DOWN),
        gear=(0, GEAR_DOWN))
    vrs[TURN] = (1, 3)
    aut.declare_variables(**vrs)
    # aut.declare_constants(**constants)
    aut.varlist = dict(
        autopilot=['mode', 'height', 'speed'],
        door_module=['door'],
        gear_module=['gear'],
        scheduler=[TURN])
    s = r'''
        UNCHANGED_Autopilot ==
            /\ (mode' = mode)
            /\ (height' = height)
            /\ (speed' = speed)

        UNCHANGED_Door ==
            /\ (door' = door)

        UNCHANGED_Gear ==
            /\ (gear' = gear)

        AutopilotInit ==
            /\ mode \in 0 .. 2
            /\ height \in 0 .. {max_height}
            /\ speed \in 0 .. {max_speed}
        DoorInit == door \in 0 .. {door_down}
        GearInit == gear \in 0 .. {gear_down}

        AutopilotInv ==
                # type invariants
            /\ mode \in 0 .. 2
            /\ height \in 0 .. {max_height}
            /\ speed \in 0 .. {max_speed}
                # other invariants
            /\ ((gear != {gear_down}) => (height > {threshold_height}))
            /\ ((mode = 0) => (gear = {gear_down}))
            /\ ((mode = 1) => (gear = 0))
            /\ ((mode = 1) => (door = 0))
            /\ ((height = 0) => (gear = {gear_down}))

        AutopilotTurn == {turn} = 1
        DoorTurn == {turn} = 2
        GearTurn == {turn} = 3

        AutopilotStep ==
            /\ AutopilotTurn

        AutopilotNext ==
            /\ AutopilotInv
            /\ \/ AutopilotStep
               \/ UNCHANGED_Autopilot

        DoorInv ==
            /\ door \in 0 .. {door_down}
            /\ ((speed > {threshold_speed}) => (door = 0))

        DoorStep ==
            /\ DoorTurn

        DoorNext ==
            /\ DoorInv
            /\ \/ DoorStep
               \/ UNCHANGED_Door

        GearInv ==
            /\ gear \in 0 .. {gear_down}
            /\ ((gear != 0) => (door = {door_down}))

        GearStep ==
            /\ GearTurn

        GearNext ==
            /\ GearInv
            /\ \/ GearStep
               \/ UNCHANGED_Gear

        # The autopilot moves first.
        SchedulerInit == ({turn} = 1)

        # The players change in a way interleaving amongst them.
        # The scheduler changes its state in every step.
        # So the scheduler changes in a noninterleaving way
        # with respect to the other players.
        # This is how interleaving can be implemented using
        # a disjoint-state specification.
        SchedulerNext ==
            /\ (({turn} = 1) => ({turn}' = 2))
            /\ (({turn} = 2) => ({turn}' = 3))
            /\ (({turn} = 3) => ({turn}' = 1))
            /\ ({turn} \in 1..3)
        '''.format(
            max_height=MAX_HEIGHT,
            max_speed=MAX_SPEED,
            threshold_height=int(0.75 * MAX_HEIGHT),
            threshold_speed=int(0.75 * MAX_SPEED),
            door_down=DOOR_DOWN,
            gear_down=GEAR_DOWN,
            turn=TURN)
    aut.define(s)
    aut.init_expr = dict(
        autopilot='AutopilotInit',
        door_module='DoorInit',
        gear_module='GearInit',
        scheduler='SchedulerInit')
    aut.action_expr = dict(
        autopilot='AutopilotNext',
        door_module='DoorNext',
        gear_module='GearNext',
        scheduler='SchedulerNext')
    # use lists to enable indexing of communication masks
    aut.win_expr = dict(
        autopilot={
            '[]<>': ['mode = 0', 'mode = 1']},
        gear_module={'[]<>': ['TRUE']},
        door_module={'[]<>': ['TRUE']},
        scheduler={'[]<>': ['TRUE']})
    aut.build()
    aut.assert_consistent()
    log.info('==== landing gear example ====\n')
    return aut


def charging_station_example():
    """Example with two components."""
    log.info('---- charging station example ----')
    aut = pinfo.Automaton()
    aut.players = dict(
        station=1,
        robot=2,
        others=None,
        scheduler=None)
    vrs = dict(
        spot_1=(0, 1),
        spot_2=(0, 1),
        free_x=(0, 18),
        free_y=(0, 18),
        free=(0, 1),
        req=(0, 1),
        pos_x=(1, 15),
        pos_y=(1, 15),
        occ=(1, 3))
    vrs[TURN] = (1, 2)
    aut.declare_variables(**vrs)
    aut.varlist = dict(
        station=[
            'spot_1', 'spot_2',
            'free_x', 'free_y', 'free'],
        robot=['pos_x', 'pos_y', 'req'],
        others=['occ'],
        scheduler=[TURN])
    s = r'''
        StationInit ==
            /\ spot_1 = 0
            /\ spot_2 = 0
            /\ free_x = 0
            /\ free_y = 0
            /\ free = 0
        RobotInit == /\ pos_x = 0
                     /\ pos_y = 0
        OthersInit == occ \in 1..3
        SchedulerInit == {turn} \in 1..2

        StationTypeInv ==
            /\ spot_1 \in 0..1
            /\ spot_2 \in 0..1
            /\ free_x \in 0..18
            /\ free_y \in 0..18
            /\ free \in 0..1
        UNCHANGED_Station ==
            /\ (spot_1' = spot_1)
            /\ (spot_2' = spot_2)
            /\ (free_x' = free_x)
            /\ (free_y' = free_y)
            /\ (free' = free)
        StationTurn == {turn} = 1
        StationInv ==
            /\ StationTypeInv
            /\ ( \/ (free = 0)
                 \/ (free_x = 1 /\ free_y = 1 /\ spot_1 = 0)
                 \/ (free_x = 2 /\ free_y = 1 /\ spot_2 = 0)
               )
            /\ ( (free = 1) => (
                 /\ (spot_1 = 0  =>  occ != 1)
                 /\ (spot_2 = 0  =>  occ != 2)
               ))
        StationStep ==
            /\ StationTurn
            /\ ((req = 0) => (free' = 0))
        StationNext ==
            /\ StationInv
            /\ \/ StationStep
               \/ UNCHANGED_Station

        RobotTypeInv ==
            /\ pos_x \in 1..15
            /\ pos_y \in 1..15
            /\ req \in 0..1
        UNCHANGED_Robot ==
            /\ (pos_x' = pos_x)
            /\ (pos_y' = pos_y)
            /\ (req' = req)
        RobotTurn == {turn} = 2
        RobotNext ==
            /\ RobotTypeInv
            /\ (  (req = 1 /\ req' = 0)
                  => ( /\ free = 1
                       /\ free_x = pos_x'
                       /\ free_y = pos_y' ) )
            /\ \/ RobotTurn
               \/ UNCHANGED_Robot

        OthersTypeInv == occ \in 1..3
        OthersNext ==
            /\ OthersTypeInv
            /\ (occ' = occ)

        SchedulerTypeInv == ({turn} \in 1..2)
        SchedulerNext ==
            /\ SchedulerTypeInv
            /\ (({turn} = 1) => ({turn}' = 2))
            /\ (({turn} = 2) => ({turn}' = 1))
        '''.format(
            turn=TURN)
    aut.define(s)
    aut.init_expr = dict(
        station='StationInit',
        robot='RobotInit',
        others='OthersInit',
        scheduler='SchedulerInit')
    aut.action_expr = dict(
        station='StationNext',
        robot='RobotNext',
        others='OthersNext',
        scheduler='SchedulerNext')
    aut.win_expr = dict(
        robot={
            '[]<>': ['req = 0', 'req = 1']},
        station={'[]<>': ['TRUE']},
        others={'[]<>': ['TRUE']},
        scheduler={'[]<>': ['TRUE']})
    s = '''
        /\ StationTypeInv
        /\ RobotTypeInv
        /\ OthersTypeInv
        /\ SchedulerTypeInv
        '''
    aut.build()
    aut.type_invariant = aut.add_expr(s, with_ops=True)
    aut.assert_consistent()
    log.info('==== charging station example ====\n')
    return aut


if __name__ == '__main__':
    handler = logging.StreamHandler()
    formatter = logging.Formatter('%(levelname)s\t%(message)s')
    handler.setFormatter(formatter)
    # `dd` logger
    log = logging.getLogger('dd')
    log.setLevel(logging.ERROR)
    # `omega` logger
    logger = logging.getLogger('omega')
    logger.setLevel(logging.WARNING)
    logger.addHandler(handler)
    logger = logging.getLogger('omega.symbolic.cover')
    logger.setLevel(logging.ERROR)
    logger.addHandler(handler)
    # `synthesizer` logger
    logger = logging.getLogger('synthesizer.contracts_pinfo')
    logger.setLevel(logging.INFO)
    # stream to stdout
    logger.addHandler(handler)
    aut = landing_gear_example()
    # aut = charging_station_example()
    pinfo.main(aut)
