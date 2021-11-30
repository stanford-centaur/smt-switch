import typing as tp

try:
    from pysmt import logics
    from pysmt.solvers.solver import Solver as SolverT
    from pysmt.exceptions import NoSolverAvailableError, NoLogicAvailableError
    from pysmt.environment import get_env
except:
    raise ImportError('Skipping pysmt_frontend since pysmt is not available')

from .pysmt_solver import SWITCH_SOLVERS

__ALL__ = ['SWITCH_SOLVERS', 'Solver']


try:
    from .pysmt_solver import SwitchBtor
    __ALL__.append('SwitchBtor')
except ImportError:
    pass

try:
    from .pysmt_solver import SwitchCvc5
    __ALL__.append('SwitchCvc5')
except ImportError:
    pass

try:
    from .pysmt_solver import SwitchMsat
    __ALL__.append('SwitchMsat')
except ImportError:
    pass

def Solver(name: str, logic: tp.Optional[logics.Logic]=None) -> SolverT:
    '''
    Convience function for building a pysmt solver object with a switch backend.
    Similar to `pysmt.shortcuts.Solver`.
    '''
    try:
        cls = SWITCH_SOLVERS[name]
    except KeyError:
        raise NoSolverAvailableError(f"Solver '{name}' is not available") from None

    if isinstance(logic, str):
        logic = logics.convert_logic_from_string(logic)
    elif logic is None:
        # Try to use the most general logic supported
        try:
            logic = logics.most_generic_logic(cls.LOGICS)
        except NoLogicAvailableError:
            # supported logics do not have a single "upper bound"
            # Check for some reasonable ones
            if logics.QF_UFLIRA in cls.LOGICS:
                logic = logics.QF_UFLIRA
            elif logics.QF_AUFBV in cls.LOGICS:
                logic = logics.QF_AUFBV
            else:
                # use the first one
                logic = cls.LOGICS[0]

    return cls(environment=get_env(), logic=logic)
