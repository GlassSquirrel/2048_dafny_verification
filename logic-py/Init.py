import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Setups as Setups

# Module: Init

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def new__game():
        grid: _dafny.Seq = _dafny.Seq({})
        d_0_row_: _dafny.Seq
        d_0_row_ = _dafny.SeqWithoutIsStrInference([0 for d_1___v0_ in range(Setups.default__.N)])
        grid = _dafny.SeqWithoutIsStrInference([d_0_row_ for d_2___v1_ in range(Setups.default__.N)])
        return grid

    @staticmethod
    def IsValidInitialBoard(grid):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            return not (((0) <= (d_0_i_)) and ((d_0_i_) < (Setups.default__.N))) or ((len((grid)[d_0_i_])) == (Setups.default__.N))

        def lambda1_(forall_var_1_):
            def lambda2_(forall_var_2_):
                d_2_j_: int = forall_var_2_
                return not ((((0) <= (d_1_i_)) and ((d_1_i_) < (Setups.default__.N))) and (((0) <= (d_2_j_)) and ((d_2_j_) < (Setups.default__.N)))) or (((((grid)[d_1_i_])[d_2_j_]) == (0)) or ((((grid)[d_1_i_])[d_2_j_]) == (2)))

            d_1_i_: int = forall_var_1_
            return _dafny.quantifier(_dafny.IntegerRange(0, Setups.default__.N), True, lambda2_)

        return ((((len(grid)) == (Setups.default__.N)) and (_dafny.quantifier(_dafny.IntegerRange(0, Setups.default__.N), True, lambda0_))) and (_dafny.quantifier(_dafny.IntegerRange(0, Setups.default__.N), True, lambda1_))) and ((Setups.default__.CountInGrid(grid, 2)) == (2))

    @staticmethod
    def initial__grid__validation(grid):
        b: bool = False
        b = default__.IsValidInitialBoard(grid)
        return b
        return b

    @staticmethod
    def game__state(grid):
        s: State = State.default()()
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < (Setups.default__.N):
            d_1_j_: int
            d_1_j_ = 0
            while (d_1_j_) < (Setups.default__.N):
                if (((grid)[d_0_i_])[d_1_j_]) == (2048):
                    s = State_Win()
                    return s
                d_1_j_ = (d_1_j_) + (1)
            d_0_i_ = (d_0_i_) + (1)
        d_0_i_ = 0
        while (d_0_i_) < (Setups.default__.N):
            d_2_j_: int
            d_2_j_ = 0
            while (d_2_j_) < (Setups.default__.N):
                if (((grid)[d_0_i_])[d_2_j_]) == (0):
                    s = State_NotOver()
                    return s
                d_2_j_ = (d_2_j_) + (1)
            d_0_i_ = (d_0_i_) + (1)
        d_0_i_ = 0
        while (d_0_i_) < (Setups.default__.N):
            d_3_j_: int
            d_3_j_ = 0
            while (d_3_j_) < ((Setups.default__.N) - (1)):
                if (((grid)[d_0_i_])[d_3_j_]) == (((grid)[d_0_i_])[(d_3_j_) + (1)]):
                    s = State_NotOver()
                    return s
                d_3_j_ = (d_3_j_) + (1)
            d_0_i_ = (d_0_i_) + (1)
        d_0_i_ = 0
        while (d_0_i_) < ((Setups.default__.N) - (1)):
            d_4_j_: int
            d_4_j_ = 0
            while (d_4_j_) < (Setups.default__.N):
                if (((grid)[d_0_i_])[d_4_j_]) == (((grid)[(d_0_i_) + (1)])[d_4_j_]):
                    s = State_NotOver()
                    return s
                d_4_j_ = (d_4_j_) + (1)
            d_0_i_ = (d_0_i_) + (1)
        s = State_Lose()
        return s
        return s


class State:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [State_Win(), State_NotOver(), State_Lose()]
    @classmethod
    def default(cls, ):
        return lambda: State_Win()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Win(self) -> bool:
        return isinstance(self, State_Win)
    @property
    def is_NotOver(self) -> bool:
        return isinstance(self, State_NotOver)
    @property
    def is_Lose(self) -> bool:
        return isinstance(self, State_Lose)

class State_Win(State, NamedTuple('Win', [])):
    def __dafnystr__(self) -> str:
        return f'Init.State.Win'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, State_Win)
    def __hash__(self) -> int:
        return super().__hash__()

class State_NotOver(State, NamedTuple('NotOver', [])):
    def __dafnystr__(self) -> str:
        return f'Init.State.NotOver'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, State_NotOver)
    def __hash__(self) -> int:
        return super().__hash__()

class State_Lose(State, NamedTuple('Lose', [])):
    def __dafnystr__(self) -> str:
        return f'Init.State.Lose'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, State_Lose)
    def __hash__(self) -> int:
        return super().__hash__()

