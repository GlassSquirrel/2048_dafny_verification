import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Setups as Setups
import Init as Init
import Move as Move
import Merge as Merge

# Module: Transform

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ReverseRow(row):
        return _dafny.SeqWithoutIsStrInference([(row)[((Setups.default__.N) - (1)) - (d_0_j_)] for d_0_j_ in range(Setups.default__.N)])

    @staticmethod
    def Reverse(grid):
        return _dafny.SeqWithoutIsStrInference([default__.ReverseRow((grid)[d_0_i_]) for d_0_i_ in range(Setups.default__.N)])

    @staticmethod
    def twotilesadjacent(i, j, grid):
        return Setups.default__.VerticalPair(i, j, grid)

    @staticmethod
    def twotilesadjacentrow(i, j, grid):
        return Setups.default__.HorizontalPair(i, j, grid)

    @staticmethod
    def Transpose(grid):
        return _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference([((grid)[d_0_j_])[d_1_i_] for d_0_j_ in range(Setups.default__.N)]) for d_1_i_ in range(Setups.default__.N)])

