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
        return _dafny.SeqWithoutIsStrInference([(row)[3], (row)[2], (row)[1], (row)[0]])

    @staticmethod
    def Reverse(grid):
        return _dafny.SeqWithoutIsStrInference([default__.ReverseRow((grid)[0]), default__.ReverseRow((grid)[1]), default__.ReverseRow((grid)[2]), default__.ReverseRow((grid)[3])])

    @staticmethod
    def Transpose(grid):
        return _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference([((grid)[0])[0], ((grid)[1])[0], ((grid)[2])[0], ((grid)[3])[0]]), _dafny.SeqWithoutIsStrInference([((grid)[0])[1], ((grid)[1])[1], ((grid)[2])[1], ((grid)[3])[1]]), _dafny.SeqWithoutIsStrInference([((grid)[0])[2], ((grid)[1])[2], ((grid)[2])[2], ((grid)[3])[2]]), _dafny.SeqWithoutIsStrInference([((grid)[0])[3], ((grid)[1])[3], ((grid)[2])[3], ((grid)[3])[3]])])

