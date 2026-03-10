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
import Transform as Transform
import DirectionControls as DirectionControls

# Module: Logic

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def new__game__wrapper():
        g: _dafny.Seq = _dafny.Seq({})
        out0_: _dafny.Seq
        out0_ = Init.default__.new__game()
        g = out0_
        return g

    @staticmethod
    def initial__grid__validation__wrapper(grid):
        b: bool = False
        out0_: bool
        out0_ = Init.default__.initial__grid__validation(grid)
        b = out0_
        return b

    @staticmethod
    def game__state__wrapper(grid):
        s: Init.State = Init.State.default()()
        out0_: Init.State
        out0_ = Init.default__.game__state(grid)
        s = out0_
        return s

    @staticmethod
    def left__wrapper(grid):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        out0_: _dafny.Seq
        out1_: bool
        out0_, out1_ = DirectionControls.default__.left(grid)
        res = out0_
        done = out1_
        return res, done

    @staticmethod
    def right__wrapper(grid):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        out0_: _dafny.Seq
        out1_: bool
        out0_, out1_ = DirectionControls.default__.right(grid)
        res = out0_
        done = out1_
        return res, done

    @staticmethod
    def up__wrapper(grid):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        out0_: _dafny.Seq
        out1_: bool
        out0_, out1_ = DirectionControls.default__.up(grid)
        res = out0_
        done = out1_
        return res, done

    @staticmethod
    def down__wrapper(grid):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        out0_: _dafny.Seq
        out1_: bool
        out0_, out1_ = DirectionControls.default__.down(grid)
        res = out0_
        done = out1_
        return res, done

    @staticmethod
    def new__tile__validation__wrapper(oldGrid, moved, newGrid):
        ok: bool = False
        out0_: bool
        out0_ = Setups.default__.new__tile__validation(oldGrid, moved, newGrid)
        ok = out0_
        return ok

