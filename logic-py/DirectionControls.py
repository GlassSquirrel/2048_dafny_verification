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

# Module: DirectionControls

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def left(game):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        d_0_g1_: _dafny.Seq
        d_1_d1_: bool
        out0_: _dafny.Seq
        out1_: bool
        out0_, out1_ = Move.default__.move(game)
        d_0_g1_ = out0_
        d_1_d1_ = out1_
        d_2_g2_: _dafny.Seq
        d_3_d2_: bool
        out2_: _dafny.Seq
        out3_: bool
        out2_, out3_ = Merge.default__.merge(d_0_g1_)
        d_2_g2_ = out2_
        d_3_d2_ = out3_
        d_4_g3_: _dafny.Seq
        d_5_d3_: bool
        out4_: _dafny.Seq
        out5_: bool
        out4_, out5_ = Move.default__.move(d_2_g2_)
        d_4_g3_ = out4_
        d_5_d3_ = out5_
        res = d_4_g3_
        done = ((d_1_d1_) or (d_3_d2_)) or (d_5_d3_)
        return res, done

