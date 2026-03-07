import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Setups as Setups
import Init as Init

# Module: Move

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def HasWinTileRow(row):
        def lambda0_(exists_var_0_):
            d_0_j_: int = exists_var_0_
            return (((0) <= (d_0_j_)) and ((d_0_j_) < (len(row)))) and (((row)[d_0_j_]) == (2048))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(row)), False, lambda0_)

    @staticmethod
    def FilterNonZeros(s):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif ((s)[0]) != (0):
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference([(s)[0]]))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
                    raise _dafny.TailCall()
                elif True:
                    in1_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CompressRow(row):
        d_0_nonZeros_ = default__.FilterNonZeros(row)
        d_1_zeroFill_ = _dafny.SeqWithoutIsStrInference([0 for d_2___v14_ in range((Setups.default__.N) - (len(d_0_nonZeros_)))])
        d_3_padded_ = (d_0_nonZeros_) + (d_1_zeroFill_)
        return (d_3_padded_, (d_3_padded_) != (row))

    @staticmethod
    def move(mat):
        new__mat: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        d_0_temp__grid_: _dafny.Seq
        d_0_temp__grid_ = _dafny.SeqWithoutIsStrInference([])
        done = False
        hi0_ = Setups.default__.N
        for d_1_i_ in range(0, hi0_):
            d_2_res_: tuple
            d_2_res_ = default__.CompressRow((mat)[d_1_i_])
            d_3_row__res_: _dafny.Seq
            d_3_row__res_ = (d_2_res_)[0]
            d_4_row__changed_: bool
            d_4_row__changed_ = (d_2_res_)[1]
            if d_4_row__changed_:
                done = True
            d_5_old__temp_: _dafny.Seq
            d_5_old__temp_ = d_0_temp__grid_
            d_0_temp__grid_ = (d_0_temp__grid_) + (_dafny.SeqWithoutIsStrInference([d_3_row__res_]))
            if done:
                if d_4_row__changed_:
                    pass
                elif True:
                    d_6_k_: int
                    with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                        assign_such_that_0_: int
                        for assign_such_that_0_ in _dafny.IntegerRange(0, d_1_i_):
                            d_6_k_ = assign_such_that_0_
                            if (((0) <= (d_6_k_)) and ((d_6_k_) < (d_1_i_))) and (((d_0_temp__grid_)[d_6_k_]) != ((mat)[d_6_k_])):
                                raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                        raise Exception("assign-such-that search produced no value")
                        pass
        new__mat = d_0_temp__grid_
        if not(done):
            pass
        elif True:
            d_7_k_: int
            with _dafny.label("_ASSIGN_SUCH_THAT_d_1"):
                assign_such_that_1_: int
                for assign_such_that_1_ in _dafny.IntegerRange(0, Setups.default__.N):
                    d_7_k_ = assign_such_that_1_
                    if (((0) <= (d_7_k_)) and ((d_7_k_) < (Setups.default__.N))) and ((default__.CompressRow((mat)[d_7_k_]))[1]):
                        raise _dafny.Break("_ASSIGN_SUCH_THAT_d_1")
                raise Exception("assign-such-that search produced no value")
                pass
        if Setups.default__.HasWinTile(mat):
            d_8_r_: int
            d_9_c_: int
            with _dafny.label("_ASSIGN_SUCH_THAT_d_2"):
                assign_such_that_2_: int
                for assign_such_that_2_ in _dafny.IntegerRange(0, Setups.default__.N):
                    d_8_r_ = assign_such_that_2_
                    assign_such_that_3_: int
                    for assign_such_that_3_ in _dafny.IntegerRange(0, Setups.default__.N):
                        d_9_c_ = assign_such_that_3_
                        if ((((0) <= (d_8_r_)) and ((d_8_r_) < (Setups.default__.N))) and (((0) <= (d_9_c_)) and ((d_9_c_) < (Setups.default__.N)))) and ((((mat)[d_8_r_])[d_9_c_]) == (2048)):
                            raise _dafny.Break("_ASSIGN_SUCH_THAT_d_2")
                raise Exception("assign-such-that search produced no value")
                pass
        if not(Setups.default__.HasWinTile(mat)):
            if Setups.default__.HasWinTile(new__mat):
                d_10_r_: int
                d_11_c_: int
                with _dafny.label("_ASSIGN_SUCH_THAT_d_3"):
                    assign_such_that_4_: int
                    for assign_such_that_4_ in _dafny.IntegerRange(0, Setups.default__.N):
                        d_10_r_ = assign_such_that_4_
                        assign_such_that_5_: int
                        for assign_such_that_5_ in _dafny.IntegerRange(0, Setups.default__.N):
                            d_11_c_ = assign_such_that_5_
                            if ((((0) <= (d_10_r_)) and ((d_10_r_) < (Setups.default__.N))) and (((0) <= (d_11_c_)) and ((d_11_c_) < (Setups.default__.N)))) and ((((new__mat)[d_10_r_])[d_11_c_]) == (2048)):
                                raise _dafny.Break("_ASSIGN_SUCH_THAT_d_3")
                    raise Exception("assign-such-that search produced no value")
                    pass
        rhs0_ = new__mat
        rhs1_ = done
        new__mat = rhs0_
        done = rhs1_
        return new__mat, done
        return new__mat, done

