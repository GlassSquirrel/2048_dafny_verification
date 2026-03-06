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

# Module: Merge

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def merge__pair(row, j):
        d_0_r1_ = (row).set(j, ((row)[j]) * (2))
        d_1_r2_ = (d_0_r1_).set((j) + (1), 0)
        return d_1_r2_

    @staticmethod
    def update__count(counts, j):
        return ((counts).set(j, ((counts)[j]) + (1))).set((j) + (1), ((counts)[(j) + (1)]) + (1))

    @staticmethod
    def MergeableAt(row, j):
        return ((((0) <= (j)) and ((j) < ((len(row)) - (1)))) and (((row)[j]) != (0))) and (((row)[j]) == ((row)[(j) + (1)]))

    @staticmethod
    def NoMergeableBefore(row, j):
        def lambda0_(forall_var_0_):
            d_0_k_: int = forall_var_0_
            return not (((0) <= (d_0_k_)) and ((d_0_k_) < (j))) or (not(default__.MergeableAt(row, d_0_k_)))

        return _dafny.quantifier(_dafny.IntegerRange(0, j), True, lambda0_)

    @staticmethod
    def merge(grid):
        res: _dafny.Seq = _dafny.Seq({})
        done: bool = False
        res = grid
        done = False
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < (Setups.default__.N):
            d_1_j_: int
            d_1_j_ = 0
            d_2_merged__counts_: _dafny.Seq
            d_2_merged__counts_ = _dafny.SeqWithoutIsStrInference([0 for d_3___v0_ in range(Setups.default__.N)])
            d_4_first__merge__j_: int
            d_4_first__merge__j_ = -1
            while (d_1_j_) < ((Setups.default__.N) - (1)):
                if ((((((res)[d_0_i_])[d_1_j_]) == (((res)[d_0_i_])[(d_1_j_) + (1)])) and ((((res)[d_0_i_])[d_1_j_]) != (0))) and (((d_2_merged__counts_)[d_1_j_]) == (0))) and (((d_2_merged__counts_)[(d_1_j_) + (1)]) == (0)):
                    if (d_4_first__merge__j_) == (-1):
                        d_4_first__merge__j_ = d_1_j_
                    d_5_count__before_: int
                    d_5_count__before_ = Setups.default__.CountNonZerosGrid(res)
                    d_6_val__before__merge_: int
                    d_6_val__before__merge_ = ((res)[d_0_i_])[(d_1_j_) + (1)]
                    d_7_old__res_: _dafny.Seq
                    d_7_old__res_ = res
                    d_8_updatedRow_: _dafny.Seq
                    d_8_updatedRow_ = default__.merge__pair((res)[d_0_i_], d_1_j_)
                    res = (res).set(d_0_i_, d_8_updatedRow_)
                    d_2_merged__counts_ = default__.update__count(d_2_merged__counts_, d_1_j_)
                    done = True
                    d_1_j_ = (d_1_j_) + (2)
                elif True:
                    d_1_j_ = (d_1_j_) + (1)
            d_0_i_ = (d_0_i_) + (1)
        return res, done

