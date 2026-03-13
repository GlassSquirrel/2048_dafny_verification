import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: Setups

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ValidGrid(grid):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            return not (((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) or ((len((grid)[d_0_i_])) == (default__.N))

        return ((len(grid)) == (default__.N)) and (_dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda0_))

    @staticmethod
    def IsPowerOfTwo(x):
        if (x) < (2):
            return False
        elif (x) == (2):
            return True
        elif True:
            return ((_dafny.euclidian_modulus(x, 2)) == (0)) and (default__.IsPowerOfTwo(_dafny.euclidian_division(x, 2)))

    @staticmethod
    def ValidValues(grid):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_1_j_: int = forall_var_1_
                return not ((((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (default__.N)))) or (((((grid)[d_0_i_])[d_1_j_]) == (0)) or (default__.IsPowerOfTwo(((grid)[d_0_i_])[d_1_j_])))

            d_0_i_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda0_)

    @staticmethod
    def HasWinTile(grid):
        def lambda0_(exists_var_0_):
            def lambda1_(exists_var_1_):
                d_1_j_: int = exists_var_1_
                return ((((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (default__.N)))) and ((((grid)[d_0_i_])[d_1_j_]) == (2048))

            d_0_i_: int = exists_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda0_)

    @staticmethod
    def HasEmptyTile(grid):
        def lambda0_(exists_var_0_):
            def lambda1_(exists_var_1_):
                d_1_j_: int = exists_var_1_
                return ((((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (default__.N)))) and ((((grid)[d_0_i_])[d_1_j_]) == (0))

            d_0_i_: int = exists_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda1_)

        return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda0_)

    @staticmethod
    def HorizontalPair(i, j, grid):
        return ((((0) <= (i)) and ((i) < (default__.N))) and (((0) <= (j)) and ((j) < ((default__.N) - (1))))) and ((((grid)[i])[j]) == (((grid)[i])[(j) + (1)]))

    @staticmethod
    def VerticalPair(i, j, grid):
        return ((((0) <= (i)) and ((i) < ((default__.N) - (1)))) and (((0) <= (j)) and ((j) < (default__.N)))) and ((((grid)[i])[j]) == (((grid)[(i) + (1)])[j]))

    @staticmethod
    def MoreToMerge(grid):
        def lambda0_(exists_var_0_):
            def lambda1_(exists_var_1_):
                d_1_j_: int = exists_var_1_
                return ((((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) and (((0) <= (d_1_j_)) and ((d_1_j_) < ((default__.N) - (1))))) and (default__.HorizontalPair(d_0_i_, d_1_j_, grid))

            d_0_i_: int = exists_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, (default__.N) - (1)), False, lambda1_)

        def lambda2_(exists_var_2_):
            def lambda3_(exists_var_3_):
                d_3_j_: int = exists_var_3_
                return ((((0) <= (d_2_i_)) and ((d_2_i_) < ((default__.N) - (1)))) and (((0) <= (d_3_j_)) and ((d_3_j_) < (default__.N)))) and (default__.VerticalPair(d_2_i_, d_3_j_, grid))

            d_2_i_: int = exists_var_2_
            return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda3_)

        return (_dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda0_)) or (_dafny.quantifier(_dafny.IntegerRange(0, (default__.N) - (1)), False, lambda2_))

    @staticmethod
    def IsLose(grid):
        return ((not(default__.HasWinTile(grid))) and (not(default__.HasEmptyTile(grid)))) and (not(default__.MoreToMerge(grid)))

    @staticmethod
    def CountNonZerosRow(s):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((1 if ((s)[0]) != (0) else 0))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[1::])
                    s = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CountNonZerosGrid(g):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(g)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (default__.CountNonZerosRow((g)[0]))
                    in0_ = _dafny.SeqWithoutIsStrInference((g)[1::])
                    g = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CountInRow(row, value):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(row)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((1 if ((row)[0]) == (value) else 0))
                    in0_ = _dafny.SeqWithoutIsStrInference((row)[1::])
                    in1_ = value
                    row = in0_
                    value = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def CountInGrid(grid, value):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(grid)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (default__.CountInRow((grid)[0], value))
                    in0_ = _dafny.SeqWithoutIsStrInference((grid)[1::])
                    in1_ = value
                    grid = in0_
                    value = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def WellPerformedRow(row):
        def lambda0_(forall_var_0_):
            d_0_k_: int = forall_var_0_
            return not (((0) <= (d_0_k_)) and ((d_0_k_) < ((len(row)) - (1)))) or (not (((row)[d_0_k_]) == (0)) or (((row)[(d_0_k_) + (1)]) == (0)))

        return _dafny.quantifier(_dafny.IntegerRange(0, (len(row)) - (1)), True, lambda0_)

    @staticmethod
    def WellPerformedGrid(grid):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            return not (((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) or (default__.WellPerformedRow((grid)[d_0_i_]))

        return (default__.ValidGrid(grid)) and (_dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda0_))

    @staticmethod
    def new__tile__validation(oldGrid, changed, newGrid):
        ok: bool = False
        def lambda0_(exists_var_0_):
            def lambda1_(exists_var_1_):
                def lambda2_(forall_var_0_):
                    def lambda3_(forall_var_1_):
                        d_3_c_: int = forall_var_1_
                        return not (((((0) <= (d_2_r_)) and ((d_2_r_) < (default__.N))) and (((0) <= (d_3_c_)) and ((d_3_c_) < (default__.N)))) and (((d_2_r_) != (d_0_i_)) or ((d_3_c_) != (d_1_j_)))) or ((((newGrid)[d_2_r_])[d_3_c_]) == (((oldGrid)[d_2_r_])[d_3_c_]))

                    d_2_r_: int = forall_var_0_
                    return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda3_)

                d_1_j_: int = exists_var_1_
                return ((((((0) <= (d_0_i_)) and ((d_0_i_) < (default__.N))) and (((0) <= (d_1_j_)) and ((d_1_j_) < (default__.N)))) and ((((oldGrid)[d_0_i_])[d_1_j_]) == (0))) and ((((newGrid)[d_0_i_])[d_1_j_]) == (2))) and (_dafny.quantifier(_dafny.IntegerRange(0, default__.N), True, lambda2_))

            d_0_i_: int = exists_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda1_)

        ok = ((((default__.ValidGrid(oldGrid)) and (default__.ValidValues(oldGrid))) and (default__.ValidGrid(newGrid))) and (default__.ValidValues(newGrid))) and (((not(changed)) and ((newGrid) == (oldGrid))) or ((changed) and (_dafny.quantifier(_dafny.IntegerRange(0, default__.N), False, lambda0_))))
        return ok

    @_dafny.classproperty
    def N(instance):
        return 4
