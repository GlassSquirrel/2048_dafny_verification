module Setups {
    type Grid = seq<seq<int>>
    const N: int := 4

    /***********
    Basic Specs
    ************/
    // Spec 5: board boundry
    predicate ValidGrid(grid: Grid) 
    {
        |grid| == N && forall i :: 0 <= i < N ==> |grid[i]| == N
    }

    predicate IsPowerOfTwo(x: int)
    {
        if x < 2 then false
        else if x == 2 then true
        else x % 2 == 0 && IsPowerOfTwo(x / 2)
    }

    // Spec 2: valid tile values
    predicate ValidValues(grid: Grid)
        requires ValidGrid(grid)
    {
        forall i, j :: 0 <= i < N && 0 <= j < N ==> grid[i][j] == 0 || IsPowerOfTwo(grid[i][j])
    }

    lemma SeqElementsValidImpliesIndexValid(row: seq<int>)
        requires forall x :: x in row ==> x == 0 || IsPowerOfTwo(x)
        ensures forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
    {
    }

    /*************************
    Predicates for Game State 
    **************************/
    // Define 4 predicates to check for "has win" / "is lose" / "can continue"
    // Predicate 1: has win (tile value reaches 2048)
    predicate HasWinTile(grid: Grid)
        requires ValidGrid(grid)
        requires ValidValues(grid)
    {
        exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 2048
    }

    // {Predicate 2: has empty tile value = 0 (can generate new 2)  =>  can continue
    predicate HasEmptyTile(grid: Grid)
        requires ValidGrid(grid)
        requires ValidValues(grid)
    {
        exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 0
    }

    // Predicate 3: has more room to merge  =>  can continue
    predicate MoreToMerge(grid: Grid)
        requires ValidGrid(grid)
        requires ValidValues(grid)
    {
        // rows
        (exists i, j :: 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j+1]) ||
        // columns
        (exists i, j {:trigger grid[i][j]} :: 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i+1][j])
    }

    // Predicate 4: State indicates lose
    predicate IsLose(grid: Grid)
        requires ValidGrid(grid)
        requires ValidValues(grid)
    {
        !HasWinTile(grid) && !HasEmptyTile(grid) && !MoreToMerge(grid)
    }

    // we develop an axiom for the for predicates
    lemma ImpliesNotLose(grid: Grid)
        requires ValidGrid(grid)
        requires ValidValues(grid)
        ensures HasEmptyTile(grid) ==> !IsLose(grid)
    {
        if (HasEmptyTile(grid)) {
            assert HasWinTile(grid) || HasEmptyTile(grid) || MoreToMerge(grid);
            assert !IsLose(grid);
        }
    }

    /*************************
    Functions frequently used
    **************************/
    /*****************************************
    (1) Count number of elements in a row/grid
    ******************************************/
    // count the number of non-zero elements in a row
    function CountNonZerosRow(s: seq<int>): nat    
    {
        if |s| == 0 then 0
        else (if s[0] != 0 then 1 else 0) + CountNonZerosRow(s[1..])
    }

    // count the number of non-zero elements in a grid
    function CountNonZerosGrid(g: Grid): nat    
    {
        if |g| == 0 then 0
        else CountNonZerosRow(g[0]) + CountNonZerosGrid(g[1..])
    }

    // count the number of elements with specific value in a row
    function CountInRow(row: seq<int>, value: int): int 
    {
        if |row| == 0 then 0
        else (if row[0] == value then 1 else 0) + CountInRow(row[1..], value)
    }

    // count the number of elements with specific value in a grid
    function CountInGrid(grid: Grid, value: int): int
    {
        if |grid| == 0 then 0
        else CountInRow(grid[0], value) + CountInGrid(grid[1..], value)
    }

    // Lemmas based on above:
    // Lemma 1: Count(a + b) == Count(a) + Count(b)
    lemma CountRowAdditivity(a: seq<int>, b: seq<int>)
        ensures CountNonZerosRow(a + b) == CountNonZerosRow(a) + CountNonZerosRow(b)
        // decreases |a|
    {
        if |a| == 0 {
            // a = []
            assert a + b == b;
            assert CountNonZerosRow(a) == 0;
        } else {
            CountRowAdditivity(a[1..], b);

            assert a == [a[0]] + a[1..];
            assert a + b == [a[0]] + (a[1..] + b);

            assert CountNonZerosRow(a) == (if a[0] != 0 then 1 else 0) + CountNonZerosRow(a[1..]);
            assert CountNonZerosRow(a + b) == (if a[0] != 0 then 1 else 0) + CountNonZerosRow(a[1..] + b);
        }
    }

    // Lemma 2: CountNonZerosRow(sequence of 0s) = 0
    lemma ZerosCountIsZero(k: nat)
        ensures CountNonZerosRow(seq(k, _ => 0)) == 0
        decreases k
    {
        if k == 0 {
            assert seq(0, _ => 0) == [];
        } else {
            ZerosCountIsZero(k - 1);
            assert seq(k, _ => 0) == [0] + seq(k - 1, _ => 0);
            assert CountNonZerosRow(seq(k, _ => 0)) == (if 0 != 0 then 1 else 0) + CountNonZerosRow(seq(k - 1, _ => 0));
        }
    }

    // Lemma 3: CountNonZerosRow(sequence of non-zeros) = |sequence of non-zeros|
    lemma NonZerosCountIsLength(s: seq<int>)
        requires forall x :: x in s ==> x != 0
        ensures CountNonZerosRow(s) == |s|
        decreases |s|
    {
        if |s| == 0 {
        } else {
            assert s[0] in s;
            assert s[0] != 0;
            assert forall x :: x in s[1..] ==> x != 0
            by {
                forall x | x in s[1..]
                ensures x != 0
                {
                    assert x in s;
                }
            }
            NonZerosCountIsLength(s[1..]);
            assert CountNonZerosRow(s) == 1 + CountNonZerosRow(s[1..]);
            assert |s| == 1 + |s[1..]|;
        }
    }

    // Lemma 4: CountNonZerosGrid additivity
    lemma CountGridAdditivity(temp: seq<seq<int>>, row: seq<int>)
        ensures CountNonZerosGrid(temp + [row]) == CountNonZerosGrid(temp) + CountNonZerosRow(row)
        // decreases |temp|
    {
        if temp == [] {
            // temp + [row] == [row]
            assert temp + [row] == [row];
            assert CountNonZerosGrid([row]) == CountNonZerosRow(row);
        } else {
            CountGridAdditivity(temp[1..], row);
            assert temp == [temp[0]] + temp[1..];
            assert temp + [row] == [temp[0]] + (temp[1..] + [row]);
            assert CountNonZerosGrid(temp) == CountNonZerosRow(temp[0]) + CountNonZerosGrid(temp[1..]);
            assert CountNonZerosGrid(temp + [row]) == CountNonZerosRow(temp[0]) + CountNonZerosGrid(temp[1..] + [row]);
        }
    }

    // Lemma 5: equal addition of CountGrid
    lemma GridEqualityAfterAppend(g1: seq<seq<int>>, g2: seq<seq<int>>, row1: seq<int>, row2: seq<int>)
        requires CountNonZerosGrid(g1) == CountNonZerosGrid(g2)
        requires CountNonZerosRow(row1) == CountNonZerosRow(row2)
        ensures CountNonZerosGrid(g1 + [row1]) == CountNonZerosGrid(g2 + [row2])
    {
        CountGridAdditivity(g1, row1);
        CountGridAdditivity(g2, row2);
        
        // Count(g1 + [row1]) = Count(g1) + Count(row1)
        // Count(g2 + [row2]) = Count(g2) + Count(row2)
        assert CountNonZerosGrid(g1 + [row1]) == CountNonZerosGrid(g1) + CountNonZerosRow(row1);
        assert CountNonZerosGrid(g2 + [row2]) == CountNonZerosGrid(g2) + CountNonZerosRow(row2);
        assert CountNonZerosGrid(g1) + CountNonZerosRow(row1) == CountNonZerosGrid(g2) + CountNonZerosRow(row2);
    }

    // For merge() use
    // Lemma 6: shows how to count non-zero tiles for a row
    lemma CountUpdate(s: seq<int>, i: int, v: int)
        requires 0 <= i < |s|
        ensures CountNonZerosRow(s[i := v]) == CountNonZerosRow(s) - (if s[i] != 0 then 1 else 0) + (if v != 0 then 1 else 0)
    {
        if i == 0 {
        } else {
            CountUpdate(s[1..], i - 1, v);
        }
    }

    // Lemma 7: shows how to count non-zero tiles for a grid
    lemma GridCountUpdate(g: seq<seq<int>>, i: int, newRow: seq<int>)
        requires 0 <= i < |g|
        requires forall k :: 0 <= k < |g| ==> |g[k]| == (if k == i then |g[i]| else |g[k]|) // 确保结构存在
        requires |newRow| == |g[i]|
        ensures CountNonZerosGrid(g[i := newRow]) == 
                CountNonZerosGrid(g) - CountNonZerosRow(g[i]) + CountNonZerosRow(newRow)
    {
        if i == 0 {
        } else {
            GridCountUpdate(g[1..], i - 1, newRow);
        }
    }

    /***********************************************
    (2) predicates for well-performed rows and grids
    ***********************************************/
    predicate WellPerformedRow(row: seq<int>) {
        forall k :: 0 <= k < |row| - 1 ==> (row[k] == 0 ==> row[k+1] == 0)
    }

    predicate WellPerformedGrid(grid: Grid) 
    {
        ValidGrid(grid) && forall i :: 0 <= i < N ==> WellPerformedRow(grid[i])
    }

    // Lemmas based on above:
    // Lemma 1: rows after filter and padding are well-performed
    lemma PaddingIsWellPerformed(nonZeros: seq<int>, numZeros: nat)
        requires forall x :: x in nonZeros ==> x != 0
        ensures WellPerformedRow(nonZeros + seq(numZeros, _ => 0))
    {
        var s := nonZeros + seq(numZeros, _ => 0);

        forall k | 0 <= k < |s| - 1
            ensures s[k] == 0 ==> s[k+1] == 0
        {
            if k < |nonZeros| {
                // k in non-zeros range
                assert s[k] == nonZeros[k];
                assert nonZeros[k] in nonZeros;
                assert nonZeros[k] != 0;
                assert s[k] != 0;
                if s[k] == 0 {
                    assert false;
                }
            } else {
                // k in paddings
                assert s[k] == 0;
                assert s[k+1] == 0;
            }
        }
    }

    // Lemma 2: if we apply move() on a well-performed row, nothing gonna change
    lemma WellPerformedRowFirstZeroAllZeros(row: seq<int>)
        requires WellPerformedRow(row)
        requires |row| > 0
        requires row[0] == 0
        ensures row == seq(|row|, _ => 0)
        decreases |row|
    {
        if |row| == 1 {
            assert row == [0];
            assert seq(1, _ => 0) == [0];
        } else {
            assert row[0] == 0 ==> row[1] == 0;
            assert row[1] == 0;

            assert WellPerformedRow(row[1..]) by {
                forall k | 0 <= k < |row[1..]| - 1
                    ensures row[1..][k] == 0 ==> row[1..][k+1] == 0
                {
                    assert row[1..][k] == row[k+1];
                    assert row[1..][k+1] == row[k+2];
                    assert row[k+1] == 0 ==> row[k+2] == 0;
                }
            }

            WellPerformedRowFirstZeroAllZeros(row[1..]);

            assert row == [row[0]] + row[1..];
            assert row[1..] == seq(|row| - 1, _ => 0);
            assert row == [0] + seq(|row| - 1, _ => 0);
            assert [0] + seq(|row| - 1, _ => 0) == seq(|row|, _ => 0);
        }
    }

    /*****
    Others
    ******/
    lemma LemmaFullSlice<T>(s: seq<T>)
        ensures s[..|s|] == s
    {}

    lemma SeqsDifferAt<T>(s1: seq<T>, s2: seq<T>, k: int)
        requires 0 <= k < |s1| && 0 <= k < |s2|
        requires s1[k] != s2[k]
        ensures s1 != s2
    {
        // s1 == s2 <==> |s1| == |s2| && forall i :: s1[i] == s2[i]
        // if exists a k such that s1[k] != s2[k]，then s1 != s2
    }

    lemma SliceExtend<T>(s: seq<T>, i: int)
        requires 0 <= i < |s|
        ensures s[..i+1] == s[..i] + [s[i]]
    {
    }

    /*****
    verify the generation of new tile
    *****/
    method new_tile_validation(oldGrid: Grid, changed: bool, newGrid: Grid) returns (ok: bool)
    ensures ok == (
            ValidGrid(oldGrid) &&
            ValidValues(oldGrid) &&
            ValidGrid(newGrid) &&
            ValidValues(newGrid) &&
            (
                (!changed && newGrid == oldGrid) ||
                (changed &&
                    exists i, j ::
                        0 <= i < N && 0 <= j < N &&
                        oldGrid[i][j] == 0 &&
                        newGrid[i][j] == 2 &&
                        (forall r, c ::
                            (0 <= r < N && 0 <= c < N && (r != i || c != j))
                             ==> newGrid[r][c] == oldGrid[r][c]
                        )
                )
            )
        )
    {
        ok :=
            ValidGrid(oldGrid) &&
            ValidValues(oldGrid) &&
            ValidGrid(newGrid) &&
            ValidValues(newGrid) &&
            (
                (!changed && newGrid == oldGrid) ||
                (changed &&
                    exists i, j ::
                        0 <= i < N && 0 <= j < N &&
                        oldGrid[i][j] == 0 &&
                        newGrid[i][j] == 2 &&
                        (forall r, c ::
                            (0 <= r < N && 0 <= c < N && (r != i || c != j))
                             ==> newGrid[r][c] == oldGrid[r][c]
                        )
                )
            );
    }
}