include "Setups.dfy"
/*************** 
2. Core Movement 
****************/
module Move {
    import opened Setups
    /********* 
    (3) move()
    **********/
    // First, we will have a new predicate to check if one row has the win tile 2048
    predicate HasWinTileRow(row: seq<int>)
        requires |row| == N
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
    {
        exists j :: 0 <= j < |row| && row[j] == 2048
    }

    // Second, define a function CompressRow
    // To develop CompressRwo, we need to have another function FilterNonZeros to extract all non-zero elements
    function FilterNonZeros(s: seq<int>): seq<int>
        ensures |FilterNonZeros(s)| <= |s|
        ensures forall x :: x in FilterNonZeros(s) ==> x in s   // all the elements come from the original row
        ensures forall x :: x in FilterNonZeros(s) ==> x != 0   // after filtering, there's no 0 in the row
    {
        if |s| == 0 then []
        else if s[0] != 0 then [s[0]] + FilterNonZeros(s[1..])
        else FilterNonZeros(s[1..])
    }

    /*
    Lemmas we develop from FilterNonZeros
    */
    // Lemma 1: FilterZerosIsEmpty, which shows that if we apply FilterNonZeros on sequence of 0s, the return sequence will be empty
    // this will later be used to show that the relative orders of non-zero elements remain the same after the row being compressed
    lemma FilterZerosIsEmpty(k: nat)
        ensures FilterNonZeros(seq(k, _ => 0)) == []
        // decreases k
    {
        // basic case
        if k == 0 {
            // seq(0, _) == []
        } else {
            assert seq(k, _ => 0) == [0] + seq(k-1, _ => 0);

            FilterZerosIsEmpty(k-1);

            assert FilterNonZeros(seq(k, _ => 0)) == FilterNonZeros(seq(k-1, _ => 0));
        }
    }

    // Lemma 2: FilterAppendZeros, which shows that if we apply FilterNonZeros on sequence of (non-zero elements + paddings of 0s), the return sequence will be the non-zero-element sequence
    // this will also be used to show that the relative orders of non-zero elements remain the same after the row being compressed
    lemma FilterAppendZeros(s: seq<int>, k: nat)
        requires forall x :: x in s ==> x != 0
        ensures FilterNonZeros(s + seq(k, _ => 0)) == s
        // decreases |s|
    {
        // basic case
        if |s| == 0 {
            assert s + seq(k, _ => 0) == seq(k, _ => 0);
            FilterZerosIsEmpty(k);
        } else {

            assert s[0] in s;
            assert s[0] != 0;

            assert forall x :: x in s[1..] ==> x in s;
            assert forall x :: x in s[1..] ==> x != 0;

            FilterAppendZeros(s[1..], k);

            assert s == [s[0]] + s[1..];
            assert s + seq(k, _ => 0) == [s[0]] + (s[1..] + seq(k, _ => 0));
            // as long s s[0] != 0, FilterNonZeros will keep it and continue on the rest part
            assert FilterNonZeros(s + seq(k, _ => 0)) == [s[0]] + FilterNonZeros(s[1..] + seq(k, _ => 0));
            assert FilterNonZeros(s[1..] + seq(k, _ => 0)) == s[1..];
            assert FilterNonZeros(s + seq(k, _ => 0)) == [s[0]] + s[1..];
            assert [s[0]] + s[1..] == s;   // FilterNonZeros(s + Padding) == s
        }
    }

    // Lemma 3: FilterNonZerosPreservesElements, which shows that FilterNonZeros preserve all the non-zero elements, without creating new ones that do not belong to the original sequence 
    lemma FilterNonZerosPreservesElements(s: seq<int>, x: int)
        requires x != 0
        ensures x in s <==> x in FilterNonZeros(s)
    {
        if |s| == 0 {
            return;
        } else if s[0] == x {
        } else {
            FilterNonZerosPreservesElements(s[1..], x);
        }
    }

    // Lemma 4: FilterLenLemma which is about the length of the output of the FilterNonZeros
    lemma FilterLenLemma(s: seq<int>)
        ensures (exists x :: x in s && x == 0) ==> |FilterNonZeros(s)| < |s|
        ensures (forall x :: x in s ==> x != 0) ==> FilterNonZeros(s) == s
    {
        if |s| == 0 {
        } else {
            FilterLenLemma(s[1..]);
            // case 1: non-zero-element sequence
            if forall x :: x in s ==> x != 0 {
                FilterAppendZeros(s, 0);
                assert FilterNonZeros(s) == s;
            }
            // case 2: sequence with 0
            if exists x :: x in s && x == 0 {
                if s[0] == 0 {
                    assert |FilterNonZeros(s)| == |FilterNonZeros(s[1..])|;
                    assert |FilterNonZeros(s[1..])| <= |s[1..]|;
                    assert |s[1..]| < |s|;
                } else {
                    assert s == [s[0]] + s[1..]; 
                    
                    // contradiction: if s[1..] does not contain 0, and s[0] is not 0, then there's no 0 in s
                    if !(exists x :: x in s[1..] && x == 0) {
                        assert forall x :: x in s[1..] ==> x != 0;
                        assert forall x :: x in s ==> x != 0;
                        assert false; 
                    }
                    
                    assert exists x :: x in s[1..] && x == 0;

                    assert |FilterNonZeros(s[1..])| < |s[1..]|;
                    assert |FilterNonZeros(s)| == 1 + |FilterNonZeros(s[1..])|;
                    assert |s| == 1 + |s[1..]|;    // |FilterNonZeros(s)| < |s|
                }
            }
        }
    }

    // Lemma 5: FilterNonZerosReturnNoZeros, shows that if FilterNonZeros() return sequence with no 0s
    lemma FilterNonZerosReturnNoZeros(row: seq<int>)
        ensures forall x :: x in FilterNonZeros(row) ==> x != 0
    {
        if |row| > 0 {
            FilterNonZerosReturnNoZeros(row[1..]);
        }
    }

        // Lemma 6：FilterNonZeros does not change Count(non-zeros)
        lemma FilterPreservesCount(s: seq<int>)
            ensures CountNonZerosRow(s) == CountNonZerosRow(FilterNonZeros(s))
        {
            if |s| == 0 {
            } else if s[0] == 0 {
                FilterPreservesCount(s[1..]);
            } else {
                FilterPreservesCount(s[1..]);
            }
        }

    // CompressRow: input is a row, it gets all non-zero elements to the left, then pad 0s if there's room
    // output a bool indicating whether the row has changed or not
    function CompressRow(row: seq<int>): (seq<int>, bool)
        requires |row| == N   // the length of the row is valid
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])   // all the values in the row is valid
    {
        // step 1: filter out all non-zero elements
        var nonZeros := FilterNonZeros(row);
        // step 2: pad zeros
        var zeroFill := seq(N - |nonZeros|, _ => 0);
        var padded := nonZeros + zeroFill;

        (padded, padded != row)
    }

    // property of CompressRow
    lemma CompressRowSpec(row: seq<int>)
        requires |row| == N
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])   // all the values in the row is valid

        // 1. validation of output
        ensures |CompressRow(row).0| == N   // spec 5: the length of the output row is still valid
        ensures forall x :: x in CompressRow(row).0 ==> x == 0 || IsPowerOfTwo(x)   // spec 2: the values are valid
        ensures forall x :: x in CompressRow(row).0 ==> x == 0 || x in row   // all the elements should come from the original row, no new elements generated
        // 2. ensure the number of non-zero elements remains the same
        ensures CountNonZerosRow(CompressRow(row).0) == CountNonZerosRow(row)
        // 3. performance of the rows
        ensures WellPerformedRow(CompressRow(row).0)
        ensures WellPerformedRow(row) ==> !CompressRow(row).1
        ensures CompressRow(row).1 == (CompressRow(row).0 != row)
    {
        var nonZeros := FilterNonZeros(row);
        var zeroFill := seq(N - |nonZeros|, _ => 0);
        var padded := nonZeros + zeroFill;

        // 1. proof for count preservation
        // Count(row) == Count(nonZeros)
        FilterPreservesCount(row);
        // nonZeros has no 0
        assert forall x :: x in nonZeros ==> x != 0;
        // Count(nonZeros) == |nonZeros|
        NonZerosCountIsLength(nonZeros);
        // Count(row) == |nonZeros|
        assert CountNonZerosRow(row) == |nonZeros|;
        // Count(padded) = Count(nonZeros) + Count(zeroFill)
        CountRowAdditivity(nonZeros, zeroFill);
        // zeroFill has 0 non-zero element
        ZerosCountIsZero(N - |nonZeros|);
        assert CountNonZerosRow(padded) == CountNonZerosRow(nonZeros) + CountNonZerosRow(zeroFill);

        assert CountNonZerosRow(padded) == |nonZeros| + 0;

        assert CountNonZerosRow(padded) == CountNonZerosRow(row);

        // 2. Well-performed proof
        PaddingIsWellPerformed(nonZeros, N - |nonZeros|);
        assert WellPerformedRow(padded);

        // 3. No-change proof
        if WellPerformedRow(row) {
            WellPerformedRowDoNotMove(row);
            assert padded == row;
        }
    }

    // lemmas developed based on CompressRow
    // Lemma 1: compressrow perserves the number of non-zero elements 
    lemma CompressRowPreservesCount(row: seq<int>)
        requires |row| == N
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
        ensures CountNonZerosRow(CompressRow(row).0) == CountNonZerosRow(row)
    {
        var nonZeros := FilterNonZeros(row);
        var zeroFill := seq(N - |nonZeros|, _ => 0);
        var padded := nonZeros + zeroFill;

        // 1. prove that Count(FilterNonZeros) = |FilterNonZeros|
        assert forall x :: x in nonZeros ==> x != 0 by {
        }
        NonZerosCountIsLength(nonZeros);
        assert CountNonZerosRow(nonZeros) == |nonZeros|;

        // 2. Count(padded) = |nonZeros|
        CountRowAdditivity(nonZeros, zeroFill);
        ZerosCountIsZero(N - |nonZeros|);
        assert CountNonZerosRow(padded) == CountNonZerosRow(nonZeros) + 0;
        assert CountNonZerosRow(padded) == |nonZeros|;

        // 3. Count(original row) = |nonZeros|
        FilterPreservesCount(row);
        assert CountNonZerosRow(row) == |nonZeros|;
    }

    // Lemma 2: CompressRowLastElementIs0, shows that if we successfully compress a row, then the last element of it should be 0
    lemma CompressRowLastElementIs0(row: seq<int>)
        requires |row| == N
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
        ensures var res := CompressRow(row);
                res.1 ==> res.0[N-1] == 0
    {
        var res := CompressRow(row);
        if res.1 { 
            FilterLenLemma(row);
            var nonZeros := FilterNonZeros(row);
            var zeroFill := seq(N - |nonZeros|, _ => 0);
            
            assert res.0 == nonZeros + zeroFill; 
            assert |nonZeros| < N;
            assert res.0[N-1] == zeroFill[N - 1 - |nonZeros|];
        }
    }

    // Lemma 3: CompressPreservesNonZeros, shows that all the elements should come from the original row, no new elements generated
    lemma CompressPreservesNonZeros(row: seq<int>)
        requires |row| == N
        requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
        ensures FilterNonZeros(CompressRow(row).0) == FilterNonZeros(row)   // the relative order of non-zero elements are not changed
        // ensures CountNonZerosRow(CompressRow(row).0) == CountNonZerosRow(row)
    {
        var nonZeros := FilterNonZeros(row);

        assert forall x :: x in nonZeros ==> x != 0;

        FilterAppendZeros(nonZeros, N - |nonZeros|);
    }

    // Lemma 4: CompressRowPreservesWin
    lemma CompressRowPreservesWin(row: seq<int>)
        requires |row| == N 
        requires forall x :: x in row ==> x == 0 || IsPowerOfTwo(x)
        ensures HasWinTileRow(row) <==> HasWinTileRow(CompressRow(row).0)
    {
        var res := CompressRow(row);
        var nonZeros := FilterNonZeros(row);
        
        // step 1: HasWinTileRow(row) ==> HasWinTileRow(res.0)
        if HasWinTileRow(row) {
            // since 2048 != 0, it should be also in non-zero-element sequence
            FilterNonZerosPreservesElements(row, 2048);
            assert 2048 in row;
            assert 2048 in nonZeros;
            assert 2048 in res.0;
            assert HasWinTileRow(res.0);
        }
        
        // step 2: HasWinTileRow(res.0) ==> HasWinTileRow(row)
        if HasWinTileRow(res.0) {
            FilterNonZerosPreservesElements(row, 2048);
            assert 2048 in res.0 ==> 2048 in nonZeros;
            assert 2048 in nonZeros ==> 2048 in row;
            assert HasWinTileRow(row);
        }
    }

    // Some lemma we developed for well-performed row
    lemma WellPerformedRowDoNotMove(row: seq<int>)
        requires WellPerformedRow(row)
        ensures FilterNonZeros(row) +
                seq(|row| - |FilterNonZeros(row)|, _ => 0) == row
        // decreases |row|
    {
        if |row| == 0 {
        } else if row[0] == 0 {
            // row is all 0s
            WellPerformedRowFirstZeroAllZeros(row);
            assert row == seq(|row|, _ => 0);

            // FilterNonZeros(seq(k,0)) == []
            FilterZerosIsEmpty(|row|);
            assert FilterNonZeros(row) == [];

            // [] + seq(|row|,0) == seq(|row|,0) == row
            assert FilterNonZeros(row) + seq(|row| - |FilterNonZeros(row)|, _ => 0)
                == [] + seq(|row| - 0, _ => 0);
            assert [] + seq(|row|, _ => 0) == seq(|row|, _ => 0);
        } else {
            // row[0] != 0
            assert WellPerformedRow(row[1..]) by {
                forall k | 0 <= k < |row[1..]| - 1
                    ensures row[1..][k] == 0 ==> row[1..][k+1] == 0
                {
                    assert row[1..][k] == row[k+1];
                    assert row[1..][k+1] == row[k+2];
                    assert row[k+1] == 0 ==> row[k+2] == 0;
                }
            }

            WellPerformedRowDoNotMove(row[1..]);

            assert FilterNonZeros(row) == [row[0]] + FilterNonZeros(row[1..]);

            // the length of padding：|row| - |FilterNonZeros(row)| = |row[1..]| - |FilterNonZeros(row[1..])|
            assert |row| == 1 + |row[1..]|;
            assert |FilterNonZeros(row)| == 1 + |FilterNonZeros(row[1..])|;

            assert FilterNonZeros(row) + seq(|row| - |FilterNonZeros(row)|, _ => 0)
                == ([row[0]] + FilterNonZeros(row[1..])) +
                seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0);

            // FilterNonZeros(row[1..]) + padding
            assert FilterNonZeros(row[1..]) +
                seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0)
                == row[1..];

            // connect
            assert ([row[0]] + FilterNonZeros(row[1..])) +
                seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0)
                == [row[0]] + (FilterNonZeros(row[1..]) +
                seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0));

            assert [row[0]] + row[1..] == row;
        }
    }

    // Third, we define the move method itself 
    // note: the move() method should accept Win state, since merging could create 2048
    method move(mat: Grid) returns (new_mat: Grid, done: bool)
        // Preconditions:
        requires ValidGrid(mat)
        requires ValidValues(mat)
        // requires !HasWinTile(mat)
        requires !IsLose(mat)    // spec 3 precondition: not lose state

        // Postconditions:
        // 1. spec 2 & 5
        ensures ValidGrid(new_mat)
        ensures ValidValues(new_mat)    
        // 2. spec 3: does not change the state of the game
        ensures HasWinTile(mat) ==> HasWinTile(new_mat)
        ensures !HasWinTile(mat) ==> !HasWinTile(new_mat)
        // ensures !HasWinTile(new_mat)
        ensures !IsLose(new_mat)
        // 3. if done=True, then the mat changes
        ensures done == (new_mat != mat)
        // 4. every row preserve the same element and non-zero element remain in same order
        ensures forall i :: 0 <= i < N ==> FilterNonZeros(new_mat[i]) == FilterNonZeros(mat[i])
        ensures CountNonZerosGrid(new_mat) == CountNonZerosGrid(mat)
        // 5. performance of the row
        // ensures WellPerformedGrid(new_mat)
        ensures WellPerformedGrid(new_mat)
        ensures WellPerformedGrid(mat) ==> !done
    {
        var temp_grid: seq<seq<int>> := [];
        done := false;

        for i := 0 to N 
            // basic controls: postcondition part 1
            invariant 0 <= i <= N 
            invariant |temp_grid| == i
            invariant forall k :: 0 <= k < i ==> |temp_grid[k]| == N   // spec 5: make sure the iterated rows lengths are valid
            // invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < N ==> temp_grid[k][j] == 0 || IsPowerOfTwo(temp_grid[k][j])  // spec 2: values are valid
            invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < N ==> temp_grid[k][j] == 0 || IsPowerOfTwo(temp_grid[k][j])
            // safety: 
            invariant forall k :: 0 <= k < i ==> temp_grid[k] == CompressRow(mat[k]).0   // the iterated rows are the outcome of the corresponding original row
            // make sure state not changed: postcondition part 2
            invariant forall k :: 0 <= k < i ==> (temp_grid[k] != mat[k] ==> done)   // if row moved, then done = True 
            // invariant (exists k :: 0 <= k < i && HasWinTileRow(temp_grid[k])) <==> (exists k :: 0 <= k < i && HasWinTileRow(mat[k]))   // spec 3: make sure the win state is preserved
            invariant !done ==> temp_grid == mat[..i]   // if no previous rows moved, stay the same
            // invariant done ==> exists k, l :: 0 <= k < i && 0 <= l < N && temp_grid[k][l] == 0    // if previous rows moved, has tile = 0
            invariant done ==> exists k :: 0 <= k < i && CompressRow(mat[k]).1
            // postcondition part 3:
            invariant done ==> temp_grid != mat[..i]    // if previous rows moved, not the same
            // postcondition part 4:
            invariant forall k :: 0 <= k < i ==> FilterNonZeros(temp_grid[k]) == FilterNonZeros(mat[k])   // preseve the relative order of non-zero elements
            invariant CountNonZerosGrid(temp_grid) == CountNonZerosGrid(mat[..i])
            // postcondition part 5:
            invariant forall k :: 0 <= k < i ==> WellPerformedRow(temp_grid[k])
            invariant WellPerformedGrid(mat) ==> (temp_grid == mat[..i] && !done)
        {
            // 1. compress the row
            var res := CompressRow(mat[i]);
            var row_res := res.0;
            var row_changed := res.1;
            CompressPreservesNonZeros(mat[i]);
            CompressRowPreservesWin(mat[i]);
            CompressRowLastElementIs0(mat[i]);
            CompressRowSpec(mat[i]);

            assert forall j :: 0 <= j < N ==> row_res[j] == 0 || IsPowerOfTwo(row_res[j]);
            SeqElementsValidImpliesIndexValid(row_res);
            assert forall x :: x in row_res ==> x in mat[i] || x == 0;

            // 2. update done
            if row_changed {
                done := true;
                assert row_res[N-1] == 0;
                assert CompressRow(mat[i]).1;
            }

            // 3. update grid
            assert CountNonZerosGrid(temp_grid) == CountNonZerosGrid(mat[..i]);

            var old_temp := temp_grid;
            assert CountNonZerosGrid(old_temp) == CountNonZerosGrid(mat[..i]);

            assert CountNonZerosRow(row_res) == CountNonZerosRow(mat[i]);

            temp_grid := temp_grid + [row_res];

            GridEqualityAfterAppend(old_temp, mat[..i], row_res, mat[i]);
            SliceExtend(mat, i);
            assert mat[..i+1] == mat[..i] + [mat[i]];

            assert CountNonZerosGrid(temp_grid) == CountNonZerosGrid(mat[..i+1]);
            // proof for !IsLose
            if done {
                if row_changed {
                    assert temp_grid[i] == row_res;
                    assert temp_grid[i] != mat[i];
                    assert temp_grid[i] != mat[..i+1][i];
                    SeqsDifferAt(temp_grid, mat[..i+1], i);
                    assert temp_grid != mat[..i+1];
                } else {
                    var k :| 0 <= k < i && temp_grid[k] != mat[k];
                    assert temp_grid[k] != mat[..i+1][k];
                    assert temp_grid != mat[..i+1];
                }
            }
            assert temp_grid[i] == res.0;  // safety invariant temp_grid[k] == CompressRow(mat[k]).0
        }

        new_mat := temp_grid;
        LemmaFullSlice(mat);
        assert mat[..N] == mat;
        assert CountNonZerosGrid(mat[..N]) == CountNonZerosGrid(mat);

        assert CountNonZerosGrid(new_mat) == CountNonZerosGrid(mat);

        if !done {
            // no changes
            assert new_mat == mat;
        } else {
        // done == true
        var k :| 0 <= k < N && CompressRow(mat[k]).1;

        // if CompressRow(mat[k]).1 is true, the last tile is 0
        CompressRowLastElementIs0(mat[k]);

        // proof for safety：new_mat[k] is CompressRow(mat[k]).0
        assert new_mat[k] == CompressRow(mat[k]).0;
        assert new_mat[k][N-1] == 0;

        assert exists r, c :: 0 <= r < N && 0 <= c < N && new_mat[r][c] == 0 by {
            assert 0 <= k < N;
            assert 0 <= N-1 < N;
            // witness
        }

            ImpliesNotLose(new_mat);
        }

        // proof for preserve the state
        if HasWinTile(mat) {
            var r, c :| 0 <= r < N && 0 <= c < N && mat[r][c] == 2048;

            CompressRowPreservesWin(mat[r]);
            assert new_mat[r] == CompressRow(mat[r]).0;
            assert HasWinTileRow(mat[r]);
            assert HasWinTileRow(new_mat[r]);
            assert HasWinTile(new_mat);
        }
        
        if !HasWinTile(mat) {
            if HasWinTile(new_mat) {
                var r, c :| 0 <= r < N && 0 <= c < N && new_mat[r][c] == 2048;

                // safety
                assert new_mat[r] == CompressRow(mat[r]).0;

                // preserves：HasWinTileRow(mat[r]) <==> HasWinTileRow(new_mat[r])
                CompressRowPreservesWin(mat[r]);

                assert HasWinTileRow(new_mat[r]);
                assert HasWinTileRow(mat[r]);
                assert HasWinTile(mat);
                assert false;
            }
        }
            assert !IsLose(mat) ==> !IsLose(new_mat);

            return new_mat, done;
    }
}