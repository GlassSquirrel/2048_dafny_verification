include "Setups.dfy"
/**********
(4) merge()
***********/
// merge() merges the neighboring 2 tiles with same value, should satisfy spec 2, 3, 4, 5, 6
// After merging 2 tiles, the number of non-zero tiles should -1
module Merge {
    import opened Setups
    // We then have a function merge_pair to do the merging given two tiles in a row
    // The merging should satisfy spec 4: only merge tiles with same value
    // the first tile value should be 2 * original value; second tile value shoud be 0
    // Other tiles should not be changed 
    function merge_pair(row: seq<int>, j: int): (res: seq<int>)
        requires 0 <= j < |row| - 1
        // spec 4: only merge tiles with the same value
        requires row[j] == row[j + 1] && row[j] != 0
        requires IsPowerOfTwo(row[j])

        ensures |res| == |row|
        ensures res[j] == row[j] * 2   // spec 4: after merging, the first tile should be exactly double the original value;
        ensures res[j+1] == 0    // spec 4: the second tile must be 0
        ensures IsPowerOfTwo(res[j])    // spec 2: valid value
        ensures forall k :: 0 <= k < |row| && k != j && k != j + 1 ==> res[k] == row[k]    // spec 4: other tiles remain unchanged
        ensures res[j] == 2048 ==> row[j] == 1024     // the generation of winning tile
        ensures res != row
        ensures CountNonZerosRow(merge_pair(row, j)) == CountNonZerosRow(row) - 1  // spec 4: after merging, count(non-zeros) - 1
    {
        var r1 := row[j := row[j] * 2];
        var r2 := r1[j+1 := 0];
        
        // proof for CountNonZerosRow(merge_pair(row, j)) == CountNonZerosRow(row) - 1
        assert CountNonZerosRow(r2) == CountNonZerosRow(row) - 1 by {
            CountUpdate(row, j, row[j] * 2); 
            CountUpdate(r1, j+1, 0);
        }
        
        r2 
    }

    // We also have a function to record hwo many merges happen to one tile
    // The function is used for the check of spec 4: every tile should only be merged once in one operation
    function update_count(counts: seq<int>, j: int): seq<int>
        requires 0 <= j < |counts| - 1
    {
        counts[j := counts[j] + 1][j + 1 := counts[j+1] + 1]
    }

    // two predicates for ensuring merge starts at the most left
    predicate MergeableAt(row: seq<int>, j: int)
    {
        0 <= j < |row| - 1 &&
        row[j] != 0 &&
        row[j] == row[j+1]
    }

    predicate NoMergeableBefore(row: seq<int>, j: int)
    {
        forall k :: 0 <= k < j ==> !MergeableAt(row, k)
    }

    // The merge method should satisfy spec 2, 3, 4, 5, 6
    method merge(grid: Grid) returns (res: Grid, done: bool)
        // Preconditions:
        // 1. spec 2 & 3: value and grid validity
        requires ValidGrid(grid)
        requires ValidValues(grid)
        // 2. game state
        requires !HasWinTile(grid)
        requires !IsLose(grid)
        // 3. only receives wellperformed grid (after move)
        requires WellPerformedGrid(grid)

        // Postconditions:
        // 1. spec 2 & 3: value and grid validity
        ensures ValidGrid(res)
        ensures ValidValues(res)
        // 2. spec 6: if done = true, then the board changes (including count)
        ensures !done ==> res == grid   
        ensures done == (res != grid)
        ensures !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
        ensures done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
        // 3. spec 4 & 5: once merged, will have empty tile and game state cannot be lose
        ensures done ==> HasEmptyTile(res)
        ensures !IsLose(res)
        // 4. spec 6: for performance, if done, can be well-performed or not well-performed; if !done, must be well-performed
        ensures !done ==> WellPerformedGrid(res)
        // 5. spec 4: ensure merge starts from the most left
        ensures forall i :: 0 <= i < N ==>
            res[i] != grid[i] ==>
                exists j :: MergeableAt(grid[i], j) &&
                        NoMergeableBefore(grid[i], j) &&
                        res[i][j] == grid[i][j] * 2 &&
                        res[i][j+1] == 0
    {
        res := grid;
        done := false;
        
        var i := 0;
        while i < N
            invariant 0 <= i <= N
            invariant ValidGrid(res)
            invariant ValidValues(res)
            invariant !done ==> res == grid
            invariant done <==> res != grid
            invariant forall k :: i <= k < N ==> res[k] == grid[k]  //current row and later rows remain unsolved
            invariant done ==> HasEmptyTile(res)
            invariant !IsLose(res)
            invariant done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
            invariant !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
            // left most merge
            invariant forall r :: 0 <= r < i ==>
                res[r] != grid[r] ==>
                    exists j :: MergeableAt(grid[r], j) &&
                            NoMergeableBefore(grid[r], j) &&
                            res[r][j] == grid[r][j] * 2 &&
                            res[r][j+1] == 0
        {
            var j := 0;   // reset j
            var merged_counts := seq(N, _ => 0);   // initialize the merge count for current row
            var first_merge_j := -1;   // initialize the leftest mergable index

            while j < N - 1
                invariant 0 <= j <= N
                invariant ValidGrid(res)
                invariant ValidValues(res)
                invariant !done ==> res == grid
                invariant !done ==> res[i] == grid[i]
                invariant done <==> res != grid
                invariant |merged_counts| == N
                // spec 4: for each tile, merge only happens once
                invariant forall k :: 0 <= k < N ==> 0 <= merged_counts[k] <= 1
                invariant forall k :: j <= k < N ==> merged_counts[k] == 0
                invariant forall k :: i < k < N ==> res[k] == grid[k]   // later rows remain unsolved
                invariant forall k :: 0 <= k < N && k != i ==> res[k] == (if k < i then res[k] else grid[k])
                invariant done ==> HasEmptyTile(res)
                invariant !IsLose(res)
                invariant done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
                invariant !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
                // spec 4: leftmost merge
                invariant -1 <= first_merge_j < N
                invariant first_merge_j == -1 ==> res[i] == grid[i]
                invariant first_merge_j == -1 ==> forall k :: 0 <= k < j ==> !MergeableAt(grid[i], k)
                invariant 0 <= first_merge_j ==> MergeableAt(grid[i], first_merge_j)
                invariant 0 <= first_merge_j ==> NoMergeableBefore(grid[i], first_merge_j)
                invariant 0 <= first_merge_j ==> res[i][first_merge_j] == grid[i][first_merge_j] * 2
                invariant 0 <= first_merge_j ==> res[i][first_merge_j+1] == 0
                invariant 0 <= first_merge_j ==> first_merge_j + 1 < j
                invariant 0 <= first_merge_j ==> merged_counts[first_merge_j] == 1 && merged_counts[first_merge_j+1] == 1
                invariant forall r :: 0 <= r < i ==>
                    res[r] != grid[r] ==>
                        exists j :: MergeableAt(grid[r], j) &&
                                    NoMergeableBefore(grid[r], j) &&
                                    res[r][j] == grid[r][j] * 2 &&
                                    res[r][j+1] == 0
            {
                if res[i][j] == res[i][j+1] && res[i][j] != 0 && merged_counts[j] == 0 && merged_counts[j+1] == 0
                {
                    if first_merge_j == -1 {
                        first_merge_j := j;
                    }

                    // record before merge
                    var count_before := CountNonZerosGrid(res);
                    var val_before_merge := res[i][j+1]; 
                    var old_res := res; 
                    if !done { assert res[i] == grid[i]; }

                    // merge the same pair
                    var updatedRow := merge_pair(res[i], j);
                    
                    // update the grid
                    res := res[i := updatedRow];

                    // show changes in grid
                    GridCountUpdate(old_res, i, updatedRow);
                    assert CountNonZerosGrid(res) == count_before - 1;
                    // proof for !IsLose
                    assert res[i][j+1] == 0;
                    ImpliesNotLose(res);
                    // update merged_counts
                    assert 0 <= j < N - 1;
                    merged_counts := update_count(merged_counts, j);
                    
                    done := true; 
                    j := j + 2;   // skip the next merged grid
                }
                else { j := j + 1; }
            }
            i := i + 1;
        }
        if !done {
            assert res == grid;
            assert WellPerformedGrid(res);
        }
    }
}