type Grid = seq<seq<int>>
const N: int := 4

/****************************************
 Basic Specs & Predicates for Game State 
*****************************************/
// Spec 5: board boundry
predicate ValidGrid(grid: Grid) 
{
    |grid| == N && forall i :: 0 <= i < N ==> |grid[i]| == N
}

// predicate IsPowerOfTwo(x: int)
// {
//     x == 2 || x == 4 || x == 8 || x == 16 || x == 32 ||
//     x == 64 || x == 128 || x == 256 || x == 512 || x == 2048
// }
// Better implementation of IsPowerOfTwo for 2048 (exclude 1)
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

// Define 3 predicates to check for "has win" / "has lose" / "can continue"
// Predicate 1: has win (tile value reaches 2048)
predicate HasWinTile(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 2048
}

// {Predicate 2: has empty tile value = 0 (can generate new 2)
predicate HasEmptyTile(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 0
}

// Predicate 3: has more room to merge
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
lemma {:axiom} ImpliesNotLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasEmptyTile(grid) ==> !IsLose(grid)
{}

/*********************************** 
1. initialization & state management
***********************************/
/**************
(1) new_game()
***************/
// First initialize a new board with all tiles being 0
method new_game() returns (grid: Grid)
    // spec 5: board boundary
    ensures ValidGrid(grid)
    // ensure tile values are all 0
    ensures forall i, j :: 0 <= i < N && 0 <= j < N ==> grid[i][j] == 0
{
    var row := seq(N, _ => 0);
    grid := seq(N, _ => row);
}


// The above board will be passed to game.py to generate random 2s
// Then we validate the random generation
// Two functions to count the frequency of value in a grid
function CountInRow(row: seq<int>, value: int): int 
{
    if |row| == 0 then 0
    else (if row[0] == value then 1 else 0) + CountInRow(row[1..], value)
}

function CountInGrid(grid: Grid, value: int): int
{
    if |grid| == 0 then 0
    else CountInRow(grid[0], value) + CountInGrid(grid[1..], value)
}

// Check whether the random initialization of grid is valid or not 
// A valid initialization should have a grid composed of 0s and two 2s.
predicate IsValidInitialBoard(grid: Grid)
{
    |grid| == N &&
    (forall i :: 0 <= i < N ==> |grid[i]| == N) &&
    (forall i, j :: 0 <= i < N && 0 <= j < N ==> grid[i][j] == 0 || grid[i][j] == 2) &&
    CountInGrid(grid, 2) == 2   // two 2 generated
}

method initial_grid_validation(grid: Grid) returns (b: bool)
    ensures b == IsValidInitialBoard(grid)
{
    return IsValidInitialBoard(grid);
}

/***************
(2) game_state()
****************/
// 3 game states: win, lose, can continue
datatype State = Win | NotOver | Lose

method game_state(grid: Grid) returns (s: State)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    // spec 3: game state evaluation
    ensures HasWinTile(grid) ==> s == Win
    ensures !(HasWinTile(grid)) && (HasEmptyTile(grid) || MoreToMerge(grid)) ==> s == NotOver
    ensures !HasWinTile(grid) && !HasEmptyTile(grid) && !MoreToMerge(grid) ==> s == Lose
{
    // 1. check for Win
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall k, l :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != 2048
    {
        var j := 0;
        while j < N
            invariant 0 <= j <= N
            invariant forall l :: 0 <= l < j ==> grid[i][l] != 2048
        {
            if grid[i][j] == 2048 
            { 
                return Win; 
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // 2. check for empty tile
    i := 0;
    while i < N 
        invariant 0 <= i <= N
        invariant !HasWinTile(grid)    // record previous state
        invariant forall k, l :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != 0
    {
        var j := 0;
        while j < N
            invariant 0 <= j <= N
            invariant forall l :: 0 <= l < j ==> grid[i][l] != 0
        {
            if grid[i][j] == 0 
            { 
                return NotOver; 
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // 3. check for mergable neighbors
    // 3.1 check rows
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant !HasWinTile(grid)
        invariant !HasEmptyTile(grid)
        invariant forall k, l :: 0 <= k < i && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]
    {
        var j := 0;
        while j < N - 1
            invariant 0 <= j <= N - 1
            invariant forall k, l :: 0 <= k < i && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]  // previous rows
            invariant forall l :: 0 <= l < j ==> grid[i][l] != grid[i][l+1]  // current row
        {
            if grid[i][j] == grid[i][j+1] 
            { 
                return NotOver; 
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // 3.2 check columns
    i := 0;
    while i < N - 1
        invariant 0 <= i <= N - 1
        invariant !HasWinTile(grid)
        invariant !HasEmptyTile(grid)
        invariant forall k, l :: 0 <= k < N && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]   // checked for rows
        invariant forall k, l {:trigger grid[k][l]} :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]
    {
        var j := 0;
        while j < N
            invariant 0 <= j <= N
            invariant forall k, l :: 0 <= k < N && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]
            invariant forall k, l {:trigger grid[k][l]} :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]   // previous columns
            invariant forall l :: 0 <= l < j ==> grid[i][l] != grid[i+1][l]   // current columns
        {
            if grid[i][j] == grid[i+1][j] 
            { 
                return NotOver; 
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // 4. Lose
    return Lose;
}

/*************** 
2. Core Movement 
****************/
/********* 
(3) move()
**********/
// move() need to satisfy spec 2, 3, 5
// Especially for spec 3: move() does not change the state of game
// which means, Win => Win, NotOver => NotOver, that means no Lose => no Lose

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

// We also develop several lemmas about FilterNonZeros function
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

        assert FilterNonZeros(seq(k, _ => 0))
            == FilterNonZeros(seq(k-1, _ => 0));
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

// To achieve that, we first define two functions:
function CountNonZerosRow(s: seq<int>): nat    // count the number of non-zero elements in a row
{
    if |s| == 0 then 0
    else (if s[0] != 0 then 1 else 0) + CountNonZerosRow(s[1..])
}

function CountNonZerosGrid(g: seq<seq<int>>): nat    // count the number of non-zero elements in a row 
{
    if |g| == 0 then 0
    else CountNonZerosRow(g[0]) + CountNonZerosGrid(g[1..])
}

// 1. 证明计数函数具有可加性：Count(a + b) == Count(a) + Count(b)
lemma LemmaCountAdditivity(a: seq<int>, b: seq<int>)
    ensures CountNonZerosRow(a + b) == CountNonZerosRow(a) + CountNonZerosRow(b)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        LemmaCountAdditivity(a[1..], b);
    }
}

// 2. 证明全为0的序列计数为0
lemma LemmaCountZerosIsZero(k: nat)
    ensures CountNonZerosRow(seq(k, _ => 0)) == 0
{
    if k > 0 {
        LemmaCountZerosIsZero(k - 1);
    }
}

// 3. 证明FilterNonZeros的结果计数等于其长度（因为它没有0）
lemma LemmaNonZerosCountIsLength(s: seq<int>)
    requires forall x :: x in s ==> x != 0
    ensures CountNonZerosRow(s) == |s|
{
    if |s| == 0 {
    } else {
        LemmaNonZerosCountIsLength(s[1..]);
    }
}

// CompressRow: input is a row, it gets all non-zero elements to the left, then pad 0s if there's room
// output a bool indicating whether the row has changed or not
function CompressRow(row: seq<int>): (seq<int>, bool)
    requires |row| == N   // the length of the row is valid
    requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])   // all the values in the row is valid

    ensures |CompressRow(row).0| == N   // 1. spec 5: the length of the output row is still valid
    ensures forall x :: x in CompressRow(row).0 ==> x == 0 || IsPowerOfTwo(x)   // 2. spec 2: the values are valid
    ensures forall x :: x in CompressRow(row).0 ==> x == 0 || x in row   // 3. all the elements should come from the original row, no new elements generated
    // ensures CompressRow(row).1 ==> CompressRow(row).0[N-1] == 0   // if the row is changed, there must be at least one 0 at the end of row
    ensures CountNonZerosRow(CompressRow(row).0) == CountNonZerosRow(row)
{
    // step 1: filter out all non-zero elements
    var nonZeros := FilterNonZeros(row);
    var zeroFill := seq(N - |nonZeros|, _ => 0);
    var padded := nonZeros + zeroFill;
    
    // 证明 1: FilterNonZeros(row) 的非零计数等于 row 的非零计数
    assert CountNonZerosRow(nonZeros) == |nonZeros|;

    // step 2: padding 0s, make sure the length of row is N
    var padded := nonZeros + seq(N - |nonZeros|, _ => 0);
    assert CountNonZerosRow(padded) == CountNonZerosRow(nonZeros) + CountNonZerosRow(seq(N - |nonZeros|, _ => 0));
    assert CountNonZerosRow(seq(N - |nonZeros|, _ => 0)) == 0;
    (padded, padded != row)
} 

// We also develop serveral lemmas based on CompressRow
// Lemma 1: CompressRowLastElementIs0, shows that if we successfully compress a row, then the last element of it should be 0
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

// Lemma 2: CompressPreservesNonZeros, shows that all the elements should come from the original row, no new elements generated
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

// Lemma 3: CompressRowPreservesWin
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
    // ensures CountNonZerosGrid(new_mat) == CountNonZerosGrid(mat)
{
    var temp_grid: seq<seq<int>> := [];
    done := false;

    for i := 0 to N 
        // basic controls: postcondition part 1
        invariant 0 <= i <= N 
        invariant |temp_grid| == i
        invariant forall k :: 0 <= k < i ==> |temp_grid[k]| == N   // spec 5: make sure the iterated rows lengths are valid
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < N ==> temp_grid[k][j] == 0 || IsPowerOfTwo(temp_grid[k][j])  // spec 2: values are valid
        // safety: 
        invariant forall k :: 0 <= k < i ==> temp_grid[k] == CompressRow(mat[k]).0   // the iterated rows are the outcome of the corresponding original row
        // make sure state not changed: postcondition part 2
        invariant forall k :: 0 <= k < i ==> (temp_grid[k] != mat[k] ==> done)   // if row moved, then done = True 
        invariant (exists k :: 0 <= k < i && HasWinTileRow(temp_grid[k])) <==> (exists k :: 0 <= k < i && HasWinTileRow(mat[k]))   // spec 3: make sure the win state is preserved
        invariant !done ==> temp_grid == mat[..i]   // if no previous rows moved, stay the same
        invariant done ==> exists k, l :: 0 <= k < i && 0 <= l < N && temp_grid[k][l] == 0    // if previous rows moved, has tile = 0
        // postcondition part 3:
        invariant done ==> temp_grid != mat[..i]    // if previous rows moved, not the same
        // postcondition part 4:
        invariant forall k :: 0 <= k < i ==> FilterNonZeros(temp_grid[k]) == FilterNonZeros(mat[k])   // preseve the relative order of non-zero elements
        // invariant CountNonZerosGrid(temp_grid) == CountNonZerosGrid(mat[..i])
    {
        // 1. compress the row
        var res := CompressRow(mat[i]);
        var row_res := res.0;
        var row_changed := res.1;
        CompressPreservesNonZeros(mat[i]);
        CompressRowPreservesWin(mat[i]);
        CompressRowLastElementIs0(mat[i]);
        
        assert forall x :: x in row_res ==> x in mat[i] || x == 0;

        // 2. update done
        if row_changed {
            done := true;
            assert row_res[N-1] == 0;
        }

        // 3. update grid
        var old_temp := temp_grid[..i];   // old_temp: before adding the new row
        temp_grid := temp_grid + [row_res];

        // proof for !IsLose
        if done {
            if row_changed {
                assert temp_grid[i] == row_res;
                assert temp_grid[i] != mat[i];
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

    if !done {
        // no changes
        assert new_mat == mat;
    } else {
        // change => some row has 0 at the end
        assert exists r, c :: 0 <= r < N && 0 <= c < N && new_mat[r][c] == 0;
        ImpliesNotLose(new_mat);
    }

    // proof for preserve the state
    assert !HasWinTile(mat) ==> !HasWinTile(new_mat);
    assert !IsLose(mat) ==> !IsLose(new_mat);

    return new_mat, done;
}

/**********
(4) merge()
***********/
// merge() merges the neighboring 2 tiles with same value, should satisfy spec 1, 2, 5

// After merging 2 tiles, the number of non-zero tiles should -1


// We have the following lemma for the two CountNonZeros functions
// Lemma 1: shows how to count non-zero tiles for a row
lemma CountUpdate(s: seq<int>, i: int, v: int)
    requires 0 <= i < |s|
    ensures CountNonZerosRow(s[i := v]) == CountNonZerosRow(s) - (if s[i] != 0 then 1 else 0) + (if v != 0 then 1 else 0)
{
    if i == 0 {
    } else {
        CountUpdate(s[1..], i - 1, v);
    }
}

// Lemma 2: shows how to count non-zero tiles for a grid
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

// We then have a function merge_pair to do the merging given two tiles in a row
// The merging should satisfy spec 1: only merge tiles with same value
// the first tile value should be 2 * original value; second tile value shoud be 0
// Other tiles should not be changed 
function merge_pair(row: seq<int>, j: int): (res: seq<int>)
    requires 0 <= j < |row| - 1
    // spec 1: only merge tiles with the same value
    requires row[j] == row[j + 1] && row[j] != 0
    requires IsPowerOfTwo(row[j])

    ensures |res| == |row|
    ensures res[j] == row[j] * 2   // spec 1: after merging, the first tile should be exactly double the original value;
    ensures res[j+1] == 0    // spec 1: the second tile must be 0
    ensures IsPowerOfTwo(res[j])    // spec 2: valid value
    ensures forall k :: 0 <= k < |row| && k != j && k != j + 1 ==> res[k] == row[k]    // does not change other tiles
    ensures res[j] == 2048 ==> row[j] == 1024     // the generation of winning tile
    ensures res != row
    ensures CountNonZerosRow(merge_pair(row, j)) == CountNonZerosRow(row) - 1
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
// The function is used for the check of spec 1: every tile should only be merged once in one operation
function update_count(counts: seq<int>, j: int): seq<int>
    requires 0 <= j < |counts| - 1
{
    counts[j := counts[j] + 1][j + 1 := counts[j+1] + 1]
}

// The merge method should satisfy spec 1, 2, 5
method merge(grid: Grid) returns (res: Grid, done: bool)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    // precondition for game state
    requires !HasWinTile(grid)
    requires !IsLose(grid)

    ensures ValidGrid(res)     // spec 5
    ensures ValidValues(res)     // spec 2
    ensures !done ==> res == grid   
    ensures done == (res != grid)
    ensures !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
    ensures done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
    // spec 1: once merged, will have empty tile and game state cannot be lose
    ensures done ==> HasEmptyTile(res)
    ensures !IsLose(res)
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
    {
        var j := 0;   // reset j
        var merged_counts := seq(N, _ => 0);   // initialize the merge count for current row

        while j < N - 1
            invariant 0 <= j <= N
            invariant ValidGrid(res)
            invariant ValidValues(res)
            invariant !done ==> res == grid
            invariant !done ==> res[i] == grid[i]
            invariant done <==> res != grid
            invariant |merged_counts| == N
            invariant forall k :: 0 <= k < N ==> 0 <= merged_counts[k] <= 1
            invariant forall k :: j <= k < N ==> merged_counts[k] == 0
            invariant forall k :: i < k < N ==> res[k] == grid[k]   // later rows remain unsolved
            invariant forall k :: 0 <= k < N && k != i ==> res[k] == (if k < i then res[k] else grid[k])
            invariant done ==> HasEmptyTile(res)
            invariant !IsLose(res)
            invariant done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
            invariant !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
        {
            if res[i][j] == res[i][j+1] && res[i][j] != 0 
            {
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

                done := true; 
                j := j + 2;   // skip the next merged grid
            }
            else { j := j + 1; }
        }
        i := i + 1;
    }
}

// should have a predicate check for spec 6: if !done, then no new generation of 2

/*
3. matrix transformation
*/

// (5) reverse()
method reverse(mat: Grid) returns (res: Grid)
    requires ValidGrid(mat)
    requires ValidValues(mat)
    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures forall i, j :: 0 <= i < N && 0 <= j < N ==> res[i][j] == mat[i][N - 1 - j]
{
    res := seq(N, (i: int) => 
        if 0 <= i < |mat| then 
            seq(N, (j: int) => 
                if 0 <= j < N then mat[i][N - 1 - j] else 0
            )
        else 
            seq(N, _ => 0)
    );
}



// (6) transpose
method transpose(mat: Grid) returns (res: Grid)
    requires ValidGrid(mat)
    requires ValidValues(mat)
    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures forall i, j :: 0 <= i < N && 0 <= j < N ==> res[i][j] == mat[j][i]
{
    res := seq(N, (i: int) => 
        seq(N, (j: int) => 
            if 0 <= i < N && 0 <= j < N then mat[j][i] else 0
        )
    );
}

/* 
4. directional controls
*/
// The game.py should guarantee that a new tile will be generated, if any of the direction function return done = True
// (7) left()

method left(game: Grid) returns (res: Grid, done: bool)
    requires ValidGrid(game)
    requires ValidValues(game)
    requires !HasWinTile(game)
    requires !IsLose(game)

    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures done == (res != game)
    ensures done ==> CountNonZerosGrid(res) <= CountNonZerosGrid(game)
    ensures !done ==> res == game
    ensures !IsLose(game)
{
    var g1, d1 := move(game);
    if !d1 { 
        assert g1 == game; 
    } 
    assert CountNonZerosGrid(g1) == CountNonZerosGrid(game);
    
    
    var g2, d2 := merge(g1);
    if !d2 { 
        assert g2 == g1;
        assert CountNonZerosGrid(g2) == CountNonZerosGrid(g1);
    } else {
        assert CountNonZerosGrid(g2) < CountNonZerosGrid(g1);
    }

    var g3, d3 := move(g2);
    if !d3 { 
        assert g3 == g2; 
    } 
    assert CountNonZerosGrid(g3) == CountNonZerosGrid(g2);

    res := g3;
    done := d1 || d2 || d3;
    if !done {
        assert g1 == game;
        assert g2 == g1;
        assert g3 == g2;
        assert res == game;
    }

    if done {
        // proof: g3 <= g2 <= g1 <= game
        assert CountNonZerosGrid(g3) == CountNonZerosGrid(g2); // move does not change the number of non-zeros
        assert CountNonZerosGrid(g2) <= CountNonZerosGrid(g1); // merge may change the number 
        assert CountNonZerosGrid(g1) == CountNonZerosGrid(game); // move does not change the number
        assert CountNonZerosGrid(g3) <= CountNonZerosGrid(game);
    }
}

// // (8) right()
// method right(game: Grid) returns (res: Grid, done: bool)
//     requires ValidGrid(game)
//     requires ValidValues(game)
//     ensures ValidGrid(res)
//     ensures ValidValues(res)
// {
//     var g1 := reverse(game);
//     var g2, d := left(g1);
//     res := reverse(g2);
//     done := d;
// }

// // (9) up()
// method up(game: Grid) returns (res: Grid, done: bool)
//     requires ValidGrid(game)
//     requires ValidValues(game)
//     ensures ValidGrid(res)
//     ensures ValidValues(res)
// {
//     var g1 := transpose(game);
//     var g2, d := left(g1);
//     res := transpose(g2);
//     done := d;
// }

// // (10) down()
// method down(game: Grid) returns (res: Grid, done: bool)
//     requires ValidGrid(game)
//     requires ValidValues(game)
//     ensures ValidGrid(res)
//     ensures ValidValues(res)
// {
//     var g1 := transpose(game);
//     var g2 := reverse(g1);
//     var g3, d := left(g2);
//     var g4 := reverse(g3);
//     res := transpose(g4);
//     done := d;
// }