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

// Lemma 4：FilterNonZeros does not change Count(non-zeros)
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

// lemma 5:
lemma CountGridAdditivity(temp: seq<seq<int>>, row: seq<int>)
    ensures CountNonZerosGrid(temp + [row]) == CountNonZerosGrid(temp) + CountNonZerosRow(row)
    // decreases |temp|
{
    if temp == [] {
        // temp + [row] == [row]
        assert temp + [row] == [row];
        assert CountNonZerosGrid([row]) 
               == CountNonZerosRow(row);
    } else {
        CountGridAdditivity(temp[1..], row);

        assert temp == [temp[0]] + temp[1..];
        assert temp + [row] == [temp[0]] + (temp[1..] + [row]);

        assert CountNonZerosGrid(temp) == CountNonZerosRow(temp[0]) + CountNonZerosGrid(temp[1..]);

        assert CountNonZerosGrid(temp + [row]) == CountNonZerosRow(temp[0]) + CountNonZerosGrid(temp[1..] + [row]);
    }
}

// lemma 6
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

// lemmas based on above:
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

// lemma 2: if we apply move() on a well-performed row, nothing gonna change
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
        // 由 well-performed 在 k=0 得到 row[1]==0
        assert row[0] == 0 ==> row[1] == 0;
        assert row[1] == 0;

        // 证明后缀仍 well-performed
        assert WellPerformedRow(row[1..]) by {
            forall k | 0 <= k < |row[1..]| - 1
                ensures row[1..][k] == 0 ==> row[1..][k+1] == 0
            {
                // row[1..][k] = row[k+1]
                assert row[1..][k] == row[k+1];
                assert row[1..][k+1] == row[k+2];
                // 用原 well-performed 的性质在索引 k+1 上
                assert row[k+1] == 0 ==> row[k+2] == 0;
            }
        }

        WellPerformedRowFirstZeroAllZeros(row[1..]);

        // 拼回来
        assert row == [row[0]] + row[1..];
        assert row[1..] == seq(|row| - 1, _ => 0);
        assert row == [0] + seq(|row| - 1, _ => 0);
        assert [0] + seq(|row| - 1, _ => 0) == seq(|row|, _ => 0);
    }
}

lemma WellPerformedRowDoNotMove(row: seq<int>)
    requires WellPerformedRow(row)
    ensures FilterNonZeros(row) +
            seq(|row| - |FilterNonZeros(row)|, _ => 0) == row
    decreases |row|
{
    if |row| == 0 {
        // 两边都是 []
    } else if row[0] == 0 {
        // row 全 0
        WellPerformedRowFirstZeroAllZeros(row);
        assert row == seq(|row|, _ => 0);

        // FilterNonZeros(seq(k,0)) == []
        FilterZerosIsEmpty(|row|);
        assert FilterNonZeros(row) == [];

        // RHS: [] + seq(|row|,0) == seq(|row|,0) == row
        assert FilterNonZeros(row) + seq(|row| - |FilterNonZeros(row)|, _ => 0)
            == [] + seq(|row| - 0, _ => 0);
        assert [] + seq(|row|, _ => 0) == seq(|row|, _ => 0);
    } else {
        // row[0] != 0
        // 证明后缀仍 well-performed
        assert WellPerformedRow(row[1..]) by {
            forall k | 0 <= k < |row[1..]| - 1
                ensures row[1..][k] == 0 ==> row[1..][k+1] == 0
            {
                assert row[1..][k] == row[k+1];
                assert row[1..][k+1] == row[k+2];
                assert row[k+1] == 0 ==> row[k+2] == 0;
            }
        }

        // 归纳假设
        WellPerformedRowDoNotMove(row[1..]);

        // 展开 FilterNonZeros 的定义（因为 row[0]!=0）
        assert FilterNonZeros(row) == [row[0]] + FilterNonZeros(row[1..]);

        // 计算 padding 长度：|row| - |FilterNonZeros(row)| = |row[1..]| - |FilterNonZeros(row[1..])|
        assert |row| == 1 + |row[1..]|;
        assert |FilterNonZeros(row)| == 1 + |FilterNonZeros(row[1..])|;

        // 拼回去
        assert FilterNonZeros(row) + seq(|row| - |FilterNonZeros(row)|, _ => 0)
            == ([row[0]] + FilterNonZeros(row[1..])) +
               seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0);

        // 用归纳假设替换 FilterNonZeros(row[1..]) + padding
        assert FilterNonZeros(row[1..]) +
               seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0)
               == row[1..];

        // 连接律
        assert ([row[0]] + FilterNonZeros(row[1..])) +
               seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0)
            == [row[0]] + (FilterNonZeros(row[1..]) +
               seq(|row[1..]| - |FilterNonZeros(row[1..])|, _ => 0));

        assert [row[0]] + row[1..] == row;
    }
}

/*****
Extras
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

// The generated empty board will be passed into game.py to generate random 2s, then passed back
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
    ensures !IsLose(new_mat)
    // 3.  spec 6: if done=True, then the mat changes
    ensures done == (new_mat != mat)
    // 4.  spec 6: every row preserve the same element and non-zero element remain in same order
    ensures forall i :: 0 <= i < N ==> FilterNonZeros(new_mat[i]) == FilterNonZeros(mat[i])
    ensures CountNonZerosGrid(new_mat) == CountNonZerosGrid(mat)
    // 5.  spec 6: performance of the row
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

        // var old_temp := temp_grid[..i];   // old_temp: before adding the new row
        // temp_grid := temp_grid + [row_res];

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
    // 从循环不变式：done ==> exists k < N && CompressRow(mat[k]).1 取 witness
    var k :| 0 <= k < N && CompressRow(mat[k]).1;

    // 用行 lemma：如果 CompressRow(mat[k]).1 为真，则压缩结果最后一格为 0
    CompressRowLastElementIs0(mat[k]);

    // safety：new_mat[k] 是 CompressRow(mat[k]).0
    assert new_mat[k] == CompressRow(mat[k]).0;

    // 所以 new_mat[k][N-1] == 0
    assert new_mat[k][N-1] == 0;

    // 构造 exists witness：r=k, c=N-1
    assert exists r, c :: 0 <= r < N && 0 <= c < N && new_mat[r][c] == 0 by {
        assert 0 <= k < N;
        assert 0 <= N-1 < N;
        // witness
    }

        ImpliesNotLose(new_mat);
    }
if HasWinTile(mat) {
    // 取 witness：mat 中存在 2048 的位置
    var r, c :| 0 <= r < N && 0 <= c < N && mat[r][c] == 2048;

    // 行级：压缩不改变 win（你已有 lemma）
    CompressRowPreservesWin(mat[r]);

    // safety：new_mat[r] 就是 CompressRow(mat[r]).0
    assert new_mat[r] == CompressRow(mat[r]).0;

    // 从 mat[r][c]==2048 推出 HasWinTileRow(mat[r])
    assert HasWinTileRow(mat[r]);

    // 用 CompressRowPreservesWin 得到 HasWinTileRow(new_mat[r])
    assert HasWinTileRow(new_mat[r]);

    // 从 HasWinTileRow(new_mat[r]) 推出 HasWinTile(new_mat)
    assert HasWinTile(new_mat);
}
    // proof for preserve the state
if !HasWinTile(mat) {
    if HasWinTile(new_mat) {
        var r, c :| 0 <= r < N && 0 <= c < N && new_mat[r][c] == 2048;

        // safety
        assert new_mat[r] == CompressRow(mat[r]).0;

        // 行级 preserves：HasWinTileRow(mat[r]) <==> HasWinTileRow(new_mat[r])
        CompressRowPreservesWin(mat[r]);

        assert HasWinTileRow(new_mat[r]);
        assert HasWinTileRow(mat[r]);   // 用 <==> 反推
        assert HasWinTile(mat);
        assert false;
    }
}
    assert !IsLose(mat) ==> !IsLose(new_mat);

    return new_mat, done;
}

// // a method to show that if two moves are in the same direction in a row, second done is false
// method TwoMovesSameDirSecondNotDone(mat: Grid)
// requires ValidGrid(mat)
// requires ValidValues(mat)
// requires !IsLose(mat)
// {
// var g1, d1 := move(mat);
// assert WellPerformedGrid(g1);

// var g2, d2 := move(g1);
// assert !d2;
// assert d2 == (g2 != g1);
// assert g2 == g1;
// }
/**********
(4) merge()
***********/
// merge() merges the neighboring 2 tiles with same value, should satisfy spec 1, 2, 3, 5, 6
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
    ensures CountNonZerosRow(merge_pair(row, j)) == CountNonZerosRow(row) - 1   // spec 1: after merging, count(non-zeros) should -1
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



// The merge method should satisfy spec 1, 2, 3, 5, 6
method merge(grid: Grid) returns (res: Grid, done: bool)
    // Preconditions:
    // 1. spec 2 & 5: value and grid validity
    requires ValidGrid(grid)
    requires ValidValues(grid)
    // 2. game state
    requires !HasWinTile(grid)
    requires !IsLose(grid)
    // 3. only receives wellperformed grid (after move)
    requires WellPerformedGrid(grid)

    // Postconditions:
    // 1. spec 2 & 5: value and grid validity
    ensures ValidGrid(res)     // spec 5
    ensures ValidValues(res)     // spec 2
    // 2. spec 6: if done = true, then the board changes (including count)
    ensures !done ==> res == grid   
    ensures done == (res != grid)
    ensures !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
    ensures done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
    // 3. spec 1 & 3: once merged, will have empty tile and game state cannot be lose
    ensures done ==> HasEmptyTile(res)
    ensures !IsLose(res)
    // 4. spec 6: for performance, if done, can be well-performed or not well-performed; if !done, must be well-performed
    ensures !done ==> WellPerformedGrid(res)
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
            // spec 1: for each tile, merge only happens once
            invariant forall k :: 0 <= k < N ==> 0 <= merged_counts[k] <= 1
            invariant forall k :: j <= k < N ==> merged_counts[k] == 0
            invariant forall k :: i < k < N ==> res[k] == grid[k]   // later rows remain unsolved
            invariant forall k :: 0 <= k < N && k != i ==> res[k] == (if k < i then res[k] else grid[k])
            invariant done ==> HasEmptyTile(res)
            invariant !IsLose(res)
            invariant done ==> CountNonZerosGrid(res) < CountNonZerosGrid(grid)
            invariant !done ==> CountNonZerosGrid(res) == CountNonZerosGrid(grid)
        {
            if res[i][j] == res[i][j+1] && res[i][j] != 0 && merged_counts[j] == 0 && merged_counts[j+1] == 0
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

// (7) left()
lemma DoneImpliesResultChanged(
    game: Grid,
    g1: Grid, g2: Grid, g3: Grid,
    d1: bool, d2: bool, d3: bool)
    requires !d1 ==> g1 == game
    requires !d2 ==> g2 == g1
    requires !d3 ==> g3 == g2

    requires d1 ==> g1 != game
    requires d2 ==> g2 != g1
    requires d3 ==> g3 != g2

    requires CountNonZerosGrid(g1) == CountNonZerosGrid(game)   // move preserves count
    requires d2 ==> CountNonZerosGrid(g2) < CountNonZerosGrid(g1) // merge done decreases count
    requires CountNonZerosGrid(g3) == CountNonZerosGrid(g2)     // move preserves count

    requires WellPerformedGrid(g1)
    requires WellPerformedGrid(g2) ==> !d3
    
    requires d1 || d2 || d3
    ensures g3 != game
{
    if g3 == game {
        // 1. move, merge, move
        if d1 && d2 && d3{
            assert g1 != game;
            assert g2 != g1;
            assert g2 != game;
            assert g2 != g3;
            assert g3 != game;
        }
        // 2. no move, merge, move
        if !d1 && d2 && d3{
            assert g1 == game;
            assert g2 != g1;
            assert g2 != game;
            assert g3 != g2;
            assert g3 != game;
        }

        // 3. move，no merge，move
        if d1 && !d2 && d3{ 
            assert g2 == g1;
            assert WellPerformedGrid(g1);
            assert WellPerformedGrid(g2);

            assert !d3;
            assert false;
        }

        // 4. move, merge, no move
        if d1 && d2 && !d3{
            assert g1 != game;
            assert g2!= g1;
            assert g2 != game;
            assert g2 == g3;
            assert g3 != game;
        }
        
        // 5. no move, no merge, move
        if !d1 && !d2 && d3{
            assert g2 == g1;
            assert g1 == game;
            assert g2 == game;
            assert g3 != g2;
            assert false;
        }

        // 6. move, no merge, no move
        if d1 && !d2 && !d3{
            assert !d3 ==> g3 == g2;
            assert !d2 ==> g2 == g1;
            assert g3 == g2;
            assert g2 == g1;
            assert g3 == g1;
            assert g1 == game;
            assert g1 != game;
            assert false;
        }

        // 7. no move, no merge, no move
        if !d1 && d2 && !d3{
            assert !d3 ==> g3 == g2;
            assert !d1 ==> g1 == game;
            assert g3 == g2;
            assert g2 == game;
            assert g1 == game;
            assert g2 == g1;
            assert g2 != g1;
            assert false;
        }

        // last chance:
        assert !d1 && !d2 && !d3;
        assert false;    // contradict requires d1 || d2 || d3
    }
}

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
    ensures !IsLose(res)
{
    // 2 2 4 8
    // step 1
    var g1, d1 := move(game);
    if !d1 { 
        assert g1 == game; 
    } else {
        assert g1 != game;
    }
    assert CountNonZerosGrid(g1) == CountNonZerosGrid(game);
    assert ValidGrid(g1);
    assert WellPerformedGrid(g1);

    // step 2  4 0 4 8
    var g2, d2 := merge(g1);
    assert ValidGrid(g2);
    if !d2 { 
        assert g2 == g1;
        assert CountNonZerosGrid(g2) == CountNonZerosGrid(g1);
        assert WellPerformedGrid(g2);
    } else {
        assert g1 != g2;
        assert CountNonZerosGrid(g2) < CountNonZerosGrid(g1);
    }

    // step 3   4 4 8 0 
    var g3, d3 := move(g2);
    assert ValidGrid(g3);
    if WellPerformedGrid(g2) {
    assert !d3;
    }
    assert WellPerformedGrid(g2) ==> !d3;

    if !d3 { 
        assert g3 == g2; 
    } else {
        assert g3 != g2;
    }
    
    assert CountNonZerosGrid(g3) == CountNonZerosGrid(g2);

    res := g3;
    done := d1 || d2 || d3;

    if !done {
        assert d1 == false && d2 == false && d3 == false;
        assert g1 == game;
        assert g2 == g1;
        assert g3 == g2;
        assert res == game;
    }

    if done {
        // proof: g3 <= g2 <= g1 <= game
        assert ValidGrid(g1);
        assert ValidGrid(g2);
        assert WellPerformedGrid(g1);
        assert WellPerformedGrid(g2) ==> !d3;
        assert d1 || d2 || d3;

        DoneImpliesResultChanged(game, g1, g2, g3, d1, d2, d3);
        // assert CountNonZerosGrid(g3) == CountNonZerosGrid(g2); // move does not change the number of non-zeros
        // assert CountNonZerosGrid(g2) <= CountNonZerosGrid(g1); // merge may change the number 
        // assert CountNonZerosGrid(g1) == CountNonZerosGrid(game); // move does not change the number
        // assert CountNonZerosGrid(g3) <= CountNonZerosGrid(game);
    }
}