type Grid = seq<seq<int>>
const N: int := 4

// spec 5: board boundry
predicate ValidGrid(grid: Grid) 
{
    |grid| == N && forall i :: 0 <= i < N ==> |grid[i]| == N
}

// predicate IsPowerOfTwo(x: int)
// {
//     x == 2 || x == 4 || x == 8 || x == 16 || x == 32 ||
//     x == 64 || x == 128 || x == 256 || x == 512 || x == 2048
// }
// better implementation of IsPowerOfTwo for 2048 (exclude 1)
predicate IsPowerOfTwo(x: int)
{
    if x < 2 then false
    else if x == 2 then true
    else x % 2 == 0 && IsPowerOfTwo(x / 2)
}

// spec 2: valid tile values
predicate ValidValues(grid: Grid)
    requires ValidGrid(grid)
{
    forall i, j :: 0 <= i < N && 0 <= j < N ==> grid[i][j] == 0 || IsPowerOfTwo(grid[i][j])
}

/*
1. initialization & state management
*/

//(1) new_game()
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

//(2) game_state()
// Define 3 predicates to check for "has win" / "has lose" / "can continue"
// predicate 1: has win (tile value reaches 2048)
predicate HasWinTile(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 2048
}

// predicate 2: has tile value = 0 (can generate new 2)
predicate HasEmptyTile(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    exists i, j :: 0 <= i < N && 0 <= j < N && grid[i][j] == 0
}

// predicate 3: has more room to merge
predicate MoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    // rows
    (exists i, j :: 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j+1]) ||
    // columns
    (exists i, j :: 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i+1][j])
}

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
        invariant forall k, l :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]
    {
        var j := 0;
        while j < N
            invariant 0 <= j <= N
            invariant forall k, l :: 0 <= k < N && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]
            invariant forall k, l :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]   // previous columns
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

/*
2. core movement 
*/

// (3) move()

// (4) merge() - merge the neighboring 2 tiles with same value
// should satisfy spec 1, 2, 3, 5

// spec 1: only merge tiles with same value, the first tile should be 2 * original value; second tile shoud be 0
function merge_pair(row: seq<int>, j: int): (res: seq<int>)
    requires 0 <= j < |row| - 1
    // spec 1: only merge tiles with the same value
    requires row[j] == row[j + 1] && row[j] != 0
    requires IsPowerOfTwo(row[j])

    ensures |res| == |row|
    // spec 1: after merging, the first tile should be exactly double the original value;
    // the second tile must be 0
    ensures res[j] == row[j] * 2
    ensures res[j+1] == 0
    ensures IsPowerOfTwo(res[j])
    // does not change other tiles
    ensures forall k :: 0 <= k < |row| && k != j && k != j + 1 ==> res[k] == row[k]
{
    var row_with_double := row[j := row[j] * 2];
    row_with_double[j+1 := 0]
}

// spec 1: every tile should only be merged once in one operation
function update_count(counts: seq<int>, j: int): seq<int>
    requires 0 <= j < |counts| - 1
{
    counts[j := counts[j] + 1][j + 1 := counts[j+1] + 1]
}

// spec 3: after merging, the same state cannot be lose
predicate IsLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    !HasWinTile(grid) && !HasEmptyTile(grid) && !MoreToMerge(grid)
}

lemma ImpliesNotLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasEmptyTile(grid) ==> !IsLose(grid)

method merge(grid: Grid, done_in: bool) returns (res: Grid, done: bool)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    // precondition for game state
    requires !HasWinTile(grid)
    requires !IsLose(grid)

    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures done_in ==> done
    ensures !done ==> res == grid
    // [pstcondition for once merged, will have empty tile and game state cannot be lose
    ensures (done && !done_in) ==> HasEmptyTile(res)
    ensures !IsLose(res)
{
    res := grid;
    done := done_in;
    
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant ValidGrid(res)
        invariant ValidValues(res)
        invariant done_in ==> done
        invariant !done ==> res == grid
        invariant forall row_idx :: i <= row_idx < N ==> res[row_idx] == grid[row_idx]  //current row and later rows remain unsolved
        invariant (done && !done_in) ==> HasEmptyTile(res)
        invariant !IsLose(res)
    {
        var j := 0;   // reset j
        var merged_counts := seq(N, _ => 0);   // initialize the merge count for current row

        while j < N - 1
            invariant 0 <= j <= N
            invariant ValidGrid(res)
            invariant ValidValues(res)
            invariant done_in ==> done
            invariant !done ==> res == grid
            invariant |merged_counts| == N
            invariant forall k :: 0 <= k < N ==> 0 <= merged_counts[k] <= 1
            invariant forall k :: j <= k < N ==> merged_counts[k] == 0
            invariant forall row_idx :: i < row_idx < N ==> res[row_idx] == grid[row_idx]  // later rows remain unsolved
            invariant (done && !done_in) ==> HasEmptyTile(res)
            invariant !IsLose(res)

        {
            if res[i][j] == res[i][j+1] && res[i][j] != 0 
            {
                assert merged_counts[j] == 0 && merged_counts[j+1] == 0;
                var updatedRow := merge_pair(res[i], j);
                res := res[i := updatedRow];

                merged_counts := update_count(merged_counts, j);

                assert res[i][j+1] == 0;
                assert HasEmptyTile(res);
                ImpliesNotLose(res);

                done := true;   // for spec 6
                
                j := j + 2;   // ignore next tile (already be 0)
            }
            else 
            {
                j := j + 1;
            }
        }
        i := i + 1;
    }
}

// should have a predicate check for spec 6: if !done, then no new generation of 2

/*
3. matrix transformation
*/
// (5) reverse()

// (6) transpose

/* 
4. directional controls
*/

// (7) left()

// (8) right()

// (9) up()

// (10) down()