type Grid = seq<seq<int>>
const N: int := 4

/*
1. initialization & state management
*/

//(1) new_game()


// First initialize a new board with all tiles being 0
method new_game() returns (matrix: Grid)
    // spec 5: board boundary
    ensures |matrix| == N
    ensures forall i :: 0 <= i < N ==> |matrix[i]| == N
    // ensure tile values are all 0
    ensures forall i, j :: 0 <= i < N && 0 <= j < N ==> matrix[i][j] == 0
{
    var row := seq(N, _ => 0);
    matrix := seq(N, _ => row);
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

method initial_grid_validation(matrix: Grid) returns (b: bool)
    ensures b == IsValidInitialBoard(matrix)
{
    return IsValidInitialBoard(matrix);
}


//(2) game_state()
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

predicate ValidValues(grid: Grid)
    requires ValidGrid(grid)
{
    forall i, j :: 0 <= i < N && 0 <= j < N ==> grid[i][j] == 0 || IsPowerOfTwo(grid[i][j])
}

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


// (4) merge()


/*
3. matrix transformation
*/

// basic definitions
const GRID: nat := 4

type Board = array2<int>

function Pow2(k:nat): int
{
  if k == 0 then 1
  else 2 * Pow2(k-1)
}

predicate ValidTile(v:int)
{
  v == 0 || exists k:nat ::
       0 <= k <= 11 && v == Pow2(k)
}

predicate ValidBoard(b:Board)
  reads b
{
  b.Length0 == GRID &&
  b.Length1 == GRID &&
  forall i,j ::
      0 <= i < GRID &&
      0 <= j < GRID
      ==> ValidTile(b[i,j])
}

// (5) reverse()
method Reverse(b:Board) returns (r:Board)
// spec 2 and 5
  requires ValidBoard(b)
  ensures ValidBoard(r)
  ensures forall i,j ::
      0 <= i < GRID &&
      0 <= j < GRID
      ==> r[i,j] == b[i, GRID-1-j]
{
  r := new int[GRID, GRID];

  var i := 0;
  while i < GRID
    invariant 0 <= i <= GRID
    invariant forall x,y ::
        0 <= x < i &&
        0 <= y < GRID
        ==> r[x,y] == b[x, GRID-1-y]
   {
    var j := 0;
    while j < GRID
      invariant 0 <= j <= GRID

        //0---j-1 cols have been reversed correctly 
      invariant forall y ::
          0 <= y < j
          ==> r[i,y] == b[i, GRID-1-y]

        //0---i-1 have been reversed correctly 
      invariant forall x,y ::
          0 <= x < i &&
          0 <= y < GRID
          ==> r[x,y] == b[x, GRID-1-y]

    {
      r[i,j] := b[i, GRID-1-j];
      j := j + 1;
    }

    i := i + 1;
  }
}


// (6) transpose
method Transpose(b:Board) returns (t:Board)
  requires ValidBoard(b)
  ensures ValidBoard(t)
  ensures forall i,j ::
    0 <= i < GRID &&
    0 <= j < GRID
    ==> t[i,j] == b[j,i]
{
  t := new int[GRID, GRID];

  var i := 0;
  while i < GRID
    invariant 0 <= i <= GRID
    //all rows finished is correct
    invariant forall x,y ::
        0 <= x < i &&
        0 <= y < GRID
        ==> t[x,y] == b[y,x]

  {
    var j := 0;
    while j < GRID
      invariant 0 <= j <= GRID

      // current col has been transposed correctly
      invariant forall y ::
          0 <= y < j
          ==> t[i,y] == b[y,i]

      // previous cols have been transposed correctly
      invariant forall x,y ::
          0 <= x < i &&
          0 <= y < GRID
          ==> t[x,y] == b[y,x]

    {
      t[i,j] := b[j,i];

      j := j + 1;
    }

    i := i + 1;
  }
}

/* 
4. directional controls
*/

// (7) left()

// (8) right()

// (9) up()

// (10) down()