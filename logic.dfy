/*
1. initialization & state management
*/

//(1) new_game()
type Grid = seq<seq<int>>

// First initialize a new board with all tiles being 0
method new_game(n: nat) returns (matrix: Grid)
    // Precondition
    requires n > 0
    // Postcondition
    // spec 5: board boundary
    ensures |matrix| == n
    ensures forall i :: 0 <= i < n ==> |matrix[i]| == n
    // ensure tile values are all 0
    ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> matrix[i][j] == 0
{
    var row := seq(n, _ => 0);
    matrix := seq(n, _ => row);
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

// Predicate to check whether the random initialization of grid is valid or not
predicate IsValidInitialBoard(grid: Grid, n: int)
{
    n > 0 &&
    |grid| == n &&
    (forall i :: 0 <= i < n ==> |grid[i]| == n) &&
    (forall i, j :: 0 <= i < n && 0 <= j < n ==> grid[i][j] == 0 || grid[i][j] == 2) &&
    CountInGrid(grid, 2) == 2   // two 2 generated
}

method initial_grid_validation(matrix: Grid, n: int) returns (b: bool)
    ensures b == IsValidInitialBoard(matrix, n)
{
    return IsValidInitialBoard(matrix, n);
}


//(2) game_state()



/*
2. core movement 
*/

// (3) move()

// (4) merge()


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