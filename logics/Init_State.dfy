include "Setups.dfy"
/*********************************** 
1. initialization & state management
***********************************/
module Init {
    import opened Setups
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
            invariant forall k, l {:trigger grid[k][l], grid[k+1][l]} :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]
        {
            var j := 0;
            while j < N
                invariant 0 <= j <= N
                invariant forall k, l :: 0 <= k < N && 0 <= l < N - 1 ==> grid[k][l] != grid[k][l+1]
                invariant forall k, l {:trigger grid[k][l], grid[k+1][l]} :: 0 <= k < i && 0 <= l < N ==> grid[k][l] != grid[k+1][l]   // previous columns
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
}