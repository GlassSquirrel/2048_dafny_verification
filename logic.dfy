include "logics/Setups.dfy"
include "logics/Init_State.dfy"
include "logics/Move.dfy"
include "logics/Merge.dfy"
include "logics/Directions.dfy"

module Logic {
    import opened Setups
    import opened Init
    import opened Move
    import opened Merge
    import opened DirectionControls

    method new_game_wrapper() returns (g: Grid)
        ensures ValidGrid(g)
        ensures ValidValues(g)
    {
        g := new_game();
    }

    method initial_grid_validation_wrapper(grid: Grid) returns (b: bool)
    {
        b := initial_grid_validation(grid);
    }

    method game_state_wrapper(grid: Grid) returns (s: State)
        requires ValidGrid(grid)
        requires ValidValues(grid)
    {
        s := game_state(grid);  
    }

    method left_wrapper(grid: Grid) returns (res: Grid, done: bool)
        requires ValidGrid(grid)
        requires ValidValues(grid)
        requires !HasWinTile(grid)
        requires !IsLose(grid)
    {
        res, done := left(grid);
    }

    //   method right_wrapper(grid: Grid) returns (res: Grid, done: bool)
    //   {
    //     res, done := right(grid);
    //   }

    //   method up_wrapper(grid: Grid) returns (res: Grid, done: bool)
    //   {
    //     res, done := up(grid);
    //   }

    //   method down_wrapper(grid: Grid) returns (res: Grid, done: bool)
    //   {
    //      res, done := down(grid);
    //   }

    method new_tile_validation_wrapper(oldGrid: Grid, moved: bool, newGrid: Grid) returns (ok: bool)
    {
        ok :=new_tile_validation(oldGrid, moved, newGrid);
    }
}
