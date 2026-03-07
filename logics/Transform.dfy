include "Setups.dfy"

// module Transform {

// import opened Setups

// function ReverseRow(row: seq<int>): seq<int>
//     requires |row| == N
// {
//     seq(N, j =>
//         if 0 <= N - 1 - j < |row| then row[N - 1 - j] else 0
//     )
// }

// function Reverse(grid: Grid): Grid
//     requires ValidGrid(grid)
// {
//     seq(N, i =>
//         if 0 <= i < |grid| then ReverseRow(grid[i])
//         else seq(N, _ => 0)
//     )
// }

// function Transpose(grid: Grid): Grid
//     requires ValidGrid(grid)
// {
//     seq(N, i =>
//         if 0 <= i < |grid| then
//             seq(N, j =>
//                 if 0 <= j < |grid| then grid[j][i] else 0
//             )
//         else seq(N, _ => 0)
//     )
// }

// }
module Transform {

  import opened Setups

  // ============================================================
  // 1. Basic transformations
  // ============================================================

  // Reverse one row: [a,b,c,d] -> [d,c,b,a]
  function ReverseRow(row: seq<int>): seq<int>
    requires |row| == N
    ensures |ReverseRow(row)| == N
    ensures forall j :: 0 <= j < N ==> ReverseRow(row)[j] == row[N - 1 - j]
  {
    [row[3], row[2], row[1], row[0]]
  }

  // Reverse every row of the grid (horizontal mirror)
  function Reverse(grid: Grid): Grid
    requires ValidGrid(grid)
    ensures ValidGrid(Reverse(grid))
    ensures forall i, j ::
      0 <= i < N && 0 <= j < N ==>
      Reverse(grid)[i][j] == grid[i][N - 1 - j]
  {
    [
      ReverseRow(grid[0]),
      ReverseRow(grid[1]),
      ReverseRow(grid[2]),
      ReverseRow(grid[3])
    ]
  }

  // Transpose the grid: new[i][j] = old[j][i]
  function Transpose(grid: Grid): Grid
    requires ValidGrid(grid)
    ensures ValidGrid(Transpose(grid))
    ensures forall i, j ::
      0 <= i < N && 0 <= j < N ==>
      Transpose(grid)[i][j] == grid[j][i]
  {
    [
      [grid[0][0], grid[1][0], grid[2][0], grid[3][0]],
      [grid[0][1], grid[1][1], grid[2][1], grid[3][1]],
      [grid[0][2], grid[1][2], grid[2][2], grid[3][2]],
      [grid[0][3], grid[1][3], grid[2][3], grid[3][3]]
    ]
  }

  // ============================================================
  // 2. Property-preservation lemmas
  // ============================================================

  // Reverse preserves valid tile values
  lemma ReversePreservesValues(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures ValidValues(Reverse(grid))
  {
    forall i, j | 0 <= i < N && 0 <= j < N
      ensures Reverse(grid)[i][j] == 0 || IsPowerOfTwo(Reverse(grid)[i][j])
    {
      assert 0 <= N - 1 - j < N;
      assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
    }
  }

  // Transpose preserves valid tile values
  lemma TransposePreservesValues(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures ValidValues(Transpose(grid))
  {
    forall i, j | 0 <= i < N && 0 <= j < N
      ensures Transpose(grid)[i][j] == 0 || IsPowerOfTwo(Transpose(grid)[i][j])
    {
      assert Transpose(grid)[i][j] == grid[j][i];
    }
  }

  // Reverse preserves existence of a 2048 tile
  lemma ReversePreservesWin(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasWinTile(grid) == HasWinTile(Reverse(grid))
  {
    if HasWinTile(grid) {
      var i, j :| 0 <= i < N && 0 <= j < N && grid[i][j] == 2048;
      assert 0 <= N - 1 - j < N;
      assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && Reverse(grid)[ii][jj] == 2048;
    }

    if HasWinTile(Reverse(grid)) {
      var i, j :| 0 <= i < N && 0 <= j < N && Reverse(grid)[i][j] == 2048;
      assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
      assert grid[i][N - 1 - j] == 2048;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && grid[ii][jj] == 2048;
    }
  }

  // Transpose preserves existence of a 2048 tile
  lemma TransposePreservesWin(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasWinTile(grid) == HasWinTile(Transpose(grid))
  {
    if HasWinTile(grid) {
      var i, j :| 0 <= i < N && 0 <= j < N && grid[i][j] == 2048;
      assert Transpose(grid)[j][i] == grid[i][j];
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && Transpose(grid)[ii][jj] == 2048;
    }

    if HasWinTile(Transpose(grid)) {
      var i, j :| 0 <= i < N && 0 <= j < N && Transpose(grid)[i][j] == 2048;
      assert Transpose(grid)[i][j] == grid[j][i];
      assert grid[j][i] == 2048;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && grid[ii][jj] == 2048;
    }
  }

  // Reverse preserves existence of empty tiles
  lemma ReversePreservesEmpty(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasEmptyTile(grid) == HasEmptyTile(Reverse(grid))
  {
    if HasEmptyTile(grid) {
      var i, j :| 0 <= i < N && 0 <= j < N && grid[i][j] == 0;
      assert 0 <= N - 1 - j < N;
      assert Reverse(grid)[i][N - 1 - j] == 0;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && Reverse(grid)[ii][jj] == 0;
    }

    if HasEmptyTile(Reverse(grid)) {
      var i, j :| 0 <= i < N && 0 <= j < N && Reverse(grid)[i][j] == 0;
      assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
      assert grid[i][N - 1 - j] == 0;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && grid[ii][jj] == 0;
    }
  }

  // Transpose preserves existence of empty tiles
  lemma TransposePreservesEmpty(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures HasEmptyTile(grid) == HasEmptyTile(Transpose(grid))
  {
    if HasEmptyTile(grid) {
      var i, j :| 0 <= i < N && 0 <= j < N && grid[i][j] == 0;
      assert Transpose(grid)[j][i] == 0;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && Transpose(grid)[ii][jj] == 0;
    }

    if HasEmptyTile(Transpose(grid)) {
      var i, j :| 0 <= i < N && 0 <= j < N && Transpose(grid)[i][j] == 0;
      assert Transpose(grid)[i][j] == grid[j][i];
      assert grid[j][i] == 0;
      assert exists ii, jj :: 0 <= ii < N && 0 <= jj < N && grid[ii][jj] == 0;
    }
  }

  // Reverse preserves whether a merge is still possible
  lemma ReversePreservesMoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures MoreToMerge(grid) == MoreToMerge(Reverse(grid))
  {
    if MoreToMerge(grid) {
      if exists i, j :: 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j + 1] {
        var i, j :| 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j + 1];
        assert 0 <= N - 2 - j < N - 1;
        assert Reverse(grid)[i][N - 2 - j] == grid[i][j + 1];
        assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
        assert exists ii, jj ::
          0 <= ii < N && 0 <= jj < N - 1 &&
          Reverse(grid)[ii][jj] == Reverse(grid)[ii][jj + 1];
      } else {
        var i, j :| 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i + 1][j];
        assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
        assert Reverse(grid)[i + 1][N - 1 - j] == grid[i + 1][j];
        assert exists ii, jj ::
          0 <= ii < N - 1 && 0 <= jj < N &&
          Reverse(grid)[ii][jj] == Reverse(grid)[ii + 1][jj];
      }
    }

    if MoreToMerge(Reverse(grid)) {
      if exists i, j :: 0 <= i < N && 0 <= j < N - 1 && Reverse(grid)[i][j] == Reverse(grid)[i][j + 1] {
        var i, j :| 0 <= i < N && 0 <= j < N - 1 && Reverse(grid)[i][j] == Reverse(grid)[i][j + 1];
        assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
        assert Reverse(grid)[i][j + 1] == grid[i][N - 2 - j];
        assert exists ii, jj ::
          0 <= ii < N && 0 <= jj < N - 1 &&
          grid[ii][jj] == grid[ii][jj + 1];
      } else {
        var i, j :| 0 <= i < N - 1 && 0 <= j < N && Reverse(grid)[i][j] == Reverse(grid)[i + 1][j];
        assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
        assert Reverse(grid)[i + 1][j] == grid[i + 1][N - 1 - j];
        assert exists ii, jj ::
          0 <= ii < N - 1 && 0 <= jj < N &&
          grid[ii][jj] == grid[ii + 1][jj];
      }
    }
  }

  // Transpose preserves whether a merge is still possible
  lemma TransposePreservesMoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures MoreToMerge(grid) == MoreToMerge(Transpose(grid))
  {
    if MoreToMerge(grid) {
      if exists i, j :: 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j + 1] {
        var i, j :| 0 <= i < N && 0 <= j < N - 1 && grid[i][j] == grid[i][j + 1];
        assert Transpose(grid)[j][i] == grid[i][j];
        assert Transpose(grid)[j + 1][i] == grid[i][j + 1];
        assert exists ii, jj ::
          0 <= ii < N - 1 && 0 <= jj < N &&
          Transpose(grid)[ii][jj] == Transpose(grid)[ii + 1][jj];
      } else {
        var i, j :| 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i + 1][j];
        assert Transpose(grid)[j][i] == grid[i][j];
        assert Transpose(grid)[j][i + 1] == grid[i + 1][j];
        assert exists ii, jj ::
          0 <= ii < N && 0 <= jj < N - 1 &&
          Transpose(grid)[ii][jj] == Transpose(grid)[ii][jj + 1];
      }
    }

    if MoreToMerge(Transpose(grid)) {
      if exists i, j :: 0 <= i < N && 0 <= j < N - 1 && Transpose(grid)[i][j] == Transpose(grid)[i][j + 1] {
        var i, j :| 0 <= i < N && 0 <= j < N - 1 && Transpose(grid)[i][j] == Transpose(grid)[i][j + 1];
        assert Transpose(grid)[i][j] == grid[j][i];
        assert Transpose(grid)[i][j + 1] == grid[j + 1][i];
        assert exists ii, jj ::
          0 <= ii < N - 1 && 0 <= jj < N &&
          grid[ii][jj] == grid[ii + 1][jj];
      } else {
        var i, j :| 0 <= i < N - 1 && 0 <= j < N && Transpose(grid)[i][j] == Transpose(grid)[i + 1][j];
        assert Transpose(grid)[i][j] == grid[j][i];
        assert Transpose(grid)[i + 1][j] == grid[j][i + 1];
        assert exists ii, jj ::
          0 <= ii < N && 0 <= jj < N - 1 &&
          grid[ii][jj] == grid[ii][jj + 1];
      }
    }
  }

  // ============================================================
  // 3. Combined game-state preservation
  // ============================================================

  lemma ReversePreservesLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures IsLose(grid) == IsLose(Reverse(grid))
  {
    ReversePreservesWin(grid);
    ReversePreservesEmpty(grid);
    ReversePreservesMoreToMerge(grid);
  }

  lemma TransposePreservesLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures IsLose(grid) == IsLose(Transpose(grid))
  {
    TransposePreservesWin(grid);
    TransposePreservesEmpty(grid);
    TransposePreservesMoreToMerge(grid);
  }

  // ============================================================
  // 4. Involution lemmas: applying twice gives back the original
  // ============================================================

  lemma ReverseRowInvolution(row: seq<int>)
    requires |row| == N
    ensures ReverseRow(ReverseRow(row)) == row
  {
    assert ReverseRow(row) == [row[3], row[2], row[1], row[0]];
    assert ReverseRow(ReverseRow(row)) ==
      [ReverseRow(row)[3], ReverseRow(row)[2], ReverseRow(row)[1], ReverseRow(row)[0]];
    assert ReverseRow(ReverseRow(row)) == [row[0], row[1], row[2], row[3]];
  }

  lemma ReverseInvolution(grid: Grid)
    requires ValidGrid(grid)
    ensures Reverse(Reverse(grid)) == grid
  {
    ReverseRowInvolution(grid[0]);
    ReverseRowInvolution(grid[1]);
    ReverseRowInvolution(grid[2]);
    ReverseRowInvolution(grid[3]);

    assert Reverse(Reverse(grid)) ==
      [
        ReverseRow(ReverseRow(grid[0])),
        ReverseRow(ReverseRow(grid[1])),
        ReverseRow(ReverseRow(grid[2])),
        ReverseRow(ReverseRow(grid[3]))
      ];

    assert Reverse(Reverse(grid)) == [grid[0], grid[1], grid[2], grid[3]];
  }

  lemma TransposeInvolution(grid: Grid)
    requires ValidGrid(grid)
    ensures Transpose(Transpose(grid)) == grid
  {
    assert |grid[0]| == N;
    assert |grid[1]| == N;
    assert |grid[2]| == N;
    assert |grid[3]| == N;

    assert Transpose(grid) ==
      [
        [grid[0][0], grid[1][0], grid[2][0], grid[3][0]],
        [grid[0][1], grid[1][1], grid[2][1], grid[3][1]],
        [grid[0][2], grid[1][2], grid[2][2], grid[3][2]],
        [grid[0][3], grid[1][3], grid[2][3], grid[3][3]]
      ];

    assert Transpose(Transpose(grid)) ==
      [
        [grid[0][0], grid[0][1], grid[0][2], grid[0][3]],
        [grid[1][0], grid[1][1], grid[1][2], grid[1][3]],
        [grid[2][0], grid[2][1], grid[2][2], grid[2][3]],
        [grid[3][0], grid[3][1], grid[3][2], grid[3][3]]
      ];

    assert [grid[0][0], grid[0][1], grid[0][2], grid[0][3]] == grid[0];
    assert [grid[1][0], grid[1][1], grid[1][2], grid[1][3]] == grid[1];
    assert [grid[2][0], grid[2][1], grid[2][2], grid[2][3]] == grid[2];
    assert [grid[3][0], grid[3][1], grid[3][2], grid[3][3]] == grid[3];
  }
}