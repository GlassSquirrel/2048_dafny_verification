include "Setups.dfy"

module Transform {

  import opened Setups

  // ============================================================
  // 1. Basic transformations
  // ============================================================

  // Reverse one row
  function ReverseRow(row: seq<int>): seq<int>
    requires |row| == N
    ensures |ReverseRow(row)| == N
    ensures forall j :: 0 <= j < N ==> ReverseRow(row)[j] == row[N - 1 - j]
  {
    seq(N, j requires 0 <= j < N => row[N - 1 - j])
  }

  // Reverse each row of grid
  function Reverse(grid: Grid): Grid
    requires ValidGrid(grid)
    ensures ValidGrid(Reverse(grid))
    ensures forall i, j ::
              0 <= i < N && 0 <= j < N ==>
                Reverse(grid)[i][j] == grid[i][N - 1 - j]
  {
    seq(N, i requires 0 <= i < N => ReverseRow(grid[i]))
  }

  // Transpose grid
  function Transpose(grid: Grid): Grid
    requires ValidGrid(grid)
    ensures ValidGrid(Transpose(grid))
    ensures forall i, j ::
              0 <= i < N && 0 <= j < N ==>
                Transpose(grid)[i][j] == grid[j][i]
  {
    seq(N, i requires 0 <= i < N =>
      seq(N, j requires 0 <= j < N => grid[j][i]))
  }

  // ============================================================
  // 2. Property-preservation lemmas
  // ============================================================

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

lemma ReversePreservesMoreToMerge(grid: Grid)
  requires ValidGrid(grid)
  requires ValidValues(grid)
  ensures MoreToMerge(grid) == MoreToMerge(Reverse(grid))
{
  // grid -> Reverse(grid)
  if MoreToMerge(grid) {
    if exists i, j ::
        0 <= i < N && 0 <= j < N - 1 &&
        grid[i][j] == grid[i][j + 1]
    {
      var i, j :|
        0 <= i < N && 0 <= j < N - 1 &&
        grid[i][j] == grid[i][j + 1];

      assert 0 <= N - 2 - j < N - 1;
      assert Reverse(grid)[i][N - 2 - j] == grid[i][j + 1];
      assert Reverse(grid)[i][N - 1 - j] == grid[i][j];

      assert exists ii, jj ::
          ii == i &&
          jj == N - 2 - j &&
          0 <= ii < N &&
          0 <= jj < N - 1 &&
          Reverse(grid)[ii][jj] == Reverse(grid)[ii][jj + 1];
    } else {
      assert exists i, j {:trigger grid[i][j], grid[i + 1][j]} ::
          0 <= i < N - 1 && 0 <= j < N &&
          grid[i][j] == grid[i + 1][j];

      var i, j :| 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i + 1][j];

      assert 0 <= N - 1 - j < N;
      assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
      assert Reverse(grid)[i + 1][N - 1 - j] == grid[i + 1][j];

      assert exists ii, jj {:trigger Reverse(grid)[ii][jj], Reverse(grid)[ii + 1][jj]} ::
          ii == i &&
          jj == N - 1 - j &&
          0 <= ii < N - 1 &&
          0 <= jj < N &&
          Reverse(grid)[ii][jj] == Reverse(grid)[ii + 1][jj];
    }
  }

  // Reverse(grid) -> grid
  if MoreToMerge(Reverse(grid)) {
    if exists i, j ::
        0 <= i < N && 0 <= j < N - 1 &&
        Reverse(grid)[i][j] == Reverse(grid)[i][j + 1]
    {
      var i, j :|
        0 <= i < N && 0 <= j < N - 1 &&
        Reverse(grid)[i][j] == Reverse(grid)[i][j + 1];

      assert 0 <= N - 2 - j < N - 1;
      assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
      assert Reverse(grid)[i][j + 1] == grid[i][N - 2 - j];

      assert exists ii, jj ::
          ii == i &&
          jj == N - 2 - j &&
          0 <= ii < N &&
          0 <= jj < N - 1 &&
          grid[ii][jj] == grid[ii][jj + 1];
    } else {
      assert exists i, j {:trigger Reverse(grid)[i][j], Reverse(grid)[i + 1][j]} ::
          0 <= i < N - 1 && 0 <= j < N &&
          Reverse(grid)[i][j] == Reverse(grid)[i + 1][j];

      var i, j :| 0 <= i < N - 1 && 0 <= j < N && Reverse(grid)[i][j] == Reverse(grid)[i + 1][j];

      assert 0 <= N - 1 - j < N;
      assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
      assert Reverse(grid)[i + 1][j] == grid[i + 1][N - 1 - j];

      assert exists ii, jj {:trigger grid[ii][jj], grid[ii + 1][jj]} ::
          ii == i &&
          jj == N - 1 - j &&
          0 <= ii < N - 1 &&
          0 <= jj < N &&
          grid[ii][jj] == grid[ii + 1][jj];
    }
  }
}

  lemma TransposePreservesMoreToMerge(grid: Grid)
  requires ValidGrid(grid)
  requires ValidValues(grid)
  ensures MoreToMerge(grid) == MoreToMerge(Transpose(grid))
{
  // grid -> Transpose(grid)
  if MoreToMerge(grid) {
    if exists i, j ::
        0 <= i < N && 0 <= j < N - 1 &&
        grid[i][j] == grid[i][j + 1]
    {
      var i, j :|
        0 <= i < N && 0 <= j < N - 1 &&
        grid[i][j] == grid[i][j + 1];

      assert Transpose(grid)[j][i] == grid[i][j];
      assert Transpose(grid)[j + 1][i] == grid[i][j + 1];

      assert exists ii, jj {:trigger Transpose(grid)[ii][jj], Transpose(grid)[ii + 1][jj]} ::
          ii == j &&
          jj == i &&
          0 <= ii < N - 1 &&
          0 <= jj < N &&
          Transpose(grid)[ii][jj] == Transpose(grid)[ii + 1][jj];
    } else {
      assert exists i, j {:trigger grid[i][j], grid[i + 1][j]} ::
          0 <= i < N - 1 && 0 <= j < N &&
          grid[i][j] == grid[i + 1][j];

      var i, j :| 0 <= i < N - 1 && 0 <= j < N && grid[i][j] == grid[i + 1][j];

      assert Transpose(grid)[j][i] == grid[i][j];
      assert Transpose(grid)[j][i + 1] == grid[i + 1][j];

      assert exists ii, jj ::
          ii == j &&
          jj == i &&
          0 <= ii < N &&
          0 <= jj < N - 1 &&
          Transpose(grid)[ii][jj] == Transpose(grid)[ii][jj + 1];
    }
  }

  // Transpose(grid) -> grid
  if MoreToMerge(Transpose(grid)) {
    if exists i, j ::
        0 <= i < N && 0 <= j < N - 1 &&
        Transpose(grid)[i][j] == Transpose(grid)[i][j + 1]
    {
      var i, j :|
        0 <= i < N && 0 <= j < N - 1 &&
        Transpose(grid)[i][j] == Transpose(grid)[i][j + 1];

      assert Transpose(grid)[i][j] == grid[j][i];
      assert Transpose(grid)[i][j + 1] == grid[j + 1][i];

      assert exists ii, jj {:trigger grid[ii][jj], grid[ii + 1][jj]} ::
          ii == j &&
          jj == i &&
          0 <= ii < N - 1 &&
          0 <= jj < N &&
          grid[ii][jj] == grid[ii + 1][jj];
    } else {
      assert exists i, j {:trigger Transpose(grid)[i][j], Transpose(grid)[i + 1][j]} ::
          0 <= i < N - 1 && 0 <= j < N &&
          Transpose(grid)[i][j] == Transpose(grid)[i + 1][j];

      var i, j :| 0 <= i < N - 1 && 0 <= j < N && Transpose(grid)[i][j] == Transpose(grid)[i + 1][j];

      assert Transpose(grid)[i][j] == grid[j][i];
      assert Transpose(grid)[i + 1][j] == grid[j][i + 1];

      assert exists ii, jj ::
          ii == j &&
          jj == i &&
          0 <= ii < N &&
          0 <= jj < N - 1 &&
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
    assert |ReverseRow(ReverseRow(row))| == N;
    assert |row| == N;

    forall j | 0 <= j < N
      ensures ReverseRow(ReverseRow(row))[j] == row[j]
    {
      assert 0 <= N - 1 - j < N;
      assert ReverseRow(ReverseRow(row))[j] == ReverseRow(row)[N - 1 - j];
      assert ReverseRow(row)[N - 1 - j] == row[N - 1 - (N - 1 - j)];
      assert N - 1 - (N - 1 - j) == j;
    }

    assert ReverseRow(ReverseRow(row)) == row;
  }

  lemma ReverseInvolution(grid: Grid)
    requires ValidGrid(grid)
    ensures Reverse(Reverse(grid)) == grid
  {
    assert |Reverse(Reverse(grid))| == N;
    assert |grid| == N;

    forall i | 0 <= i < N
      ensures Reverse(Reverse(grid))[i] == grid[i]
    {
      assert Reverse(grid)[i] == ReverseRow(grid[i]);
      assert Reverse(Reverse(grid))[i] == ReverseRow(Reverse(grid)[i]);
      assert Reverse(Reverse(grid))[i] == ReverseRow(ReverseRow(grid[i]));
      ReverseRowInvolution(grid[i]);
      assert Reverse(Reverse(grid))[i] == grid[i];
    }

    assert Reverse(Reverse(grid)) == grid;
  }

  lemma TransposeInvolution(grid: Grid)
    requires ValidGrid(grid)
    ensures Transpose(Transpose(grid)) == grid
  {
    assert |Transpose(Transpose(grid))| == N;
    assert |grid| == N;

    forall i | 0 <= i < N
      ensures Transpose(Transpose(grid))[i] == grid[i]
    {
      assert |Transpose(Transpose(grid))[i]| == N;
      assert |grid[i]| == N;

      forall j | 0 <= j < N
        ensures Transpose(Transpose(grid))[i][j] == grid[i][j]
      {
        assert Transpose(Transpose(grid))[i][j] == Transpose(grid)[j][i];
        assert Transpose(grid)[j][i] == grid[i][j];
      }

      assert Transpose(Transpose(grid))[i] == grid[i];
    }

    assert Transpose(Transpose(grid)) == grid;
  }
}