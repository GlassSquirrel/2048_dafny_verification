include "Setups.dfy"

module Transform {

  import opened Setups

  //  ----------------reverse-----------------

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



  // 2. Property-preservation lemmas for reverse
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


  lemma EnsuresMoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires MoreToMerge(grid)
    ensures
      (exists i, j :: HorizontalPair(i, j, grid))
      ||
      (exists i, j :: VerticalPair(i, j, grid))
  {
  }

  lemma HorizontalPairReverse(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires HorizontalPair(i, j, grid)
    ensures HorizontalPair(i, N - 2 - j, Reverse(grid))
  {
    assert 0 <= N - 2 - j < N - 1;
    assert Reverse(grid)[i][N - 2 - j] == grid[i][j + 1];
    assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
  }

  lemma VerticalPairReverse(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires VerticalPair(i, j, grid)
    ensures VerticalPair(i, N - 1 - j, Reverse(grid))
  {
    assert 0 <= N - 1 - j < N;
    assert Reverse(grid)[i][N - 1 - j] == grid[i][j];
    assert Reverse(grid)[i + 1][N - 1 - j] == grid[i + 1][j];
  }

  lemma HorizontalPairReverseBack(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires HorizontalPair(i, j, Reverse(grid))
    ensures HorizontalPair(i, N - 2 - j, grid)
  {
    assert 0 <= N - 2 - j < N - 1;
    assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
    assert Reverse(grid)[i][j + 1] == grid[i][N - 2 - j];
  }

  lemma VerticalPairReverseBack(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires VerticalPair(i, j, Reverse(grid))
    ensures VerticalPair(i, N - 1 - j, grid)
  {
    assert 0 <= N - 1 - j < N;
    assert Reverse(grid)[i][j] == grid[i][N - 1 - j];
    assert Reverse(grid)[i + 1][j] == grid[i + 1][N - 1 - j];
  }

lemma NoHorizontalThenVertical(grid: Grid)
  requires ValidGrid(grid)
  requires ValidValues(grid)
  requires MoreToMerge(grid)
  requires !(exists i, j | 0 <= i < N && 0 <= j < N - 1 :: HorizontalPair(i, j, grid))
  ensures exists i, j | 0 <= i < N - 1 && 0 <= j < N :: VerticalPair(i, j, grid)
{
  if !(exists i, j | 0 <= i < N - 1 && 0 <= j < N :: VerticalPair(i, j, grid)) {
    assert !(
      (exists i, j | 0 <= i < N && 0 <= j < N - 1 :: HorizontalPair(i, j, grid))
      ||
      (exists i, j | 0 <= i < N - 1 && 0 <= j < N :: VerticalPair(i, j, grid))
    );
    assert false;
  }
}

lemma ExistsHorizontalPair(grid: Grid) returns (i: int, j: int)
  requires ValidGrid(grid)
  requires ValidValues(grid)
  requires exists i, j | 0 <= i < N && 0 <= j < N - 1 :: HorizontalPair(i, j, grid)
  ensures HorizontalPair(i, j, grid)
{
  var i1, j1 :| HorizontalPair(i1, j1, grid);
  i, j := i1, j1;
}

lemma ExistsVerticalPair(grid: Grid) returns (i: int, j: int)
  requires ValidGrid(grid)
  requires ValidValues(grid)
  requires exists i, j | 0 <= i < N - 1 && 0 <= j < N :: VerticalPair(i, j, grid)
  ensures VerticalPair(i, j, grid)
{
  var i1, j1 :| VerticalPair(i1, j1, grid);
  i, j := i1, j1;
}

  lemma ReversePreservesMoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures MoreToMerge(grid) == MoreToMerge(Reverse(grid))
  {
    // grid -> Reverse(grid)
    if MoreToMerge(grid) {
      EnsuresMoreToMerge(grid);
      if exists i, j :: HorizontalPair(i, j, grid)
      {
        var i, j := ExistsHorizontalPair(grid);
        HorizontalPairReverse(grid, i, j);
        assert exists ii, jj :: HorizontalPair(ii, jj, Reverse(grid));
      } else {
        NoHorizontalThenVertical(grid);
        var i, j := ExistsVerticalPair(grid);
        VerticalPairReverse(grid, i, j);
        assert exists ii, jj :: VerticalPair(ii, jj, Reverse(grid));
      }
    }

    // Reverse(grid) -> grid
    if MoreToMerge(Reverse(grid)) {
      ReversePreservesValues(grid);
      EnsuresMoreToMerge(Reverse(grid));
      if exists i, j :: HorizontalPair(i, j, Reverse(grid))
      {
        var i, j := ExistsHorizontalPair(Reverse(grid));
        HorizontalPairReverseBack(grid, i, j);
        assert exists ii, jj :: HorizontalPair(ii, jj, grid);
      } else {
        NoHorizontalThenVertical(Reverse(grid));
        var i, j := ExistsVerticalPair(Reverse(grid));
        VerticalPairReverseBack(grid, i, j);
        assert exists ii, jj :: VerticalPair(ii, jj, grid);
      }
    }
  }

  // two adjacent tiles with the same value in the same col
  lemma ExistsVerticalMerge(grid: Grid) returns (i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires exists i, j :: twotilesadjacent(i, j, grid)
    ensures VerticalPair(i, j, grid)
  {
    var i1, j1 :| twotilesadjacent(i1, j1, grid);
    i, j := i1, j1;
  }

  predicate twotilesadjacent(i: int, j: int, grid: Grid)
    requires ValidGrid(grid)
  {
    VerticalPair(i, j, grid)
  }

  // two adjacent tiles with the same value in the same row
  predicate twotilesadjacentrow(i: int, j: int, grid: Grid)
    requires ValidGrid(grid)
  {
    HorizontalPair(i, j, grid)
  }

  lemma ExistsHorizontalMerge(grid: Grid) returns (i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires exists i, j :: twotilesadjacentrow(i, j, grid)
    ensures HorizontalPair(i, j, grid)
  {
    var i1, j1 :| twotilesadjacentrow(i1, j1, grid);
    i, j := i1, j1;
  }


  lemma ReversePreservesLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures IsLose(grid) == IsLose(Reverse(grid))
  {
    ReversePreservesWin(grid);
    ReversePreservesEmpty(grid);
    ReversePreservesMoreToMerge(grid);
  }


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


  // -------------------transpose-----------------
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

  lemma TransposeHorizontalPairToVertical(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires HorizontalPair(i, j, grid)
    ensures VerticalPair(j, i, Transpose(grid))
  {
    assert Transpose(grid)[j][i] == grid[i][j];
    assert Transpose(grid)[j + 1][i] == grid[i][j + 1];
  }

  lemma TransposeVerticalPairToHorizontal(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires VerticalPair(i, j, grid)
    ensures HorizontalPair(j, i, Transpose(grid))
  {
    assert Transpose(grid)[j][i] == grid[i][j];
    assert Transpose(grid)[j][i + 1] == grid[i + 1][j];
  }

  lemma TransposeHorizontalPairBack(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires HorizontalPair(i, j, Transpose(grid))
    ensures VerticalPair(j, i, grid)
  {
    assert Transpose(grid)[i][j] == grid[j][i];
    assert Transpose(grid)[i][j + 1] == grid[j + 1][i];
  }

  lemma TransposeVerticalPairBack(grid: Grid, i: int, j: int)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    requires VerticalPair(i, j, Transpose(grid))
    ensures HorizontalPair(j, i, grid)
  {
    assert Transpose(grid)[i][j] == grid[j][i];
    assert Transpose(grid)[i + 1][j] == grid[j][i + 1];
  }

  lemma TransposePreservesMoreToMerge(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
    ensures MoreToMerge(grid) == MoreToMerge(Transpose(grid))
  {
    // grid -> Transpose(grid)
    if MoreToMerge(grid) {
      EnsuresMoreToMerge(grid);
      if exists i, j :: HorizontalPair(i, j, grid) {
        var i, j := ExistsHorizontalPair(grid);
        TransposeHorizontalPairToVertical(grid, i, j);
        assert exists ii, jj :: VerticalPair(ii, jj, Transpose(grid));
      } else {
        NoHorizontalThenVertical(grid);
        var i, j := ExistsVerticalPair(grid);
        TransposeVerticalPairToHorizontal(grid, i, j);
        assert exists ii, jj :: HorizontalPair(ii, jj, Transpose(grid));
      }
    }

    // Transpose(grid) -> grid
    if MoreToMerge(Transpose(grid)) {
      TransposePreservesValues(grid);
      EnsuresMoreToMerge(Transpose(grid));
      if exists i, j :: HorizontalPair(i, j, Transpose(grid)) {
        var i, j := ExistsHorizontalPair(Transpose(grid));
        TransposeHorizontalPairBack(grid, i, j);
        assert exists ii, jj :: VerticalPair(ii, jj, grid);
      } else {
        NoHorizontalThenVertical(Transpose(grid));
        var i, j := ExistsVerticalPair(Transpose(grid));
        TransposeVerticalPairBack(grid, i, j);
        assert exists ii, jj :: HorizontalPair(ii, jj, grid);
      }
    }
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