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

// spec 3: after merging, the same state cannot be lose
predicate IsLose(grid: Grid)
    requires ValidGrid(grid)
    requires ValidValues(grid)
{
    !HasWinTile(grid) && !HasEmptyTile(grid) && !MoreToMerge(grid)
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
// 需要满足spec 2, 3, 5
// spec 3: state不改变
// 需要确保dafny知道，新棋盘的元素全部来自旧棋盘
predicate HasWinTileRow(row: seq<int>)
    requires |row| == N
    requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])
{
    exists j :: 0 <= j < |row| && row[j] == 2048
}

lemma NoWinImpliesNoWinRow(mat: Grid, i: int)
    requires ValidGrid(mat) && ValidValues(mat) && !HasWinTile(mat)
    requires 0 <= i < N
    ensures !HasWinTileRow(mat[i])
{}

// 将一行中所有非零的方块拿出来
function FilterNonZeros(s: seq<int>): seq<int>
    ensures |FilterNonZeros(s)| <= |s|
    ensures forall x :: x in FilterNonZeros(s) ==> x in s   // 过滤后所有元素来自原序列
    ensures forall x :: x in FilterNonZeros(s) ==> x != 0   // 过滤后所有元素中不再有0
{
    if |s| == 0 then []
    else if s[0] != 0 then [s[0]] + FilterNonZeros(s[1..])
    else FilterNonZeros(s[1..])
}

lemma FilterLenLemma(s: seq<int>)
    ensures (exists x :: x in s && x == 0) ==> |FilterNonZeros(s)| < |s|
    ensures (forall x :: x in s ==> x != 0) ==> FilterNonZeros(s) == s
{
    if |s| == 0 {
        // 空序列
    } else {
        // 对尾部递归
        FilterLenLemma(s[1..]);

        if forall x :: x in s ==> x != 0 {
            // 推出 s[0] != 0
            assert s[0] in s;
            assert s[0] != 0;

            // 推出尾部也没有 0
            forall x | x in s[1..] 
                ensures x in s
            {
                // 这通常能帮 Dafny 意识到既然 x 在 s 里，那 x 就不是 0
            }
            assert forall x :: x in s[1..] ==> x != 0;

            // 用归纳假设
            assert FilterNonZeros(s[1..]) == s[1..];

            // 展开定义
            assert FilterNonZeros(s) == [s[0]] + s[1..];

            assert [s[0]] + s[1..] == s;
        }

        if exists x :: x in s && x == 0 {
            if s[0] == 0 {
                // 明显长度变小
                assert |FilterNonZeros(s)| == |FilterNonZeros(s[1..])|;
                assert |FilterNonZeros(s[1..])| <= |s[1..]|;
                assert |s[1..]| < |s|;
            } else {
                // 0 在尾部
                assert exists x :: x in s[1..] && x == 0;
                // 用归纳假设
                assert |FilterNonZeros(s[1..])| < |s[1..]|;
                assert |FilterNonZeros(s)| == 1 + |FilterNonZeros(s[1..])|;
                assert |s| == 1 + |s[1..]|;
            }
        }
    }
}

// 处理一行，先过滤掉0，拿出所有非0元素，再用0补齐右侧
// 返回一个bool值告诉我们这行有没有动过
function CompressRow(row: seq<int>): (seq<int>, bool)
    requires |row| == N   // row长度合法
    requires forall j :: 0 <= j < |row| ==> row[j] == 0 || IsPowerOfTwo(row[j])   // row中数值合法

    ensures |CompressRow(row).0| == N   // 输出的行长度依然为 N (Spec 5)
    ensures forall x :: x in CompressRow(row).0 ==> x == 0 || IsPowerOfTwo(x)   // 输出数值合法 (Spec 2)
    ensures forall x :: x in CompressRow(row).0 ==> x == 0 || x in row   // 不会凭空产生新的数
    // ensures CompressRow(row).1 ==> CompressRow(row).0[N-1] == 0   //如果发生了移动，棋盘末尾一定会留下空格
{
    var nonZeros := FilterNonZeros(row);
    // 补齐右侧的 0，使长度重新变为 N
    var padded := nonZeros + seq(N - |nonZeros|, _ => 0);
    (padded, padded != row)
} 

lemma CompressRowCorrectness(row: seq<int>)
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
        
        // 显式连接 res.0 和拼接逻辑
        assert res.0 == nonZeros + zeroFill; 
        assert |nonZeros| < N;
        // 证明 N-1 落在 zeroFill 的范围内
        assert res.0[N-1] == zeroFill[N - 1 - |nonZeros|];
    }
}

method move(mat: Grid) returns (new_mat: Grid, done: bool)
    requires ValidGrid(mat)
    requires ValidValues(mat)
    // spec 3: precondition, not win/lose state
    requires !HasWinTile(mat)
    requires !IsLose(mat)

    // spec 2 & 5
    ensures ValidGrid(new_mat)
    ensures ValidValues(new_mat)
    ensures done == (new_mat != mat)
    //spec 3
    ensures !HasWinTile(new_mat)
    ensures !IsLose(new_mat)
{
    var temp_grid: seq<seq<int>> := [];
    done := false;

    for i := 0 to N 
        invariant 0 <= i <= N 
        invariant |temp_grid| == i
        invariant forall k :: 0 <= k < i ==> |temp_grid[k]| == N
        // 维持合法数值 (Spec 2):
        invariant forall k :: 0 <= k < i ==> 
            forall j :: 0 <= j < N ==> temp_grid[k][j] == 0 || IsPowerOfTwo(temp_grid[k][j])
        // spec 3: no win: no 2048
        invariant forall k :: 0 <= k < i ==> !HasWinTileRow(temp_grid[k])
        // spec 3: no lose: done then there shoud be tile with 0
        invariant !done ==> temp_grid == mat[..i]  // 关联 done 和 mat 的前 i 行，没动说明状态保持，使得最后的assertion hold
        invariant done ==> exists k :: 0 <= k < i && exists j :: 0 <= j < N && temp_grid[k][j] == 0
        invariant done ==> temp_grid != mat[..i]
    {
        // no win row
        NoWinImpliesNoWinRow(mat, i);

        var res := CompressRow(mat[i]);
        var row_res := res.0;
        var row_changed := res.1;
        
        CompressRowCorrectness(mat[i]);
        
        // 1. 引导：Dafny 需要知道 row_res 的元素来源
        assert forall x :: x in row_res ==> x in mat[i] || x == 0;

        // 2. 引导：证明 row_res 的每一项都不可能是 2048
        forall j | 0 <= j < N 
            ensures row_res[j] != 2048
        {
            if row_res[j] == 2048 {
                // 如果是 2048，根据上面的来源断言，它必须在 mat[i] 里
                assert row_res[j] in mat[i]; 
                // 但引理 NoWinImpliesNoWinRow 已经证明了 mat[i] 里没有 2048
                // 这里会产生矛盾，Dafny 从而理解 row_res[j] 绝不可能是 2048
            }
        }
        
        // 3. 现在这个 predicate 就能通过了
        assert !HasWinTileRow(row_res);

        // 只要有一行发生了变动，整个 move 操作的 done 就为 true
        if row_changed {
            done := true;
            assert row_res[N-1] == 0;
        }

        // 将处理完的新行加入临时棋盘
        // 在 temp_grid := temp_grid + [row_res] 之后：
        var old_temp := temp_grid[..i]; // 记录添加新行前的状态
        temp_grid := temp_grid + [row_res];

        if done {
            if row_changed {
                // 情况 A: 这一行刚变，row_res[N-1] 是引理保证的 0
                // 我们直接证明新加的这一行 temp_grid[i] 满足条件
                assert temp_grid[i][N-1] == 0;
            } else {
                // 情况 B: 之前已经有行变了
                // 我们通过一个 forall 语句引导 Dafny 意识到存在性被保持了
                forall k, j | 0 <= k < i && 0 <= j < N && old_temp[k][j] == 0
                    ensures exists r, c :: 0 <= r < i + 1 && 0 <= c < N && temp_grid[r][c] == 0
                {
                    // 只要证明这一个点在 temp_grid 里也是 0 即可
                    assert temp_grid[k][j] == 0; 
                }
            }
        }
    }

    new_mat := temp_grid;

    // --- 最后一步：证明结局状态 ---
    if !done {
        // 没动，状态自然保持
        assert new_mat == mat;
    } else {
        // 动了，根据最后一个 invariant，棋盘里一定有空格
        assert exists r, c :: 0 <= r < N && 0 <= c < N && new_mat[r][c] == 0;
        // 调用你之前写的证明“有空格就不输”的引理
        ImpliesNotLose(new_mat);
    }

    return new_mat, done;
}


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
    // postcondition for once merged, will have empty tile and game state cannot be lose
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

// (7) left()
// method left(game: Grid) returns (res: Grid, done: bool)
//     requires ValidGrid(game)
//     requires ValidValues(game)
//     ensures ValidGrid(res)
//     ensures ValidValues(res)
// {
//     var g1, d1 := move(game);
//     var g2, d2 := merge(g1, d1);
//     var g3, _ := move(g2);
//     res := g3;
//     done := d2;
// }

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