/*
1. initialization & state management
*/

//(1) new_game()
// type Grid = seq<seq<int>>

// method new_game(n: nat) returns (matrix: Grid)
// {
// }

//(2) game_state()



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