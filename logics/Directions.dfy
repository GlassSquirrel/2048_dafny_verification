/********************** 
4. directional controls
***********************/
// The game.py should guarantee that a new tile will be generated, if any of the direction function return done = True
// (7) left()
include "Setups.dfy"
include "Move.dfy"
include "Merge.dfy"
include "Transform.dfy"

module DirectionControls{
    import opened Setups
    import opened Move
    import opened Merge
    import opened Transform

    lemma DoneImpliesResultChanged(
        game: Grid,
        g1: Grid, g2: Grid, g3: Grid,
        d1: bool, d2: bool, d3: bool)
        requires !d1 ==> g1 == game
        requires !d2 ==> g2 == g1
        requires !d3 ==> g3 == g2

        requires d1 ==> g1 != game
        requires d2 ==> g2 != g1
        requires d3 ==> g3 != g2

        // for case 1, 2, 4
        requires CountNonZerosGrid(g1) == CountNonZerosGrid(game)   // move preserves count
        requires d2 ==> CountNonZerosGrid(g2) < CountNonZerosGrid(g1) // merge done decreases count
        requires CountNonZerosGrid(g3) == CountNonZerosGrid(g2)     // move preserves count

        // for case 3
        requires WellPerformedGrid(g1)
        requires WellPerformedGrid(g2) ==> !d3
        
        requires d1 || d2 || d3
        ensures g3 != game
    {
        if g3 == game {
            // 1. move, merge, move
            if d1 && d2 && d3{
                assert g1 != game;
                assert g2 != g1;
                assert g2 != game;
                assert g2 != g3;
                assert g3 != game;
            }
            // 2. no move, merge, move
            if !d1 && d2 && d3{
                assert g1 == game;
                assert g2 != g1;
                assert g2 != game;
                assert g3 != g2;
                assert g3 != game;
            }

            // 3. move，no merge，move
            if d1 && !d2 && d3{ 
                assert g2 == g1;
                assert WellPerformedGrid(g1);
                assert WellPerformedGrid(g2);

                assert !d3;
                assert false;
            }

            // 4. move, merge, no move
            if d1 && d2 && !d3{
                assert g1 != game;
                assert g2!= g1;
                assert g2 != game;
                assert g2 == g3;
                assert g3 != game;
            }
            
            // 5. no move, no merge, move
            if !d1 && !d2 && d3{
                assert g2 == g1;
                assert g1 == game;
                assert g2 == game;
                assert g3 != g2;
                assert false;
            }

            // 6. move, no merge, no move
            if d1 && !d2 && !d3{
                assert !d3 ==> g3 == g2;
                assert !d2 ==> g2 == g1;
                assert g3 == g2;
                assert g2 == g1;
                assert g3 == g1;
                assert g1 == game;
                assert g1 != game;
                assert false;
            }

            // 7. no move, no merge, no move
            if !d1 && d2 && !d3{
                assert !d3 ==> g3 == g2;
                assert !d1 ==> g1 == game;
                assert g3 == g2;
                assert g2 == game;
                assert g1 == game;
                assert g2 == g1;
                assert g2 != g1;
                assert false;
            }

            // 8. last chance:
            assert !d1 && !d2 && !d3;
            assert false;    // contradict requires d1 || d2 || d3
        }
    }

    method left(game: Grid) returns (res: Grid, done: bool)
        requires ValidGrid(game)
        requires ValidValues(game)
        requires !HasWinTile(game)
        requires !IsLose(game)

        ensures ValidGrid(res)
        ensures ValidValues(res)
        ensures done == (res != game)
        ensures done ==> CountNonZerosGrid(res) <= CountNonZerosGrid(game)
        ensures !done ==> res == game
        ensures !IsLose(res)
    {
        // step 1
        var g1, d1 := move(game);
        if !d1 { 
            assert g1 == game; 
        } else {
            assert g1 != game;
        }
        assert CountNonZerosGrid(g1) == CountNonZerosGrid(game);
        assert ValidGrid(g1);
        assert WellPerformedGrid(g1);

        // step 2
        var g2, d2 := merge(g1);
        assert ValidGrid(g2);
        if !d2 { 
            assert g2 == g1;
            assert CountNonZerosGrid(g2) == CountNonZerosGrid(g1);
            assert WellPerformedGrid(g2);
        } else {
            assert g1 != g2;
            assert CountNonZerosGrid(g2) < CountNonZerosGrid(g1);
        }

        // step 3
        var g3, d3 := move(g2);
        assert ValidGrid(g3);
        if WellPerformedGrid(g2) {
        assert !d3;
        }
        assert WellPerformedGrid(g2) ==> !d3;

        if !d3 { 
            assert g3 == g2; 
        } else {
            assert g3 != g2;
        }
        
        assert CountNonZerosGrid(g3) == CountNonZerosGrid(g2);

        res := g3;
        done := d1 || d2 || d3;

        if !done {
            assert d1 == false && d2 == false && d3 == false;
            assert g1 == game;
            assert g2 == g1;
            assert g3 == g2;
            assert res == game;
        }

        if done {
            // proof: g3 <= g2 <= g1 <= game
            assert ValidGrid(g1);
            assert ValidGrid(g2);
            assert WellPerformedGrid(g1);
            assert WellPerformedGrid(g2) ==> !d3;
            assert d1 || d2 || d3;

            DoneImpliesResultChanged(game, g1, g2, g3, d1, d2, d3);
        }
    }


    method right(game: Grid) returns (res: Grid, done: bool)
    requires ValidGrid(game)
    requires ValidValues(game)
    requires !HasWinTile(game)
    requires !IsLose(game)

    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures done == (res != game)
    ensures !done ==> res == game
    ensures !IsLose(res)
{
    // Step 1: reverse the board, so right becomes left
    var r1 := Reverse(game);

    // Prove r1 satisfies left's preconditions
    ReversePreservesValues(game);
    ReversePreservesWin(game);
    ReversePreservesLose(game);

    assert ValidGrid(r1);
    assert ValidValues(r1);
    assert !HasWinTile(r1);
    assert !IsLose(r1);

    // Step 2: reuse verified left
    var g, d := left(r1);

    // Step 3: reverse back
    ReversePreservesValues(g);
    ReversePreservesLose(g);

    var r2 := Reverse(g);

    assert ValidGrid(r2);
    assert ValidValues(r2);
    assert !IsLose(r2);

    res := r2;
    done := d;

    // Needed for proving res == game when nothing changed
    ReverseInvolution(game);
    ReverseInvolution(g);

    if !done {
        // from left's postcondition
        assert g == r1;

        // apply Reverse to both sides
        assert Reverse(g) == Reverse(r1);

        // unfold names
        assert r2 == Reverse(g);
        assert r1 == Reverse(game);

        // reverse twice gives original
        assert Reverse(g) == g ==> false || true; // harmless trigger hint if needed
        assert res == game;
    }

    // prove done == (res != game)
    if res == game {
        assert r2 == game;
        assert Reverse(g) == game;
        assert Reverse(g) == Reverse(Reverse(game));
        assert g == Reverse(game);
        assert g == r1;
        assert !d;
    }

    if res != game {
        assert g != r1;
        assert d;
    }

    assert done == (res != game);
}

method up(game: Grid) returns (res: Grid, done: bool)
    requires ValidGrid(game)
    requires ValidValues(game)
    requires !HasWinTile(game)
    requires !IsLose(game)

    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures done == (res != game)
    ensures !done ==> res == game
    ensures !IsLose(res)
{
    // Step 1: transpose so that up becomes left
    var t1 := Transpose(game);

    // Prove t1 satisfies left's preconditions
    TransposePreservesValues(game);
    TransposePreservesWin(game);
    TransposePreservesLose(game);

    assert ValidGrid(t1);
    assert ValidValues(t1);
    assert !HasWinTile(t1);
    assert !IsLose(t1);

    // Step 2: reuse verified left
    var g, d := left(t1);

    // Step 3: transpose back
    TransposePreservesValues(g);
    TransposePreservesLose(g);

    var t2 := Transpose(g);

    assert ValidGrid(t2);
    assert ValidValues(t2);
    assert !IsLose(t2);

    res := t2;
    done := d;

    // Needed for proving res == game when nothing changed
    TransposeInvolution(game);
    TransposeInvolution(g);

    if !done {
        assert g == t1;
        assert Transpose(g) == Transpose(t1);
        assert res == game;
    }

    if res == game {
        assert t2 == game;
        assert Transpose(g) == game;
        assert Transpose(g) == Transpose(Transpose(game));
        assert g == t1;
        assert !d;
    }

    if res != game {
        assert g != t1;
        assert d;
    }

    assert done == (res != game);
}

method down(game: Grid) returns (res: Grid, done: bool)
    requires ValidGrid(game)
    requires ValidValues(game)
    requires !HasWinTile(game)
    requires !IsLose(game)

    ensures ValidGrid(res)
    ensures ValidValues(res)
    ensures done == (res != game)
    ensures !done ==> res == game
    ensures !IsLose(res)
{
    // Step 1: transpose and reverse so that down becomes left
    var t1 := Transpose(game);
    var r1 := Reverse(t1);

    // Prove t1 satisfies the transformation lemmas
    TransposePreservesValues(game);
    TransposePreservesWin(game);
    TransposePreservesLose(game);

    assert ValidGrid(t1);
    assert ValidValues(t1);
    assert !HasWinTile(t1);
    assert !IsLose(t1);

    // Prove r1 satisfies left's preconditions
    ReversePreservesValues(t1);
    ReversePreservesWin(t1);
    ReversePreservesLose(t1);

    assert ValidGrid(r1);
    assert ValidValues(r1);
    assert !HasWinTile(r1);
    assert !IsLose(r1);

    // Step 2: reuse verified left
    var g, d := left(r1);

    // Step 3: reverse back, then transpose back
    ReversePreservesValues(g);
    ReversePreservesLose(g);

    var r2 := Reverse(g);

    assert ValidGrid(r2);
    assert ValidValues(r2);
    assert !IsLose(r2);

    TransposePreservesValues(r2);
    TransposePreservesLose(r2);

    var t2 := Transpose(r2);

    assert ValidGrid(t2);
    assert ValidValues(t2);
    assert !IsLose(t2);

    res := t2;
    done := d;

    // Needed for proving res == game when nothing changed
    ReverseInvolution(t1);
    ReverseInvolution(g);
    TransposeInvolution(game);
    TransposeInvolution(r2);

    if !done {
        assert g == r1;
        assert Reverse(g) == Reverse(r1);
        assert r2 == t1;
        assert Transpose(r2) == Transpose(t1);
        assert res == game;
    }

    if res == game {
        assert t2 == game;
        assert Transpose(r2) == game;
        assert Transpose(r2) == Transpose(Transpose(game));
        assert r2 == t1;
        assert Reverse(g) == Reverse(r1);
        assert g == r1;
        assert !d;
    }

    if res != game {
        assert g != r1;
        assert d;
    }

    assert done == (res != game);
}
}