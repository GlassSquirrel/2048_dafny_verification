/********************** 
4. directional controls
***********************/
// The game.py should guarantee that a new tile will be generated, if any of the direction function return done = True
// (7) left()
include "Setups.dfy"
include "Move.dfy"
include "Merge.dfy"

module DirectionControls{
    import opened Setups
    import opened Move
    import opened Merge

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
}