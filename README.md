# 2048_dafny_verification
## Overview
This project implements the game 2048 with a graphical interface and formally verified game logic using Dafny.

The game logic (tile movement, merging rules, game state detection, etc.) is specified and verified in Dafny to ensure correctness with respect to the game rules.

A Python GUI built with Tkinter provides an interactive interface for playing the game. And the Python program interacts with Dafny-generated code to guarantee that each move and tile generation satisfies the verified specifications.

## Verified Game Logic
The following components are formally specified and verified in Dafny:

### 1. Grid Validity
Ensures that the board always satisfies:

- Fixed grid size 𝑁×𝑁
- Each tile value is either 0 or a power of two.

### 2. Move Operation
The move operation satisfies:
- All tiles slide as far as possible in the chosen direction.
- Tile relative ordering is preserved.
- The number of non-zero tiles does not change.

### 3. Merge Operation
The merge operation satisfies:
- Only tiles with equal values merge.
- Each tile can merge at most once per move.
- The merged tile has value 2 * original.
- The merge follows the leftmost priority rule.

### 4. Direction Controls
Each directional operation (left, right, up, down) is implemented as: move → merge → move
The correctness of this composition is formally verified.

### 5. Game State Detection
The game state can be:
- Win
- NotOver
- Lose

Verified conditions:
- Win: a tile with value 2048 exists
- NotOver: empty tile or mergeable neighbors exist
- Lose: no moves remain

### 6. Random Tile Generation
After a successful move:
A new tile 2 is generated at a random empty position.
Dafny verifies the correctness of the new board via `initial_grid_validation(grid` and `new_tile_validation(oldGrid, changed, newGrid)`.

## System Requirements
Python 3.9+
Dafny 4.x
TKinter

### Install TKinter (WSL/Linux)
```
sudo apt update
sudo apt install python3-tk
```

## Build Game Logic
### Compile Dafny code
Compile the Dafny logic into Python code:
```
dafny build --target:py logic.dfy
```
This generates the folder:
```
logic-py/
```
which contains the Python bindings used by `game.py`.

### Run the Game
Start the GUI:
```
python3 game.py
```

### Controls
| Key | Action |
|-----|-------|
| ↑ / W / I | Move Up |
| ↓ / S / K | Move Down |
| ← / A / J | Move Left |
| → / D / L | Move Right |
| Esc | Quit |

### Python ↔ Dafny Interaction
The Python GUI interacts with Dafny logic through wrapper functions generated in:
```
logic-py/Logic.py
```
Example:
```
left__wrapper(board)
game__state__wrapper(board)
new__tile__validation__wrapper(old_board, changed, new_board)
```
These wrappers ensure that every board state manipulated by the GUI satisfies the verified Dafny specifications.

## Example Gameplay Flow
```
User presses a key
        ↓
Python GUI calls Dafny directional control
        ↓
Dafny returns (new_board, done)
        ↓
Game state checked (Win / Lose / NotOver)
        ↓
If done:
    Python randomly generates a new tile
        ↓
Dafny validates the new board
        ↓
Game state checked (Win / Lose / NotOver)
```