import os
import sys
# 把logic-py加到sys.path
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.join(BASE_DIR, "logic-py"))

from tkinter import Frame, Label, CENTER
import random
import Logic
import constants as c
import _dafny

# seq <=> list
def dafny_seq_to_list_2d(board):
    return [[int(x) for x in row] for row in board]

def list_2d_to_dafny_seq(board):
    return _dafny.Seq([_dafny.Seq(row) for row in board])

# random generation of tile
def random_empty_position(board):
    empty = [
        (i, j)
        for i in range(c.GRID_LEN)
        for j in range(c.GRID_LEN)
        if board[i][j] == 0
    ]
    if not empty:
        return None
    return random.choice(empty)

def spawn_random_two(board):
    """
    Return a NEW board with exactly one extra 2 placed in a random empty cell.
    Accepts either a Dafny Seq board or a Python 2D list.
    """
    if isinstance(board, list):
        py_board = [row[:] for row in board]
    else:
        py_board = dafny_seq_to_list_2d(board)

    new_board = [row[:] for row in py_board]

    pos = random_empty_position(new_board)
    if pos is None:
        return new_board

    i, j = pos
    new_board[i][j] = 2
    return new_board

class GameGrid(Frame):
    def __init__(self):
        # initialize TKinter GUI
        Frame.__init__(self)

        self.grid()
        self.master.title('2048')
        # input listener
        self.master.bind("<Key>", self.key_down)

        self.commands = {
            # c.KEY_UP: Logic.default__.up__wrapper,
            # c.KEY_DOWN: Logic.default__.down__wrapper,
            c.KEY_LEFT: Logic.default__.left__wrapper,
            # c.KEY_RIGHT: Logic.default__.right__wrapper,
            # c.KEY_UP_ALT1: Logic.default__.up__wrapper,
            # c.KEY_DOWN_ALT1: Logic.default__.down__wrapper,
            c.KEY_LEFT_ALT1: Logic.default__.left__wrapper,
            # c.KEY_RIGHT_ALT1: Logic.default__.right__wrapper,
            # c.KEY_UP_ALT2: Logic.default__.up__wrapper,
            # c.KEY_DOWN_ALT2: Logic.default__.down__wrapper,
            c.KEY_LEFT_ALT2: Logic.default__.left__wrapper,
            # c.KEY_RIGHT_ALT2: Logic.default__.right__wrapper,
        }

        self.grid_cells = []
        self.init_grid()
        
        # initialize the new game board
        self.matrix = Logic.default__.new__game__wrapper()
        py_board = spawn_random_two(self.matrix)
        py_board = spawn_random_two(py_board)
        self.matrix = list_2d_to_dafny_seq(py_board)
        
        # check for new game board validation
        ok = Logic.default__.initial__grid__validation__wrapper(self.matrix)
        if not ok:
            raise ValueError("Initial board failed Dafny validation")
        
        # # for undo
        # self.history_matrixs = [self.matrix]
        
        self.update_grid_cells()
        self.mainloop()

    # initialize the board
    def init_grid(self):
        background = Frame(self, bg=c.BACKGROUND_COLOR_GAME,width=c.SIZE, height=c.SIZE)
        background.grid()

        for i in range(c.GRID_LEN):
            grid_row = []
            for j in range(c.GRID_LEN):
                cell = Frame(
                    background,
                    bg=c.BACKGROUND_COLOR_CELL_EMPTY,
                    width=c.SIZE // c.GRID_LEN,
                    height=c.SIZE // c.GRID_LEN
                )
                cell.grid(
                    row=i,
                    column=j,
                    padx=c.GRID_PADDING,
                    pady=c.GRID_PADDING
                )
                t = Label(
                    master=cell,
                    text="",
                    bg=c.BACKGROUND_COLOR_CELL_EMPTY,
                    justify=CENTER,
                    font=c.FONT,
                    width=5,
                    height=2)
                t.grid()
                grid_row.append(t)
            self.grid_cells.append(grid_row)

    # render color according to the board
    def update_grid_cells(self):
        for i in range(c.GRID_LEN):
            for j in range(c.GRID_LEN):
                new_number = self.matrix[i][j]
                if new_number == 0:
                    self.grid_cells[i][j].configure(text="",bg=c.BACKGROUND_COLOR_CELL_EMPTY, fg=c.CELL_COLOR_DICT[2])
                else:
                    self.grid_cells[i][j].configure(
                        text=str(new_number),
                        bg=c.BACKGROUND_COLOR_DICT.get(new_number, c.BACKGROUND_COLOR_CELL_EMPTY),
                        fg=c.CELL_COLOR_DICT.get(new_number, c.CELL_COLOR_DICT[2])
                    )
        self.update_idletasks()
    
    """
    process:
    1. call directional controls, get (moved_board, done)
    2. if done == False => next input
       if done == True => game_state(moved_board):
                            if Win => win
                            if Lose => lose
                            if NotOver => random generate new tile
    3. if random new tile generated => new_tile_validation(old=moved_board, moved=done, new=spawned_board)
                                       game_state(spawned_board):
                                         if Lose => lose
                                         else next input
    """
    def key_down(self, event):
        key = event.keysym
        print(event)
        if key == c.KEY_QUIT: exit()
        # # for undo
        # if key == c.KEY_BACK and len(self.history_matrixs) > 1:
        #     self.matrix = self.history_matrixs.pop()
        #     self.update_grid_cells()
        #     print('back on step total step:', len(self.history_matrixs))
        if key not in self.commands:
            return 
        
        # 1. call directional controls, get (moved_board, done)
        moved_board, done = self.commands[key](self.matrix)

        # 2. if done == False => next input
        if not done:
            return
        
        # 3. if done == True => game_state(moved_board)
        state_after_move = Logic.default__.game__state__wrapper(moved_board)
        print("state_after_move =", state_after_move)
        state_str = str(state_after_move)
        # if Win => win
        if "Win" in state_str:
            self.matrix = moved_board
            self.update_grid_cells()
            self.grid_cells[1][1].configure(text="You", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            self.grid_cells[1][2].configure(text="Win!", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            return
        # if Lose => lose
        if "Lose" in state_str:
            self.matrix = moved_board
            self.update_grid_cells()
            self.grid_cells[1][1].configure(text="You", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            self.grid_cells[1][2].configure(text="Lose!", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            return
        # if NotOver => random generate new tile
        spawned_board_py = spawn_random_two(moved_board)
        spawned_board = list_2d_to_dafny_seq(spawned_board_py)
        
        # 3. new_tile_validation(old=moved_board, moved=done, new=spawned_board)
        ok = Logic.default__.new__tile__validation__wrapper(moved_board, done, spawned_board)
        if not ok:
            raise ValueError("New tile failed Dafny validation")

        # update new board
        self.matrix = spawned_board
        self.update_grid_cells()

        # game_state(spawned_board)
        final_state = Logic.default__.game__state__wrapper(self.matrix)
        print("final_state =", final_state)
        final_state_str = str(final_state)
        # if Lose => lose
        if "Win" in final_state_str:
            self.grid_cells[1][1].configure(text="You", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            self.grid_cells[1][2].configure(text="Win!", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
        # else: next input
        elif "Lose" in final_state_str:
            self.grid_cells[1][1].configure(text="You", bg=c.BACKGROUND_COLOR_CELL_EMPTY)
            self.grid_cells[1][2].configure(text="Lose!", bg=c.BACKGROUND_COLOR_CELL_EMPTY)

game_grid = GameGrid()