#from language3 import *
import math
import compiler
import sft
import pygame
#import pygame_textinput
import pygame_gui
import time
import numpy as np
from numpy.linalg import inv
import os
import re

"""
nodes = [0]
dim = 2
topology = [("up", (0,0,0), (0,1,0)),
            ("dn", (0,0,0), (0,-1,0)),
            ("rt", (0,0,0), (1,0,0)),
            ("dn", (0,0,0), (-1,0,0))]
alphabet = [0, 1]
# golden mean shift
c = compiler.formula_to_circuit(nodes = nodes, # N = nodes
                       dim = dim, # dimension
                       topology = topology, # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = alphabet,
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

the_SFT = sft.SFT(dim, nodes, alphabet, forbs=None, circuit=c)

"""


#from constraint import *
#from ortools.sat.python import cp_model
#from ortools.constraint_solver import pywrapcp

#import threader
#import threading
#import traceback
#from multiprocessing import Process, Queue

# Define some colors
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
GREEN = (0, 255, 0)
YELLOW = (255, 255, 0)
GRAY = (120, 120, 120)

# UNKNOWN means we deduce the color
# EMPTY
UNKNOWN = "UNKNOWN" # not set by user, should deduce
EMPTY = "EMPTY" # cell is not used -- actually we just erase these from grid but useful for drawcolor
DEDUCED = "DEDUCED" # not set by user, some value has been deduced
SET = "SET" # set by user

TILING_OK_GRID_COLOR = (30,30,30)
TILING_BAD_GRID_COLOR = (100, 50, 50)
TILING_UNKNOWN_GRID_COLOR = (50,50,50)

# colors used for alphabet symbols, and tinted versions for deduced ones
colors = {0 : WHITE, 1 : (255,0,0), 2 : (0,255,0), 3 :(0,0,255),
          4 : (255,255,0), 5 : (255,0,255), 6 : (0,255,255),
          7 : (255, 80, 80), 8 : (80, 255, 80), 9 : (80, 80, 255)}
deduced_colors = {}
for c in colors:
    deduced_colors[c] = tuple(map(lambda a:a//2, colors[c]))

#deduced_colors = {0 : (150, 150, 150), 1 : (50, 130, 50),
#                  2 : (16,56,190), 3: (85, 111, 222),
#                  4: (190, 180, 170)}

UNKNOWN_COLOR = GRAY
EMPTY_COLOR = BLACK # actually we just don't draw these



# number meanings in grid: 0 = not there, 1 = there,
# 2 = unknown, 3 = not there deduced, 4 = there deduced
# None/not in the dict = not part of grid even

TILING_UNKNOWN = 0
TILING_OK = 1
TILING_BAD = 2


def deduce_a_tiling(grid, the_SFT, x_period, y_period):

    global currentstate
    currentstate = TILING_UNKNOWN

    for g in grid:
        if grid[g] != UNKNOWN and grid[g][0] == DEDUCED:
            grid[g] = UNKNOWN

    known_values = {}
    domain = set()
    for g in grid:
        if the_SFT.dim == 1 and g[1] != 0:
            continue
        if grid[g] != UNKNOWN:
            assert grid[g][0] == SET
            try:
                val = the_SFT.alph[g[-1]][grid[g][1]]
            except:
                print(g)
                print(the_SFT.alph)
                print(grid[g])
                a = bbb
            if the_SFT.dim == 1:
                known_values[(g[0], g[-1])] = val
            else:
                #known_values[flipy(g)] = val
                known_values[g] = val
                
            #print("knowing", val, "at", g)
        if the_SFT.dim == 1:
            domain.add((g[0],))
        else:
            #domain.add(flipy(g[:-1]))
            domain.add(g[:-1])
            
    #print("domain", domain)
    #print("known", known_values)        

    #print("deducing model")
    

    model = the_SFT.deduce(known_values, domain, periods=[x_period, y_period])

    #print("model found")

    if model == None:
        currentstate = TILING_BAD
    else:
        currentstate = TILING_OK

        for d in model:
            if the_SFT.dim == 1:
                dd = (d[0], 0, d[-1])
            else:
                dd = d #flipy(d)
            #print(d, "in model", grid[dd])
                
            # grid may not contain all nodes of all cells, but deduction uses all in each cell
            if dd not in grid:
                continue
            if grid[dd] == UNKNOWN:
                val = model[d]
                #print("model maps", d, "to", val)
                
                if val != None:
                    # here b {(0, 0): ['a', 'b', 'c']} (10, 10, (0, 0))
                    #here c {('D', 0): ['a', 'b', 'c'], ('C', 0): [0, 1]} (10, 10, ('C', 0))

                    #print("here", val, the_SFT.alph, d)
                    grid[dd] = (DEDUCED, the_SFT.alph[d[-1]].index(val))
                else:
                    grid[dd] = UNKNOWN
                #print(d, "in model", grid[dd])

def vadd(u, v):
    return u[0] + v[0], u[1] + v[1]
def vsub(u, v):
    return u[0] - v[0], u[1] - v[1]
def smul(s, u):
    return s*u[0], s*u[1]
def vmul(u, v):
    return u[0]*v[0], u[1]*v[1]
def distance(u, v):
    w = vsub(u, v)
    return math.sqrt(w[0]*w[0] + w[1]*w[1])

def flipy(t):
    return (t[0], -t[1]) + t[2:]

# coordinate preprocess to screen
def cp_to_screen(v):
    return v[0], screenheight-v[1]
# coordinate preprocess from screen
def cp_from_screen(v):
    return v[0], screenheight-v[1]

def get_picture(p):
    for typ in ["", ".png", ".jpg", ".gif"]:
        path = p + typ
        if os.path.exists(path):
            return pygame.image.load(path)
    if "_" not in p:
        raise Exception("Image %s does not exist." % p)
    pos = p.rindex("_")
    if p[pos+1] != "r":
        raise Exception("Incorrect image transformation syntax in %s, try filename_r90." % p)
    angle = int(p[pos+2:])
    filename = p[:pos]
    pic = get_picture(filename)
    return pygame.transform.rotate(pic, angle)

"""
# newer pygame should have scale_by
def scale_picture(pic, factor):
    size = pic.get_width(), pic.get_height()
    # consider dest_surface?
    return pygame.transform.scale(pic, (max(1, int(size[0]*factor)), max(1, int(size[1]*factor))))
"""

def ok_file(s):
    return len(s) >= 1 # s[-5:] == ".ptrn" or len(p )

def save(grid, filename):
    if filename[:-5] != ".ptrn":
        filename = filename + ".ptrn"
    with open(filename, "w") as fil:
        for (x, y, n) in grid:
            #print((x,y,n), "was", grid[(x,y,n)])
            # for ease-of-use, we print out an ASCII table
            fil.write("%s: %s\n" % ((x, y, n), grid[(x, y, n)]))

def load(grid, filename):
    if filename[:-5] != ".ptrn":
        filename = filename + ".ptrn"
    for n in list(grid.keys()):
        del grid[n]
    with open(filename, "r") as fil:
        for line in fil:
            a, b = line.split(": ")[:2]
            #print(a, b)

            # for safety, we parse manually
            a = re.match("\((\-?[0-9]+), (\-?[0-9]+), ([\'a-zA-Z0-9_]+)\)", a)
            a = int(a[1]), int(a[2]), a[3]
            
            if a[2][0] == "'":
                a = a[0], a[1], a[2][1:-1]
            else:
                # for some reason our convention with integer nodes is to use python ints
                a = a[0], a[1], int(a[2])
            #print(a)

            if b.strip() == UNKNOWN:
                grid[a] = UNKNOWN
            else:
                b = re.match("\(\'([A-Z]+)\', ([0-9]+)\)", b)
                set_or_ded, idx = b[1], b[2]
                grid[a] = set_or_ded, int(idx)
            #print(b)                
            #print(a, "now", grid[a])


#print(re.match("\((\-?[0-9]+), (\-?[0-9]+), ([\'a-zA-Z0-9_]+)\)", "(29, 9, 'top'))"))

#a = bbb

def run(the_SFT, topology, gridmoves, nodeoffsets, skew=1, x_size=10, y_size=10, x_periodic=False, y_periodic=False, pictures=None):
    #print(topology)

    # check dimension in the first command of topology
    dimension = len(topology[0][1]) - 1
    print("dimension %s" % dimension)
    #print("dimension %s" % dimension)
    # we force topology 2-dimensional
    if dimension == 1:
        #print(topology)
        newtopology = []
        for t in topology:
            print(t)
            newtopology.append((t[0],) + tuple(i[:-1] + (0, i[-1]) for i in t[1:]))
        #print (newtopology)
        topology = newtopology
    elif dimension not in [1, 2]:
        raise Exception("Tiler only supports dimensions 1 and 2, not %s." % dimension)

    #if dimension == 2:
    #y_range = list(range(-r, r+1))
    #else:
    #    dimension_y_range = [0]

    #print(pictures)

    
    
    #print(gridmoves)
    #print(nodeoffsets)
    #print("mus")
    global nodes
    nodes = list(the_SFT.nodes) #list(n for n in the_SFT.nodes)
    runningoffset = 0
    for n in nodes:
        if n not in nodeoffsets:
            # this only makes sense if either all or none are set
            nodeoffsets[n] = (0, runningoffset)
            runningoffset += 1/len(nodes)
    #print("nodes and offsets", nodes, nodeoffsets)
    dim = the_SFT.dim
    alphabets = the_SFT.alph

    #print("alph", alphabets)

    origin = (0,)*dimension + (nodes[0],)

    #que = Queue()

    currentstate = TILING_OK

    # This sets the positions of nodes in grid cells.
    # This is done after transformation.
    #nodeoffsets = {0 : (0,0)} #{0 : (0.25, 0.75), 1: (0.75, 0.25)}

    # Shearing and stuff, i.e. what is x & y movement in grid visually
    #gridmoves = [(1, 0), (0, 1)]

    nodesize = 12
     
    # This sets the margin between each cell
    #MARGIN = 3

    #gridheight = 15
    #gridwidth = 15
    
    camera = (x_size/2, y_size/2) # where we looking; center of screen is here
    zoom = (40, 40*skew) # how big are cells basically
    global screenwidth, screenheight
    screenwidth = 700
    screenheight = 500

    pygame.font.init() 
    my_font = pygame.font.SysFont('Consolas', 30)
    msg_font = pygame.font.SysFont('Consolas', 15)
     
    # our grid is now just all initial_state
    grid = {}
    for x in range(0, x_size):
        for y in range(0, y_size):
            # EMPTY means we'll try to deduce a color here
            for n in nodes: #range(len(nodes)):
                grid[(x, y, n)] = UNKNOWN
    #grid[(0, 0, nodes[0])] = (SET, 1)
    #grid[(1, 0, nodes[0])] = (SET, 1)
    # print(grid)

    nodepositions = {}
     
    # Initialize pygame
    pygame.init()
     
    # Set the HEIGHT and WIDTH of the screen
    WINDOW_SIZE = [screenwidth, screenheight]
    screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)
    manager = pygame_gui.UIManager(WINDOW_SIZE)
     
    # Set title of screen
    pygame.display.set_caption("Tiler")

    if pictures != None:
        pictures = {p : [get_picture(q) for q in pictures[p]] for p in pictures}
      
    # Loop until the user clicks the close button.
    done = False
    
    # Used to manage how fast the screen updates
    clock = pygame.time.Clock()

    mouseisdown = False
    drawcolor = None

    thred = None

    filename_box = pygame_gui.elements.UITextEntryLine(pygame.Rect((10, 160), (100, 50)),
                                                        manager=manager,
                                                        object_id="#filename")
    filename_box.set_text("conf")

    save_button = pygame_gui.elements.UIButton(relative_rect=pygame.Rect((10, 220), (60, 50)),
                                             text='save',
                                             manager=manager)
    load_button = pygame_gui.elements.UIButton(relative_rect=pygame.Rect((70, 220), (60, 50)),
                                             text='load',
                                             manager=manager)

    ui_things = [filename_box, save_button, load_button]

    """
    #manager = pygame_textinput.TextInputManager(validator)
    textinput = pygame_textinput.TextInputVisualizer(font_object = msg_font)
    textinput.cursor_width = 4
    textinput.cursor_blink_interval = 399
    textinput.antialias = True
    textinput.font_color = (10,10,10)
    """
    
    

    def to_screen(x, y):
        if False and dimension == 1:
            return vadd((screenwidth/2, screenheight/2), smul((x - camera[0])*zoom[0], gridmoves[0]))
        else: # dimension == 2:
            return vadd((screenwidth/2, screenheight/2), vadd(smul((x - camera[0])*zoom[0], gridmoves[0]), smul((y - camera[1])*zoom[1], gridmoves[1])))            
    
    def to_grid(u, v):
        if False and dimension == 1:
            # ignore v
            #u = vadd((screenwidth/2, screenheight/2), smul((x - camera[0])*zoom, gridmoves[0]))
            pass
        
        else: # dimension == 2:
            """
            u, v = vadd((screenwidth/2, screenheight/2), vadd(smul((x - camera[0])*zoom, gridmoves[0]), smul((y - camera[1])*zoom, gridmoves[1])))
            vsub((u, v), vadd((screenwidth/2, screenheight/2)) = vadd(smul((x - camera[0])*zoom, gridmoves[0]), smul((y - camera[1])*zoom, gridmoves[1]))
            let (U, V) = vsub((u, v), (screenwidth/2, screenheight/2))
            (X, Y) = (x - camera[0])*zoom, (y - camera[1])*zoom
            of course x = X/zoom + camera[0], y = Y/zoom + camera[1]
            then
            (U, V) = vadd(smul(X, gridmoves[0]), smul(Y, gridmoves[1]))
            so consider matrix with M columns gridmoves[0], gridmoves[1] and column vector XY = (X, Y)
            then (U, V) = M XY
            we should invert this matrix M to get some MI
            then MI (U, V) = X, Y
            """
            a, b = gridmoves[0][0], gridmoves[1][0]
            c, d = gridmoves[0][1], gridmoves[1][1]
            M = np.array([gridmoves[0], gridmoves[1]]).transpose()
            MI = inv(M)
            U, V = vsub((u, v), (screenwidth/2, screenheight/2))
            XY = np.matmul(MI, np.array([[U], [V]])).transpose()
            assert XY.shape == (1, 2)
            XY = XY[0]
            #A, B = d, -b
            #C, D = -c, a
            #st = smul(1/zoom, vsub((u, v), (screenwidth/2, screenheight/2)))
            x = XY[0]/zoom[0] + camera[0]
            y = XY[1]/zoom[1] + camera[1]
            #return A*st[0] + B*st[1], C*st[0] + D*st[1]
            return x, y

    # given grid coords, find closest node
    def get_node(x, y, debug_prints = False):
        if debug_prints:
            print()
            print("getting")
            print(x, y)
            
        closest = None
        dist = 10000
        rr = 2
        for x0 in range(math.floor(x) - rr, math.floor(x) + rr + 1):
            for y0 in list(range(math.floor(y) - rr, math.floor(y) + rr + 1)):
                for n in range(len(nodes)):
                    d = distance(vadd(to_screen(x0, y0), vmul(zoom, nodeoffsets[nodes[n]])), to_screen(x, y))
                    #if debug_prints:
                    #    print(x0, y0, n, vadd(to_screen(x0, y0), smul(zoom,nodeoffsets[nodes[n]]), d, x, y)
                    if d < dist:
                        dist = d
                        closest = (x0, y0, n)
        return closest
        
    # print(get_node(0,7))

    def mouse_on_ui(mpos):
        for u in ui_things:
            r = u.relative_rect
            x, y, w, h = r
            if mpos[0] >= x and mpos[0] < x+w and mpos[1] >= y and mpos[1] < y+h:
                return True
        return False

    nnn = 0

    tim = time.time()
    
    show_help = True
    # -------- Main Program Loop -----------
    while not done:
        #print("main looppo")
        new_tim = time.time()
        time_delta = new_tim - tim
        tim = new_tim
        
        nnn += 1

        #vemmel = set()
        #gimmel = {}

        """
        if not que.empty():
            currentstate = que.get()
            grid = que.get()
            if currentstate == TILING_OK:
                print ("deduction successful")
            if currentstate == TILING_BAD:
                print ("deduction FAILED")
            # thread has ended by protocol
            thred.join()
            thred = None
        """


        events = pygame.event.get()
        #textinput.update(events)

        focus_set = manager.get_focus_set()
        # if UI is used, we should not use mouse or key inputs for other things
        cancel_non_UI = False
        if focus_set == None:
            pass
        else:
            assert len(focus_set) == 1
            focused = list(focus_set)[0]
            # we want some focuses to steal input, let's just use the object type
            if type(focused) == pygame_gui.elements.ui_text_entry_line.UITextEntryLine:
                cancel_non_UI = True # TODO: IGNORE THINGS WHEN TRUE, AND DO SAVES
        
        for event in events:  # User did something

            manager.process_events(event)

            if event.type == pygame_gui.UI_BUTTON_START_PRESS:
                cancel_non_UI = True
                #print("canceling")
                filename = filename_box.get_text()
                if not ok_file(filename):
                    print("Filename %s is not valid; for safety, we require length at least 1." % filename)
                else:
                    if event.ui_element == save_button:
                        save(grid, filename)
                        print('Configuration saved in %s.' % filename)
                    if event.ui_element == load_button:
                        load(grid, filename)
                        print('Configuration loaded from %s.' % filename)
            
            if event.type == pygame.QUIT:  # If user clicked close
                done = True  # Flag that we are done so we exit this loop
                
            elif event.type == pygame.KEYDOWN and not cancel_non_UI:

                if event.key == pygame.K_1:
                    drawcolor = (SET, 0)
                if event.key == pygame.K_2:
                    drawcolor = (SET, 1)
                if event.key == pygame.K_3:
                    drawcolor = (SET, 2)
                if event.key == pygame.K_4:
                    drawcolor = (SET, 3)
                if event.key == pygame.K_5:
                    drawcolor = (SET, 4)
                if event.key == pygame.K_6:
                    drawcolor = (SET, 5)
                if event.key == pygame.K_7:
                    drawcolor = (SET, 6)
                if event.key == pygame.K_8:
                    drawcolor = (SET, 7)
                if event.key == pygame.K_9:
                    drawcolor = (SET, 8)
                if event.key == pygame.K_0:
                    drawcolor = (SET, 9)
                if event.key == pygame.K_u:
                    drawcolor = UNKNOWN # means unused
                if event.key == pygame.K_BACKSPACE:
                    drawcolor = EMPTY
                    
                if event.key == pygame.K_h:
                    show_help = not show_help
                    
                if event.key == pygame.K_e:
                    if event.mod & pygame.KMOD_SHIFT:
                        for (nvec, status) in grid.items():
                            grid[nvec] = UNKNOWN
                    else:
                        for (nvec, status) in grid.items():
                            if status != UNKNOWN and status[0] == DEDUCED:
                                grid[nvec] = UNKNOWN
                
                if event.key == pygame.K_ESCAPE:
                    if thred != None:
                        thred.terminate()
                        thred = None
                        print ("deduction cancelled")
                if event.key == pygame.K_SPACE:
                    if thred != None:
                        thred.terminate()
                        thred = None
                        print ("deduction cancelled")

                    print ("Tiling started.")
                    tim = time.time()
                    #thred = Process(target=deduce_a_tiling_threaded, args=(que, grid, gridheight, gridwidth))
                    #thred.start()

                    deduce_a_tiling(grid, the_SFT, x_period = x_size if x_periodic else None, y_period = y_size if y_periodic else None)

                    print ("Tiling process finished in %s seconds." % (time.time() - tim)) # deduce_a_tiling returned (debug print)")
                    
            elif event.type == pygame.MOUSEBUTTONDOWN:

                # even if using _START_PRESS in _gui, mouse events come one iteration later
                # than in pygame, so we just do an explicit check...
                if not mouse_on_ui(mpos):
                    mouseisdown = True
                    
            elif event.type == pygame.MOUSEBUTTONUP:
                mouseisdown = False
                
            elif event.type == pygame.VIDEORESIZE:
                # There's some code to add back window content here.
                screenwidth, screenheight = event.w, event.h
                WINDOW_SIZE = [screenwidth, screenheight]
                
                screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)
                # should probably also tell UI?
                
            # end of event loop

        mpos = pygame.mouse.get_pos()

        manager.update(time_delta)
            
        keys=pygame.key.get_pressed()
        screenmove = (0, 0)
        if not cancel_non_UI:
            if keys[pygame.K_LEFT]:
                screenmove = (-1, 0)
            if keys[pygame.K_RIGHT]:
                screenmove = (1, 0)
            if keys[pygame.K_UP]:
                screenmove = (0, 1)
            if keys[pygame.K_DOWN]:
                screenmove = (0, -1)
            
        #screenmove = smul(zoom*0.01, screenmove)
        screenmove = smul(4, screenmove)
        gridmove = vsub(to_grid(*screenmove), to_grid(0, 0))
        
        camera = vadd(camera, gridmove)
        if not cancel_non_UI:
            if keys[pygame.K_a]:
                zoom = smul(1.01, zoom)
            if keys[pygame.K_z]:
                zoom = smul(1/1.01, zoom)
            if keys[pygame.K_s]:
                nodesize += 1
            if keys[pygame.K_x]:
                nodesize -= 1

        pos = cp_from_screen(mpos)
        #print(pos)
        pos = to_grid(*pos)
        #print(pos)
        #print(to_screen(*pos), pos, pygame.mouse.get_pos())
        node = get_node(*pos) #, mouseisdown)
        #if mouseisdown:
        #    assert gimmel[0] != None
        #if node != None:
        #    print(node)
        """
        if mousecolumn < 0: mousecolumn = 0
        if mousecolumn >= gridwidth: mousecolumn = gridwidth-1
        if mouserow < 0: mouserow = 0
        if mouserow >= gridheight: mouserow = gridheight-1
        """

        # cases where grid is perhaps clicked
        if node != None and mouseisdown and drawcolor != None and not cancel_non_UI:
            period_ok = True
            if x_periodic:
                if node[0] < 0 or node[0] >= x_size:
                    period_ok = False
            if y_periodic:
                if node[1] < 0 or node[1] >= y_size:
                    period_ok = False
            # cases where we should change
            if period_ok and (node not in grid or grid[node] != drawcolor):
                #print(drawcolor)
                currentstate = TILING_UNKNOWN
                #print(node)
                node = node[:-1] + (nodes[node[-1]],)
                
                if drawcolor == EMPTY:
                    if node in grid:
                        del grid[node]
                elif drawcolor == UNKNOWN:
                    grid[node] = UNKNOWN
                elif drawcolor[0] == SET and drawcolor[1] < len(alphabets[node[-1]]):
                    if node in grid and grid[node] != drawcolor:
                        print("node", node, "set to", alphabets[node[-1]][drawcolor[1]])
                        
                    grid[node] = drawcolor

                
                
                #print(node, drawcolor)
                if thred != None:
                    thred.terminate()
                    thred = None
                    print ("deduction cancelled")

        # screen corners to grid
        xmin, ymin = to_grid(0, 0)
        xmin = math.floor(xmin-5)
        ymin = math.floor(ymin-5)

        xmax, ymax = to_grid(screenwidth, screenheight)
        xmax = math.ceil(xmax+5)
        ymax = math.ceil(ymax+5)
        #print(xmin, ymin, xmax, ymax)
     
        # Set the screen background
        if currentstate == TILING_UNKNOWN:
            screen.fill(TILING_UNKNOWN_GRID_COLOR)
        if currentstate == TILING_OK:
            screen.fill(TILING_OK_GRID_COLOR)
        if currentstate == TILING_BAD:
            #print "pad"
            screen.fill(TILING_BAD_GRID_COLOR)

        # Draw the grid
        for x in range(xmin, xmax + 1):
            for y in range(ymin, ymax + 1):
                if dimension == 1 and y != 0: # we need not draw in this case
                    continue
                for n in range(len(nodes)):
                    
                    if (x, y, nodes[n]) not in grid:
                        continue
                    for t in topology:
                        a, b = t[1], t[2]
                        if a[-1] == nodes[n]:
                            xx, yy, nn = vadd((x, y), vsub(b[:-1], a[:-1])) + (b[2],)
                            if (xx, yy, nn) in grid:
                                p = vadd(to_screen(x, y), vmul(zoom, nodeoffsets[nodes[n]]))
                                #pp = to_screen(*vadd((xx, yy), nodeoffsets[nn]))
                                pp = vadd(to_screen(xx, yy), vmul(zoom, nodeoffsets[nn]))
                                pygame.draw.line(screen, GRAY, cp_to_screen(p), cp_to_screen(pp), 1)
                                


        # Draw the grid
        for x in range(xmin, xmax + 1):
            for y in range(ymin, ymax + 1):
                if dimension == 1 and y != 0:
                    continue
                for n in range(len(nodes)):
                    p = vadd(to_screen(x, y), vmul(zoom, nodeoffsets[nodes[n]]))
                    if (x,y,nodes[n]) not in grid:
                        continue
                    else:

                        sym = None
                        #if grid[(x,y,n)] != UNKNOWN:
                        #    print (grid[(x,y,n)],  DEDUCED)

                        white_circle = False
                        #print(grid[(x,y,n)] )
                        if grid[(x,y,nodes[n])] == UNKNOWN:
                            color = UNKNOWN_COLOR
                        #else:
                        #    print(grid[(x,y,n)], "!=", UNKNOWN)
                        elif grid[(x,y,nodes[n])][0] == DEDUCED:
                            #print(alphabets[nodes[n]])
                            symidx = grid[(x,y,nodes[n])][1]
                            sym = alphabets[nodes[n]][symidx]
                            color = colors[grid[(x,y,nodes[n])][1]] #deduced_colors[sym]
                        elif grid[(x,y,nodes[n])][0] == SET:
                            symidx = grid[(x,y,nodes[n])][1]
                            sym = alphabets[nodes[n]][symidx]
                            #print(sym)
                            color = colors[grid[(x,y,nodes[n])][1]]
                            white_circle = True

                        #if (x, y, n) in vemmel:
                        #    xxxx = int(255- gimmel[(x, y, nodes[n])]*3)
                        #    if xxxx < 0:
                        #        xxxx = 0
                        #    color = (0,0,xxxx)
                        #if (x, y, n) == gimmel[0]:
                            #print("did")
                        #    color = (60,70,80)
                        #print(gimmel, nnn) #time.time())

                        if white_circle:
                            pygame.draw.circle(screen, WHITE, cp_to_screen(p), nodesize+4)
                            pygame.draw.circle(screen, BLACK, cp_to_screen(p), nodesize+2)

                        drawing_picture = False
                        if pictures != None and nodes[n] in pictures:
                            drawing_picture = True

                        if not drawing_picture or True: # actually I like the circles
                            pygame.draw.circle(screen, color, cp_to_screen(p), nodesize)

                        if not drawing_picture and sym != None:
                            #print(sym, color)
                            col = (255, 255, 255)
                            if sum(color) > 250:
                                col = (10, 10, 10)
                            
                            # write name of node, or draw picture
                            if pictures == None or nodes[n] not in pictures:
                                font_surf = my_font.render(str(sym), False, col)
                                v = (font_surf.get_width()//2, -font_surf.get_height()//2)
                                screen.blit(font_surf, cp_to_screen(vsub(p, v)))
                                
                        if sym != None and drawing_picture:
                            pic = pictures[nodes[n]][symidx]
                            pic = pygame.transform.scale(pic, (nodesize*2, nodesize*2))
                            v = (pic.get_width()//2, -pic.get_height()//2)
                            screen.blit(pic, cp_to_screen(vsub(p, v)))

        
                               
        if show_help:                               
            # Draw some helper text
            if type(drawcolor) == tuple and drawcolor[0] == SET:
                draw_msg = ["Drawing symbol {}".format(drawcolor[1])]
            else:
                draw_msg = ["Drawing {}".format(drawcolor)]
            draw_msg.append("Draw: left mouse button")
            draw_msg.append("Select symbol: number keys")
            draw_msg.append("Select unknown symbol: u")
            draw_msg.append("Pan: arrow keys")
            draw_msg.append("Zoom: az")
            draw_msg.append("Node size: sx")
            draw_msg.append("Deduce pattern: spacebar")
            draw_msg.append("Clear deduced nodes: e")
            draw_msg.append("Clear all nodes: shift-e")
            #draw_msg.append("Cancel deduction: escape")
            draw_msg.append("Toggle this text: h")
            for (i, msg) in enumerate(draw_msg):
                font_surf = msg_font.render(msg, False, GREEN)
                screen.blit(font_surf, (10, 10+i*15))
     
        #screen.blit(textinput.surface, (30, 30))
        manager.draw_ui(screen)

        # Limit to 60 frames per second
        clock.tick(60)
     
        # Go ahead and update the screen with what we've drawn.
        pygame.display.flip()
     
    # Be IDLE friendly. If you forget this line, the program will 'hang'
    # on exit.
    pygame.quit()
