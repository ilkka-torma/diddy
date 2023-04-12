#from language3 import *
import math
import compiler
import sft
import pygame
import time
import numpy as np
from numpy.linalg import inv

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

TILING_OK_GRID_COLOR = BLACK
TILING_BAD_GRID_COLOR = (100, 50, 50)
TILING_UNKNOWN_GRID_COLOR = (50,50,50)

# colors used for alphabet symbols, and tinted versions for deduced ones
colors = {0 : WHITE, 1 : GREEN}
deduced_colors = {0 : (150, 150, 150), 1 : (50, 130, 50)}

UNKNOWN_COLOR = YELLOW
EMPTY_COLOR = BLACK # actually we just don't draw these



# number meanings in grid: 0 = not there, 1 = there,
# 2 = unknown, 3 = not there deduced, 4 = there deduced
# None/not in the dict = not part of grid even

TILING_UNKNOWN = 0
TILING_OK = 1
TILING_BAD = 2


def deduce_a_tiling(grid, the_SFT):

    global currentstate
    currentstate = TILING_UNKNOWN

    for g in grid:
        if grid[g] != UNKNOWN and grid[g][0] == DEDUCED:
            grid[g] = UNKNOWN

    known_values = {}
    domain = set()
    for g in grid:
        if grid[g] != UNKNOWN:
            assert grid[g][0] == SET
            val = grid[g][1]
            known_values[g] = val
        domain.add(g[:-1])
    #print("domain", domain)
    #print("known", known_values)
    model = the_SFT.deduce(known_values, domain)
    #print(model)

    if model == None:
        currentstate = TILING_BAD
    else:
        currentstate = TILING_OK

        for d in model:
            if grid[d] == UNKNOWN:
                val = model[d]
                #print("val", val)
                if val != None:
                    grid[d] = (DEDUCED, val)
                else:
                    grid[d] = UNKNOWN

def vadd(u, v):
    return u[0] + v[0], u[1] + v[1]
def vsub(u, v):
    return u[0] - v[0], u[1] - v[1]
def smul(s, u):
    return s*u[0], s*u[1]
def distance(u, v):
    w = vsub(u, v)
    return math.sqrt(w[0]*w[0] + w[1]*w[1])



    

def run(the_SFT, topology, gridmoves, nodeoffsets):
    print(topology)
    print(gridmoves)
    print(nodeoffsets)
    #print("mus")
    global nodes
    nodes = the_SFT.nodes
    dim = the_SFT.dim
    alphabet = the_SFT.alph


    #que = Queue()

    currentstate = TILING_OK

    # This sets the positions of nodes in grid cells.
    # This is done after transformation.
    #nodeoffsets = {0 : (0,0)} #{0 : (0.25, 0.75), 1: (0.75, 0.25)}

    # Shearing and stuff, i.e. what is x & y movement in grid visually
    #gridmoves = [(1, 0), (0, 1)]

    nodesize = 7
     
    # This sets the margin between each cell
    #MARGIN = 3

    #gridheight = 15
    #gridwidth = 15
    
    camera = (0, 0) # where we looking; center of screen is here
    zoom = 20 # how big are cells basically
    screenwidth = 500
    screenheight = 500
     
    # our grid is now just all initial_state
    grid = {}
    r = 10
    for x in range(-r, r+1):
        for y in range(-r, r+1):
            # EMPTY means we'll try to deduce a color here
            for n in nodes:
                grid[(x, y, n)] = UNKNOWN
    grid[(0, 0, 0)] = (SET, 1)
    # print(grid)

    nodepositions = {}
     
    # Initialize pygame
    pygame.init()
     
    # Set the HEIGHT and WIDTH of the screen
    WINDOW_SIZE = [screenwidth, screenheight]
    screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)
     
    # Set title of screen
    pygame.display.set_caption("Tiler")
     
    # Loop until the user clicks the close button.
    done = False
     
    # Used to manage how fast the screen updates
    clock = pygame.time.Clock()

    mouseisdown = False
    drawcolor = None

    thred = None

    def to_screen(x, y):
        return vadd((screenwidth/2, screenheight/2), vadd(smul((x - camera[0])*zoom, gridmoves[0]), smul((y - camera[1])*zoom, gridmoves[1])))
    
    def to_grid(u, v):
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
        x = XY[0]/zoom + camera[0]
        y = XY[1]/zoom + camera[1]
        #return A*st[0] + B*st[1], C*st[0] + D*st[1]
        return x, y

    # given grid coords, find closest node
    def get_node(x, y, vemmelate = False):
        if vemmelate:
            print()
            print("getting")
            print(x, y)
            
        closest = None
        dist = 10000
        rr = 2
        for x0 in range(math.floor(x) - rr, math.floor(x) + rr + 1):
            for y0 in range(math.floor(y) - rr, math.floor(y) + rr + 1):
                for n in range(len(nodes)):
                    d = distance(vadd(to_screen(x0, y0), smul(zoom, nodeoffsets[nodes[n]])), to_screen(x, y))
                    #if vemmelate:
                    #    print(x0, y0, n, vadd(to_screen(x0, y0), smul(zoom,nodeoffsets[nodes[n]]), d, x, y)
                    if d < dist:
                        dist = d
                        closest = (x0, y0, n)
                    if vemmelate:
                        vemmel.add((x0, y0, n))
                        gimmel[(x0, y0, n)] = d
        #if vemmelate:
        #    gimmel[0] = closest
            #print(closest)
        """
        for node in grid:
            nodex, nodey, nodenode = node
            realpos = nodepositions[node]
            #d = distance(to_screen(*vadd((x0, y0), nodeoffsets[n])), to_screen(x, y))
            d = distance(realpos, x, y)
            if d < dist:
                dist = d
                closest = node
        """
        return closest
        
    # print(get_node(0,7))

    nnn = 0
    # -------- Main Program Loop -----------
    while not done:

        nnn += 1

        vemmel = set()
        gimmel = {}
        #print(vemmel)

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
        
        for event in pygame.event.get():  # User did something
            if event.type == pygame.QUIT:  # If user clicked close
                done = True  # Flag that we are done so we exit this loop
            elif event.type == pygame.KEYDOWN:

                if event.key == pygame.K_1:
                    drawcolor = (SET, alphabet[0])
                if event.key == pygame.K_2:
                    drawcolor = (SET, alphabet[1])
                if event.key == pygame.K_9:
                    drawcolor = UNKNOWN # means unused
                if event.key == pygame.K_0:
                    drawcolor = EMPTY
                
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
                    print ("deduction starting")
                    #thred = Process(target=deduce_a_tiling_threaded, args=(que, grid, gridheight, gridwidth))
                    #thred.start()

                    deduce_a_tiling(grid, the_SFT)
                    print ("deduce_a_tiling returned (debug print)")
                    
            elif event.type == pygame.MOUSEBUTTONDOWN:
                mouseisdown = True
                # User clicks the mouse. Get the position
                # Change the x/y screen coordinates to grid coordinates
                #x, y = mouse
                # Set that location to one
                #get_node(
                #drawcolor = 1 - grid[mouserow][mousecolumn]
                #print("Click ", pos, "Grid coordinates: ", row, column)
            elif event.type == pygame.MOUSEBUTTONUP:
                mouseisdown = False
                
            elif event.type == pygame.VIDEORESIZE:
                # There's some code to add back window content here.
                screenwidth, screenheight = event.w, event.h
                WINDOW_SIZE = [screenwidth, screenheight]
                
                screen = pygame.display.set_mode(WINDOW_SIZE, pygame.RESIZABLE)

        keys=pygame.key.get_pressed()
        screenmove = (0, 0)
        if keys[pygame.K_LEFT]:
            screenmove = (-1, 0)
        if keys[pygame.K_RIGHT]:
            screenmove = (1, 0)
        if keys[pygame.K_UP]:
            screenmove = (0, -1)
        if keys[pygame.K_DOWN]:
            screenmove = (0, 1)
            
        #screenmove = smul(zoom*0.01, screenmove)
        screenmove = smul(4, screenmove)
        gridmove = vsub(to_grid(*screenmove), to_grid(0, 0))
        
        camera = vadd(camera, gridmove)
        if keys[pygame.K_a]:
            zoom *= 1.01
        if keys[pygame.K_z]:
            zoom /= 1.01
        if keys[pygame.K_s]:
            nodesize += 1
        if keys[pygame.K_x]:
            nodesize -= 1

        pos = pygame.mouse.get_pos()
        
        pos = to_grid(*pos)
        #print(to_screen(*pos), pos, pygame.mouse.get_pos())
        node = get_node(*pos) #, mouseisdown)
        #if mouseisdown:
        #    assert gimmel[0] != None

        """
        if mousecolumn < 0: mousecolumn = 0
        if mousecolumn >= gridwidth: mousecolumn = gridwidth-1
        if mouserow < 0: mouserow = 0
        if mouserow >= gridheight: mouserow = gridheight-1
        """

        if mouseisdown and drawcolor != None:
            if node not in grid or grid[node] != drawcolor:
                currentstate = TILING_UNKNOWN
                grid[node] = drawcolor
                if drawcolor == EMPTY:
                    del grid[node]
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
                for n in range(len(nodes)):
                    if (x, y, n) not in grid:
                        continue
                    for t in topology:
                        a, b = t[1], t[2]
                        if a[2] == n:
                            xx, yy, nn = vadd((x, y), vsub(b[:-1], a[:-1])) + (b[2],)
                            if (xx, yy, nn) in grid:
                                p = vadd(to_screen(x, y), smul(zoom, nodeoffsets[n]))
                                #pp = to_screen(*vadd((xx, yy), nodeoffsets[nn]))
                                pp = vadd(to_screen(xx, yy), smul(zoom, nodeoffsets[nn]))
                                pygame.draw.line(screen, GRAY, p, pp, 1)


        #print(gimmel, gimmel in vemmel, vemmel)
        # Draw the grid
        for x in range(xmin, xmax + 1):
            for y in range(ymin, ymax + 1):
                for n in range(len(nodes)):
                    p = vadd(to_screen(x, y), smul(zoom, nodeoffsets[n]))
                    if (x,y,n) not in grid:
                        continue
                    else:

                        #if grid[(x,y,n)] != UNKNOWN:
                        #    print (grid[(x,y,n)],  DEDUCED)
                        
                        #print(grid[(x,y,n)] )
                        if grid[(x,y,n)] == UNKNOWN:
                            color = UNKNOWN_COLOR
                        #else:
                        #    print(grid[(x,y,n)], "!=", UNKNOWN)
                        elif grid[(x,y,n)][0] == DEDUCED:
                            sym = alphabet[grid[(x,y,n)][1]]
                            color = deduced_colors[sym]
                        elif grid[(x,y,n)][0] == SET:
                            sym = alphabet[grid[(x,y,n)][1]]
                            #print(sym)
                            color = colors[sym]

                        if (x, y, n) in vemmel:
                            xxxx = int(255- gimmel[(x, y, n)]*3)
                            if xxxx < 0:
                                xxxx = 0
                            color = (0,0,xxxx)
                        #if (x, y, n) == gimmel[0]:
                            #print("did")
                        #    color = (60,70,80)
                        #print(gimmel, nnn) #time.time())
                        
                        pygame.draw.circle(screen, color, p, nodesize)

                    
                    #print(vadd(to_screen(x, y), nodeoffsets[n]))
                    
                    """
                if (x, y,grid[row][column] == 0:
                    color = EMPTY_COLOR
                elif grid[row][column] == 1:
                    color = FULL_COLOR

                elif grid[row][column] == 2 or currentstate != TILING_OK:
                    color = UNKNOWN_COLOR

                elif grid[row][column] == 3:
                    color = DEDUCED_EMPTY_COLOR
                elif grid[row][column] == 4:
                    color = DEDUCED_FULL_COLOR
                    
                pygame.draw.rect(screen,
                                 color,
                                 [(MARGIN + WIDTH) * column + MARGIN,
                                  (MARGIN + HEIGHT) * row + MARGIN,
                                  WIDTH,
                                  HEIGHT])"""
     
        # Limit to 60 frames per second
        clock.tick(60)
     
        # Go ahead and update the screen with what we've drawn.
        pygame.display.flip()
     
    # Be IDLE friendly. If you forget this line, the program will 'hang'
    # on exit.
    pygame.quit()
