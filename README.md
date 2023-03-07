# Diddy
Diddy: Python toolbox for analysis of infinite discrete dynamical systems

## Period automaton

The file `period_automaton.py` contains a class that represents the set of **v**-periodic configurations of a binary 2D shift of finite type on a gridlike graph.
It also contains functions for finding minimum-density configurations in such automata, and a command line interface for accessing them.

### Command line interface

The script takes at least three arguments: a height `h` (which must be positive), a shear `s`, and a computation mode from among `Q` (for quadratic space), `L` (for linear space) and `S` (for `n^(3/2)` space).
Modes `Q` and `S` compute an explicit cycle, mode `L` does not.
It computes the minimum density of a configuration of an SFT (by default, the SFT of identifying codes on the hexagobal grid) with periods `(s,h)` and `(x,0)` over all integers `x > 0`.

Optional arguments affecting the search:
- `-S` can only be used if `h` is even. It "breaks symmetry" by restricting to state sets whose top half and bottom half differ by at most the given number of forbidden sets. Thus, `h=2k -S m` is somewhere between `h=k` and `h=2k`, both in terms of time/memory requirements and the set of codes that are searched through.
- `-K` restricts Karp's algorithm by using a fixed (smaller) value in place of `n`, the number of states. We give no guarantees that the result is indicative of anything.
- `-R` can only be used if  `s` is 0. It prunes the state space by rotating the state set to a lexicographically minimal version after each transition.

Optional technical arguments:
- `-i` reads the automaton from a given file instead of computing it.
- `-o` saves the automaton into a given file after computing it.
- `-a` saves the automaton into an automatically named file after computing it.
- `-r1` controls how often the populating function reports its progress.
- `-r2` controls how often the cycle search function reports its progress.
- `-t` sets the number of threads for the populating and search functions.
- `-c` sets the size of each chunk sent to the populating threads.

### Modifying the SFT

The top part of the file contains the global value `NODES` and the function `forbs_at`.
By changing them, one can analyze different SFTs.
`NODES` is the fundamental domain of the gridlike graph; its vertex set is **Z² × NODES**, and its alphabet is **{0,1}^NODES**.
`forbs_at` takes a vector **(x,y)** and returns the set of forbidden patterns of the SFT translated by **(x,y)**.
The function should commute with translations.

Note that for the density analysis to work correctly, the automaton of **v**-periodic configurations must be strongly connected.
This is not true in general, but is guaranteed if, for example, the forbidden patterns contain no 1-symbols.

In a future update, we plan to implement a more convenient way of representing SFTs, which may be passed to the period automaton as arguments, instead of redefining global variables and functions.
We will also get rid of the requirement of strong connectedness.
