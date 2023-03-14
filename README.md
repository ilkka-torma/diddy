# Diddy
Diddy: Python toolbox for analysis of infinite discrete dynamical systems

## SFT

The file `sft.py` contains a thin wrapper class for defining a shift of finite type over a **d**-dimensional gridlike graph.
The set of nodes of the graph is **Z^d × nodes**, and its alphabet is **alph**.
This corresponds to a **Z^d**-SFT whose alphabet is **alph^nodes**.
The forbidden patterns should be given as a list of dictionaries.

## Period automaton

The file `period_automaton.py` contains a class that represents the set of **L**-periodic configurations of a *Z^d* shift of finite type on a gridlike graph, where **L** is a rank-**(d-1)** sublattice of **Z^d**.
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

The bottom part of the file defines the SFT used by the command line interface, which is currently the set of identifying codes on the hexagonal grid.
By changing it, one can analyze different SFTs.
The alphabet should consist of numbers, as they're used directly as weights by the density computation.
