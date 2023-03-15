# Diddy
Diddy: Python toolbox for analysis of infinite discrete dynamical systems

## Diddy's DSL

Diddy implements a domain-specific language (DSL) for defining an analyzing multidimensional shifts of finite type (SFTs).
The script `diddy.py` can be invoked with the name of a file to be interpreted.

### Commands

The available commands are the following:

* `dim d` sets the dimension to `d`.
* `nodes n1 n2 .. nk` sets the set of nodes mod translations to **{n1,n2,..,nk}**.
* `alphabet a1 a2 .. ap` sets the alphabet to **{a1,a2,..,ap}**
* `topology T` sets the topology of the grid graph to **T**. The built-in topologies are `grid` for the 2D square grid, and `hex` for the 2D hexagonal grid. **T** can also be a custom topology; in this case the next rows define connections between nodes. For example, if dimension is 2 and nodes mod translations are `a` and `b`, one row could be `up (0,0,a) (0,1,b)`, which states that `(x,y,a).up = (x,y+1,b)` for each vector **(x,y)**. `up` can be replaced by any label.
* `SFT name formula` defines an SFT using a first-order formula describing its valid configurations. The syntax of the formulas is described below.
* `SFT name forbs` defins an SFT using a set of forbidden patterns. Each pattern occupies a separate line, and patterns are lists of `node : symbol`. For example, `(0,0,a):0 (1,0,b):1` defines a forbidden pattern of size 2. A formula for the SFT is also computed automatically.
* `compute_forbidden_patterns name` computes a set of forbidden patterns for the SFT previously defined with `name` using a formula.
* `show_formula name` displays the formula defining the SFT `name`.
* `show_forbidden_patterns name` displays the forbidden patterns defining the SFT `name`, if they have been given or computed.
* `contains name1 name2` tests whether the SFT `name1` contains the SFT `name2`. The computation is not guaranteed to halt.
* `equal name1 name2` tests whether the SFTs are equal. The computation is not guaranteed to halt.
* `compare_SFT_pairs` tests all defined pairs of SFTs for containment.
* `compare_SFT_pairs_equality` tests all defined pairs of SFTs for equality.
* `minimum_density name periods` computes the minimum density of the SFT `name` when restricted to the given periods, and displays the periodic configuration attaining the minimum. The SFT must have a set of forbidden patterns.

Most of these commands assume the SFTs are two-dimensional and the alphabet is **{0,1}**.

### First-order formulas

TODO

## SFT

The file `sft.py` contains a class for defining a shift of finite type over a **d**-dimensional gridlike graph.
The set of nodes of the graph is **Z^d × nodes**, and its alphabet is **alph**.
This corresponds to a **Z^d**-SFT whose alphabet is **alph^nodes**.

An SFT can be defined by either a list of forbidden patterns or a first-order formula describing allowed configurations.
In the former case, a formula is automatically computed as well.
SFTs can be compared for equality and containment (though the computation is not guaranteed to halt).

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
