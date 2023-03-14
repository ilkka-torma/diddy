
class SFT:
    "Two-dimensional SFT on a gridlike graph"

    def __init__(self, dim, nodes, alph, forbs):
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        self.forbs = forbs

    def __str__(self):
        return "SFT(dim={}, nodes={}, alph={}, #forbs={})".format(self.dim, self.nodes, self.alph, len(self.forbs))
