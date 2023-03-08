
class SFT:
    "Two-dimensional SFT on a gridlike graph"

    def __init__(self, nodes, alph, forbs):
        self.nodes = nodes
        self.alph = alph
        self.forbs = forbs

    def __str__(self):
        return "SFT(nodes={}, alph={}, #forbs={})".format(self.nodes, self.alph, len(self.forbs))
