from general import *

# Markers are used to structure recognizable configurations
# Markers for a single axis can be given as
# a) None (equivalent to (min-1,min,max+1,max+2))
# b) integer n (equivalent to (0,0,n,n))
# c) pair (a,b) (equivalent to (a,a,b,b))
# d) triple (a,b,c) (equivalent to (a,b,b,c)
# e) quadruple (a,b,c,d)
# Each quadruple (a,b,c,d) gives the positions of eventual periodicity markers on its axis
# a=b & c=d means we are periodic
# b=c means we are concatenation of periodic tails

def normalize_markers(i, markers, domain=None):
    "Normalize a marker specification into a quadruple"
    #print("normalizing", i, markers)
    if markers is None: # Here domain should not be None
        minpos = min(nvec[i] for nvec in domain)
        maxpos = max(nvec[i] for nvec in domain)
        return (minpos-1, minpos, maxpos+1, maxpos+2)
    elif type(markers) == int:
        return (0,0, markers,markers)
    elif len(markers) == 2:
        a, b = markers
        return (a,a, b,b)
    elif len(markers) == 3:
        a, b, c = markers
        return (a, b,b, c)
    elif len(markers) == 4:
        return markers
    else:
        raise Exception("Bad marker specification: {}".format(axis))
        
def gen_markers_from_minimal(markers, periodic=None):
    """
    Generate quadruples of markers that are in principle compatible with the given ones (and possibly periodic).
    The input markers are assumed to be minimized.
    """
    # TODO: take into account all apecial cases
    a, b, c, d = markers
    if periodic:
        if (a != b) or (c != d):
            # incompatible with periodic
            return
        k = 0
        while True:
            yield (a, a, a+k*(b-a), a+k*(b-a))
            k += 1
    else:
        left_period = ((k+1)*(b-a) for k in naturals())
        left_border = (b-k for k in naturals())
        right_border = (c+k for k in naturals())
        right_period = ((k+1)*(d-c) for k in naturals())
        for (p1, b1, b2, p2) in iter_prod(left_period, left_border, right_border, right_period):
            #print("generated markers", (b1-p1, b1, b2, b2+p2), "from", markers)
            yield (b1-p1, b1, b2, b2+p2)
    
    

class Conf:
    """
    A recognizable configuration of some full shift,
    possibly with missing and/or indeterminate values.
    A missing value (i.e. node where the local rule is not checked)
    is modeled as a value not in the internal pattern.
    Use "nvec in conf" or catch a KeyError to test for it.
    An indeterminate value is modeled as a list of possible values,
    or None as a shorthand for an unrestricted value.
    """

    def __init__(self, onesided=None):
        if onesided is None:
            onesided = []
        self.onesided = onesided

    def __getitem__(self, nvec):
        raise Exception("Base configuration class has no methods")
        
    def __contains__(self, nvec):
        raise Exception("Base configuration class has no methods")

    def display_str(self):
        return "An abstract configuration"

class RecognizableConf(Conf):
    "A recognizable configuration"

    def __init__(self, markers, pat, onesided=None):
        super().__init__(onesided)
        # markers is a list of (possibly not normalized) markers
        # pat is a dict from nvecs to symbols
        # it will be wrapped around the markers
        if type(markers) == list:
            self.dim = dim = len(markers)
        elif pat:
            self.dim = dim = len(min(pat)) - 1
        else:
            raise Exception("Cannot deduce dimension for configuration")
        
        #print("got markers", markers)
        if type(markers) == tuple and type(markers[0]) == tuple:
            raise Exception("bad marker tuple")
        if type(markers) != list:
            markers = [markers]*dim
        #print("markers are now", markers)
        self.markers = [normalize_markers(i, marker, domain=set(pat))
                        for (i, marker) in enumerate(markers)]
                        
        #print("normalized markers to", self.markers)
        
        self.pat = dict()
        
        for (nvec, sym) in pat.items():
            self.pat[nvwraps(self.markers, nvec)] = sym

    def __getitem__(self, nvec):
        return self.pat[nvwraps(self.markers, nvec)]
        
    def __contains__(self, nvec):
        return nvwraps(self.markers, nvec) in self.pat
        
    def can_be_equal_at(self, *nvecs):
        "Check if values are equal in these nodes; nonexistent nodes are equal."
        #print("equal at", nvecs)
        if any(nvec not in self for nvec in nvecs):
            return all(nvec not in self for nvec in nvecs)
        if not nvecs:
            return True
        return all(self[nvec] == self[nvecs[0]] for nvec in nvecs[1:])
        
    def minimized_markers(self):
        "Move the markers as close to each other as possible and return them."
        # more specifically, first minimize periods of both periodic tails, then rewind right and left tail
        # TODO: handle all special cases
        markers = self.markers[:]
        #print("pattern", self.pat)
        for (i, (a, b, c, d)) in enumerate(markers):
            #print("minimizing marker", (a,b,c,d))
            # if we are periodic, minimize period
            if a==b and c==d:
                p = min(p for p in range(1, c-a+1)
                        if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (p,) + (0,)*(self.dim-i-1)))
                               for nvec in self.pat))
                markers[i] = (a,a, a+p,a+p)
                continue
            # minimize left periodic tail
            for p in range(1, b-a):
                if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (-p,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat
                       if nvec[i] < b):
                    markers[i] = (b-p, b, c, d)
                    break
            (a, b, c, d) = markers[i]
            #print(1, i, markers[i])
            # minimize right periodic tail
            for p in range(1, d-c):
                if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (p,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat
                       if nvec[i] >= c):
                    markers[i] = (a, b, c, p)
                    break
            (a, b, c, d) = markers[i]
            #print(2, i, markers[i])
            # check if everything is periodic
            if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (b-a,) + (0,)*(self.dim-i-1)), nvadd(nvec, (0,)*i + (a-b,) + (0,)*(self.dim-i-1)))
                       for nvec in self.pat):
                markers[i] = (a, a, b, b)
                #print(3, i, markers[i])
                continue
            # rewind right tail
            t = min(t for t in range(b+1, c+1)
                    if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (d-c,) + (0,)*(self.dim-i-1)))
                           for nvec in self.pat
                           if nvec[i] >= t))
            #print("right tail", b+1, c+1, t)
            #print(self.pat)
            # rewind left tail
            s = max(s for s in range(a, b+1)
                    if all(self.can_be_equal_at(nvec, nvadd(nvec, (0,)*i + (a-b,) + (0,)*(self.dim-i-1)))
                           for nvec in self.pat
                           if nvec[i] < s))
            #print("left tail", a, b+1, s)
            markers[i] = (s-b+a, s, t, t+d-c)
            #print(4, i, markers[i])
        #print("minimized to", markers)
        return markers
        
    def remark(self, new_markers):
        """
        Produce a restructured configuration using the new marker structure.
        It's assumed to be compatible with the minimized markers.
        """
        
        nodes = set(nvec[-1] for nvec in self.pat)
        
        new_pat = dict()
        for vec in hyperrect([(a,d) for (a,_,_,d) in new_markers]):
            for node in nodes:
                nvec = vec + (node,)
            try:
                new_pat[nvec] = self[nvec]
            except KeyError:
                pass
        
        return RecognizableConf(new_markers, new_pat, onesided=self.onesided)

    def display_str(self, hide_contents=False):
        s = "recognizable configuration with markers {}".format(self.markers)
        if not hide_contents:
            s += ":\n{" + ", ".join(["{}: {}".format(nvec, sym) for (nvec, sym) in sorted(self.pat.items())]) + "}"
        return s
