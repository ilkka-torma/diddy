from general import *

class Conf:
    "A configuration of some full shift"

    def __init__(self, onesided=None):
        if onesided is None:
            onesided = []
        self.onesided = onesided

    def __getitem__(self, nvec):
        raise Exception("Base configuration class has no methods")

    def display_str(self):
        return "An abstract configuration"

class PeriodicConf(Conf):
    "A fully periodic configuration"

    def __init__(self, pat, onesided=None, minimize=True):
        super().__init__(onesided)
        # pat is a dict from nvecs to symbols
        assert pat
        self.dim = dim = len(min(pat)) - 1
        periods = []
        for i in range(dim):
            min_coord = min(nvec[i] for nvec in pat)
            max_coord = max(nvec[i] for nvec in pat)
            periods.append(max_coord - min_coord + 1)
        self.periods = periods
        self.pat = dict()
        for (nvec, sym) in pat.items():
            self.pat[nvmods(periods, nvec)] = sym
        if minimize:
            for i in range(dim):
                for p in range(1,periods[i]):
                    if periods[i]%p == 0 and all(sym == self[nvadd(nvec, (0,)*i + (p,) + (0,)*(dim-i-1))]
                                                 for (nvec, sym) in self.pat.items()):
                        self.pat = {nvec:sym for (nvec,sym) in self.pat.items()
                                    if nvec[i] < p}
                        self.periods[i] = p
                        break

    def __getitem__(self, nvec):
        if len(nvec) != self.dim+1:
            raise Exception("Cannot index into {}-dimensional configuration with {}-dimensional vector".format(self.dim, len(nvec)-1))
        if any(nvec[i] < 0 for i in self.onesided):
            raise Exception("Negative index of {} in onesided dimension {}".format(nvec, i))
        return self.pat[nvmods(self.periods, nvec)]

    def display_str(self, hide_contents=False):
        s = "fully periodic configuration of periods {}".format(self.periods)
        if not hide_contents:
            s += ":\n{" + ", ".join(["{}: {}".format(nvec, sym) for (nvec, sym) in sorted(self.pat.items())]) + "}"
        return s

class RecognizableConf(Conf):
    "A recognizable configuration"

    def __init__(self, geometry, pat, onesided=None, periodics=None):
        super().__init__(onesided)
        # geometry is a list of triples (negper, transient, posper), pairs (transient, per), or integers that stand for all the parameters
        # it can also be a single tuple, tripe or integer, which is then used for every dimension
        # it will be converted to a list-of-tuples format
        # pat is a dict from nvecs to symbols
        assert pat
        if periodics is None:
            periodics = []
        self.dim = dim = len(min(pat)) - 1
        if type(geometry) != list:
            geometry = [geometry]*dim
        else:
            # make a copy, so it can be safely modified
            geometry = geometry[:]
        self.geometry = geometry
        for i in range(len(geometry)):
            period = geometry[i]
            if type(period) == int:
                if i in self.onesided:
                    geometry[i] = (0, period, period)
                else:
                    geometry[i] = (period, period, period)
            elif type(period) == tuple and len(period) == 2:
                if i in self.onesided:
                    geometry[i] = (0,) + period
                else:
                    geometry[i] = period[-1:] + period
            elif type(period) == tuple and len(period) == 3:
                if i in self.onesided:
                    geometry[i] = (0,) + period[1:]
            else:
                raise Exception("Unknown specifier for recognizable configuration: {}".format(period))
        self.pat = dict()
        for (nvec, sym) in pat.items():
            new_nvecs = [[]]
            for i in range(dim):
                pre, trans, post = self.geometry[i]
                for new_nvec in new_nvecs:
                    if nvec[i] < -pre:
                        new_nvec.append(nvec[i] - (nvec[i]//pre+1)*pre)
                    elif nvec[i] >= trans + post:
                        new_nvec.append(nvec[i] - ((nvec[i]-trans)//post)*post)
                    else:
                        new_nvec.append(nvec[i])
                if i in periodics:
                    new_nvecs = [[a+b for (a,b) in zip(new_nvec, [0]*(i-1) + [c])]
                                 for new_nvec in new_nvecs
                                 for c in ([0, post] if i in self.onesided else [-post, 0, post])]
            for new_nvec in new_nvecs:
                new_nvec.append(nvec[-1])
                self.pat[tuple(new_nvec)] = sym

    def __getitem__(self, nvec):
        new_nvec = []
        for i in range(self.dim):
            if nvec[i] < 0 and i in self.onesided:
                raise Exception("Negative index of {} in onesided dimension {}".format(nvec, i))
            negper, trans, posper = self.geometry[i]
            if nvec[i] < -negper:
                new_nvec.append(nvec[i] - (nvec[i]//negper+1)*negper)
            elif nvec[i] >= trans + posper:
                new_nvec.append(nvec[i] - ((nvec[i]-trans)//posper)*posper)
            else:
                new_nvec.append(nvec[i])
        new_nvec.append(nvec[-1])
        return self.pat[tuple(new_nvec)]

    def display_str(self, hide_contents=False):
        s = "recognizable configuration of periods {}".format(self.geometry)
        if not hide_contents:
            s += ":\n{" + ", ".join(["{}: {}".format(nvec, sym) for (nvec, sym) in sorted(self.pat.items())]) + "}"
        return s
