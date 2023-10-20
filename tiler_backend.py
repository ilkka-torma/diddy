
from general import *
import compiler
import sft
from configuration import *
from enum import Enum

class AxisState(Enum):
    # Don't change markers
    FIXED = 0
    # Change markers to periodic ones
    PERIODIC = 1
    # Change markers to any
    RECOG = 2
    
def replace_sym(conf, nvec, sym, axis_states):
    "Replace the symbol at a single node of the configuration;"
    "return a new configuration and a boolean for changes."
    if conf[nvec] == sym:
        return (False, conf)
        
    new_markers = []
    for (i, marker) in enumerate(conf.markers):
        if axis_states[i] == AxisState.FIXED:
            new_markers.append(marker)
        elif axis_states[i] == AxisState.PERIODIC:
            # markers are necessarily periodic
            (a, b, c, d) = marker
            #assert a == b and c == d <- this failed, I misunderstand something I guess
            if nvec[i] < a:
                new_a = a-((a-nvec[i])//(c-a)+1)*(c-a)
                new_markers.append((new_a,new_a, c,c))
            elif nvec[i] >= c:
                new_c = c+((nvec[i]-c)//(c-a)+1)*(c-a)
                new_markers.append((a,a, new_c,new_c))
            else:
                new_markers.append(marker)
        elif axis_states[i] == AxisState.RECOG:
            # markers can be anything
            (a, b, c, d) = marker
            # first, expand markers
            if a == b:
                if c == d:
                    # fully periodic
                    a, d = a-(c-a), c+(c-a)
                else:
                    a = a-(c-b)
            elif c == d:
                d = c+(c-b)
            if nvec[i] < b:
                new_b = b-((b-nvec[i])//(b-a)+1)*(b-a)
                new_markers.append((new_b-(b-a),new_b, c,d))
            elif nvec[i] >= c:
                new_c = c+((nvec[i]-c)//(d-c)+1)*(d-c)
                new_markers.append((a,b, new_c,new_c+(d-c)))
            else:
                new_markers.append(marker)
                
    new_conf = conf.remark(new_markers)
    new_conf.pat[nvec] = sym
    min_markers = new_conf.minimized_markers()
    new_conf.remark(min_markers)
    return (True, new_conf)

class TilerState:
    """
    A class that maintains an undoable state for tiler.
    It contains the current decorated configuration and selection.
    The nodes of the configuration are decorated with fixedness information.
    """
    
    def __init__(self, conf=None, selection=None, dim=None, nodes=None, sizes=None):
        if conf is None: # sizes used if no initial config
            pat = {vec + (node,) : None for vec in hyperrect([(0,sizes[d]) for d in range(dim)]) for node in nodes}
            conf = RecognizableConf(None, pat, nodes)
        self.conf = conf
        if selection is None:
            selection = set()
        self.selection = selection

def decorate_default(conf):
    "Add default (False) decorations."
    decor_pat = {nvec : (sym, False) for (nvec, sym) in conf.pat.items()}
    return RecognizableConf(conf.markers, decor_pat, conf.nodes, onesided=conf.onesided)
    
def undecorate(conf):
    "Remove decorations."
    print("undecorating", conf.display_str())
    undec_pat = {nvec : tup[0] if tup is not None else None for (nvec, tup) in conf.pat.items()}
    return RecognizableConf(conf.markers, undec_pat, conf.nodes, onesided=conf.onesided)

class TilerBackend:
    """
    A class that maintains the backend for tiler.
    It contains the ambient SFT and settings, the current state, and a history of states.
    """
    
    def __init__(self, sft, init_conf=None, sizes=None):
        self.sft = sft
        if init_conf is not None:
            init_conf = decorate_default(init_conf)
        self.history = [TilerState(conf=init_conf, dim=sft.dim, nodes=sft.nodes, sizes=sizes)]
        self.history_index = 0
        self.axis_states = [AxisState.FIXED]*sft.dim
        self.clipboard = None
        
    def conf(self):
        return self.history[self.history_index].conf
        
    def selection(self):
        return self.history[self.history_index].selection
        
    def undo(self):
        "Rewind into the previous stored state if possible, return a boolean."
        if self.history_index > 0:
            self.history_index -= 1
            return True
        else:
            return False
            
    def redo(self):
        "Advance into the next stored state if possible, return a boolean."
        if self.history_index < len(self.history) - 1:
            self.history_index += 1
            return True
        else:
            return False
            
    def update_state(self, new_state):
        "Update the state, keeping the history that's older than the current state."
        self.history = self.history[:self.history_index+1]
        self.history.append(new_state)
        self.history_index += 1
    
    def replace_conf(self, conf):
        "Replace the configuration with a new one, save the old state."
        self.update_state(TilerState(conf=conf, selection=self.selection(), dim=self.sft.dim, nodes=self.sft.nodes))
        
    def update_selection(self, selection):
        "Replace selection with a new one, save the old state."
        self.update_state(TilerState(conf=self.conf(), selection=selection))
        
    def deduce(self):
        "Deduce the configuration, save the old state."

        #if self.conf().empty(): <- maybe smth like this is a good idea, since this fails with periodic right now.
        #    return
        
        fixed_axes = [i for (i,st) in enumerate(self.axis_states) if st == AxisState.FIXED]
        periodics = [i for (i,st) in enumerate(self.axis_states) if st == AxisState.PERIODIC]
        conf = undecorate(self.conf())
        deduced_conf = self.sft.deduce_global(conf, periodics=periodics, fixed_axes=fixed_axes)
        print("deduced",deduced_conf)
        if deduced_conf is not None:
            print("it's", deduced_conf.display_str())
            decorated_conf = decorate_default(deduced_conf)
            """
            prev_conf = self.conf()
            # previous configuration should be decorated
            for (nvec, tup) in prev_conf.pat.items():
                # fixed cell, copy this information
                if tup and tup[1]:
                    assert nvec in decorated_conf.pat
                    assert decorated_conf.pat[nvec][0] == tup[0]
                    decorated_conf.pat[nvec] = tup
            """
            self.replace_conf(decorated_conf) # TODO: keep fixedness

    def replace_patch(self, pat):
        "Replace patch in configuration, save the old state if changes were made."
        conf = self.conf()
        changed = False
        for (nvec, sym) in pat.items():
            change_now, conf = replace_sym(conf, nvec, sym, self.axis_states)
            changed = changed or change_now
        if changed:
            self.replace_conf(conf)
            
    def copy_selection(self):
        """
        Copy the current selection (translated to origin) to clipboard.
        Also remove the selection and save the state.
        """
        min_vec = [min(nvec[i] for nvec in self.selection())
                   for i in range(self.sft.dim)]
        self.clipboard = {nvsub(nvec, min_vec) : self.conf()[nvec]
                          for nvec in self.selection()}
        update_selection(set())
        
    def paste_clipboard(self, vec):
        "Paste a translated copy of the clipboard, and save the old state if changes were made."
        if self.clipboard is not None:
            replace_patch({nvadd(nvec, vec) : sym for (nvec, sym) in self.clipboard.items()})
            
    def toggle_axis(self, axis, new_state):
        "Toggle the state of an axis."
        self.axis_states[axis] = new_state
        
    def replace_markers(self, axis, new_markers):
        "Replace the markers on a given axis, save the old state."
        conf = self.conf()
        markers = conf.markers[:]
        markers[axis] = new_markers
        new_conf = conf.remark(markers)
        self.replace_conf(new_conf)
        
    def fix_nodes(self, nvecs):
        "Fix the given nodes, save if changes are made."
        pat = dict()
        for nvec in nvecs:
            (sym, _) = self.conf()[nvec]
            pat[nvec] = (sym, True)
        self.replace_patch(pat)
        
    def unfix_all(self):
        "Unfix all nodes, save if changes are made."
        pat = dict()
        for nvec in self.conf().pat:
            (sym, _) = self.conf()[nvec]
            pat[nvec] = (sym, False)
        self.replace_patch(pat)
        
    def clear_all(self):
        "Set all nodes to unknown, save if changes are made."
        pat = dict()
        for nvec in self.conf().pat:
            syms = list(self.sft.alph[nvec[-1]])
            pat[nvec] = (syms, False)
        self.replace_patch(pat)
