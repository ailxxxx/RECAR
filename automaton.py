"""
Class Automaton.
"""

from transition import Transition
from state import State
from collections import defaultdict

class Automaton:
    """
    Class to store the automaton.
    """

    def __init__(self, initialStateId, clockNum, unobserverNum, observerNum, invariantDict):
        """
        Constructor to initialize the Automaton.
        """
        self.mapState = {}
        self.transitionList = []
        self.nextTransition = []
        self.initialStateId = initialStateId
        self.maxLabel = -1
        self.clockNum = clockNum
        self.unobserverNum = unobserverNum
        self.observerNum = observerNum
        self.invariantDict = invariantDict

        self.faultDiagnoser = []
        self.normalDiagnoser = []

        # Add initial state and transition
        self.addState(-1, 1)
        self.appendTransition(
            -1, -1, 0, ['c' + str(i+1) + ">=0" for i in range(clockNum)], [])

    def __str__(self):
        """
        String representation of the automaton.
        """
        assert(self.initialStateId in self.mapState)
        ret = "Initial State = " + str(self.mapState[self.initialStateId]) + "\n"
        for t in self.transitionList:
            ret += str(t) + "\n"
        return ret

    def appendTransition(self, sourceId, finalId, event, guard, resetList):
        """
        Add a transition to the automaton.
        """
        assert(sourceId in self.mapState)
        assert(finalId in self.mapState)
        self.transitionList.append(Transition(
            self.mapState[sourceId], self.mapState[finalId], event, guard, resetList))

    def insertTransition(self, id, sourceId, finalId, event, guard, resetList):
        """
        Insert a transition at a specific index.
        """
        assert(sourceId in self.mapState)
        assert(finalId in self.mapState)
        self.transitionList.insert(id, Transition(
            self.mapState[sourceId], self.mapState[finalId], event, guard, resetList))

    def getnextTransition(self):
        """
        Getter for next transitions.
        """
        self.nextTransition = [[] for _ in range(len(self.transitionList))]
        for i in range(len(self.transitionList)):
            for j in range(len(self.transitionList)):
                if self.transitionList[i].getFinalState() == self.transitionList[j].getSourceState():
                    self.nextTransition[i].append(j)
        return self.nextTransition

    def getState(self, stateId):
        """
        Getter for state by ID.
        """
        return self.mapState[stateId]

    def addState(self, stateId, invariant):
        """
        Add a new state to the automaton.
        """
        if stateId > self.maxLabel:
            self.maxLabel = stateId
        if stateId not in self.mapState:
            self.mapState[stateId] = State(stateId, invariant)

    def getTransitionAt(self, idx):
        """
        Getter for transition by index.
        """
        assert(0 <= idx < len(self.transitionList))
        return self.transitionList[idx]

    def getNbTransition(self):
        """
        Getter for number of transitions.
        """
        return len(self.transitionList)

    def getTransitionList(self):
        """
        Getter for transition list.
        """
        return self.transitionList

    def getMaxStateLabel(self):
        """
        Getter for maximum state label.
        """
        return self.maxLabel

    def getClockNum(self):
        """
        Getter for number of clocks.
        """
        return self.clockNum

    def getInitialState(self):
        """
        Getter for initial state.
        """
        return self.mapState[self.initialStateId]

    def getUnObservableNum(self):
        """
        Getter for number of unobservable transitions.
        """
        return self.unobserverNum

    def getObservableNum(self):
        """
        Getter for number of observable transitions.
        """
        return self.observerNum

    def getInvariantDict(self):
        """
        Getter for invariant dictionary.
        """
        return self.invariantDict

    def checkEmptylist(self, one_dict):
        """
        Check if there is an empty list in the dictionary.
        """
        for elem in one_dict.keys():
            if one_dict[elem] == []:
                return elem
        return True

    def getFaultDiagnoser(self):
        """
        Getter for fault diagnoser.
        """
        fd = set()  # fault diagnoser
        faultTransitions = [i for i in range(len(self.transitionList)) if self.transitionList[i].getEventId() == 1]

        if faultTransitions:
            nextLevel = faultTransitions.copy()
            new_level = [1]

            while nextLevel and new_level:
                new_level = []
                for item in nextLevel:
                    for transition in self.nextTransition[item]:
                        if transition not in fd:
                            fd.add(transition)
                            nextLevel.append(transition)
                            new_level.append(transition)

            beforeLevel = faultTransitions.copy()
            new_level = [1]
            ffd = set()

            while beforeLevel and new_level:
                new_level = []
                for item in beforeLevel:
                    for i in range(len(self.nextTransition)):
                        if item in self.nextTransition[i]:
                            if i not in ffd:
                                ffd.add(i)
                                beforeLevel.append(i)
                                new_level.append(i)

            fd |= ffd
            fd.update(faultTransitions)

            self.faultDiagnoser = fd

        return self.faultDiagnoser

    def getNormalDiagnoser(self):
        """
        Getter for normal diagnoser.
        """
        nd = set()  # normal diagnoser
        mother = [i for i in range(len(self.transitionList)) if self.transitionList[i].getSourceState() == self.getInitialState() and self.transitionList[i].getEventId() != 1]

        new_level = [1]
        while mother and new_level:
            new_level = []
            for item in mother:
                for node in self.nextTransition[item]:
                    if self.transitionList[node].getEventId() != 1 and node not in nd:
                        nd.add(node)
                        mother.append(node)
                        new_level.append(node)

        nd.update(mother)
        self.normalDiagnoser = nd
        return self.normalDiagnoser 
