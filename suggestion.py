#!/usr/bin/python3
# -*- coding: utf-8 -*-

from z3 import Solver, Int, Bool, Real, Implies, And, If, Or, Not, sat
from parsert import Parser
from fractions import Fraction
from automaton import Automaton
import re
import time
import sys

class Z3Model:
    NOP = 0
    FAULT = 1
    NO_OBS = 2
    NOP_TRANSITION = 0

    def __init__(self):
        self.s = Solver()
        self.p = Parser()
        self.automaton, self.BOUND, self.DELTA = self.p.parse(sys.argv[1])
        self.initState = 0
        self.nextTransition = []
        self.idxAssum = 0
        self.maxLabelTransition = 0
        self.maxLabelState = 0
        self.observable_map = {}
        self.initialize_z3_variables()
        self.setup_transitions()
        self.create_observable_map(sys.argv[1])
        self.add_initial_constraints()

    def initialize_z3_variables(self):
        self.faultyPath = [Int("fp_1")]
        self.normalPath = [Int("np_1")]
        self.lastlyActiveFaultyPath = [Int("lfp_1")]
        self.lastlyActiveNormalPath = [Int("lnp_1")]
        self.idTransitionFaultyPath = [Int("idt_fp_1")]
        self.idTransitionNormalPath = [Int("idt_np_1")]
        self.nopFaultyPath = [Bool("nop_fp_1")]
        self.nopNormalPath = [Bool("nop_np_1")]
        self.faultOccursByThePast = [Bool("faultOccurs_1")]
        self.checkSynchro = [Bool("check_synchro_1")]
        self.cptFaultOccursByThePast = [Real("cptFaultOccurs_1")]
        self.cptFaultOccursByThePast.append(Real("cptFaultOccurs_2"))

        self.globalClockFaultyPath = [Real("g_fp_1")]
        self.globalClockNormalPath = [Real("g_np_1")]

        self.delayClockFaultyPath = [Real("delay_fp_1")]
        self.delayClockNormalPath = [Real("delay_np_1")]
        self.delayClockFaultyPath.append(Real("delay_fp_2"))
        self.delayClockNormalPath.append(Real("delay_np_2"))

        self.clockConstraintFaultyPath = [Bool("constraint_fp_1")]
        self.clockConstraintNormalPath = [Bool("constraint_np_1")]

        self.clockValueFaultyPath = [
            [Real(f"clock{i+1}_fp_1"), Real(f"clock{i+1}_fp_2")] for i in range(self.automaton.clockNum)]
        self.clockValueNormalPath = [
            [Real(f"clock{i+1}_np_1"), Real(f"clock{i+1}_np_2")] for i in range(self.automaton.clockNum)]

        self.sourceInvFaultyPath = [
            [Bool(f"sourceInv{i+1}_fp_1")] for i in range(self.automaton.clockNum)]
        self.sourceInvNormalPath = [
            [Bool(f"sourceInv{i+1}_np_1")] for i in range(self.automaton.clockNum)]
        self.finalInvFaultyPath = [
            [Bool(f"finalInv{i+1}_fp_1")] for i in range(self.automaton.clockNum)]
        self.finalInvNormalPath = [
            [Bool(f"finalInv{i+1}_np_1")] for i in range(self.automaton.clockNum)]

        self.lengthFaultyPath = [Int("length_fp_1")]
        self.lengthNormalPath = [Int("normal_np_1")]

        self.resetConstraintFaultyPath = [
            [Bool(f"reset{i+1}_fp_1")] for i in range(self.automaton.clockNum)]
        self.resetConstraintNormalPath = [
            [Bool(f"reset{i+1}_np_1")] for i in range(self.automaton.clockNum)]

        self.bound = Int("bound")
        self.delta = Real("delta")

    def setup_transitions(self):
        self.nextTransition = [[self.NOP_TRANSITION] for _ in range(self.automaton.getNbTransition())]

        self.maxLabelState = self.automaton.getMaxStateLabel()

        transitionList = self.automaton.getTransitionList()

        for i in range(self.automaton.getNbTransition()):
            for j in range(self.automaton.getNbTransition()):
                if transitionList[i].getFinalState() == transitionList[j].getSourceState():
                    self.nextTransition[i].append(j)

        self.maxLabelState += 1

        self.automaton.addState(self.maxLabelState, 1)
        self.automaton.appendTransition(self.maxLabelState, self.initState, 2, [
            f'c{i+1}=0' for i in range(self.automaton.clockNum)], list(range(self.automaton.clockNum)))

        self.nextTransition.append([self.NOP_TRANSITION])
        self.nextTransition[-1] += [idx for idx in range(
            self.automaton.getNbTransition()) if transitionList[idx].getSourceState() == self.automaton.getInitialState()]

        self.labelTransition = [Int(f"statusTransition_{i+1}")
                                for i in range(self.automaton.getNbTransition())]

        self.resetTransition = [
            [False for _ in range(self.automaton.getNbTransition())] for _ in range(self.automaton.clockNum)]
        for i in range(self.automaton.getNbTransition()):
            for c in self.automaton.getTransitionAt(i).getResetList():
                self.resetTransition[c][i] = True

        self.clockTransition = [t.getGuard() for t in self.automaton.getTransitionList()]

        for t in self.automaton.getTransitionList():
            if t.getEventId() > self.maxLabelTransition:
                self.maxLabelTransition = t.getEventId()

    def create_observable_map(self, input_file):
        with open(input_file, 'r') as file:
            lines = file.readlines()
            for i, line in enumerate(lines):
                if not line.startswith("Initial_state") and not line.startswith("invariant:"):
                    self.observable_map[f"isObservable_{i+1}"] = line.strip()

    def add_initial_constraints(self):
        self.s.add(self.labelTransition[0] == 0)
        self.s.add(And([And(x >= 0, x <= self.maxLabelTransition)
                   for x in self.labelTransition]))
        self.s.add(self.faultyPath[0] == self.automaton.getNbTransition() - 1)
        self.s.add(self.normalPath[0] == self.automaton.getNbTransition() - 1)
        self.s.add(self.faultyPath[0] == self.lastlyActiveFaultyPath[0])
        self.s.add(self.normalPath[0] == self.lastlyActiveNormalPath[0])

        for i in range(self.automaton.clockNum):
            self.s.add(self.clockValueFaultyPath[i][0] == 0)
            self.s.add(self.clockValueNormalPath[i][0] == 0)

        self.s.add(self.globalClockFaultyPath[0] == 0)
        self.s.add(self.globalClockNormalPath[0] == 0)

        self.s.add(self.idTransitionNormalPath[0] != self.FAULT)
        self.s.add(self.nopFaultyPath[0] == False)
        self.s.add(self.nopNormalPath[0] == False)

        self.s.add(self.faultOccursByThePast[0] == (self.idTransitionFaultyPath[0] == self.FAULT))
        self.s.add(self.cptFaultOccursByThePast[0] == 0)
        self.s.add(self.bound >= 0)
        self.s.add(self.delta >= 0)

        self.s.add(self.delayClockFaultyPath[0] == 0)
        self.s.add(self.delayClockNormalPath[0] == 0)

        self.s.add(self.lengthNormalPath[0] == 0)
        self.s.add(self.lengthFaultyPath[0] == 0)

        self.isObservableTransition = [Bool(
            f"isObservable_{i + 1}") for i in range(self.automaton.getNbTransition())]
        self.addConstraintOnIdTransition(0)

    def addConstraintOnIdTransition(self, pos):
        for j in range(self.automaton.getNbTransition()):
            self.s.add(Implies(
                self.faultyPath[pos] == j, self.idTransitionFaultyPath[pos] == self.labelTransition[j]))
            self.s.add(Implies(self.faultyPath[pos] == j, self.clockConstraintFaultyPath[pos] == And(
                self.transConstraints(self.parseConstraints(self.clockTransition[j]), pos, 'f'))))
            self.s.add(Implies(
                self.normalPath[pos] == j, self.idTransitionNormalPath[pos] == self.labelTransition[j]))
            self.s.add(Implies(self.normalPath[pos] == j, self.clockConstraintNormalPath[pos] == And(
                self.transConstraints(self.parseConstraints(self.clockTransition[j]), pos, 'n'))))

            for i in range(self.automaton.clockNum):
                self.s.add(Implies(
                    self.faultyPath[pos] == j, self.resetConstraintFaultyPath[i][pos] == self.resetTransition[i][j]))
                self.s.add(Implies(
                    self.normalPath[pos] == j, self.resetConstraintNormalPath[i][pos] == self.resetTransition[i][j]))

                transition = self.automaton.getTransitionAt(j)
                sourceState = transition.getSourceState()
                finalState = transition.getFinalState()

                self.s.add(Implies(self.faultyPath[pos] == j, self.sourceInvFaultyPath[i][pos] == And(
                    self.parseInv(sourceState.getInvariant(), i, pos, 'f'))))
                self.s.add(Implies(self.faultyPath[pos] == j, self.finalInvFaultyPath[i][pos] == And(
                    self.parseInv(finalState.getInvariant(), i, pos+1, 'f'))))

                self.s.add(Implies(self.normalPath[pos] == j, self.sourceInvNormalPath[i][pos] == And(
                    self.parseInv(sourceState.getInvariant(), i, pos, 'n'))))
                self.s.add(Implies(self.normalPath[pos] == j, self.finalInvNormalPath[i][pos] == And(
                    self.parseInv(finalState.getInvariant(), i, pos+1, 'n'))))

        self.s.add(self.clockConstraintFaultyPath[pos] == True)
        self.s.add(self.clockConstraintNormalPath[pos] == True)

        for j in range(self.automaton.clockNum):
            self.s.add(Implies(self.resetConstraintFaultyPath[j][pos] == True,
                               self.clockValueFaultyPath[j][pos + 1] == 0 + self.delayClockFaultyPath[pos+1]))
            self.s.add(Implies(self.resetConstraintFaultyPath[j][pos] == False,
                               self.clockValueFaultyPath[j][pos + 1] == self.clockValueFaultyPath[j][pos] + self.delayClockFaultyPath[pos+1]))

            self.s.add(Implies(self.resetConstraintNormalPath[j][pos] == True,
                               self.clockValueNormalPath[j][pos+1] == 0 + self.delayClockNormalPath[pos+1]))
            self.s.add(Implies(self.resetConstraintNormalPath[j][pos] == False,
                               self.clockValueNormalPath[j][pos + 1] == self.clockValueNormalPath[j][pos] + self.delayClockNormalPath[pos+1]))

            self.s.add(And(self.sourceInvFaultyPath[j][pos] == True, self.finalInvFaultyPath[j][pos] == True))
            self.s.add(And(self.sourceInvNormalPath[j][pos] == True, self.finalInvNormalPath[j][pos] == True))

        self.s.add(self.delayClockFaultyPath[pos] >= 0)
        self.s.add(self.delayClockNormalPath[pos] >= 0)
        self.s.add(self.delayClockNormalPath[pos+1] >= 0)
        self.s.add(self.delayClockFaultyPath[pos+1] >= 0)

        self.s.add(
            self.globalClockFaultyPath[pos] == self.globalClockFaultyPath[pos-1] + self.delayClockFaultyPath[pos])
        self.s.add(
            self.globalClockNormalPath[pos] == self.globalClockNormalPath[pos-1] + self.delayClockNormalPath[pos])

        self.s.add(
            Implies(self.faultyPath[pos] == 0, self.delayClockFaultyPath[pos+1] == 0))
        self.s.add(
            Implies(self.normalPath[pos] == 0, self.delayClockNormalPath[pos+1] == 0))

        if pos >= 1:
            self.s.add(If(self.faultyPath[pos] == 0, 
                          self.lengthFaultyPath[pos] == self.lengthFaultyPath[pos-1], 
                          self.lengthFaultyPath[pos] == self.lengthFaultyPath[pos-1] + 1))
            self.s.add(If(self.normalPath[pos] == 0, 
                          self.lengthNormalPath[pos] == self.lengthNormalPath[pos-1], 
                          self.lengthNormalPath[pos] == self.lengthNormalPath[pos-1] + 1))

        self.s.add(And(Or(self.idTransitionFaultyPath[pos] > self.NO_OBS,
                          self.idTransitionNormalPath[pos] > self.NO_OBS), self.isObservableTransition[pos]) == self.checkSynchro[pos])
        self.s.add(Or(Not(self.checkSynchro[pos]), And(self.idTransitionFaultyPath[pos] ==
                                                       self.idTransitionNormalPath[pos], self.globalClockFaultyPath[pos] == self.globalClockNormalPath[pos])))

    def incVariableList(self):
        idx = len(self.faultyPath) + 1
        self.faultyPath.append(Int("fp_" + str(idx)))
        self.normalPath.append(Int("np_" + str(idx)))
        self.lastlyActiveFaultyPath.append(Int("lfp_" + str(idx)))
        self.lastlyActiveNormalPath.append(Int("lnp_" + str(idx)))
        self.idTransitionFaultyPath.append(Int("idt_fp_" + str(idx)))
        self.idTransitionNormalPath.append(Int("idt_np_" + str(idx)))
        self.nopFaultyPath.append(Bool("nop_fp_" + str(idx)))
        self.faultOccursByThePast.append(Bool("faultOccurs_" + str(idx)))
        self.nopNormalPath.append(Bool("nop_np_" + str(idx)))
        self.checkSynchro.append(Bool("checkSynchro_" + str(idx)))

        self.globalClockFaultyPath.append(Real("g_fp_" + str(idx)))
        self.globalClockNormalPath.append(Real("g_np_" + str(idx)))

        self.delayClockFaultyPath.append(Real("delay_fp_" + str(idx+1)))
        self.delayClockNormalPath.append(Real("delay_np_" + str(idx+1)))

        self.clockConstraintFaultyPath.append(
            Bool("constraint_fp_" + str(idx)))
        self.clockConstraintNormalPath.append(
            Bool("constraint_np_" + str(idx)))

        self.cptFaultOccursByThePast.append(
            Real("cptFaultOccurs_" + str(idx+1)))

        self.lengthFaultyPath.append(Int("length_fp_" + str(idx)))
        self.lengthNormalPath.append(Int("length_np_" + str(idx)))

        for i in range(self.automaton.clockNum):
            self.clockValueFaultyPath[i].append(
                Real("clock" + str(i + 1) + "_fp_" + str(idx+1)))
            self.clockValueNormalPath[i].append(
                Real("clock" + str(i + 1) + "_np_" + str(idx+1)))

            self.resetConstraintFaultyPath[i].append(
                Int("reset" + str(i + 1) + "_fp_" + str(idx)))
            self.resetConstraintNormalPath[i].append(
                Int("reset" + str(i + 1) + "_np_" + str(idx)))

            self.sourceInvFaultyPath[i].append(
                Bool("sourceInv" + str(i + 1) + "_fp_" + str(idx)))
            self.finalInvFaultyPath[i].append(
                Bool("finalInv" + str(i + 1) + "_fp_" + str(idx)))

            self.sourceInvNormalPath[i].append(
                Bool("sourceInv" + str(i + 1) + "_np_" + str(idx)))
            self.finalInvNormalPath[i].append(
                Bool("finalInv" + str(i + 1) + "_np_" + str(idx)))

    def incBound(self):
        idx = len(self.faultyPath)
        assert(idx > 0)

        self.incVariableList()

        self.s.add(self.faultyPath[idx] <= self.automaton.getNbTransition())
        self.s.add(self.normalPath[idx] <= self.automaton.getNbTransition())

        self.s.add(self.idTransitionFaultyPath[idx] <= self.maxLabelTransition)
        self.s.add(self.idTransitionNormalPath[idx] <= self.maxLabelTransition)

        self.s.add(Implies(self.faultyPath[idx] == self.NOP_TRANSITION,
                   self.lastlyActiveFaultyPath[idx] == self.lastlyActiveFaultyPath[idx-1]))
        self.s.add(Implies(self.faultyPath[idx] != self.NOP_TRANSITION,
                   self.lastlyActiveFaultyPath[idx] == self.faultyPath[idx]))
        self.s.add(Implies(self.normalPath[idx] == self.NOP_TRANSITION,
                   self.lastlyActiveNormalPath[idx] == self.lastlyActiveNormalPath[idx-1]))
        self.s.add(Implies(self.normalPath[idx] != self.NOP_TRANSITION,
                   self.lastlyActiveNormalPath[idx] == self.normalPath[idx]))

        for j in range(self.automaton.getNbTransition()):
            self.s.add(Implies(self.lastlyActiveFaultyPath[idx-1] == j, Or(
                [self.faultyPath[idx] == n for n in self.nextTransition[j]])))
            self.s.add(Implies(self.lastlyActiveNormalPath[idx-1] == j, Or(
                [self.normalPath[idx] == n for n in self.nextTransition[j]])))

        self.s.add(self.idTransitionNormalPath[idx] != self.FAULT)

        self.s.add(self.delayClockFaultyPath[idx] >= 0)
        self.s.add(self.delayClockNormalPath[idx] >= 0)

        self.addConstraintOnIdTransition(idx)

        self.s.add(self.nopFaultyPath[idx] == (
            self.faultyPath[idx] == self.NOP_TRANSITION))
        self.s.add(self.nopNormalPath[idx] == (
            self.normalPath[idx] == self.NOP_TRANSITION))

        self.s.add(
            Or(Not(self.nopFaultyPath[idx]), Not(self.nopNormalPath[idx])))

        self.s.add(Implies(self.nopFaultyPath[idx-1], Or(
            self.nopFaultyPath[idx], self.idTransitionFaultyPath[idx] > self.NO_OBS)))
        self.s.add(Implies(self.nopNormalPath[idx-1], Or(
            self.nopNormalPath[idx], self.idTransitionNormalPath[idx] > self.NO_OBS)))

        self.s.add(Or(self.faultOccursByThePast[idx-1], self.idTransitionFaultyPath[idx]
                   == self.FAULT) == self.faultOccursByThePast[idx])

        self.s.add(Implies(
            self.faultOccursByThePast[idx-1] == False, self.cptFaultOccursByThePast[idx] == 0))

        self.s.add(Implies(
            self.faultOccursByThePast[idx] == False, self.cptFaultOccursByThePast[idx+1] == 0))
        self.s.add(Implies(self.faultOccursByThePast[idx] == True, self.cptFaultOccursByThePast[idx+1]
                   == self.cptFaultOccursByThePast[idx] + self.delayClockFaultyPath[idx+1]))

    def printAutomatonInfo(self):
        print("Information ...")
        print("automata:")
        print(self.automaton)
        print("next transition:")
        for i in range(len(self.nextTransition)):
            print(i, ':', self.nextTransition[i])
        print("BOUND:", self.BOUND)
        print("DELTA:", self.DELTA)
        print("delta:", self.delta)

    def printZ3Constraints(self):
        print(self.s)

    def checkModel(self, model):
        bound = int(model.evaluate(self.bound).as_long())
        previous = None
        for i in range(len(self.faultyPath)):
            v = int(model.evaluate(self.faultyPath[i]).as_long())
            if i > 0:
                lv = int(model.evaluate(
                    self.lastlyActiveFaultyPath[i-1]).as_long())
            id = int(model.evaluate(self.idTransitionFaultyPath[i]).as_long())
            nop = model.evaluate(self.nopFaultyPath[i])
            assert(id == 0 or self.automaton.getTransitionAt(
                v).getFinalState().getId() == id)
            assert(nop or v != 0)
            if previous is not None:
                assert(
                    nop or self.automaton.getTransitionAt(previous).getFinalState() == self.automaton.getTransitionAt(v).getSourceState())
                print(lv, previous)
                assert(lv == previous)
            if not nop:
                previous = v

        previous = None
        for i in range(len(self.normalPath)):
            v = int(model.evaluate(self.normalPath[i]).as_long())
            if i > 0:
                lv = int(model.evaluate(
                    self.lastlyActiveNormalPath[i-1]).as_long())
            id = int(model.evaluate(self.idTransitionNormalPath[i]).as_long())
            nop = model.evaluate(self.nopNormalPath[i])
            assert(id == 0 or self.automaton.getTransitionAt(
                v).getFinalState().getId() == id)
            assert(nop or v != 0)
            if previous is not None:
                assert(
                    nop or self.automaton.getTransitionAt(previous).getFinalState() == self.automaton.getTransitionAt(v).getSourceState())
                assert(lv == previous)
            if not nop:
                previous = v

    def printOneIntArray(self, model, array):
        for x in array:
            print('{:-6}'.format(int(model.evaluate(x).as_long())), end=" ")
        print()

    def printOneRealArray(self, model, array, cpt):
        print([model[array[i]] for i in range(cpt)])

    def printOneBoolArray(self, model, array):
        for x in array:
            r = model.evaluate(x)
            id = 0
            if r:
                id = 1
            print('{:-6}'.format(id), end=" ")
        print()

    def printModel(self, model, cpt):
        print("--------------------")
        print("z3 arrays (size = " + str(len(self.faultyPath)) + ")")
        print("--------------------")
        print("faultyPath: ")
        self.printOneIntArray(model, self.faultyPath)
        print("normalPath: ")
        self.printOneIntArray(model, self.normalPath)
        print("lastlyActiveFaultyPath")
        self.printOneIntArray(model, self.lastlyActiveFaultyPath)
        print("lastlyActiveNormalPath")
        self.printOneIntArray(model, self.lastlyActiveNormalPath)
        print("idTransitionFaultyPath: ")
        self.printOneIntArray(model, self.idTransitionFaultyPath)
        print("idTransitionNormalPath: ")
        self.printOneIntArray(model, self.idTransitionNormalPath)
        print("cptFaultOccursByThePast: ")
        print("nopFaultyPath:")
        self.printOneBoolArray(model, self.nopFaultyPath)
        print("nopNormalPath: ")
        self.printOneBoolArray(model, self.nopNormalPath)
        print("faultOccursByThePast: ")
        self.printOneBoolArray(model, self.faultOccursByThePast)
        print("checkSynchro")
        self.printOneBoolArray(model, self.checkSynchro)
        print("labelTransition")
        self.printOneIntArray(model, self.labelTransition)
        print("globalClockFaultyPath")
        self.printOneRealArray(model, self.globalClockFaultyPath, cpt)
        print("globalClockNormalPath")
        self.printOneRealArray(model, self.globalClockNormalPath, cpt)
        print("delta")
        self.printOneRealArray(model, self.cptFaultOccursByThePast, cpt+1)
        print("delayNP")
        self.printOneRealArray(model, self.delayClockNormalPath, cpt+1)
        print("delayFP")
        self.printOneRealArray(model, self.delayClockFaultyPath, cpt+1)
        print()

    def parseConstraints(self, constraint_original):
        parsed_constraints = []
        constraints = constraint_original.copy()
        while constraints:
            constraint = constraints.pop(0)
            clock_num = constraint.split("c")[1].split(">")[0]
            clock = 'c' + clock_num
            parts = constraint.split(clock)
            for part in parts:
                if part:
                    if part[0] == ">":
                        item = clock + part
                    else:
                        item = part + clock
                    parsed_constraints.append(item)
        return parsed_constraints

    def transConstraints(self, constraint_single, idx, path_type):
        clocklist = ["c" + str(i + 1) for i in range(self.automaton.clockNum)]
        constraints = []
        for constraint in constraint_single:
            parts = constraint.split("=")
            flag = 0
            if parts[0][0] == "c":
                if len(parts) == 1:
                    flag = 1
                    number = parts[0].split(">")[1]
                else:
                    flag = 2
                    number = parts[1]
                clock = parts[0].split(">")[0]
            else:
                if len(parts) == 1:
                    flag = 3
                    number = parts[0].split(">")[0]
                    clock = parts[0].split(">")[1]
                else:
                    flag = 4
                    number = parts[0].split(">")[0]
                    clock = parts[1]
            number = float(number)
            for j, clock_name in enumerate(clocklist):
                if clock == clock_name:
                    if path_type == "f":
                        clock_value = self.clockValueFaultyPath[j][idx]
                    else:
                        clock_value = self.clockValueNormalPath[j][idx]
                    if flag == 1:
                        item = clock_value > number
                    elif flag == 2:
                        item = clock_value >= number
                    elif flag == 3:
                        item = clock_value < number
                    elif flag == 4:
                        item = clock_value <= number
                    constraints.append(item)
                    break
        return constraints

    def transReset(self, resetConstraint):
        resetList = resetConstraint.split(";")
        reset = [0] * self.automaton.clockNum
        for element in resetList:
            if element != '0':
                clockIndex = int(element.split("c")[1])
                reset[clockIndex - 1] = 1
        return reset

    def parseInv(self, invariant, clock, pos, path_type):
        if isinstance(invariant, int):
            if invariant == 1:
                return True
            else:
                return False
        invariant_list = invariant.split(';')
        for inv in invariant_list:
            clock_index = inv.split('c')[1]
            if clock_index == str(clock + 1):
                number = float(inv.split('>')[0])
                if path_type == 'f':
                    return self.clockValueFaultyPath[clock][pos] <= number
                elif path_type == 'n':
                    return self.clockValueNormalPath[clock][pos] <= number
        return True

    def run(self):
        assumD = Bool("d" + str(self.idxAssum))
        self.s.add(Implies(assumD, self.delta == self.DELTA))

        for i in range(self.automaton.getNbTransition()):
            self.s.add(self.labelTransition[i] == self.automaton.getTransitionAt(i).getEventId())

        cpt = 1
        tmp = list(self.isObservableTransition)
        this_time = 0
        while cpt <= self.BOUND:
            cpt += 1
            self.incBound()

            self.idxAssum += 1
            assumB = Bool("b" + str(self.idxAssum))
            assumF = Bool("f" + str(self.idxAssum))

            self.s.add(Implies(assumB, self.bound == len(self.faultyPath)))
            self.s.add(Implies(assumF, self.cptFaultOccursByThePast[-1] == self.DELTA))
            assumFO = Bool("fo" + str(self.idxAssum))
            self.s.add(Implies(assumFO, self.faultOccursByThePast[-1] == True))

            listAssum = [assumB, assumF] + tmp
            res = self.s.check(assumD, *listAssum)
            timeLine = str(self.s.statistics()).split("\n")[-1]
            ctime = re.findall(r"\d+\.?\d*", timeLine)

            this_time += float(ctime[0])

            if res == sat:
                print("sat")
                m = self.s.model()
                self.printModel(m, cpt)
                print("total_time", this_time)
                return
            else:
                print("Increase the bound:", len(self.faultyPath))

        print("The problem is UNSAT")
        print("total_time", this_time)
        self.print_unsat_core()

    def print_unsat_core(self):
        unsat_core = self.s.unsat_core()
        print("UNSAT Core:")
        for constraint in unsat_core:
            print(f"{constraint} -> {self.observable_map.get(str(constraint), 'Unknown')}")
        self.suggestions_based_on_unsat_core(unsat_core)

    def suggestions_based_on_unsat_core(self, unsat_core):
        suggestions = set()
        for constraint in unsat_core:
            constraint_str = str(constraint)
            if "length_fp" in constraint_str or "length_np" in constraint_str:
                suggestions.add("Increase the bound.")
            elif "delay_fp" in constraint_str or "delay_np" in constraint_str:
                suggestions.add("Adjust the delay constraints. Check if the delays are too restrictive.")
            elif "constraint_fp" in constraint_str or "constraint_np" in constraint_str:
                suggestions.add("Review clock constraints. Ensure they are correctly defined.")
            elif "cptFaultOccurs" in constraint_str:
                suggestions.add("Review fault occurrence assumptions. Verify the fault occurrence timing.")
            elif "bound" in constraint_str:
                suggestions.add("Consider increasing the bound.")
            elif "delta" in constraint_str:
                suggestions.add("Adjust delta value. Ensure delta constraints are realistic.")
            else:
                suggestions.add(f"Review the constraint: {constraint_str}")

        if suggestions:
            print("\nSuggestions to make the model SAT:")
            for suggestion in suggestions:
                print(suggestion)
        else:
            print("No specific suggestions generated based on the UNSAT core.")


if __name__ == "__main__":
    assert(len(sys.argv) == 2)
    z3Model = Z3Model()
    start = time.time()
    z3Model.run()
    end = time.time()
    print("Execution time:", str(end-start))
