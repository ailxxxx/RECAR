#!/usr/bin/python3
# -*- coding: utf-8 -*-
from collections import defaultdict
from transition import Transition
from state import State
from automaton import Automaton

class Parser:
    def __init__(self):
        pass

    def parse(self, nameFile: str):
        """
        Parse the input file to create an Automaton object.
        
        Args:
        nameFile (str): The name of the file to parse.

        Returns:
        tuple: A tuple containing the automaton object, bound, and delta.
        """
        with open(nameFile, "r") as file:
            context = file.readlines()  # context stores all txt transitions and parameters

        initState, bound, delta, event_dict, clockList = self._parse_header(context[0])

        transitionList = self._parse_transitions(context, initState, event_dict)

        maxstate = self._get_max_state(transitionList)

        invariantsList, invariantDict = self._parse_invariants(context, transitionList, maxstate)

        automaton = Automaton(initState, len(clockList), len(event_dict) - 3, len(event_dict) - 2, invariantDict)

        self._add_transitions_to_automaton(automaton, transitionList, invariantsList)

        return automaton, bound, delta

    def _parse_header(self, header_line):
        """
        Parse the header line of the file.
        
        Args:
        header_line (str): The header line to parse.

        Returns:
        tuple: Parsed initial state, bound, delta, event dictionary, and clock list.
        """
        parts = header_line.split(" ")
        initState = int(parts[1])
        bound = int(parts[3])
        delta = int(parts[5])

        observable = parts[6].split("{")[1].split("}")[0].split(",")
        unobservable = parts[7].split("{")[1].split("}")[0].split(",")

        event_dict = defaultdict(int)
        for i, key in enumerate(observable):
            event_dict[key] = i + 3
        for key in unobservable:
            event_dict[key] = 2

        clockString = parts[9]
        clockList = clockString.split("{")[1].split("}")[0].split(",")

        return initState, bound, delta, event_dict, clockList

    def _parse_transitions(self, context, initState, event_dict):
        """
        Parse the transitions from the context.

        Args:
        context (list): The list of lines from the file.
        initState (int): The initial state.
        event_dict (dict): The dictionary of event mappings.

        Returns:
        list: The list of parsed transitions.
        """
        transitionList = []
        for line in context[1:]:
            if line == '\n':
                break
            transitionList.append(self._parse_transition(line, initState, event_dict))
        return transitionList

    def _parse_transition(self, line, initState, event_dict):
        """
        Parse a single transition line.

        Args:
        line (str): The line to parse.
        initState (int): The initial state.
        event_dict (dict): The dictionary of event mappings.

        Returns:
        list: The parsed transition.
        """
        parts = line.split(" ")
        sourceState = int(parts[0].split(',')[0]) - initState
        finalState = int(parts[2].split(',')[0]) - initState
        event = parts[1]
        event = 1 if event == "f" else event_dict[event]
        guard = parts[3].split(";")
        reset = parts[4].strip()
        resetList = [int(elt[1:]) - 1 for elt in reset.split(';')] if reset != '0' else []

        return [sourceState, finalState, event, guard, resetList]

    def _get_max_state(self, transitionList):
        """
        Get the maximum state value from the transition list.

        Args:
        transitionList (list): The list of transitions.

        Returns:
        int: The maximum state value.
        """
        return max(max(transition[0], transition[1]) for transition in transitionList)

    def _parse_invariants(self, context, transitionList, maxstate):
        """
        Parse the invariants from the context.

        Args:
        context (list): The list of lines from the file.
        transitionList (list): The list of transitions.
        maxstate (int): The maximum state value.

        Returns:
        tuple: A tuple containing the list of invariants and the invariant dictionary.
        """
        invariantsList = [1 for _ in range(maxstate + 1)]
        invariantDict = {}
        invariant_section = False
        for line in context:
            if line.strip() == "invariant:":
                invariant_section = True
                continue
            if invariant_section:
                parts = line.split(' ')
                if len(parts) < 2:
                    print(f"Skipping invalid invariant line: {line}")
                    continue
                state, inv = map(str.strip, parts[:2])
                state = int(state)
                invariantsList[state] = inv
                invariantDict[state] = inv
        return invariantsList, invariantDict


    def _add_transitions_to_automaton(self, automaton, transitionList, invariantsList):
        """
        Add parsed transitions to the automaton.

        Args:
        automaton (Automaton): The automaton object.
        transitionList (list): The list of parsed transitions.
        invariantsList (list): The list of invariants.
        """
        for transition in transitionList:
            sourceState, finalState = transition[0], transition[1]
            transition.insert(1, invariantsList[sourceState])
            transition.insert(3, invariantsList[finalState])

            sourceState, sourceState_inv = transition[0], transition[1]
            finalState, finalState_inv = transition[2], transition[3]
            event, guard, resetList = transition[4], transition[5], transition[6]

            automaton.addState(sourceState, sourceState_inv)
            automaton.addState(finalState, finalState_inv)
            automaton.appendTransition(sourceState, finalState, event, guard, resetList)
