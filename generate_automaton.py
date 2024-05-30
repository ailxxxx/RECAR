import sys
from collections import defaultdict
from graphviz import Digraph
from automaton import Automaton
from state import State
from transition import Transition

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

        event_dict = defaultdict(lambda: "unknown")
        event_dict["f"] = 1
        for i, key in enumerate(unobservable):
            event_dict[key] = i + 2
        for i, key in enumerate(observable):
            event_dict[key] = i + 2 + len(unobservable)

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
            if line == '\n' or line.startswith("invariant:"):
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
        sourceState = int(parts[0])
        finalState = int(parts[2])
        event = parts[1]
        event = event_dict[event]
        guard = parts[3].split(";")
        reset = parts[4].strip()
        resetList = [f"c{int(elt[1:])}" for elt in reset.split(';')] if reset != '0' else []

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
        invariantsList = [""] * (maxstate + 1)
        invariantDict = {}

        transitionNum = len(transitionList)
        for line in context[transitionNum + 2:]:
            if not line.strip():
                continue
            parts = line.split(' ')
            if len(parts) < 2:
                continue
            state, inv = map(str.strip, parts)
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

def generate_automaton_graph(automaton, event_dict, output_file):
    dot = Digraph()
    dot.attr(rankdir='LR')

    # 添加状态节点
    for state_id, state in automaton.mapState.items():
        state_label = f"q_{state_id}"
        dot.node(str(state_id), f'{state_label}\n{state.getInvariant()}')

    # 添加转换边
    for transition in automaton.getTransitionList():
        src = transition.getSourceState().getId()
        tgt = transition.getFinalState().getId()
        event_id = transition.getEventId()
        event_label = next((k for k, v in event_dict.items() if v == event_id), "unknown")
        guard = " & ".join(transition.getGuard())
        reset = " & ".join([f"{r}:=0" for r in transition.getResetList()])
        label = f'{event_label}\n{guard}'
        if reset:
            label += f"\n{reset}"
        dot.edge(str(src), str(tgt), label)

    # 保存和渲染图像
    dot.render(output_file, format='png', cleanup=True)
    print(f"Automaton graph saved as '{output_file}.png'")

def main():
    # 检查命令行参数
    if len(sys.argv) != 2:
        print("Usage: python generate_automaton.py <input_file>")
        sys.exit(1)

    # 获取输入文件名
    input_file = sys.argv[1]
    
    # 创建 Parser 对象
    parser = Parser()
    
    # 解析输入文件
    automaton, bound, delta = parser.parse(input_file)
    
    # 打印解析结果
    print("Automaton Information:")
    print(automaton)
    print(f"Bound: {bound}")
    print(f"Delta: {delta}")
    
    print("\nTransitions:")
    for transition in automaton.getTransitionList():
        print(transition)
    
    print("\nStates:")
    for state_id in automaton.mapState:
        state = automaton.getState(state_id)
        print(f"State ID: {state_id}, State Info: {state}")

    # 获取事件字典
    _, _, _, event_dict, _ = parser._parse_header(open(input_file, "r").readlines()[0])

    # 生成自动机图像，输出文件名与输入文件名保持一致
    output_file = input_file.rsplit('.', 1)[0] + '_graph'
    generate_automaton_graph(automaton, event_dict, output_file)

if __name__ == "__main__":
    main()
