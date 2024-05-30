class Transition:
    """
    Class to store transition information.
    """
    uniq_id = 0

    def __init__(self, source, target, event, guard, reset):
        """
        Constructor.

        Args:
        source (State): The source state of the transition.
        target (State): The target state of the transition.
        event (int): The event ID associated with the transition.
        guard (list): The guard conditions for the transition.
        reset (list): The list of clocks to reset.
        """
        self.id = Transition.uniq_id
        Transition.uniq_id += 1

        self.source = source
        self.target = target
        self.event = event
        self.guard = guard
        self.reset = reset

    def __str__(self):
        """
        String representation of the transition.
        """
        return (f"*********************\nTransition id = {self.id}:\n"
                f"{self.source} -> {self.target}\nevent = {self.event}\n"
                f"guard = {self.guard}\nreset = {self.reset}")

    def getFinalState(self):
        """
        Getter for the target state.
        
        Returns:
        State: The target state.
        """
        return self.target

    def getSourceState(self):
        """
        Getter for the source state.
        
        Returns:
        State: The source state.
        """
        return self.source

    def getResetList(self):
        """
        Getter for the reset list.
        
        Returns:
        list: The list of clocks to reset.
        """
        return self.reset

    def getGuard(self):
        """
        Getter for the guard conditions.
        
        Returns:
        list: The guard conditions.
        """
        return self.guard

    def getEventId(self):
        """
        Getter for the event ID.
        
        Returns:
        int: The event ID.
        """
        return self.event
