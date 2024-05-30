class State:
    """
    Class to represent a state.
    """

    def __init__(self, id_state, invariant):
        """
        Constructor.

        Args:
        id_state (int): The ID of the state.
        invariant (str): The invariant associated with the state.
        """
        self.id_state = id_state
        self.invariant = invariant

    def __str__(self):
        """
        String representation of the state.
        
        Returns:
        str: The string representation of the state.
        """
        return f"{self.id_state}({self.invariant})"

    def getInvariant(self):
        """
        Getter for the invariant.

        Returns:
        str: The invariant of the state.
        """
        return self.invariant

    def getId(self):
        """
        Getter for the state ID.

        Returns:
        int: The ID of the state.
        """
        return self.id_state
