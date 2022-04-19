import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random
from collections import defaultdict

class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__ ( self, gb, trail, val_sh, var_sh, cc ):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck ( self ):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    """
        Part 1 TODO: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Note: remember to trail.push variables before you assign them
        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """
    def forwardChecking ( self ):
        # check if the intial state of the board is consistent
        if not self.network.isConsistent(): return ({}, False)

        mvariables = dict()

        for v in self.network.getVariables():
            # check if the domain is consistent
            if not v.getDomain().size(): return (mvariables, False)

            # if the variable is assigned check its neighbors
            if v.isAssigned():

                # perform constraint propagation
                for n in self.network.getNeighborsOfVariable(v):
                    
                    if v.getAssignment() in n.getValues():
                        # before the neighbor is modified, push it into the trail so that we can backtrack
                        self.trail.push(n)
                        n.removeValueFromDomain(v.getAssignment())
                        mvariables[n] = n.getDomain()

                    # check if the assignment is not legal
                    if not n.getDomain().size(): return (mvariables, False)

        # perform consistency check on the current state of the network
        return (mvariables, self.network.isConsistent())



    # =================================================================
	# Arc Consistency
	# =================================================================
    def arcConsistency( self ):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

    
    """
        Part 2 TODO: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Note: remember to trail.push variables before you assign them
        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """
    def norvigCheck ( self ):
        mvariables = dict()

        #################### FIRST STRATEGY ####################

        # check if the intial state of the board is consistent
        if not self.network.isConsistent(): return ({}, False)

        for v in self.network.getVariables():
            # check if the domain is consistent
            if not v.getDomain().size(): return (mvariables, False)

            # if the variable is assigned check its neighbors
            if v.isAssigned():

                # perform constraint propagation
                for n in self.network.getNeighborsOfVariable(v):
                    
                    if v.getAssignment() in n.getValues():
                        # before the neighbor is modified, push it into the trail so that we can backtrack
                        self.trail.push(n)
                        n.removeValueFromDomain(v.getAssignment())

                    # check if the assignment is not legal
                    if not n.getDomain().size(): return (mvariables, False)

                    # check if there is only one value left that is possible for the neighbor
                    if n.getDomain().size() == 1:
                        n.assignValue(n.getValues())
                        mvariables[n] = n.getAssignment()

        #################### SECOND STRATEGY ####################

        # go through all the constraints
        for c in self.network.getConstraints():
            count = [0 for i in range(self.gameboard.N + 1)]

            # count the values in the variables within the constraint
            for v in c.vars:
                for val in v.getValues():
                    count[val] += 1

            # inconsistent if any value never appears
            if 0 in count[1:]: return (mvariables, False)

            # find all variables within the constraint who only have one value and assign them that value
            for i in range(1, self.gameboard.N + 1):
                if count[i] == 1:
                    for v in c.vars:
                        if not v.isAssigned() and i in v.getValues():
                            # before the variable is assigned, push it into the trail so that we can backtrack
                            self.trail.push(v)
                            v.assignValue(i)
                            mvariables[v] = v.getAssignment()

        # perform consistency check on the current state of the network
        return (mvariables, self.network.isConsistent())

    """
         Optional TODO: Implement your own advanced Constraint Propagation

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournCC ( self ):
        return False

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable ( self ):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    """
        Part 1 TODO: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """
    def getMRV ( self ):
        # keep track of the min domain size and its corresponding variable
        min_domain, min_domain_variable = float('inf'), None

        # iterate through all unassigned variables
        for v in self.network.getVariables():
            if not v.isAssigned() and v.size() < min_domain:
                min_domain, min_domain_variable = v.size(), v

        return min_domain_variable

    """
        Part 2 TODO: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """
    def MRVwithTieBreaker ( self ):
        # get all the unassigned variables in the constraint network
        variables = [v for v in self.network.getVariables() if not v.isAssigned()]

        # taking care of base case
        if not len(variables): return [None]
        if len(variables) == 1: return variables

        # keep track of the min domain size and its corresponding variables
        min_domain, min_domain_variables = float('inf'), []

        # iterate through the unassigned variables
        for v in variables:
            # clear the list every time we find a variable with a smaller domain size
            if v.size() < min_domain:
                min_domain_variables = [v]
                min_domain = v.size()

            # add to the list every time we find a variable of the same min domain size
            elif v.size() == min_domain:
                min_domain_variables.append(v)

        # taking care of base case
        if not len(min_domain_variables): return [None]
        if len(min_domain_variables) == 1: return min_domain_variables

        # keep track of the max unassigned neighbors and its corresponding variables
        max_unassigned_neighbors, min_max_variables = float('-inf'), []

        # iterate through the previously found variables with min domain size
        for v in min_domain_variables:
            # get the variable's number of unassigned neighbors
            v_unassigned_neighbors = len([n for n in self.network.getNeighborsOfVariable(v) if not n.isAssigned()])

            # clear the list every time we find a variable with a larger amount of unassigned neighbors
            if v_unassigned_neighbors > max_unassigned_neighbors:
                min_max_variables = [v]
                max_unassigned_neighbors = v_unassigned_neighbors

            # add to the list every time we find a variable with the same amount of unassigned neighbors
            elif v_unassigned_neighbors == max_unassigned_neighbors:
                min_max_variables.append(v)

        return min_max_variables

    """
         Optional TODO: Implement your own advanced Variable Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVar ( self ):
        return None

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    """
        Part 1 TODO: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """
    def getValuesLCVOrder ( self, v ):
        # get the variable's domain values
        count_neighbors = {d:0 for d in self.getValuesInOrder(v)}

        # iterate through neighbors of the variable
        for n in self.network.getNeighborsOfVariable(v):
            neighbors = self.getValuesInOrder(n)

            # iterate through the domain values of the neighbors
            for dv in neighbors:
                # count each one that appears in the variable's domain
                if dv in count_neighbors.keys():
                    count_neighbors[dv] += 1
        
        return [item[0] for item in sorted(count_neighbors.items(), key=lambda x: x[1])]

    """
         Optional TODO: Implement your own advanced Value Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVal ( self, v ):
        return None

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve ( self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if ( v == None ):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues( v ):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push( v )

            # Assign the value
            v.assignValue( i )

            # Propagate constraints, check consistency, recur
            if self.checkConsistency():
                elapsed_time = time.time() - start_time 
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1
                
            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()
        
        return 0

    def checkConsistency ( self ):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking()[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck()[1]

        if self.cChecks == "tournCC":
            return self.getTournCC()

        else:
            return self.assignmentsCheck()

    def selectNextVariable ( self ):
        if self.varHeuristics == "MinimumRemainingValue":
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            return self.MRVwithTieBreaker()[0]

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues ( self, v ):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder( v )

        if self.valHeuristics == "tournVal":
            return self.getTournVal( v )

        else:
            return self.getValuesInOrder( v )

    def getSolution ( self ):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
