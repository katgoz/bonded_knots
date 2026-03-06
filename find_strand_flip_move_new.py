#!!! description? two times slower(but cleaner) from find_strand_flip_move_old

import re
import heapq
from collections import defaultdict, deque
import knotpy as kp
from itertools import combinations

def find_path_of_type(diagram, start, end, allowed_type):
    """Finds the path between two endpoints in a PlanarDiagram using only transitions of allowed types(over/under) inside crossings.

    Args:
        diagram : PlanarDiagram
        start : Endpoint; starting endpoint 
        end : Endpoint; target endpoint 
        allowed_type : allowed type of transitions inside crossings ({"over"} or {"under"})

    Returns:
        list[tuple] or None: Sequence of endpoints forming the path or None if no path exists.


    Example:
        >>> pd_text = "V[0,1,2],V[2,3,4],X[0,6,5,1],X[4,3,5,6]"
        >>> diagram = kp.from_pd_notation(pd_text)
        >>> start = diagram.endpoints[('a', 1)]
        >>> end = diagram.endpoints[('d', 3)]
        >>> path = find_path_of_type(diagram, start, end, allowed_type={"over"})
        >>> print("Path:", path)

        Path: [a1, c3, c1, d3]
    """

    path = []
    current = start

    visited = set()

    while True:
        if current in visited:
            return None
        visited.add(current)
        path.append(current)
        current = diagram.twin(current)
        path.append(current)

        if current == end:
            return path

        node, pos = current.node, current.position

        if node not in diagram.crossings:
            return None

        if "over" in allowed_type and pos in (1, 3):
            next_ep = diagram.endpoints[(node, 4 - pos)]
        elif "under" in allowed_type and pos in (0, 2):
            next_ep = diagram.endpoints[(node, 2 - pos)]
        else:
            return None

        current = next_ep


def min_crossings_path(diagram, start, end, blocked_transitions):
    """Computes the minimal-cost path between two endpoints in a planar diagram, where cost represents the number of crossings that would be created
    by inserting an edge alongside this path.

    We construct an implicit graph where each node is a pair (endpoint, last_turn) and transitions correspond to legal moves through vertices or crossings,
    with edge weights 0 or 1; therefore, a 0-1 BFS algorithm is used.
    last_turn describes the last turning direction ("R" - right, "L" - left, "A" - no side has been chosen yet).

    Cost model:
    =>  Turns at vertices or crossings -> changing side costs 1; maintaining or choosing a side costs 0:

        Turning left:
            -> "A" -> "L": 0
            -> "R" -> "L": 1
            -> "L" -> "L": 0

        Turning right:
            -> "A" -> "R": 0
            -> "L" -> "R": 1
            -> "R" -> "R": 0


    => Straight transitions through a crossing:
        -> move maintaining side ("L" -> "L", "R" -> "R", "A" -> "A"): 1
        -> exception: 0
            If a crossing was used in the maximal pure path, alternative straight transitions
            through that crossing have zero cost (the crossing will disappear after moving the pure path).

    Transitions inside crossings may be blocked if they correspond to straight (over/under) transitions used previously in a maximal pure path.
    Other transitions through the same crossing remain allowed. 


    Args:
        diagram: PlanarDiagram
        start: Starting endpoint (Endpoint).
        end: Target endpoint (Endpoint).
        blocked_transitions (dict):
            Mapping: crossing_node -> set of forbidden straight transitions.
            Each transition is represented as a tuple (min_pos, max_pos) describing a straight passage inside that crossing which is not allowed.

    Returns:
        tuple[float, list[tuple[Endpoint, str]]] | tuple[None, None]:
            (minimal_cost, reconstructed_path_states), where each state is (endpoint, last_turn).
            minimal_cost represents the number of crossings that would be created by inserting an edge alongside reconstructed_path_states
            and is the minimal cost of all possible paths
            Returns (None, None) if no path exists.

    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> start = diagram.endpoints[('h', 2)]
    >>> end  = diagram.endpoints[('f', 0)]
    >>> print(min_crossings_path(diagram, start, end, {}))


    (1.0, [(h2, 'L'), (h0, 'L'), (a2, 'L'), (a1, 'L'), (e0, 'L'), (e3, 'L'), (f0, 'L')])
    """
    twin = diagram.twin
    vertices = diagram.vertices
    crossings = diagram.crossings
    endpoints = diagram.endpoints

    dq = deque() # dq: (endpoint, last_turn)

    dq.append((start, "A"))
    dq.append((twin(start), "A"))

    dist = {(start, "A"): 0.0, (twin(start), "A"): 0.0} # dist[(endpoint, last_turn)] = best known cost to reach this state so far

    parent = {}
    parent[(twin(start), "A")] = (start, "A")
    end_state = None

    while dq:
        endpoint, last_turn = dq.popleft()
        cost = dist[(endpoint, last_turn)]

        if endpoint == end or twin(endpoint) == end:
            end_state = (endpoint, last_turn)
            break

        node = endpoint.node
        pos = endpoint.position

        # ==================================================
        # TRANSITIONS THROUGH V
        # ==================================================
        if node in vertices:
            for ep in endpoints[node]:
                if ep == endpoint:
                    continue

                w=0

                # ---------- RIGHT ----------
                if (pos + 1) % 3 == ep.position:
                    new_turn = "R"
                    if last_turn == "L":
                        w=1

                 # ---------- LEFT ----------
                elif (pos - 1) % 3 == ep.position:
                    new_turn = "L"
                    if last_turn == "R":
                        w=1

                new_cost = cost + w
                state = (twin(ep), new_turn)

                if new_cost < dist.get(state, float("inf")):
                    dist[state] = new_cost
                    parent[state] = (endpoint, last_turn)
                    
                    if w == 0:
                        dq.appendleft(state)
                    else:
                        dq.append(state)

        # ==================================================
        # TRANSITIONS THROUGH X
        # ==================================================
        if node in crossings:
            for ep in endpoints[node]:
                if ep == endpoint:
                    continue

                w=0
                new_turn = last_turn


                # ---------- STRAIGHT (over/under) ----------
                if (pos + 2) % 4 == ep.position:
                    transition = (min(pos, ep.position), max(pos, ep.position))

                    if node in blocked_transitions and transition in blocked_transitions[node]:
                        continue

                    if node not in blocked_transitions:
                        w = 1
                    

                # ---------- RIGHT ----------
                elif (pos + 1) % 4 == ep.position:
                    new_turn = "R"
                    if last_turn == "L":
                        w=1

                # ---------- LEFT ----------
                elif (pos - 1) % 4 == ep.position:
                    new_turn = "L"
                    if last_turn == "R":
                        w=1


                new_cost = cost + w
                state = (twin(ep), new_turn)

                if new_cost < dist.get(state, float("inf")):
                    dist[state] = new_cost
                    parent[state] = (endpoint, last_turn)

                    if w == 0:
                        dq.appendleft(state)
                    else:
                        dq.append(state)


    if end_state is None:
        return None, None

    # ==========================
    # PATH RECONSTRUCTION
    # ==========================
    path_states = []
    ep, turn = end_state
    last_turn = "A"
    
    if twin(ep) == end:
        path_states.append((twin(ep), turn))
        cur = parent[end_state]

    else:
        cur = end_state

    while cur in parent:
        ep, turn = cur
        if turn == "A":
            path_states.append((ep, last_turn))
            path_states.append((twin(ep), last_turn))
        else:
            path_states.append(cur)
            path_states.append((twin(ep), turn))
            last_turn = turn

        cur = parent[cur]


    ep, turn = cur
    if turn == "A":
        path_states.append((ep, last_turn))
    else:
        path_states.append(cur)


    path_states.reverse()

    return dist[end_state], path_states


def max_between_nodes(diagram, node1, node2, allowed_type):
    """Finds the longest path with crossings of allowed type between two nodes (vertex or crossing) in a PlanarDiagram.

    For every pair of endpoints (one from node1, one from node2) computes the shortest allowed path
    (which is the only possible path due to restrictions on types of transitions) and returns the longest of them.

    Args:
    diagram : PlanarDiagram
    node1, node2 : node labels between which we look for a path (e.g. 'a', 'b', ...)
    allowed_type : allowed type of transitions inside crossings on the maximum path ({"over"} or {"under"})

    Returns:
    (int | None, list | None): Length of the longest allowed path (measured in number of endpoints) and the path itself. !!!list of endpoints

    Raises:
    ValueError: If "allowed_type" doesn't contain exactly one of {'over'} or {'under'}")

    Example:
    >>> pd_text = "V[0,1,2],V[2,3,4],X[0,6,5,1],X[4,3,5,6]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> print(max_between_nodes(diagram, 'a', 'b', allowed_type={"over"}))

    (6, [a1, c3, c1, d3, d1, b1])
    """
    if allowed_type not in {"over", "under"}:
        raise ValueError("allowed_type must contain exactly one of {'over'} or {'under'}")

    worst_len = None
    worst_path = None
    
    endpoints1 = [ep for ep in diagram.endpoints[node1]]
    endpoints2 = [ep for ep in diagram.endpoints[node2]]

    for s in endpoints1:
        for t in endpoints2:
            twin_s = diagram.twin(s)
            if twin_s== t:
                continue

            path = find_path_of_type(diagram, s, t, allowed_type)

            if path is not None:
                length = len(path)
                if worst_len is None or length > worst_len:
                    worst_len = length
                    worst_path = path


    return worst_len, worst_path


def find_blocked_transitions(diagram, max_path):
    """
    !!!!description
    """
    blocked_transitions = defaultdict(set)
    for i in range(1, len(max_path) - 1, 2):
        node1, pos1 = max_path[i]
        node2, pos2 = max_path[i + 1]

        if node1 == node2 and node1 in diagram.crossings:
            transition = (min(pos1, pos2), max(pos1, pos2))
            blocked_transitions[node1].add(transition)

    return blocked_transitions

def min_between_nodes(diagram, max_path):
    #!!!! can be optimized?: give min_crossings_path all possible endings for one start at once 
    """Computes the minimal-cost path between two nodes in a planar diagram, where the cost represents the number of crossings that would be created
    by inserting a new strand alongside this path. The function is intended to find an alternative placement for max_path, which is a strand 
    between these nodes. As such the search is subject to constraints imposed by max_path.

    The admissible start and end endpoints are selected depending on the types of the nodes involved (V–V, V–X, X–V, X–X).

    For crossings (X), only the endpoints of max_path are considered. The strand segment being moved must start and end at these fixed positions
    within the crossing, as its placement cannot be altered arbitrarily inside that X.

    For vertices (V), all incident sections are considered. In this case, the strand may be freely repositioned within the vertex, so every
    incident section is an admissible start or end point.

    For each admissible pair of endpoints (s, t), function min_crossings_path is executed. Among all valid paths, the one minimizing the cost is selected.

    The length of minimal-cost path is returned as a number of endpoints needed to insert it:
        The endpoint count is computed as: 2 * (number_of_crossings_along_path + 1) which corresponds to twice the number of arcs in the path.
        If s and t are directly connected (diagram.twin(s) == t), the trivial path of length 2 is returned.

    Args:
    diagram : PlanarDiagram; the diagram in which the search is performed
    max_path : list[Endpoint]; the previously computed maximal pure path determining fixed endpoints at crossings

    Returns:
    tuple[float, list[tuple[Endpoint, str]]] | tuple[None, None]
    (minimal_endpoint_count, reconstructed_path_states) or (None, None) if no admissible path exists

    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> cost, max_path = max_between_nodes(diagram, 'h', 'f', allowed_type={"over"})
    >>> print(min_between_nodes(diagram, max_path))

    (4.0, [(h2, 'L'), (h0, 'L'), (a2, 'L'), (a1, 'L'), (e0, 'L'), (e3, 'L'), (f0, 'L')])

    """
    blocked_transitions = find_blocked_transitions(diagram, max_path)

    best = None
    best_path = None

    start_ep = max_path[0]
    end_ep = max_path[-1]

    node1 = start_ep.node
    node2 = end_ep.node

    pairs = []

    if node1 in diagram.crossings and node2 in diagram.crossings:
        pairs = [(start_ep, end_ep)]

    elif node1 in diagram.crossings and node2 in diagram.vertices:
        pairs = [(start_ep, t) for t in diagram.endpoints[node2]]

    elif node1 in diagram.vertices and node2 in diagram.crossings:
        pairs = [(s, end_ep) for s in diagram.endpoints[node1]]

    else:
        pairs = [(s, t) for s in diagram.endpoints[node1] for t in diagram.endpoints[node2]]

    for s, t in pairs:
        if diagram.twin(s) == t:
            return (2.0, [(s, 'A'), (t, 'A')])

        d, path = min_crossings_path(diagram, s, t, blocked_transitions)

        if d is not None:
            length = (d + 1)*2
            if best is None or length < best:
                best = length
                best_path = path

    if best is None:
        return None, None

    return best, best_path


def find_strand_flip_move(diagram, allowed_type):
    """Searches for a strand flip move and returns found strand together with its alternative placement.
    A strand flip move consists of:
    1) Finding a strand whose crossings are exclusively of the allowed type (either 'over' or 'under')
    2) Finding an alternative placement for this strand such that 'flipping' it into position along the alternative path introduces fewer crossings
    If such an alternative placement exists, the diagram can be reduced.

    The strand is represented as a list of endpoints forming its path.
    The alternative placement is represented as a list of tuples (endpoint, turn), where 'turn' specifies on which side of the endpoint
    the strand should be placed after flipping.
    The sides are marked as either:
    => 'L' - left
    => 'R' - right
    => 'A' - ambiguous (both sides admissible)
    Left and right are determined relative to the direction of traversal along the path from the first endpoint to the last.

    Algorithm:
    For every pair of nodes(vertices and crossings) in the diagram the function computes between them:
    1) The pure-type path (over–over or under–under) with maximal number of crossings
    2) The path alongside which inserting a strand would result in the minimal possible number of crossings
    3) If the alternative path produces strictly fewer crossings than the maximal pure path, return both paths.

    Args:
    diagram : PlanarDiagram
        The diagram in which the search is performed.

    allowed_type : {"over", "under"}
        Specifies whether maximal over–over or under–under paths are considered.

    Returns:
    tuple[list[Endpoint], list[tuple[Endpoint, str]]] | tuple[None, None]
        (max_path, alternative_path) if a strictly shorter admissible path exists; otherwise (None, None).

    Raises:
        ValueError: If "allowed_type" doesn't contain exactly one of {'over'} or {'under'}")

    Example: (!!!)

    """
    if allowed_type not in {"over", "under"}:
        raise ValueError("allowed_type must be 'over' or 'under'")

    nodes = list(diagram.nodes)

    for node1, node2 in combinations(nodes, 2):
        max_len, max_path = max_between_nodes(diagram, node1, node2, allowed_type)

        if max_len is None:
            continue

        min_any, alternative_path = min_between_nodes(diagram, max_path)


        if min_any is not None and min_any<max_len:
            return max_path, alternative_path
            
    return None, None



def from_pd_notation_file(filename):
    """Creates a list of planar diagrams from PD notation.

    Args:
        filename: filename containing multiple PD notation strings each in a new line and a header

    Returns:
        List of PlanarDiagrams: list of parsed diagrams.

    Raises:
        ValueError: If the PD string is malformed or arcs are not paired.
    """
    diagrams = []
    with open(filename, "r") as f:
        next(f)
        for line in f:
            pd_text = line.strip()
            if not pd_text:
                continue

            D = kp.from_pd_notation(pd_text)
            diagrams.append(D)

    return diagrams

def main(filename):
    """Looks for a possible over_under move reducing number of crossings for each diagram in file. over_under move involves changing the position of an arc
    with exclusively over (or under) crossings to one with less. 

    Args:
        filename: filename containing multiple PD notation strings each in a new line and a header

    Returns:(!!<-to change later, should ideally return changed pd-code?)
        Number of diagrams that can be reduced

    """
    diagrams=from_pd_notation_file(filename)

    results=[]
    for D in diagrams:
        for kind in ("over", "under"):
            result = find_strand_flip_move(D, kind)
            max_path, alternative_path = result
            if max_path is not None and alternative_path is not None:
                results.append(result)
                break

    print("Results:", results)
    print("Number:", len(results))


    return len(results)


from pathlib import Path
file = "Re_Konsultacje/tri10_knots_reduced_inc3.txt"
main(file)
