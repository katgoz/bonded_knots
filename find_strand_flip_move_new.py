"""
Finds a strand-flip move: a strand that passes only through over or under crossings,
and checks whether it can be rerouted along an alternative path with fewer crossings.
If such a cheaper placement exists, the strand is replaced accordingly (flip).
"""

import random
import re
import heapq
from collections import defaultdict, deque
import knotpy as kp
from itertools import combinations
from knotpy.classes.endpoint import Endpoint

def find_path_of_type(diagram, start, end=None, allowed_type={"over"}):
    """Finds a path in a PlanarDiagram using only transitions of allowed types (over/under) inside crossings.

    If end is provided, the function searches for a path from start to end.
    If end is None, it follows the path starting from start as long as allowed transitions are possible,
    and returns the maximal path obtained this way.

    Args:
        diagram : PlanarDiagram
        start : Endpoint
            Starting endpoint.
        end : Endpoint or None, optional
            Target endpoint. If None, the path is extended as far as possible.
        allowed_type : set
            Allowed types of transitions inside crossings ({"over"} or {"under"}).

    Returns:
        list[Endpoint] or None:
            - If end is given: path from start to end, or None if no such path exists.
            - If end is None: maximal path starting from start, or None if a loop is detected.

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

        if end is not None and current == end:
            return path

        node, pos = current.node, current.position

        if node not in diagram.crossings:
            return path if end is None else None

        if "over" in allowed_type and pos in (1, 3):
            next_ep = diagram.endpoints[(node, 4 - pos)]
        elif "under" in allowed_type and pos in (0, 2):
            next_ep = diagram.endpoints[(node, 2 - pos)]
        else:
            return path if end is None else None

        current = next_ep


def min_crossings_path(diagram, start_endpoints, target_endpoints, blocked_transitions):
    """Computes the minimal-cost path between a set of start endpoints and a set of target endpoints in a planar diagram, where cost represents
    the number of crossings that would be created by inserting an edge alongside this path.

    The search is initialized with all start_endpoints and terminates when any endpoint from target_endpoints is reached.

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
        start_endpoints (Iterable[Endpoint]):
            Endpoints from which the search is initialized.

        target_endpoints (Iterable[Endpoint]):
            Endpoints at which the search terminates.

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
    >>> print(min_crossings_path(diagram, [start], [end], {}))


    (1.0, [(h2, 'L'), (h0, 'L'), (a2, 'L'), (a1, 'L'), (e0, 'L'), (e3, 'L'), (f0, 'L')])
    """
    if not isinstance(start_endpoints, (list, tuple, set)) or not isinstance(target_endpoints, (list, tuple, set)):
        raise TypeError("start_endpoints and target_endpoints must be a list/tuple/set of Endpoint objects")

    if len(start_endpoints) == 0 or len(target_endpoints) == 0:
        raise ValueError("start_endpoints and target_endpoints cannot be empty")

    if not all(isinstance(ep, Endpoint) for ep in start_endpoints) or not all(isinstance(ep, Endpoint) for ep in target_endpoints):
        raise TypeError("All elements of start_endpoints and target_endpoints must be Endpoint objects")

    twin = diagram.twin
    vertices = diagram.vertices
    crossings = diagram.crossings
    endpoints = diagram.endpoints
    target_endpoints = set(target_endpoints)

    dq = deque() # dq: (endpoint, last_turn)
    parent = {}
    dist = {} # dist[(endpoint, last_turn)] = best known cost to reach this state so far

    for s in start_endpoints:
        dq.append((s, "A"))
        dq.append((twin(s), "A"))

        dist[(s, "A")] = 0.0
        dist[(twin(s), "A")] = 0.0
        parent[(twin(s), "A")] = (s, "A")

    end_state = None

    while dq:
        endpoint, last_turn = dq.popleft()
        cost = dist[(endpoint, last_turn)]

        if endpoint in target_endpoints or twin(endpoint) in target_endpoints:
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
    
    if twin(ep) in target_endpoints:
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
    if not path_states or path_states[-1][0] != ep:
        if turn == "A":
            path_states.append((ep, last_turn))
        else:
            path_states.append(cur)


    path_states.reverse()

    return dist[end_state], path_states


def max_between_nodes(diagram, node1, node2, allowed_type):
    """Finds the longest path with crossings of allowed type between two nodes (vertex or crossing) in a PlanarDiagram.

    For every pair of endpoints (one from node1, one from node2), the function attempts to find
    a path whose crossings are all of the given type (over/under). Such a path may not exist due
    to the imposed transition restrictions. Among all existing paths, the longest one is returned.

    Args:
    diagram : PlanarDiagram
    node1, node2 : node labels between which we look for a path (e.g. 'a', 'b', ...)
    allowed_type : allowed type of transitions inside crossings on the maximum path ("over" or "under")

    Returns:
    (int | None, list | None): (int | None, list | None):   
        Length of the longest allowed path (measured in number of endpoints)
        and the path itself (list of endpoints). Returns (None, None) if no valid path exists.

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
    """Extracts and records all crossing transitions used along a given path.

    The function scans the path and collects all transitions that pass through crossings.
    In particular, it records the straight transitions (over/under) that were actually used
    along this path. Each such transition is stored as a pair of endpoint positions at a crossing.

    Args:
    diagram : PlanarDiagram
    max_path : list[Endpoint]
        Path represented as a sequence of endpoints (typically returned by find_path_of_type or max_between_nodes).

    Returns:
    dict[node, set[tuple[int, int]]]:
        Mapping from crossing nodes to sets of blocked transitions (pairs of positions).
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
    """Computes the minimal-cost path between two nodes in a planar diagram, where the cost represents the number of crossings that would be created
    by inserting a new strand alongside this path. The function is intended to find an alternative placement for max_path, which is a strand 
    between these nodes. As such the search is subject to constraints imposed by max_path.

    The admissible start and end endpoints are selected depending on the types of the nodes involved (V–V, V–X, X–V, X–X).

    For crossings (X), only the endpoints of max_path are considered. The strand segment being moved must start and end at these fixed positions
    within the crossing, as its placement cannot be altered arbitrarily inside that X.

    For vertices (V), all incident sections are considered. In this case, the strand may be freely repositioned within the vertex, so every
    incident section is an admissible start or end point.

    The admissible start and end endpoints are collected according to the node types. The function min_crossings_path is then executed once with
    these sets of start and target endpoints, and the minimal-cost path connecting any admissible pair is selected.

    The length of minimal-cost path is returned as a number of endpoints needed to insert it:
        The endpoint count is computed as: 2 * (number_of_crossings_along_path + 1) which corresponds to twice the number of arcs in the path.
        If s and t are directly connected (diagram.twin(s) == t), the trivial path of length 2 is returned.

    Args:
    diagram : PlanarDiagram; the diagram in which the search is performed
    max_path : list[Endpoint]; the previously computed maximal pure path determining fixed endpoints at crossings

    Returns:
    tuple[float, list[tuple[Endpoint, str]]] | tuple[None, None]
    (minimal_endpoint_count, reconstructed_path_states) where each element is (Endpoint, turn), with turn ∈ {'L', 'R', 'A'}
    or (None, None) if no admissible path exists

    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> cost, max_path = max_between_nodes(diagram, 'h', 'f', allowed_type={"over"})
    >>> print(min_between_nodes(diagram, max_path))

    (4.0, [(h2, 'L'), (h0, 'L'), (a2, 'L'), (a1, 'L'), (e0, 'L'), (e3, 'L'), (f0, 'L')])

    """
    blocked_transitions = find_blocked_transitions(diagram, max_path)

    start_ep = max_path[0]
    end_ep = max_path[-1]

    node1 = start_ep.node
    node2 = end_ep.node

    start_endpoints = [start_ep]
    target_endpoints = [end_ep]

    if node1 in diagram.crossings and node2 in diagram.vertices:
        target_endpoints = list(diagram.endpoints[node2])

        for t in target_endpoints:
            if diagram.twin(start_ep) == t:
                return (2.0, [(start_ep, 'A'), (t, 'A')])

    elif node1 in diagram.vertices and node2 in diagram.crossings:
        start_endpoints = list(diagram.endpoints[node1])

        for s in start_endpoints:
            if diagram.twin(s) == end_ep:
                return (2.0, [(s, 'A'), (end_ep, 'A')])

    elif node1 in diagram.vertices and node2 in diagram.vertices :
        for s in diagram.endpoints[node1]:
            if diagram.twin(s).node == node2:
                return (2.0, [(s, 'A'), (diagram.twin(s), 'A')])

        start_endpoints = list(diagram.endpoints[node1])
        target_endpoints = list(diagram.endpoints[node2])

    d, path = min_crossings_path(diagram, start_endpoints, target_endpoints, blocked_transitions)

    if d is None:
        return None, None

    length = (d + 1) * 2
    return length, path

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
    """Looks for a possible strand flip move that reduces the number of crossings in each diagram from a file.
    A strand flip move is detected when a strand consisting exclusively of over (or under) crossings
    admits an alternative placement with fewer crossings.

    The function tests each diagram for both "over" and "under" types and prints those for which
    a valid reduction exists, together with their total count.

    Args:
        filename: filename containing multiple PD notation strings, each in a new line with a header

    Returns:
        None
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


def insert_crossing(diagram, last_ep, turn, from_ep=None, to_ep=None, kind="under"):
    """Inserts a crossing by subdividing an existing endpoint and routing a new connection through it.

    The function splits the given endpoint by introducing a crossing between the original strand and a newly
    created strand. The parameter `kind` determines whether the new strand passes over or under the original one.

    After subdivision, two new endpoints are created, corresponding to the ends of the new (alternative) strand.
    They are either connected to the growing alternative path via `from_ep` and `to_ep`, or left free and returned.

    Parameters turn, from_ep and to_ep:

        The function is used during construction of an `alternative_path` (see: insert_path_core), which specifies the full structure of the
        new strand as a sequence of (endpoint, turn) instructions. The `turn` value ("L"/"R") is taken directly from
        this path according to function insert_path_core and determines the local ordering of strands at each crossing.

        The strand is constructed incrementally: at each step, a new crossing is inserted and attached to the already
        built part of the alternative strand. `from_ep` represents the current end of this partial construction and
        is used to extend it step by step along the path.

        `to_ep`, if provided, connects the new crossing to the next step in the alternative path; otherwise it remains free.

        Thus, `from_ep`, `to_ep`, and `turn` all come from and are consistent with the `alternative_path`, and refer
        to the newly constructed strand.

    Args:
    diagram : PlanarDiagram
        Diagram being modified in-place.
    last_ep : Endpoint
        Endpoint that is replaced by a crossing.
    turn : str
        Direction of traversal at the crossing ("L" or "R").
    from_ep : tuple, optional
        Previous endpoint of the newly constructed alternative strand (incremental construction).
    to_ep : tuple, optional
        Next endpoint of the alternative strand.
    kind : str
        Relative position of the new strand ("over" or "under").

    Returns:
    list[tuple]
        List of unconnected endpoints created at the crossing.
    """
    pos = 1 if kind == "under" else 0

    x = kp.subdivide_endpoint_by_crossing(diagram, last_ep, pos)

    p1 = (pos + 1) % 4
    p2 = (pos - 1) % 4

    if turn == "R":
        first, second = p1, p2
    else:
        first, second = p2, p1

    free_endpoints = []

    if from_ep is not None:
        diagram.set_endpoint((x, first), (from_ep[0], from_ep[1]))
        diagram.set_endpoint((from_ep[0], from_ep[1]), (x, first))
    else:
        free_endpoints.append((x, first))

    if to_ep is not None:
        diagram.set_endpoint((x, second), (to_ep[0], to_ep[1]))
        diagram.set_endpoint((to_ep[0], to_ep[1]), (x, second))
    else:
        free_endpoints.append((x, second))

    return free_endpoints

def insert_path_core(diagram, alternative_path, kind , max_path = None, outer = False):
    """Builds a new strand in the diagram following the structure given by `alternative_path`.

    The function inserts a new strand step-by-step according to `alternative_path`, which is a sequence of
    (endpoint, turn) instructions describing how the strand should be embedded in the diagram.
    At this stage, the construction does not directly connect the two final ends of the strand.

    For each step, the function checks whether a crossing must be inserted between consecutive elements of
    the path. If so, a new crossing is created via `insert_crossing`, where the `from_ep` argument is used to connect
    the newly created crossing to the already constructed part of the strand. This allows the strand to be extended incrementally along the path.

    If `max_path` is provided, it is used to avoid inserting unnecessary crossings with segments belonging
    to the original maximal strand (that will be removed later in the algorithm).

    If `outer=True`, the function additionally tracks whether the newly constructed strand crosses
    into the outer face. All endpoints of the newly built strand that become part of the outer face are recorded.

    Returns:
    - start_ep: first endpoint of the constructed strand
    - free_ep: last endpoint of the constructed strand
    - new_outer (optional): list of newly inserted endpoints belonging to the outer face if `outer=True`
    """
    def need_crossing(prev_ep, prev_turn, ep, turn):
        if turn != prev_turn: #insert crossing when changing side (left <-> right)
             if max_path is None or (max_path and prev_ep not in max_path[1:-1]): #dont insert crossing if its with a part of max_path that will be removed
                return prev_ep
        elif prev_ep.node == ep.node and ep.node in diagram.crossings and (prev_ep.position + 2) % 4 == ep.position: #crossing when going straight through a crossing
            offset = 1 if turn == "R" else -1
            if max_path is None or (max_path and diagram.endpoints[(prev_ep.node, (prev_ep.position + offset)%4)] not in max_path[1:-1]):
                return diagram.endpoints[(prev_ep.node, (prev_ep.position + offset)%4)]
        return None

    start_ep = None
    free_ep = None

    prev_ep, prev_turn = alternative_path[0]

    # check whether we start on the outside or inside of the diagram;
    # if we start inside, we append "S" instead of an endpoint to new_outer,
    # since the actual endpoints at the ends of the path are not yet known.
    # We track whether we are currently inside or outside using the boolean `out`.
    if outer == True:
        new_outer=[]
        out = False
        if prev_ep.attr.get("outer") or diagram.twin(prev_ep).attr.get("outer"):
            ep, turn = alternative_path[1]
            if ep.attr.get("outer") or diagram.twin(ep).attr.get("outer"):
                node_obj = diagram.nodes[prev_ep.node]
                dg = node_obj.degree()
                if (
                    (ep.node == prev_ep.node) or 
                    (ep.node != prev_ep.node and (
                        (prev_turn == "R" and (
                            diagram.endpoints[(prev_ep.node, (prev_ep.position-1)%dg)].attr.get("outer") == True or
                            diagram.twin(diagram.endpoints[(prev_ep.node, (prev_ep.position-1)%dg)]).attr.get("outer") == True
                        )) or 
                        (prev_turn == "L" and (
                            diagram.endpoints[(prev_ep.node, (prev_ep.position+1)%dg)].attr.get("outer") == True or 
                            diagram.twin(diagram.endpoints[(prev_ep.node, (prev_ep.position+1)%dg)]).attr.get("outer") == True
                        ))
                    ))
                ):
                    out = True
                    new_outer.append("S")
            
            elif ep.node == prev_ep.node and ep.node in diagram.crossings and ep.position == (prev_ep.position + 2)%4:
                out = True
                new_outer.append("S")
             
    #main core inserting algorithm
    for ep, turn in alternative_path[1:]:
        ep_cross = need_crossing(prev_ep, prev_turn, ep, turn)
        if ep_cross is not None:
            # update whether we are inside or outside after crossing insertion
            if outer == True:
                if ep_cross.attr.get("outer") or diagram.twin(ep_cross).attr.get("outer"): 
                    if out == True:
                        out = False

                    else:
                        out = True
                elif out == True:
                    out = False

            use_turn = turn

            if prev_turn != turn:
                if ep_cross == ep:
                    use_turn = prev_turn

            free = insert_crossing(diagram, ep_cross, use_turn, free_ep, None, kind)


            if not free:
                raise ValueError("No free endpoints")

            #at the first step we get 2 endpoints from insert_crossing function, first of them is a start (that we leave free), second will be extended
            if len(free) == 2 and start_ep is None:
                start_ep = free[0]

            free_ep = free[-1]

            # if we are currently on the outer face, record endpoint
            if outer == True and out == True:
                new_outer.append(free_ep)

        # crossing that belongs to max_path and is not inserted (because it would be removed), still affects outer-face tracking
        elif outer == True and prev_ep.node == ep.node and ep.node in diagram.crossings and (prev_ep.position + 2) % 4 == ep.position: 
            offset = 1 if turn == "R" else -1
            ep_cross = diagram.endpoints[(prev_ep.node, (prev_ep.position + offset)%4)]

            if ep_cross.attr.get("outer") or diagram.twin(ep_cross).attr.get("outer"): 
                if out == False:
                    out = True
                    if free_ep:
                        new_outer.append(free_ep)
                    else:
                        new_outer.append("S")


        prev_ep, prev_turn = ep, turn

    if outer == True:
        return start_ep, free_ep, new_outer

    return start_ep, free_ep

def insert_endpoint(diagram, node, pos, new_ep):
    """Inserts an endpoint into a node at a given position and updates twin references.

    For vertices, the function:
    - removes invalid endpoints in the target node,
    - inserts the new endpoint at position `pos` (there has to be one free place, for example after removing invalid endpoint),
    - rebuilds the endpoint list,
    - updates positions of shifted endpoints and fixes twin references if needed.

    For crossings, the function:
    - inserts the endpoint only if the position is free or invalid,
    - otherwise raises an error to avoid overwriting an existing valid connection.

    Args:
    diagram : PlanarDiagram (knotpy)
    node : node label
        Node to which the endpoint is inserted.
    pos : int
        Index at which the endpoint is inserted.
    new_ep : Endpoint or tuple
        Endpoint to insert, given either as an Endpoint object or (node, position).

    Returns:
    None
    """
    if not isinstance(new_ep, Endpoint):
        new_ep = Endpoint(new_ep[0], new_ep[1])
    
    if node in diagram.vertices:
        endpoints=[]

        # collect valid endpoints; mark invalid one for removal
        remove = None
        for i, ep in enumerate(diagram.nodes[node]):
            if ep.node in diagram.nodes:
                endpoints.append(ep)
            else:
                remove = (node, i) #usuwamy jak natrafimy na zły


        if len(endpoints) == 3:
            raise ValueError("cannot insert endpoint: no free slot")

        # remove invalid endpoint from diagram
        if remove is not None:
            diagram.remove_endpoint(remove)

        endpoints.insert(pos, new_ep)

        diagram._nodes[node]._inc = endpoints

        # fix twin references for shifted endpoints
        for i in range(pos + 1, len(endpoints)):
            ep = endpoints[i]
            if ep is None:
                continue

            twin_ep = diagram.twin(ep)

            if twin_ep is None:
                continue


            if twin_ep.node == node:
                twin_ep.position = i

    if node in diagram.crossings:
        twin = diagram.twin((node, pos))
        # insert only if slot is free or invalid
        if twin is None or twin.node not in diagram.nodes:
            diagram.set_endpoint((node, pos), new_ep)
        else:
            raise ValueError("cannot overwrite legitimate endpoint")

def decide_insert_place_2ep(del_pos, first_pos, second_pos):
    """Determines the correct insertion position in a node when an alternative path passes through
    the vertex in two steps, e.g. [(a0, 'R'), (a1, 'R'), (b1, 'R'), ...] passes through node 'a' in 2 steps.

    The function preserves the correct cyclic ordering of endpoints in a node at the end of the new
    strand after removing the old strand.

    After removing the old endpoint, we are left with a list of two endpoints. The task reduces
    to choosing the correct index for a standard list `insert` operation on this 2-element list,
    so that the resulting ordering matches the cyclic order in the node.

    Since the path passes through two endpoints in a single node, the new insertion position must
    lie between them in the cyclic order. However, removing one endpoint (`del_pos`) shifts the
    indexing of the remaining elements, which must be taken into account.

    The function compares the positions of the two consecutive endpoints (`first_pos`, `second_pos`)
    with the removed position (`del_pos`) and determines the correct insertion index accordingly.

    Args:
        del_pos : int
            Position of the removed (original) connection in the node.
        first_pos : int
            Position of the first endpoint of the alternative path.
        second_pos : int
            Position of the second endpoint of the alternative path.

    Returns:
        int:
            Index for `insert` in the 2-element list of endpoints preserving cyclic ordering.
    """
    if first_pos + second_pos == 1: #1->0, 0->1
        if del_pos == 0:
            return 2
        else:
            return 1
    if first_pos + second_pos == 3: #1 -> 2, 2-> 1
        if del_pos == 2:
            return 2
        else:
            return 1
    else:
        return 2

def decide_insert_place_1ep(del_pos, first_pos, turn):
    """Determines the correct insertion position in a node when an alternative path passes through
    the vertex in a single step (i.e. [(a0, 'R'), (b1, 'R'), ...] leaves node 'a' in 1 step).

    The function preserves the correct cyclic ordering of edges in a planar diagram after replacing
    an original strand with a new one.

    After removing the old endpoint, we consider how to insert new endpoint using a
    standard list `insert` operation so that the resulting ordering matches the cyclic structure of
    the node.

    The insertion position is determined relative to the incoming endpoint (`first_pos`) and must
    be placed immediately to its right ("R") or left ("L") in the cyclic order. However, this local
    choice must also take into account that removing the old endpoint (`del_pos`) shifts the indexing
    of the remaining endpoints.

    Args:
        del_pos : int
            Position of the removed (original) connection in the node.
        first_pos : int
            Position of the endpoint of the alternative path in the node.
        turn : str
            Direction of the turn in the path ("R" or "L"), influencing ordering.

    Returns:
        int:
            Index for `insert` that preserves the cyclic ordering of the node.
    """
    if del_pos == 1:
        if first_pos == 1:
            return 1
        elif first_pos == 2:
            pos1 = 1 if turn == "R" else 2
            return pos1
        else:
            pos1 = 2 if turn == "R" else 1
            return pos1

    else: #del_pos 0,2
        if del_pos == first_pos:
            return 2
        elif first_pos == (del_pos + 1)%3:
            pos1 = 2 if turn == "R" else 1
            return pos1
        else:
            pos1 = 1 if turn == "R" else 2
            return pos1

def attach_ends(diagram, path, max_path, start_ep, free_ep, start = False):
    """Attaches the newly constructed strand to the diagram by connecting its end endpoints
    to the nodes at both ends of the original strand (`max_path`).

    First, the function determines how the connections should be made at both ends, i.e. how the new strand
    should be attached at the nodes at both ends of `max_path`. This is necessary because for vertices the
    cyclic order of endpoints may change, while for crossings the positions are fixed.

    The attachment positions are determined based on the local configuration: the position of the removed
    endpoint (from `max_path`) and the alternative path (`path`).
    For vertices, helper functions decide the correct position depending on how the alternative path passes
    through the end nodes: whether it moves through it in two steps (helper function: `decide_insert_place_2ep`) 
    or immediately leaves the node (helper function: `decide_insert_place_1ep`),
    for example: [(a0, 'R'), (a1, 'R'), (b1, 'R'), ...] goes through the node 'a' in 2 steps,
    while [(a0, 'R'), (b1, 'R'), ...] immediately leaves node.

    For crossings, the position is taken directly from the path.

    Once these positions are determined, the function connects them to the core of the new strand.
    That is, the beginning of the core (`start_ep`) is attached to the first node, and the end of the core
    (`free_ep`) is attached to the last node.

    If no core was created (i.e. `start_ep` and `free_ep` are None), the function directly connects
    the two computed positions to each other, forming a simple edge.

    This completes the replacement of the original strand with the newly constructed one.


    Args:
    diagram : PlanarDiagram
    path : list of (Endpoint, turn)
        The alternative path that defines how the new strand is constructed.
    max_path : list of Endpoint
        The original strand being replaced.
    start_ep, free_ep : Endpoint or None
        Endpoints of the newly constructed strand (core of the new path).
    start : bool, optional
        If True, returns the insertion position of the starting endpoint attachment.

    Returns:
    tuple or None:
        (node, position) of the starting attachment if `start=True`, otherwise None.
    """
    first_del_ep = max_path[0]
    first_ep, first_turn = path[0]
    second_ep = path[1][0]

    node1 = first_ep.node
    if node1 in diagram.vertices:
        if node1 == second_ep.node:
            pos1 = decide_insert_place_2ep(first_del_ep.position, first_ep.position, second_ep.position)

        else:
            pos1 = decide_insert_place_1ep(first_del_ep.position, first_ep.position, first_turn)

    if node1 in diagram.crossings:
        pos1 = first_ep.position

    last_del_ep = max_path[-1]
    last_ep, last_turn = path[-1]
    second_to_last_ep, second_to_last_turn = path[-2]
    node2 = last_ep.node
    if node2 in diagram.vertices:
        if node2 == second_to_last_ep.node:
            pos2 = decide_insert_place_2ep(last_del_ep.position, second_to_last_ep.position, last_ep.position)

        else:
            turn = "L" if last_turn == "R" else "R"
            pos2 = decide_insert_place_1ep(last_del_ep.position, last_ep.position, turn)

    if node2 in diagram.crossings:
        pos2 = last_ep.position

    if start_ep == None and free_ep == None:
        insert_endpoint(diagram, node1, pos1, (node2, pos2))
        insert_endpoint(diagram, node2, pos2, (node1, pos1))

    else:
        insert_endpoint(diagram, node1, pos1, (start_ep[0], start_ep[1]))
        insert_endpoint(diagram, start_ep[0], start_ep[1], (node1, pos1))
        insert_endpoint(diagram, node2, pos2, (free_ep[0], free_ep[1]))
        insert_endpoint(diagram, free_ep[0], free_ep[1], (node2, pos2))

    if start == True:
        return (node1, pos1)


def crossing_to_arc(k, crossing, parity) -> None:
    """
    From knotpy:
    Remove a crossing and join two of its arcs into one (remove it and connect the adjacent endpoints).
    This ignores the non-parity endpoints and connect the parity endpoints.

    Args:
        k (Diagram): Diagram to modify.
        crossing (Hashable): Crossing node identifier.
        parity (int): Use 0 (even) or 1 (odd) side to connect.
    """
    if not isinstance(k.nodes[crossing], kp.Crossing):
        raise TypeError("Variable crossing must be of a crossing")


    # connect two arcs of a knot
    ep_a = k.nodes[crossing][parity]
    ep_b = k.nodes[crossing][parity + 2]
    k.set_endpoint(ep_a, ep_b)
    k.set_endpoint(ep_b, ep_a)

    # remove the crossing
    k.remove_node(crossing, remove_incident_endpoints=False)

def delete_path(diagram, max_path):
    """Removes a path (strand) from a planar diagram.

    The function detects local pairs of consecutive endpoints in `max_path` that belong to the same
    node and correspond to an internal arc that must be removed.

    These nodes are collected and then updated by converting the affected crossings into arcs
    (`crossing_to_arc`), effectively deleting the old strand from the diagram.

    Args:
        diagram : PlanarDiagram
            The diagram to update.
        max_path : list of Endpoint
            The strand to be removed.

    Returns:
        PlanarDiagram:
            Updated diagram without the given path.
    """
    to_remove = []

    for i in range(len(max_path) - 1):
        ep1 = max_path[i]
        ep2 = max_path[i+1]

        if (ep1.node == ep2.node and ep1.position == (ep2.position + 2) % 4):
            to_remove.append((ep1.node, (ep1.position + 1) % 2))

    for node, parity in to_remove:
        if node in diagram.nodes:
            crossing_to_arc(diagram, node, parity)

    return diagram


def perform_strand_flip(diagram, max_path, alternative_path, kind, outer = False):
    """Performs a strand flip in a planar diagram by replacing an existing strand (`max_path`)
    with a new strand defined by `alternative_path`.

    The operation consists of inserting the new core path, deleting the old strand, and connecting
    the core of the new strand back into the diagram in the appropriate places by attaching its endpoints.

    If `outer=True`, the function also records which endpoints of the newly created strand appear on the outer face.

    Args:
        diagram : PlanarDiagram
            The diagram to be modified.
        max_path : list of Endpoint
            The original strand being replaced.
        alternative_path : list of (Endpoint, turn)
            The alternative strand placement.
        kind : str
            Specifies how the new strand passes at crossings ("over" or "under").
        outer : bool, optional
            Whether outer-face information is tracked during the construction of the new strand.   

    Returns:
        new_outer (optional): list of newly inserted endpoints belonging to the outer face if `outer=True`
    """
    if outer == True:
        start_ep, free_ep, new_outer = insert_path_core(diagram, alternative_path, kind, max_path, outer = True)
    else:
        start_ep, free_ep = insert_path_core(diagram, alternative_path, kind, max_path)
    delete_path(diagram, max_path)
    if outer == True and new_outer and new_outer[0] == "S":
        ep1 = attach_ends(diagram, alternative_path, max_path, start_ep, free_ep, start = True)
        new_outer[0] = ep1
    else:
        attach_ends(diagram, alternative_path, max_path, start_ep, free_ep)        
    if outer == True:
        return new_outer


def find_and_perform_strand_flip(diagram, outer = False):
    """Finds and performs a strand flip move in the diagram if possible.

    The function first searches for a strand that uses only one type of crossing
    transitions ("over" or "under") and an alternative placement of this strand
    that produces fewer crossings than the original one. 
    Then the strand flip is performed by replacing the old strand with the new one.

    Args:
        diagram : PlanarDiagram
            The diagram to be modified.
        outer : bool, optional
            If True, additionally tracks endpoints on the outer face during the operation.

    Returns:
        (bool, optional):
            - True if a strand flip was performed, otherwise False
            - Outer-face information if `outer=True`, otherwise None
    """
    for kind in ("over", "under"):
        result = find_strand_flip_move(diagram, kind)
        max_path, alternative_path = result
        if max_path and alternative_path:
            if outer == True:
                new_outer = perform_strand_flip(diagram, max_path, alternative_path, kind, outer = True)
                if new_outer:
                    return True, new_outer

            else:
                perform_strand_flip(diagram, max_path, alternative_path, kind, outer = False)
            return True, None
    return False, None


if __name__ == "__main__":
    #file = "Re_Konsultacje/tri10_knots_reduced_inc3.txt"
    #main(file)
    pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    D = kp.from_pd_notation(pd_text)
    find_and_perform_strand_flip(D)
