#!!! description? two times slower(but cleaner) from find_strand_flip_move_old
import random
import re
import heapq
from collections import defaultdict, deque
import knotpy as kp
from itertools import combinations
from knotpy.classes.endpoint import Endpoint

def find_path_of_type(diagram, start, end=None, allowed_type={"over"}):#!!!! zmeinione na end=None
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


def min_crossings_path(diagram, start_endpoints, target_endpoints, blocked_transitions, randomize = False):
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

    if randomize == True:
        best_cost = float("inf")
        end_states = []

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

        if randomize and cost > best_cost:
            break

        if randomize == False:
            if endpoint in target_endpoints or twin(endpoint) in target_endpoints:
                end_state = (endpoint, last_turn)
                break
        else:
            if endpoint in target_endpoints or twin(endpoint) in target_endpoints:
                if cost < best_cost:
                    best_cost = cost
                    end_states = [(endpoint, last_turn)]
                elif cost == best_cost:
                    end_states.append((endpoint, last_turn))
                continue

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


    if randomize == False:
        if end_state is None:
            return None, None

    else:
        if not end_states:
            return None, None


        end_state = random.choice(end_states)
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

def min_between_nodes(diagram, max_path, randomize = False):
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

    d, path = min_crossings_path(diagram, start_endpoints, target_endpoints, blocked_transitions, randomize = randomize)

    if d is not None:
        length = (d + 1)*2
        if best is None or length < best:
            best = length
            best_path = path

    if best is None:
        return None, None

    return best, best_path


def find_strand_flip_move(diagram, allowed_type, randomize = False):
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

        min_any, alternative_path = min_between_nodes(diagram, max_path, randomize = randomize)


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


def insert_crossing(diagram, last_ep, turn, from_ep=None, to_ep=None, kind="under"):
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
    else:
        free_endpoints.append((x, first))

    if to_ep is not None:
        diagram.set_endpoint((x, second), (to_ep[0], to_ep[1]))
    else:
        free_endpoints.append((x, second))

    return free_endpoints

def insert_path_core(diagram, path, kind , max_path = None, outer = False):
    def need_crossing(prev_ep, prev_turn, ep, turn):
        if turn != prev_turn: #nie wstawiamy tam gdzie zniknie
             if max_path is None or (max_path and prev_ep not in max_path[1:-1]):
                return prev_ep
        elif prev_ep.node == ep.node and ep.node in diagram.crossings and (prev_ep.position + 2) % 4 == ep.position:
            offset = 1 if turn == "R" else -1
            if max_path and diagram.endpoints[(prev_ep.node, (prev_ep.position + offset)%4)] not in max_path[1:-1]:
                return diagram.endpoints[(prev_ep.node, (prev_ep.position + offset)%4)]
        return None

    start_ep = None
    free_ep = None

    prev_ep, prev_turn = path[0]

    if outer == True:
        new_outer=[]
        out = False
        if prev_ep.attr.get("outer") or diagram.twin(prev_ep).attr.get("outer"): #najpierw trzeba sie skapnac czy zaczynamy w srodku czy na zewnatrz
            ep, turn = path[1]
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
                    new_outer.append("S")#dodac start ale go tu nie ma trzeba potem

    for ep, turn in path[1:]:
        ep_cross = need_crossing(prev_ep, prev_turn, ep, turn)
        if ep_cross is not None:
            if outer == True:
                if ep_cross.attr.get("outer") or diagram.twin(ep_cross).attr.get("outer"): 
                    if out == True:
                        out = False
                    else:
                        out = True
                elif out == True: #wchodzimy do nieoznaczonego(po usuneciu outer np.)
                    out = False

            use_turn = turn
            if prev_turn != turn:
                if ep_cross == ep:
                    use_turn = prev_turn

            free = insert_crossing(diagram, ep_cross, use_turn, free_ep, None, kind)


            if not free:
                raise ValueError("No free endpoints")

            if len(free) == 2 and start_ep is None:
                start_ep = free[0]

            free_ep = free[-1]

            if outer == True and out == True:
                new_outer.append(free_ep)

        elif outer == True and prev_ep.node == ep.node and ep.node in diagram.crossings and (prev_ep.position + 2) % 4 == ep.position: #cross ale z tym co znika
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
    """
    Wstaw endpoint do node na pozycję `pos` i napraw wszystkie twin referencje.

    Args:
        diagram: Diagram (knotpy)
        node: node do którego wstawiamy
        pos: indeks wstawienia
        new_ep: Endpoint (node, position) lub tuple
    """
    if not isinstance(new_ep, Endpoint):
        new_ep = Endpoint(new_ep[0], new_ep[1])
    
    if node in diagram.vertices:
        endpoints=[]
        for i, ep in enumerate(diagram.nodes[node]):
            if ep.node in diagram.nodes:
                endpoints.append(ep)
            else:
                remove = (node, i) #usuwamy jak natrafimy na zły


        diagram.remove_endpoint(remove)
        endpoints.insert(pos, new_ep)

        diagram._nodes[node]._inc = endpoints

        # --- 2. FIX TWINÓW dla przesuniętych endpointów ---
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
        if twin is None or twin.node not in diagram.nodes:
            diagram.set_endpoint((node, pos), new_ep)
        else:
            raise ValueError("cannot overwrite legitimate endpoint")

def decide_insert_place_2ep(del_pos, first_pos, second_pos):
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


def find_and_perform_strand_flip(diagram, outer = False, randomize = False):
#    knot_diagrams = []
#    diagram1 = diagram.copy()
#    diagram1.name = kp.to_pd_notation(diagram1)
#    knot_diagrams.append(diagram1)
    for kind in ("over", "under"):
        result = find_strand_flip_move(diagram, kind, randomize = randomize)
        max_path, alternative_path = result
        if max_path and alternative_path:
            if outer == True:
                new_outer = perform_strand_flip(diagram, max_path, alternative_path, kind, outer = True)
                if new_outer:
                    return True, new_outer

            else:
                perform_strand_flip(diagram, max_path, alternative_path, kind, outer = False)
            return True, None
        #    knot_diagrams.append(diagram)

        #    diagram.name = kp.to_pd_notation(diagram)
        #    break


    #output_path = "C:/Users/gozma/Desktop/uw_pliki/licencjat/flip_strand.pdf"
    #kp.export_pdf(knot_diagrams, output_path)
    #print(f"Zapisano do pliku: {output_path}")


    return False, None


if __name__ == "__main__":
    #file = "Re_Konsultacje/tri10_knots_reduced_inc3.txt"
    #main(file)
    pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    D = kp.from_pd_notation(pd_text)
    find_and_perform_strand_flip(D)
