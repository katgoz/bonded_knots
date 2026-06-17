import knotpy as kp
from find_strand_flip_move_new import min_crossings_path, insert_path_core, find_and_perform_strand_flip, find_path_of_type, min_between_nodes, perform_strand_flip
from find_strand_flip_move_new import min_crossings_path_all
from knotpy.algorithms.sanity import sanity_check_raise_exception
import sys
import traceback
from knotpy.classes.endpoint import Endpoint

pd_text = 'V(0,1,2);V(3,4,5);V(6,7,8);V(0,6,9);X(2,10,3,11);X(11,5,12,7);X(13,14,10,1);X(8,12,4,15);X(9,15,14,13)'
#"V[0,1,2],V[0,3,4],V[5,3,6],V[7,8,9],X[10,11,12,4],X[13,14,11,10],X[1,12,7,15],X[14,13,5,8],X[6,2,15,9] "
"V[0,1,2],V[0,3,4],X[3,2,5,6],X[5,7,8,9],X[6,9,10,11],X[7,14,12,8],X[11,10,12,13],X[14,1,16,15],X[15,16,4,13]"
D = kp.from_pd_notation(pd_text)

def strand_components(diagram):
    """Finds strand components in a PlanarDiagram.

    Performs a depth-first search (DFS) over endpoints, grouping nodes into connected components.
    Traversal follows edges (via twin endpoints) and passes through nodes depending on their type:
    - crossings: only straight-through transitions (0↔2, 1↔3)
    - vertices: all incident endpoints are allowed

    Each component is returned as a set of node labels that are connected under these rules.

    Args:
    diagram : PlanarDiagram

    Returns:
    list[set]: A list of components, where each component is a set of node labels.

    Example:
    >>> pd_text = "V[0,1,2],V[0,3,4],V[1,5,6],V[4,7,5],X[8,9,10,2],X[3,10,11,12],X[6,13,9,8],X[13,7,12,11]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> print(strand_components(diagram))

    [{'f', 'c', 'a', 'd', 'b', 'h', 'e', 'g'}, {'g', 'e', 'h', 'f'}]
    """
    visited = set()
    components = []

    for ep in diagram.endpoints:
        if ep in visited:
            continue

        comp = set()
        stack = [ep]

        while stack:
            curr = stack.pop()
            if curr in visited:
                continue

            visited.add(curr)
            comp.add(curr.node)

            # przejście po łuku
            twin = diagram.twin(curr)
            if twin not in visited:
                stack.append(twin)

            # przejście przez crossing (TYLKO dozwolone)
            if curr.node in diagram.crossings:
                pos = curr.position
                if pos == 0:
                    nxt = diagram.endpoints[(curr.node, 2)]
                elif pos == 2:
                    nxt = diagram.endpoints[(curr.node, 0)]
                elif pos == 1:
                    nxt = diagram.endpoints[(curr.node, 3)]
                else:
                    nxt = diagram.endpoints[(curr.node, 1)]

                if nxt not in visited:
                    stack.append(nxt)

            elif curr.node in diagram.vertices:
                # wszystkie endpointy
                for ep2 in diagram.endpoints[curr.node]:
                    if ep2 not in visited:
                        stack.append(ep2)

        components.append(comp)

    return components



# !!! NOTE: Sorting faces before lexicographic comparison would make this deterministic

def get_outerplanar_endpoints(diagram, node = None, subset = None, add_endpoints = None): 
    """Selects and marks an outer face in a PlanarDiagram.

    The function starts from all faces in the diagram and progressively narrows them down:

    1. If there are already endpoints marked as "outer", it keeps only those faces that contain all of them.
    2. If add_endpoints is provided, it keeps only faces that contain each of these endpoints
       or their twins (this allows updating/expanding the outer face consistently).
    3. If node is given, it further restricts to faces that contain this node
       (so that this node lies on the outer face).
    4. From the remaining faces, it selects those with the maximum number of vertices.
    5. If subset is provided (typically the previous outer face), it prefers faces that contain
       as many nodes from this subset as possible, to keep the outer face stable between steps
       instead of frequently switching to a different one.
    6. Finally, from the remaining candidates, it chooses the face with the largest number of endpoints,
       and in case of a tie, the lexicographically smallest one.

    All endpoints of the selected face are marked with attribute "outer" = True.

    Args:
    diagram : PlanarDiagram
    node : node label, optional
        If provided, restricts candidate faces to those containing this node.
    subset : iterable of node labels, optional
        If provided, prefers faces containing the largest number of nodes from this subset.
    add_endpoints : iterable of Endpoint, optional
        If provided, restricts faces to those containing each endpoint or its twin.

    Returns:
    tuple: The selected outer face (tuple/list of endpoints).

    Raises:
    ValueError:
        If no face satisfies required constraints (e.g. no face contains given node
        or no face matches previously marked outer endpoints).

    Example:
    >>> pd_text = "V[0,1,2],V[0,3,4],V[1,5,6],V[4,7,5],X[8,9,10,2],X[3,10,11,12],X[6,13,9,8],X[13,7,12,11]"
    >>> diagram = kp.from_pd_notation(pd_text)
    >>> print("All node labels: ", list(diagram.nodes))
    >>> print("All possible faces: ", list(diagram.faces))

    >>> outer = get_outerplanar_endpoints(
            diagram,
            node='c',
            subset=['a', 'b', 'c', 'd'],
            add_endpoints=[
                diagram.endpoints[('a', 1)]
            ]
        )

    >>> print("Chosen face: ", outer)

    All node labels:  ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
    All possible faces:  [(a1, b0, d0, c1), (d2, h1, g1, c2), (g0, e0, a2, c0), (g3, e1), (f2, e2, g2, h0), (f1, b1, a0, e3), (h2, d1, b2, f0), (h3, f3)]
    Chosen face: (a1[outer], b0[outer], d0[outer], c1[outer])
    """
    external_endpoints = [ep for ep in diagram.endpoints if ep.attr.get("outer")]
    faces = list(diagram.faces)

    working_faces = faces

    if external_endpoints:
        working_faces = [face for face in working_faces if all((ep in face) or (diagram.twin(ep) in face) for ep in external_endpoints)]
        """
        working_faces = [face for face in working_faces if set(face).issuperset(external_endpoints)]
        """
        if not working_faces:
            raise ValueError("No external face candidates")

    if add_endpoints:
        working_faces = [face for face in working_faces if all((ep in face) or (diagram.twin(ep) in face) for ep in add_endpoints)]

    if node is not None:
        working_faces = [
            face for face in working_faces
            if any(ep.node == node for ep in face)
        ]

        if not working_faces:
            raise ValueError("No face contains given node")

    def node_score(face):
        return len({ep.node for ep in face if ep.node in diagram.vertices})

    best_node_score = max(node_score(face) for face in working_faces)

    working_faces = [
        face for face in working_faces
        if node_score(face) == best_node_score
    ]

    if subset is not None:
        subset = set(subset)

        def score(face):
            return len({ep.node for ep in face} & subset)

        max_score = max(score(face) for face in working_faces)

        working_faces = [
            face for face in working_faces
            if score(face) == max_score
        ]
         
    """   
    external_face = min(
        working_faces,
        key=lambda face: (-len(face), tuple(face))
    )
    """
    external_face = min(
        working_faces,
        key=lambda face: (
            -len(face),
            tuple(sorted((ep.node, ep.position) for ep in face))
        )
    )


    remove_endpoints = [ep for ep in diagram.endpoints if ep.attr.get("outer")]
    clear_outer_endpoints(remove_endpoints, remove_endpoints)

    for ep in external_face:
    	ep.attr["outer"] = True

    return external_face

def clear_outer_endpoints(old_face, remove_endpoints):
    """Removes the "outer" attribute from selected endpoints.

    The function iterates over the current outer face and removes the "outer"
    flag only from those endpoints that are included in remove_endpoints.

    Args:
    old_face : iterable of Endpoint
        Current outer face endpoints.
    remove_endpoints : iterable of Endpoint
        Subset of endpoints from old_face that should lose the "outer" attribute.

    Returns:
    None
    """
    for ep in old_face:
    	if ep in remove_endpoints:
        	ep.attr.pop("outer", None)


def closest_node_to_outer_face(diagram):
    """Finds a shortest path from the outer face to the nearest inner node in a PlanarDiagram.

    The function first determines the current outer face of the diagram and extracts all nodes
    belonging to it. It then identifies inner nodes (vertices not present on the outer face)
    and collects all their endpoints as potential targets.

    Using a shortest-path search in the diagram, it computes a minimal-crossing path from any
    outer endpoint to any endpoint belonging to an inner node.

    Args:
    diagram : PlanarDiagram
    knot_diagrams : unused
        Present for compatibility with the broader pipeline; not used in this function.

    Returns:
    list[tuple[Endpoint, str]]:
        A path represented as a sequence of (endpoint, turn) pairs connecting the outer face
        to the nearest inner node.
    
    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,8],V[9,10,11],X[12,5,7,2],X[1,11,3,12],X[0,6,13,9],X[8,4,10,13]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> outer = get_outerplanar_endpoints(D)
    >>> print("outer:", outer)
    >>> path = closest_node_to_outer_face(D)
    >>> print("path:", path)

    outer: (b1[outer], f2[outer], d2[outer], h2[outer])
    path: [(b1[outer], 'R'), (b2, 'R'), (e1, 'R'), (e2, 'R'), (c1, 'R')]
    """
    outer_endpoints = list(get_outerplanar_endpoints(diagram))
    outer_nodes = {ep.node for ep in outer_endpoints}
    inner_nodes = [n for n in diagram.vertices if n not in outer_nodes]
    inner_endpoints = [ep for n in inner_nodes for ep in diagram.endpoints[n]]


    cost, path = min_crossings_path(
        diagram,
        start_endpoints=outer_endpoints,
        target_endpoints=inner_endpoints,
        blocked_transitions={}
    )


    return path 



def closest_node_to_outer_face_all(diagram, max_paths_per_target=1):
    outer_endpoints = list(get_outerplanar_endpoints(diagram))
    outer_nodes = {ep.node for ep in outer_endpoints}

    inner_nodes = [n for n in diagram.vertices if n not in outer_nodes]
    inner_endpoints = [ep for n in inner_nodes for ep in diagram.endpoints[n]]

    results = min_crossings_path_all(
        diagram,
        start_endpoints=inner_endpoints,
        target_endpoints=outer_endpoints,
        blocked_transitions={}
    )

    if results is None:
        return []

    # wyciągamy same ścieżki
    paths = [path for cost, path in results]



    """
    # 🔥 KLUCZ: ograniczenie liczby ścieżek
    selected = []
    seen_targets = set()

    for path in paths:
        end_ep = path[-1][0]
        key = frozenset([end_ep, diagram.twin(end_ep)])

        if key not in seen_targets:
            selected.append(path)
            seen_targets.add(key)

        if len(selected) >= max_paths_per_target:
            break
    """

    def path_key(path):
        return tuple(
            (ep.node, ep.position, turn)
            for ep, turn in path
        )
    return sorted(paths, key=path_key)#selected

def node_in_multiple_components(node, components):
    """Checks whether a given node appears in more than one connected component.

    The function iterates over all provided components and counts how many of them contain
    the given node. It returns True as soon as the node is found in at least two different
    components, otherwise returns False.

    Args:
    node : node label
        Node label to check.
    components : iterable of sets
        Collection of connected components, where each component is a set of node labels; typically computed using strand_components(diagram).

    Returns:
    bool:
        True if the node appears in more than one component, False otherwise.

    Example:
    >>> pd_text = "V[0,1,2],V[0,3,4],V[1,5,6],V[4,7,5],X[8,9,10,2],X[3,10,11,12],X[6,13,9,8],X[13,7,12,11]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> components = strand_components(D)
    >>> print(node_in_multiple_components('a', components))
    >>> print(node_in_multiple_components('e', components))

    False
    True
    """
    seen = 0
    for comp in components:
        if node in comp:
            seen += 1
            if seen > 1:
                return True
    return False


def over_or_under(diagram, node):
    """Determines whether a vertex is predominantly over or under at crossings.

    If a vertex has a direct connection to a crossing, this connection is counted as either "over" or "under"
    depending on the position at the crossing. Connections to crossings belonging to different strand components are ignored.

    The function returns which type occurs more often.

    Args:
    diagram : PlanarDiagram
    node : node label
        Node to classify.

    Returns:
    str:
        "over" if over-count is greater than under-count, otherwise "under".

    Example:
    >>> pd_text = "V[0,1,2],V[0,3,4],X[1,5,6,7],X[8,6,5,4],X[7,8,3,2]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> print(D)
    >>> print(over_or_under(D, 'a'))

    Diagram a → V(b0 c0 e3), b → V(a0 e2 d3), c → X(a1 d2 d1 e0), d → X(e1 c2 c1 b2), e → X(c3 d0 b1 a2)
    under
    """
    under=0
    over=0
    components = strand_components(diagram)

    for ep in diagram.endpoints[node]:
        twin = diagram.twin(ep)
        twin_node, twin_pos = twin.node, twin.position
        if twin_node in diagram.crossings:
            if not node_in_multiple_components(twin_node, components):
                if twin_pos in (0,2):
                    under+=1
                else:
                    over+=1
    if over>under:
        return "over"
    else:
        return "under"


def drag_node_out(diagram, path, kind, knot_diagrams):
    """Moves a node from the interior of the diagram to the outer face by reconstructing its connections along a given path.

    The function takes a path (typically produced by closest_node_to_outer_face) and uses it to
    systematically relocate a node to the outer face by locally rewiring the diagram.

    At the beginning, the first element of the path is modified to enforce a crossing with the outer face,
    ensuring that the node is pushed outward and becomes exposed to the boundary of the diagram.

    Then, along the path, the function builds new strand structures (3 strands for a vertex, 4 for a crossing).
    New crossings are created according to the specified kind ("over" or "under").

    Finally, the constructed strands are connected together on the outside, forming the extracted node
    in its new outer position. On the inside, the remaining ends are connected to the free twin endpoints
    left behind by the original node, completing the rerouting of all connections.

    Args:
    diagram : PlanarDiagram
        Diagram being modified in-place.
    path : list[tuple[Endpoint, str]]
        Path from outer face to the node being dragged out, where the second element indicates L/R turn.
    kind : str
        Crossing type used during reconstruction ("over" or "under").
    knot_diagrams : list
        Container for storing intermediate diagram states.

    Returns:
    None

    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,8],V[9,10,11],X[12,5,7,2],X[1,11,3,12],X[0,6,13,9],X[8,4,10,13]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> print("Before:", get_outerplanar_endpoints(D))
    >>> path = closest_node_to_outer_face(D)

    >>> ep, _ = path[-1]
    >>> kind = over_or_under(D, ep.node)

    >>> drag_node_out(D, path, kind, knot_diagrams=[])
    >>> print("After dragging out node", ep.node, ": ", get_outerplanar_endpoints(D))
    
    Before: (a0[outer], e3[outer], c1[outer], g1[outer])
    After dragging out node d :  (d0[outer], k2[outer], a0[outer], e3[outer], c1[outer], g1[outer], i3[outer])
    """

    first = path[0]
    outer_endpoints = list(get_outerplanar_endpoints(diagram))
    all_outer_nodes = len(outer_endpoints)


    turn = 'L' if first[1] == 'R' else 'R'
    path[0] = (first[0], turn)
    if path[1][0] == diagram.twin(first[0]):
        path[1] = (path[1][0], turn)
        ep_1 = path[1][0]
        ep_2 = path[2][0]
        i=2
        while ep_2.node == ep_1.node and ep_1.node in diagram.crossings and ep_2.position == (ep_1.position + 2)%4:
            path[i] = (ep_2, turn)
            ep_1 = ep_2
            ep_2 = path[i+1][0]
        path[i+1] = (ep_2, turn)

    if len(path) >= 2 and path[-2][0].node == path[-1][0].node:
        drag_ep = path[-2][0]
    else:
        drag_ep = path[-1][0] #ep of a node that we will drag this node out by

    node = drag_ep.node
    end_endpoints = []
    endpoints = diagram.endpoints[node]


    if path[-1][1] == 'R':
        i = (drag_ep.position + 1) % len(endpoints)
    else:
        i = drag_ep.position

    order = endpoints[i:] + endpoints[:i]

    if path[-1][1] == 'L':
        order = order[::-1]

    for ep in order:
        start_ep, free_ep = insert_path_core(diagram, path, kind)
        diagram.set_endpoint(free_ep, diagram.twin(ep)) #free/twin
        diagram.set_endpoint(diagram.twin(ep), free_ep)
        diagram.set_endpoint(ep, start_ep)
        diagram.set_endpoint(start_ep, ep) #start/ep


        for ep1 in diagram.endpoints[free_ep[0]]:
            ep1.attr.pop("outer", None)

        for ep1 in diagram.endpoints[start_ep[0]]:
            ep1.attr.pop("outer", None)

    get_outerplanar_endpoints(diagram)



def drag_node_out_all(diagram, path, kind, knot_diagrams):
    """Moves a node from the interior of the diagram to the outer face by reconstructing its connections along a given path.

    The function takes a path (typically produced by closest_node_to_outer_face) and uses it to
    systematically relocate a node to the outer face by locally rewiring the diagram.

    At the beginning, the first element of the path is modified to enforce a crossing with the outer face,
    ensuring that the node is pushed outward and becomes exposed to the boundary of the diagram.

    Then, along the path, the function builds new strand structures (3 strands for a vertex, 4 for a crossing).
    New crossings are created according to the specified kind ("over" or "under").

    Finally, the constructed strands are connected together on the outside, forming the extracted node
    in its new outer position. On the inside, the remaining ends are connected to the free twin endpoints
    left behind by the original node, completing the rerouting of all connections.

    Args:
    diagram : PlanarDiagram
        Diagram being modified in-place.
    path : list[tuple[Endpoint, str]]
        Path from outer face to the node being dragged out, where the second element indicates L/R turn.
    kind : str
        Crossing type used during reconstruction ("over" or "under").
    knot_diagrams : list
        Container for storing intermediate diagram states.

    Returns:
    None

    Example:
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,8],V[9,10,11],X[12,5,7,2],X[1,11,3,12],X[0,6,13,9],X[8,4,10,13]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> print("Before:", get_outerplanar_endpoints(D))
    >>> path = closest_node_to_outer_face(D)

    >>> ep, _ = path[-1]
    >>> kind = over_or_under(D, ep.node)

    >>> drag_node_out(D, path, kind, knot_diagrams=[])
    >>> print("After dragging out node", ep.node, ": ", get_outerplanar_endpoints(D))
    
    Before: (a0[outer], e3[outer], c1[outer], g1[outer])
    After dragging out node d :  (d0[outer], k2[outer], a0[outer], e3[outer], c1[outer], g1[outer], i3[outer])
    """
    drag_node = path[0][0].node
    if path[0][1] == "A": #!!!zawsze L?
        for i, state in enumerate(path):
            path[i] = (path[i][0], "L")

    last = path[-1]

    outer_endpoints = list(get_outerplanar_endpoints(diagram))
    all_outer_nodes = len(outer_endpoints)

    if path[-2][0] != diagram.twin(last[0]):
        path.append((diagram.twin(last[0]), last[1]))

    last_ep, last_turn = path[-1]
    prev_ep, prev_turn = path[-2]
    out = False
    if prev_ep.attr.get("outer") or diagram.twin(prev_ep).attr.get("outer"):
        if last_ep.attr.get("outer") or diagram.twin(last_ep).attr.get("outer"):
            node_obj = diagram.nodes[prev_ep.node]
            dg = node_obj.degree()
            if (
                (last_ep.node == prev_ep.node) or 
                (last_ep.node != prev_ep.node and (
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
        
        elif last_ep.node == prev_ep.node and last_ep.node in diagram.crossings and last_ep.position == (prev_ep.position + 2)%4 and (
                   (prev_turn == "R" and (
                        diagram.endpoints[(prev_ep.node, (prev_ep.position+1)%4)].attr.get("outer") == True or
                        diagram.twin(diagram.endpoints[(prev_ep.node, (prev_ep.position+1)%4)]).attr.get("outer") == True
                    )) or 
                    (prev_turn == "L" and (
                        diagram.endpoints[(prev_ep.node, (prev_ep.position-1)%4)].attr.get("outer") == True or 
                        diagram.twin(diagram.endpoints[(prev_ep.node, (prev_ep.position-1)%4)]).attr.get("outer") == True
                    ))
              
            ): #po and dopisalam
            out = True


    if out == False:
        if last[1] == 'R':
            turn = 'L'
            pos = (path[-1][0].position - 1) % (len(diagram.endpoints[path[-1][0].node]))
            add_ep = Endpoint(path[-1][0].node, pos)
        else:
            turn = 'R'
            pos = (path[-1][0].position + 1) % (len(diagram.endpoints[path[-1][0].node]))
            add_ep = Endpoint(path[-1][0].node, pos)
        path.append((add_ep, turn))


    if len(path) >= 2 and path[1][0].node == path[0][0].node:
        drag_ep = path[1][0]
    else:
        drag_ep = path[0][0] #ep of a node that we will drag this node out by

    node = drag_ep.node
    end_endpoints = []
    endpoints = diagram.endpoints[node]

    if path[0][1] == 'L':
        i = (drag_ep.position + 1) % len(endpoints)
    else:
        i = drag_ep.position

    order = endpoints[i:] + endpoints[:i]

    if path[0][1] == 'L':
        order = order[::-1]

    cross_with_outer=[]
    for ep in order:
        free_ep, start_ep, new_alt_path = insert_path_core(diagram, path, kind, alt=True) 
        path = new_alt_path
        diagram.set_endpoint(free_ep, diagram.twin(ep)) #free/twin
        diagram.set_endpoint(diagram.twin(ep), free_ep)
        diagram.set_endpoint(ep, start_ep)
        diagram.set_endpoint(start_ep, ep) #start/ep

        cross_with_outer.append(start_ep[0])

    for clean_node in cross_with_outer:
        for ep1 in diagram.endpoints[clean_node]:
            ep1.attr.pop("outer", None)


    get_outerplanar_endpoints(diagram, node=drag_node)

def add_diagram_state(diagram, knot_diagrams):
    """Creates a validated copy of the diagram and stores it in the history list.

    The function copies the diagram, assigns it a PD-based name, runs a sanity check,
    recomputes the outer face, and appends the result to knot_diagrams.
    If validation fails, the exception is printed and re-raised.

    Args:
    diagram : PlanarDiagram
    knot_diagrams : list
        History container for diagram states.

    Returns:
    None
    """
    d_copy = diagram.copy()
    d_copy.name = kp.to_pd_notation(d_copy)
    try:
        sanity_check_raise_exception(d_copy)
        get_outerplanar_endpoints(d_copy)
    except Exception:
        import traceback
        traceback.print_exc()
        raise

    knot_diagrams.append(d_copy)

def change_outer(diagram, new_outer, drag_node, knot_diagrams): 
    """Sets a new outer face containing the specified new_outer elements and the dragged node (drag_ep),
    while preserving as much of the previous outer face structure as possible.

    The function first removes all existing outer markings and stores the previous outer face as a set
    of nodes (old outer nodes). It then constructs constraints for selecting the new outer face:

    - nodes from the previous outer face are kept as a reference,
    - new_outer nodes are added to the previous outer-face reference to guide selection of the new outer face,
    - corresponding endpoints from new_outer are converted into add_endpoints constraints,
    - drag_ep.node is passed to ensure the dragged node remains visible and is not hidden during selection.

    Finally, get_outerplanar_endpoints is used to recompute the outer face under these constraints,
    favoring continuity with the previous outer structure.

    Args:
    diagram : PlanarDiagram
    new_outer : iterable of (node, position) or None
        Elements guiding the new outer face selection.
    drag_ep : Endpoint
        Node endpoint that must remain considered during recomputation.
    knot_diagrams : list
        History container (not used directly).

    Returns:
    None
    """
    remove_endpoints = [ep for ep in diagram.endpoints if ep.attr.get("outer")]
    old_outer_nodes = [ep1.node for ep1 in remove_endpoints]
    if new_outer:
        for ep2 in new_outer:
            old_outer_nodes.append(ep2[0])
    add_endpoints = []
    if new_outer:
        for ep_tuple in new_outer:
            add_endpoints.append(diagram.endpoints[(ep_tuple[0], ep_tuple[1])])
    clear_outer_endpoints(remove_endpoints, remove_endpoints)
    get_outerplanar_endpoints(diagram, drag_node, old_outer_nodes, add_endpoints)

def reduce_strand_flip(diagram, knot_diagrams, dont_cover = None, outer = True):
    """Repeatedly applies strand flip reductions until no further updates are possible.

    The function iteratively searches for and performs strand flip moves on the diagram
    (using find_and_perform_strand_flip with outer=True). After each successful update,
    the diagram state is optionally adjusted in terms of its outer face and then stored.

    If dont_cover is provided, the outer face is updated after each modification so that
    the specified endpoint is not hidden during subsequent outer-face recomputation.

    Each intermediate diagram state is saved into knot_diagrams.

    Args:
    diagram : PlanarDiagram
        Diagram being modified in-place.
    knot_diagrams : list
        History container storing successive diagram states.
    dont_cover : Endpoint, optional
        Endpoint that should remain visible and not be covered by the outer face updates.

    Returns:
    None
    """
    updated = True
    while updated:
        if outer == True:
            updated, new_outer = find_and_perform_strand_flip(diagram, outer = True)
            if updated == True:
                if dont_cover:
                    change_outer(diagram, new_outer, dont_cover, knot_diagrams)
                else:
                    change_outer(diagram, new_outer, None, knot_diagrams)
            #    add_diagram_state(diagram, knot_diagrams)
        else:
            updated, new_outer = find_and_perform_strand_flip(diagram, outer = False)


def reduce_drag_ep(diagram, drag_node, kind, knot_diagrams, dont_cover = None):
    """Attempts to simplify the newly extracted node by searching for local strand flip moves
    that reduce the complexity of its outgoing strands.

    After a node has been dragged to the outer face, the function checks whether the newly created
    strands originating from this node can be simplified using strand flip operations.

    For each strand leaving the node (i.e. each strand incident to its endpoints), it compares the
    current maximal path of a given type (over/under) with a shorter alternative path. If such a
    simplification exists, a strand flip is performed.

    Optionally, the outer face is updated so that the dragged node remains visible during modifications,
    and each intermediate diagram state is stored in knot_diagrams.

    Args:
    diagram : PlanarDiagram
    drag_node : Node
        Recently moved node (i.e. the node whose outgoing strands are being simplified).
    kind : str
        Crossing type constraint ("over" or "under").
    knot_diagrams : list
        History container for diagram states.
    dont_cover : Endpoint, optional
        Endpoint that should remain visible during outer face updates.

    Returns:
    None
    """
    for ep in diagram.endpoints[drag_node]:
        max_path = find_path_of_type(diagram, ep, allowed_type = kind)
        max_len = len(max_path)

        min_any, alternative_path = min_between_nodes(diagram, max_path)

        if min_any is not None and min_any<max_len:
            new_outer = perform_strand_flip(diagram, max_path, alternative_path, kind, outer = True)
            if dont_cover:
                change_outer(diagram, new_outer, drag_node, knot_diagrams)
        #    add_diagram_state(diagram, knot_diagrams)


def diagram_to_outerplanar(D, knot_diagrams):
    #!!! błedy w drag_node_out
    """Transforms a diagram into an outerplanar form by iteratively extracting inner nodes to the outer face
    and simplifying the resulting structure.

    In each iteration, a node closest to the outer face is selected. A path connecting the outer face to this node
    is computed, and the node is then moved along this path to the outer face of the diagram. This path determines
    how the node is extracted and how new crossings and strands are introduced during the process.

    Before the node is moved, it is classified as "over" or "under" based on its direct interactions with crossings.

    This classification is determined by counting how the node connects to crossings in its immediate neighborhood:
    - if "over" occurs more frequently, the node is classified as "over",
    - otherwise (including ties), it is classified as "under".

    This rule is then used during the extraction process along the chosen path: when the node is moved to the outer face,
    new crossings are created in a way that preserves this selected crossing type consistently along the constructed structure.

    After the node is moved along the path to the outer face:
    - local simplifications are applied to the newly created strands incident to the node (reduce_drag_ep),
    - global strand flip simplifications are applied to remove redundant structure (reduce_strand_flip).

    The process repeats until all vertices lie on the outer face or a maximum number of iterations is reached.
    If the limit is exceeded, the last valid configuration is returned.

    Finally, a sanity check is performed and the canonical form of the resulting diagram is returned.

    Args:
    D : PlanarDiagram
        Input diagram to be transformed.
    knot_diagrams : list
        History container storing successive diagram states.

    Returns:
    PlanarDiagram
        Canonical outerplanar form of the diagram (or last valid state if iteration limit is exceeded).
    """
    #add_diagram_state(D, knot_diagrams)
    reduce_strand_flip(D, knot_diagrams)

    outer_endpoints = list(get_outerplanar_endpoints(D))
    outer_nodes = {ep.node for ep in outer_endpoints}
    inner_nodes = [n for n in D.vertices if n not in outer_nodes]

    i = 0
    max_iter = 100

    while inner_nodes:

        if i >= max_iter:
            print(" Przekroczono limit iteracji")
            return kp.canonical(knot_diagrams[-1])


        path = closest_node_to_outer_face(D)
        ep, turn = path[-1]
        kind = over_or_under(D, ep.node)

        drag_node_out(D, path, kind, knot_diagrams)
        #add_diagram_state(D, knot_diagrams)

        reduce_drag_ep(D, ep.node, kind, knot_diagrams, dont_cover=ep.node)
        reduce_strand_flip(D, knot_diagrams, dont_cover=ep.node)


        outer_endpoints = list(get_outerplanar_endpoints(D))
        outer_nodes = {ep1.node for ep1 in outer_endpoints}
        inner_nodes = [n for n in D.vertices if n not in outer_nodes]

        i += 1

    #sanity_check_raise_exception(D)
    get_outerplanar_endpoints(D)

    return kp.canonical(D)

def all_outer_len(diagram, outer_len):
    diagrams = []
    faces = [face for face in diagram.faces if len(face) == outer_len]

    for face in faces:
        d = diagram.copy()

        # wyczyść outer w kopii
        for ep in d.endpoints:
            ep.attr.pop("outer", None)

        # znajdź odpowiadającą face w kopii
        copy_face = [
            d.endpoint_from_pair((ep.node, ep.position))
            for ep in face
        ]

        # ustaw outer
        for ep in copy_face:
            ep.attr["outer"] = True

        diagrams.append(d)

    return diagrams

def has_vertex_face(diagram):
    all_vertices = set(diagram.vertices)

    for face in diagram.faces:
        face_vertices = {ep.node for ep in face if ep.node in diagram.vertices}

        if face_vertices == all_vertices:
            for ep in diagram.endpoints:
                ep.attr.pop("outer", None)

             # ustaw outer
            for ep in face:
                ep.attr["outer"] = True
            
            #add_diagram_state(diagram, knot_diagrams)
            return True

    return False


def outside(diagram):
    external = {
        ep.node
        for ep in diagram.endpoints
        if ep.attr.get("outer") and ep.node in diagram.vertices
    }

    return external == set(diagram.vertices)

def expand(diagram, knot_diagrams):
    next_states = []
    outer_len = len([
        ep for ep in diagram.endpoints
        if ep.attr.get("outer")
    ])

    for diagram in all_outer_len(diagram, outer_len):

        if outside(diagram):
            continue

        paths = closest_node_to_outer_face_all(diagram, max_paths_per_target=3)
        for path in paths:
            new_diag = diagram.copy()

            ep, _ = path[0]
            kind = over_or_under(new_diag, ep.node)

            #print("drag")
            drag_node_out_all(new_diag, path, kind, knot_diagrams)
            #print("red")
            reduce_drag_ep(new_diag, ep.node, kind, knot_diagrams, dont_cover=ep.node)
            #print("all")

            reduce_strand_flip(new_diag, knot_diagrams, dont_cover=ep.node)


            #explore_outerplanar(new_diag, visited, results, depth+1, max_depth)
            get_outerplanar_endpoints(new_diag)
            next_states.append(new_diag)

    return next_states



from collections import deque

def max_X_face(diagram):
    faces = diagram.faces

    def node_score(face):
        return len({ep.node for ep in face if ep.node in diagram.crossings})

    best_node_score = max(node_score(face) for face in faces)

    faces = [
        face for face in faces
        if node_score(face) == best_node_score
    ]

    for ep in faces[0]:
        ep.attr["outer"] = True

import time


from collections import deque
import time


def explore_seed_merge(seeds, results=[], knot_diagrams=[], max_depth=30):

    visited = set()
    canon_to_seeds = {}

    # każda grupa = SET seedów (STABILNA tożsamość)
    seed_groups = [frozenset({i}) for i in range(len(seeds))]
    group_best = {}

    frontier = deque()

    for seed_id, d in enumerate(seeds):
        max_X_face(d)
        frontier.append((d, 0, frozenset({seed_id})))

    total_seeds = len(seeds)

    # -------------------------
    # GROUP MERGE (UNION)
    # -------------------------
    def add_set(new_set):

        nonlocal seed_groups, group_best

        new_set = frozenset(new_set)

        affected = []
        merged = set(new_set)

        # znajdź grupy które się łączą
        for g in seed_groups:
            if not merged.isdisjoint(g):
                affected.append(g)
                merged |= set(g)

        affected = set(affected)

        # usuń stare grupy
        seed_groups[:] = [g for g in seed_groups if g not in affected]

        merged = frozenset(merged)

        # BEST merge
        pending = []
        for g in affected:
            if g in group_best:
                pending.append(group_best[g])
                group_best.pop(g, None)

        if pending:
            group_best[merged] = min(
                pending,
                key=lambda c: (len(kp.to_pd_notation(c)), kp.to_pd_notation(c))
            )
        else:
            group_best[merged] = None

        seed_groups.append(merged)

    # -------------------------
    # BFS
    # -------------------------
    start_time = time.time()
    TIME_LIMIT = 20

    while frontier:

        if time.time() - start_time > TIME_LIMIT:
            print("⏱ TIME LIMIT REACHED")
            break

        new_frontier = []

        for diagram, depth, origins in frontier:
            #sanity_check_raise_exception(diagram)
            canon = kp.canonical(diagram)

            outer_len = len([ep for ep in diagram.endpoints if ep.attr.get("outer")])

            key = (canon, outer_len)

                # merge seeds by canonical
#            print(canon)
#            print("SEED:", seed_groups)
#            print("BEST:", group_best)
#            print("canon", canon_to_seeds)
            if canon in canon_to_seeds:
                canon_to_seeds[canon] |= origins
                add_set(canon_to_seeds[canon])
            else:
                canon_to_seeds[canon] = set(origins)


            # find group (STABLE)
            gid = None
            for s in origins:
                for g in seed_groups:
                    if s in g:
                        gid = g
                        break
                if gid is not None:
                    break

                # BEST update
            if gid is not None:
                if gid not in group_best:
                    group_best[gid] = canon
                else:
                    old = group_best[gid]

                    p_new = kp.to_pd_notation(canon)
                    p_old = kp.to_pd_notation(old)

                    if (len(p_new), p_new) < (len(p_old), p_old):
                        group_best[gid] = canon

#           print("PO")
#           print("canon", canon_to_seeds)
#            print("SEED:", seed_groups)
#            print("Best:", group_best)
            # stop condition
            if len(seed_groups) == 1 and len(seed_groups[0]) == total_seeds:
                print("🎯 ALL SEEDS MERGED!")

                final_group = seed_groups[0]
                final_canon = group_best.get(final_group)

                print("\nFINAL CANON:")
                print(final_canon)
                print(kp.to_pd_notation(final_canon))

                return True

            # pruning
            if key in visited:
                continue

            visited.add(key)

            if outside(diagram):
                continue

                        

            if depth >= max_depth:
                continue

            for nxt in expand(diagram, knot_diagrams):
                new_frontier.append((nxt, depth + 1, set(origins)))

        frontier = new_frontier

    print("⚠️ NOT FULL MERGE")

    for g in seed_groups:
        print("GROUP:", g)
        print("CANON:", group_best.get(g))
        print(kp.to_pd_notation(group_best.get(g)))
        print("-" * 40)


    return False




#        "V[0,1,2],V[0,3,4],V[1,5,6],X[2,7,8,3],X[4,9,10,11],V[5,11,12],X[13,8,7,6],X[9,13,12,10]",
if __name__ == "__main__":
    #4,5, 6
    #2,3

    #V[0,1,2],V[0,3,4],V[1,5,6],V[2,7,8],X[3,9,10,11],V[4,12,5],V[6,13,7],X[8,14,15,9],X[16,12,11,10],X[16,15,14,13]
    pd_codes=[
        #"V[0,1,2],V[0,3,4],V[1,5,6],X[2,7,8,9],X[3,10,11,12],V[4,13,5],X[14,8,7,6],V[9,15,10],X[16,13,12,11],V[14,16,15]",
        "V[0,1,2],V[0,3,4],V[2,5,3],V[6,7,8],X[7,9,10,11],X[12,10,9,5],X[1,13,14,15],X[15,8,11,12],X[6,14,13,4]",
        "V[0,1,2],V[0,3,4],V[1,5,6],V[7,8,9],X[10,9,11,12],X[2,13,14,7],X[3,10,12,15],X[8,14,13,6],X[15,11,5,4]",
        "V[0,1,2],V[0,3,4],V[1,4,5],X[3,6,7,8],X[9,10,11,2],V[6,12,13],X[10,14,12,11],X[13,15,8,7],X[5,15,14,9]",




        #"V[0,1,2],V[0,3,4],V[1,4,5],V[2,5,3]"
        ]

    results=[]
    seeds=[]
    knot_diagrams=[]
    for pd_code in pd_codes:
        seeds.append(kp.from_pd_notation(pd_code))
    print(explore_seed_merge(seeds, results, knot_diagrams, max_depth=400))
    output_path = "check_outer.pdf"
    #kp.export_pdf(knot_diagrams2, output_path)
