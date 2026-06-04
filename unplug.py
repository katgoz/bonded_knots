from itertools import product
import knotpy as kp
from find_strand_flip_move_new import delete_path
from outer_nodes import reduce_strand_flip
from collections import Counter, defaultdict



def all_unplug_choices(diagram):
    """
    Generate all possible unplugging choices.

    Each vertex selects exactly one of its 3 incident endpoints.

    Returns:
    --------
    iterator of lists: A generator yielding lists of tuples, 
                       where each list looks like [(vertex, removed_endpoint_position), ...]
    """
    vertices = list(diagram.vertices)

    for selection in product(range(3), repeat=len(vertices)):
        yield list(zip(vertices, selection))



def update_choice(choice, v, removed_pos):
    """
    Update the tracking indices of an unplugging choice after an endpoint removal.

    Because removing an endpoint from a vertex causes its remaining incident 
    endpoints to shift their internal positional array indices downward, this 
    function adjusts the stored selection positions to keep them synchronized 
    with the mutated diagram.

    Args:
        choice (list): Current choice tracking list of tuples `[(vertex, pos), ...]`.
        v (str/int): The vertex identifier where an endpoint was removed.
        removed_pos (int): The position index that was removed from vertex `v`.

    Returns:
        list: A updated choice tracking list with adjusted index positions.
    """
    new_choice = []

    for u, pos in choice:
        if u == v:
            if pos == removed_pos:
                continue
            elif pos > removed_pos:
                new_choice.append((u, pos - 1))
            else:
                new_choice.append((u, pos))
        else:
            new_choice.append((u, pos))

    return new_choice

def apply_choice(diagram, choice):
    """
    Apply a specific unplugging choice by tracing and deleting the chosen strands.

    This function clones the diagram and sequentially processes the vertex endpoint 
    selections. For each targeted endpoint, it traces the continuous strand straight 
    through any intermediate crossings using the (pos + 2) % 4 rule until it hits another 
    vertex. The entire traced path and its bounding endpoints are then removed from the 
    graph, dynamically updating the remaining choice indices to prevent drift.

    Args:
        diagram (PlanarDiagram): The original planar diagram template.
        choice (list): List of tuples `[(vertex, pos), ...]` representing the current 
                       unplugging configuration.

    Returns:
        PlanarDiagram: A modified, disconnected copy of the input diagram.
    """

    d = diagram.copy()
    while len(choice) != 0:
        v, pos = choice[0]

        del_ep = d.endpoints[(v, pos)]
        del_twin = d.twin(del_ep)

        remove=[]
        remove.append(del_ep)
        remove.append(del_twin)



        while del_twin.node not in d.vertices:
            del_ep = d.endpoints[(del_twin.node, (del_twin.position+2)%4)]
            del_twin = d.twin(del_ep)
            remove.append(del_ep)
            remove.append(del_twin)


        start_tuple = (remove[0].node, remove[0].position)
        end_tuple = (remove[-1].node, remove[-1].position)

        if start_tuple[0]==end_tuple[0] and start_tuple<end_tuple:
            start_tuple, end_tuple = end_tuple, start_tuple


        if len(remove)>2:
            delete_path(d, remove)
        
        d.remove_endpoint(start_tuple)
        d.remove_endpoint(end_tuple)

        choice = update_choice(choice, start_tuple[0], start_tuple[1])
        choice = update_choice(choice, end_tuple[0], end_tuple[1])



    return d

def clean_diagram_from_invalid_seeds(diagram):
    """
    Remove broken strands and dead-end paths from the diagram.

    This function finds vertices that are mostly disconnected (having fewer than 
    2 active connections). It follows their loose strands straight through any 
    crossings, deletes those paths from the graph, and repeats the process if 
    deleting those paths creates new dead ends.

    Args:
        diagram: The planar diagram to clean up.

    Returns:
        A clean copy of the diagram with all dead ends removed.
    """
    d = diagram.copy()

    invalid_vertices = [
        v for v in d.vertices 
        if sum(1 for p in range(3) if (v, p) in d.endpoints) < 2
    ]
    
    processed_vertices = set()

    while invalid_vertices:
        v = invalid_vertices.pop(0)
        if v in processed_vertices or v not in d.nodes:
            continue
            
        processed_vertices.add(v)
        
        start_endpoints = []
        for pos in range(3):
            if (v, pos) in d.endpoints:
                start_endpoints.append(d.endpoints[(v, pos)])
                
        for start_ep in start_endpoints:
            path_to_delete = []
            curr_ep = start_ep
            
            while curr_ep:
                if (curr_ep.node, curr_ep.position) not in d.endpoints:
                    break
                    
                path_to_delete.append(curr_ep)
                
                twin_ep = d.twin(curr_ep)
                path_to_delete.append(twin_ep)
                    
                if twin_ep.node in d.crossings:
                    nxt_pos = (twin_ep.position + 2) % 4
                    if (twin_ep.node, nxt_pos) in d.endpoints:
                        curr_ep = d.endpoints[(twin_ep.node, nxt_pos)]
                    else:
                        curr_ep = None
                else:
                    neighbor_v = twin_ep.node
                    if neighbor_v in d.vertices and neighbor_v not in processed_vertices:
                        invalid_vertices.append(neighbor_v)
                    curr_ep = None
                    delete_path(d, path_to_delete)
                    start_tuple = (path_to_delete[0].node, path_to_delete[0].position)
                    end_tuple = (path_to_delete[-1].node, path_to_delete[-1].position)
                    if start_tuple[0]==end_tuple[0] and start_tuple<end_tuple:
                        start_tuple, end_tuple = end_tuple, start_tuple
                    
                    d.remove_endpoint(start_tuple)
                    d.remove_endpoint(end_tuple)
                        


        if v in d.nodes:
            for pos in range(3):
                if (v, pos) in d.endpoints:
                   d.remove_endpoint((v, pos))

            d.remove_node(v)

    return d



def untwist_all_moves(diagram):
    """
    #!!!! TODO: Add reduce_strand_flip here, not later (with unknot)
    Simplify the diagram by undoing twisted kinks and loops.

    This function repeatedly looks for and removes two types of twists:
    1. Reidemeister 1 (R1) moves: Self-crossing loops on a single strand.
    2. Reidemeister 5 (R5) moves: Twists where a strand loops around a vertex.

    It keeps flattening these twists in a loop until no more simplifications 
    can be found.

    Args:
        diagram: The planar diagram to untwist.

    Returns:
        An untwisted, simplified copy of the diagram.
    """
    d = diagram.copy()
    
    while True:
        simplified = False
        
        r1_locations = list(kp.find_reidemeister_1_remove_kink(d))
        if r1_locations:
            d = kp.reidemeister_1_remove_kink(d, r1_locations[0], inplace=True)
            simplified = True
            continue 

        r5_locations = list(kp.find_reidemeister_5_untwists(d))
        if r5_locations:
            d = kp.reidemeister_5_untwist(d, r5_locations[0], inplace=True)
            simplified = True
            continue
            
        if not simplified:
            break
            
    return d



def get_strand_diagram_components(diagram):
    """

    Separate a diagram into independent structural layers or strands.

    This function follows strands straight through crossings (connecting 0 to 2, 
    and 1 to 3) to find components that sit completely on top of or underneath 
    other parts of the diagram. When it finds a layer that is purely an overpass 
    or an underpass, it detaches it by bypassing the relevant crossings, 
    simplifying the diagram into separate pieces.

    Args:
        diagram: The planar diagram to analyze.

    Returns:
        A list of isolated sub-diagram components.
    """


    while True:
        visited_endpoints = set()
        detached_any = False

        current_endpoints = list(diagram.endpoints)

        for ep in current_endpoints:
            if (ep.node, ep.position) not in diagram.endpoints or ep in visited_endpoints:
                continue

            comp_endpoints = set()
            stack = [ep]

            while stack:
                curr = stack.pop()
                if curr in visited_endpoints:
                    continue

                visited_endpoints.add(curr)
                comp_endpoints.add(curr)

                # 1. Step along the arc to its twin
                twin = diagram.twin(curr)
                if twin and twin not in visited_endpoints:
                    stack.append(twin)

                # 2. Step straight through junctions based on rules
                if curr.node in diagram.crossings:
                    pos = curr.position
                    if pos == 0:   nxt_pos = 2
                    elif pos == 2: nxt_pos = 0
                    elif pos == 1: nxt_pos = 3
                    else:          nxt_pos = 1
                    
                    nxt = diagram.endpoints.get((curr.node, nxt_pos))
                    if nxt and nxt not in visited_endpoints:
                        stack.append(nxt)

                elif curr.node in diagram.vertices:
                    for pos in range(len(curr.node)):
                        nxt = diagram.endpoints.get((curr.node, pos))
                        if nxt and nxt not in visited_endpoints:
                            stack.append(nxt)

            shared_crossings = {e.node for e in comp_endpoints if e.node in diagram.crossings}
            
            is_pure_over = None
            is_pure_under = None
            delete_cross = []

            for crossing in shared_crossings:
                layer_positions = {e.position for e in comp_endpoints if e.node == crossing}
                
                if len(layer_positions) >= 4:
                    delete_cross.append(crossing)
                    continue
                
                pos_iter = iter(layer_positions)

                if is_pure_over is None:
                    pos = next(pos_iter) 

                    if pos in (1, 3):
                        is_pure_over = True
                        is_pure_under = False

                    elif pos in (0, 2):
                        is_pure_under = True
                        is_pure_over = False

                for pos in pos_iter:
                    if pos in (1, 3):
                        is_pure_under = False

                    if pos in (0, 2):
                        is_pure_over = False 


            for d in delete_cross:
                if d in shared_crossings:
                    shared_crossings.remove(d)

            if shared_crossings and (is_pure_over or is_pure_under):
                for crossing in list(shared_crossings):
                    if crossing not in diagram.crossings:
                        continue
                            
                    ep0 = diagram.endpoints[(crossing, 0)]
                    ep1 = diagram.endpoints[(crossing, 1)]
                    ep2 = diagram.endpoints[(crossing, 2)]
                    ep3 = diagram.endpoints[(crossing, 3)]
                    
                    if ep0 and ep2:
                        twin0 = diagram.twin(ep0)
                        twin2 = diagram.twin(ep2)
                        if twin0 and twin2:
                            diagram.set_endpoint(twin0, twin2)
                            diagram.set_endpoint(twin2, twin0)
                            
                    if ep1 and ep3:
                        twin1 = diagram.twin(ep1)
                        twin3 = diagram.twin(ep3)
                        if twin1 and twin3:
                            diagram.set_endpoint(twin1, twin3)
                            diagram.set_endpoint(twin3, twin1)
                            


                    if crossing in diagram.nodes:
                        cross = diagram.crossings[crossing]

                        if cross and crossing == cross[0].node and diagram.twin(cross[0]) == cross[2] and crossing == cross[1].node and diagram.twin(cross[1]) == cross[3]:
                            diagram.remove_node(crossing, remove_incident_endpoints=False)
                            kp.add_unknot(diagram)
                            kp.add_unknot(diagram)
                        elif cross and (crossing == cross[0].node and diagram.twin(cross[0]) == cross[2]) or (crossing == cross[1].node and diagram.twin(cross[1]) == cross[3]):
                            diagram.remove_node(crossing, remove_incident_endpoints=False)
                            kp.add_unknot(diagram)
                        
                        else:
                            diagram.remove_node(crossing, remove_incident_endpoints=False)



                detached_any = True
                break

        if not detached_any:
            break

    return kp.disjoint_union_decomposition(diagram)



def get_canonical_component_counts(pd_notation):
    """
    Test all unplugging choices for a diagram and map each choice to its outcomes.

    This function takes a planar diagram string and tests every possible way to 
    unplug its vertices. For each choice, it cuts the strands, cleans up dead ends 
    and empty nodes, splits the diagram into separate pieces (like knots or links), 
    and untwists them into their simplest mathematical forms.

    Args:
        pd_notation: The Planar Diagram notation string.

    Returns:
        A dictionary mapping each specific choice to its sorted list of simplified 
        component shapes.
    """
    base_diagram = kp.from_pd_notation(pd_notation)
    
    choice_profiles = {}
    
    for choice_variant in all_unplug_choices(base_diagram):
        choice_key = tuple(sorted(choice_variant))

        modified_d = apply_choice(base_diagram.copy(), choice_variant)
        
        cleaned_d = clean_diagram_from_invalid_seeds(modified_d)

        kp.remove_bivalent_vertices(cleaned_d, match_attributes=False)

        kp.remove_empty_nodes(cleaned_d)

        
        raw_components = kp.disjoint_union_decomposition(cleaned_d)


        #!!! TODO: this can probably be done a bit better (reduce_strand_flip with unknot somewhere higher?)
        components = []
        for raw_comp in raw_components:
            if len(raw_comp) > 1:
                components2 = get_strand_diagram_components(raw_comp)

                for raw2 in components2:
                    if len(raw2) > 1:
                        reduce_strand_flip(raw2, [])
                        if get_strand_diagram_components(raw2) == []:

                            components.append(kp.add_unknot(raw2))
                        else:
                            components.extend(get_strand_diagram_components(raw2))
                    else:
                        components.append(raw2)
            else:
                components.append(raw_comp)


        processed_components = []
        for comp in components:
            comp = untwist_all_moves(comp)
            canonical_key = kp.canonical(comp)
            processed_components.append(canonical_key)


        choice_profiles[choice_key] = tuple(sorted(processed_components))
        
    return choice_profiles



def compare_multiple_pd_groups(pd_codes_list, depth=1, flype=False):
    """
    Compare multiple diagram strings and group together those that yield identical results.

    This function takes a list of Planar Diagram strings and builds an unplugging 
    profile for each one. It uses Reidemeister moves to identify and merge 
    topologically equivalent component shapes across different diagrams. Finally, 
    it groups the original diagrams together if they produce the exact same overall 
    distribution of simplified outcome shapes.

    Args:
        pd_codes_list: A list of Planar Diagram notation strings to compare.
        depth: The search depth for Reidemeister simplifications.
        flype: Whether to include flype moves during reduction.

    Returns:
        A list of groups, where each group contains the indices of diagrams 
        sharing identical outcome distributions.
    """

    if not pd_codes_list:
        print("No PD codes provided for comparison.")
        return []

    all_diagram_profiles = []
    for index, pd_string in enumerate(pd_codes_list):
        profile_dict = get_canonical_component_counts(pd_string)
        all_diagram_profiles.append(profile_dict)


    all_observed_single_components = set()
    for profile_dict in all_diagram_profiles:
        for component_tuple in profile_dict.values():
            all_observed_single_components.update(component_tuple)

    diagram_objects = [k for k in all_observed_single_components]
    equivalence_map = kp.reduce_equivalent_diagrams(diagram_objects, depth=depth, flype=flype)

    canonical_lookup = {}
    for representative, equivalent_set in equivalence_map.items():
        rep_str = kp.canonical(representative)
        for eq_obj in equivalent_set:
            eq_str = kp.canonical(eq_obj)
            canonical_lookup[eq_str] = rep_str

    normalized_dictionaries = []
    for original_profile in all_diagram_profiles:
        normalized_profile = {}
        
        for choice_key, component_tuple in original_profile.items():
            normalized_components = []
            for raw_comp_str in component_tuple:
                if raw_comp_str in canonical_lookup:
                    reduce_strand_flip(canonical_lookup[raw_comp_str], [])
                    unified_comp = canonical_lookup[raw_comp_str]
                else:
                    reduce_strand_flip(raw_comp_str, [])
                    unified_comp = kp.canonical(raw_comp_str)
                normalized_components.append(unified_comp)
            
            normalized_profile[choice_key] = tuple(sorted(normalized_components))
            
        normalized_dictionaries.append(normalized_profile)



    profile_groups = defaultdict(list)
    
    for idx, profile in enumerate(normalized_dictionaries):
        outcome_counts = Counter(profile.values())

        stable_signature = tuple(
            sorted(outcome_counts.items(), key=lambda x: str(x[0]))
        )
        
        profile_groups[stable_signature].append(idx)

    grouped_indices = list(profile_groups.values())

    print("\n--- TOPOLOGICAL GROUPING RESULTS ---")
    print(f"Found {len(grouped_indices)} unique topological distribution group(s).")
    for group_idx, indices in enumerate(grouped_indices):
        sample_profile = normalized_dictionaries[indices[0]]
        sorted_summary = dict(sorted(Counter(sample_profile.values()).items(), key=lambda x: str(x[0])))
        
        print(f" Group {group_idx + 1}: Diagrams {indices} -> Outcomes Summary: {sorted_summary}")
        
    return grouped_indices


if __name__ == "__main__":
    group_of_diagrams = [
        "V[0,1,2],V[3,4,5],V[3,6,7],V[8,9,10],V[1,10,11],V[5,2,12],X[4,7,13,0],X[6,14,8,13],X[11,9,14,12]",
        "V[0,1,2],V[3,4,5],V[3,6,7],V[8,9,10],V[11,2,12],V[6,13,8],X[7,14,0,4],X[14,10,12,1],X[5,11,9,13]"
        ]

    resulting_groups = compare_multiple_pd_groups(group_of_diagrams, depth=1)
    print("\nReturned Structure:", resulting_groups)


