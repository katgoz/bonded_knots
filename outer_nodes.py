import knotpy as kp
from find_strand_flip_move_new import min_crossings_path, insert_path_core, find_and_perform_strand_flip, find_path_of_type, min_between_nodes, perform_strand_flip
from knotpy.algorithms.sanity import sanity_check_raise_exception
import sys

pd_text = "V(0,1,2);V(3,4,5);V(6,5,7);V(0,8,9);X(3,6,8,2);X(1,10,11,12);X(13,4,12,11);X(7,13,14,15);X(15,14,10,9)"
D = kp.from_pd_notation(pd_text)

def _disjoint_components_nodes(k) -> list[set]:
    """
    Compute connected components as sets of nodes.

    Args:
        k: Diagram.

    Returns:
        List of node-sets, one per connected component.
    """
    dsu = kp.DisjointSetUnion(k.nodes)
    for ep0, ep1 in k.arcs:
        dsu[ep0.node] = ep1.node
    return list(dsu.classes())

def get_outerplanar_endpoints(diagram, knot_diagrams, node = None, subset = None, add_endpoints = None):
    # ustala na poczatku zewnetrzne, a potem to juz zwraca na podstawie ustalonych i zawiera Node na outer i jest subset tego wymienionego
    # po zmianach wybiera endpoint lub twin w faces, add
    """
    Example:
    zawsze zwraca inne; irytujace; moze wybierac leksykograficznie? idk? bo wyniki beda rozne
    >>> pd_text = "V[0,1,2],V[3,4,5],V[6,7,4],V[0,8,9],X[1,10,3,11],X[11,5,7,12],X[9,13,6,10],X[2,12,13,8]"
    >>> D = kp.from_pd_notation(pd_text)
    >>> print(get_outerplanar_endpoints(D))

    (b1[outer], e2[outer], g3[outer], c0[outer])
    """
    external_endpoints = [ep for ep in diagram.endpoints if ep.attr.get("outer")]

    faces = list(diagram.faces)

    working_faces = faces

    twins=[]
    if add_endpoints:
        twins = [diagram.twin(ep) for ep in add_endpoints]

    if external_endpoints:
        working_faces = [face for face in working_faces if set(face).issuperset(external_endpoints)]
        if not working_faces:
            raise ValueError("No external face candidates")

    if add_endpoints: #byly zmainy z outer wiec sus external enspoints i też twiny
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
            
    external_face = min(
        working_faces,
        key=lambda face: (-len(face), tuple(face))
    )


    for ep in external_face:
    	ep.attr["outer"] = True

    return external_face

#print(get_outerplanar_endpoints(D))

def change_outer_face(old_face, remove_endpoints, add_endpoints):
    """
    Zmienia outer face -> usuwa stare i dodaje nowe endpointy
    """
    for ep in old_face:
    	if ep in remove_endpoints:
        	ep.attr.pop("outer", None)
    # mark new outer face
    for ep in add_endpoints:
        ep.attr["outer"] = True


def closest_node_to_outer_face(diagram, knot_diagrams):
    outer_endpoints = list(get_outerplanar_endpoints(diagram, knot_diagrams))
    outer_nodes = {ep.node for ep in outer_endpoints}
    inner_nodes = [n for n in diagram.vertices if n not in outer_nodes]
    inner_endpoints = [ep for n in inner_nodes for ep in diagram.endpoints[n]]
    cost, path = min_crossings_path(
        diagram,
        start_endpoints=outer_endpoints,
        target_endpoints=inner_endpoints,
        blocked_transitions={},
        randomize = False
    )

    return path 


def over_or_under(node, diagram):
	#for vertices for crossings we dont have to
    #!! test for more components
    under=0
    over=0
    components = _disjoint_components_nodes(diagram)

    for ep in diagram.endpoints[node]:
        twin = diagram.twin(ep)
        twin_node, twin_pos = twin.node, twin.position
        if twin_node in diagram.crossings:
            if any(node in comp and twin_node in comp for comp in components):
                if twin_pos in (0,2):
                    under+=1
                else:
                    over+=1
    print(over, under)
    if over>under:
        return "over"
    else:
        return "under"



#path = closest_node_to_outer_face(D)
#print(path)
#ep, turn = path[-1]
#kind = (over_or_under(ep.node, D))




def find_outer_ep_on_path(diagram, path, knot_diagrams):
    outer_endpoints = list(get_outerplanar_endpoints(diagram, knot_diagrams))
    all_outer_endpoints = outer_endpoints + [diagram.twin(ep) for ep in outer_endpoints]

    outer_on_path=[]
    prev_ep = path[0][0]
    prev_turn = path[0][1]
    out = False
    for ep, turn in path[1:]:
        if (ep in all_outer_endpoints or prev_ep in all_outer_endpoints) and ((prev_ep.node == ep.node and ep.node in diagram.crossings and prev_ep.position == (ep.position + 2)%4) or (prev_turn!=turn)):
            if out == False:
                outer_on_path.append(ep)
                out = True
            else:
                out = False

        elif out == True:
            outer_on_path.append(ep)
    return outer_on_path

def left_or_right(diagram, path, knot_diagrams):
    #czy zmienic left right i ulozenie out (co zakryc)
    #dla obu ale dla crossing ignorujemy change_site? bez tego out moze bo to automatycznie?
    #nie wiem czy dziala
    drag_ep = path[-1][0]
    endpoints = diagram.endpoints[drag_ep.node]
    first = path[0][0]

    cost, min_path = min_crossings_path(
        diagram,
        start_endpoints=endpoints,
        target_endpoints=[first],
        blocked_transitions={},
        randomize = False
    )

    change_out = False
    change_site = False

    covered_outer_nodes = []
    outer_on_path = find_outer_ep_on_path(diagram, min_path, knot_diagrams)
    for i in range(len(outer_on_path[:-1])):
        if outer_on_path[i].node == outer_on_path[i+1].node:
            covered_outer_nodes.append(outer_on_path[i].node)

    outer_endpoints = list(get_outerplanar_endpoints(diagram, knot_diagrams))
    all_outer_nodes = len(outer_endpoints)
    all_covered_outer_nodes = len(covered_outer_nodes)
    rest = all_outer_nodes - all_covered_outer_nodes
    if all_covered_outer_nodes>0:
        if covered_outer_nodes[-1].node == first.node:
            if all_covered_outer_nodes>rest:
                change_out = True
            else:
                change_site = True
        else:
            if all_covered_outer_nodes>=rest:
                change_out = True
                change_site = True

    return change_out, change_site

def drag_node_out(diagram, path, kind, knot_diagrams):
    # wyciagamy tak zeby ladnie sie robily kolejno crossingi, dodajemy L/R zeby sie zrobil dodatkowy crossing
    #!!! by crossing??
    drag_ep = path[-1][0] #ep of a node that we will drag this node out by
    first = path[0]
    outer_endpoints = list(get_outerplanar_endpoints(diagram, knot_diagrams))
    all_outer_nodes = len(outer_endpoints)

    """
    if drag_ep.node in diagram.vertices:
        change_out, change_site = left_or_right(diagram, path, knot_diagrams)

        if change_site:
            if diagram.endpoints(first.node, (first.position + 1)%3) in all_outer_endpoints:
                new_first = diagram.endpoints(first.node, (first.position + 1)%3)
            else:
                new_first = diagram.endpoints(first.node, (first.position + 2)%3) 

            site = "L" if first[1] == "R" else "R"
            path[0] = (new_first, site)
            path[1] = (path[1][0], site)
    """
    node = drag_ep.node
    end_endpoints = []


    add_cross = (first[0], 'L' if first[1] == 'R' else 'R')
    path.insert(0, add_cross)

    endpoints = diagram.endpoints[node]
    if first[1] == 'R':
        i = (drag_ep.position + 1) % len(endpoints)
    else:
        i = drag_ep.position

    order = endpoints[i:] + endpoints[:i]

    if first[1] == 'L':
        order = order[::-1]

    for ep in order:
        start_ep, free_ep = insert_path_core(diagram, path, kind)
        diagram.set_endpoint(start_ep, diagram.twin(ep))
        diagram.set_endpoint(diagram.twin(ep), start_ep)
        diagram.set_endpoint(free_ep, ep)
        diagram.set_endpoint(ep, free_ep)
        for ep1 in diagram.endpoints[free_ep[0]]:
            ep1.attr.pop("outer", None)

    get_outerplanar_endpoints(diagram, knot_diagrams)


#outer_endpoints = list(get_outerplanar_endpoints(D))
#outer_nodes = {ep.node for ep in outer_endpoints}
#print(outer_nodes)
#print(set(D.nodes))


def add_diagram_state(diagram, knot_diagrams):
    d_copy = diagram.copy()
    d_copy.name = kp.to_pd_notation(d_copy)
    try:
        sanity_check_raise_exception(d_copy)
        get_outerplanar_endpoints(d_copy, knot_diagrams)
        print("WWWWW dodanie:", d_copy)
    except Exception:
        import traceback
        traceback.print_exc()
        raise

    knot_diagrams.append(d_copy)

def change_outer(new_outer, drag_ep, knot_diagrams): # jesli!! jest okreslone outer face(pelne/nie del) to koncowy outer to subset tego old_outer_nodes
    remove_endpoints = [ep for ep in D.endpoints if ep.attr.get("outer")]
    old_outer_nodes = [ep1.node for ep1 in remove_endpoints]
    if new_outer:
        for ep2 in new_outer:
            old_outer_nodes.append(ep2[0])
    add_endpoints = []
    if new_outer:
        for ep_tuple in new_outer:
            add_endpoints.append(D.endpoints[(ep_tuple[0], ep_tuple[1])])
    change_outer_face(remove_endpoints, remove_endpoints, [])
    get_outerplanar_endpoints(D, knot_diagrams, drag_ep.node, old_outer_nodes, add_endpoints)

def reduce_strand_flip(diagram, knot_diagrams, dont_cover = None):
    #dont_cover to ep wyciagany
    updated = True
    while updated:
        updated, new_outer = find_and_perform_strand_flip(diagram, outer = True, randomize = False)
        if updated == True:
            if dont_cover:
                change_outer(new_outer, dont_cover, knot_diagrams)
            add_diagram_state(diagram, knot_diagrams)

def reduce_drag_ep(diagram, drag_ep, kind, knot_diagrams, dont_cover = None):
    for ep in diagram.endpoints[drag_ep.node]:
        max_path = find_path_of_type(diagram, ep, allowed_type = kind)
        max_len = len(max_path)

        min_any, alternative_path = min_between_nodes(diagram, max_path, randomize = False)

        if min_any is not None and min_any<max_len:
            new_outer = perform_strand_flip(diagram, max_path, alternative_path, kind, outer = True)
            if dont_cover:
                change_outer(new_outer, drag_ep, knot_diagrams)
            add_diagram_state(diagram, knot_diagrams)


def diagram_to_outerplanar(D, knot_diagrams):
    #knot_diagrams = []

    add_diagram_state(D, knot_diagrams)
    reduce_strand_flip(D, knot_diagrams)
    outer_endpoints = list(get_outerplanar_endpoints(D, knot_diagrams))
    outer_nodes = {ep.node for ep in outer_endpoints}
    inner_nodes = [n for n in D.vertices if n not in outer_nodes]
    max_iter = 15
    i = 0
    while inner_nodes:
        if i >= 10:
            raise RuntimeError("Przekroczono limit 15 iteracji")
        path = closest_node_to_outer_face(D, knot_diagrams)
        ep, turn = path[-1]
        kind = (over_or_under(ep.node, D))
        print("KINDL", kind)
        drag_node_out(D, path, kind, knot_diagrams)
        add_diagram_state(D, knot_diagrams)
        reduce_drag_ep(D, ep, kind, knot_diagrams, dont_cover = ep)
        reduce_strand_flip(D, knot_diagrams, dont_cover = ep)
        outer_endpoints = list(get_outerplanar_endpoints(D, knot_diagrams))
        outer_nodes = {ep1.node for ep1 in outer_endpoints}
        inner_nodes = [n for n in D.vertices if n not in outer_nodes]
        if ep not in outer_nodes:
            ValueError("nie wyciagniety")
        i += 1
    if not inner_nodes:
        sanity_check_raise_exception(D)
        get_outerplanar_endpoints(D, knot_diagrams)
        print("zrobione")

    D.name = kp.to_pd_notation(D)
    output_path = ""
    kp.export_pdf(knot_diagrams, output_path)
 #   print(f"Zapisano do pliku: {output_path}")
    #funkcja przekladajaca ten strand *2 + ustawianie ep ale to moze w innej

knot_diagrams=[]

try:
    diagram_to_outerplanar(D, knot_diagrams)
except Exception:
    import traceback
    traceback.print_exc()
    output_path = ""
 #   kp.export_pdf(knot_diagrams, output_path)



"""
file_path = "Re_Konsultacje/tri7_knots_reduced_inc3.txt"  

success = 0
total = 0

with open(file_path, "r") as f:
    lines = f.readlines()

# pomijamy pierwszy wiersz
for line in lines[1:]:
    pd_text = line.strip()
    
    if not pd_text:  # pomijamy puste linie
        continue

    total += 1

    try:
        D = kp.from_pd_notation(pd_text)
        knot_diagrams = []
        diagram_to_outerplanar(D, knot_diagrams)
        success += 1
    except Exception:
        print(f"❌ Failed: {pd_text}")

print(f"\nWynik: {success}/{total}")
"""

"""
def mark_outer(face):
    for ep in face:
        ep.attr["outer"] = True


def same_face(f1, f2):
    return {(ep.node, ep.position) for ep in f1} == \
           {(ep.node, ep.position) for ep in f2}


def run_all_faces(D):
    success = 0
    total = 0

    faces = list(D.faces)

    for i in range(len(faces)):
        pd = kp.to_pd_notation(D)
        D1 = kp.from_pd_notation(pd)


        faces1 = list(D1.faces)
        target_face = None

        original_face_signature = {
            (ep.node, ep.position) for ep in faces[i]
        }

        for f in faces1:
            sig = {(ep.node, ep.position) for ep in f}
            if sig == original_face_signature:
                target_face = f
                break

        if target_face is None:
            print(" Nie znaleziono odpowiadającej ściany")
            continue

        mark_outer(target_face)

        total += 1

        try:
            knot_diagrams = []
            diagram_to_outerplanar(D1, knot_diagrams)
            success += 1

        except Exception:
            import traceback
            traceback.print_exc()
            print(f" Failed: {kp.to_pd_notation(D1)}")

    print(f"\nWynik: {success}/{total}")

run_all_faces(D)
"""