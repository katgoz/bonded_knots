"""
1. Znajduję wszystkie możliwe drogi składające się wyłącznie z przejść typu over(lub under, w zależności od wybranej opcji). Te drogi mogą zaczynać się
i kończyć w wierzchołkach(V) i skrzyżowaniach(X), tzn. V-over-V, X-over-X, X-over-V, V-over-X
2. Nastepnie znajduję najkrótszą możliwą drogę między znalezionymi w kroku 1 końcowymi obiektami(V/X). Rozważam:
- 'poprawne' przejście przez skrzyżowanie(ruch typu over/under), dla X[a,b,c,d] to ruch a->c, c->a, b->d, d->b
    ==> daje to 1 przecięcie na nowej drodze -> 1 pkt
- 'niepoprawne' przejście przez skrzyżowanie, tzn. dla X[a,b,c,d] ruch typu a->b, b->a, a->d, d->a, b->c, c->b, c->d, d->c
    ==> OPIS: idziemy obok krawędzi odpowiednio po prawej lub lewej stronie. Jeśli jesteśmy po prawej to skręcając w prawo (np. b->c)
     nie tworzymy nowego przecięcia, a skręcając w lewo (np. b->a) tworzymy 1 przecięcie. Analogicznie dla lewej strony: w lewą(0 pkt), w prawą(1 pkt). 

    (*)Jeśli najpierw szliśmy "po" krawędzi a nie "obok" (nie ma obranej strony prawa/lewa) to skręcając w którąkolwiek stronę
    koszt będzie wynosił 0.5 pkt(na koniec zaokrąglamy pkt w dół, więc jak nie napotkamy V to nie ma to znaczenia, potrzebne tylko do V)

- przejścia przez V: 
    => TO MOŻNA BYĆ MOŻE POPRAWIĆ: załóżmy, że mamy V1[a,b,c], V2[c,d,e] i rozważam ruchy a->c->d, wówczas jeśli a,c,d oznaczymy jako prostą 
    to odcinki b i e mogą albo leżeć po tej samej stronie tej prostej(wtedy możemy otrzymać 0 przecięć) bądź po 2 różnych(wtedy 1 przecięcie).
    Podobnie dla większej ilości V. W związku z tym, żeby zawsze w najlepszy możliwy sposób wyznaczyć najkrótsze przejście trzeba byłoby badać
    jak są względem siebie położone wszystkie odcinki w napotykanych V. Nie widać tego bezpośrednio z pd-codu i nie mam pomysłu jak to łatwo zrobić.
    => AKTUALNE ROZWIĄZANIE(NAJGORSZY PRZYPADEK): w najgorszym możliwym przypadku po każdej stronie opisanej wyżej prostej będzie połowa odcinków.
    W związku z tym liczę liczbę przecięć jakie powstaną na ścieżce złożonej z V, jako ich liczbę/2(część całkowita). Oczywiście w ten sposób nie
    rozpoznam czasami lepszych ścieżek.
    Liczenie tego "liczba V/2(część całkowita)" zostało zrealizowane jako punktowanie każdego mijanego wierzchołka 0.5 pkt. Na koniec zaokraglam liczbę
    wszystkich przecięć(sumę pkt ze ścieżki) w dół. Np. dla ścieżki start-V-end liczba przecięć to int(0,5)=0; dla ścieżki start-V-V-end będzie int(0,5+0,5)=1;
    Jeśli był wcześniej obrany kierunek(prawa/lewa) to przy obieraniu go zostało dodane 0,5 pkt(*). Uzasadnienie: jeśli idziemy np. po lewej stronie
     i przechodzimy obok V z odcinkiem 'odstającym' w lewo to albo go przetniemy(łącznie 1 pkt), albo przejdziemy na prawą stronę(łącznie 1 pkt).
     Obranie kierunku pogarsza nam "najgorszy przypadek" gdy mijamy V.

"""
import re
import heapq
from collections import defaultdict, deque


# =========================
# Wczytanie PD-codu

def make_V_X_dictionaries(pd_text):
    raw_V = re.findall(r"V\((.*?)\)", pd_text)
    raw_X = re.findall(r"X\((.*?)\)", pd_text)

    V = {}
    X = {}

    for i, block in enumerate(raw_V, start=1):
        V[i] = list(map(int, block.split(",")))

    for i, block in enumerate(raw_X, start=1):
        X[i] = list(map(int, block.split(",")))

    return V, X


# =========================
# Budujemy graf postaci 

def build_graph(V, X):
    """
    Graf sekcji:
    graph[s] = [(t, type, object)]
    t - sekcja, dla której zachodzi s->t
    type ∈ {"over", "under", "neutral"}
    obj     : ("V", v_id) lub ("X", x_id) – obiekt, w obrębie którego zachodzi przejście
    """
    graph = defaultdict(list)

    # Połączenia w V (neutralne)
    for v_id, sections in V.items():
        a, b, c = sections
        for u, v in [(a, b), (b, c), (a, c)]:
            graph[u].append((v, "neutral", ("V", v_id)))
            graph[v].append((u, "neutral", ("V", v_id)))

    # Połączenia w X
    for x_id, sections in X.items():
        u1, o1, u2, o2 = sections

        # over–over
        graph[o1].append((o2, "over", ("X", x_id)))
        graph[o2].append((o1, "over", ("X", x_id)))

        # under–under
        graph[u1].append((u2, "under", ("X", x_id)))
        graph[u2].append((u1, "under", ("X", x_id)))

    return graph

def build_section_maps(V, X): #do dijstry
    section_to_X = defaultdict(list)
    section_to_V = defaultdict(list)

    for x_id, secs in X.items():
        for i, s in enumerate(secs):
            section_to_X[s].append((("X", x_id), i))

    for v_id, secs in V.items():
        for i, s in enumerate(secs):
            section_to_V[s].append((("V", v_id), i))

    return section_to_X, section_to_V

""" =========================
BFS najkrótszej ścieżki (sekcje)
To wykorzystujemy do znajdowania ścieżek over lub under; jest tylko 1 możliwość poprowadzenia ścieżki tego typu łączącej 2 wybrane sekcje, więc
najkrótsza ścieżka to jedyna ścieżka
"""

def shortest_path(graph, start, end, allowed_types, forbidden):
    """
    graph         – graf sekcji: graph[s] = [(t, kind, obj)]
    start, end    – sekcje początkowa i końcowa
    allowed_types – zbiór dozwolonych typów krawędzi (albo {"over"} albo {"under"})
    forbidden     – zbiór sekcji, przez które nie wolno przechodzić (blokowanie sekcji z krańcowych obiektów(X lub V) z wyjątkiem sekcji start i end)

    Zwraca listę sekcji tworzących najkrótszą ścieżkę
    """
    q = deque([start])
    visited_parent = {start: None}#visited_child: parent

    while q:
        v = q.popleft()
        if v == end:
            path=[]#for path a,b,c,d we return [a,b,c,d]
            while v is not None:
                path.append(v)
                v = visited_parent[v]
            return list(reversed(path))

        for nxt, t, obj in graph[v]:
            if t in allowed_types and nxt not in visited_parent and nxt not in forbidden:
                visited_parent[nxt] = v
                q.append(nxt)

    return None

# =========================
# Djestra - najkrótsza ścieżka
# Tu szukamy najkrótszej ścieżki między dwoma sekcjami
# =========================
def shortest_path_dijkstra(graph, start, end, X, V, section_to_X, section_to_V, blocked_X_pairs):
    """
    graph            – graf sekcji
    start, end       – sekcje pomiędzy którymi szukana jest ścieżka
    X                – słownik skrzyżowań: x_id -> [s0, s1, s2, s3]; (potrzebne do rozróżniania skrętów w lewo, w prawo i przejść na wprost)
    blocked_X_pairs  – zbiór zabronionych przejść przez skrzyżowania X: ("X", x_id) -> {(s_i, s_j), ...} używany do blokowania przejść
                      wykorzystanych w ścieżce over(lub under). Musimy je blokować, bo inaczej nie usuniemy tych skrzyżowań z over.
                      Możemy jednak przechodzić przez te "użyte" X, ale niewykorzystaną drogą. Wówczas koszt takiego przejącia to 0 pkt, bo
                      wiemy, że ten X zniknie po przeniesieniu ścieżki over(nie ma się z czym krzyżować).
    
    Zwraca minimalny koszt (int).
    """

    # kolejka: (koszt, fragment, last_turn, last_object); koszt od początku do momentu dojścia do danego fragmentu, gdzie ostatni ruch z obiektu last_object(V lub X) za pomocą skrętu last_turn(R-prawy, L-lewy, A-nie wybraliśmy strony)
    pq = [(0.0, start, "A", "A")] # "A" zamiast None, żeby nie było problemu z heappush; 
    dist = {(start, "A", "A"): 0.0} #słownik z najlepszą opcją dojścia do danego miejsca do tej pory

    parent={}#do wypisywania
    end_state = None #do wypisywania

    # sekcja -> [((X, x_id), pozycja)], wystaczyłoby samo x_id, pozycja gdyby nie to, że tak łatwiej potem porównywać z object(X, x_id) lub (V, v_id)


    while pq:
        d, v, last_turn, last_obj = heapq.heappop(pq)

        if v == end:
            #return int(d)
            #do wypisywania:
            end_state = (v, last_turn, last_obj)
            break


        if d > dist.get((v, last_turn, last_obj), float("inf")):
            continue

        # ==================================================
        # PRZEJŚCIA NEUTRALNE (V)
        # ==================================================
        for obj, pos in section_to_V.get(v, []):
            if last_obj == obj: #do tego nie weszliśmy, bo się robi obrót o 180 (wracamy skąd przyszliśmy i to do tego złą drogą)
                continue

            secs = V[obj[1]]

            for i, other in enumerate(secs):
                if other == v:
                    continue

                w=0

                if (pos + 1) % len(secs) == i:
                    new_turn = "R"
                    if last_turn == "L":
                        w=1

                elif (pos - 1) % len(secs) == i: # lewo
                    new_turn = "L"
                    if last_turn == "R":
                        w=1

                nd = d + w
                state = (other, new_turn, obj)

                if nd < dist.get(state, float("inf")):
                    dist[state] = nd
                    parent[state] = (v, last_turn, last_obj)#do wypisywania
                    heapq.heappush(pq, (nd, other, new_turn, obj))

        # ==================================================
        # PRZEJŚCIA W OBRĘBIE X
        # ==================================================
        for obj, pos in section_to_X.get(v, []):
            if last_obj == obj:#do tego nie weszliśmy, bo się robi obrót o 180
                continue

            secs = X[obj[1]]  # [a,b,c,d]

            for i, other in enumerate(secs):
                if other == v:
                    continue

                w=0

                # ---------- NA WPROST (over/under) ----------
                if (pos + 2) % 4 == i:
                    if obj in blocked_X_pairs and (v, other) in blocked_X_pairs[obj]:#przejscie przez X jak w max_over nielegalne
                        continue

                    if obj in blocked_X_pairs:#inne przejście przez to X z max_over jest z kosztem 0, bo ten X znika
                        w = 0.0
                    else:
                        w = 1.0
                    new_turn = last_turn

                # ---------- PRAWO ----------
                elif (pos + 1) % 4 == i:
                    new_turn = "R"
                    if last_turn == "L":
                        w=1

                # ---------- LEWO ----------
                elif (pos - 1) % 4 == i:
                    new_turn = "L"
                    if last_turn == "R":
                        w=1


                nd = d + w
                state = (other, new_turn, obj)

                if nd < dist.get(state, float("inf")):
                    dist[state] = nd
                    parent[state] = (v, last_turn, last_obj)#do wypisywania
                    heapq.heappush(pq, (nd, other, new_turn, obj))


    #return None <-!! jak bez wypisywania
    #wypisywanie:

    if end_state is None:
        return None

    path_states = []
    cur = end_state
    while cur in parent:
        path_states.append(cur)
        cur = parent[cur]
    path_states.append(cur)
    path_states.reverse()

    path_sections = [v for (v, turn, obj) in path_states]
  #  print("dla start, end ",start, end, d,":",path_states)
    return int(d)



# =========================
# Sekcje należące do wierzchołków
# =========================
#czy to sie nie pokrywa z dijkstra?

def all_objects_sections(V, X):
    """
    Zwraca:
    obj_id -> set(sections)
    gdzie obj_id = ("V", v_id) albo ("X", x_id)
    """
    objs = {}

    for v_id, sections in V.items():
        objs[("V", v_id)] = set(sections)

    for x_id, sections in X.items():
        objs[("X", x_id)] = set(sections)

    return objs



# =========================
# MAX ścieżka OVER/UNDER (liczba sekcji) 
"""Szuka max długości ścieżkę over(under) między daną parą obiektów(X lub V). Dla każdego zestawu sekcji z tych obiektów wywołuje funkcję shortest_path
i wybiera najdłuższy wynik
"""
# =========================

def max_between_vertices(graph, objects, o1, o2, allowed_types):
    """
    graph – graf sekcji
    objects – słownik:  (obj_type, obj_id) -> set(sections), np. objects[("X", 1)]=[1,2,3,4]
    o1, o2 – identyfikatory obiektów (np. ("V", i) lub ("X", j)), pomiędzy którymi szukamy ścieżek
    allowed_types – dozwolony typ krawędzi ({"over"} lub {"under"})
    """
    worst_len = None
    worst_path=[]
    
    for s in objects[o1]:
        for t in objects[o2]:
            if s == t:
                continue

            if s in objects[o2] or t in objects[o1]:
                continue

            forbidden = (objects[o1] | objects[o2]) - {s, t}

            path = shortest_path(graph, s, t, allowed_types, forbidden)

            if path is not None:
                length = len(path)
                if worst_len is None or length > worst_len:
                    worst_len = length
                    worst_path = path


    return worst_len, worst_path


# =========================
# MIN dowolna ścieżka (liczba sekcji)
"""
Dla danej pary obiektów v1 i v2 (V lub X) szukamy najkrótszej dopuszczalnej ścieżki pomiędzy ich sekcjami.

Możliwe punkty startowe i końcowe (sekcje) są dobierane w zależności od typu obiektów (V–V, V–X, X–V, X–X):
-> dla obiektów X wykorzystujemy tylko krańce wcześniej znalezionej ścieżki over–over(bo jak przenosimy ten fragment to musi się zawsze tak zaczynać; nie da się zmienić jego położenia w ramach tego X)
-> dla obiektów V sprawdzamy wszystkie wychodzące z nich sekcje (bo możemy dowolnie zmieniać położenie fragmentu wychodzącego z tego V)

Dla każdej dopuszczalnej pary sekcji (s, t) uruchamiana jest funkcja shortest_path_dijkstra. Spośród wszystkich poprawnych ścieżek wybierana 
jest ta o najmniejszej długości (liczbie sekcji).

Funkcja zwraca długość najkrótszej ścieżki oraz sekcje początkową i końcową, albo None, jeśli taka ścieżka nie istnieje.
"""
# =========================

def min_any_between_vertices(graph, Vsecs, v1, v2, X, V, blocked_X_pairs, max_path, section_to_X, section_to_V):
    best = None
    best_pair = None#po co nam start i end?

    start_mp = max_path[0]
    end_mp   = max_path[-1]

    pairs = []

    is_X1 = v1[0] == "X"
    is_X2 = v2[0] == "X"


    if is_X1 and is_X2:
        pairs = [(start_mp, end_mp)]

    elif is_X1 and not is_X2:
        pairs = [(start_mp, t) for t in Vsecs[v2]]

    elif not is_X1 and is_X2:
        pairs = [(s, end_mp) for s in Vsecs[v1]]

    else:  # V → V
        pairs = [(s, t) for s in Vsecs[v1] for t in Vsecs[v2]]

    for s, t in pairs:
        if s == t:
            return s, t, 1

        d = shortest_path_dijkstra(
            graph, s, t, X, V, section_to_X, section_to_V, blocked_X_pairs)

        if d is not None:
            length = d + 1
            if best is None or length < best:
                best = length
                best_pair = (s, t)

    if best_pair is None:
        return None, None, None

    return best, best_pair[0], best_pair[1]



#wypisywanie wyników
def print_paths(v1, v2, over_path, min_len):
    print("=" * 60)
    print(f"{v1} — {v2}")
    print("over–over(under -under) path (sekcje):", over_path)
    print("najkrótsza długość:", min_len)




# =========================
# Główne sprawdzenie
# =========================

def exists_shorter_than(V, X, allowed_types):
    """
Logika głównego sprawdzenia:
Dla wszystkich par obiektów (V oraz X) budowany jest graf sekcji i znajdowana jest:
1) Najdłuższa dopuszczalna ścieżka typu over–over (lub under-under)
2) Najkrótsza dowolna ścieżka (liczba sekcji)

Punkt 2) korzysta z min_any_between_vertices(czyli shortest_path_dijkstra), dlatego przed wywołaniem liczone jest blocked_X_pairs(argument funkcji shortest_path_dijkstra),
 aby zapobiec użyciu tej samej konfiguracji przejścia przez X, wykorzystanego w over-over(under).

Jeśli istnieje ścieżka krótsza niż maksymalna ścieżka over–over(under), funkcja wypisuje odpowiednie informacje i kończy działanie.

Funkcja zwraca:
- (True, dane) jeśli znaleziono krótszą ścieżkę,
- (False, None) jeśli dla żadnej pary obiektów taka sytuacja nie zachodzi.
"""

    graph = build_graph(V, X)
    section_to_X, section_to_V = build_section_maps(V, X)
    objects = all_objects_sections(V, X)
    obj_ids = list(objects.keys())

    for i in range(len(obj_ids)):
        for j in range(i + 1, len(obj_ids)):
            v1, v2 = obj_ids[i], obj_ids[j]


            max_over, max_path = max_between_vertices(
                graph, objects, v1, v2, allowed_types
            )

            if max_over is None:
                continue

#w alternatywnej krótszej scieżce mozna przejsc przez te X użyte w overover ale tylko tą drogą nie przez overover, wiec np. jesli w over over przechodzimy a->c
#i jest X1[a,b,c,d] to do blokowania dajemy blocked_X_pairs[(X, 1)]={(a,c),(c,a)}
            blocked_X_pairs = defaultdict(set)

            for k in range(len(max_path) - 1):
                u, v = max_path[k], max_path[k + 1]
                for nxt, t, obj in graph[u]:
                    if nxt == v and obj[0] == "X":
                        blocked_X_pairs[obj].add((u, v))
                        blocked_X_pairs[obj].add((v, u))


            min_any, start, end = min_any_between_vertices(
                graph, objects, v1, v2, X, V, blocked_X_pairs, max_path, section_to_X, section_to_V
            )


            if min_any is not None and min_any<max_over:
                print(start, end)
                print_paths(v1, v2, max_path, min_any)
                return True
            


    return False



def run_file(filename, kind="over"):

#   kind ∈ {"over", "under"}#czy trasy over czy under


    results = []

    with open(filename, "r") as f:
        next(f)
        for line in f:
            code = (line.strip()
                    .replace("],", ");")
                    .replace("]", ")")
                    .replace("[", "("))

            V, X = make_V_X_dictionaries(code)

            ok = exists_shorter_than(V, X, kind)

            if ok:
                results.append(code)

    return results

# =========================
# PRZYKŁADOWE UŻYCIE
# =========================
def to_pd(item: str) -> str:
    # usuń spacje i newlines
    item = item.strip().replace(" ", "")

    # zamień () na []
    item = item.replace("(", "[").replace(")", "]")

    # zamień ; na ,
    item = item.replace(";", ",")

    return item

from pathlib import Path

#file = "zle.txt"
file = "Re_Konsultacje/tri10_knots_reduced_inc3.txt"
# --- PRZETWARZANIE ---
over_results = set(run_file(filename=file, kind="over"))
under_results = set(run_file(filename=file, kind="under"))
all_results = over_results | under_results

print("Wyniki:", all_results)
print("Liczba:", len(all_results))

# --- ŚCIEŻKI ---
"""
input_path = Path(file)
base_name = input_path.stem  # np. "tri4_knots_reduced_inc3"

# katalog wynikowy
output_dir = Path("wyniki")
output_dir.mkdir(exist_ok=True)

# plik wynikowy w folderze wyniki/
out_file = output_dir / (base_name + ".txt")

# plik porównawczy w tym samym folderze co input
# zamiana _reduced_inc3 → _maybereduced_flip
compare_base = base_name.replace("_reduced_inc3", "_maybereduced_flip")
compare_file = input_path.parent / (compare_base + ".txt")

print("INPUT       =", input_path)
print("OUTFILE     =", out_file)
print("COMPAREFILE =", compare_file)

# --- ZAPIS ---
with open(out_file, "w", encoding="utf-8") as f:
    if all_results:
        f.write("pd notation\n")
    for item in all_results:
        f.write(to_pd(item) + "\n")

print("Zapisano:", out_file)

# --- FUNKCJA WCZYTYWANIA (zwrot SET) ---
def load_pd_file(path):
    with open(path, encoding="utf-8") as f:
        return set(line.strip() for line in f if line.strip())

# --- WCZYTANIE DANYCH Z PLIKÓW ---
set1 = load_pd_file(out_file)

if compare_file.exists():
    set2 = load_pd_file(compare_file)
else:
    print(f"UWAGA: plik porównawczy {compare_file} nie istnieje — traktuję jako pusty.")
    set2 = set()

# --- PORÓWNANIE ---
if set1 == set2:
    print("Pliki mają IDENTYCZNĄ zawartość (jako zbiory).")
else:
    print("Pliki RÓŻNIĄ się zawartością.")
    print("Linie tylko w wynikach:", set1 - set2)
    print("Linie tylko w porównywanym:", set2 - set1)

"""