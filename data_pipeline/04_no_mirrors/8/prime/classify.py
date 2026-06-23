import re
from collections import defaultdict, deque

# ============================================================
# PARSE PD
# ============================================================

def parse_pd(pd):
    Vs = []
    Xs = []

    for part in pd.split("],"):
        part = part.strip()

        if not part.endswith("]"):
            part += "]"

        if part.startswith("V["):
            nums = list(map(int, re.findall(r"\d+", part)))
            Vs.append(nums)

        elif part.startswith("X["):
            nums = list(map(int, re.findall(r"\d+", part)))
            Xs.append(nums)

    return Vs, Xs


# ============================================================
# X GRAPH
# ============================================================

def build_x_graph(Xs):
    G = defaultdict(set)

    for a, b, c, d in Xs:

        # opposite strands only
        G[a].add(c)
        G[c].add(a)

        G[b].add(d)
        G[d].add(b)

    return G


# ============================================================
# CONNECTIVITY
# ============================================================

def connected(G, s, t):

    if s == t:
        return True

    q = deque([s])
    seen = {s}

    while q:

        v = q.popleft()

        for w in G[v]:

            if w == t:
                return True

            if w not in seen:
                seen.add(w)
                q.append(w)

    return False


# ============================================================
# H or B
# ============================================================

def classify_type(Vs, Xs):

    G = build_x_graph(Xs)

    for a, b, c in Vs:

        for x, y in [(a, b), (a, c), (b, c)]:

            if connected(G, x, y):
                return "H"

    return "B"


# ============================================================
# CLASSIFY
# only V + X <= 8
# ============================================================

def classify(pd, limit):

    Vs, Xs = parse_pd(pd)

    v = len(Vs)
    x = len(Xs)

    if v + x != limit:
        return None

    t = classify_type(Vs, Xs)

    m = x
    n = v // 2

    return (t, m, n)


# ============================================================
# READ FILE
# one PD per line
# ============================================================

def main(filename):

    from collections import defaultdict

    groups = defaultdict(list)

    with open(filename, "r", encoding="utf-8") as f:
        for line in f:
            pd = line.strip()
            if not pd:
                continue

            cls = classify(pd)   # your existing function

            if cls is None:
                continue

            groups[cls].append(pd)

    with open("output.txt", "w", encoding="utf-8") as out:
        for key in sorted(groups):
            diagrams = sorted(groups[key])

            t, m, n = key

            for i, pd in enumerate(diagrams, start=1):
                name = f"{t}({m},{n})_{i}"
                out.write(name + "\n")
                out.write(pd + "\n\n")

if __name__ == "__main__":
    main("8_sum_merged.txt")