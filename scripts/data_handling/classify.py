"""
This module implements classification of planar diagram (PD) codes according to the following scheme:

• Bonded knots (B): diagrams whose underlying graph contains no simple loop and no additional connected components.
  Denoted by B(c, b)i, where:
    c = minimal number of crossings,
    b = number of bonds,
    i = index enumerating diagrams with the same (c, b).

• Bonded handcuff links (H): diagrams whose underlying graph contains a simple loop (a vertex adjacent to itself).
  Denoted by H(c, b)i.

• Bonded links (L): diagrams whose underlying graph contains additional connected components.
  Denoted by L(c, b)i.

Note:
A suffix parameter for sums of type #3 (e.g. "#3") is supported and appended to all generated labels.
However, the current implementation applies this suffix uniformly to the entire input dataset.
Therefore, connected-sum datasets must be provided separately for each suffix value, as mixing different sums
within a single run would result in incorrect global suffix assignment.
"""

import pandas as pd
import re
from collections import defaultdict, deque


def parse_pd(pd_text):
    """
    Parses a planar diagram (PD) notation string into vertex and crossing lists.

    Args:
        pd_text: String in PD notation format.

    Returns:
        tuple:
            - Vs: list of vertex triples [a, b, c]
            - Xs: list of crossing quadruples [a, b, c, d]
    """
    Vs = []
    Xs = []
    for part in str(pd_text).split("],"):
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


def build_x_graph(Xs):
    """
    Builds an adjacency graph based on crossing relations.

    Each crossing X[a,b,c,d] generates connections:
        a <-> c
        b <-> d

    Args:
        Xs: list of crossing definitions.

    Returns:
        dict: adjacency list representation of the graph.
    """
    G = defaultdict(set)
    for a, b, c, d in Xs:
        G[a].add(c)
        G[c].add(a)
        G[b].add(d)
        G[d].add(b)
    return G


def connected(G, s, t):
    """
    Checks whether two nodes are connected in an undirected graph.

    Uses BFS traversal.

    Args:
        G: adjacency list graph
        s: start node
        t: target node

    Returns:
        bool: True if path exists, False otherwise
    """
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


def classify_type(Vs, Xs):
    """
    Classifies a diagram into structural types:
        - "L": link-like (multiple connected components)
        - "H": handcuff-like structure (simple loop in graph)
        - "B": bonded knot (no loops, connected)

    Args:
        Vs: vertex list
        Xs: crossing list

    Returns:
        str: one of "L", "H", "B"
    """
    G = build_x_graph(Xs)

    for a, b, c in Vs:
        G[a].update([b, c])
        G[b].update([a, c])
        G[c].update([a, b])

    all_nodes = set(G.keys())
    visited = set()
    components_count = 0

    for node in all_nodes:
        if node not in visited:
            components_count += 1
            stack = [node]
            while stack:
                curr = stack.pop()
                if curr not in visited:
                    visited.add(curr)
                    stack.extend(G[curr] - visited)

    if components_count > 1:
        return "L"

    G_crossings_only = build_x_graph(Xs)
    for a, b, c in Vs:
        for x, y in [(a, b), (a, c), (b, c)]:
            if connected(G_crossings_only, x, y):
                return "H"

    return "B"


def get_new_base_name(pd_text):
    """
    Generates a normalized base label for a PD diagram.

    Format:
        TYPE(c, b)

    where:
        TYPE ∈ {B, H, L}
        c = number of crossings
        b = number of bonds (vertices)

    Returns:
        str: normalized base name (e.g. B(4,3))
    """
    Vs, Xs = parse_pd(pd_text)
    t = classify_type(Vs, Xs)
    m = len(Xs)
    n = len(Vs) // 2
    return f"{t}({m},{n})"



def reindex_excel_file(input_file, output_file, suffix=None):
    """
    Reindexes diagram names in an Excel file based on topological classification.

    Returns:
        pd.DataFrame: processed dataframe
    """
    df = pd.read_excel(input_file)

    name_col = df.columns[0]
    pd_col = df.columns[1]

    print("Starting diagram classification and renumbering...")

    df["Base"] = df[pd_col].apply(get_new_base_name)
    df = df.sort_values(by="Base").reset_index(drop=True)

    if suffix:
        df["Base_with_suffix"] = df["Base"] + str(suffix)
    else:
        df["Base_with_suffix"] = df["Base"]

    df[name_col] = (
        df["Base_with_suffix"]
        + "_"
        + (df.groupby("Base").cumcount() + 1).astype(str)
    )

    df = df.drop(columns=["Base", "Base_with_suffix"], errors="ignore")

    df.to_excel(output_file, index=False)
    print(f"Success! File saved to: {output_file}")

    return df


if __name__ == "__main__":
    input_path = "data_pipeline/04_no_mirrors/10/prime_sum/tri10_knots_sum3_reduced_inc2.xlsx"
    output_path = "data_pipeline/04_no_mirrors/10/prime_sum/tri10_knots_sum3_reduced_inc2.xlsx"

    reindex_excel_file(input_path, output_path, suffix='#3')