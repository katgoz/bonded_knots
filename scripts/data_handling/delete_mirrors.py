"""
This module removes mirror duplicates from a dataset of Yamada polynomials.

If two polynomials are mirror images of each other (P and P*), the program keeps only one version and removes the other.
 Mirror images are found by replacing A with A^-1.

The program counts how many times P and P* appear in the original file. If P appears 3 times, P* should also appear 3 times. 
If the counts do not match, it prints a warning about data inconsistency.

Output:
A cleaned Excel file where mirror duplicates are removed, but the original number of copies for the chosen side is preserved.
"""

import pandas as pd
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr

_A = sp.Symbol("A")


def normalize_poly(p):
    """
    Normalizes a Yamada polynomial by removing global power shifts in A.

    This ensures that two equivalent polynomials differing only by a power of A are mapped to the same canonical representative.

    Args:
        p: sympy expression

    Returns:
        sympy expression: normalized polynomial
    """
    p = sp.expand(p)
    terms = p.as_ordered_terms()
    if not terms:
        return p
    lowest_exp = min(t.as_coeff_exponent(_A)[1] for t in terms)
    return sp.expand(p * (-_A) ** (-lowest_exp))


def yamada_mirror(expr):
    """
    Computes the mirror image of a polynomial under A -> A^{-1}, followed by normalization.

    Args:
        expr: sympy expression

    Returns:
        sympy expression: normalized mirror polynomial
    """
    return normalize_poly(expr.subs(_A, _A**-1))


def remove_yamada_mirror_duplicates(input_path: str, output_path: str):
    """
    Removes duplicate entries induced by mirror symmetry in a dataset of Yamada polynomials.

    The function:
        - normalizes all polynomials,
        - computes mirror counterparts,
        - identifies symmetric pairs,
        - keeps only one representative per pair,
        - checks consistency of mirror multiplicities in the dataset.

    Args:
        input_path: path to input Excel file
        output_path: path to output Excel file

    Returns:
        pd.DataFrame: filtered dataset
    """
    df = pd.read_excel(input_path)

    seen_originals = set()
    seen_mirrors = set()
    rows = []

    counts = {}

    for _, row in df.iterrows():
        poly = parse_expr(row["Yamada"], local_dict={"A": _A})
        poly = normalize_poly(poly)
        poly_str = str(poly)
        counts[poly_str] = counts.get(poly_str, 0) + 1

    reported_errors = set()
    has_any_error = False

    for _, row in df.iterrows():
        poly = parse_expr(row["Yamada"], local_dict={"A": _A})
        poly = normalize_poly(poly)
        poly_str = str(poly)

        mirror = yamada_mirror(poly)
        mirror_str = str(mirror)

        if poly_str == mirror_str:
            rows.append(row)
            continue

        pair_key = min(poly_str, mirror_str)

        orig_count = counts.get(poly_str, 0)
        mirr_count = counts.get(mirror_str, 0)

        if orig_count != mirr_count and pair_key not in reported_errors:
            print(f" Inconsistency detected for polynomial: {pair_key}")
            print(poly_str)
            print(mirror_str)
            print(f"   -> Occurrences of P: {orig_count}")
            print(f"   -> Occurrences of P*: {mirr_count}\n")
            reported_errors.add(pair_key)
            has_any_error = True

        if poly_str in seen_mirrors:
            continue

        if poly_str in seen_originals:
            rows.append(row)
            continue

        if poly_str <= mirror_str:
            seen_originals.add(poly_str)
            seen_mirrors.add(mirror_str)
            rows.append(row)
        else:
            seen_originals.add(mirror_str)
            seen_mirrors.add(poly_str)

    print("=" * 50)
    if not has_any_error:
        print("Success: All mirror pairs are perfectly balanced!")
    else:
        print("Warning: Processing completed, but inconsistencies were detected.")
    print("=" * 50 + "\n")

    out = pd.DataFrame(rows)
    out.to_excel(output_path, index=False)

    return out


if __name__ == "__main__":
    input_file = "data_pipeline/04_no_mirrors/9/prime/tri9_knots_consensus.xlsx"
    output_file = "data_pipeline/04_no_mirrors/9/prime/tri9_knots_consensus.xlsx"

    remove_yamada_mirror_duplicates(input_file, output_file)