"""
This module normalizes and renumbers diagram names in an Excel dataset.

Each name is assumed to encode a topological base of the form B(c, b), H(c, b), or L(c, b), optionally followed by a suffix (e.g. "#3") and an index.

The procedure:
- extracts the topological base B(c, b), H(c, b), or L(c, b),
- extracts optional suffix information,
- sorts entries first by base and then by suffix,
- renumbers entries within each base group while preserving suffix information,
- reconstructs the final standardized naming format.

"""

import pandas as pd
import re


def fix_names_and_export_excel(input_file, output_file="output.xlsx"):
    """
    Renumbers and standardizes diagram names in an Excel file based on their topological base.

    Names are decomposed into:
        - Base: topological type B(c,b), H(c,b), or L(c,b)
        - Suffix: optional additional tag (e.g. "#3")
        - Index: regenerated sequential numbering within each base

    Args:
        input_file: path to input Excel file
        output_file: path to output Excel file

    Returns:
        pd.DataFrame: processed dataframe with updated naming scheme
    """
    df = pd.read_excel(input_file)
    name_col = df.columns[0]

    df["Base"] = df[name_col].astype(str).str.extract(r"(^.*?\))")
    df["Suffix"] = df[name_col].astype(str).str.extract(r"\)(.*?)(?:_\d+|$)").fillna("")

    df = df.sort_values(by=["Base", "Suffix"]).reset_index(drop=True)

    df[name_col] = (
        df["Base"]
        + df["Suffix"]
        + "_"
        + (df.groupby("Base").cumcount() + 1).astype(str)
    )

    df = df.drop(columns=["Base", "Suffix"])

    df.to_excel(output_file, index=False)

    return df


if __name__ == "__main__":

    input_file = "data_pipeline/04_no_mirrors/10/prime_sum/tri10_knots_sum3_reduced_inc2.xlsx"
    output_file = "data_pipeline/04_no_mirrors/10/prime_sum/tri10_knots_sum3_reduced_inc2.xlsx"

    fix_names_and_export_excel(input_file, output_file)


    input_file = "classification/10/10.xlsx"
    output_file = "classification/10/10.xlsx"

    fix_names_and_export_excel(input_file, output_file)