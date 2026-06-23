"""
This module generates labeled illustrations of knot diagrams from an Excel dataset of PD codes and their names.
The final output is a single PDF where each page contains a diagram signed with its identifier.
"""


import pandas as pd
import knotpy as kp
from outer_nodes import get_outerplanar_endpoints

from pypdf import PdfReader, PdfWriter
from reportlab.pdfgen import canvas


def add_signatures_to_pdf(pdf_path, names_list, output_path):
    """
    Overlays text labels onto each page of a PDF document.

    Each page receives a centered label taken from names_list.
    """
    reader = PdfReader(pdf_path)
    writer = PdfWriter()

    for i, page in enumerate(reader.pages):
        if i >= len(names_list):
            writer.add_page(page)
            continue

        packet = io.BytesIO()
        can = canvas.Canvas(packet, pagesize=(page.mediabox.width, page.mediabox.height))

        can.setFont("Helvetica-Bold", 14)

        x_pos = float(page.mediabox.width) / 2
        y_pos = 30

        can.drawCentredString(x_pos, y_pos, names_list[i])
        can.save()

        packet.seek(0)
        new_pdf = PdfReader(packet)

        page.merge_page(new_pdf.pages[0])
        writer.add_page(page)

    with open(output_path, "wb") as f:
        writer.write(f)



if __name__ == "__main__":

    input_excel = "../classification/10/10.xlsx"
    temp_pdf = "temp_diagrams_no_labels.pdf"
    final_pdf = "classification/10/10k.pdf"

    df = pd.read_excel(input_excel)

    name_col = df.columns[0]
    pd_col = df.columns[1]

    knot_diagrams = []
    saved_names = []

    print("Processing diagrams from Excel file...")

    for _, row in df.iterrows():
        name_value = str(row[name_col]).strip()
        pd_line = str(row[pd_col]).strip()

        if not pd_line or pd_line == "nan":
            continue

        pd_converted = (
            pd_line.replace("],", ");")
                   .replace("]", ")")
                   .replace("[", "(")
        )

        k = kp.from_pd_notation(pd_converted)

        get_outerplanar_endpoints(k)

        knot_diagrams.append(k)
        saved_names.append(name_value)

    print("Generating base PDF using knotpy...")

    kp.export_pdf(knot_diagrams, temp_pdf)

    print("Adding signatures to PDF...")

    add_signatures_to_pdf(temp_pdf, saved_names, final_pdf)

    if os.path.exists(temp_pdf):
        os.remove(temp_pdf)

    print(f"Success! Final PDF saved as: {final_pdf}")