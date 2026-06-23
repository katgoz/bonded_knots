# Bonded Knots Classification Project

This project presents a systematic classification of **uncolored bonded knots** with singularity number 8-10.
Bonded knots are used as mathematical models of protein structures containing strong long-range interactions such as ionic bonds or disulfide bridges.

To the best of our knowledge, this is the first time such a classification has been performed, as no prior research has addressed this specific range of singularity numbers. 

The study identifies and distinguishes knot and link types by applying diagrammatic transformations and algebraic invariants to capture their underlying topological structure.


---

## Research Objective

The main objective of this work is to classify bonded knots with:

- Singularity number 8, 9, 10  
- At most 5 crossings  
- At least one bond  

The classification includes:

- Prime bonded knots and links  
- Connected sums of type #3  
- Exclusion of structures decomposable as #1 or #2 connected sums  

The classification is given up to mirror images, since obtaining a mirror image of a knot is straightforward, and this reduces the classification complexity by nearly half.

---

## Methodology

The classification is performed using:

- Generation of bonded knot diagrams
- Computation of Yamada polynomial
- Detection of knot equivalence classes using automated simplification (Reidemeister moves)
- Unplugging

---



## Project Structure

```
bonded_knots/
│
├── classification/
│   ├── 8/
│   ├── 9/
│   └── 10/
│
├── scripts/
│   ├── __init__.py
│   │
│   ├── unplug.py
│   │
│   ├── automated_simplification/
│   │   ├── __init__.py
│   │   ├── find_strand_flip_move.py
│   │   └── outer_nodes.py
│   │
│   └── data_handling/
│
├── data_pipeline/
│   ├── 01_automated_simplification/
│   ├── 02_unplugging/
│   ├── 03_final_merged/
│   └── 04_no_mirrors/
│
├── classification_of_bonded_knots.pdf
└── README.md
```

---



### classification/

This folder contains the **main results of the classification**.

It includes:
- Excel files with:
  - Yamada polynomial values
  - PD-code representations
  - representative knot/link diagrams (selected after simplification)
- PDF files containing **visualizations of the corresponding knot diagrams**

Each singularity number (8, 9, 10) is organized separately.

---

### scripts/

This folder contains all implementation code used in the project.

The most important part of the pipeline is located in:

* **`automated_simplification/`** — Core algorithms for diagram simplification and equivalence detection.
  * **`find_strand_flip_move.py`** — Implements strand flip operations used in knot transformations and equivalence checking.
  * **`outer_nodes.py`** — Main script for automated simplification of knot diagrams by moving vertices outward.

* **`unplug.py`** — Implementation of the unplugging operation used as a structural invariant.

* **`data_handling/`** — Auxiliary scripts for data processing (Excel handling, renaming, mirror elimination, plotting, exporting diagrams).
---

### data_pipeline/

This folder contains the results from each step of the computational pipeline used to generate the final classification.

* **`01_automated_simplification/`** — Initial classification after automated simplification.
  * Each of the groups is divided into structural categories:
    * `prime`
    * `prime_sum`
    * `2_comp`
    * `2_comp_sum`
  * Results are then further split into two main groups:
    * **`merged`** — A single representative from each Yamada equivalence class identified after simplification.
    * **`not_merged`** — Diagrams that were not identified as equivalent within Yamada groups (non-equivalent or unresolved).

  * All results are stored in Excel files containing: **Yamada polynomial values**, **PD-code representations**, and **Classification labels**.

* **`02_unplugging/`** — Contains cases where the unplugging operation produced identical results for different diagrams.
  * These cases required **manual verification**.
  * Includes Excel files and PDF documents with manual analysis.

* **`03_final_merged/`** — Complete, unified dataset after incorporating unplugging corrections, before mirror reduction.

* **`04_no_mirrors/`** — Final step where mirror duplicates were removed. At this stage, files are still divided into the four structural categories (`prime`, `prime_sum`, `2_comp`, `2_comp_sum`).

> **Note:** Across all pipeline stages, diagram indexing was independent. All results are merged into a single, consistent global indexing system only in the final `classification/` stage.

---

### classification_of_bonded_knots.pdf

This document contains the theoretical background and full description of the computational framework used in the project, including:

- generation of bonded knot diagrams  
- computation of the Yamada polynomial  
- automated simplification procedures  
- implementation details of the Python pipeline  

It serves as a complete reference for the methodology and implementation.


---


## Reference

This work is based on the following thesis:
* **Katarzyna Gozdek**, *Mathematical classification of bonded
links and its application to proteins*, University of Warsaw, 2026.