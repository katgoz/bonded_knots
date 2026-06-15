# Bonded Knots Classification Project

This project presents a systematic classification of **uncolored bonded knots** with singularity number 8-10.
Bonded knots are used as mathematical models of protein structures containing strong long-range interactions such as ionic bonds or disulfide bridges.

To the best of our knowledge, this is the first time such a classification has been performed, as no prior research has addressed this specific range of singularity numbers. 

The study identifies and distinguishes knot and link types by applying diagrammatic transformations and algebraic invariants to capture their underlying topological structure.


---

## Research Objective

The main objective of this work is to classify bonded knots with:

- Singularity number ≤ 10  
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

## Data Overview (Results)

Results are grouped by singularity number:

- 8 singularities
- 9 singularities
- 10 singularities

Each group is divided into:

- prime
- prime_sum
- 2_comp
- 2_comp_sum

Additionally, datasets are split into:

- merged (a single representative from each Yamada equivalence class identified after simplification)
- non-merged (diagrams that were not identified as equivalent within Yamada groups after simplification)

All results are stored in Excel files containing:

- Yamada polynomial values
- PD-code representations
- Classification labels

---

## Project Structure

```
results/
├── 8/
│   ├── 2_comp/
│   ├── 2_comp_sum/
│   ├── prime/
│   └── prime_sum/
│
├── 9/
│   ├── 2_comp/
│   ├── 2_comp_sum/
│   ├── prime/
│   └── prime_sum/
│
└── 10/
    ├── 2_comp/
    ├── 2_comp_sum/
    ├── prime/
    └── prime_sum/

code/
├── find_strand_flip_move_new.py
├── outer_nodes.py
└── unplug.py

knots.pdf
README.md
```

---

## Code Description

### find_strand_flip_move_new.py
Implements strand flip operations used in knot transformations and equivalence checking.

### outer_nodes.py
Main script for automated simplification of knot diagrams by moving vertices outward.

### unplug.py
Implements the unplugging operation used as an invariant for bonded knot structures.

---

## knots.pdf

This document contains a detailed description of the theoretical background, computational methods, and implementation details used in the project. 

The PDF documents the full pipeline of the classification process, including:
- generation of bonded knot diagrams,
- the use of Yamada polynomial,
   automated simplification procedures.

It also provides an overview of the Python implementation and describes how each script contributes to the overall classification workflow.


## Reference

This work is based on a thesis on computational classification of bonded knots.
