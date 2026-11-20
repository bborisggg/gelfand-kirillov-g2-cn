# Gelfand-Kirillov hypothesis for G_2 and type C is false

## A valuation obstruction to Weyl coordinates in types C and G2

WeylCoordinates.tex is the complete manuscript. Compile it with pdflatex twice.
SOURCE-NOTES.md identifies the published inputs.

For the Python checks, install SymPy and run
    python checks/check_cubic_casimir.py
    python checks/check_orbit_products.py
The first entry point also checks the angular commutators and coordinate identities.

The Lean supplement can be rebuilt with native Lean 4.28.0 on PATH:
    cd lean
    python verify.py

lean/README.md gives the precise scope of the formal results. lean/Axioms.txt
is the axiom report from the included sources. SHA256SUMS covers every other
file in this archive.
