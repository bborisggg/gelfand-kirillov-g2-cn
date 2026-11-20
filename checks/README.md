Exact Python checks
===================

Run these commands in this directory with Python 3.9+ and SymPy installed.

    python check_cubic_casimir.py
    python check_orbit_products.py

The first command also runs the assertions in its two helper scripts.
check_radial_relations.py sorts matrix-unit words and discards terminal
Cartan terms in the weight-zero quotient. It checks the three hand
normal forms, the quadratic Casimir and the angular commutators.
check_identities.py multiplies skew Laurent operators and checks the
G2 shift identities, the cubic norm polynomial and the C2 quartic.
check_cubic_casimir.py independently identifies the squared cubic
Casimir and the integration parameter in the radial and shift models.

The same run verifies the explicit C2 Weyl pair after ordering the central roots, its commutator and its corrected derivative.

check_orbit_products.py multiplies all p translates of the two profiles
as polynomials in F_p[t,r,s], where r,s are independent spectral roots.
For C2 it reproduces the quartic orbit polynomial for p=3,5,7,11. For G2
it checks the sextic orbit numerator, the denominator and all four
branch points for p=5,7,11. No parameter is sampled. The proof for all
good primes uses the Artin-Schreier polynomial identity in the paper.

These scripts check algebraic computations. They do not formalize the
proof involving division rings, valuations, descent, or the Brauer group.
