"""Direct symbolic checks of the two modular orbit products in the manuscript.

Both free spectral parameters remain indeterminate.  All arithmetic is in
the polynomial ring F_p[t,r,s], including at p=11.  We multiply the
unfactored profiles over all translations, rather than assuming the
Artin--Schreier norm formula that gives the manuscript's short proof.
"""
from math import prod

from sympy import GF
from sympy.polys.rings import ring


def check_products(p):
    polynomials, t, r, s = ring("t,r,s", GF(p))
    x = t**p-t
    ell = [root**p-root for root in (r,s,-r-s)]

    # C2. Take c_i = lambda_i(lambda_i+1), lambda_i = r,s.
    c1, c2 = r*(r+1), s*(s+1)
    c2_norm = polynomials.one
    for j in range(p):
        z = t+j
        c2_norm *= (c1-z*(z+1))*(c2-z*(z+1))
    assert c2_norm == (x**2-ell[0]**2)*(x**2-ell[1]**2)
    assert ell[0] and ell[1] and ell[0]**2 != ell[1]**2
    print(f"PASS: C2 orbit product in F_{p}[t,r,s]")

    if p == 3:
        return  # The G2 reduction in the paper uses p > 3.

    # G2. The cubic g(z)-sqrt(beta) has roots r,s,-r-s.
    # sum of roots = 0; J+1 = r^2+rs+s^2; beta = (rs(-r-s))^2.
    cubic_slope = r**2+r*s+s**2
    beta = (r*s*(r+s))**2
    half = pow(2, -1, p)
    numerator, denominator = polynomials.one, polynomials.one
    for j in range(p):
        z = t+j
        shifted = z+half
        g = shifted**3-cubic_slope*shifted
        numerator *= 4*(g**2-beta)
        denominator *= z*(z+1)
    assert denominator == x**2
    assert numerator == 4*prod(x**2-value**2 for value in ell)
    roots = [polynomials.zero]+[value**2 for value in ell]
    assert all(a != b for i,a in enumerate(roots) for b in roots[:i])
    print(f"PASS: G2 numerator, denominator and four distinct branches in F_{p}[t,r,s]")


if __name__ == "__main__":
    for prime in (3, 5, 7, 11):
        check_products(prime)
