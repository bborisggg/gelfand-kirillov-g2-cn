"""Verify the exact normalization of the G2 translation parameter.
Run beside check_radial_relations.py and check_identities.py.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
from check_radial_relations import D, J, V, W, Operator, ordered, root_order
import check_identities as shift

beta = (D*(D-J)*(D-J)+(2*D-J)*(2*D-J)
        - Fraction(1,16)*V*D*V + Fraction(1,64)*W*W)
terms = defaultdict(Fraction)
for i,j,k in product(range(1,4),repeat=3):
    for word in permutations(((i,j),(j,k),(k,i))):
        for monomial, coeff in ordered(word).items():
            if not monomial or monomial[-1] in root_order:
                terms[monomial] += Fraction(coeff,6)
omega = Operator({monomial:c for monomial,c in terms.items() if c})
assert omega*omega == 9*beta

D, V, W = shift.D, shift.V, shift.W
t, J, b = shift.t, shift.J, shift.beta
d = D[0]
profile = shift.combine((1,shift.product(shift.product(V,D),V)),
                        (-shift.quarter,shift.product(W,W)))
assert set(profile)=={0}
value = profile[0].xreplace({shift.f(t):shift.h(t),shift.f(t-1):shift.h(t-1)})
shift.zero(d*(d-J)**2+(2*d-J)**2-value/16-b)
print("PASS: squared PBW cubic Casimir equals 9 times the G2 shift parameter")
