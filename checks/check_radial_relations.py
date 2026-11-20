"""Verify the type-G2 radial identities in the zero-weight quotient of U(gl3).

The traceless version gives the same algebra because the scalar diagonal
generator acts by zero. Only weight-zero expressions are multiplied after
the projection to the quotient.
"""
from collections import Counter
from functools import cache


root_order = [(1, 2), (2, 1), (2, 3), (3, 2), (3, 1), (1, 3)]
letters = root_order + [(1, 1), (2, 2), (3, 3)]
rank = {letter: i for i, letter in enumerate(letters)}


@cache
def ordered(word):
    """Apply Eij Ekl = Ekl Eij + delta(j,k) Eil - delta(l,i) Ekj."""
    for pos in range(len(word) - 1):
        first, second = word[pos:pos + 2]
        if rank[first] <= rank[second]:
            continue
        left, right = word[:pos], word[pos + 2:]
        terms = Counter(ordered(left + (second, first) + right))
        i, j = first
        k, l = second
        if j == k:
            terms.update(ordered(left + ((i, l),) + right))
        if i == l:
            terms.subtract(ordered(left + ((k, j),) + right))
        return {monomial: coeff for monomial, coeff in terms.items() if coeff}
    return {word: 1}


class Operator(dict):
    def __add__(self, other):
        result = Counter(self)
        result.update(other)
        return Operator({m: c for m, c in result.items() if c})

    def __neg__(self):
        return Operator({m: -c for m, c in self.items()})

    def __sub__(self, other):
        return self + (-other)

    def __rmul__(self, scalar):
        return Operator({m: scalar * c for m, c in self.items() if scalar * c})

    def __mul__(self, other):
        result = Counter()
        for a, ca in self.items():
            for b, cb in other.items():
                for monomial, coeff in ordered(a + b).items():
                    if monomial and monomial[-1] not in root_order:
                        continue
                    result[monomial] += ca * cb * coeff
        return Operator({m: c for m, c in result.items() if c})

    def comm(self, other):
        return self * other - other * self

    def anticom(self, other):
        return self * other + other * self


def pair(i, j):
    return Operator(ordered(((i, j), (j, i))))


def projected_word(*word):
    """PBW expansion modulo the rightmost Cartan generators."""
    return Operator({monomial: coefficient
                     for monomial, coefficient in ordered(word).items()
                     if not monomial or monomial[-1] in root_order})


A, B, D = pair(1, 2), pair(2, 3), pair(3, 1)
J = A + B + D
N = A.comm(B)
V = 4*(A-B)
W = D.comm(V)

# The cubic words are the two triangles in the manuscript's root order.
u, v, j, k, l, m = root_order
R, R_prime = projected_word(u, j, l), projected_word(v, k, m)
assert N == A-B+D-R+R_prime
assert B.comm(N) == 2*(B*D-A*B)
assert A.comm(N) == 2*(A*B-A*D-A+B-D+R-R_prime)

quadratic_casimir = Operator()
for i in range(1, 4):
    for j in range(1, 4):
        quadratic_casimir += projected_word((i,j),(j,i))
assert quadratic_casimir == 2*J

assert not J.comm(A) and not J.comm(B)
assert A.comm(N) == A.anticom(B)-A.anticom(D)
assert B.comm(N) == B.anticom(D)-A.anticom(B)
assert W == 8*N
assert D.comm(W) == 2*D.anticom(V)
assert V.comm(W) + 2*V*V == 32*(J-D)*(J-3*D)
print("PASS: G2 quadratic Casimir, three PBW normal forms and angular commutators")
