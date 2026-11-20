"""Exact computations for the local coordinate calculations in the paper.
Run with Python 3 and SymPy. No sampling or floating-point arithmetic is used.
"""
import sympy as sp

t, J, beta = sp.symbols("t J beta")
r, s, u = sp.symbols("r s u")
f = sp.Function("f")
half = sp.Rational(1, 2)
quarter = half**2


def zero(expr):
    assert sp.cancel(expr) == 0, expr


def product(left, right):
    """Coefficients on the left of e^i, with e t = (t-1)e."""
    terms = {}
    for i, a in left.items():
        for j, b in right.items():
            terms[i+j] = terms.get(i+j, 0) + a*b.subs(t, t-i)
    return terms


def combine(*summands):
    terms = {}
    for scale, expr in summands:
        for i, coef in expr.items():
            terms[i] = terms.get(i, 0) + scale*coef
    return {i: coef for i, value in terms.items() if (coef := sp.factor(value)) != 0}


def bracket(left, right, second_sign=-1):
    return combine((1, product(left, right)), (second_sign, product(right, left)))


D = {0: t**2-quarter}
V = {1: sp.Integer(1), -1: f(t)}
W = bracket(D, V)
assert not combine((1, bracket(D, W)), (-2, bracket(D, V, 1)))
lhs = combine((1, bracket(V, W)), (2, product(V, V)))
assert set(lhs) == {0}
zero(lhs[0] - 4*((t+1)*f(t)-(t-1)*f(t-1)))


def g(x):
    return x**3 - (J+1)*x


def h(x):
    return 4*(g(x+half)**2-beta)/(x*(x+1))


zero(lhs[0].xreplace({f(t): h(t), f(t-1): h(t-1)})
     - 32*(J-D[0])*(J-3*D[0]))
zero(h(-t)-h(t-1))
ell = (r, s, -r-s)
a = -sum(x*y for i,x in enumerate(ell) for y in ell[i+1:])
d = sp.prod(ell)**2
zero(-sp.prod(u-x**2 for x in ell) - d+u*(u-a)**2)


def P(x):
    return (r-x*(x+1))*(s-x*(x+1))


zero(P(-t)-P(t-1))
zero(P(t-1)-P(t)+4*t**3-2*(r+s)*t)
print("PASS: C2 quartic reflection and finite difference")
print("PASS: G2 full Laurent support of both commutators")
print("PASS: G2 shift weight, reflection and modular cubic norm polynomial")

# The C2 chart after ordering the central roots.  delta=theta^2,
# [t,v]=v, so [t,q(v)] = v*dq/dv on the rational coefficient field.
v, theta = sp.symbols("v theta", nonzero=True)
def Qroot(argument):
    return (argument-r)*(argument-s)

scalar_profile = P(t).subs({r:r*(r+1), s:s*(s+1)}, simultaneous=True)
zero(scalar_profile-Qroot(t)*Qroot(-t-1))
position = (v-1)/(theta*(v+1))
momentum_multiplier = theta*(v+1)**2/(2*v)
reflected = {v:1/v, theta:-theta}
zero(position.subs(reflected, simultaneous=True)-position)
zero(momentum_multiplier.subs(reflected, simultaneous=True)+momentum_multiplier)
zero(momentum_multiplier*v*sp.diff(position,v)-1)
zero(sp.diff(position,theta)/(2*theta)+position/(2*theta**2))
zero(sp.diff(momentum_multiplier,theta)/(2*theta)-momentum_multiplier/(2*theta**2))
print("PASS: C2 central-root factorization, invariant Weyl pair and corrected derivative")
