import Std

/-! Trace polynomials for the oscillator realization on traceless matrices.
The statements use concrete three by three matrices over a commutative
ring. All formulas clear denominators, including the gradient identities. -/
namespace MatrixSymbols
open Lean.Grind
set_option maxHeartbeats 15000000

structure Mat (R : Type) where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R
  g : R
  h : R
  i : R

variable {R : Type} [CommRing R]

def mul (x y : Mat R) : Mat R :=
  ⟨x.a*y.a+x.b*y.d+x.c*y.g, x.a*y.b+x.b*y.e+x.c*y.h, x.a*y.c+x.b*y.f+x.c*y.i,
   x.d*y.a+x.e*y.d+x.f*y.g, x.d*y.b+x.e*y.e+x.f*y.h, x.d*y.c+x.e*y.f+x.f*y.i,
   x.g*y.a+x.h*y.d+x.i*y.g, x.g*y.b+x.h*y.e+x.i*y.h, x.g*y.c+x.h*y.f+x.i*y.i⟩

def tr (x : Mat R) : R := x.a+x.e+x.i

def square (x : Mat R) : Mat R := mul x x

/-- Three times the projection to traceless matrices for the trace pairing. -/
def proj3 (x : Mat R) : Mat R :=
  ⟨3*x.a-tr x, 3*x.b, 3*x.c, 3*x.d, 3*x.e-tr x, 3*x.f,
   3*x.g, 3*x.h, 3*x.i-tr x⟩

/-- The gradient of tr(X³) on the trace-zero space. -/
def cubicGradient (x : Mat R) : Mat R := proj3 (square x)

theorem projection_trace (x : Mat R) : tr (proj3 x) = 0 := by
  simp only [tr, proj3]
  grind

theorem projection_pairing (x y : Mat R) :
    tr (mul (proj3 x) (proj3 y)) =
      9 * tr (mul x y) - 3 * tr x * tr y := by
  simp only [tr, mul, proj3]
  grind

/-- The two extreme cubics recover the degree-four mixed invariant. -/
theorem mixed_quartic (x y : Mat R) :
    tr (mul (cubicGradient x) (cubicGradient y)) =
      9 * tr (mul (square x) (square y)) - 3 * tr (square x) * tr (square y) :=
  projection_pairing (square x) (square y)

theorem traceless_quartic (x : Mat R) (hx : tr x = 0) :
    2 * tr (square (square x)) = (tr (square x))^2 := by
  cases x with
  | mk a b c d e f g h i =>
    simp only [tr] at hx
    have hi : i = -a-e := by grind
    subst i
    simp only [square, mul, tr]
    grind

/-- Twice the scalar symbol of the double oscillator commutator
[T,[F,T]] is three times tr(X²)². With E=tr(X²)/2 this is [T,[F,T]]=6E². -/
theorem cubic_gradient_norm (x : Mat R) (hx : tr x = 0) :
    2 * tr (square (cubicGradient x)) = 3 * (tr (square x))^2 := by
  have hpair := mixed_quartic x x
  have hquartic := traceless_quartic x hx
  change tr (square (cubicGradient x)) =
    9 * tr (square (square x)) - 3 * tr (square x) * tr (square x) at hpair
  grind

end MatrixSymbols
