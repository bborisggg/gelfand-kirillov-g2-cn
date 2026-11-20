import Std

/-! Exact algebraic lemmas for the C2 quartic and the G2 translation cubic.
The orbit lemmas are Frobenius identities in any commutative ring in which
5, 7, or 11 vanishes. They do not formalize a statement for every prime. -/

namespace CoordinateIdentities
open Lean.Grind
set_option maxHeartbeats 2500000

variable {R : Type} [CommRing R]

def quartic (a b t : R) : R :=
  (t * (t + 1))^2 - a * t * (t + 1) + b

theorem quartic_reflection (a b t : R) :
    quartic a b (-t) = quartic a b (t - 1) := by
  unfold quartic
  grind

theorem quartic_factorization (r s t : R) :
    quartic (r+s) (r*s) t = (t*(t+1)-r)*(t*(t+1)-s) := by
  unfold quartic
  grind

/-- For the roots l, k, −l−k of the depressed cubic. -/
theorem cubic_norm (l k x : R) :
    (x-l^2)*(x-k^2)*(x-(-l-k)^2) =
      x*(x-(l^2+l*k+k^2))^2 - (l*k*(-l-k))^2 := by
  grind

/-- After doubling the argument this equals eight times the paper's g. -/
def sexticRoot (j x : R) : R := x^3-4*(j+1)*x

theorem sextic_difference (j s : R) :
    (sexticRoot j (s+1))^2 - (sexticRoot j (s-1))^2 =
      4*s*(4*j+1-s^2)*(4*j+3-3*s^2) := by
  unfold sexticRoot
  grind


def orbit5 (x : R) : R :=
  x*(x+1)*(x+2)*(x+3)*(x+4)

private theorem falling5 (x : R) :
    orbit5 x - (x^5-x) = 5*(2*x^4 + 7*x^3 + 10*x^2 + 5*x) := by
  unfold orbit5
  grind

private theorem frobenius5 (t l : R) :
    (t-l)^5-t^5+l^5 = 5*(l^4*t - 2*l^3*t^2 + 2*l^2*t^3 - l*t^4) := by
  grind

theorem orbit_product_5 (t l : R) (hp : (5 : R) = 0) :
    orbit5 (t-l) = (t^5-t)-(l^5-l) := by
  have hf := falling5 (t-l)
  have hb := frobenius5 t l
  rw [hp] at hf hb
  grind

def orbit7 (x : R) : R :=
  x*(x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6)

private theorem falling7 (x : R) :
    orbit7 x - (x^7-x) = 7*(3*x^6 + 25*x^5 + 105*x^4 + 232*x^3 + 252*x^2 + 103*x) := by
  unfold orbit7
  grind

private theorem frobenius7 (t l : R) :
    (t-l)^7-t^7+l^7 = 7*(l^6*t - 3*l^5*t^2 + 5*l^4*t^3 - 5*l^3*t^4 + 3*l^2*t^5 - l*t^6) := by
  grind

theorem orbit_product_7 (t l : R) (hp : (7 : R) = 0) :
    orbit7 (t-l) = (t^7-t)-(l^7-l) := by
  have hf := falling7 (t-l)
  have hb := frobenius7 t l
  rw [hp] at hf hb
  grind

def orbit11 (x : R) : R :=
  x*(x+1)*(x+2)*(x+3)*(x+4)*(x+5)*(x+6)*(x+7)*(x+8)*(x+9)*(x+10)

private theorem falling11 (x : R) :
    orbit11 x - (x^11-x) = 11*(5*x^10 + 120*x^9 + 1650*x^8 + 14343*x^7 + 82005*x^6 + 310630*x^5 + 764500*x^4 + 1159416*x^3 + 966240*x^2 + 329891*x) := by
  unfold orbit11
  grind

private theorem frobenius11 (t l : R) :
    (t-l)^11-t^11+l^11 = 11*(l^10*t - 5*l^9*t^2 + 15*l^8*t^3 - 30*l^7*t^4 + 42*l^6*t^5 - 42*l^5*t^6 + 30*l^4*t^7 - 15*l^3*t^8 + 5*l^2*t^9 - l*t^10) := by
  grind

theorem orbit_product_11 (t l : R) (hp : (11 : R) = 0) :
    orbit11 (t-l) = (t^11-t)-(l^11-l) := by
  have hf := falling11 (t-l)
  have hb := frobenius11 t l
  rw [hp] at hf hb
  grind

end CoordinateIdentities
