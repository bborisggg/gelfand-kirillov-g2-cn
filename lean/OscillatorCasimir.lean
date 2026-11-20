import OscillatorWeights

/-! Twice-differentiated highest-weight identities in the determinant
oscillator. The normalized angular Casimir is 4FE + H² + 2H. -/

namespace OscillatorWeights
open Lean.Grind
attribute [local instance] Semiring.natCast
set_option maxHeartbeats 2500000

variable {R : Type} [CommRing R]

/-- The second equality verifies the result of further differentiation in
direction w. Both derivatives act on the actual polynomial expression. -/
private def jet (x : Index → R) (v w : Index → Poly) (p : Poly) (a : R) : Prop :=
  ev x (deriv v p) = a * ev x p ∧
  ev x (deriv w (deriv v p)) = a * ev x (deriv w p)

private theorem jet_mul (x : Index → R) (v w : Index → Poly)
    (p q : Poly) (a b : R) (hp : jet x v w p a) (hq : jet x v w q b) :
    jet x v w (.mul p q) (a+b) := by
  obtain ⟨hp₁,hp₂⟩ := hp
  obtain ⟨hq₁,hq₂⟩ := hq
  constructor
  · simp only [deriv, ev]; rw [hp₁,hq₁]; grind
  · simp only [deriv, ev]; rw [hp₂,hq₂,hp₁,hq₁]; grind

private theorem jet_power (x : Index → R) (v w : Index → Poly)
    (p : Poly) (a : R) (hp : jet x v w p a) (n : Nat) :
    jet x v w (power p n) ((n:R)*a) := by
  induction n with
  | zero => unfold jet; simp only [power, ev, deriv]; constructor <;> grind
  | succ n ih =>
    have h := jet_mul x v w (power p n) p ((n:R)*a) a ih hp
    have he : (((n+1:Nat):R)*a) = (n:R)*a + a := by grind
    rw [he]
    exact h

private theorem jet_vector (x : Index → R) (v w : Index → Poly)
    (r n : Nat) (a b : R) (hp : jet x v w f₁ a) (hq : jet x v w minor b) :
    jet x v w (vector r n) ((r:R)*a+(n:R)*b) :=
  jet_mul x v w _ _ _ _ (jet_power x v w f₁ a hp r) (jet_power x v w minor b hq n)

inductive Factor | left | right

def Factor.positive : Factor → Positive | .left => .left | .right => .right
def Factor.cartan : Factor → Cartan | .left => .left | .right => .right

/-- Lower the corresponding row or column of each 2×2 matrix. -/
def lowerDir : Factor → Index → Poly
  | .left, (s,.f) => .coord (s,.h)
  | .left, (s,.g) => .coord (s,.k)
  | .right, (s,.f) => .coord (s,.g)
  | .right, (s,.h) => .coord (s,.k)
  | _, _ => .zero

def fourCasimir (x : Index → R) (i : Factor) (p : Poly) : R :=
  4 * ev x (deriv (lowerDir i) (deriv (raiseDir i.positive) p)) +
  ev x (deriv (cartanDir i.cartan) (deriv (cartanDir i.cartan) p)) +
  2 * ev x (deriv (cartanDir i.cartan) p)

private theorem twice_raise (x : Index → R) (i : Factor) (w : Index → Poly) (r n : Nat) :
    ev x (deriv w (deriv (raiseDir i.positive) (vector r n))) = 0 := by
  have hf : jet x (raiseDir i.positive) w f₁ 0 := by
    cases i <;> unfold jet <;> simp only [Factor.positive,f₁,deriv,raiseDir,ev] <;>
      constructor <;> grind
  have hm : jet x (raiseDir i.positive) w minor 0 := by
    cases i <;> unfold jet <;>
      simp only [Factor.positive,minor,f₁,g₁,f₂,g₂,deriv,raiseDir,ev] <;>
      constructor <;> grind
  have h := (jet_vector x _ w r n 0 0 hf hm).2
  grind

private def minorCartan : Factor → R | .left => 2 | .right => 0

private theorem twice_cartan (x : Index → R) (i : Factor) (w : Index → Poly) (r n : Nat) :
    ev x (deriv w (deriv (cartanDir i.cartan) (vector r n))) =
    weight r n i.cartan * ev x (deriv w (vector r n)) := by
  have hf : jet x (cartanDir i.cartan) w f₁ 1 := by
    cases i <;> unfold jet <;> simp only [Factor.cartan,f₁,deriv,cartanDir,ev] <;>
      constructor <;> grind
  have hm : jet x (cartanDir i.cartan) w minor (minorCartan i) := by
    cases i <;> unfold jet <;>
      simp only [minorCartan,Factor.cartan,minor,f₁,f₂,g₁,g₂,deriv,cartanDir,ev] <;>
      constructor <;> grind
  have h := (jet_vector x _ w r n 1 (minorCartan i) hf hm).2
  have he : ((r:R)*1+(n:R)*minorCartan i) = weight r n i.cartan := by
    cases i <;> simp only [minorCartan,weight,Factor.cartan] <;> grind
  rw [he] at h
  exact h

/-- If (m,n)=(r+n,n), the two normalized Casimir eigenvalues are
(m+n)(m+n+2) and (m−n)(m−n+2). -/
theorem angular_casimir_eigenvalue (x : Index → R) (i : Factor) (r n : Nat) :
    fourCasimir x i (vector r n) =
    weight r n i.cartan * (weight r n i.cartan + 2) * ev x (vector r n) := by
  unfold fourCasimir
  rw [twice_raise, twice_cartan, cartan_eigenvalues]
  grind

end OscillatorWeights
