import Std

/-!
The simultaneous highest-weight calculation for the oscillator realization of
sp₄ × so₄. Polynomials are represented by expressions in eight variables; an
identity is proved after evaluation in every commutative ring. In each of two
matrix slots the four coordinates are the entries f, g, h, k, so det = fk−gh.
The parameter r is m−n: every pair m ≥ n has the form (r+n,n).
-/
namespace OscillatorWeights
open Lean.Grind
attribute [local instance] Semiring.natCast
set_option maxHeartbeats 2500000

inductive Slot | first | second deriving DecidableEq
inductive Entry | f | g | h | k deriving DecidableEq
abbrev Index := Slot × Entry

inductive Poly
  | zero | one | coord (i : Index)
  | sub (p q : Poly) | add (p q : Poly) | mul (p q : Poly)

variable {R : Type} [CommRing R]

/-- Evaluation is universal in the coefficient ring. -/
def ev (x : Index → R) : Poly → R
  | .zero => 0 | .one => 1 | .coord i => x i
  | .sub p q => ev x p - ev x q
  | .add p q => ev x p + ev x q
  | .mul p q => ev x p * ev x q

/-- The vector field whose value on coordinate i is v i. -/
def deriv (v : Index → Poly) : Poly → Poly
  | .zero => .zero | .one => .zero | .coord i => v i
  | .sub p q => .sub (deriv v p) (deriv v q)
  | .add p q => .add (deriv v p) (deriv v q)
  | .mul p q => .add (.mul (deriv v p) q) (.mul p (deriv v q))

def power (p : Poly) : Nat → Poly
  | 0 => .one
  | n+1 => .mul (power p n) p

def f₁ := Poly.coord (.first,.f)
def g₁ := Poly.coord (.first,.g)
def f₂ := Poly.coord (.second,.f)
def g₂ := Poly.coord (.second,.g)
def minor := Poly.sub (.mul f₁ g₂) (.mul g₁ f₂)
def vector (r n : Nat) := Poly.mul (power f₁ r) (power minor n)

private theorem weight_power (x : Index → R) (v : Index → Poly)
    (p : Poly) (a : R) (h : ev x (deriv v p) = a * ev x p) (n : Nat) :
    ev x (deriv v (power p n)) = ((n:R)*a) * ev x (power p n) := by
  induction n with
  | zero => simp only [power, deriv, ev]; grind
  | succ n ih =>
    simp only [power, deriv, ev]
    rw [ih, h]
    grind

private theorem weight_vector (x : Index → R) (v : Index → Poly)
    (r n : Nat) (a b : R) (ha : ev x (deriv v f₁) = a * ev x f₁)
    (hb : ev x (deriv v minor) = b * ev x minor) :
    ev x (deriv v (vector r n)) =
    ((r:R)*a + (n:R)*b) * ev x (vector r n) := by
  change ev x (deriv v (power f₁ r)) * ev x (power minor n) +
    ev x (power f₁ r) * ev x (deriv v (power minor n)) = _
  rw [weight_power x v f₁ a ha, weight_power x v minor b hb]
  change _ = _ * (ev x (power f₁ r) * ev x (power minor n))
  grind

inductive Positive | left | right | polar
/-- Simple positive root actions from the two orthogonal sl₂ factors and
the slot raising polarization. -/
def raiseDir : Positive → Index → Poly
  | .left, (s,.h) => .coord (s,.f)
  | .left, (s,.k) => .coord (s,.g)
  | .right, (s,.g) => .coord (s,.f)
  | .right, (s,.k) => .coord (s,.h)
  | .polar, (.second,j) => .coord (.first,j)
  | _, _ => .zero

theorem raising_annihilates (x : Index → R) (i : Positive) (r n : Nat) :
    ev x (deriv (raiseDir i) (vector r n)) = 0 := by
  have ha : ev x (deriv (raiseDir i) f₁) = 0 * ev x f₁ := by
    cases i <;> simp only [f₁, deriv, raiseDir, ev] <;> grind
  have hb : ev x (deriv (raiseDir i) minor) = 0 * ev x minor := by
    cases i <;> simp only [minor, f₁, f₂, g₁, g₂, deriv, raiseDir, ev] <;> grind
  rw [weight_vector x (raiseDir i) r n 0 0 ha hb]
  grind

inductive Cartan | left | right | slot (s : Slot)
def cartanDir : Cartan → Index → Poly
  | .left, (s,j) => match j with
    | .f | .g => .coord (s,j)
    | .h | .k => .sub .zero (.coord (s,j))
  | .right, (s,j) => match j with
    | .f | .h => .coord (s,j)
    | .g | .k => .sub .zero (.coord (s,j))
  | .slot s, (t,j) => if s = t then .coord (t,j) else .zero

private def fWeight : Cartan → R
  | .left | .right | .slot .first => 1
  | .slot .second => 0
private def minorWeight : Cartan → R
  | .left => 2 | .right => 0 | .slot _ => 1

def weight (r n : Nat) : Cartan → R
  | .left => (r:R)+2*(n:R)
  | .right => (r:R)
  | .slot .first => (r:R)+(n:R)
  | .slot .second => (n:R)

theorem cartan_eigenvalues (x : Index → R) (i : Cartan) (r n : Nat) :
    ev x (deriv (cartanDir i) (vector r n)) = weight r n i * ev x (vector r n) := by
  have ha : ev x (deriv (cartanDir i) f₁) = fWeight i * ev x f₁ := by
    cases i with
    | left | right => simp only [f₁, deriv, cartanDir, fWeight, ev]; grind
    | slot s => cases s <;> simp [f₁, deriv, cartanDir, fWeight, ev] <;> grind
  have hb : ev x (deriv (cartanDir i) minor) = minorWeight i * ev x minor := by
    cases i with
    | left | right => simp only [minor, f₁, f₂, g₁, g₂, deriv, cartanDir, minorWeight, ev]; grind
    | slot s => cases s <;> simp [minor, f₁, f₂, g₁, g₂, deriv, cartanDir, minorWeight, ev] <;> grind
  rw [weight_vector x (cartanDir i) r n (fWeight i) (minorWeight i) ha hb]
  cases i with
  | left | right => simp only [fWeight, minorWeight, weight]; grind
  | slot s => cases s <;> simp only [fWeight, minorWeight, weight] <;> grind

/-- The oscillator Cartan operator in slot s is Euler_s + dim(V)/2. -/
theorem symplectic_eigenvalues (x : Index → R) (s : Slot) (r n : Nat) :
    ev x (deriv (cartanDir (.slot s)) (vector r n)) + 2 * ev x (vector r n) =
    (weight r n (.slot s) + 2) * ev x (vector r n) := by
  rw [cartan_eigenvalues]; grind

def unitDir (i j : Index) : Poly := if i = j then .one else .zero
def partialD (i : Index) := deriv (unitDir i)

private def topIndex (i : Index) : Prop := i.2 = .f ∨ i.2 = .g
private def top : Poly → Prop
  | .zero | .one => True
  | .coord i => topIndex i
  | .sub p q | .add p q | .mul p q => top p ∧ top q

private theorem top_partial (i : Index) (p : Poly) (h : top p) :
    top (partialD i p) := by
  induction p with
  | zero | one => trivial
  | coord j => simp only [partialD, deriv, unitDir]; split <;> trivial
  | sub p q hp hq | add p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | mul p q hp hq => exact ⟨⟨hp h.1,h.2⟩,⟨h.1,hq h.2⟩⟩

private theorem inactive (x : Index → R) (i : Index) (hi : ¬ topIndex i)
    (p : Poly) (h : top p) : ev x (partialD i p) = 0 := by
  induction p with
  | zero | one => rfl
  | coord j =>
    have hne : i ≠ j := by
      intro he
      subst j
      exact hi h
    simp [partialD, deriv, unitDir, hne, ev]
  | sub p q hp hq =>
    change ev x (partialD i p) - ev x (partialD i q) = 0
    rw [hp h.1,hq h.2]; grind
  | add p q hp hq =>
    change ev x (partialD i p) + ev x (partialD i q) = 0
    rw [hp h.1,hq h.2]; grind
  | mul p q hp hq =>
    change ev x (partialD i p) * ev x q + ev x p * ev x (partialD i q) = 0
    rw [hp h.1,hq h.2]; grind

private theorem top_power (p : Poly) (h : top p) (n : Nat) : top (power p n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,h⟩

private theorem top_vector (r n : Nat) : top (vector r n) := by
  exact ⟨top_power f₁ (Or.inl rfl) r, top_power minor
    ⟨⟨Or.inl rfl,Or.inr rfl⟩,⟨Or.inr rfl,Or.inl rfl⟩⟩ n⟩

/-- The polarization of the determinant Laplacian. Partial derivatives are
written with the bottom-row derivative on the left. -/
def contraction (s t : Slot) (p : Poly) : Poly :=
  .sub (.add (partialD (t,.k) (partialD (s,.f) p))
             (partialD (s,.k) (partialD (t,.f) p)))
       (.add (partialD (t,.h) (partialD (s,.g) p))
             (partialD (s,.h) (partialD (t,.g) p)))

theorem contractions_annihilate (x : Index → R) (s t : Slot) (r n : Nat) :
    ev x (contraction s t (vector r n)) = 0 := by
  have hk (s : Slot) : ¬ topIndex (s,.k) := by simp [topIndex]
  have hh (s : Slot) : ¬ topIndex (s,.h) := by simp [topIndex]
  simp only [contraction, ev]
  rw [inactive x _ (hk t) _ (top_partial _ _ (top_vector r n)),
      inactive x _ (hk s) _ (top_partial _ _ (top_vector r n)),
      inactive x _ (hh t) _ (top_partial _ _ (top_vector r n)),
      inactive x _ (hh s) _ (top_partial _ _ (top_vector r n))]
  grind

/-- A witness for nonvanishing: f₁ = g₂ = 1 and the other entries vanish. -/
def witness : Index → R
  | (.first,.f) | (.second,.g) => 1
  | _ => 0

private theorem power_one (x : Index → R) (p : Poly) (h : ev x p = 1)
    (n : Nat) : ev x (power p n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => change ev x (power p n) * ev x p = 1; rw [ih,h]; grind

theorem value_at_witness (r n : Nat) : ev (witness (R:=R)) (vector r n) = 1 := by
  have hm : ev (witness (R:=R)) minor = 1 := by
    simp only [minor, f₁, f₂, g₁, g₂, ev, witness]; grind
  change ev witness (power f₁ r) * ev witness (power minor n) = (1:R)
  rw [power_one _ _ rfl, power_one _ _ hm]
  grind

end OscillatorWeights
