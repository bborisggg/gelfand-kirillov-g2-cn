import OscillatorCasimir

/-! On either matrix factor the quadratic Casimir for row multiplication
is equal to that for column multiplication, on every polynomial. Since the
six infinitesimal actions annihilate the determinant, they also act on its
level-one coordinate ring. -/
namespace OscillatorWeights
open Lean.Grind
set_option maxHeartbeats 4500000
variable {R : Type} [CommRing R]

private def localDir (s : Slot) (v : Index → Poly) (i : Index) : Poly :=
  if i.1 = s then v i else .zero

def matrixE (s : Slot) (i : Factor) := localDir s (raiseDir i.positive)
def matrixF (s : Slot) (i : Factor) := localDir s (lowerDir i)
def matrixH (s : Slot) (i : Factor) := localDir s (cartanDir i.cartan)

def matrixCasimir (x : Index → R) (s : Slot) (i : Factor) (p : Poly) : R :=
  4 * ev x (deriv (matrixF s i) (deriv (matrixE s i) p)) +
    ev x (deriv (matrixH s i) (deriv (matrixH s i) p)) +
    2 * ev x (deriv (matrixH s i) p)

/-- The portion of the product rule in which one derivative hits each factor. -/
private def pairing (x : Index → R) (s : Slot) (i : Factor) (p q : Poly) : R :=
  4 * (ev x (deriv (matrixE s i) p) * ev x (deriv (matrixF s i) q) +
       ev x (deriv (matrixF s i) p) * ev x (deriv (matrixE s i) q)) +
  2 * ev x (deriv (matrixH s i) p) * ev x (deriv (matrixH s i) q)

private theorem pairing_symmetric (x : Index → R) (s : Slot) (i : Factor) (p q : Poly) :
    pairing x s i p q = pairing x s i q p := by
  unfold pairing; grind

private theorem pairing_add (x : Index → R) (s : Slot) (i : Factor) (p q t : Poly) :
    pairing x s i p (.add q t) = pairing x s i p q + pairing x s i p t := by
  simp only [pairing,deriv,ev]; grind

private theorem pairing_sub (x : Index → R) (s : Slot) (i : Factor) (p q t : Poly) :
    pairing x s i p (.sub q t) = pairing x s i p q - pairing x s i p t := by
  simp only [pairing,deriv,ev]; grind

private theorem pairing_mul (x : Index → R) (s : Slot) (i : Factor) (p q t : Poly) :
    pairing x s i p (.mul q t) = pairing x s i p q * ev x t + ev x q * pairing x s i p t := by
  simp only [pairing,deriv,ev]; grind

private theorem pairing_coordinates (x : Index → R) (s : Slot) (a b : Index) :
    pairing x s .left (.coord a) (.coord b) = pairing x s .right (.coord a) (.coord b) := by
  rcases a with ⟨a,j⟩
  rcases b with ⟨b,q⟩
  by_cases ha : a = s
  · subst a
    by_cases hb : b = s
    · subst b; cases j <;> cases q <;>
        simp [pairing,deriv,ev,matrixE,matrixF,matrixH,localDir,Factor.positive,Factor.cartan,raiseDir,lowerDir,cartanDir] <;> grind
    · simp [pairing,deriv,ev,matrixE,matrixF,matrixH,localDir,hb]; grind
  · simp [pairing,deriv,ev,matrixE,matrixF,matrixH,localDir,ha]; grind

private theorem pairing_extend (x : Index → R) (s : Slot) (p : Poly)
    (h : ∀ j, pairing x s .left p (.coord j) = pairing x s .right p (.coord j)) (q : Poly) :
    pairing x s .left p q = pairing x s .right p q := by
  induction q with
  | zero | one => simp only [pairing,deriv,ev]; grind
  | coord j => exact h j
  | add q t hq ht => rw [pairing_add, pairing_add, hq, ht]
  | sub q t hq ht => rw [pairing_sub, pairing_sub, hq, ht]
  | mul q t hq ht => rw [pairing_mul, pairing_mul, hq, ht]

private theorem pairing_equal (x : Index → R) (s : Slot) (p q : Poly) :
    pairing x s .left p q = pairing x s .right p q := by
  apply pairing_extend
  intro j
  rw [pairing_symmetric x s .left p, pairing_symmetric x s .right p]
  exact pairing_extend x s (.coord j) (pairing_coordinates x s j) p

private theorem casimir_add (x : Index → R) (s : Slot) (i : Factor) (p q : Poly) :
    matrixCasimir x s i (.add p q) = matrixCasimir x s i p + matrixCasimir x s i q := by
  simp only [matrixCasimir,deriv,ev]; grind

private theorem casimir_sub (x : Index → R) (s : Slot) (i : Factor) (p q : Poly) :
    matrixCasimir x s i (.sub p q) = matrixCasimir x s i p - matrixCasimir x s i q := by
  simp only [matrixCasimir,deriv,ev]; grind

private theorem casimir_mul (x : Index → R) (s : Slot) (i : Factor) (p q : Poly) :
    matrixCasimir x s i (.mul p q) =
    matrixCasimir x s i p * ev x q + ev x p * matrixCasimir x s i q + pairing x s i p q := by
  simp only [matrixCasimir,pairing,deriv,ev]; grind

private theorem casimir_coord (x : Index → R) (s : Slot) (a : Index) :
    matrixCasimir x s .left (.coord a) = matrixCasimir x s .right (.coord a) := by
  rcases a with ⟨t,j⟩
  by_cases ht : t = s
  · subst t
    cases j <;> simp [matrixCasimir,matrixE,matrixF,matrixH,localDir,Factor.positive,Factor.cartan,
      raiseDir,lowerDir,cartanDir,deriv,ev] <;> grind
  · simp [matrixCasimir,matrixE,matrixF,matrixH,localDir,ht,deriv,ev]

/-- The left- and right-multiplication Casimirs coincide on all polynomial
expressions in the entries of the pair of matrices, for either factor. -/
theorem left_right_casimir (x : Index → R) (s : Slot) (p : Poly) :
    matrixCasimir x s .left p = matrixCasimir x s .right p := by
  induction p with
  | zero | one => rfl
  | coord a => exact casimir_coord x s a
  | add p q hp hq => rw [casimir_add, casimir_add, hp, hq]
  | sub p q hp hq => rw [casimir_sub, casimir_sub, hp, hq]
  | mul p q hp hq => rw [casimir_mul, casimir_mul, hp, hq, pairing_equal]

def determinant (s : Slot) : Poly :=
  .sub (.mul (.coord (s,.f)) (.coord (s,.k)))
       (.mul (.coord (s,.g)) (.coord (s,.h)))

/-- All six row/column infinitesimal generators are tangent to SL₂. -/
theorem determinant_directions (x : Index → R) (s : Slot) (i : Factor) :
    ev x (deriv (matrixE s i) (determinant s)) = 0 ∧
    ev x (deriv (matrixF s i) (determinant s)) = 0 ∧
    ev x (deriv (matrixH s i) (determinant s)) = 0 := by
  cases i <;> simp [determinant,matrixE,matrixF,matrixH,localDir,Factor.positive,Factor.cartan,
      raiseDir,lowerDir,cartanDir,deriv,ev] <;> (repeat' apply And.intro) <;> grind

end OscillatorWeights
