import Std

/-! Zariski density of the shifted highest weights (m+1,n) with m ≥ n.
Polynomials are lists of coefficients in ascending order, allowing trailing
zeros. The characteristic-zero hypothesis is injectivity of the natural map. -/

namespace WeightDensity
open Lean.Grind
variable {K : Type} [Field K]
attribute [local instance] Semiring.natCast

def eval (x : K) : List K → K
  | [] => 0
  | a :: p => a + x * eval x p

def vanishingCoeffs : List K → Prop
  | [] => True
  | a :: p => a = 0 ∧ vanishingCoeffs p

private def tailsAt (t : K) : List K → List K
  | [] => []
  | a :: p => eval t (a :: p) :: tailsAt t p

private theorem tails_length (t : K) (p : List K) :
    (tailsAt t p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [tailsAt, ih]

private theorem eval_zero (x : K) (p : List K) :
    vanishingCoeffs p → eval x p = 0 := by
  induction p with
  | nil => intro; rfl
  | cons a p ih =>
    intro ⟨ha, hp⟩
    simp only [eval, ha, ih hp]
    grind

private theorem recover_zero_coeffs (t : K) (p : List K) :
    vanishingCoeffs (tailsAt t p) → vanishingCoeffs p := by
  induction p with
  | nil => intro; trivial
  | cons a p ih =>
    intro ⟨ha, hp⟩
    have h := ih hp
    refine ⟨?_, h⟩
    have hz := eval_zero t p h
    change a + t * eval t p = 0 at ha
    grind

private theorem synthetic_division (t x a : K) (p : List K) :
    eval x (a :: p) = eval t (a :: p) + (x-t)*eval x (tailsAt t p) := by
  induction p generalizing a with
  | nil => simp only [eval, tailsAt]; grind
  | cons b q ih =>
    have h := ih b
    simp only [eval, tailsAt] at h ⊢
    grind

/-- A polynomial over a characteristic-zero field that vanishes at all
    sufficiently large integers has every coefficient zero. -/
theorem integer_tail (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j)
    (p : List K) (k : Nat)
    (h : ∀ n : Nat, k ≤ n → eval (n:K) p = 0) : vanishingCoeffs p := by
  cases p with
  | nil => trivial
  | cons a p =>
    have hbase := h k (Nat.le_refl _)
    have hquot : ∀ n : Nat, k+1 ≤ n → eval (n:K) (tailsAt (k:K) p) = 0 := by
      intro n hn
      have hx := h n (by omega)
      have hd := synthetic_division (k:K) (n:K) a p
      have prod : ((n:K)-(k:K))*eval (n:K) (tailsAt (k:K) p) = 0 := by grind
      rcases Field.of_mul_eq_zero prod with hEq | hz
      · have he : (n:K) = (k:K) := by grind
        have := hchar n k he
        omega
      · exact hz
    have htail := integer_tail hchar (tailsAt (k:K) p) (k+1) hquot
    have hp := recover_zero_coeffs (k:K) p htail
    refine ⟨?_, hp⟩
    have hz := eval_zero (k:K) p hp
    change a+(k:K)*eval (k:K) p = 0 at hbase
    grind
termination_by p.length
decreasing_by simp_all [tails_length]

/-- p_i(Y) are the coefficients of powers X^i. -/
def evalTwo (p : List (List K)) (x y : K) := eval x (p.map (eval y))

private theorem zero_rows (p : List (List K))
    (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j)
    (h : ∀ n : Nat, vanishingCoeffs (p.map (eval (n:K)))) :
    ∀ row ∈ p, vanishingCoeffs row := by
  induction p with
  | nil => simp
  | cons row rest ih =>
    have hrow (n : Nat) : eval (n:K) row = 0 := (h n).1
    have hrest (n : Nat) : vanishingCoeffs (rest.map (eval (n:K))) := (h n).2
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      apply integer_tail hchar row 0
      intro n _
      exact hrow n
    · exact ih hrest r hr

/-- Zariski density on the entire plane, as a coefficient assertion for every
    bivariate polynomial of arbitrary degree, over every characteristic-zero field. -/
theorem shifted_highest_weights_dense (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j)
    (p : List (List K))
    (h : ∀ m n : Nat, n ≤ m → evalTwo p ((m+1:Nat):K) (n:K) = 0) :
    ∀ row ∈ p, vanishingCoeffs row := by
  apply zero_rows p hchar
  intro n
  apply integer_tail hchar _ (n+1)
  intro i hi
  have hs : i-1+1 = i := by omega
  have hv := h (i-1) n (by omega)
  rw [hs] at hv
  exact hv

/-- Polynomial identities on the shifted dominant lattice hold throughout K². -/
theorem evalTwo_of_dense (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j)
    (p : List (List K))
    (h : ∀ m n : Nat, n ≤ m → evalTwo p ((m+1:Nat):K) (n:K) = 0)
    (x y : K) : evalTwo p x y = 0 := by
  have hh := shifted_highest_weights_dense hchar p h
  unfold evalTwo
  apply eval_zero x
  clear h
  induction p with
  | nil => trivial
  | cons row rest ih =>
    constructor
    · exact eval_zero y row (hh row List.mem_cons_self)
    · apply ih
      intro r hr
      exact hh r (List.mem_cons_of_mem _ hr)

end WeightDensity
#print axioms WeightDensity.integer_tail
#print axioms WeightDensity.shifted_highest_weights_dense
#print axioms WeightDensity.evalTwo_of_dense
