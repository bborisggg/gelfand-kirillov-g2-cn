import CartanCoordinates
import WeightDensity

/-! The specialization step for the rank-two central characters. Values of
the two polynomial characters on the integral highest-weight grid determine
the generated field at every Cartan point, with arbitrary order and choices
of the angular roots. -/

namespace CartanComparison
open Lean.Grind CartanCoordinates WeightDensity
variable {K : Type} [Field K]
attribute [local instance] Semiring.natCast

private def minusRows : List K → List K → List K
  | [], q => q.map (fun z => -z)
  | p, [] => p
  | a::p, b::q => (a-b)::minusRows p q

private theorem eval_neg (x : K) (p : List K) :
    eval x (p.map (fun z => -z)) = -eval x p := by
  induction p with
  | nil => change (0:K) = -0; grind
  | cons a p ih => simp only [List.map_cons, eval, ih]; grind

private theorem eval_minus (x : K) (p q : List K) :
    eval x (minusRows p q) = eval x p - eval x q := by
  induction p generalizing q with
  | nil =>
    simp only [minusRows, eval_neg, eval]
    grind
  | cons a p ih =>
    cases q with
    | nil => simp only [minusRows, eval]; grind
    | cons b q => simp only [minusRows, eval, ih]; grind

private def minusPolys : List (List K) → List (List K) → List (List K)
  | [], q => q.map (fun row => row.map (fun z => -z))
  | p, [] => p
  | a::p, b::q => minusRows a b :: minusPolys p q

private theorem eval_cons (a : List K) (p : List (List K)) (x y : K) :
    evalTwo (a::p) x y = eval y a + x * evalTwo p x y := rfl

private theorem eval_neg_rows (x y : K) (p : List (List K)) :
    evalTwo (p.map (fun row => row.map (fun z => -z))) x y = -evalTwo p x y := by
  induction p with
  | nil => change (0:K) = -0; grind
  | cons a p ih => simp only [List.map_cons, eval_cons, eval_neg, ih]; grind

private theorem eval_minus_polys (x y : K) (p q : List (List K)) :
    evalTwo (minusPolys p q) x y = evalTwo p x y - evalTwo q x y := by
  induction p generalizing q with
  | nil =>
    simp only [minusPolys, eval_neg_rows]
    change -evalTwo q x y = 0 - evalTwo q x y
    grind
  | cons a p ih =>
    cases q with
    | nil =>
      change evalTwo (a::p) x y = evalTwo (a::p) x y - 0
      grind
    | cons b q =>
      simp only [minusPolys, eval_cons, eval_minus, ih]
      grind

private theorem equal_on_grid
    (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j)
    (p q : List (List K))
    (h : ∀ m n : Nat, n ≤ m →
      evalTwo p ((m+1:Nat):K) (n:K) = evalTwo q ((m+1:Nat):K) (n:K))
    (x y : K) : evalTwo p x y = evalTwo q x y := by
  have hg (m n : Nat) (hm : n ≤ m) : evalTwo (minusPolys p q) ((m+1:Nat):K) (n:K) = 0 := by
    rw [eval_minus_polys, h m n hm]
    grind
  have hw := evalTwo_of_dense hchar (minusPolys p q) hg x y
  rw [eval_minus_polys] at hw
  grind

private def sumNumerator : List (List K) := [[-1,0,1],[],[1]]
private def productNumerator : List (List K) := [[1,0,-2,0,1],[],[-2,0,-2],[],[1]]

private theorem eval_sum (x y : K) :
    evalTwo sumNumerator x y = x^2+y^2-1 := by
  simp only [sumNumerator, evalTwo, List.map_cons, List.map_nil, eval]
  grind

private theorem eval_product (x y : K) :
    evalTwo productNumerator x y = (x^2+y^2-1)^2-4*x^2*y^2 := by
  simp only [productNumerator, evalTwo, List.map_cons, List.map_nil, eval]
  grind

/-- A and B are the polynomial characters for twice the sum and sixteen
times the product of the angular Casimirs. Their values on the weight grid
alone determine the angular root field. No global formula for A or B is
assumed. The two hypotheses at (x,y) say which quadratic roots are taken. -/
theorem field_from_weight_grid
    (hchar : ∀ i j : Nat, (i:K) = (j:K) → i = j) (ht : (2:K) ≠ 0)
    (base : K → Prop) (A B : List (List K))
    (gridA : ∀ m n : Nat, n ≤ m →
      evalTwo A ((m+1:Nat):K) (n:K) = ((m+1:Nat):K)^2+(n:K)^2-1)
    (gridB : ∀ m n : Nat, n ≤ m →
      evalTwo B ((m+1:Nat):K) (n:K) =
      (((m+1:Nat):K)^2+(n:K)^2-1)^2-4*((m+1:Nat):K)^2*(n:K)^2)
    (x y a b : K)
    (sumAt : 2*(casimir a+casimir b) = evalTwo A x y)
    (productAt : 16*(casimir a*casimir b) = evalTwo B x y) :
    adjoinPair base a b = adjoinPair base x y := by
  have as' := equal_on_grid hchar A sumNumerator (fun m n hm => (gridA m n hm).trans
    (eval_sum _ _).symm) x y
  have bs' := equal_on_grid hchar B productNumerator (fun m n hm => (gridB m n hm).trans
    (eval_product _ _).symm) x y
  rw [eval_sum] at as'
  rw [eval_product] at bs'
  have invTwo : (2:K)*(2:K)⁻¹ = 1 := Field.mul_inv_cancel ht
  have rootsPlus : 2*rootPlus x y = x+y-1 := by
    calc
      _ = (x+y-1)*((2:K)*(2:K)⁻¹) := by unfold rootPlus; grind
      _ = _ := by rw [invTwo]; grind
  have rootsMinus : 2*rootMinus x y = x-y-1 := by
    calc
      _ = (x-y-1)*((2:K)*(2:K)⁻¹) := by unfold rootMinus; grind
      _ = _ := by rw [invTwo]; grind
  let u := rootPlus x y
  let v := rootMinus x y
  have fourU : 4*casimir u = (x+y)^2-1 := by
    calc
      _ = (2*u)*(2*u+2) := by unfold casimir; grind
      _ = _ := by dsimp [u]; rw [rootsPlus]; grind
  have fourV : 4*casimir v = (x-y)^2-1 := by
    calc
      _ = (2*v)*(2*v+2) := by unfold casimir; grind
      _ = _ := by dsimp [v]; rw [rootsMinus]; grind
  have cancel2 {j k : K} (eq2 : 2*j = 2*k) : j=k := by
    have mul0 : 2*(j-k)=0 := by grind
    rcases Field.of_mul_eq_zero mul0 with h | h
    · exact (ht h).elim
    · grind
  apply field_from_symmetric_characters ht
  · change casimir a + casimir b = casimir u+casimir v
    apply cancel2
    apply cancel2
    grind
  · change casimir a * casimir b = casimir u*casimir v
    apply cancel2
    apply cancel2
    apply cancel2
    apply cancel2
    have hprod : (4*casimir u)*(4*casimir v) = ((x+y)^2-1)*((x-y)^2-1) := by rw [fourU, fourV]
    grind

end CartanComparison
