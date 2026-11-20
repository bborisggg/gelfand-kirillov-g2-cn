import Std

/-! The traceless-matrix oscillator bracket on arbitrary polynomial test
expressions. Write the matrix in row order as (a,b,c; d,e,f; g,h,-a-e).
The operator L below is three times the trace-pairing Laplacian. We use
the integral identity [T,[-L,T]]=9 tr(X²)², with T=tr(X³). -/
namespace OscillatorBracket
open Lean.Grind
set_option maxHeartbeats 15000000
inductive Slot | a | b | c | d | e | f | g | h deriving DecidableEq
open Slot

inductive Term (R : Type)
  | lit (s : R) | var (i : Slot)
  | add (u v : Term R) | mul (u v : Term R) | neg (u : Term R)
local infixl:65 " +ₚ " => Term.add
local infixl:70 " *ₚ " => Term.mul
local prefix:75 "-ₚ" => Term.neg

variable {R : Type} [CommRing R]

def eval (x : Slot → R) : Term R → R
  | .lit s => s
  | .var i => x i
  | .add u v => eval x u + eval x v
  | .mul u v => eval x u * eval x v
  | .neg u => -eval x u

/-- Coordinate differentiation on the polynomial syntax. -/
def deriv (i : Slot) : Term R → Term R
  | .lit _ => .lit 0
  | .var j => .lit (if i = j then 1 else 0)
  | .add u v => deriv i u +ₚ deriv i v
  | .mul u v => (deriv i u *ₚ v) +ₚ (u *ₚ deriv i v)
  | .neg u => -ₚ deriv i u

def first (x : Slot → R) (u : Term R) (i : Slot) := eval x (deriv i u)
def second (x : Slot → R) (u : Term R) (i j : Slot) := eval x (deriv j (deriv i u))

/-- Three times the diagonal trace form on the dual has diagonal
block ((2,-1),(-1,2)); each transposed pair has off-diagonal entries 3. -/
def contract (B : Slot → Slot → R) : R :=
  2*B a a - B a e - B e a + 2*B e e +
    3*(B b d + B d b + B c g + B g c + B f h + B h f)

def lap (x : Slot → R) (u : Term R) := contract (second x u)

/-- Applying the two product rules cancels all derivatives of the test
polynomial and all second derivatives of the multiplier. -/
theorem double_product_rule (x : Slot → R) (t u : Term R) (i j : Slot) :
    second x (t *ₚ (t *ₚ u)) i j - 2 * eval x t * second x (t *ₚ u) i j
       + (eval x t)^2 * second x u i j = 2 * first x t i * first x t j * eval x u := by
  simp only [second, first, deriv, eval]
  grind

private theorem contract_combine (A B C : Slot → Slot → R) (s t : R) :
    contract A - s * contract B + t * contract C =
      contract (fun i j => A i j - s * B i j + t * C i j) := by
  simp only [contract]
  grind

theorem double_commutator (x : Slot → R) (t u : Term R) :
    lap x (t *ₚ (t *ₚ u)) - 2 * eval x t * lap x (t *ₚ u) + (eval x t)^2 * lap x u =
      contract (fun i j => 2 * first x t i * first x t j * eval x u) := by
  unfold lap
  rw [contract_combine]
  apply congrArg contract
  funext i j
  exact double_product_rule x t u i j

/-- Three times the determinant of a generic traceless matrix. -/
def cubic : Term R :=
  let v : Slot → Term R := Term.var
  Term.lit 3 *ₚ
    (-ₚ(v a *ₚ v e *ₚ (v a +ₚ v e)) +ₚ -ₚ(v a *ₚ v f *ₚ v h)
     +ₚ (v b *ₚ v d *ₚ (v a +ₚ v e)) +ₚ (v b *ₚ v f *ₚ v g)
     +ₚ (v c *ₚ v d *ₚ v h) +ₚ -ₚ(v c *ₚ v e *ₚ v g))

/-- Trace of the square of the matrix in the given coordinates. -/
def quadratic (x : Slot → R) : R :=
  (x a)^2+(x e)^2+(x a+x e)^2+2*(x b*x d+x c*x g+x f*x h)

private def detDerivative (x : Slot → R) : Slot → R
  | .a => -2*x a*x e-(x e)^2-x f*x h+x b*x d
  | .e => -(x a)^2-2*x a*x e+x b*x d-x c*x g
  | .b => x d*(x a+x e)+x f*x g
  | .c => x d*x h-x e*x g
  | .d => x b*(x a+x e)+x c*x h
  | .f => -x a*x h+x b*x g
  | .g => x b*x f-x c*x e
  | .h => -x a*x f+x c*x d

private theorem cubic_first (x : Slot → R) (i : Slot) :
    first x cubic i = 3 * detDerivative x i := by
  cases i <;> simp [first, cubic, deriv, eval, detDerivative] <;> grind

/-- Cleared differential-operator identity, evaluated on every polynomial
test expression at every point, with no assumptions on either. -/
theorem oscillator_bracket (x : Slot → R) (u : Term R) :
    lap x (cubic *ₚ (cubic *ₚ u)) - 2 * eval x cubic * lap x (cubic *ₚ u) +
      (eval x cubic)^2 * lap x u = 9 * (quadratic x)^2 * eval x u := by
  rw [double_commutator]
  simp only [contract, cubic_first, detDerivative, quadratic]
  grind

end OscillatorBracket
