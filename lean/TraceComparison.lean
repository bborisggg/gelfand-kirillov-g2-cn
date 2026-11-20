import MatrixSymbols
import OscillatorBracket

/-! Identification of the coordinate expressions in the oscillator bracket
with actual matrix traces. -/
namespace OscillatorBracket
open Lean.Grind Slot MatrixSymbols
variable {R : Type} [CommRing R]

def matrix (x : Slot → R) : Mat R :=
  ⟨x a, x b, x c, x d, x e, x f, x g, x h, -(x a + x e)⟩

theorem matrix_traceless (x : Slot → R) : tr (matrix x) = 0 := by
  simp only [matrix, tr]
  grind

theorem matrix_quadratic (x : Slot → R) :
    quadratic x = tr (square (matrix x)) := by
  simp only [quadratic, tr, square, mul, matrix]
  grind

theorem matrix_cubic (x : Slot → R) :
    eval x cubic = tr (mul (square (matrix x)) (matrix x)) := by
  simp only [cubic, eval, tr, square, mul, matrix]
  grind

/-- For T=tr(X³), the left side acts as [T,[-3Δ,T]] on any polynomial u. -/
theorem oscillator_bracket_traces (x : Slot → R) (u : Term R) :
    lap x (.mul cubic (.mul cubic u))
      - 2 * tr (mul (square (matrix x)) (matrix x)) * lap x (.mul cubic u)
      + (tr (mul (square (matrix x)) (matrix x)))^2 * lap x u =
      9 * (tr (square (matrix x)))^2 * eval x u := by
  simpa only [← matrix_quadratic, ← matrix_cubic] using oscillator_bracket x u

end OscillatorBracket
