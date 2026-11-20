import Std

/-! The filtered comparison used for the two algebra presentations in section 5.
The components of the associated graded are expressed using representatives.
At degree zero the preceding filtration group is zero. -/

namespace FilteredComparison
open Lean.Grind

structure Filtration (A : Type) where
  part : Nat → A → Prop
  exhaustive : ∀ a, ∃ n, part n a

def lower {A : Type} [Zero A] (F : Filtration A) : Nat → A → Prop
  | 0, a => a = 0
  | n+1, a => F.part n a

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

/-- A filtered additive map whose associated graded is injective and
surjective in every degree is bijective. 'separates' and 'lifts' express
the kernel and image conditions on representatives modulo the preceding
filtration group. The assertion applies in particular to the underlying
additive map of a filtered algebra homomorphism. -/
theorem bijective_of_graded
    (F : Filtration A) (G : Filtration B) (f : A → B)
    (additive : ∀ x y, f (x + y) = f x + f y)
    (subtractive : ∀ x y, f (x - y) = f x - f y)
    (filtered : ∀ n x, F.part n x → G.part n (f x))
    (zero_in : ∀ n, F.part n 0)
    (separates : ∀ n x, F.part n x → lower G n (f x) → lower F n x)
    (lifts : ∀ n y, G.part n y → ∃ x, F.part n x ∧ lower G n (y - f x)) :
    (∀ x y, f x = f y → x = y) ∧ (∀ y, ∃ x, f x = y) := by
  have mapZero : f 0 = 0 := by
    have h := subtractive 0 0
    have za : (0 : A) - 0 = 0 := AddCommGroup.sub_eq_zero_iff.mpr rfl
    rw [za] at h
    exact h.trans (AddCommGroup.sub_eq_zero_iff.mpr rfl)
  have zeroLower (n : Nat) : lower G n 0 := by
    cases n with
    | zero => rfl
    | succ n =>
      change G.part n 0
      rw [← mapZero]
      exact filtered n 0 (zero_in n)
  have kernelLevel (n : Nat) : ∀ x, F.part n x → f x = 0 → x = 0 := by
    induction n with
    | zero =>
      intro x hx h
      exact separates 0 x hx (by rw [h]; exact zeroLower 0)
    | succ n ih =>
      intro x hx h
      exact ih x (separates (n+1) x hx (by rw [h]; exact zeroLower (n+1))) h
  constructor
  · intro x y e
    obtain ⟨n, hn⟩ := F.exhaustive (x-y)
    have ez : f (x-y) = 0 := by rw [subtractive]; exact AddCommGroup.sub_eq_zero_iff.mpr e
    have h := kernelLevel n (x-y) hn ez
    exact AddCommGroup.sub_eq_zero_iff.mp h
  · have imageLevel (n : Nat) : ∀ y, G.part n y → ∃ x, f x = y := by
      induction n with
      | zero =>
        intro y hy
        obtain ⟨x, _, h⟩ := lifts 0 y hy
        exact ⟨x, (AddCommGroup.sub_eq_zero_iff.mp h).symm⟩
      | succ n ih =>
        intro y hy
        obtain ⟨x, _, residual⟩ := lifts (n+1) y hy
        obtain ⟨u, hu⟩ := ih (y - f x) residual
        refine ⟨u+x, ?_⟩
        rw [additive, hu]
        exact AddCommGroup.sub_add_cancel
    intro y
    obtain ⟨n, hy⟩ := G.exhaustive y
    exact imageLevel n y hy

end FilteredComparison
