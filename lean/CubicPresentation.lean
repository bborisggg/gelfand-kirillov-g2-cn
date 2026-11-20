import AngularJacobi

/-! Equivalence of the normalized cubic presentations, over every associative
ring with torsion-free multiplication by 2 and 3 on its additive group. -/
namespace CubicPresentation
open Lean.Grind AngularJacobi
variable {A : Type} [Ring A]

structure Generators (A : Type) where
  e : A
  f : A
  h : A
  v0 : A
  v1 : A
  v2 : A
  v3 : A

/-- The relations of sl₂ and its cubic module, in a divided-weight basis.
Only the two Cartan weights actually needed for the calculation are listed. -/
structure Action (g : Generators A) : Prop where
  ef : br g.e g.f = g.h
  eh : br g.e g.h = -(two g.e)
  fh : br g.f g.h = two g.f
  lower0 : br g.f g.v0 = three g.v1
  lower1 : br g.f g.v1 = two g.v2
  lower2 : br g.f g.v2 = g.v3
  lower3 : br g.f g.v3 = 0
  raise0 : br g.e g.v0 = 0
  raise1 : br g.e g.v1 = g.v0
  raise2 : br g.e g.v2 = two g.v1
  raise3 : br g.e g.v3 = three g.v2
  weight0 : br g.h g.v0 = three g.v0
  weight1 : br g.h g.v1 = g.v1

/-- The complete bracket table, written in the basis of the weight-four
summand and the invariant line. Its central parameter is free to vary. -/
structure FullRelations (g : Generators A) (c : A) : Prop where
  weight4 : br g.v0 g.v1 = g.e*g.e
  weight2 : two (br g.v0 g.v2) = -(g.h*g.e+g.e*g.h)
  weight0 : middle g.v0 g.v1 g.v2 g.v3 = g.h*g.h-g.f*g.e-g.e*g.f
  weightNeg2 : two (br g.v1 g.v3) = g.f*g.h+g.h*g.f
  weightNeg4 : br g.v2 g.v3 = g.f*g.f
  invariantLine : invariant g.v0 g.v1 g.v2 g.v3 = c + two (casimir g.e g.f g.h)
  central : br c g.e=0 ∧ br c g.f=0 ∧ br c g.h=0 ∧ br c g.v0=0 ∧
            br c g.v1=0 ∧ br c g.v2=0 ∧ br c g.v3=0

private theorem cancel2 (t : ∀ x : A, two x=0 → x=0) {x y : A} (h : two x=two y) :
    x=y := by
  apply AddCommGroup.sub_eq_zero_iff.mp
  apply t
  have h' : two (x-y) = two x - two y := by unfold two; grind
  rw [h', h]
  grind

private theorem cancel3 (t : ∀ x : A, three x=0 → x=0) {x y : A}
    (h : three x=three y) : x=y := by
  apply AddCommGroup.sub_eq_zero_iff.mp
  apply t
  have h' : three (x-y) = three x - three y := by unfold three; grind
  rw [h', h]
  grind

private theorem addR (x y z : A) : br x (y+z)=br x y+br x z := by unfold br; grind
private theorem subR (x y z : A) : br x (y-z)=br x y-br x z := by unfold br; grind
private theorem prodR (x y z : A) : br x (y*z)=br x y*z+y*br x z := by unfold br; grind
private theorem twoR (x y : A) : br x (two y)=two (br x y) := by unfold br two; grind
private theorem twoL (x y : A) : br (two x) y=two (br x y) := by unfold br two; grind
private theorem threeR (x y : A) : br x (three y)=three (br x y) := by unfold br three; grind
private theorem threeL (x y : A) : br (three x) y=three (br x y) := by unfold br three; grind
private theorem zeroR (x : A) : br x 0=0 := by unfold br; grind
private theorem same (x : A) : br x x=0 := by unfold br; grind

/-- A single highest-weight bracket is equivalent to the entire
quadratic bracket table together with a unique central generator. -/
theorem complete_table (g : Generators A) (a : Action g)
    (t2 : ∀ x : A, two x=0 → x=0) (t3 : ∀ x : A, three x=0 → x=0) :
    br g.v0 g.v1 = g.e*g.e ↔
      ∃ c : A, FullRelations g c ∧ ∀ d : A, FullRelations g d → d=c := by
  constructor
  · intro top
    have fe : br g.f g.e = -g.h := by
      have b : br g.f g.e = -br g.e g.f := by unfold br; grind
      rw [b, a.ef]
    obtain ⟨c02, sm⟩ := quadratic_relations g.e g.f g.h g.v0 g.v1 g.v2 g.v3
      fe a.fh a.lower0 a.lower1 a.lower2 top
    have sm' := cancel2 t2 sm
    have ds : br g.f (middle g.v0 g.v1 g.v2 g.v3)=six (br g.v1 g.v3) := by
      unfold middle
      rw [addR, threeR, jacobi g.f g.v0 g.v3, jacobi g.f g.v1 g.v2,
          a.lower0, a.lower1, a.lower2, a.lower3, zeroR, threeL, twoL, same]
      unfold six two three
      grind
    have dr : br g.f (g.h*g.h-g.f*g.e-g.e*g.f)=three (g.f*g.h+g.h*g.f) := by
      simp only [subR, prodR, same, fe, a.fh]
      unfold three two
      grind
    have c13 : two (br g.v1 g.v3) = g.f*g.h+g.h*g.f := by
      apply cancel3 t3
      have hh := congrArg (br g.f) sm'
      rw [ds, dr] at hh
      calc
        three (two (br g.v1 g.v3)) = six (br g.v1 g.v3) := by unfold six two three; grind
        _ = _ := hh
    have c23 : br g.v2 g.v3 = g.f*g.f := by
      apply cancel2 t2
      apply cancel2 t2
      have h' := congrArg (br g.f) c13
      rw [twoR, jacobi g.f g.v1 g.v3, a.lower1, a.lower3, twoL, zeroR,
          addR, prodR g.f g.f g.h, prodR g.f g.h g.f, same, a.fh] at h'
      unfold two at h' ⊢
      simpa only [Semiring.left_distrib, Semiring.right_distrib, Semiring.zero_mul,
        Semiring.mul_zero, AddCommMonoid.zero_add, AddCommMonoid.add_zero] using h'
    let c := invariant g.v0 g.v1 g.v2 g.v3 - two (casimir g.e g.f g.h)
    refine ⟨c, ⟨top, c02, sm', c13, c23, ?_, ?_⟩, ?_⟩
    · unfold c
      grind
    · exact central_on_generators g.e g.f g.h g.v0 g.v1 g.v2 g.v3 t2 t3
        a.ef a.eh a.fh a.lower0 a.lower1 a.lower2 a.lower3 a.raise0 a.raise1
        a.raise2 a.raise3 a.weight0 a.weight1 top
    · intro d hd
      unfold c
      rw [hd.invariantLine]
      grind
  · rintro ⟨_, h, _⟩
    exact h.weight4

#print axioms CubicPresentation.complete_table
end CubicPresentation
