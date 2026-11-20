import Std

/-! Rank-two Cartan coordinates. A generated subfield is described by the
intersection of all subfields containing the displayed scalars and generators.
No algebraic-independence assumption is needed for this equality. -/

namespace CartanCoordinates
open Lean.Grind
set_option maxHeartbeats 2000000

section Coordinates

variable {R : Type} [Field R]

/-- Closure properties for the underlying subset of a subfield. -/
structure SubfieldClosed (S : R → Prop) : Prop where
  one_mem : S 1
  add_mem : ∀ {u v}, S u → S v → S (u+v)
  sub_mem : ∀ {u v}, S u → S v → S (u-v)
  mul_mem : ∀ {u v}, S u → S v → S (u*v)
  inv_mem : ∀ {u}, S u → S u⁻¹

def adjoinPair (base : R → Prop) (u v z : R) : Prop :=
  ∀ (S : R → Prop), SubfieldClosed S → (∀ x, base x → S x) →
    S u → S v → S z

/-- The two ordered roots associated with the shifted weights. -/
def rootPlus (x y : R) : R := (x+y-1)*(2:R)⁻¹
def rootMinus (x y : R) : R := (x-y-1)*(2:R)⁻¹

private theorem double_half (ht : (2:R) ≠ 0) (x : R) :
    2*(x*(2:R)⁻¹) = x := by
  have h : (2:R)*(2:R)⁻¹ = 1 := Field.mul_inv_cancel ht
  calc
    2*(x*(2:R)⁻¹) = x*((2:R)*(2:R)⁻¹) := by grind
    _ = x := by rw [h]; grind

theorem recover_pair (ht : (2:R) ≠ 0) (x y : R) :
    rootPlus x y + rootMinus x y + 1 = x ∧
    rootPlus x y - rootMinus x y = y := by
  have h : (2:R)*(2:R)⁻¹ = 1 := Field.mul_inv_cancel ht
  constructor
  · calc
      _ = (x-1)*((2:R)*(2:R)⁻¹)+1 := by unfold rootPlus rootMinus; grind
      _ = x := by rw [h]; grind
  · calc
      _ = y*((2:R)*(2:R)⁻¹) := by unfold rootPlus rootMinus; grind
      _ = y := by rw [h]; grind

theorem ordered_root_fields (ht : (2:R) ≠ 0) (base : R → Prop) (x y : R) :
    adjoinPair base (rootPlus x y) (rootMinus x y) = adjoinPair base x y := by
  funext z
  apply propext
  constructor
  · intro hz S hs hbase hx hy
    have htwo : S (2:R) := by
      have h := hs.add_mem hs.one_mem hs.one_mem
      have he : (1:R)+1 = 2 := by grind
      rw [he] at h
      exact h
    exact hz S hs hbase
      (hs.mul_mem (hs.sub_mem (hs.add_mem hx hy) hs.one_mem) (hs.inv_mem htwo))
      (hs.mul_mem (hs.sub_mem (hs.sub_mem hx hy) hs.one_mem) (hs.inv_mem htwo))
  · intro hz S hs hbase hp hm
    obtain ⟨h₁,h₂⟩ := recover_pair ht x y
    exact hz S hs hbase (h₁ ▸ hs.add_mem (hs.add_mem hp hm) hs.one_mem)
      (h₂ ▸ hs.sub_mem hp hm)

private theorem other_root (u v : R) (h : u*(u+1) = v*(v+1)) :
    u = v ∨ u = -1-v := by
  have hprod : (u-v)*(u+v+1) = 0 := by grind
  rcases Field.of_mul_eq_zero hprod with hzero | hzero
  · left; grind
  · right; grind

private theorem same_generator {u v : R} (h : u*(u+1) = v*(v+1))
    (S : R → Prop) (hs : SubfieldClosed S) : S u ↔ S v := by
  rcases other_root u v h with he | he
  · rw [he]
  · have hn : S (-1:R) := by
      have e : ((1:R)-1)-1 = -1 := by grind
      exact e ▸ hs.sub_mem (hs.sub_mem hs.one_mem hs.one_mem) hs.one_mem
    constructor
    · intro hu
      have e : -1-u = v := by grind
      exact e ▸ hs.sub_mem hn hu
    · intro hv
      rw [he]
      exact hs.sub_mem hn hv

/-- The equality is independent of which of the two roots of each
    Casimir quadratic was selected. -/
theorem cartan_field_for_casimir_roots (ht : (2:R) ≠ 0)
    (base : R → Prop) (x y a b : R)
    (ha : a*(a+1) = rootPlus x y*(rootPlus x y+1))
    (hb : b*(b+1) = rootMinus x y*(rootMinus x y+1)) :
    adjoinPair base a b = adjoinPair base x y := by
  rw [← ordered_root_fields ht base x y]
  funext z
  apply propext
  constructor
  · intro hz S hs hbase hp hm
    exact hz S hs hbase ((same_generator ha S hs).mpr hp) ((same_generator hb S hs).mpr hm)
  · intro hz S hs hbase ha' hb'
    exact hz S hs hbase ((same_generator ha S hs).mp ha') ((same_generator hb S hs).mp hb')

private theorem adjoin_swap (base : R → Prop) (a b : R) :
    adjoinPair base a b = adjoinPair base b a := by
  funext z
  apply propext
  constructor
  · intro hz S hs hbase hb ha
    exact hz S hs hbase ha hb
  · intro hz S hs hbase ha hb
    exact hz S hs hbase hb ha

def casimir (l : R) : R := l*(l+1)

private theorem unordered_pair (a b c d : R)
    (hs : a+b=c+d) (hp : a*b=c*d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have mult := congrArg (fun t : R => a*t) hs
  have h : (a-c)*(a-d) = 0 := by grind
  rcases Field.of_mul_eq_zero h with he | he
  · left; constructor <;> grind
  · right; constructor <;> grind

/-- The symmetric central eigenvalues suffice: the two angular Casimirs
may be interchanged and each quadratic may be solved by either root. -/
theorem field_from_symmetric_characters (ht : (2:R) ≠ 0)
    (base : R → Prop) (x y a b : R)
    (hs : casimir a + casimir b =
      casimir (rootPlus x y) + casimir (rootMinus x y))
    (hp : casimir a * casimir b =
      casimir (rootPlus x y) * casimir (rootMinus x y)) :
    adjoinPair base a b = adjoinPair base x y := by
  rcases unordered_pair _ _ _ _ hs hp with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact cartan_field_for_casimir_roots ht base x y a b h₁ h₂
  · exact (adjoin_swap base a b).trans (cartan_field_for_casimir_roots ht base x y b a h₂ h₁)

/-- The two scalar Casimir eigenvalues at the weights (m+n,m-n). -/
theorem weight_casimirs (ht : (2:R) ≠ 0) (m n : R) :
    4*rootPlus (m+1) n*(rootPlus (m+1) n+1) = (m+n)*(m+n+2) ∧
    4*rootMinus (m+1) n*(rootMinus (m+1) n+1) = (m-n)*(m-n+2) := by
  have hp : 2*rootPlus (m+1) n = m+n := by
    unfold rootPlus
    rw [double_half ht]
    grind
  have hm : 2*rootMinus (m+1) n = m-n := by
    unfold rootMinus
    rw [double_half ht]
    grind
  constructor
  · calc
      _ = (2*rootPlus (m+1) n)*(2*rootPlus (m+1) n+2) := by grind
      _ = _ := by rw [hp]
  · calc
      _ = (2*rootMinus (m+1) n)*(2*rootMinus (m+1) n+2) := by grind
      _ = _ := by rw [hm]

private theorem cancel_double (ht : (2:R) ≠ 0) {s t : R} (he : 2*s=2*t) :
    s=t := by
  have hp : 2*(s-t)=0 := by grind
  rcases Field.of_mul_eq_zero hp with bad | ok
  · exact (ht bad).elim
  · grind

/-- The two symmetric angular Casimirs and the standard generators of
the signed-permutation invariants in two variables. -/
theorem symplectic_central_characters (ht : (2:R) ≠ 0) (x y : R) :
    let a := casimir (rootPlus x y)
    let b := casimir (rootMinus x y)
    2*(a+b)+1 = x^2+y^2 ∧ (a+b)^2-4*(a*b)=x^2*y^2 := by
  let a := casimir (rootPlus x y)
  let b := casimir (rootMinus x y)
  change 2*(a+b)+1 = x^2+y^2 ∧ (a+b)^2-4*(a*b)=x^2*y^2
  have ⟨hp,hm⟩ := weight_casimirs ht (x-1) y
  have hx : x-1+1=x := by grind
  rw [hx] at hp hm
  have ha : 4*a = (x+y)^2-1 := by unfold a casimir; grind
  have hb : 4*b = (x-y)^2-1 := by unfold b casimir; grind
  constructor
  · apply cancel_double ht; grind
  · have hd : a-b=x*y := by apply cancel_double ht; apply cancel_double ht; grind
    calc
      _ = (a-b)^2 := by grind
      _ = x^2*y^2 := by rw [hd]; grind

private theorem two_mem (S : R → Prop) (hs : SubfieldClosed S) : S (2:R) := by
  have he : (1:R)+1=2 := by grind
  exact he ▸ hs.add_mem hs.one_mem hs.one_mem

private theorem halve_mem (ht : (2:R) ≠ 0) (S : R → Prop) (hs : SubfieldClosed S)
    (v : R) (hv : S (2*v)) : S v := by
  have he : (2*v)*(2:R)⁻¹=v := by
    calc
      _ = 2*(v*(2:R)⁻¹) := by grind
      _ = _ := double_half ht v
  exact he ▸ hs.mul_mem hv (hs.inv_mem (two_mem S hs))

/-- The field generated by the symmetric angular eigenvalues is the field
generated by the elementary symmetric functions in x² and y². -/
theorem symmetric_central_fields (ht : (2:R) ≠ 0) (base : R → Prop) (x y : R) :
    let a := casimir (rootPlus x y)
    let b := casimir (rootMinus x y)
    adjoinPair base (a+b) (a*b) = adjoinPair base (x^2+y^2) (x^2*y^2) := by
  let a := casimir (rootPlus x y)
  let b := casimir (rootMinus x y)
  change adjoinPair base (a+b) (a*b) = adjoinPair base (x^2+y^2) (x^2*y^2)
  have h := symplectic_central_characters ht x y
  change 2*(a+b)+1=x^2+y^2 ∧ (a+b)^2-4*(a*b)=x^2*y^2 at h
  obtain ⟨h₁,h₂⟩ := h
  funext z
  apply propext
  constructor
  · intro hz S hs hbase hx hy
    have he₁ : (x^2+y^2)-1=2*(a+b) := by grind
    have hsum := halve_mem ht S hs (a+b) (he₁ ▸ hs.sub_mem hx hs.one_mem)
    have he₂ : (a+b)*(a+b) - x^2*y^2=2*(2*(a*b)) := by grind
    have hprod₂ := halve_mem ht S hs (2*(a*b)) (he₂ ▸ hs.sub_mem (hs.mul_mem hsum hsum) hy)
    exact hz S hs hbase hsum (halve_mem ht S hs (a*b) hprod₂)
  · intro hz S hs hbase hsum hprod
    have hx := h₁ ▸ hs.add_mem (hs.mul_mem (two_mem S hs) hsum) hs.one_mem
    have four : S (4:R) := by
      have he : (2:R)*2=4 := by grind
      exact he ▸ hs.mul_mem (two_mem S hs) (two_mem S hs)
    have he : (a+b)*(a+b)-4*(a*b)=x^2*y^2 := by grind
    exact hz S hs hbase hx (he ▸ hs.sub_mem (hs.mul_mem hsum hsum) (hs.mul_mem four hprod))

end Coordinates
end CartanCoordinates

