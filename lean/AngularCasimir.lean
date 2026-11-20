import Std

/-! Antipode and matrix-coefficient identities for the normalized sl₂ Casimir.
The Lie group, its representations and the angular chart are not defined here. -/
namespace AngularCasimir
open Lean.Grind

variable {A : Type} [Ring A]

def casimir (e f t : A) : A := f*e+t*(t+1)

/-- Negative on the generators and reversed multiplication characterize the
relevant action of the enveloping antipode on this quadratic expression. -/
theorem antipode_fixes (e f t : A) (hbr : e*f-f*e=t+t)
    (S : A → A) (hadd : ∀ x y, S (x+y)=S x+S y)
    (hmul : ∀ x y, S (x*y)=S y*S x) (h1 : S 1=1)
    (he : S e = -e) (hf : S f = -f) (ht : S t = -t) :
    S (casimir e f t) = casimir e f t := by
  unfold casimir
  rw [hadd, hmul, hmul, hadd, he, hf, ht, h1]
  simp only [Semiring.left_distrib, Semiring.right_distrib, Ring.mul_neg,
             Ring.neg_mul, Semiring.mul_one, Semiring.one_mul]
  grind

private def comm (a b : A) := a*b-b*a
local macro "nc_expand" : tactic =>
  `(tactic| (simp only [comm, AddCommGroup.sub_eq_add_neg, Semiring.left_distrib,
      Semiring.right_distrib, Ring.mul_neg, Ring.neg_mul, Semiring.mul_assoc,
      Semiring.mul_one, Semiring.one_mul] <;> grind))
private theorem comm_mul (a b x : A) :
    comm (a*b) x = a*comm b x + comm a x *b := by nc_expand
private theorem comm_add (a b x : A) :
    comm (a+b) x = comm a x + comm b x := by nc_expand
private theorem comm_unit (x : A) : comm 1 x = 0 := by nc_expand
private theorem comm_self (x : A) : comm x x = 0 := by nc_expand
private theorem comm_flip (x y : A) : comm x y = - comm y x := by nc_expand

/-- Direct centrality calculation for the normalized Casimir on the
three generators of the sl₂ enveloping algebra, using only its relations. -/
theorem commutes_with_generators (e f t : A)
    (hef : e*f-f*e=t+t) (hte : t*e-e*t=e) (htf : t*f-f*t= -f) :
    casimir e f t * e = e * casimir e f t ∧ casimir e f t * f = f * casimir e f t ∧
    casimir e f t * t = t * casimir e f t := by
  change comm e f = t+t at hef
  change comm t e = e at hte
  change comm t f = -f at htf
  have hfe : comm f e = -(t+t) := by rw [comm_flip, hef]
  have het : comm e t = -e := by rw [comm_flip, hte]
  have hft : comm f t = f := by rw [comm_flip, htf]; grind
  have hc (x : A) : comm (casimir e f t) x =
      f*comm e x+comm f x*e+(t*(comm t x+comm 1 x)+comm t x*(t+1)) := by
    unfold casimir
    rw [comm_add, comm_mul, comm_mul, comm_add]
  have he := hc e
  rw [comm_self, hfe, hte, comm_unit] at he
  have hf := hc f
  rw [hef, comm_self, htf, comm_unit] at hf
  have ht := hc t
  rw [het, hft, comm_unit, comm_self] at ht
  simp only [comm, Semiring.left_distrib, Semiring.right_distrib,
              Ring.neg_mul, Ring.mul_neg, Semiring.mul_one] at he hf ht hte htf
  grind

/-- Evaluating either regular action on a matrix coefficient gives one
value: the Casimir may be passed across the group action in the product. -/
theorem coefficient_actions_agree {L : Type} (e f t g : A)
    (hbr : e*f-f*e=t+t) (S : A → A) (hadd : ∀ x y, S (x+y)=S x+S y)
    (hmul : ∀ x y, S (x*y)=S y*S x) (h1 : S 1=1)
    (he : S e = -e) (hf : S f = -f) (ht : S t = -t)
    (hcentral : casimir e f t * g = g * casimir e f t) (coefficient : A → L) :
    coefficient (S (casimir e f t)*g) = coefficient (g*casimir e f t) := by
  rw [antipode_fixes e f t hbr S hadd hmul h1 he hf ht, hcentral]

end AngularCasimir
#print axioms AngularCasimir.antipode_fixes
#print axioms AngularCasimir.coefficient_actions_agree
#print axioms AngularCasimir.commutes_with_generators
