import Std

/-! The alternating line in the exterior square of the cubic sl₂-module.
All operations below are in an arbitrary associative ring. The hypotheses
on E and F are the action on the four vectors, in divided-weight basis.
The identities are integral and require no characteristic assumptions. -/

namespace AngularJacobi
open Lean.Grind

variable {A : Type} [Ring A]
def br (x y : A) := x*y-y*x
def two (x : A) := x+x
def three (x : A) := x+x+x
def six (x : A) := two (three x)

def invariant (v0 v1 v2 v3 : A) := br v0 v3 - three (br v1 v2)
def middle (v0 v1 v2 v3 : A) := br v0 v3 + three (br v1 v2)

local macro "expand_nc" : tactic =>
  `(tactic| (simp only [br, two, three, six, invariant, middle,
        AddCommGroup.sub_eq_add_neg, Semiring.left_distrib, Semiring.right_distrib,
        Ring.mul_neg, Ring.neg_mul, Semiring.mul_assoc] <;> grind))

theorem jacobi (x y z : A) :
    br x (br y z) = br (br x y) z + br y (br x z) := by expand_nc
private theorem reverse (x y : A) : br x y = -br y x := by expand_nc
private theorem same (x : A) : br x x = 0 := by expand_nc
private theorem addR (x y z : A) : br x (y+z)=br x y+br x z := by expand_nc
private theorem subR (x y z : A) : br x (y-z)=br x y-br x z := by expand_nc
private theorem zeroL (x : A) : br 0 x = 0 := by unfold br; grind
private theorem zeroR (x : A) : br x 0 = 0 := by unfold br; grind
private theorem twoL (x y : A) : br (two x) y = two (br x y) := by expand_nc
private theorem twoR (x y : A) : br x (two y) = two (br x y) := by expand_nc
private theorem threeL (x y : A) : br (three x) y=three (br x y) := by expand_nc
private theorem threeR (x y : A) : br x (three y)=three (br x y) := by expand_nc

/-- Killing the highest weight vector gives both positive-weight relations. -/
theorem lowered (f v0 v1 v2 v3 : A)
    (h0 : br f v0 = three v1) (h1 : br f v1 = two v2) (h2 : br f v2 = v3) :
    br f (br v0 v1) = two (br v0 v2) ∧
    br f (br f (br v0 v1)) = two (middle v0 v1 v2 v3) := by
  have h : br f (br v0 v1) = two (br v0 v2) := by
    rw [jacobi, h0, h1, threeL, twoR, same]
    unfold three
    grind
  refine ⟨h, ?_⟩
  rw [h, twoR, jacobi, h0, h2, threeL]
  unfold middle two three
  grind

/-- The alternating line in ∧² Sym³ is invariant under the raising operator. -/
theorem raising_invariant (e v0 v1 v2 v3 : A)
    (h0 : br e v0 = 0) (h1 : br e v1 = v0)
    (h2 : br e v2 = two v1) (h3 : br e v3 = three v2) :
    br e (invariant v0 v1 v2 v3) = 0 := by
  unfold invariant
  rw [subR, threeR, jacobi e v0 v3, jacobi e v1 v2, h0, h1, h2, h3,
      zeroL, threeR, twoR, same]
  unfold three two
  grind

/-- The same line is invariant under the lowering operator. -/
theorem lowering_invariant (f v0 v1 v2 v3 : A)
    (h0 : br f v0 = three v1) (h1 : br f v1 = two v2)
    (h2 : br f v2 = v3) (h3 : br f v3 = 0) :
    br f (invariant v0 v1 v2 v3) = 0 := by
  unfold invariant
  rw [subR, threeR, jacobi f v0 v3, jacobi f v1 v2, h0, h1, h2, h3,
      threeL, zeroR, twoL, same]
  unfold three two
  grind

/-- In the normalized basis S=C03+3 C12 and I=C03−3 C12. Jacobi
expresses the commutator with I in terms of the three prescribed brackets. -/
theorem eliminate (v0 v1 v2 v3 : A) :
    br v0 (invariant v0 v1 v2 v3) =
      br v0 (middle v0 v1 v2 v3) - six (br v1 (br v0 v2)) +
                                    six (br v2 (br v0 v1)) := by
  unfold invariant middle
  rw [subR, addR, threeR, jacobi v0 v1 v2, reverse (br v0 v1) v2]
  unfold six two three
  grind

/-- The associative Leibniz rule used to evaluate the lowered quadratic. -/
private theorem prodR (x y z : A) : br x (y*z) = br x y*z+y*br x z := by expand_nc
private theorem negR (x y : A) : br x (-y) = -br x y := by expand_nc

/-- With [v₀,v₁]=e², lowering gives the two explicitly prescribed quadratics.
The factors 2 have been retained so the statement holds over every ring. -/
theorem quadratic_relations (e f h v0 v1 v2 v3 : A)
    (hfe : br f e = -h) (hfh : br f h = two f)
    (hf0 : br f v0 = three v1) (hf1 : br f v1 = two v2)
    (hf2 : br f v2 = v3) (top : br v0 v1 = e*e) :
    two (br v0 v2) = -(h*e+e*h) ∧
    two (middle v0 v1 v2 v3) = two (h*h-f*e-e*f) := by
  obtain ⟨u, w⟩ := lowered f v0 v1 v2 v3 hf0 hf1 hf2
  have step : br f (e*e) = -(h*e+e*h) := by rw [prodR, hfe]; grind
  constructor
  · rw [←u, top, step]
  · rw [←w, top, step, negR, addR, prodR f h e, prodR f e h, hfe, hfh]
    unfold two
    grind

/-- Quadratic Casimir correction on the highest-weight vector. In characteristic
zero this gives [v₀, I − 2Ω]=0; the displayed factor 2 keeps the identity integral. -/
theorem casimir_correction (e f h v0 v1 v2 v3 : A)
    (hfe : br f e = -h) (hfh : br f h = two f)
    (hf0 : br f v0 = three v1) (hf1 : br f v1 = two v2) (hf2 : br f v2 = v3)
    (he0 : br e v0 = 0) (he1 : br e v1 = v0) (he2 : br e v2 = two v1)
    (hh0 : br h v0 = three v0) (hh1 : br h v1 = v1)
    (top : br v0 v1 = e*e) :
    two (br v0 (invariant v0 v1 v2 v3 - two (h*h+two (e*f+f*e)))) = 0 := by
  obtain ⟨q, s⟩ := quadratic_relations e f h v0 v1 v2 v3 hfe hfh hf0 hf1 hf2 top
  have q' : two (br v1 (br v0 v2)) = br v1 (-(h*e+e*h)) := by
    simpa only [twoR] using congrArg (br v1) q
  have s' : two (br v0 (middle v0 v1 v2 v3)) = two (br v0 (h*h-f*e-e*f)) := by
    simpa only [twoR] using congrArg (br v0) s
  have t' : br v2 (br v0 v1) = br v2 (e*e) := congrArg (br v2) top
  let om := h*h+two (e*f+f*e)
  change two (br v0 (invariant v0 v1 v2 v3 - two om)) = 0
  have regroup :
      two (br v0 (invariant v0 v1 v2 v3 - two om)) =
      two (br v0 (middle v0 v1 v2 v3)) - six (two (br v1 (br v0 v2))) +
      six (two (br v2 (br v0 v1))) - two (two (br v0 om)) := by
    rw [subR, twoR, eliminate]
    unfold six three two
    grind
  rw [regroup, q', s', t']
  dsimp only [om]
  simp only [negR, subR, addR, twoR, prodR]
  rw [reverse v0 h, reverse v0 f, reverse v0 e, reverse v1 h, reverse v1 e,
      reverse v2 e, hf0, he0, he1, he2, hh0, hh1]
  unfold six three two
  grind

/-- Centralizing two generators implies centralizing their bracket, so the
Casimir correction can be propagated through the lowering string. -/
theorem commutes_bracket (z x y : A) (hx : br z x = 0) (hy : br z y = 0) :
    br z (br x y) = 0 := by
  rw [jacobi, hx, hy, zeroL, zeroR]
  grind

/-- The standard quadratic Casimir of the sl₂-triple. -/
def casimir (e f h : A) := h*h + two (e*f+f*e)

theorem sl2_casimir (e f h : A)
    (hef : br e f = h) (heh : br e h = -(two e)) (hfh : br f h = two f) :
    br e (casimir e f h) = 0 ∧ br f (casimir e f h) = 0 := by
  have hfe : br f e = -h := by rw [reverse f e, hef]
  constructor <;>
    simp only [casimir, addR, twoR, prodR, same, hef, heh, hfh, hfe] <;>
    unfold two <;> grind

/-- After normalizing C₀₁=e², I−2Ω centralizes all seven algebra generators.
The hypotheses are exactly the indicated sl₂ and Sym³ actions and absence
of additive 2- and 3-torsion. No PBW or centrality hypothesis is used. -/
theorem central_on_generators (e f h v0 v1 v2 v3 : A)
    (torsion2 : ∀ x : A, two x = 0 → x = 0)
    (torsion3 : ∀ x : A, three x = 0 → x = 0)
    (hef : br e f = h) (heh : br e h = -(two e)) (hfh : br f h = two f)
    (hf0 : br f v0 = three v1) (hf1 : br f v1 = two v2)
    (hf2 : br f v2 = v3) (hf3 : br f v3 = 0)
    (he0 : br e v0 = 0) (he1 : br e v1 = v0)
    (he2 : br e v2 = two v1) (he3 : br e v3 = three v2)
    (hh0 : br h v0 = three v0) (hh1 : br h v1 = v1)
    (top : br v0 v1 = e*e) :
    let z := invariant v0 v1 v2 v3 - two (casimir e f h)
    br z e=0 ∧ br z f=0 ∧ br z h=0 ∧ br z v0=0 ∧ br z v1=0 ∧
      br z v2=0 ∧ br z v3=0 := by
  let z := invariant v0 v1 v2 v3 - two (casimir e f h)
  have hfe : br f e = -h := by rw [reverse f e, hef]
  obtain ⟨ce, cf⟩ := sl2_casimir e f h hef heh hfh
  have ze : br z e = 0 := by
    rw [reverse z e]
    dsimp only [z]
    rw [subR, twoR, ce, raising_invariant e v0 v1 v2 v3 he0 he1 he2 he3]
    unfold two
    grind
  have zf : br z f = 0 := by
    rw [reverse z f]
    dsimp only [z]
    rw [subR, twoR, cf, lowering_invariant f v0 v1 v2 v3 hf0 hf1 hf2 hf3]
    unfold two
    grind
  have zh : br z h = 0 := by
    rw [←hef]
    exact commutes_bracket z e f ze zf
  have h0 : br v0 z = 0 :=
    torsion2 _ (casimir_correction e f h v0 v1 v2 v3 hfe hfh
      hf0 hf1 hf2 he0 he1 he2 hh0 hh1 top)
  have z0 : br z v0 = 0 := by rw [reverse z v0, h0]; grind
  have a1 := commutes_bracket z f v0 zf z0
  rw [hf0, threeR] at a1
  have z1 := torsion3 _ a1
  have a2 := commutes_bracket z f v1 zf z1
  rw [hf1, twoR] at a2
  have z2 := torsion2 _ a2
  have z3 : br z v3 = 0 := by
    rw [←hf2]
    exact commutes_bracket z f v2 zf z2
  exact ⟨ze, zf, zh, z0, z1, z2, z3⟩

#print axioms AngularJacobi.sl2_casimir
#print axioms AngularJacobi.central_on_generators
#print axioms AngularJacobi.quadratic_relations
#print axioms AngularJacobi.casimir_correction
#print axioms AngularJacobi.commutes_bracket
#print axioms AngularJacobi.jacobi
#print axioms AngularJacobi.lowered
#print axioms AngularJacobi.raising_invariant
#print axioms AngularJacobi.lowering_invariant
#print axioms AngularJacobi.eliminate
end AngularJacobi
