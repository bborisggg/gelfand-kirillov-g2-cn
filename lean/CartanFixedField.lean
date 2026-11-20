import CartanCoordinates

/-! The rational invariants of the signed permutations in rank two.  The
proof descends successively through the two sign changes and the swap.
It works in any ambient field admitting these automorphisms. -/
namespace CartanFixedField
open Lean.Grind CartanCoordinates
set_option maxHeartbeats 2000000
variable {R : Type} [Field R]

/-- Only the forward maps of the three automorphisms are used. -/
structure MapField (f : R → R) : Prop where
  one : f 1 = 1
  add : ∀ a b, f (a+b) = f a + f b
  sub : ∀ a b, f (a-b) = f a - f b
  mul : ∀ a b, f (a*b) = f a * f b
  inv : ∀ a, f a⁻¹ = (f a)⁻¹
  injective : ∀ a b, f a = f b → a=b

private theorem zero_mem (K : R → Prop) (hK : SubfieldClosed K) : K 0 := by
  have e : (1:R)-1=0 := by grind
  exact e ▸ hK.sub_mem hK.one_mem hK.one_mem

private theorem map_zero (f : R → R) (hf : MapField f) : f 0=0 := by
  have h := hf.sub 1 1
  have e : (1:R)-1=0 := by grind
  rw [e, hf.one] at h
  grind

private theorem adjoin_closed (base : R → Prop) (u v : R) :
    SubfieldClosed (adjoinPair base u v) where
  one_mem := fun _ hs _ _ _ => hs.one_mem
  add_mem := fun ha hb S hs h0 a b => hs.add_mem (ha S hs h0 a b) (hb S hs h0 a b)
  sub_mem := fun ha hb S hs h0 a b => hs.sub_mem (ha S hs h0 a b) (hb S hs h0 a b)
  mul_mem := fun ha hb S hs h0 a b => hs.mul_mem (ha S hs h0 a b) (hb S hs h0 a b)
  inv_mem := fun ha S hs h0 a b => hs.inv_mem (ha S hs h0 a b)

private theorem base_mem (base : R → Prop) (u v z : R) (h : base z) :
    adjoinPair base u v z := fun _ _ incl _ _ => incl z h
private theorem first_mem (base : R → Prop) (u v : R) :
    adjoinPair base u v u := fun _ _ _ hx _ => hx
private theorem second_mem (base : R → Prop) (u v : R) :
    adjoinPair base u v v := fun _ _ _ _ hy => hy

private theorem fixed_closed (f : R → R) (hf : MapField f) :
    SubfieldClosed (fun z => f z = z) where
  one_mem := hf.one
  add_mem := by intro a b ha hb; rw [hf.add, ha, hb]
  sub_mem := by intro a b ha hb; rw [hf.sub, ha, hb]
  mul_mem := by intro a b ha hb; rw [hf.mul, ha, hb]
  inv_mem := by intro a ha; rw [hf.inv, ha]

private def quad (K : R → Prop) (r z : R) :=
  ∃ a b, K a ∧ K b ∧ z=a+b*r

private theorem quad_algebra (K : R → Prop) (hK : SubfieldClosed K)
    (r : R) (hrr : K (r*r)) (f : R → R) (hf : MapField f)
    (hfix : ∀ a, K a → f a=a) (hsign : f r = -r) :
    SubfieldClosed (quad K r) where
  one_mem := ⟨1,0,hK.one_mem,zero_mem K hK,by grind⟩
  add_mem := by
    rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,d,hc,hd,rfl⟩
    exact ⟨a+c,b+d,hK.add_mem ha hc,hK.add_mem hb hd,by grind⟩
  sub_mem := by
    rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,d,hc,hd,rfl⟩
    exact ⟨a-c,b-d,hK.sub_mem ha hc,hK.sub_mem hb hd,by grind⟩
  mul_mem := by
    rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,d,hc,hd,rfl⟩
    exact ⟨a*c+(b*d)*(r*r),a*d+b*c,
      hK.add_mem (hK.mul_mem ha hc) (hK.mul_mem (hK.mul_mem hb hd) hrr),
      hK.add_mem (hK.mul_mem ha hd) (hK.mul_mem hb hc),by grind⟩
  inv_mem := by
    rintro z ⟨a,b,ha,hb,hz⟩
    by_cases he : z=0
    · exact ⟨0,0,zero_mem K hK,zero_mem K hK,by rw [he, Field.inv_zero]; grind⟩
    let N := a*a-(b*b)*(r*r)
    have hn : K N := hK.sub_mem (hK.mul_mem ha ha) (hK.mul_mem (hK.mul_mem hb hb) hrr)
    have hc : a-b*r ≠ 0 := by
      intro hc
      have hv : f z=0 := by rw [hz,hf.add,hf.mul,hfix a ha,hfix b hb,hsign]; grind
      exact he (hf.injective z 0 (hv.trans (map_zero f hf).symm))
    have mult : z*(a-b*r)=N := by rw [hz]; unfold N; grind
    have hn0 : N≠0 := by
      intro hn0
      rcases Field.of_mul_eq_zero (mult.trans hn0) with h | h
      · exact he h
      · exact hc h
    have hzInv : z*z⁻¹=1 := Field.mul_inv_cancel he
    have hnInv : N*N⁻¹=1 := Field.mul_inv_cancel hn0
    have hzM : z*((a-b*r)*N⁻¹)=1 := by
      calc
        _ = (z*(a-b*r))*N⁻¹ := by grind
        _ = 1 := by rw [mult,hnInv]
    have hzi : z⁻¹=(a-b*r)*N⁻¹ := by
      calc
        _ = z⁻¹*(z*((a-b*r)*N⁻¹)) := by rw [hzM]; grind
        _ = (z*z⁻¹)*((a-b*r)*N⁻¹) := by grind
        _ = _ := by rw [hzInv]; grind
    exact ⟨a*N⁻¹,(0-b)*N⁻¹,hK.mul_mem ha (hK.inv_mem hn),
      hK.mul_mem (hK.sub_mem (zero_mem K hK) hb) (hK.inv_mem hn),by rw [hzi]; grind⟩

private theorem quad_scalar (K : R → Prop) (hK : SubfieldClosed K) (r z : R)
    (hz : K z) : quad K r z :=
  ⟨z,0,hz,zero_mem K hK,by grind⟩

private theorem quad_gen (K : R → Prop) (hK : SubfieldClosed K) (r : R) :
    quad K r r := ⟨0,1,zero_mem K hK,hK.one_mem,by grind⟩

private theorem fixed_in_quad (ht : (2:R) ≠ 0) (K : R → Prop) (r z : R)
    (f : R → R) (hf : MapField f) (hfix : ∀ a, K a → f a = a)
    (hsign : f r = -r) (hq : quad K r z) (hz : f z=z) : K z := by
  obtain ⟨a,b,ha,hb,he⟩ := hq
  rw [he,hf.add,hf.mul,hfix a ha,hfix b hb,hsign] at hz
  have prod0 : (2:R)*(b*r)=0 := by grind
  rcases Field.of_mul_eq_zero prod0 with h | h
  · exact (ht h).elim
  · have za : z=a := by grind
    exact za.symm ▸ ha

/-- Fixing a sign while retaining a generator from its fixed field. -/
private theorem one_sign (ht : (2:R) ≠ 0) (base : R → Prop) (x y z : R)
    (f : R → R) (hf : MapField f) (hb : ∀ a, base a → f a=a)
    (hx : f x = -x) (hy : f y=y) (hz : f z=z) :
    adjoinPair base x y z → adjoinPair base (x*x) y z := by
  let K := adjoinPair base (x*x) y
  have hK := adjoin_closed base (x*x) y
  have hrr : K (x*x) := first_mem _ _ _
  have hfix (a) (ha : K a) : f a=a :=
    ha (fun t => f t=t) (fixed_closed f hf) hb (by change f _ = _; rw [hf.mul,hx]; grind) hy
  intro hfull
  apply fixed_in_quad ht K x z f hf hfix hx _ hz
  exact hfull _ (quad_algebra K hK x hrr f hf hfix hx)
    (fun t h => quad_scalar K hK x t (base_mem _ _ _ t h))
    (quad_gen K hK x) (quad_scalar K hK x y (second_mem _ _ _))

private theorem switch {base : R → Prop} {x y z : R} (h : adjoinPair base x y z) :
    adjoinPair base y x z := fun S hs hb hy hx => h S hs hb hx hy


private theorem under_swap (ht : (2:R) ≠ 0) (base : R → Prop) (u v z : R)
    (f : R → R) (hf : MapField f) (hb : ∀ a, base a → f a=a)
    (hu : f u=v) (hv : f v=u) (hz : f z=z) :
    adjoinPair base u v z → adjoinPair base (u+v) (u*v) z := by
  let K := adjoinPair base (u+v) (u*v)
  let d := u-v
  have hK := adjoin_closed base (u+v) (u*v)
  have Hs : K (u+v) := first_mem _ _ _
  have Hp : K (u*v) := second_mem _ _ _
  have htwo : K (2:R) := by
    have he : (1:R)+1=2 := by grind
    exact he ▸ hK.add_mem hK.one_mem hK.one_mem
  have hfour : K (4:R) := by
    have he : (2:R)*2=4 := by grind
    exact he ▸ hK.mul_mem htwo htwo
  have hrr : K (d*d) := by
    have he : (u+v)*(u+v)-4*(u*v)=d*d := by unfold d; grind
    exact he ▸ hK.sub_mem (hK.mul_mem Hs Hs) (hK.mul_mem hfour Hp)
  have hfix (a) (ha : K a) : f a=a :=
    ha (fun t => f t=t) (fixed_closed f hf) hb
      (by change f _ = _; rw [hf.add,hu,hv]; grind) (by change f _ = _; rw [hf.mul,hu,hv]; grind)
  have hsign : f d = -d := by unfold d; rw [hf.sub,hu,hv]; grind
  let h := (2:R)⁻¹
  have hh : (2:R)*h=1 := Field.mul_inv_cancel ht
  have Hh : K h := hK.inv_mem htwo
  have Hu : quad K d u := by
    refine ⟨(u+v)*h,h,hK.mul_mem Hs Hh,Hh,?_⟩
    calc
      u = u*(2*h) := by rw [hh]; grind
      _ = _ := by unfold d; grind
  have Hv : quad K d v := by
    refine ⟨(u+v)*h,0-h,hK.mul_mem Hs Hh,hK.sub_mem (zero_mem K hK) Hh,?_⟩
    calc
      v = v*(2*h) := by rw [hh]; grind
      _ = _ := by unfold d; grind
  intro hfull
  apply fixed_in_quad ht K d z f hf hfix hsign _ hz
  exact hfull _ (quad_algebra K hK d hrr f hf hfix hsign)
    (fun t ht' => quad_scalar K hK d t (base_mem _ _ _ t ht')) Hu Hv

/-- If the three field maps realize the two independent changes of sign
and the transposition on the coordinates, their simultaneous fixed
subfield in k(x,y) is k(x²+y²,x²y²). The base is an arbitrary set of
scalars preserved pointwise by the maps. -/
theorem signed_permutation_fixed_field (ht : (2:R) ≠ 0)
    (base : R → Prop) (x y : R) (s₁ s₂ w : R → R)
    (h₁ : MapField s₁) (h₂ : MapField s₂) (hw : MapField w)
    (b₁ : ∀ a, base a → s₁ a=a) (b₂ : ∀ a, base a → s₂ a=a)
    (bw : ∀ a, base a → w a=a)
    (sx : s₁ x = -x) (sy : s₁ y=y) (tx : s₂ x=x) (ty : s₂ y = -y)
    (wx : w x=y) (wy : w y=x) :
    (fun z => adjoinPair base x y z ∧ s₁ z=z ∧ s₂ z=z ∧ w z=z) =
      adjoinPair base (x^2+y^2) (x^2*y^2) := by
  have xx : x^2=x*x := by grind
  have yy : y^2=y*y := by grind
  rw [xx,yy]
  funext z
  apply propext
  constructor
  · rintro ⟨hA,hf,hg,hk⟩
    have hB := one_sign ht base x y z s₁ h₁ b₁ sx sy hf hA
    have sxx : s₂ (x*x)=x*x := by rw [h₂.mul,tx]
    have hC := one_sign ht base y (x*x) z s₂ h₂ b₂ ty sxx hg (switch hB)
    exact under_swap ht base (x*x) (y*y) z w hw bw
      (by rw [hw.mul,wx]) (by rw [hw.mul,wy]) hk (switch hC)
  · intro hz
    have hK := adjoin_closed base x y
    have xa := first_mem base x y
    have ya := second_mem base x y
    have xxa := hK.mul_mem xa xa
    have yya := hK.mul_mem ya ya
    refine ⟨hz (adjoinPair base x y) hK (base_mem base x y)
      (hK.add_mem xxa yya) (hK.mul_mem xxa yya), ?_, ?_, ?_⟩
    · exact hz (fun a => s₁ a=a) (fixed_closed s₁ h₁) b₁
        (by change s₁ _ = _; rw [h₁.add,h₁.mul,h₁.mul,sx,sy]; grind)
        (by change s₁ _ = _; rw [h₁.mul,h₁.mul,h₁.mul,sx,sy]; grind)
    · exact hz (fun a => s₂ a=a) (fixed_closed s₂ h₂) b₂
        (by change s₂ _ = _; rw [h₂.add,h₂.mul,h₂.mul,tx,ty]; grind)
        (by change s₂ _ = _; rw [h₂.mul,h₂.mul,h₂.mul,tx,ty]; grind)
    · exact hz (fun a => w a=a) (fixed_closed w hw) bw
        (by change w _ = _; rw [hw.add,hw.mul,hw.mul,wx,wy]; grind)
        (by change w _ = _; rw [hw.mul,hw.mul,hw.mul,wx,wy]; grind)

end CartanFixedField
