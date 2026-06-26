import Towers.ClassField.CohomologyOps.CocycleExtension

/-!
# Chapter II, Example 1.18(b): extensions and second cohomology

Milne treats extensions with an abelian kernel and a fixed induced action.
These are central extensions precisely in the special case where that action
is trivial.  This file states the classification using Mathlib's concrete
`GroupExtension` and ordinary degree-two group cohomology.
-/

namespace Towers.CField.COps

open groupCohomology

variable {G M E : Type} [Group G] [CommGroup M] [Group E]
  [MulDistribMulAction G M]

/-- An extension realizes the prescribed `G`-action on its abelian kernel
when conjugation by a lift of `g` acts as `g`. -/
def ExtensionRealizesAction (S : GroupExtension M E G) : Prop :=
  S.conjAct = (MulDistribMulAction.toMulAut G M).comp S.rightHom

/-- The central-extension specialization: the embedded kernel lies in the
center of the middle group. -/
def CGExt (S : GroupExtension M E G) : Prop :=
  S.inl.range ≤ Subgroup.center E

/-- An extension of `G` by `M`, bundled with the assertion that its induced
action on `M` is the fixed external action. -/
structure AEAct (G M : Type) [Group G] [CommGroup M]
    [MulDistribMulAction G M] where
  middle : Type
  [middleGroup : Group middle]
  extension : GroupExtension M middle G
  realizesAction : ExtensionRealizesAction extension

attribute [instance] AEAct.middleGroup

namespace AEAct

/-- Equivalence of extensions means an isomorphism of the middle groups
commuting with the kernel inclusions and quotient maps. -/
def Equivalent (S T : AEAct G M) : Prop :=
  Nonempty (S.extension.Equiv T.extension)

end AEAct

namespace CExt

/-- In the cocycle extension, moving a kernel element left across an element
applies the action of its quotient coordinate. -/
theorem mul_inl_smul
    (f : G × G → M) (hf : IsMulCocycle₂ f)
    (x : CExt f) (m : M) :
    letI := group f hf
    x * (toGroupExtension f hf).inl m =
      (toGroupExtension f hf).inl (x.2 • m) * x := by
  letI : Group (CExt f) := group f hf
  apply Prod.ext
  · change x.1 * (x.2 • (m * (f (1, 1))⁻¹)) * f (x.2, 1) =
      ((x.2 • m) * (f (1, 1))⁻¹) * (1 • x.1) * f (1, x.2)
    rw [map_one_snd_of_isMulCocycle₂ hf x.2,
      map_one_fst_of_isMulCocycle₂ hf x.2]
    simp only [smul_mul', smul_inv', one_smul]
    simp [mul_assoc]
    ac_rfl
  · change x.2 * 1 = 1 * x.2
    simp

/-- The conjugation action of the cocycle extension is its original
prescribed action on `M`. -/
theorem realizes_action_extension
    (f : G × G → M) (hf : IsMulCocycle₂ f) :
    letI := group f hf
    ExtensionRealizesAction (toGroupExtension f hf) := by
  letI : Group (CExt f) := group f hf
  let S := toGroupExtension f hf
  ext x m
  change S.conjAct x m = x.2 • m
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  apply mul_right_cancel (b := x)
  calc
    (x * S.inl m * x⁻¹) * x = x * S.inl m := by group
    _ = S.inl (x.2 • m) * x := mul_inl_smul f hf x m

/-- The abelian extension with prescribed action represented by a
multiplicative two-cocycle. -/
noncomputable def abelianExtensionAction
    (f : G × G → M) (hf : IsMulCocycle₂ f) :
    AEAct G M where
  middle := CExt f
  middleGroup := group f hf
  extension := toGroupExtension f hf
  realizesAction := realizes_action_extension f hf

/-- The standard section `g ↦ (1,g)` of the cocycle extension. -/
def standardSection (f : G × G → M) (hf : IsMulCocycle₂ f) :
    (abelianExtensionAction f hf).extension.Section where
  toFun := fun g ↦ (1, g)
  rightInverse_rightHom := fun _ ↦ rfl

end CExt

/-- The factor set attached to a section `s`, characterized by
`s(g) * s(h) = inl(factorSet(g,h)) * s(gh)`.  The element inside `invFun`
lies in the range of `inl` by exactness of the extension. -/
noncomputable def extensionFactorSet
    (S : GroupExtension M E G) (s : S.Section) : G × G → M :=
  fun p => Function.invFun S.inl
    (s p.1 * s p.2 * (s (p.1 * p.2))⁻¹)

omit [MulDistribMulAction G M] in
/-- The defining factor-set equation. -/
theorem extension_set_section
    (S : GroupExtension M E G) (s : S.Section) (g h : G) :
    S.inl (extensionFactorSet S s (g, h)) * s (g * h) = s g * s h := by
  have hmem := s.mul_mul_mul_inv_mem_range_inl g h
  have hinl : S.inl (extensionFactorSet S s (g, h)) =
      s g * s h * (s (g * h))⁻¹ := by
    exact Function.invFun_eq hmem
  rw [hinl]
  group

/-- The standard section of the twisted extension recovers the cocycle from
which it was constructed. -/
theorem extension_standard_section
    (f : G × G → M) (hf : IsMulCocycle₂ f) :
    extensionFactorSet
        (CExt.abelianExtensionAction f hf).extension
        (CExt.standardSection f hf) = f := by
  let S := (CExt.abelianExtensionAction f hf).extension
  let s := CExt.standardSection f hf
  funext p
  obtain ⟨g, h⟩ := p
  apply S.inl_injective
  apply mul_right_cancel (b := s (g * h))
  calc
    S.inl (extensionFactorSet S s (g, h)) * s (g * h) = s g * s h :=
      extension_set_section S s g h
    _ = S.inl (f (g, h)) * s (g * h) := by
      apply Prod.ext
      · change 1 * (g • 1) * f (g, h) =
          (f (g, h) * (f (1, 1))⁻¹) * (1 • 1) * f (1, g * h)
        rw [map_one_fst_of_isMulCocycle₂ hf (g * h)]
        simp
      · change g * h = 1 * (g * h)
        simp

/-- Moving a kernel element past a section applies the prescribed action. -/
theorem section_mul_inl
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s : S.Section) (g : G) (m : M) :
    s g * S.inl m = S.inl (g • m) * s g := by
  have haction : S.conjAct (s g) m = g • m := by
    have h := congrArg (fun a : E →* MulAut M => a (s g) m) hS
    simpa using h
  calc
    s g * S.inl m = (s g * S.inl m * (s g)⁻¹) * s g := by group
    _ = S.inl (S.conjAct (s g) m) * s g := by
      rw [S.inl_conjAct_comm]
    _ = S.inl (g • m) * s g := by rw [haction]

/-- An abelian-kernel extension realizing the fixed action is central exactly
when that action is trivial. -/
theorem extension_trivial_action
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S) :
    CGExt S ↔ ∀ (g : G) (m : M), g • m = m := by
  constructor
  · intro hcentral g m
    obtain ⟨e, rfl⟩ := S.rightHom_surjective g
    have hmem : S.inl m ∈ Subgroup.center E :=
      hcentral ⟨m, rfl⟩
    have hcomm : e * S.inl m = S.inl m * e :=
      Subgroup.mem_center_iff.mp hmem e
    have haction : S.conjAct e m = S.rightHom e • m := by
      have h := congrArg (fun a : E →* MulAut M => a e m) hS
      simpa using h
    rw [← haction]
    apply S.inl_injective
    rw [S.inl_conjAct_comm, hcomm]
    group
  · intro htrivial x hx
    obtain ⟨m, rfl⟩ := hx
    rw [Subgroup.mem_center_iff]
    intro e
    have haction : S.conjAct e m = S.rightHom e • m := by
      have h := congrArg (fun a : E →* MulAut M => a e m) hS
      simpa using h
    have hconj : S.conjAct e m = m := haction.trans (htrivial _ _)
    have hinl := S.inl_conjAct_comm (e := e) (n := m)
    rw [hconj] at hinl
    calc
      e * S.inl m = (e * S.inl m * e⁻¹) * e := by group
      _ = S.inl m * e := by rw [← hinl]

/-- Associativity in the middle group is exactly the factor-set cocycle
identity. -/
theorem extension_set_cocycle₂
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s : S.Section) : IsMulCocycle₂ (extensionFactorSet S s) := by
  intro g h j
  apply S.inl_injective
  simp only [map_mul]
  apply mul_right_cancel (b := s ((g * h) * j))
  calc
    (S.inl (extensionFactorSet S s (g * h, j)) *
        S.inl (extensionFactorSet S s (g, h))) * s ((g * h) * j) =
      S.inl (extensionFactorSet S s (g, h)) *
        (S.inl (extensionFactorSet S s (g * h, j)) * s ((g * h) * j)) := by
          have hcomm :
              S.inl (extensionFactorSet S s (g * h, j)) *
                  S.inl (extensionFactorSet S s (g, h)) =
                S.inl (extensionFactorSet S s (g, h)) *
                  S.inl (extensionFactorSet S s (g * h, j)) := by
            rw [← map_mul, ← map_mul, mul_comm]
          rw [hcomm, mul_assoc]
    _ = S.inl (extensionFactorSet S s (g, h)) * (s (g * h) * s j) := by
      rw [extension_set_section]
    _ = (s g * s h) * s j := by
      rw [← mul_assoc, extension_set_section]
    _ = s g * (s h * s j) := mul_assoc _ _ _
    _ = s g *
        (S.inl (extensionFactorSet S s (h, j)) * s (h * j)) := by
      rw [extension_set_section]
    _ = (S.inl (g • extensionFactorSet S s (h, j)) * s g) * s (h * j) := by
      rw [← mul_assoc, section_mul_inl S hS]
    _ = S.inl (g • extensionFactorSet S s (h, j)) *
        (s g * s (h * j)) := by rw [mul_assoc]
    _ = S.inl (g • extensionFactorSet S s (h, j)) *
        (S.inl (extensionFactorSet S s (g, h * j)) * s (g * (h * j))) := by
      rw [extension_set_section]
    _ = (S.inl (g • extensionFactorSet S s (h, j)) *
        S.inl (extensionFactorSet S s (g, h * j))) * s ((g * h) * j) := by
      rw [mul_assoc, mul_assoc]

omit [MulDistribMulAction G M] in
/-- The value of the factor set at `(1,1)` records the value of the section
at the identity. -/
theorem inl_set_section
    (S : GroupExtension M E G) (s : S.Section) :
    S.inl (extensionFactorSet S s (1, 1)) = s 1 := by
  apply mul_right_cancel (b := s 1)
  simpa using extension_set_section S s 1 1

/-- The twisted extension built from the factor set of a section is
equivalent to the original extension. -/
noncomputable def cocycleExtensionEquiv
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s : S.Section) :
    let f := extensionFactorSet S s
    let hf := extension_set_cocycle₂ S hS s
    (CExt.abelianExtensionAction f hf).extension.Equiv S := by
  let f := extensionFactorSet S s
  let hf := extension_set_cocycle₂ S hS s
  let T := CExt.abelianExtensionAction f hf
  let F : T.middle →* E :=
    { toFun := fun x ↦ S.inl x.1 * s x.2
      map_one' := by
        change S.inl ((f (1, 1))⁻¹) * s 1 = 1
        rw [map_inv, inl_set_section]
        simp
      map_mul' := fun x y ↦ by
        change S.inl (x.1 * (x.2 • y.1) * f (x.2, y.2)) *
              s (x.2 * y.2) =
            (S.inl x.1 * s x.2) * (S.inl y.1 * s y.2)
        calc
          S.inl (x.1 * (x.2 • y.1) * f (x.2, y.2)) *
                s (x.2 * y.2) =
              S.inl (x.1 * (x.2 • y.1)) *
                (S.inl (f (x.2, y.2)) * s (x.2 * y.2)) := by
                  simp only [map_mul]
                  ac_rfl
          _ = S.inl (x.1 * (x.2 • y.1)) * (s x.2 * s y.2) := by
            rw [extension_set_section]
          _ = S.inl x.1 *
              ((S.inl (x.2 • y.1) * s x.2) * s y.2) := by
            rw [map_mul]
            ac_rfl
          _ = S.inl x.1 * ((s x.2 * S.inl y.1) * s y.2) := by
            rw [section_mul_inl S hS s x.2 y.1]
          _ = (S.inl x.1 * s x.2) * (S.inl y.1 * s y.2) := by ac_rfl }
  refine GroupExtension.Equiv.ofMonoidHom F ?_ ?_
  · ext m
    change S.inl (m * (f (1, 1))⁻¹) * s 1 = S.inl m
    calc
      S.inl (m * (f (1, 1))⁻¹) * s 1 =
          S.inl (m * (f (1, 1))⁻¹) * S.inl (f (1, 1)) := by
        rw [inl_set_section S s]
      _ = S.inl ((m * (f (1, 1))⁻¹) * f (1, 1)) := by
        simp only [map_mul]
      _ = S.inl m := by simp
  · ext x
    change S.rightHom (S.inl x.1 * s x.2) = x.2
    simp

/-- Cohomologous multiplicative cocycles define equivalent twisted
extensions. -/
noncomputable def cocycleExtensionCoboundary₂
    (f g : G × G → M) (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g)
    (hfg : IsMulCoboundary₂ (fun p ↦ f p / g p)) :
    (CExt.abelianExtensionAction f hf).extension.Equiv
      (CExt.abelianExtensionAction g hg).extension := by
  let S := CExt.abelianExtensionAction f hf
  let T := CExt.abelianExtensionAction g hg
  let a : G → M := hfg.choose
  have ha : ∀ x y : G, x • a y / a (x * y) * a x = f (x, y) / g (x, y) :=
    hfg.choose_spec
  have ha_one : a 1 = f (1, 1) / g (1, 1) := by
    simpa using ha 1 1
  let F : S.middle →* T.middle :=
    { toFun := fun x ↦ (x.1 * a x.2, x.2)
      map_one' := by
        apply Prod.ext
        · change (f (1, 1))⁻¹ * a 1 = (g (1, 1))⁻¹
          rw [ha_one]
          simp [div_eq_mul_inv]
        · rfl
      map_mul' := fun x y ↦ by
        have hdiv : ((x.2 • a y.2) * a x.2) / a (x.2 * y.2) =
            f (x.2, y.2) / g (x.2, y.2) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            ha x.2 y.2
        have hfactor :
            f (x.2, y.2) * a (x.2 * y.2) =
              (x.2 • a y.2) * a x.2 * g (x.2, y.2) := by
          have := (div_eq_div_iff_mul_eq_mul.mp hdiv).symm
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        apply Prod.ext
        · change
            (x.1 * (x.2 • y.1) * f (x.2, y.2)) * a (x.2 * y.2) =
              (x.1 * a x.2) * (x.2 • (y.1 * a y.2)) * g (x.2, y.2)
          simp only [smul_mul']
          calc
            x.1 * (x.2 • y.1) * f (x.2, y.2) * a (x.2 * y.2) =
                x.1 * (x.2 • y.1) *
                  (f (x.2, y.2) * a (x.2 * y.2)) := by ac_rfl
            _ = x.1 * (x.2 • y.1) *
                  ((x.2 • a y.2) * a x.2 * g (x.2, y.2)) := by
                rw [hfactor]
            _ = x.1 * a x.2 * ((x.2 • y.1) * (x.2 • a y.2)) *
                  g (x.2, y.2) := by ac_rfl
        · rfl }
  refine GroupExtension.Equiv.ofMonoidHom F ?_ ?_
  · ext m
    apply Prod.ext
    · change (m * (f (1, 1))⁻¹) * a 1 =
        m * (g (1, 1))⁻¹
      rw [ha_one]
      simp [div_eq_mul_inv, mul_assoc]
    · rfl
  · rfl

/-- The kernel-valued cochain measuring the difference between two
set-theoretic sections. -/
noncomputable def extensionSectionChange
    (S : GroupExtension M E G) (s t : S.Section) : G → M :=
  fun g => Function.invFun S.inl (s g * (t g)⁻¹)

omit [MulDistribMulAction G M] in
/-- A section is obtained from another by multiplying by its change
cochain. -/
theorem extension_section_change
    (S : GroupExtension M E G) (s t : S.Section) (g : G) :
    S.inl (extensionSectionChange S s t g) * t g = s g := by
  have hmem := s.mul_inv_mem_range_inl t g
  have hinl : S.inl (extensionSectionChange S s t g) = s g * (t g)⁻¹ :=
    Function.invFun_eq hmem
  rw [hinl]
  group

/-- Factor sets from two sections differ by the coboundary of the section
change cochain. -/
theorem extension_sets_coboundary₂
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s t : S.Section) :
    IsMulCoboundary₂ (fun p =>
      extensionFactorSet S s p / extensionFactorSet S t p) := by
  let a := extensionSectionChange S s t
  refine ⟨a, ?_⟩
  intro g h
  have hu : a g * (g • a h) * extensionFactorSet S t (g, h) =
      extensionFactorSet S s (g, h) * a (g * h) := by
    apply S.inl_injective
    simp only [map_mul]
    apply mul_right_cancel (b := t (g * h))
    calc
      ((S.inl (a g) * S.inl (g • a h)) *
          S.inl (extensionFactorSet S t (g, h))) * t (g * h) =
        S.inl (a g) * S.inl (g • a h) * (t g * t h) := by
          rw [mul_assoc, extension_set_section]
      _ = S.inl (a g) * (S.inl (g • a h) * t g) * t h := by ac_rfl
      _ = S.inl (a g) * (t g * S.inl (a h)) * t h := by
        rw [section_mul_inl S hS]
      _ = (S.inl (a g) * t g) * (S.inl (a h) * t h) := by ac_rfl
      _ = s g * s h := by rw [extension_section_change, extension_section_change]
      _ = S.inl (extensionFactorSet S s (g, h)) * s (g * h) := by
        rw [extension_set_section]
      _ = S.inl (extensionFactorSet S s (g, h)) *
          (S.inl (a (g * h)) * t (g * h)) := by
        rw [extension_section_change]
      _ = (S.inl (extensionFactorSet S s (g, h)) *
          S.inl (a (g * h))) * t (g * h) := by rw [mul_assoc]
  have hdiv : (a g * (g • a h)) / a (g * h) =
      extensionFactorSet S s (g, h) / extensionFactorSet S t (g, h) :=
    div_eq_div_iff_mul_eq_mul.mpr hu
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- The ordinary degree-two cohomology class represented by the factor set
of a chosen section. -/
noncomputable def extensionClassSection
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s : S.Section) : H2 (Rep.ofMulDistribMulAction G M) :=
  H2π (Rep.ofMulDistribMulAction G M)
    (cocyclesOfIsMulCocycle₂ (extension_set_cocycle₂ S hS s))

/-- The cohomology class of an extension is independent of the chosen
section. -/
theorem extension_class_section
    (S : GroupExtension M E G) (hS : ExtensionRealizesAction S)
    (s t : S.Section) :
    extensionClassSection S hS s = extensionClassSection S hS t := by
  unfold extensionClassSection
  rw [H2π_eq_iff]
  change
    (Additive.ofMul ∘ extensionFactorSet S s) -
        (Additive.ofMul ∘ extensionFactorSet S t) ∈
      coboundaries₂ (Rep.ofMulDistribMulAction G M)
  have hboundary :=
    (coboundariesOfIsMulCoboundary₂
      (extension_sets_coboundary₂ S hS s t)).property
  convert hboundary using 1

omit [MulDistribMulAction G M] in
/-- Transporting a section across an equivalence of extensions does not
change its factor set. -/
theorem extension_set_comp
    {E' : Type} [Group E']
    (S : GroupExtension M E G) (T : GroupExtension M E' G)
    (e : S.Equiv T) (s : S.Section) :
    extensionFactorSet T (s.equivComp e) = extensionFactorSet S s := by
  funext p
  obtain ⟨g, h⟩ := p
  apply T.inl_injective
  apply mul_right_cancel (b := (s.equivComp e) (g * h))
  calc
    T.inl (extensionFactorSet T (s.equivComp e) (g, h)) *
          (s.equivComp e) (g * h) =
        (s.equivComp e) g * (s.equivComp e) h :=
      extension_set_section T (s.equivComp e) g h
    _ = e (s g) * e (s h) := rfl
    _ = e (s g * s h) := (map_mul e (s g) (s h)).symm
    _ = e (S.inl (extensionFactorSet S s (g, h)) * s (g * h)) := by
      rw [extension_set_section]
    _ = T.inl (extensionFactorSet S s (g, h)) * e (s (g * h)) := by
      rw [map_mul, e.map_inl]
    _ = T.inl (extensionFactorSet S s (g, h)) *
        (s.equivComp e) (g * h) := rfl

/-- Equivalent extensions, equipped with the same prescribed action, give
the same degree-two cohomology class. -/
theorem extension_section_comp
    {E' : Type} [Group E']
    (S : GroupExtension M E G) (T : GroupExtension M E' G)
    (hS : ExtensionRealizesAction S) (hT : ExtensionRealizesAction T)
    (e : S.Equiv T) (s : S.Section) :
    extensionClassSection S hS s =
      extensionClassSection T hT (s.equivComp e) := by
  unfold extensionClassSection
  apply congrArg (H2π (Rep.ofMulDistribMulAction G M))
  apply Subtype.ext
  funext p
  change Additive.ofMul (extensionFactorSet S s p) =
    Additive.ofMul (extensionFactorSet T (s.equivComp e) p)
  rw [extension_set_comp]

/-- The extension class obtained from Mathlib's fixed choice of a section. -/
noncomputable def AEAct.extensionClass
    (S : AEAct G M) :
    H2 (Rep.ofMulDistribMulAction G M) :=
  extensionClassSection S.extension S.realizesAction
    S.extension.surjInvRightHom

/-- The extension constructed from a cocycle has the cohomology class of
that cocycle. -/
theorem CExt.ext_classabelian_extaction
    (f : G × G → M) (hf : IsMulCocycle₂ f) :
    (CExt.abelianExtensionAction f hf).extensionClass =
      H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) := by
  let S := CExt.abelianExtensionAction f hf
  calc
    S.extensionClass = extensionClassSection S.extension S.realizesAction
        (CExt.standardSection f hf) :=
      extension_class_section S.extension S.realizesAction
        S.extension.surjInvRightHom (CExt.standardSection f hf)
    _ = H2π (Rep.ofMulDistribMulAction G M)
        (cocyclesOfIsMulCocycle₂ hf) := by
      unfold extensionClassSection
      apply congrArg (H2π (Rep.ofMulDistribMulAction G M))
      apply Subtype.ext
      funext p
      change Additive.ofMul
          (extensionFactorSet S.extension
            (CExt.standardSection f hf) p) =
        Additive.ofMul (f p)
      rw [extension_standard_section]

/-- Equivalence of extensions implies equality of their canonical
degree-two classes. -/
theorem AEAct.ext_class_eqequivalent
    (S T : AEAct G M) (h : S.Equivalent T) :
    S.extensionClass = T.extensionClass := by
  obtain ⟨e⟩ := h
  calc
    S.extensionClass = extensionClassSection T.extension T.realizesAction
        (S.extension.surjInvRightHom.equivComp e) :=
      extension_section_comp S.extension T.extension
        S.realizesAction T.realizesAction e S.extension.surjInvRightHom
    _ = T.extensionClass :=
      extension_class_section T.extension T.realizesAction
        (S.extension.surjInvRightHom.equivComp e)
        T.extension.surjInvRightHom

/-- Every degree-two cohomology class is represented by an extension
inducing the prescribed action. -/
theorem AEAct.extensionClass_surjective :
    Function.Surjective
      (AEAct.extensionClass (G := G) (M := M)) := by
  intro z
  induction z using H2_induction_on with
  | h x =>
      let f : G × G → M := Additive.toMul ∘ x
      have hf : IsMulCocycle₂ f :=
        isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := M) x x.property
      refine ⟨CExt.abelianExtensionAction f hf, ?_⟩
      rw [CExt.ext_classabelian_extaction]
      apply congrArg (H2π (Rep.ofMulDistribMulAction G M))
      apply Subtype.ext
      rfl

/-- Equality of extension classes produces an equivalence of extensions. -/
theorem AEAct.equivalent_ext_classeq
    (S T : AEAct G M)
    (hclass : S.extensionClass = T.extensionClass) : S.Equivalent T := by
  let s := S.extension.surjInvRightHom
  let t := T.extension.surjInvRightHom
  let f := extensionFactorSet S.extension s
  let g := extensionFactorSet T.extension t
  let hf := extension_set_cocycle₂ S.extension S.realizesAction s
  let hg := extension_set_cocycle₂ T.extension T.realizesAction t
  have hπ :
      H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) =
        H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hg) := by
    simpa [AEAct.extensionClass, extensionClassSection,
      s, t, f, g, hf, hg] using hclass
  have hboundary := (H2π_eq_iff
    (cocyclesOfIsMulCocycle₂ hf) (cocyclesOfIsMulCocycle₂ hg)).mp hπ
  let d : G × G → Additive M :=
    (Additive.ofMul ∘ f) - (Additive.ofMul ∘ g)
  have hd : d ∈ coboundaries₂ (Rep.ofMulDistribMulAction G M) := by
    simpa [d] using hboundary
  have hd_mul := isMulCoboundary₂_of_mem_coboundaries₂
    (G := G) (M := M) d hd
  have hfg : IsMulCoboundary₂ (fun p ↦ f p / g p) := by
    convert hd_mul using 1
  let eS := cocycleExtensionEquiv S.extension S.realizesAction s
  let efg := cocycleExtensionCoboundary₂ f g hf hg hfg
  let eT := cocycleExtensionEquiv T.extension T.realizesAction t
  exact ⟨eS.symm.trans (efg.trans eT)⟩

/-- **Example II.1.18(b), classification statement.** The factor-set class
is independent of the chosen section, every degree-two class occurs, and two
extensions have the same class exactly when they are equivalent extensions. -/
def AbelianExtensionsClassified : Prop :=
  Function.Surjective
      (AEAct.extensionClass (G := G) (M := M)) ∧
    (∀ (S T : AEAct G M),
      S.extensionClass = T.extensionClass ↔ S.Equivalent T) ∧
    ∀ (S : AEAct G M) (s : S.extension.Section),
      S.extensionClass =
        extensionClassSection S.extension S.realizesAction s

/-- **Example II.1.18(b).** Abelian-kernel extensions inducing a fixed
`G`-action are classified by ordinary degree-two group cohomology. -/
theorem abelianExtensionsClassified :
    AbelianExtensionsClassified (G := G) (M := M) := by
  refine ⟨AEAct.extensionClass_surjective, ?_, ?_⟩
  · intro S T
    constructor
    · exact AEAct.equivalent_ext_classeq S T
    · exact AEAct.ext_class_eqequivalent S T
  · intro S s
    exact extension_class_section S.extension S.realizesAction
      S.extension.surjInvRightHom s

end Towers.CField.COps
