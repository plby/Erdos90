import Submission.ClassField.NormCorrespondence.Statement

/-!
# Chapter I, Corollary 1.2: proof of the local norm correspondence

The finite-level norm-residue isomorphisms identify norm groups with kernels
of restriction.  The Galois correspondence then gives all five clauses of
Milne's corollary.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u

variable {K : Type u} [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

namespace FASubext

/-- The compositum of two finite abelian subextensions is again a finite
abelian subextension. -/
noncomputable def sup (L L' : FASubext K) :
    FASubext K := by
  let E := L.finiteIntermediateField ⊔
    L'.finiteIntermediateField
  letI : IsMulCommutative Gal(E/K) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) τ
    let c : LocalAbsoluteGalois K := σ' * τ' * (τ' * σ')⁻¹
    have hcL : c ∈ L.intermediateField.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L.intermediateField,
        MonoidHom.mem_ker]
      change (AlgEquiv.restrictNormalHom L.intermediateField) c = 1
      simp only [c, map_mul, map_inv]
      rw [mul_comm'
        ((AlgEquiv.restrictNormalHom L.intermediateField) σ')
        ((AlgEquiv.restrictNormalHom L.intermediateField) τ')]
      simp
    have hcL' : c ∈ L'.intermediateField.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L'.intermediateField,
        MonoidHom.mem_ker]
      change (AlgEquiv.restrictNormalHom L'.intermediateField) c = 1
      simp only [c, map_mul, map_inv]
      rw [mul_comm'
        ((AlgEquiv.restrictNormalHom L'.intermediateField) σ')
        ((AlgEquiv.restrictNormalHom L'.intermediateField) τ')]
      simp
    have hcE : c ∈ E.toIntermediateField.fixingSubgroup := by
      rw [show E.toIntermediateField =
        L.intermediateField ⊔ L'.intermediateField from rfl,
        IntermediateField.fixingSubgroup_sup]
      exact ⟨hcL, hcL'⟩
    have hcmap : (AlgEquiv.restrictNormalHom E.toIntermediateField) c = 1 := by
      rw [← MonoidHom.mem_ker,
        IntermediateField.restrictNormalHom_ker]
      exact hcE
    rw [← mul_inv_eq_one]
    simpa only [c, map_mul, map_inv] using hcmap
  exact { finiteIntermediateField := E }

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem sup_intermediateField (L L' : FASubext K) :
    (sup L L').intermediateField = L.intermediateField ⊔ L'.intermediateField :=
  rfl

/-- The intersection of two finite abelian subextensions is again a finite
abelian subextension. -/
noncomputable def inf (L L' : FASubext K) :
    FASubext K := by
  let E := L.finiteIntermediateField ⊓
    L'.finiteIntermediateField
  letI : IsMulCommutative Gal(E/K) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := SeparableClosure K) τ
    let c : LocalAbsoluteGalois K := σ' * τ' * (τ' * σ')⁻¹
    have hcL : c ∈ L.intermediateField.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L.intermediateField,
        MonoidHom.mem_ker]
      change (AlgEquiv.restrictNormalHom L.intermediateField) c = 1
      simp only [c, map_mul, map_inv]
      rw [mul_comm'
        ((AlgEquiv.restrictNormalHom L.intermediateField) σ')
        ((AlgEquiv.restrictNormalHom L.intermediateField) τ')]
      simp
    have hcE : c ∈ E.toIntermediateField.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone inf_le_left hcL
    have hcmap : (AlgEquiv.restrictNormalHom E.toIntermediateField) c = 1 := by
      rw [← MonoidHom.mem_ker,
        IntermediateField.restrictNormalHom_ker]
      exact hcE
    rw [← mul_inv_eq_one]
    simpa only [c, map_mul, map_inv] using hcmap
  exact { finiteIntermediateField := E }

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem inf_intermediateField (L L' : FASubext K) :
    (inf L L').intermediateField = L.intermediateField ⊓ L'.intermediateField :=
  rfl

end FASubext

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- At every finite level, the norm group is exactly the kernel of the
reciprocity homomorphism. -/
theorem norm_abelian_restriction
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L : FASubext K) (x : Kˣ) :
    x ∈ L.normGroup ↔ localAbelianRestriction L (phi x) = 1 := by
  obtain ⟨e, he⟩ := hphi L
  rw [← he]
  constructor
  · intro hx
    have hq : QuotientGroup.mk' L.normGroup x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    rw [hq, map_one]
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    exact e.injective (hx.trans (map_one e).symm)

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Restriction to a smaller finite abelian field preserves triviality. -/
theorem local_abelian_restriction
    {L L' : FASubext K}
    (hLL' : L.intermediateField ≤ L'.intermediateField)
    (q : AbsoluteAbelianGalois K)
    (hq : localAbelianRestriction L' q = 1) :
    localAbelianRestriction L q = 1 := by
  obtain ⟨σ, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)))) q
  change localAbelianRestriction L'
      (localAbelianizationMap K σ) = 1 at hq
  change localAbelianRestriction L
      (localAbelianizationMap K σ) = 1
  rw [abelian_restriction_quotient] at hq ⊢
  rw [← MonoidHom.mem_ker,
    IntermediateField.restrictNormalHom_ker] at hq ⊢
  exact IntermediateField.fixingSubgroup_antitone hLL' hq

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Restriction to a compositum is trivial exactly when both component
restrictions are trivial. -/
theorem abelian_restriction_sup
    (L L' : FASubext K)
    (q : AbsoluteAbelianGalois K) :
    localAbelianRestriction (L.sup L') q = 1 ↔
      localAbelianRestriction L q = 1 ∧
        localAbelianRestriction L' q = 1 := by
  obtain ⟨σ, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)))) q
  change localAbelianRestriction (L.sup L')
      (localAbelianizationMap K σ) = 1 ↔
    localAbelianRestriction L (localAbelianizationMap K σ) = 1 ∧
      localAbelianRestriction L' (localAbelianizationMap K σ) = 1
  rw [abelian_restriction_quotient,
    abelian_restriction_quotient,
    abelian_restriction_quotient]
  rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker,
    IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker]
  change σ ∈ (L.intermediateField ⊔ L'.intermediateField).fixingSubgroup ↔
    σ ∈ L.intermediateField.fixingSubgroup ∧
      σ ∈ L'.intermediateField.fixingSubgroup
  rw [IntermediateField.fixingSubgroup_sup]
  rfl

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The norm group of a compositum is the intersection of the two norm
groups. -/
theorem normGroup_sup
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L L' : FASubext K) :
    (L.sup L').normGroup = L.normGroup ⊓ L'.normGroup := by
  ext x
  rw [norm_abelian_restriction phi hphi,
    abelian_restriction_sup]
  change
    (localAbelianRestriction L) (phi x) = 1 ∧
      (localAbelianRestriction L') (phi x) = 1 ↔
      x ∈ L.normGroup ∧ x ∈ L'.normGroup
  rw [
    norm_abelian_restriction phi hphi,
    norm_abelian_restriction phi hphi]

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
private theorem finrank_norm_group
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    {L L' : FASubext K}
    (h : L.normGroup = L'.normGroup) :
    Module.finrank K L.finiteIntermediateField =
      Module.finrank K L'.finiteIntermediateField := by
  obtain ⟨e, _⟩ := hphi L
  obtain ⟨e', _⟩ := hphi L'
  calc
    Module.finrank K L.finiteIntermediateField =
        Nat.card Gal(L.finiteIntermediateField/K) :=
      (IsGalois.card_aut_eq_finrank K
        L.finiteIntermediateField).symm
    _ = Nat.card (Kˣ ⧸ L.normGroup) :=
      (Nat.card_congr e.toEquiv).symm
    _ = Nat.card (Kˣ ⧸ L'.normGroup) := by rw [h]
    _ = Nat.card Gal(L'.finiteIntermediateField/K) :=
      Nat.card_congr e'.toEquiv
    _ = Module.finrank K L'.finiteIntermediateField :=
      IsGalois.card_aut_eq_finrank K
        L'.finiteIntermediateField

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The finite-level norm correspondence reverses inclusions. -/
theorem intermediate_norm_group
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L L' : FASubext K) :
    L.intermediateField ≤ L'.intermediateField ↔
      L'.normGroup ≤ L.normGroup := by
  constructor
  · intro hLL' x hx
    rw [norm_abelian_restriction phi hphi] at hx ⊢
    exact local_abelian_restriction hLL' (phi x) hx
  · intro hnorm
    let M := L.sup L'
    have hMnorm : M.normGroup = L'.normGroup := by
      rw [show M.normGroup = L.normGroup ⊓ L'.normGroup from
        normGroup_sup phi hphi L L', inf_eq_right.mpr hnorm]
    have hfinrank :
        Module.finrank K L'.finiteIntermediateField =
          Module.finrank K M.finiteIntermediateField :=
      (finrank_norm_group phi hphi hMnorm).symm
    have hfield : L'.intermediateField = M.intermediateField :=
      IntermediateField.eq_of_le_of_finrank_eq le_sup_right hfinrank
    rw [hfield]
    exact le_sup_left

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
private theorem abelian_subextension_ext
    {L L' : FASubext K}
    (h : L.intermediateField = L'.intermediateField) : L = L' := by
  cases L with
  | mk L =>
      cases L' with
      | mk L' =>
          simp only [FASubext.intermediateField] at h
          have : L = L' :=
            FiniteGaloisIntermediateField.val_injective h
          subst L'
          rfl

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Part (a): finite abelian subextensions are recovered uniquely from
their norm groups. -/
theorem abelian_norm_bijective
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L) :
    Function.Bijective (abelianNormGroup K) := by
  constructor
  · intro L L' h
    have hnorm : L.normGroup = L'.normGroup :=
      congrArg Subtype.val h
    apply abelian_subextension_ext
    apply le_antisymm
    · exact (intermediate_norm_group phi hphi L L').2
        (le_of_eq hnorm.symm)
    · exact (intermediate_norm_group phi hphi L' L).2
        (le_of_eq hnorm)
  · rintro ⟨H, L, hL⟩
    refine ⟨L, Subtype.ext ?_⟩
    exact hL

/-- The finite reciprocity homomorphism before passage to its quotient by
the norm group. -/
noncomputable def finiteReciprocityHom
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) :
    Kˣ →* Gal(L.finiteIntermediateField/K) :=
  (localAbelianRestriction L).comp phi

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The kernel of finite reciprocity is the norm group. -/
theorem reciprocity_hom_ker
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L : FASubext K) :
    (finiteReciprocityHom phi L).ker = L.normGroup := by
  ext x
  exact (norm_abelian_restriction
    phi hphi L x).symm

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The fixing subgroup of a lifted intermediate field is detected by
restriction to the containing finite extension. -/
private theorem fixing_subgroup_lift
    (L : FASubext K)
    (E : IntermediateField K L.finiteIntermediateField)
    (σ : LocalAbsoluteGalois K) :
    σ ∈ (IntermediateField.lift E).fixingSubgroup ↔
      AlgEquiv.restrictNormalHom L.intermediateField σ ∈
        E.fixingSubgroup := by
  simp only [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    apply Subtype.ext
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      h x.1 ((IntermediateField.mem_lift x).2 hx)
  · intro h x hx
    have hxL : x ∈ L.intermediateField :=
      IntermediateField.lift_le E hx
    let y : L.finiteIntermediateField := ⟨x, hxL⟩
    have hyE : y ∈ E := (IntermediateField.mem_lift y).1 hx
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (h y hyE)

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Part (e): every subgroup containing a finite-level norm group is the
norm group of the fixed field of its reciprocity image. -/
theorem supergroup_subextension_group
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L : FASubext K) (I : Subgroup Kˣ)
    (hLI : L.normGroup ≤ I) :
    SubextensionNormGroup K I := by
  let f := finiteReciprocityHom phi L
  let J : Subgroup Gal(L.finiteIntermediateField/K) :=
    Subgroup.map f I
  letI : J.Normal := ⟨by
    intro n hn g
    simpa [mul_comm'] using hn⟩
  let E₀ : IntermediateField K L.finiteIntermediateField :=
    IntermediateField.fixedField J
  letI : IsAbelianGalois K L.finiteIntermediateField := {
    toIsGalois := inferInstance
    toIsMulCommutative := inferInstance
  }
  let Efield : IntermediateField K (SeparableClosure K) :=
    IntermediateField.lift E₀
  let e : E₀ ≃ₐ[K] Efield := IntermediateField.liftAlgEquiv E₀
  letI : Module.Finite K Efield := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K Efield := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField K (SeparableClosure K) := {
    Efield with
    finiteDimensional := inferInstance
    isGalois := inferInstance
  }
  let eAut : Gal(E₀/K) ≃* Gal(Efg/K) := e.autCongr
  letI : IsMulCommutative Gal(Efg/K) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using mul_comm' (eAut.symm σ) (eAut.symm τ)
  let E : FASubext K := {
    finiteIntermediateField := Efg
  }
  refine ⟨E, ?_⟩
  ext x
  rw [norm_abelian_restriction phi hphi]
  have hrestriction :
      localAbelianRestriction E (phi x) = 1 ↔
        finiteReciprocityHom phi L x ∈ J := by
    obtain ⟨σ, hσ⟩ := (QuotientGroup.mk'_surjective
      (Subgroup.topologicalClosure
        (commutator (LocalAbsoluteGalois K)))) (phi x)
    change localAbelianRestriction E (phi x) = 1 ↔
      localAbelianRestriction L (phi x) ∈ J
    rw [← hσ]
    change localAbelianRestriction E (localAbelianizationMap K σ) = 1 ↔
      localAbelianRestriction L (localAbelianizationMap K σ) ∈ J
    rw [abelian_restriction_quotient,
      abelian_restriction_quotient]
    change (AlgEquiv.restrictNormalHom E.intermediateField) σ = 1 ↔
      AlgEquiv.restrictNormalHom L.intermediateField σ ∈ J
    rw [← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker]
    change σ ∈ Efield.fixingSubgroup ↔ _
    rw [fixing_subgroup_lift L E₀ σ,
      IntermediateField.fixingSubgroup_fixedField]
  rw [hrestriction]
  change x ∈ Subgroup.comap f (Subgroup.map f I) ↔ x ∈ I
  rw [Subgroup.comap_map_eq_self]
  rw [reciprocity_hom_ker phi hphi L]
  exact hLI

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- Part (d): the norm group of an intersection is generated by the two
norm groups. -/
theorem normGroup_inf
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L L' : FASubext K) :
    (L.inf L').normGroup = L.normGroup ⊔ L'.normGroup := by
  let M := L.inf L'
  have hLM : L.normGroup ≤ M.normGroup :=
    (intermediate_norm_group phi hphi M L).1 inf_le_left
  have hL'M : L'.normGroup ≤ M.normGroup :=
    (intermediate_norm_group phi hphi M L').1 inf_le_right
  apply le_antisymm
  · obtain ⟨E, hE⟩ := supergroup_subextension_group
      phi hphi L (L.normGroup ⊔ L'.normGroup) le_sup_left
    have hEL : E.intermediateField ≤ L.intermediateField :=
      (intermediate_norm_group phi hphi E L).2
        (hE.symm ▸ le_sup_left)
    have hEL' : E.intermediateField ≤ L'.intermediateField :=
      (intermediate_norm_group phi hphi E L').2
        (hE.symm ▸ le_sup_right)
    have hEM : E.intermediateField ≤ M.intermediateField :=
      le_inf hEL hEL'
    have hnorm :=
      (intermediate_norm_group phi hphi E M).1 hEM
    simpa [hE] using hnorm
  · exact sup_le hLM hL'M

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The finite-level reciprocity isomorphisms imply all five clauses of the
local norm correspondence. -/
theorem local_correspondence_reciprocity
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L) :
    LocalNormCorrespondence K where
  normGroup_bijective := abelian_norm_bijective phi hphi
  inclusion_iff := intermediate_norm_group phi hphi
  norm_compositum L L' :=
    ⟨L.sup L', rfl, normGroup_sup phi hphi L L'⟩
  norm_intersection L L' :=
    ⟨L.inf L', rfl, normGroup_inf phi hphi L L'⟩
  supergroup_norm_group L I hLI :=
    supergroup_subextension_group phi hphi L I hLI

/-- The Local Recip Law supplies the local norm correspondence. -/
theorem norm_correspondence_reciprocity
    (hrec : LocalReciprocityLaw K) :
    LocalNormCorrespondence K := by
  obtain ⟨phi, hphi, _⟩ := hrec
  exact local_correspondence_reciprocity phi hphi.2

/-- **Corollary I.1.2.** A local reciprocity map induces the bijective,
order-reversing correspondence between finite abelian extensions and norm
groups, with the stated compositum, intersection, and supergroup formulas. -/
theorem localNormCorrespondence :
    (∃ φ : Kˣ →* AbsoluteAbelianGalois K,
      IsReciprocityMap K φ) →
    LocalNormCorrespondence K
  := by
  rintro ⟨phi, hphi⟩
  exact local_correspondence_reciprocity phi hphi.2

end

end Submission.CField.LFTheory
