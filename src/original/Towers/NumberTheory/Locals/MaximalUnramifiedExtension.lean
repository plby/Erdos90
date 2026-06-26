import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.FieldTheory.PrimitiveElement
import Towers.NumberTheory.Integers.IntegralClosureLattice
import Towers.NumberTheory.Locals.ClosureRootsUnity
import Towers.NumberTheory.Locals.UnramifiedExtensions


/-!
# Maximal unramified subalgebras and residue algebraic closures

This file specializes the residue-field correspondence of
`UnramifiedResidueLift` to Milne's Corollaries 7.51 and 7.52.

For a finite separable ambient residue extension, lifting the top
intermediate field gives the greatest finite formally unramified subalgebra.
For an algebraically closed ambient field, the residue field of its local
integral closure is an algebraic closure of the residue field of the base.
The locality hypothesis on the integral closure records the choice of the
extension of the base valuation to the algebraic closure.
-/

namespace Towers.NumberTheory.Milne

open IsLocalRing Polynomial

noncomputable section

attribute [local instance] Ideal.Quotient.field

section InfiniteMaximalUnramified

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [FaithfulSMul A B]

/-- A finite formally unramified subalgebra of an ambient algebra. -/
def FUSubalg (U : Subalgebra A B) : Prop :=
  Module.Finite A U ∧ Algebra.FormallyUnramified A U

omit [FaithfulSMul A B] in
/-- Formal unramifiedness descends from a finite unramified local stage to
a finite Dedekind local substage. -/
theorem FUSubalg.formally_unram_le
    [IsDomain B] (U V : Subalgebra A B) (hUV : U ≤ V)
    [Module.Finite A U] [IsLocalRing U] [IsLocalRing V]
    [IsDedekindDomain U]
    (hV : FUSubalg A B V) :
    Algebra.FormallyUnramified A U := by
  letI : Module.Finite A V := hV.1
  letI : Algebra.FormallyUnramified A V := hV.2
  letI : Algebra U V :=
    (Subalgebra.inclusion hUV).toRingHom.toAlgebra
  letI : IsScalarTower A U V :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul U V :=
    (faithfulSMul_iff_algebraMap_injective U V).mpr
      (Subalgebra.inclusion_injective hUV)
  letI : Module.IsTorsionFree U V := by
    constructor
    intro r hr
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro v hv
    rw [Algebra.smul_def] at hv
    exact (mul_eq_zero.mp hv).resolve_left <| by
      intro hr0
      apply hr.ne_zero
      apply FaithfulSMul.algebraMap_injective U V
      simpa using hr0
  letI : Algebra.IsIntegral A V := Algebra.IsIntegral.of_finite A V
  letI : Algebra.IsIntegral U V := Algebra.IsIntegral.tower_top A
  letI : IsLocalHom (algebraMap U V) :=
    Algebra.IsIntegral.isLocalHom U V
  letI : Algebra.EssFiniteType A U := inferInstance
  letI : Algebra.EssFiniteType A V := inferInstance
  letI : Algebra.IsUnramifiedAt A (maximalIdeal V) := inferInstance
  letI : (maximalIdeal V).LiesOver (maximalIdeal U) := inferInstance
  letI : Algebra.IsUnramifiedAt A (maximalIdeal U) :=
    Algebra.IsUnramifiedAt.of_liesOver
      A (maximalIdeal U) (maximalIdeal V)
  have hunit :
      (maximalIdeal U).primeCompl ≤ IsUnit.submonoid U := by
    intro x hx
    change IsUnit x
    have hx' : x ∉ maximalIdeal U := hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx'
    exact Classical.not_not.mp hx'
  let eU : U ≃ₐ[U] Localization.AtPrime (maximalIdeal U) :=
    IsLocalization.atUnits U (maximalIdeal U).primeCompl hunit
  let eA : U ≃ₐ[A] Localization.AtPrime (maximalIdeal U) :=
    eU.restrictScalars A
  exact Algebra.FormallyUnramified.of_equiv eA.symm

theorem formally_subalgebra_bot :
    FUSubalg A B ⊥ := by
  letI : Algebra.FormallyUnramified A A := inferInstance
  exact ⟨Subalgebra.finite_bot,
    Algebra.FormallyUnramified.of_equiv
      (Algebra.botEquivOfInjective
        (FaithfulSMul.algebraMap_injective A B)).symm⟩

omit [FaithfulSMul A B] in
/-- Finite formally unramified subalgebras are stable under compositum. -/
theorem FUSubalg.sup
    {U V : Subalgebra A B}
    (hU : FUSubalg A B U)
    (hV : FUSubalg A B V) :
    FUSubalg A B (U ⊔ V) := by
  letI : Module.Finite A U := hU.1
  letI : Module.Finite A V := hV.1
  letI : Algebra.FormallyUnramified A U := hU.2
  letI : Algebra.FormallyUnramified A V := hV.2
  exact ⟨Subalgebra.finite_sup U V, formally_sup_subalgebra U V⟩

omit [FaithfulSMul A B] in
/-- The finite unramified stages form a directed family under inclusion. -/
theorem formally_subalgebra_directed :
    Directed (· ≤ ·)
      (fun U : {U : Subalgebra A B //
          FUSubalg A B U} ↦ U.1) := by
  intro U V
  let W : Subalgebra A B := U.1 ⊔ V.1
  have hW : FUSubalg A B W :=
    U.property.sup A B V.property
  exact ⟨⟨W, hW⟩, le_sup_left, le_sup_right⟩

/-- Milne, Corollary 7.51, for a possibly infinite ambient algebra: the
union of all finite formally unramified subalgebras. -/
noncomputable def maximalFormallySubalgebra : Subalgebra A B :=
  ⨆ U : {U : Subalgebra A B //
    FUSubalg A B U}, U.1

omit [FaithfulSMul A B] in
/-- Every finite formally unramified stage is contained in the maximal
unramified union. -/
theorem maximal_subalgebra
    (U : Subalgebra A B)
    (hU : FUSubalg A B U) :
    U ≤ maximalFormallySubalgebra A B :=
  le_iSup
    (fun V : {V : Subalgebra A B //
      FUSubalg A B V} ↦ V.1)
    ⟨U, hU⟩

/-- Elementwise description of the maximal unramified union. -/
theorem formally_subalgebra (x : B) :
    x ∈ maximalFormallySubalgebra A B ↔
      ∃ U : Subalgebra A B,
        FUSubalg A B U ∧ x ∈ U := by
  let I := {U : Subalgebra A B //
    FUSubalg A B U}
  let K : I → Subalgebra A B := fun U ↦ U.1
  haveI : Nonempty I :=
    ⟨⟨⊥, formally_subalgebra_bot A B⟩⟩
  have hdir : Directed (· ≤ ·) K :=
    formally_subalgebra_directed A B
  change x ∈ ⨆ U : I, K U ↔ _
  have hcoe : ((⨆ U : I, K U : Subalgebra A B) : Set B) =
      ⋃ U : I, (K U : Set B) :=
    Subalgebra.coe_iSup_of_directed hdir
  constructor
  · intro hx
    have hx' : x ∈ ((⨆ U : I, K U : Subalgebra A B) : Set B) := hx
    rw [hcoe] at hx'
    obtain ⟨U, hxU⟩ := Set.mem_iUnion.mp hx'
    exact ⟨U.1, U.property, hxU⟩
  · rintro ⟨U, hU, hxU⟩
    have hx' : x ∈ ⋃ V : I, (K V : Set B) :=
      Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    have hx'' : x ∈ ((⨆ V : I, K V : Subalgebra A B) : Set B) := by
      rw [hcoe]
      exact hx'
    exact hx''

/-- A finitely generated subalgebra lies in the maximal unramified union
exactly when it is contained in one finite formally unramified stage. -/
theorem fg_formally_subalgebra
    (U : Subalgebra A B) (hUfg : U.FG) :
    U ≤ maximalFormallySubalgebra A B ↔
      ∃ V : Subalgebra A B,
        FUSubalg A B V ∧ U ≤ V := by
  constructor
  · intro hU
    obtain ⟨t, htfinite, ht⟩ := Subalgebra.fg_def.mp hUfg
    let s : Finset B := htfinite.toFinset
    classical
    have finite_stages : ∀ u : Finset B,
        (∀ x ∈ u, x ∈ maximalFormallySubalgebra A B) →
        ∃ V : Subalgebra A B,
          FUSubalg A B V ∧
            ∀ x ∈ u, x ∈ V := by
      intro u hu
      induction u using Finset.induction_on with
      | empty =>
          exact ⟨⊥, formally_subalgebra_bot A B, by simp⟩
      | @insert x u hxu ih =>
          obtain ⟨V, hV, hxV⟩ :=
            (formally_subalgebra A B x).mp
              (hu x (Finset.mem_insert_self x u))
          obtain ⟨W, hW, huW⟩ := ih fun y hy ↦
            hu y (Finset.mem_insert_of_mem hy)
          refine ⟨V ⊔ W, hV.sup A B hW, ?_⟩
          intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact (show V ≤ V ⊔ W from le_sup_left) hxV
          · exact (show W ≤ V ⊔ W from le_sup_right) (huW y hy)
    have hsmax : ∀ x ∈ s,
        x ∈ maximalFormallySubalgebra A B := by
      intro x hx
      apply hU
      rw [← ht]
      exact Algebra.subset_adjoin (by simpa [s] using hx)
    obtain ⟨V, hV, hsV⟩ := finite_stages s hsmax
    refine ⟨V, hV, ?_⟩
    rw [← ht]
    apply Algebra.adjoin_le
    intro x hx
    exact hsV x (by simpa [s] using hx)
  · rintro ⟨V, hV, hUV⟩
    exact hUV.trans (maximal_subalgebra A B V hV)

/-- Module-finite version of the finite-stage characterization. -/
theorem maximal_unramified_subalgebra
    (U : Subalgebra A B) [Module.Finite A U] :
    U ≤ maximalFormallySubalgebra A B ↔
      ∃ V : Subalgebra A B,
        FUSubalg A B V ∧ U ≤ V :=
  fg_formally_subalgebra A B U
    ((Subalgebra.fg_iff_finiteType U).mpr inferInstance)

/-- The directed union of the finite formally unramified stages remains
formally unramified. -/
theorem maximal_formally_unramified :
    Algebra.FormallyUnramified A
      (maximalFormallySubalgebra A B) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro C _ _ I hI f g hfg
  ext x
  obtain ⟨U, hU, hxU⟩ :=
    (formally_subalgebra A B x).mp x.property
  letI : Algebra.FormallyUnramified A U := hU.2
  let inclusion : U →ₐ[A] maximalFormallySubalgebra A B :=
    Subalgebra.inclusion
      (maximal_subalgebra A B U hU)
  have hrestricted :
      (Ideal.Quotient.mkₐ A I).comp (f.comp inclusion) =
        (Ideal.Quotient.mkₐ A I).comp (g.comp inclusion) := by
    simpa [AlgHom.comp_assoc] using
      congrArg (fun q ↦ q.comp inclusion) hfg
  have heq : f.comp inclusion = g.comp inclusion :=
    Algebra.FormallyUnramified.comp_injective I hI hrestricted
  exact AlgHom.congr_fun heq ⟨x, hxU⟩

end InfiniteMaximalUnramified

section InfiniteMaximalUnramifiedField

variable (A B K L : Type*)
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L]
  [Algebra A B] [FaithfulSMul A B]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]

/-- The intermediate field of the ambient fraction field generated by an
`A`-subalgebra of `B`.  When `K` and `L` are the fraction fields of `A` and
`B`, this is the fraction field of the subalgebra, embedded in `L`. -/
noncomputable def fractionFieldSubalgebra
    (U : Subalgebra A B) : IntermediateField K L :=
  IntermediateField.adjoin K
    ((algebraMap B L) '' (U : Set B))

/-- The canonical algebra structure from an integral stage to its generated
intermediate fraction field. -/
@[reducible] noncomputable def fractionIntermediateSubalgebra
    (U : Subalgebra A B) :
    Algebra U (fractionFieldSubalgebra A B K L U) :=
  ((algebraMap B L).comp U.val).codRestrict
    (fractionFieldSubalgebra A B K L U).toSubalgebra
      (fun (u : U) ↦ IntermediateField.subset_adjoin K
        ((algebraMap B L) '' (U : Set B))
          ⟨(u : B), u.property, rfl⟩) |>.toAlgebra

/-- The field generated by a subalgebra inside the ambient fraction field
is a fraction field of that subalgebra. -/
theorem fraction_intermediate_subalgebra
    (U : Subalgebra A B) :
    letI := fractionIntermediateSubalgebra A B K L U
    IsFractionRing U (fractionFieldSubalgebra A B K L U) := by
  let F := fractionFieldSubalgebra A B K L U
  letI : Algebra U F :=
    fractionIntermediateSubalgebra A B K L U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : FaithfulSMul U F :=
    (faithfulSMul_iff_algebraMap_injective U F).mpr <| by
      change Function.Injective (fun u : U ↦
        (⟨algebraMap B L (u : B), IntermediateField.subset_adjoin K
          ((algebraMap B L) '' (U : Set B))
            ⟨(u : B), u.property, rfl⟩⟩ : F))
      intro x y hxy
      apply Subtype.ext
      apply IsFractionRing.injective B L
      exact congrArg Subtype.val hxy
  apply IsFractionRing.of_field
  intro z
  have hrat : ∀ r : L,
      r ∈ Algebra.adjoin K ((algebraMap B L) '' (U : Set B)) →
        ∃ a b : U, b ≠ 0 ∧
          r = algebraMap B L (a : B) / algebraMap B L (b : B) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        obtain ⟨u, hu, rfl⟩ := hr
        exact ⟨⟨u, hu⟩, 1, one_ne_zero, by simp⟩
    | algebraMap k =>
        obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A k
        refine ⟨algebraMap A U a, algebraMap A U b, ?_, ?_⟩
        · intro h
          exact nonZeroDivisors.ne_zero hb <|
            FaithfulSMul.algebraMap_injective A U (by simpa using h)
        · calc
            algebraMap K L k = algebraMap K L
                (algebraMap A K a / algebraMap A K b) :=
              congrArg (algebraMap K L) hab.symm
            _ = algebraMap K L (algebraMap A K a) /
                algebraMap K L (algebraMap A K b) :=
              map_div₀ (algebraMap K L) _ _
            _ = algebraMap A L a / algebraMap A L b := by
              rw [IsScalarTower.algebraMap_apply A K L,
                IsScalarTower.algebraMap_apply A K L]
            _ = algebraMap B L (algebraMap A B a) /
                algebraMap B L (algebraMap A B b) := by
              rw [IsScalarTower.algebraMap_apply A B L,
                IsScalarTower.algebraMap_apply A B L]
            _ = algebraMap B L ((algebraMap A U a : U) : B) /
                algebraMap B L ((algebraMap A U b : U) : B) := rfl
    | add x y _ _ hx hy =>
        obtain ⟨a, b, hb, rfl⟩ := hx
        obtain ⟨c, d, hd, rfl⟩ := hy
        refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_⟩
        have hbL : algebraMap B L (b : B) ≠ 0 := by
          intro h; apply hb; apply Subtype.ext
          apply IsFractionRing.injective B L
          simpa using h
        have hdL : algebraMap B L (d : B) ≠ 0 := by
          intro h; apply hd; apply Subtype.ext
          apply IsFractionRing.injective B L
          simpa using h
        rw [show ((a * d + c * b : U) : B) =
            (a : B) * (d : B) + (c : B) * (b : B) from rfl,
          show ((b * d : U) : B) = (b : B) * (d : B) from rfl,
          map_add, map_mul, map_mul, map_mul]
        field_simp [hbL, hdL]
    | mul x y _ _ hx hy =>
        obtain ⟨a, b, hb, rfl⟩ := hx
        obtain ⟨c, d, hd, rfl⟩ := hy
        refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_⟩
        have hbL : algebraMap B L (b : B) ≠ 0 := by
          intro h; apply hb; apply Subtype.ext
          apply IsFractionRing.injective B L
          simpa using h
        have hdL : algebraMap B L (d : B) ≠ 0 := by
          intro h; apply hd; apply Subtype.ext
          apply IsFractionRing.injective B L
          simpa using h
        rw [show ((a * c : U) : B) = (a : B) * (c : B) from rfl,
          show ((b * d : U) : B) = (b : B) * (d : B) from rfl,
          map_mul, map_mul]
        field_simp [hbL, hdL]
  obtain ⟨r, hr, s, hs, hz⟩ :=
    IntermediateField.mem_adjoin_iff_div.mp z.property
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ?_⟩
    apply Subtype.ext
    simp [hz, hs0]
  obtain ⟨a, b, hb, hra⟩ := hrat r hr
  obtain ⟨c, d, hd, hsc⟩ := hrat s hs
  have hc : c ≠ 0 := by
    intro hc
    apply hs0
    rw [hsc, hc]
    simp
  refine ⟨a * d, b * c, ?_⟩
  apply Subtype.ext
  have hbL : algebraMap B L (b : B) ≠ 0 := by
    intro h; apply hb; apply Subtype.ext
    apply IsFractionRing.injective B L
    simpa using h
  have hcL : algebraMap B L (c : B) ≠ 0 := by
    intro h; apply hc; apply Subtype.ext
    apply IsFractionRing.injective B L
    simpa using h
  have hdL : algebraMap B L (d : B) ≠ 0 := by
    intro h; apply hd; apply Subtype.ext
    apply IsFractionRing.injective B L
    simpa using h
  have hL : (z : L) = algebraMap B L ((a * d : U) : B) /
      algebraMap B L ((b * c : U) : B) := by
    rw [hz, hra, hsc]
    rw [show ((a * d : U) : B) = (a : B) * (d : B) from rfl,
      show ((b * c : U) : B) = (b : B) * (c : B) from rfl,
      map_mul, map_mul]
    field_simp [hbL, hcL, hdL]
  change (z : L) = algebraMap B L ((a * d : U) : B) /
    algebraMap B L ((b * c : U) : B)
  exact hL

omit [IsDomain A] [IsDomain B] [FaithfulSMul A B] [Algebra A K] [IsFractionRing A K]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] in
/-- Passing from a subalgebra to its generated intermediate fraction field
is monotone. -/
theorem fraction_subalgebra_mono :
    Monotone (fractionFieldSubalgebra A B K L) := by
  intro U V hUV
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨u, hu, rfl⟩
  exact IntermediateField.subset_adjoin K
    ((algebraMap B L) '' (V : Set B)) ⟨u, hUV hu, rfl⟩

/-- Corollary 7.51 at field level: the intermediate field generated by the
union of all finite formally unramified valuation subalgebras. -/
noncomputable def maximalFormallyIntermediate :
    IntermediateField K L :=
  fractionFieldSubalgebra A B K L
    (maximalFormallySubalgebra A B)

omit [IsDomain A] [IsDomain B] [FaithfulSMul A B] [Algebra A K] [IsFractionRing A K]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] in
/-- Every finite formally unramified stage has its fraction field contained
in the maximal unramified intermediate field. -/
theorem fraction_formally_unramified
    (U : Subalgebra A B)
    (hU : FUSubalg A B U) :
    fractionFieldSubalgebra A B K L U ≤
      maximalFormallyIntermediate A B K L :=
  fraction_subalgebra_mono A B K L
    (maximal_subalgebra A B U hU)

omit [IsDomain A] [IsDomain B] [Algebra A K] [IsFractionRing A K]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
  [IsScalarTower A K L] in
/-- The maximal field is the supremum of the fraction fields of its finite
formally unramified stages. -/
theorem formally_i_sup :
    maximalFormallyIntermediate A B K L =
      ⨆ U : {U : Subalgebra A B //
        FUSubalg A B U},
        fractionFieldSubalgebra A B K L U.1 := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨U, hU, hbU⟩ :=
      (formally_subalgebra A B b).mp hb
    apply le_iSup
      (fun V : {V : Subalgebra A B //
        FUSubalg A B V} ↦
          fractionFieldSubalgebra A B K L V.1)
      ⟨U, hU⟩
    exact IntermediateField.subset_adjoin K
      ((algebraMap B L) '' (U : Set B)) ⟨b, hbU, rfl⟩
  · apply iSup_le
    intro U
    exact
      fraction_formally_unramified
        A B K L U.1 U.2

omit [IsDomain A] [IsDomain B] [Algebra A K] [IsFractionRing A K]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
  [IsScalarTower A K L] in
/-- A finitely generated intermediate field lies in the maximal unramified
field exactly when it lies in the fraction field of one finite formally
unramified stage.  This is the finite-subextension content of Corollaries
7.51--7.52. -/
theorem fg_maximal_formally
    (E : IntermediateField K L) (hEfg : E.FG) :
    E ≤ maximalFormallyIntermediate A B K L ↔
      ∃ U : Subalgebra A B,
        FUSubalg A B U ∧
          E ≤ fractionFieldSubalgebra A B K L U := by
  let I := {U : Subalgebra A B //
    FUSubalg A B U}
  let fields : I → IntermediateField K L := fun U ↦
    fractionFieldSubalgebra A B K L U.1
  constructor
  · intro hE
    rw [formally_i_sup] at hE
    obtain ⟨t, rfl⟩ := hEfg
    have hcompact : IsCompactElement
        (IntermediateField.adjoin K (t : Set L)) :=
      IntermediateField.adjoin_finite_isCompactElement t.finite_toSet
    have hadjoin : IntermediateField.adjoin K (t : Set L) ≤
        ⨆ U : I, fields U := by
      simpa [I, fields] using hE
    obtain ⟨s, hs⟩ :=
      CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
        (α := IntermediateField K L) hcompact fields hadjoin
    classical
    have combine : ∀ u : Finset I,
        ∃ W : I, ∀ V ∈ u, V.1 ≤ W.1 := by
      intro u
      induction u using Finset.induction_on with
      | empty =>
          exact ⟨⟨⊥, formally_subalgebra_bot A B⟩,
            by simp⟩
      | @insert V u hVu ih =>
          obtain ⟨W, hW⟩ := ih
          let VW : Subalgebra A B := V.1 ⊔ W.1
          have hVW : FUSubalg A B VW :=
            V.2.sup A B W.2
          refine ⟨⟨VW, hVW⟩, ?_⟩
          intro Z hZ
          rw [Finset.mem_insert] at hZ
          rcases hZ with rfl | hZu
          · exact le_sup_left
          · exact (hW Z hZu).trans le_sup_right
    obtain ⟨W, hW⟩ := combine s
    refine ⟨W.1, W.2, ?_⟩
    exact hs.trans <| by
      apply iSup_le
      intro V
      apply iSup_le
      intro hVs
      exact fraction_subalgebra_mono A B K L
        (hW V hVs)
  · rintro ⟨U, hU, hEU⟩
    exact hEU.trans
      (fraction_formally_unramified
        A B K L U hU)

omit [IsDomain A] [IsDomain B] [Algebra A K] [IsFractionRing A K]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
  [IsScalarTower A K L] in
/-- The field in Corollary 7.51 is the least intermediate field containing
the fraction field of every finite formally unramified stage.  Thus it is an
actual embedded field `K₀ ⊆ L`, not merely the directed union of valuation
rings. -/
theorem maximal_formally_least :
    IsLeast
      {F : IntermediateField K L |
        ∀ (U : Subalgebra A B),
          FUSubalg A B U →
            fractionFieldSubalgebra A B K L U ≤ F}
      (maximalFormallyIntermediate A B K L) := by
  constructor
  · intro U hU
    exact
      fraction_formally_unramified
        A B K L U hU
  · intro F hF
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨U, hU, hbU⟩ :=
      (formally_subalgebra A B b).mp hb
    apply hF U hU
    exact IntermediateField.subset_adjoin K
      ((algebraMap B L) '' (U : Set B)) ⟨b, hbU, rfl⟩

end InfiniteMaximalUnramifiedField

section MaximalUnramified

variable (A B : Type*) [CommRing A] [CommRing B]
  [HenselianLocalRing A] [HenselianLocalRing B]
  [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- Milne, Corollary 7.51, on valuation rings: lift the whole ambient
residue extension to obtain the maximal finite unramified subalgebra. -/
noncomputable def maximalUnramifiedSubalgebra : Subalgebra A B :=
  unramifiedAdjoinIntermediate A B
    (⊤ : IntermediateField (ResidueField A) (ResidueField B))

theorem maximal_subalgebra_finite :
    Module.Finite A (maximalUnramifiedSubalgebra A B) := by
  exact unramified_adjoin_residue A B
    (⊤ : IntermediateField (ResidueField A) (ResidueField B))

theorem maximal_subalgebra_ring :
    IsLocalRing (maximalUnramifiedSubalgebra A B) := by
  exact adjoin_intermediate_ring A B
    (⊤ : IntermediateField (ResidueField A) (ResidueField B))

theorem maximal_subalgebra_formally :
    Algebra.FormallyUnramified A (maximalUnramifiedSubalgebra A B) := by
  exact adjoin_intermediate_formally A B
    (⊤ : IntermediateField (ResidueField A) (ResidueField B))

theorem subalgebra_discrete_valuation :
    IsDiscreteValuationRing (maximalUnramifiedSubalgebra A B) := by
  exact
    intermediate_discrete_valuation A B
      (⊤ : IntermediateField (ResidueField A) (ResidueField B))

/-- The maximal unramified subalgebra realizes the entire ambient residue
field. -/
theorem maximal_subalgebra_image :
    residueImage A B (maximalUnramifiedSubalgebra A B) = ⊤ := by
  simpa [maximalUnramifiedSubalgebra, residueImageAdjoin] using
    (unramified_adjoin_image A B
      (⊤ : IntermediateField (ResidueField A) (ResidueField B)))

/-- The extension above the maximal unramified subalgebra has no remaining
residue-field extension.  This is the residue-theoretic input for the
totally ramified factor in Remark 7.65. -/
theorem maximal_subalgebra_surjective :
    let U := maximalUnramifiedSubalgebra A B
    letI : IsLocalRing U := maximal_subalgebra_ring A B
    letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
    letI : FaithfulSMul U B :=
      (faithfulSMul_iff_algebraMap_injective U B).mpr (by
        intro x y hxy
        exact Subtype.ext hxy)
    letI : IsLocalHom (algebraMap U B) :=
      Algebra.IsIntegral.isLocalHom U B
    Function.Surjective
      (algebraMap (ResidueField U) (ResidueField B)) := by
  let U := maximalUnramifiedSubalgebra A B
  letI : IsLocalRing U := maximal_subalgebra_ring A B
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr (by
      intro x y hxy
      exact Subtype.ext hxy)
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  dsimp only
  intro y
  obtain ⟨b, rfl⟩ :=
    (residue_surjective : Function.Surjective (residue B)) y
  have hb : residue B b ∈ residueImage A B U := by
    rw [maximal_subalgebra_image A B]
    trivial
  obtain ⟨u, hu, hres⟩ := hb
  let uU : U := ⟨u, hu⟩
  refine ⟨residue U uU, ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  exact hres

/-- Milne, Corollary 7.51, roots-of-unity description: over a complete base
DVR, every root of unity whose order is a unit in the base belongs to the
maximal unramified subalgebra.  Being a unit is the intrinsic version of the
order being prime to the residue characteristic.

The root is first lifted inside the maximal unramified subalgebra from its
residue class.  The lift and the original root agree because reduction is
injective on roots of unity of order invertible in the base. -/
theorem pow_maximal_subalgebra
    [IsAdicComplete (maximalIdeal A) A]
    {n : ℕ} {zeta : B} (hn : IsUnit (n : A))
    (hzeta : zeta ^ n = 1) :
    zeta ∈ maximalUnramifiedSubalgebra A B := by
  let U := maximalUnramifiedSubalgebra A B
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : IsLocalRing U := maximal_subalgebra_ring A B
  letI : HenselianLocalRing U :=
    adjoin_intermediate_henselian A B
      (⊤ : IntermediateField (ResidueField A) (ResidueField B))
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  obtain ⟨zeta₀, hzeta₀⟩ :=
    maximal_subalgebra_surjective A B
      (residue B zeta)
  change algebraMap (ResidueField U) (ResidueField B) zeta₀ =
    residue B zeta at hzeta₀
  have hzeta₀pow : zeta₀ ^ n = 1 := by
    apply (algebraMap (ResidueField U) (ResidueField B)).injective
    rw [map_pow, hzeta₀]
    simpa using congrArg (residue B) hzeta
  let f : U[X] := X ^ n - 1
  have hnU : IsUnit (n : U) := by
    simpa using hn.map (algebraMap A U)
  have hnresidue : (n : ResidueField U) ≠ 0 :=
    (hnU.map (residue U)).ne_zero
  have hnzero : n ≠ 0 := by
    intro hnzero
    subst n
    simp at hn
  have hfmonic : f.Monic := by
    simpa [f] using monic_X_pow_sub_C (1 : U) hnzero
  have hfseparable : (f.map (residue U)).Separable := by
    have : (X ^ n - 1 : (ResidueField U)[X]).Separable :=
      X_pow_sub_one_separable_iff.mpr hnresidue
    simpa [f] using this
  have hzeta₀root : aeval zeta₀ f = 0 := by
    simp [f, aeval_def, hzeta₀pow]
  have hzeta₀simple : aeval zeta₀ (derivative f) ≠ 0 := by
    have hzeta₀rootMapped :
        aeval zeta₀ (f.map (residue U)) = 0 := by
      simp [f, aeval_def, hzeta₀pow]
    have hsimpleMapped :=
      hfseparable.aeval_derivative_ne_zero hzeta₀rootMapped
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map]
    simpa [aeval_def] using hsimpleMapped
  have hlift :=
    ((HenselianLocalRing.TFAE U).out 0 1).mp
      (inferInstance : HenselianLocalRing U)
  obtain ⟨w, hwroot, hwresidue⟩ :=
    hlift f hfmonic zeta₀ hzeta₀root hzeta₀simple
  have hwpow : w ^ n = 1 := by
    exact sub_eq_zero.mp (by
      simpa [f, Polynomial.IsRoot.def] using hwroot)
  have hwpowB : (algebraMap U B w) ^ n = 1 := by
    simpa using congrArg (algebraMap U B) hwpow
  have hwresidueB : residue B (algebraMap U B w) = residue B zeta := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue, hwresidue, hzeta₀]
  have hnB : IsUnit (n : B) := by
    simpa using hn.map (algebraMap A B)
  have heq : algebraMap U B w = zeta :=
    residue_nat_cast hnB
      hwpowB hzeta hwresidueB
  rw [← heq]
  exact w.property

/-- The `A`-algebra generated by all roots of unity of order invertible in
`A` is contained in the maximal unramified subalgebra. -/
theorem characteristic_roots_unity
    [IsAdicComplete (maximalIdeal A) A] :
    Algebra.adjoin A
        {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} ≤
      maximalUnramifiedSubalgebra A B := by
  apply Algebra.adjoin_le
  rintro zeta ⟨n, hn, hzeta⟩
  exact pow_maximal_subalgebra A B hn hzeta

/-- A finite field extension has a nonzero primitive element.  The explicit
nonzero choice is useful because every nonzero element of a finite field is a
root of unity. -/
private theorem nonzero_algebra_field
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l] :
    ∃ x : l, x ≠ 0 ∧ Algebra.adjoin k {x} = ⊤ := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element_of_finite_top k l
  by_cases hx0 : x = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    apply Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (1 : l))
    simpa [hx0] using hx
  · exact ⟨x, hx0,
      Algebra.adjoin_eq_top_of_primitive_element
        (Algebra.IsAlgebraic.isAlgebraic x) hx⟩

/-- Milne, Corollary 7.51, converse roots-of-unity containment.  When the
base residue field is finite, the maximal unramified algebra is generated by
roots of unity of order invertible in the base DVR. -/
theorem subalgebra_characteristic_unity
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] :
    maximalUnramifiedSubalgebra A B ≤
      Algebra.adjoin A
        {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} := by
  let U := maximalUnramifiedSubalgebra A B
  let R := Algebra.adjoin A
    {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1}
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Algebra.FormallyUnramified A U :=
    maximal_subalgebra_formally A B
  letI : IsLocalRing U := maximal_subalgebra_ring A B
  letI : IsLocalHom (algebraMap A U) := Algebra.IsIntegral.isLocalHom A U
  letI : HenselianLocalRing U :=
    adjoin_intermediate_henselian A B
      (⊤ : IntermediateField (ResidueField A) (ResidueField B))
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsLocalHom (algebraMap U B) := Algebra.IsIntegral.isLocalHom U B
  letI : Finite (ResidueField B) := Module.finite_of_finite (ResidueField A)
  letI : Fintype (ResidueField B) := Fintype.ofFinite (ResidueField B)
  obtain ⟨x, hx0, hxgen⟩ :=
    nonzero_algebra_field
      (ResidueField A) (ResidueField B)
  let n := Nat.card (ResidueField B) - 1
  have hnpos : 0 < n := Nat.sub_pos_of_lt Finite.one_lt_card
  have hnx : x ^ n = 1 := by
    simpa [n, Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one x hx0
  have hnB : (n : ResidueField B) ≠ 0 := by
    have hcard : (Nat.card (ResidueField B) : ResidueField B) = 0 := by
      simp [Nat.card_eq_fintype_card]
    rw [show n = Nat.card (ResidueField B) - 1 from rfl,
      Nat.cast_sub (Nat.le_of_lt Finite.one_lt_card), hcard]
    simp
  have hnAres : (n : ResidueField A) ≠ 0 := by
    intro hn
    apply hnB
    simpa using congrArg
      (algebraMap (ResidueField A) (ResidueField B)) hn
  have hnA : IsUnit (n : A) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).mp (by simpa using hnAres)
  obtain ⟨xU, hxU⟩ :=
    maximal_subalgebra_surjective A B x
  change algebraMap (ResidueField U) (ResidueField B) xU = x at hxU
  let e : ResidueField U ≃ₐ[ResidueField A] ResidueField B :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom (ResidueField A)
        (ResidueField U) (ResidueField B))
      ⟨RingHom.injective _,
        maximal_subalgebra_surjective A B⟩
  have hxUgen : Algebra.adjoin (ResidueField A) {xU} = ⊤ := by
    have hmap :
        (Algebra.adjoin (ResidueField A) {xU}).map e.toAlgHom = ⊤ := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      change Algebra.adjoin (ResidueField A)
        {algebraMap (ResidueField U) (ResidueField B) xU} = ⊤
      simpa [hxU] using hxgen
    apply top_unique
    intro y _
    have hey : e y ∈
        (Algebra.adjoin (ResidueField A) {xU}).map e.toAlgHom := by
      rw [hmap]
      trivial
    rcases hey with ⟨z, hz, hzy⟩
    have : z = y := e.injective hzy
    simpa [this] using hz
  have hxUpow : xU ^ n = 1 := by
    apply (algebraMap (ResidueField U) (ResidueField B)).injective
    rw [map_pow, hxU]
    exact hnx
  let f : U[X] := X ^ n - 1
  have hnU : IsUnit (n : U) := by
    simpa using hnA.map (algebraMap A U)
  have hnUres : (n : ResidueField U) ≠ 0 :=
    (hnU.map (residue U)).ne_zero
  have hfmonic : f.Monic := by
    simpa [f] using monic_X_pow_sub_C (1 : U) hnpos.ne'
  have hfseparable : (f.map (residue U)).Separable := by
    have : (X ^ n - 1 : (ResidueField U)[X]).Separable :=
      X_pow_sub_one_separable_iff.mpr hnUres
    simpa [f] using this
  have hxUroot : aeval xU f = 0 := by
    simp [f, aeval_def, hxUpow]
  have hxUsimple : aeval xU (derivative f) ≠ 0 := by
    have hxUrootMapped : aeval xU (f.map (residue U)) = 0 := by
      simp [f, aeval_def, hxUpow]
    have hsimpleMapped :=
      hfseparable.aeval_derivative_ne_zero hxUrootMapped
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map]
    simpa [aeval_def] using hsimpleMapped
  have hlift :=
    ((HenselianLocalRing.TFAE U).out 0 1).mp
      (inferInstance : HenselianLocalRing U)
  obtain ⟨w, hwroot, hwresidue⟩ :=
    hlift f hfmonic xU hxUroot hxUsimple
  have hwpow : w ^ n = 1 := by
    exact sub_eq_zero.mp (by
      simpa [f, Polynomial.IsRoot.def] using hwroot)
  have hwR : (w : B) ∈ R := by
    apply Algebra.subset_adjoin
    exact ⟨n, hnA, by simpa using congrArg (algebraMap U B) hwpow⟩
  let W := Algebra.adjoin A ({(w : B)} : Set B)
  have hWU : W ≤ U := by
    apply Algebra.adjoin_le
    rintro _ ⟨_, rfl⟩
    exact w.property
  have hwresidueB : residue B (w : B) = x := by
    change residue B (algebraMap U B w) = x
    rw [← IsLocalRing.ResidueField.algebraMap_residue, hwresidue, hxU]
  have hresWU : residueImage A B W = residueImage A B U := by
    rw [show W = Algebra.adjoin A ({(w : B)} : Set B) from rfl,
      residue_adjoin_singleton, hwresidueB, hxgen,
      show U = maximalUnramifiedSubalgebra A B from rfl,
      maximal_subalgebra_image]
  have hWUeq : W = U :=
    formally_unramified_image A B W U hWU hresWU
  change U ≤ R
  rw [← hWUeq]
  apply Algebra.adjoin_le
  rintro _ ⟨_, rfl⟩
  exact hwR

/-- Milne, Corollary 7.51, finite-residue-field roots-of-unity
characterization of the maximal unramified subalgebra. -/
theorem characteristic_roots_subalgebra
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] :
    Algebra.adjoin A
        {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} =
      maximalUnramifiedSubalgebra A B := by
  apply le_antisymm
  · exact characteristic_roots_unity A B
  · exact
      subalgebra_characteristic_unity A B

/-- Milne, Corollary 7.51: every finite formally unramified subalgebra of
the ambient local integral algebra is contained in the lift of its full
residue field. -/
theorem unramified_subalgebra
    (U : Subalgebra A B) [Module.Finite A U]
    [Algebra.FormallyUnramified A U] :
    U ≤ maximalUnramifiedSubalgebra A B := by
  letI : Module.Finite A (maximalUnramifiedSubalgebra A B) :=
    maximal_subalgebra_finite A B
  letI : Algebra.FormallyUnramified A (maximalUnramifiedSubalgebra A B) :=
    maximal_subalgebra_formally A B
  apply (formally_unramified_subalgebra A B U
    (maximalUnramifiedSubalgebra A B)).2
  rw [maximal_subalgebra_image]
  exact le_top

/-- Greatest-element packaging of the maximality assertion in Corollary
7.51. -/
theorem maximal_subalgebra_greatest :
    IsGreatest
      {U : Subalgebra A B |
        Module.Finite A U ∧ Algebra.FormallyUnramified A U}
      (maximalUnramifiedSubalgebra A B) := by
  constructor
  · exact ⟨maximal_subalgebra_finite A B,
      maximal_subalgebra_formally A B⟩
  · intro U hU
    letI : Module.Finite A U := hU.1
    letI : Algebra.FormallyUnramified A U := hU.2
    exact unramified_subalgebra A B U

/-- In the finite separable residue-field case, the directed union of all
finite formally unramified subalgebras agrees with the explicit lift of the
full residue field. -/
theorem maximal_formally_subalgebra :
    maximalFormallySubalgebra A B =
      maximalUnramifiedSubalgebra A B := by
  apply le_antisymm
  · apply iSup_le
    intro U
    letI : Module.Finite A U.1 := U.property.1
    letI : Algebra.FormallyUnramified A U.1 := U.property.2
    exact unramified_subalgebra A B U.1
  · exact maximal_subalgebra A B
      (maximalUnramifiedSubalgebra A B)
      ⟨maximal_subalgebra_finite A B,
        maximal_subalgebra_formally A B⟩

end MaximalUnramified

section InfiniteMaximalUnramifiedRootsOfUnity

/-- A prime-to-residue-characteristic root of unity in a possibly infinite
integral ambient local domain lies in a finite formally unramified stage.

The finite residue extension generated by its reduction has an unramified
lift. Hensel lifting inside that stage and uniqueness of roots with the same
reduction identify the lifted root with the original one. -/
theorem pow_formally_subalgebra
    (A B : Type*) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [IsAdicComplete (maximalIdeal A) A]
    [Finite (ResidueField A)]
    {n : ℕ} {zeta : B} (hn : IsUnit (n : A))
    (hzeta : zeta ^ n = 1) :
    zeta ∈ maximalFormallySubalgebra A B := by
  let k := ResidueField A
  let l := ResidueField B
  let x : l := residue B zeta
  let E : IntermediateField k l := IntermediateField.adjoin k {x}
  have hxint : IsIntegral k x := by
    refine ⟨X ^ n - 1, ?_, ?_⟩
    · have hnzero : n ≠ 0 := by
        intro hnzero
        subst n
        simp at hn
      simpa using monic_X_pow_sub_C (1 : k) hnzero
    · simp only [eval₂_sub, eval₂_X_pow, eval₂_one]
      rw [sub_eq_zero, show x ^ n = residue B (zeta ^ n) by simp [x], hzeta,
        map_one]
  letI : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin (S := ({x} : Set l)) <| by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hxint
  letI : Algebra.IsSeparable k E := inferInstance
  let U := unramifiedAdjoinIntermediate A B E
  letI : Module.Finite A U :=
    unramified_adjoin_residue A B E
  letI : IsLocalRing U :=
    adjoin_intermediate_ring A B E
  letI : HenselianLocalRing U :=
    adjoin_intermediate_henselian A B E
  letI : Algebra.FormallyUnramified A U :=
    adjoin_intermediate_formally A B E
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  have hxE : x ∈ E :=
    IntermediateField.subset_adjoin k ({x} : Set l) (Set.mem_singleton x)
  have hximage : x ∈ residueImage A B U := by
    change x ∈ residueImageAdjoin A B
      (unramifiedIntermediateLift A B E).generator
    rw [unramified_adjoin_image]
    exact hxE
  obtain ⟨u, hu, hures⟩ := hximage
  let uU : U := ⟨u, hu⟩
  let zeta₀ : ResidueField U := residue U uU
  have hzeta₀image :
      algebraMap (ResidueField U) (ResidueField B) zeta₀ =
        residue B zeta := by
    rw [show zeta₀ = residue U uU from rfl,
      IsLocalRing.ResidueField.algebraMap_residue]
    exact hures
  have hzeta₀pow : zeta₀ ^ n = 1 := by
    apply (algebraMap (ResidueField U) (ResidueField B)).injective
    rw [map_pow, hzeta₀image]
    simpa using congrArg (residue B) hzeta
  let f : U[X] := X ^ n - 1
  have hnU : IsUnit (n : U) := by
    simpa using hn.map (algebraMap A U)
  have hnresidue : (n : ResidueField U) ≠ 0 :=
    (hnU.map (residue U)).ne_zero
  have hnzero : n ≠ 0 := by
    intro hnzero
    subst n
    simp at hn
  have hfmonic : f.Monic := by
    simpa [f] using monic_X_pow_sub_C (1 : U) hnzero
  have hfseparable : (f.map (residue U)).Separable := by
    have : (X ^ n - 1 : (ResidueField U)[X]).Separable :=
      X_pow_sub_one_separable_iff.mpr hnresidue
    simpa [f] using this
  have hzeta₀root : aeval zeta₀ f = 0 := by
    simp [f, aeval_def, hzeta₀pow]
  have hzeta₀simple : aeval zeta₀ (derivative f) ≠ 0 := by
    have hzeta₀rootMapped :
        aeval zeta₀ (f.map (residue U)) = 0 := by
      simp [f, aeval_def, hzeta₀pow]
    have hsimpleMapped :=
      hfseparable.aeval_derivative_ne_zero hzeta₀rootMapped
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map]
    simpa [aeval_def] using hsimpleMapped
  have hlift :=
    ((HenselianLocalRing.TFAE U).out 0 1).mp
      (inferInstance : HenselianLocalRing U)
  obtain ⟨w, hwroot, hwresidue⟩ :=
    hlift f hfmonic zeta₀ hzeta₀root hzeta₀simple
  have hwpow : w ^ n = 1 := by
    exact sub_eq_zero.mp (by
      simpa [f, Polynomial.IsRoot.def] using hwroot)
  have hwpowB : (algebraMap U B w) ^ n = 1 := by
    simpa using congrArg (algebraMap U B) hwpow
  have hwresidueB : residue B (algebraMap U B w) = residue B zeta := by
    rw [← IsLocalRing.ResidueField.algebraMap_residue, hwresidue,
      hzeta₀image]
  have hnB : IsUnit (n : B) := by
    simpa using hn.map (algebraMap A B)
  have heq : algebraMap U B w = zeta :=
    residue_nat_cast hnB
      hwpowB hzeta hwresidueB
  apply (formally_subalgebra A B zeta).2
  refine ⟨U, ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [← heq]
  exact w.property

/-- Every finite formally unramified stage in a possibly infinite integral
ambient local domain is generated by prime-to-residue-characteristic roots
of unity, and hence their directed union is contained in the algebra generated
by all such roots in the ambient domain. -/
theorem formally_characteristic_unity
    (A B : Type*) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [IsAdicComplete (maximalIdeal A) A]
    [Finite (ResidueField A)] :
    maximalFormallySubalgebra A B ≤
      Algebra.adjoin A
        {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} := by
  apply iSup_le
  intro U
  let V := U.1
  letI : Module.Finite A V := U.2.1
  letI : Algebra.FormallyUnramified A V := U.2.2
  letI : FaithfulSMul A V :=
    (faithfulSMul_iff_algebraMap_injective A V).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A V :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A V)
  letI : Algebra.IsIntegral A V := Algebra.IsIntegral.of_finite A V
  letI : IsLocalRing V := subalgebra_ring_integral A B V
  letI : IsLocalHom (algebraMap A V) :=
    Algebra.IsIntegral.isLocalHom A V
  letI : HenselianLocalRing V :=
    henselian_formally_unramified A V
  letI : FiniteDimensional (ResidueField A) (ResidueField V) :=
    inferInstance
  letI : Algebra.IsSeparable (ResidueField A) (ResidueField V) :=
    inferInstance
  have hmax : maximalUnramifiedSubalgebra A V = ⊤ := by
    letI : Module.Finite A (⊤ : Subalgebra A V) :=
      Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv.symm)
    letI : Algebra.FormallyUnramified A (⊤ : Subalgebra A V) :=
      Algebra.FormallyUnramified.of_equiv Subalgebra.topEquiv.symm
    apply top_unique
    exact unramified_subalgebra A V ⊤
  have hgenerated : Algebra.adjoin A
        {zeta : V | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} = ⊤ := by
    rw [characteristic_roots_subalgebra,
      hmax]
  let R := Algebra.adjoin A
    {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1}
  have hmap : Algebra.adjoin A
      {zeta : V | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} ≤
      R.comap V.val := by
    apply Algebra.adjoin_le
    rintro zeta ⟨n, hn, hzeta⟩
    apply Algebra.subset_adjoin
    exact ⟨n, hn, by simpa using congrArg Subtype.val hzeta⟩
  intro b hb
  let bV : V := ⟨b, hb⟩
  have hbtop : bV ∈ (⊤ : Subalgebra A V) := trivial
  rw [← hgenerated] at hbtop
  exact hmap hbtop

/-- Milne, Corollary 7.51, in a possibly infinite integral ambient local
domain: the union of its finite unramified stages is exactly the algebra
generated by roots of unity whose orders are units in the base DVR. -/
theorem characteristic_unity_subalgebra
    (A B : Type*) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [IsAdicComplete (maximalIdeal A) A]
    [Finite (ResidueField A)] :
    Algebra.adjoin A
        {zeta : B | ∃ n : ℕ, IsUnit (n : A) ∧ zeta ^ n = 1} =
      maximalFormallySubalgebra A B := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro zeta ⟨n, hn, hzeta⟩
    exact pow_formally_subalgebra
      A B hn hzeta
  · exact
      formally_characteristic_unity
        A B

end InfiniteMaximalUnramifiedRootsOfUnity

section ResidueAlgebraicClosure

set_option maxHeartbeats 2000000 in
-- Splitting lifted polynomials over an algebraic closure exceeds the default heartbeat budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- Elaborating the quotient algebra structure requires a deeper typeclass search.
/-- Corollary 7.52 with an explicit choice of the extension of the valuation:
for every maximal ideal of the integral closure lying over the maximal ideal
of `A`, the corresponding residue field is an algebraic closure of the base
residue field.

This formulation does not require the entire integral closure to be local;
choosing `P` is exactly the algebraic datum of choosing a prolongation of the
valuation to the algebraic closure. -/
theorem integral_closure_alg
    (A Omega : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field Omega] [Algebra A Omega] [FaithfulSMul A Omega] [IsAlgClosed Omega]
    (P : Ideal (integralClosure A Omega)) [P.IsMaximal]
    [P.LiesOver (maximalIdeal A)] :
    letI : Algebra (ResidueField A)
        (integralClosure A Omega ⧸ P) :=
      Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
    IsAlgClosure (ResidueField A) (integralClosure A Omega ⧸ P) := by
  let B := integralClosure A Omega
  letI : Algebra (ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
  letI : Algebra.IsIntegral (ResidueField A) (B ⧸ P) := by
    change Algebra.IsIntegral (A ⧸ maximalIdeal A) (B ⧸ P)
    infer_instance
  apply IsAlgClosure.of_splits
  intro f₀ hf₀monic _hf₀irreducible
  have hf₀lift : f₀ ∈ Polynomial.lifts (residue A) :=
    Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective f₀
  obtain ⟨f, hfmap, _hfdegree, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf₀lift hf₀monic
  have hsplitsOmega :
      (f.map (algebraMap A Omega)).Splits :=
    IsAlgClosed.splits (f.map (algebraMap A Omega))
  have hsplitsB : (f.map (algebraMap A B)).Splits := by
    apply Splits.of_splits_map_of_injective
      (i := (integralClosure A Omega).val.toRingHom)
      Subtype.val_injective
    · simpa [B, Polynomial.map_map] using hsplitsOmega
    · intro x hx
      have hxroot : (f.map (algebraMap A Omega)).eval x = 0 := by
        have hx' := (mem_roots
          (((hfmonic.map (algebraMap A B)).map
            (integralClosure A Omega).val.toRingHom).ne_zero)).mp hx
        simpa [B, Polynomial.map_map] using hx'
      have hxintegral : IsIntegral A x := by
        refine ⟨f, hfmonic, ?_⟩
        simpa [aeval_def] using hxroot
      exact ⟨⟨x, hxintegral⟩, rfl⟩
  have hsplitsResidue := hsplitsB.map (Ideal.Quotient.mk P)
  have hreduce :
      (f.map (algebraMap A B)).map (Ideal.Quotient.mk P) =
        f₀.map (algebraMap (ResidueField A) (B ⧸ P)) := by
    rw [← hfmap]
    ext n
    simp only [coeff_map]
    exact (Ideal.Quotient.algebraMap_mk_of_liesOver P
      (maximalIdeal A) (f.coeff n)).symm
  rw [hreduce] at hsplitsResidue
  exact hsplitsResidue

set_option maxHeartbeats 2000000 in
-- Transporting the algebraic-closure result through the residue tower exceeds the default budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- Elaborating the residue-field algebra tower requires a deeper typeclass search.
/-- Milne, Corollary 7.52: if the integral closure of a local domain in an
algebraically closed field is local, then its residue field is an algebraic
closure of the residue field of the base.

For a Henselian valuation ring the locality expresses the chosen extension
of the valuation to the algebraic closure. -/
theorem residue_closure_alg
    (A Omega : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field Omega] [Algebra A Omega] [FaithfulSMul A Omega] [IsAlgClosed Omega]
    [IsLocalRing (integralClosure A Omega)] :
    letI : FaithfulSMul A (integralClosure A Omega) :=
      (faithfulSMul_iff_algebraMap_injective A
        (integralClosure A Omega)).mpr (by
          intro x y hxy
          apply FaithfulSMul.algebraMap_injective A Omega
          exact congrArg Subtype.val hxy)
    letI : IsLocalHom (algebraMap A (integralClosure A Omega)) :=
      Algebra.IsIntegral.isLocalHom A (integralClosure A Omega)
    IsAlgClosure (ResidueField A)
      (ResidueField (integralClosure A Omega)) := by
  let B := integralClosure A Omega
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr (by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A Omega
      exact congrArg Subtype.val hxy)
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  letI : Algebra.IsIntegral (ResidueField A) (ResidueField B) :=
    by
      change Algebra.IsIntegral
        (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B)
      infer_instance
  apply IsAlgClosure.of_splits
  intro f₀ hf₀monic _hf₀irreducible
  have hf₀lift : f₀ ∈ Polynomial.lifts (residue A) :=
    Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective f₀
  obtain ⟨f, hfmap, _hfdegree, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf₀lift hf₀monic
  have hsplitsOmega :
      (f.map (algebraMap A Omega)).Splits :=
    IsAlgClosed.splits (f.map (algebraMap A Omega))
  have hsplitsB : (f.map (algebraMap A B)).Splits := by
    apply Splits.of_splits_map_of_injective
      (i := (integralClosure A Omega).val.toRingHom)
      Subtype.val_injective
    · simpa [B, Polynomial.map_map] using hsplitsOmega
    · intro x hx
      have hxroot : (f.map (algebraMap A Omega)).eval x = 0 := by
        have hx' := (mem_roots
          (((hfmonic.map (algebraMap A B)).map
            (integralClosure A Omega).val.toRingHom).ne_zero)).mp hx
        simpa [B, Polynomial.map_map] using hx'
      have hxintegral : IsIntegral A x := by
        refine ⟨f, hfmonic, ?_⟩
        simpa [aeval_def] using hxroot
      exact ⟨⟨x, hxintegral⟩, rfl⟩
  have hsplitsResidue := hsplitsB.map (residue B)
  have hreduce :
      (f.map (algebraMap A B)).map (residue B) =
        f₀.map (algebraMap (ResidueField A) (ResidueField B)) := by
    rw [← hfmap]
    ext n
    simp only [coeff_map]
    exact (IsLocalRing.ResidueField.algebraMap_residue (f.coeff n)).symm
  rw [hreduce] at hsplitsResidue
  exact hsplitsResidue

end ResidueAlgebraicClosure

section AlgebraicClosureMaximalUnramifiedField

variable (A K Omega : Type*)
  [CommRing A] [IsDomain A] [Field K] [Field Omega]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K Omega] [Algebra A Omega] [IsScalarTower A K Omega]
  [IsAlgClosure K Omega]

/-- Corollary 7.52: the maximal unramified intermediate field `K^un` inside
a chosen algebraic closure.  It is generated by the fraction fields of all
finite formally unramified subalgebras of the integral closure of `A` in
`Omega`. -/
noncomputable def maximalAlgebraicClosure :
    IntermediateField K Omega := by
  let B := integralClosure A Omega
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : Algebra.IsAlgebraic A Omega :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K Omega)
  letI : IsFractionRing B Omega :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Omega) <| by
      intro x hx
      exact hAinj (by simpa using hx)
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <| by
      intro x y hxy
      apply hAinj
      exact congrArg Subtype.val hxy
  exact maximalFormallyIntermediate A B K Omega

/-- The intrinsic integral model of an embedded intermediate field: the
elements of the integral closure of `A` in `Omega` that lie in `E`. -/
noncomputable def intermediateIntegralModel
    (E : IntermediateField K Omega) :
    Subalgebra A (integralClosure A Omega) :=
  (E.toSubalgebra.restrictScalars A).comap
    (integralClosure A Omega).val

/-- A finite embedded intermediate field is unramified when its intrinsic
integral model is module-finite and formally unramified over `A`. -/
def FUInterm
    (E : IntermediateField K Omega) : Prop :=
  E.FG ∧
    FUSubalg A (integralClosure A Omega)
      (intermediateIntegralModel A K Omega E)

omit [IsAlgClosure K Omega] in
include K in
/-- A finite formally unramified integral stage over a Henselian DVR is
again a DVR. -/
theorem FUSubalg.discreteValuation
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))]
    (V : Subalgebra A (integralClosure A Omega))
    (hV : FUSubalg A
      (integralClosure A Omega) V) :
    IsDiscreteValuationRing V := by
  letI : Module.Finite A V := hV.1
  letI : Algebra.FormallyUnramified A V := hV.2
  letI : FaithfulSMul A V :=
    (faithfulSMul_iff_algebraMap_injective A V).mpr <| by
      intro x y hxy
      apply IsFractionRing.injective A K
      apply (algebraMap K Omega).injective
      simpa [IsScalarTower.algebraMap_apply A K Omega] using
        congrArg (fun z : V ↦ (z : Omega)) hxy
  letI : IsLocalRing V :=
    subalgebra_ring_integral A (integralClosure A Omega) V
  letI : IsDedekindDomainDvr V :=
    isDedekindDomainDvr.of_formallyUnramified A V
  have hmax : maximalIdeal V ≠ ⊥ := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := V)]
    exact (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective A V)).not.mpr
        (IsDiscreteValuationRing.not_a_field A)
  exact ((IsDiscreteValuationRing.TFAE V
    (IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmax)).out 2 0).mp
      (inferInstance : IsDedekindDomain V)

omit [IsAlgClosure K Omega] in
include K in
/-- The fraction field generated by the intrinsic integral model of `E` is
exactly `E`. -/
theorem fraction_intermediate_model
    [Algebra.IsAlgebraic K Omega]
    (E : IntermediateField K Omega) :
    fractionFieldSubalgebra A (integralClosure A Omega) K Omega
        (intermediateIntegralModel A K Omega E) = E := by
  let B := integralClosure A Omega
  let U := intermediateIntegralModel A K Omega E
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  · intro x hx
    let xE : E := ⟨x, hx⟩
    have hxint : IsIntegral K xE :=
      IntermediateField.isIntegral_iff.mpr <|
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization
        (M := nonZeroDivisors A) xE hxint
    let y : B :=
      ⟨(E.val.restrictScalars A) (m • xE),
        hm.map (E.val.restrictScalars A)⟩
    let d : B := algebraMap A B m
    have hyU : y ∈ U := by
      exact (m • xE).property
    have hdU : d ∈ U := by
      change algebraMap A Omega m ∈ E
      rw [IsScalarTower.algebraMap_apply A K Omega]
      exact E.algebraMap_mem (algebraMap A K (m : A))
    let F := fractionFieldSubalgebra A B K Omega U
    have hyF : algebraMap B Omega y ∈ F :=
      IntermediateField.subset_adjoin K
        ((algebraMap B Omega) '' (U : Set B)) ⟨y, hyU, rfl⟩
    have hdF : algebraMap B Omega d ∈ F :=
      IntermediateField.subset_adjoin K
        ((algebraMap B Omega) '' (U : Set B)) ⟨d, hdU, rfl⟩
    have hmOmega : algebraMap A Omega (m : A) ≠ 0 := by
      intro hm
      have hmK : algebraMap A K (m : A) = 0 := by
        apply (algebraMap K Omega).injective
        simp [IsScalarTower.algebraMap_apply A K Omega] at hm
      have hmA : (m : A) = 0 :=
        IsFractionRing.injective A K (by simp at hmK)
      exact nonZeroDivisors.ne_zero m.property hmA
    have hquot : algebraMap B Omega y / algebraMap B Omega d = x := by
      simpa [y, d, B, xE, Submonoid.smul_def, Algebra.smul_def] using
        (mul_div_cancel_left₀ x hmOmega)
    rw [← hquot]
    exact F.div_mem hyF hdF

/-- Over a Noetherian normal base with perfect fraction field, the intrinsic
integral model of a finite intermediate field is module-finite. -/
theorem intermediate_model_module
    [IsIntegrallyClosed A] [IsNoetherianRing A] [PerfectField K]
    (E : IntermediateField K Omega) (hEfg : E.FG) :
    Module.Finite A (intermediateIntegralModel A K Omega E) := by
  letI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr hEfg
  letI : Module.Finite K E :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : Algebra.IsSeparable K E := inferInstance
  letI : Module.Finite A (integralClosure A E) :=
    integral_module_noetherian A K E
  let U := intermediateIntegralModel A K Omega E
  let f : integralClosure A E →ₐ[A] integralClosure A Omega :=
    (E.val.restrictScalars A).mapIntegralClosure
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply E.val.injective
    simpa [f] using
      congrArg (fun z : integralClosure A Omega ↦ (z : Omega)) hxy
  have hrange : f.range = U := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.1.property
    · intro hz
      let zE : E := ⟨z.1, hz⟩
      have hzint : IsIntegral A zE :=
        (isIntegral_algHom_iff (E.val.restrictScalars A)
          E.val.injective).mp
            ((mem_integralClosure_iff A Omega).mp z.property)
      let w : integralClosure A E := ⟨zE, hzint⟩
      exact ⟨w, Subtype.ext rfl⟩
  let e : integralClosure A E ≃ₐ[A] U :=
    (AlgEquiv.ofInjective f hf).trans
      (Subalgebra.equivOfEq f.range U hrange)
  exact Module.Finite.equiv e.toLinearEquiv

/-- The intrinsic integral model acts on its embedded fraction field by the
ambient inclusion. -/
@[reducible] noncomputable def intermediateModelAlgebra
    (E : IntermediateField K Omega) :
    Algebra (intermediateIntegralModel A K Omega E) E :=
  ({ (((IsScalarTower.toAlgHom A (integralClosure A Omega) Omega).comp
      (intermediateIntegralModel A K Omega E).val).toRingHom.codRestrict
        E.toSubring fun u ↦ u.property) with
      commutes' := fun a ↦ Subtype.ext
        (IsScalarTower.algebraMap_apply A (integralClosure A Omega) Omega a).symm } :
    intermediateIntegralModel A K Omega E →ₐ[A] E).toRingHom.toAlgebra

/-- Under the standard finite-separable hypotheses, the intrinsic model is
the integral closure of `A` in `E`, hence is a Dedekind domain. -/
theorem intermediate_dedekind_domain
    [IsDiscreteValuationRing A] [PerfectField K]
    (E : IntermediateField K Omega) (hEfg : E.FG) :
    IsDedekindDomain (intermediateIntegralModel A K Omega E) := by
  let B := integralClosure A Omega
  let U := intermediateIntegralModel A K Omega E
  letI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr hEfg
  letI : Module.Finite K E :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : Algebra.IsSeparable K E := inferInstance
  let algUE : Algebra U E := intermediateModelAlgebra A K Omega E
  letI : SMul U E := algUE.toSMul
  letI : Algebra U E := algUE
  letI : IsScalarTower A U E := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap A Omega a =
      algebraMap B Omega (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B Omega a
  letI : IsIntegralClosure U A E := by
    refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : E ↦ (z : Omega)) hxy
    · intro x
      constructor
      · intro hx
        have hxOmega : IsIntegral A (x : Omega) :=
          hx.map (E.val.restrictScalars A)
        obtain ⟨b, hb⟩ :=
          (IsIntegralClosure.isIntegral_iff (R := A) (A := B)
            (B := Omega)).mp hxOmega
        have hbE : algebraMap B Omega b ∈ E := by
          rw [hb]
          exact x.property
        refine ⟨⟨b, hbE⟩, ?_⟩
        apply E.val.injective
        change algebraMap B Omega b = (x : Omega)
        exact hb
      · rintro ⟨y, rfl⟩
        apply (isIntegral_algHom_iff (E.val.restrictScalars A)
          E.val.injective).mp
        change IsIntegral A (algebraMap B Omega (y : B))
        exact (IsIntegralClosure.isIntegral A Omega (y : B)).map
          (IsScalarTower.toAlgHom A B Omega)
  exact IsIntegralClosure.isDedekindDomain A K E U

omit [IsAlgClosure K Omega] in
include K in
/-- If `E` lies in the fraction field of a finite unramified stage `V`,
then every element of its intrinsic integral model already lies in `V`. -/
theorem intermediate_model_fraction
    [Algebra.IsAlgebraic K Omega]
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))]
    (E : IntermediateField K Omega)
    (V : Subalgebra A (integralClosure A Omega))
    (hV : FUSubalg A
      (integralClosure A Omega) V)
    (hEV : E ≤ fractionFieldSubalgebra A
      (integralClosure A Omega) K Omega V) :
    intermediateIntegralModel A K Omega E ≤ V := by
  let B := integralClosure A Omega
  let F := fractionFieldSubalgebra A B K Omega V
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : Algebra.IsAlgebraic A Omega :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K Omega)
  letI : IsFractionRing B Omega :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Omega) <| by
      intro x hx
      exact hAinj (by simpa using hx)
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <| by
      intro x y hxy
      apply hAinj
      exact congrArg Subtype.val hxy
  letI : IsDiscreteValuationRing V :=
    hV.discreteValuation A K Omega V
  let algVF : Algebra V F :=
    fractionIntermediateSubalgebra A B K Omega V
  letI : SMul V F := algVF.toSMul
  letI : Algebra V F := algVF
  letI : FaithfulSMul A V :=
    (faithfulSMul_iff_algebraMap_injective A V).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : IsScalarTower A V F := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap A Omega a = algebraMap B Omega (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B Omega a
  letI : IsFractionRing V F :=
    fraction_intermediate_subalgebra A B K Omega V
  intro u hu
  let x : F := ⟨algebraMap B Omega u, hEV hu⟩
  have hxA : IsIntegral A x := by
    apply (isIntegral_algHom_iff (F.val.restrictScalars A)
      F.val.injective).mp
    exact (Algebra.IsIntegral.isIntegral u).map
      (IsScalarTower.toAlgHom A B Omega)
  have hxV : IsIntegral V x := hxA.tower_top
  obtain ⟨v, hv⟩ := (isIntegrallyClosed_iff F).mp inferInstance hxV
  have hvOmega := congrArg (fun y : F ↦ (y : Omega)) hv
  change algebraMap B Omega (v : B) = algebraMap B Omega u at hvOmega
  have huvB : u = (v : B) := Subtype.val_injective hvOmega.symm
  exact huvB.symm ▸ v.property

/-- Formal unramifiedness descends to the intrinsic integral model of a
finite intermediate subfield of an unramified stage. -/
theorem intermediate_model_formally
    [IsDiscreteValuationRing A] [HenselianLocalRing A] [PerfectField K]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))]
    (E : IntermediateField K Omega) (hEfg : E.FG)
    (V : Subalgebra A (integralClosure A Omega))
    (hV : FUSubalg A
      (integralClosure A Omega) V)
    (hEV : E ≤ fractionFieldSubalgebra A
      (integralClosure A Omega) K Omega V) :
    Algebra.FormallyUnramified A
      (intermediateIntegralModel A K Omega E) := by
  let B := integralClosure A Omega
  let U := intermediateIntegralModel A K Omega E
  letI : Module.Finite A U :=
    intermediate_model_module A K Omega E hEfg
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : IsLocalRing V := subalgebra_ring_integral A B V
  letI : IsDedekindDomain U :=
    intermediate_dedekind_domain A K Omega E hEfg
  have hUV : U ≤ V :=
    intermediate_model_fraction
      A K Omega E V hV hEV
  exact hV.formally_unram_le A B U V hUV

omit [IsDomain A] [IsFractionRing A K] [IsAlgClosure K Omega] in
/-- Taking the intrinsic integral model is monotone on embedded intermediate
fields. -/
theorem intermediate_model_mono :
    Monotone (intermediateIntegralModel A K Omega) := by
  intro E F hEF x hx
  exact hEF hx

omit [IsAlgClosure K Omega] in
include K in
/-- A finite formally unramified integral stage is recovered as the integral
elements in its generated fraction field.  This is the bridge from the
valuation-ring correspondence in Proposition 7.50 to its literal formulation
in terms of embedded intermediate fields. -/
theorem intermediate_integral_fraction
    [Algebra.IsAlgebraic K Omega]
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))]
    (U : Subalgebra A (integralClosure A Omega))
    (hU : FUSubalg A
      (integralClosure A Omega) U) :
    intermediateIntegralModel A K Omega
        (fractionFieldSubalgebra A
          (integralClosure A Omega) K Omega U) = U := by
  apply le_antisymm
  · exact intermediate_model_fraction
      A K Omega
      (fractionFieldSubalgebra A
        (integralClosure A Omega) K Omega U)
      U hU le_rfl
  · intro u hu
    exact IntermediateField.subset_adjoin K
      ((algebraMap (integralClosure A Omega) Omega) ''
        (U : Set (integralClosure A Omega)))
      ⟨u, hu, rfl⟩

/-- Finite unramified intermediate fields of a fixed algebraic closure,
bundled for the field-level correspondence in Proposition 7.50. -/
def FiniteIntermediateField :=
  {E : IntermediateField K Omega //
    FUInterm A K Omega E}

instance unramifiedIntermediateField :
    LE (FiniteIntermediateField A K Omega) :=
  ⟨fun E F ↦ E.1 ≤ F.1⟩

/-- Proposition 7.50 at the embedded-field level, before reduction: taking
integral elements gives an order isomorphism between finite unramified
intermediate fields and finite formally unramified valuation subalgebras. -/
noncomputable def intermediateIsoSubalgebra
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))] :
    FiniteIntermediateField A K Omega ≃o
      FiniteFormallySubalgebra A (integralClosure A Omega) := by
  let B := integralClosure A Omega
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : Algebra.IsAlgebraic A Omega :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K Omega)
  letI : IsFractionRing B Omega :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Omega) <| by
      intro x hx
      exact hAinj (by simpa using hx)
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <| by
      intro x y hxy
      apply hAinj
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A B)
  let toField : FiniteFormallySubalgebra A B →
      FiniteIntermediateField A K Omega := fun U ↦ by
    let F := fractionFieldSubalgebra A B K Omega U.1
    let algUF : Algebra U.1 F :=
      fractionIntermediateSubalgebra A B K Omega U.1
    letI : SMul U.1 F := algUF.toSMul
    letI : Algebra U.1 F := algUF
    letI : IsFractionRing U.1 F :=
      fraction_intermediate_subalgebra
        A B K Omega U.1
    letI : FaithfulSMul A U.1 :=
      (faithfulSMul_iff_algebraMap_injective A U.1).mpr <| by
        intro x y hxy
        apply FaithfulSMul.algebraMap_injective A B
        exact congrArg Subtype.val hxy
    letI : Module.Finite A U.1 := U.2.1
    letI : Module.IsTorsionFree A U.1 :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (FaithfulSMul.algebraMap_injective A U.1)
    letI : Algebra.IsIntegral A U.1 :=
      Algebra.IsIntegral.of_finite A U.1
    letI : Algebra.IsAlgebraic A U.1 :=
      Algebra.IsIntegral.isAlgebraic
    letI : IsScalarTower A U.1 F := IsScalarTower.of_algebraMap_eq' <| by
      ext a
      change algebraMap A Omega a =
        algebraMap B Omega (algebraMap A B a)
      exact IsScalarTower.algebraMap_apply A B Omega a
    letI : Module.Finite K F :=
      Module.Finite.of_isLocalization A U.1 (nonZeroDivisors A)
    refine ⟨F, IntermediateField.essFiniteType_iff.mp inferInstance, ?_⟩
    rw [intermediate_integral_fraction
      A K Omega U.1 U.2]
    exact U.2
  refine
    { toEquiv :=
        { toFun := fun E ↦
            ⟨intermediateIntegralModel A K Omega E.1, E.2.2⟩
          invFun := toField
          left_inv := by
            intro E
            apply Subtype.ext
            dsimp only [toField]
            exact fraction_intermediate_model
              A K Omega E.1
          right_inv := by
            intro U
            apply Subtype.ext
            dsimp only [toField]
            exact intermediate_integral_fraction
              A K Omega U.1 U.2 }
      map_rel_iff' := ?_ }
  intro E F
  change intermediateIntegralModel A K Omega E.1 ≤
      intermediateIntegralModel A K Omega F.1 ↔ E.1 ≤ F.1
  constructor
  · intro h
    rw [← fraction_intermediate_model A K Omega E.1,
      ← fraction_intermediate_model A K Omega F.1]
    exact fraction_subalgebra_mono A B K Omega h
  · intro h
    exact intermediate_model_mono A K Omega h

/-- Milne, Proposition 7.50 in its literal embedded-field form: finite
unramified intermediate fields of the chosen algebraic closure correspond,
order-isomorphically, to finite separable intermediate extensions of the
ambient residue field. -/
noncomputable def intermediateIsoResidue
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))] :
    FiniteIntermediateField A K Omega ≃o
      SeparableResidueIntermediate A
        (integralClosure A Omega) := by
  let B := integralClosure A Omega
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr <| by
      intro x y hxy
      apply hAinj
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A B)
  exact (intermediateIsoSubalgebra
    A K Omega).trans
      (subalgebraIsoIntermediate A B)

omit [IsDomain A] [IsAlgClosure K Omega] in
/-- Every finite formally unramified integral stage in the algebraic closure
has its fraction field contained in `K^un`. -/
theorem fraction_intermediate_algebraic
    [Algebra.IsAlgebraic K Omega]
    (U : Subalgebra A (integralClosure A Omega))
    (hU : FUSubalg A
      (integralClosure A Omega) U) :
    fractionFieldSubalgebra A (integralClosure A Omega)
        K Omega U ≤
      maximalAlgebraicClosure A K Omega := by
  letI : IsDomain A :=
    Function.Injective.isDomain (algebraMap A K)
      (IsFractionRing.injective A K)
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : Algebra.IsAlgebraic A Omega :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K Omega)
  letI : IsFractionRing (integralClosure A Omega) Omega :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Omega) <| by
      intro x hx
      exact hAinj (by simpa using hx)
  letI : FaithfulSMul A (integralClosure A Omega) :=
    (faithfulSMul_iff_algebraMap_injective A
      (integralClosure A Omega)).mpr <| by
        intro x y hxy
        apply hAinj
        exact congrArg Subtype.val hxy
  exact fraction_formally_unramified
    A (integralClosure A Omega) K Omega U hU

/-- An intermediate field whose intrinsic integral model is finite and
formally unramified is contained in the maximal unramified extension. -/
theorem FUInterm.le_maximalUnramified
    {E : IntermediateField K Omega}
    (hE : FUInterm A K Omega E) :
    E ≤ maximalAlgebraicClosure A K Omega := by
  rw [← fraction_intermediate_model A K Omega E]
  exact fraction_intermediate_algebraic
    A K Omega (intermediateIntegralModel A K Omega E) hE.2

omit [IsDomain A] [IsAlgClosure K Omega] in
/-- Corollary 7.52, finite-subextension characterization: a finitely
generated subfield of the algebraic closure lies in `K^un` exactly when it
is contained in the fraction field of one finite formally unramified
integral stage. -/
theorem fg_algebraic_closure
    [Algebra.IsAlgebraic K Omega]
    (E : IntermediateField K Omega) (hEfg : E.FG) :
    E ≤ maximalAlgebraicClosure A K Omega ↔
      ∃ U : Subalgebra A (integralClosure A Omega),
        FUSubalg A
            (integralClosure A Omega) U ∧
          E ≤ fractionFieldSubalgebra A
            (integralClosure A Omega) K Omega U := by
  letI : IsDomain A :=
    Function.Injective.isDomain (algebraMap A K)
      (IsFractionRing.injective A K)
  have hAinj : Function.Injective (algebraMap A Omega) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K Omega).injective
    exact (IsScalarTower.algebraMap_apply A K Omega x).symm.trans <|
      hxy.trans (IsScalarTower.algebraMap_apply A K Omega y)
  letI : Algebra.IsAlgebraic A Omega :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K Omega)
  letI : IsFractionRing (integralClosure A Omega) Omega :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Omega) <| by
      intro x hx
      exact hAinj (by simpa using hx)
  letI : FaithfulSMul A (integralClosure A Omega) :=
    (faithfulSMul_iff_algebraMap_injective A
      (integralClosure A Omega)).mpr <| by
        intro x y hxy
        apply hAinj
        exact congrArg Subtype.val hxy
  exact fg_maximal_formally
    A (integralClosure A Omega) K Omega E hEfg

/-- Corollary 7.52 in intrinsic form: under the Henselian DVR hypotheses and
a fixed local prolongation to the algebraic closure, a finite intermediate
field is unramified exactly when it lies in `K^un`. -/
theorem unramified_intermediate_maximal
    [IsDiscreteValuationRing A] [HenselianLocalRing A] [PerfectField K]
    [HenselianLocalRing (integralClosure A Omega)]
    [IsLocalHom (algebraMap A (integralClosure A Omega))]
    (E : IntermediateField K Omega) (hEfg : E.FG) :
    FUInterm A K Omega E ↔
      E ≤ maximalAlgebraicClosure A K Omega := by
  constructor
  · exact FUInterm.le_maximalUnramified A K Omega
  · intro hE
    obtain ⟨V, hV, hEV⟩ :=
      (fg_algebraic_closure
        A K Omega E hEfg).mp hE
    refine ⟨hEfg,
      intermediate_model_module A K Omega E hEfg, ?_⟩
    exact intermediate_model_formally
      A K Omega E hEfg V hV hEV

/-- Intrinsic form of Corollary 7.52, conditional only on the remaining
descent step for formal unramifiedness.  The module-finiteness part of that
descent is supplied by `intermediate_model_module`. -/
theorem intermediate_maximal_descent
    [IsIntegrallyClosed A] [IsNoetherianRing A] [PerfectField K]
    (E : IntermediateField K Omega) (hEfg : E.FG)
    (hdescent : ∀ V : Subalgebra A (integralClosure A Omega),
      FUSubalg A
          (integralClosure A Omega) V →
        E ≤ fractionFieldSubalgebra A
          (integralClosure A Omega) K Omega V →
        Algebra.FormallyUnramified A
          (intermediateIntegralModel A K Omega E)) :
    FUInterm A K Omega E ↔
      E ≤ maximalAlgebraicClosure A K Omega := by
  constructor
  · exact FUInterm.le_maximalUnramified A K Omega
  · intro hE
    refine ⟨hEfg, ?_⟩
    refine ⟨intermediate_model_module A K Omega E hEfg, ?_⟩
    obtain ⟨V, hV, hEV⟩ :=
      (fg_algebraic_closure
        A K Omega E hEfg).mp hE
    exact hdescent V hV hEV

end AlgebraicClosureMaximalUnramifiedField

end

end Towers.NumberTheory.Milne
