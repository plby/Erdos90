import Mathlib.NumberTheory.Divisors
import Mathlib.FieldTheory.Normal.Closure
import Submission.NumberTheory.Locals.FiniteExtensionClasses
import Submission.NumberTheory.Locals.FiniteFieldExample
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition


/-!
# Finite extension classes of fixed degree

This file records the finite-union argument in Milne's Remark 7.65.  Once an
extension of degree `n` is classified by an unramified degree `m ∣ n` and a
totally ramified class over that unramified field, finiteness for each fixed
`m` implies finiteness for degree `n`.
-/

namespace Submission.NumberTheory.Milne

open Set Valued

open scoped NNReal NormedField

/-- Milne, Remark 7.65, abstract finite-union step.  There are only finitely
many divisors `m` of `n`; hence a family of finite classification sets indexed
by those divisors has finite union. -/
theorem extension_classes_divisors
    {ExtensionClass : Type*} (n : ℕ)
    (classes : ℕ → Set ExtensionClass)
    (hfinite : ∀ m ∈ n.divisors, (classes m).Finite) :
    (⋃ m ∈ n.divisors, classes m).Finite := by
  exact Set.Finite.biUnion n.divisors.finite_toSet fun m hm ↦
    hfinite m hm

/-- Milne, Remark 7.65, applied to a specified set of degree-`n`
extensions.  If every such extension is obtained from one of the finite
totally ramified families indexed by a divisor `m ∣ n`, then the set of all
degree-`n` extension classes is finite. -/
theorem classes_fixed_degree
    {ExtensionClass : Type*} (n : ℕ)
    (allClasses : Set ExtensionClass)
    (classes : ℕ → Set ExtensionClass)
    (hfinite : ∀ m ∈ n.divisors, (classes m).Finite)
    (hcover : allClasses ⊆ ⋃ m ∈ n.divisors, classes m) :
    allClasses.Finite := by
  exact (extension_classes_divisors n classes hfinite).subset hcover

/-- Type-valued form of Remark 7.65: an exhaustive classification by the
finite totally ramified families over the finitely many unramified degrees
`m ∣ n` makes the type of degree-`n` extension classes finite. -/
theorem type_classes_degree
    {ExtensionClass : Type*} (n : ℕ)
    (classes : ℕ → Set ExtensionClass)
    (hfinite : ∀ m ∈ n.divisors, (classes m).Finite)
    (hcover : ∀ L : ExtensionClass, ∃ m ∈ n.divisors, L ∈ classes m) :
    Finite ExtensionClass := by
  rw [← Set.finite_univ_iff]
  apply classes_fixed_degree n Set.univ classes hfinite
  intro L _
  obtain ⟨m, hm, hL⟩ := hcover L
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, hL⟩⟩

/-- Milne, Remark 7.65, with the family cover constructed from the maximal
unramified degree.  Once every degree-`n` extension class is assigned its
unramified degree `m`, the divisibility `m ∣ n` puts it in one of the
finitely many divisor-indexed fibers. -/
theorem classes_fixed_unramified
    {ExtensionClass : Type*} (n : ℕ) (hn : n ≠ 0)
    (unramifiedDegree : ExtensionClass → ℕ)
    (hdegree_dvd : ∀ L, unramifiedDegree L ∣ n)
    (hfinite : ∀ m ∈ n.divisors,
      {L : ExtensionClass | unramifiedDegree L = m}.Finite) :
    Finite ExtensionClass := by
  rw [← Set.finite_univ_iff]
  let classes : ℕ → Set ExtensionClass :=
    fun m ↦ {L | unramifiedDegree L = m}
  apply classes_fixed_degree n Set.univ classes hfinite
  intro L _
  have hm : unramifiedDegree L ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨hdegree_dvd L, hn⟩
  exact Set.mem_iUnion.mpr ⟨unramifiedDegree L,
    Set.mem_iUnion.mpr ⟨hm, rfl⟩⟩

section EmbeddedLocalExtensions

universe u v

variable {K : Type u} {Omega : Type v}
  [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [CharZero K]
  [NormedField Omega] [NormedAlgebra K Omega]
  [Algebra.IsAlgebraic K Omega] [IsGalois K Omega] [IsAlgClosed Omega]

attribute [local instance] NormedField.toValued

/-- The local-field structures needed to apply Proposition 7.64 over an
embedded intermediate field `U`.  In Remark 7.65, `U` is the chosen
unramified extension of `K` of degree `m`.

These fields are bundled because the valuation and completeness structures
on a varying intermediate field are dependent data; they cannot be supplied
by ordinary theorem-level typeclass arguments indexed by `m`. -/
structure ILData (U : IntermediateField K Omega) where
  completeSpace : CompleteSpace U
  isUltrametricDist : IsUltrametricDist U
  norm_coe : ∀ r : U, ‖(r : Omega)‖ = ‖r‖
  rankOne :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    (Valued.v : Valuation U NNReal).RankOne
  valuationRingComplete :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    CompleteSpace 𝒪[U]
  valuationRingDVR :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    IsDiscreteValuationRing 𝒪[U]
  finiteResidueField :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    Finite (Valued.ResidueField U)
  algebraicAmbient : Algebra.IsAlgebraic U Omega
  galoisAmbient : IsGalois U Omega
  uniformizer :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    𝒪[U]
  uniformizer_irreducible :
    letI : IsUltrametricDist U := isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance isUltrametricDist
    Irreducible uniformizer

/-- The norm valuation on an embedded local field extends the base norm
valuation.  This is bundled through `ILData` so all
dependent integer-ring structures use the same valuation instance. -/
@[reducible]
def ILData.valuationHasExtension
    {U : IntermediateField K Omega} (data : ILData U) :
    letI : IsUltrametricDist U := data.isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance data.isUltrametricDist
    Valuation.HasExtension
      (@NormedField.valuation K inferInstance inferInstance)
      (@NormedField.valuation U inferInstance data.isUltrametricDist) := by
  letI : IsUltrametricDist U := data.isUltrametricDist
  letI : Valued U NNReal :=
    @NormedField.toValued U inferInstance data.isUltrametricDist
  exact ⟨fun x y ↦ by
    have hnorm (z : K) : ‖algebraMap K U z‖₊ = ‖z‖₊ := by
      apply NNReal.eq
      change ‖algebraMap K U z‖ = ‖z‖
      rw [← data.norm_coe]
      change ‖algebraMap K Omega z‖ = ‖z‖
      rw [norm_algebraMap, norm_one, mul_one]
    simp only [Valuation.comap_apply, NormedField.valuation_apply, hnorm]⟩

/-- The arithmetic assertion that an embedded local field is unramified of
residue degree `m`.  The local instances are installed from the accompanying
`ILData`. -/
def UnramifiedBaseDegree
    {U : IntermediateField K Omega} (m : ℕ)
    (data : ILData U) : Prop := by
  letI : IsUltrametricDist U := data.isUltrametricDist
  letI : Valued U NNReal :=
    @NormedField.toValued U inferInstance data.isUltrametricDist
  letI : Valuation.HasExtension
      (@NormedField.valuation K inferInstance inferInstance)
      (@NormedField.valuation U inferInstance data.isUltrametricDist) :=
    data.valuationHasExtension
  exact Algebra.FormallyUnramified 𝒪[K] 𝒪[U] ∧
    Module.finrank (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[U]) = m

/-- The additional arithmetic data saying that a selected embedded local
field is the unramified extension of degree `m`. -/
structure SelectedBaseData
    (m : ℕ) (U : IntermediateField K Omega)
    extends ILData U where
  finiteDimensional : FiniteDimensional K U
  normal : Normal K U
  valuationRingFinite :
    let data := toILData
    letI : IsUltrametricDist U := data.isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance data.isUltrametricDist
    letI : Valuation.HasExtension
        (@NormedField.valuation K inferInstance inferInstance)
        (@NormedField.valuation U inferInstance data.isUltrametricDist) :=
      data.valuationHasExtension
    Module.Finite (Valued.integer K) (Valued.integer U)
  valuationRingHenselian :
    let data := toILData
    letI : IsUltrametricDist U := data.isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance data.isUltrametricDist
    letI : Valuation.HasExtension
        (@NormedField.valuation K inferInstance inferInstance)
        (@NormedField.valuation U inferInstance data.isUltrametricDist) :=
      data.valuationHasExtension
    HenselianLocalRing (Valued.integer U)
  unramified :
    UnramifiedBaseDegree m toILData

/-- A totally ramified presentation over a varying intermediate local field.
The local instances are installed from `data` inside the predicate, avoiding
dependent typeclass obligations at every use site. -/
def TotallyDVRPresentation
    {U E : IntermediateField K Omega} (data : ILData U)
    (d : ℕ) (hUE : U ≤ E) : Prop :=
  letI : CompleteSpace U := data.completeSpace
  letI : IsUltrametricDist U := data.isUltrametricDist
  letI : Valued U NNReal :=
    @NormedField.toValued U inferInstance data.isUltrametricDist
  letI : (Valued.v : Valuation U NNReal).RankOne := data.rankOne
  letI : CompleteSpace 𝒪[U] := data.valuationRingComplete
  letI : IsDiscreteValuationRing 𝒪[U] := data.valuationRingDVR
  letI : Finite (Valued.ResidueField U) := data.finiteResidueField
  letI : NormedAlgebra U Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, data.norm_coe] }
  letI : Algebra.IsAlgebraic U Omega := data.algebraicAmbient
  letI : IsGalois U Omega := data.galoisAmbient
  Nonempty
    (@TotallyRamifiedDVR.{v, v, v} U inferInstance
      data.isUltrametricDist data.valuationRingDVR Omega inferInstance
      inferInstance d
      (IntermediateField.extendScalars (F := U) (E := E) hUE))

omit [CompleteSpace K] [IsUltrametricDist K] [Algebra.IsAlgebraic K Omega] [IsGalois K Omega] in
/-- Milne, Remark 7.65, assembled for actual embedded local extensions.

For every divisor `m` of the fixed degree `n`, choose the (canonical up to
`K`-isomorphism) unramified degree-`m` field `unramifiedBase m` inside the
ambient algebraic closure.  The cover hypothesis is now only the mathematical
decomposition from Corollary 7.51: every field under consideration contains
one chosen base and is totally ramified of degree `n / m` over it, expressed
by a `TotallyRamifiedDVR`.

Unlike the earlier abstract finite-union wrappers, no finiteness of the
divisor fibers is assumed.  It is proved internally from Proposition 7.64,
then transported back to `K` by restriction of scalars. -/
theorem embedded_extensions_degree
    (n : ℕ) (_hn : n ≠ 0)
    (allExtensions : Set (IntermediateField K Omega))
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ m ∈ n.divisors,
      ILData (unramifiedBase m))
    (hna : IsNonarchimedean (norm : Omega → ℝ))
    (hcover : ∀ E ∈ allExtensions,
      ∃ m, ∃ hm : m ∈ n.divisors, ∃ hUE : unramifiedBase m ≤ E,
        TotallyDVRPresentation
          (baseData m hm) (n / m - 1) hUE) :
    allExtensions.Finite := by
  let classes : ℕ → Set (IntermediateField K Omega) := fun m ↦
    {E | ∃ hm : m ∈ n.divisors, ∃ hUE : unramifiedBase m ≤ E,
      TotallyDVRPresentation
        (baseData m hm) (n / m - 1) hUE}
  have hfinite : ∀ m ∈ n.divisors, (classes m).Finite := by
    intro m hm
    let U := unramifiedBase m
    let data := baseData m hm
    letI : CompleteSpace U := data.completeSpace
    letI : IsUltrametricDist U := data.isUltrametricDist
    letI : Valued U NNReal :=
      @NormedField.toValued U inferInstance data.isUltrametricDist
    letI : (Valued.v : Valuation U NNReal).RankOne := data.rankOne
    letI : CompleteSpace 𝒪[U] := data.valuationRingComplete
    letI : IsDiscreteValuationRing 𝒪[U] := data.valuationRingDVR
    letI : Finite (Valued.ResidueField U) := data.finiteResidueField
    letI : NormedAlgebra U Omega :=
      { norm_smul_le := fun r x ↦ by
          rw [Algebra.smul_def, norm_mul,
            IntermediateField.algebraMap_apply, data.norm_coe] }
    letI : Algebra.IsAlgebraic U Omega := data.algebraicAmbient
    letI : IsGalois U Omega := data.galoisAmbient
    have hfields :
        {F : IntermediateField U Omega |
          Nonempty
            (@TotallyRamifiedDVR.{v, v, v} U inferInstance
              data.isUltrametricDist data.valuationRingDVR Omega inferInstance
              inferInstance (n / m - 1) F)}.Finite :=
      @totally_dvr_fields.{v, v, v} U inferInstance
        data.completeSpace data.isUltrametricDist data.rankOne
        data.valuationRingComplete data.valuationRingDVR
        data.finiteResidueField Omega inferInstance inferInstance
        data.algebraicAmbient data.galoisAmbient inferInstance inferInstance
        (n / m - 1) data.uniformizer data.uniformizer_irreducible hna
    apply (hfields.image fun F ↦ F.restrictScalars K).subset
    rintro E ⟨hm', hUE, hE⟩
    have hhm : hm' = hm := Subsingleton.elim _ _
    subst hm'
    change Nonempty
      (@TotallyRamifiedDVR.{v, v, v} U inferInstance
        data.isUltrametricDist data.valuationRingDVR Omega inferInstance
        inferInstance (n / m - 1)
        (IntermediateField.extendScalars (F := U) (E := E) hUE)) at hE
    refine ⟨IntermediateField.extendScalars
      (F := U) (E := E) hUE, hE, ?_⟩
    exact IntermediateField.extendScalars_restrictScalars hUE
  apply (extension_classes_divisors n classes hfinite).subset
  intro E hE
  obtain ⟨m, hm, hUE, hpresentation⟩ := hcover E hE
  exact Set.mem_iUnion.mpr ⟨m,
    Set.mem_iUnion.mpr ⟨hm, ⟨hm, hUE, hpresentation⟩⟩⟩

/-- The actual divisor-indexed family assembled in Remark 7.65.  Membership
already means that the field contains the selected unramified degree-`m`
stage and is totally ramified of degree `n / m` over it. -/
def decomposedEmbeddedExtensions
    (n : ℕ) (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ m ∈ n.divisors,
      ILData (unramifiedBase m)) :
    Set (IntermediateField K Omega) :=
  {E | ∃ m, ∃ hm : m ∈ n.divisors, ∃ hUE : unramifiedBase m ≤ E,
    TotallyDVRPresentation
      (baseData m hm) (n / m - 1) hUE}

omit [CompleteSpace K] [IsUltrametricDist K] [Algebra.IsAlgebraic K Omega] [IsGalois K Omega] in
/-- Remark 7.65 without a user-supplied cover: the type of embedded fields
equipped propositionally with the unramified/totally-ramified decomposition
is finite.  The finiteness of the totally ramified fibers is supplied
internally by Proposition 7.64. -/
theorem decomposed_embedded_extensions
    (n : ℕ) (hn : n ≠ 0)
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ m ∈ n.divisors,
      ILData (unramifiedBase m))
    (hna : IsNonarchimedean (norm : Omega → ℝ)) :
    (decomposedEmbeddedExtensions n unramifiedBase baseData).Finite := by
  apply embedded_extensions_degree n hn
    (decomposedEmbeddedExtensions n unramifiedBase baseData)
    unramifiedBase baseData hna
  intro E hE
  exact hE

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [Algebra.IsAlgebraic K Omega]
  [IsGalois K Omega] [IsAlgClosed Omega] in
/-- Embedded uniqueness for unramified bases.  If `F/K` is normal and is
`K`-isomorphic to a subfield `U` of `E`, then every such embedding into the
fixed algebraic closure has range `F`; hence the chosen field `F` itself is
contained in `E`.  This is the normality step that converts Proposition
7.50's uniqueness up to isomorphism into the literal containment needed in
Remark 7.65. -/
theorem intermediate_alg_equiv
    {F U E : IntermediateField K Omega}
    [Normal K F] (hUE : U ≤ E) (e : F ≃ₐ[K] U) : F ≤ E := by
  let j : F →ₐ[K] Omega := E.val.comp
    ((IntermediateField.inclusion hUE).comp e.toAlgHom)
  have hj : j.fieldRange = F := AlgHom.fieldRange_of_normal j
  rw [← hj]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact ((IntermediateField.inclusion hUE) (e y)).property

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [Algebra.IsAlgebraic K Omega]
  [IsGalois K Omega] [IsAlgClosed Omega] in
/-- Embedded uniqueness in its equality form.  A normal intermediate field
is the image of every one of its `K`-embeddings in the fixed algebraic
closure.  Thus a `K`-equivalence from it onto another embedded intermediate
field identifies the two fields literally, not merely up to isomorphism. -/
theorem intermediate_normal_alg
    {F U : IntermediateField K Omega}
    [Normal K F] (e : F ≃ₐ[K] U) : F = U := by
  let j : F →ₐ[K] Omega := U.val.comp e.toAlgHom
  have hjF : j.fieldRange = F := AlgHom.fieldRange_of_normal j
  have hjU : j.fieldRange = U := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact (e y).property
    · intro x hx
      let xU : U := ⟨x, hx⟩
      refine AlgHom.mem_fieldRange.mpr ⟨e.symm xU, ?_⟩
      change ((e (e.symm xU) : U) : Omega) = x
      rw [e.apply_symm_apply]
  exact hjF.symm.trans hjU

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] [Algebra.IsAlgebraic K Omega]
  [IsGalois K Omega] [IsAlgClosed Omega] in
/-- Proposition 7.50(b), specialized to embedded fraction fields.  An
isomorphism of the residue fields of two finite unramified DVR extensions
extends to their fraction fields; if the first fraction field is normal,
the two resulting subfields of the fixed algebraic closure are literally
equal.  This is the uniqueness step used to replace the maximal unramified
subfield of an extension by the selected degree-`m` base in Remark 7.65. -/
theorem intermediate_formally_unramified
    {A S T : Type*} {F U : IntermediateField K Omega}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    [HenselianLocalRing A] [HenselianLocalRing S] [HenselianLocalRing T]
    [Algebra A S] [Algebra A T]
    [IsLocalHom (algebraMap A S)] [IsLocalHom (algebraMap A T)]
    [Module.Finite A S] [Module.Finite A T]
    [Module.IsTorsionFree A S] [Module.IsTorsionFree A T]
    [Algebra.IsIntegral A S] [Algebra.IsIntegral A T]
    [Algebra.FormallyUnramified A S] [Algebra.FormallyUnramified A T]
    [FiniteDimensional (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S)]
    [FiniteDimensional (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField T)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField T)]
    [Algebra A K] [IsFractionRing A K]
    [Algebra S F] [IsFractionRing S F]
    [Algebra T U] [IsFractionRing T U]
    [Algebra A F] [Algebra A U]
    [IsScalarTower A S F] [IsScalarTower A T U]
    [IsScalarTower A K F] [IsScalarTower A K U]
    [Normal K F]
    (e : IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField T) :
    F = U := by
  obtain ⟨eFU⟩ :=
    nonempty_fraction_formally
      A S T K F U e
  exact intermediate_normal_alg eFU

section IntegralDVRModel

universe w

variable {K₀ : Type u} {U : Type v} {KU : Type v} {Omega' : Type w}
  [NontriviallyNormedField K₀] [CompleteSpace K₀] [IsUltrametricDist K₀]
  [NontriviallyNormedField KU] [CompleteSpace KU] [IsUltrametricDist KU]
  [(Valued.v : Valuation KU NNReal).RankOne]
  [CompleteSpace 𝒪[KU]] [IsDiscreteValuationRing 𝒪[KU]]
  [Finite (Valued.ResidueField KU)]
  [NormedAlgebra K₀ KU] [Algebra.IsAlgebraic K₀ KU]
  [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [Algebra 𝒪[K₀] U] [Algebra U KU] [IsFractionRing U KU]
  [IsScalarTower 𝒪[K₀] U KU] [Algebra.IsIntegral 𝒪[K₀] U]
  [NormedField Omega'] [NormedAlgebra KU Omega']
  [Algebra.IsAlgebraic KU Omega'] [IsGalois KU Omega'] [IsAlgClosed Omega']

attribute [local instance] NormedField.toValued

/-- A totally ramified presentation over an abstract integral DVR model of
the norm-defined integer ring of `KU`. -/
structure TotallyDVRModel
    (n : ℕ) (E : IntermediateField KU Omega') where
  B : Type w
  [commRing : CommRing B]
  [isDomain : IsDomain B]
  [discreteValuationRing : IsDiscreteValuationRing B]
  [algebra : Algebra U B]
  [moduleFinite : Module.Finite U B]
  [moduleTorsionFree : Module.IsTorsionFree U B]
  [fractionAlgebra : Algebra B E]
  [isFractionRing : IsFractionRing B E]
  [fractionBaseAlgebra : Algebra U E]
  [isScalarTower : IsScalarTower U B E]
  [scalarTowerFraction : IsScalarTower U KU E]
  [finiteDimensional : FiniteDimensional KU E]
  finrank_eq : Module.finrank KU E = n + 1
  totallyRamified :
    TotallyRamified U B (IsLocalRing.maximalIdeal U)

omit [CompleteSpace KU] [(Valued.v : Valuation KU NNReal).RankOne]
  [IsUltrametricDist KU]
  [CompleteSpace ↥𝒪[KU]] [IsDiscreteValuationRing ↥𝒪[KU]] [Finite 𝓀[KU]]
  [IsFractionRing U KU] [Algebra.IsAlgebraic KU Omega'] [IsGalois KU Omega']
  [IsAlgClosed Omega'] in
/-- Package the output of the maximal-unramified decomposition as the
integral-model presentation consumed by Proposition 7.64. -/
theorem totally_ramified_dvr
    {n : ℕ} {E : IntermediateField KU Omega'}
    {B : Type w} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra U B]
    [Module.Finite U B] [Module.IsTorsionFree U B]
    [Algebra B E] [IsFractionRing B E]
    [Algebra U E] [IsScalarTower U B E]
    [IsScalarTower U KU E] [FiniteDimensional KU E]
    (hfinrank : Module.finrank KU E = n + 1)
    (htotal : TotallyRamified U B (IsLocalRing.maximalIdeal U)) :
    Nonempty (TotallyDVRModel
      (U := U) n E) := by
  exact ⟨
    { B := B
      finrank_eq := hfinrank
      totallyRamified := htotal }⟩

set_option maxHeartbeats 1000000 in
-- Resolving the four fraction-field and valuation-ring towers is expensive.
include K₀ in
omit [CompleteSpace KU] in
omit [(Valued.v : Valuation KU NNReal).RankOne]
  [CompleteSpace ↥𝒪[KU]] [Finite 𝓀[KU]] [IsGalois KU Omega']
  [IsAlgClosed Omega'] in
/-- An abstract totally ramified integral-DVR presentation gives an
Eisenstein presentation over the norm-defined integer ring.  The model is
identified with `𝒪[KU]` by uniqueness of integral closure, and the
Eisenstein generator supplied by Proposition 7.55 is transported across
that equivalence. -/
theorem eisenstein_totally_model
    {n : ℕ} {E : IntermediateField KU Omega'}
    (hE : Nonempty (TotallyDVRModel
      (U := U) n E)) :
    EisensteinPresentedExtension n E := by
    obtain ⟨data⟩ := hE
    let B := data.B
    letI : CommRing B := data.commRing
    letI : IsDomain B := data.isDomain
    letI : IsDiscreteValuationRing B := data.discreteValuationRing
    letI : Algebra U B := data.algebra
    letI : Module.Finite U B := data.moduleFinite
    letI : Module.IsTorsionFree U B := data.moduleTorsionFree
    letI : Algebra B E := data.fractionAlgebra
    letI : IsFractionRing B E := data.isFractionRing
    letI : Algebra U E := data.fractionBaseAlgebra
    letI : IsScalarTower U B E := data.isScalarTower
    letI : IsScalarTower U KU E := data.scalarTowerFraction
    letI : FiniteDimensional KU E := data.finiteDimensional
    letI : Algebra 𝒪[KU] E :=
      ((algebraMap KU E).comp (algebraMap 𝒪[KU] KU)).toAlgebra
    letI : IsScalarTower 𝒪[KU] KU E :=
      IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨Pi, hPi⟩ := IsDiscreteValuationRing.exists_irreducible B
    let beta : E := algebraMap B E Pi
    let alpha : Omega' := beta
    let e : U ≃+* 𝒪[KU] := dvrValuedInteger K₀ U KU
    let f : Polynomial 𝒪[KU] := (minpoly U Pi).map e.toRingHom
    have heisU : (minpoly U Pi).IsEisensteinAt
        (IsLocalRing.maximalIdeal U) :=
      minpoly_eisenstein_ramified
        U B KU E data.totallyRamified Pi hPi
    have hfmonic : f.Monic := (minpoly.monic
      (Algebra.IsIntegral.isIntegral Pi)).map e.toRingHom
    have hfEis : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[KU]) := by
      change ((minpoly U Pi).map e.toRingHom).IsEisensteinAt _
      simpa using
        Submission.NumberTheory.Milne.Polynomial.IsEisensteinAt.map_rin
          heisU e
    have hbetaRoot : Polynomial.aeval beta f = 0 := by
      change Polynomial.aeval beta ((minpoly U Pi).map e.toRingHom) = 0
      rw [aeval_dvr_valued K₀ U KU]
      rw [← Polynomial.aeval_def]
      have hmin : minpoly U beta = minpoly U Pi :=
        minpoly.algebraMap_eq (IsFractionRing.injective B E) Pi
      rw [← hmin]
      exact minpoly.aeval U beta
    have hrootAlpha : Polynomial.aeval alpha f = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (algebraMap 𝒪[KU] Omega') (E.val beta) f = 0
      have hmap : algebraMap 𝒪[KU] Omega' =
          E.val.toRingHom.comp (algebraMap 𝒪[KU] E) := by
        ext r
        change algebraMap KU Omega' (r : KU) =
          E.val (algebraMap KU E (r : KU))
        rfl
      rw [hmap]
      calc
        Polynomial.eval₂
          (E.val.toRingHom.comp (algebraMap 𝒪[KU] E))
            (E.val beta) f =
            E.val (Polynomial.eval₂ (algebraMap 𝒪[KU] E) beta f) :=
          (Polynomial.hom_eval₂ f (algebraMap 𝒪[KU] E)
            E.val.toRingHom beta).symm
        _ = E.val (Polynomial.aeval beta f) := by
          rw [Polynomial.aeval_def]
        _ = 0 := by rw [hbetaRoot, map_zero]
    have hfdegree : f.natDegree = (minpoly U Pi).natDegree := by
      dsimp only [f]
      exact Polynomial.natDegree_map_eq_of_injective
        e.injective (minpoly U Pi)
    have hfield : IntermediateField.adjoin KU ({beta} : Set E) = ⊤ :=
      fraction_weakly_eisenstein
        U B KU E data.totallyRamified Pi hPi heisU.isWeaklyEisensteinAt
    have hPiInt : IsIntegral U Pi := Algebra.IsIntegral.isIntegral Pi
    have hpoly : (minpoly U Pi).map (algebraMap U KU) =
        minpoly KU beta := by
      exact (minpoly.isIntegrallyClosed_eq_field_fractions KU E hPiInt).symm
    have hbetaDegree : (minpoly KU beta).natDegree = Module.finrank KU E :=
      (Field.primitive_element_iff_minpoly_natDegree_eq KU beta).mp hfield
    have hfdegree' : f.natDegree = n + 1 := by
      calc
        f.natDegree = (minpoly U Pi).natDegree := hfdegree
        _ = ((minpoly U Pi).map (algebraMap U KU)).natDegree :=
          ((minpoly.monic hPiInt).natDegree_map (algebraMap U KU)).symm
        _ = (minpoly KU beta).natDegree := congrArg Polynomial.natDegree hpoly
        _ = Module.finrank KU E := hbetaDegree
        _ = n + 1 := data.finrank_eq
    have hE : E = IntermediateField.adjoin KU {alpha} := by
      have hmap := congrArg (fun F : IntermediateField KU E ↦ F.map E.val) hfield
      change (IntermediateField.adjoin KU {beta}).map E.val =
        (⊤ : IntermediateField KU E).map E.val at hmap
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val] at hmap
      simpa [IntermediateField.adjoin_map, beta, alpha] using hmap.symm
    have hrootMapped : Polynomial.aeval alpha
        (f.map (algebraMap 𝒪[KU] KU)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      exact hrootAlpha
    refine ⟨f, hfmonic, hfdegree', hfEis, alpha, ?_, hE⟩
    rw [Polynomial.mem_aroots]
    exact ⟨(hfmonic.map (algebraMap 𝒪[KU] KU)).ne_zero, hrootMapped⟩

include K₀ in
/-- Proposition 7.64 applied through an abstract integral DVR model. -/
theorem totally_model_fields
    [CharZero KU] (n : ℕ) (pi : 𝒪[KU]) (hpi : Irreducible pi)
    (hna : IsNonarchimedean (norm : Omega' → ℝ)) :
    {E : IntermediateField KU Omega' |
      Nonempty (TotallyDVRModel
        (U := U) n E)}.Finite := by
  apply (eisenstein_presented_fields n pi hpi hna).subset
  intro E hE
  exact
    eisenstein_totally_model
      (K₀ := K₀) (U := U) hE

end IntegralDVRModel

section AmbientIntegralModelTransport

variable {F E₀ : IntermediateField K Omega}
  {U B : Type v} {KU : IntermediateField K E₀}
  [CompleteSpace F] [isUltraF : IsUltrametricDist F]

local instance : Valued F NNReal :=
  @NormedField.toValued F inferInstance isUltraF

variable
  [rankOneF : (Valued.v : Valuation F NNReal).RankOne]
  [completeIntegersF : CompleteSpace 𝒪[F]]
  [dvrF : IsDiscreteValuationRing 𝒪[F]]
  [finiteResidueF : Finite (Valued.ResidueField F)]
  [FiniteDimensional K F]
  [Algebra.IsAlgebraic F Omega] [IsGalois F Omega]
  [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra 𝒪[K] U] [Algebra U B]
  [Algebra.IsIntegral 𝒪[K] U]
  [Module.Finite U B] [Module.IsTorsionFree U B]
  [Algebra B E₀] [IsFractionRing B E₀]
  [Algebra U KU] [IsFractionRing U KU] [Algebra U E₀]
  [Algebra 𝒪[K] KU]
  [IsScalarTower 𝒪[K] U KU]
  [IsScalarTower 𝒪[K] K KU]
  [IsScalarTower U B E₀] [IsScalarTower U KU E₀]
  [FiniteDimensional K E₀]

set_option maxHeartbeats 1000000 in
-- Resolving the canonical fraction-field and embedded scalar towers is expensive.
set_option synthInstance.maxHeartbeats 100000 in
-- The same towers require a larger local typeclass-search budget.
omit [CharZero K] [Algebra.IsAlgebraic K Omega] [IsGalois K Omega]
  [CompleteSpace ↥F] [IsAlgClosed Omega] rankOneF completeIntegersF
  finiteResidueF [IsGalois F Omega] in
/-- Transport an abstract integral-model presentation from its canonical
fraction field `KU ⊆ E₀` to the literally equal selected embedded base
`F = KU.map E₀.val`.  The algebra structures are defined through the
ambient inclusions, so the two scalar towers agree. -/
theorem totally_transport_selected
    (hEq : F = KU.map E₀.val)
    (hnorm : ∀ r : F, ‖(r : Omega)‖ = ‖r‖)
    (htotal : TotallyRamified U B (IsLocalRing.maximalIdeal U)) :
    ∃ hFE : F ≤ E₀,
      ∃ algUF : Algebra U F,
      letI : Algebra U F := algUF
      ∃ hfrac : IsFractionRing U F,
      ∃ htower : IsScalarTower (Valued.integer K) U F,
      letI : NormedAlgebra F Omega :=
        { norm_smul_le := fun r x ↦ by
            rw [Algebra.smul_def, norm_mul,
              IntermediateField.algebraMap_apply, hnorm] }
      @EisensteinPresentedExtension F inferInstance isUltraF dvrF
        Omega inferInstance inferInstance
        (Module.finrank F
          (IntermediateField.extendScalars (F := F) (E := E₀) hFE) - 1)
        (IntermediateField.extendScalars (F := F) (E := E₀) hFE) := by
  let hmapE : KU.map E₀.val ≤ E₀ := by
    intro x hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  let hFE : F ≤ E₀ := hEq.le.trans hmapE
  let eKUF : KU ≃ₐ[K] F :=
    (IntermediateField.equivMap KU E₀.val).trans
      (IntermediateField.equivOfEq hEq.symm)
  let algUF : Algebra U F :=
    (eKUF.toRingHom.comp (algebraMap U KU)).toAlgebra
  refine ⟨hFE, algUF, ?_⟩
  letI : Algebra U F := algUF
  let eUKUF : KU ≃ₐ[U] F :=
    { eKUF with commutes' := fun _ ↦ rfl }
  let hfrac : IsFractionRing U F :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors U) eUKUF
  letI : IsFractionRing U F := hfrac
  let htower : IsScalarTower (Valued.integer K) U F :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro a
      change algebraMap K F (algebraMap (Valued.integer K) K a) =
        eKUF (algebraMap U KU (algebraMap (Valued.integer K) U a))
      rw [← IsScalarTower.algebraMap_apply (Valued.integer K) U KU]
      rw [IsScalarTower.algebraMap_apply (Valued.integer K) K KU]
      exact (eKUF.commutes (algebraMap (Valued.integer K) K a)).symm
  letI : IsScalarTower (Valued.integer K) U F := htower
  refine ⟨hfrac, htower, ?_⟩
  letI : NormedAlgebra F Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, hnorm] }
  let EF := IntermediateField.extendScalars (F := F) (E := E₀) hFE
  let eE : E₀ ≃+* EF :=
    { toFun := fun x ↦ ⟨x, x.property⟩
      invFun := fun x ↦ ⟨x, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let algBEF : Algebra B EF :=
    (eE.toRingHom.comp (algebraMap B E₀)).toAlgebra
  letI : SMul B EF := algBEF.toSMul
  letI : Algebra B EF := algBEF
  let eBE : E₀ ≃ₐ[B] EF :=
    { eE with commutes' := fun _ ↦ rfl }
  letI : IsFractionRing B EF :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors B) eBE
  let algUEF : Algebra U EF :=
    ((algebraMap B EF).comp (algebraMap U B)).toAlgebra
  letI : SMul U EF := algUEF.toSMul
  letI : Algebra U EF := algUEF
  letI : IsScalarTower U B EF := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U F EF := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    dsimp [algUEF, algUF, algBEF, eKUF, eE]
    exact congrArg E₀.val
      ((IsScalarTower.algebraMap_apply U B E₀ u).symm.trans
        (IsScalarTower.algebraMap_apply U KU E₀ u))
  letI : Algebra.EssFiniteType K E₀ := inferInstance
  have hEfg : E₀.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  have hEFfg : (EF : IntermediateField F Omega).FG := by
    apply IntermediateField.FG.of_restrictScalars (K := K)
    simpa [EF] using hEfg
  letI : Algebra.EssFiniteType F EF :=
    IntermediateField.essFiniteType_iff.mpr hEFfg
  letI : Module.Finite F EF :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : IsUltrametricDist F := isUltraF
  letI : IsDiscreteValuationRing (Valued.integer F) := dvrF
  have hpos : 0 < Module.finrank F EF := Module.finrank_pos
  let hpresentation : Nonempty (TotallyDVRModel
      (U := U) (Module.finrank F EF - 1) EF) := ⟨
    { B := B
      finrank_eq := (Nat.sub_add_cancel hpos).symm
      totallyRamified := htotal }⟩
  exact eisenstein_totally_model
    (K₀ := K) (U := U) (KU := F) (Omega' := Omega)
    (E := EF) hpresentation

end AmbientIntegralModelTransport

end EmbeddedLocalExtensions

section ArbitraryFiniteExtensionDecomposition

universe u v

variable {K : Type u} {Omega : Type v}
  [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [CharZero K]
  [NontriviallyNormedField Omega] [NormedAlgebra K Omega]
  [Algebra.IsAlgebraic K Omega] [IsGalois K Omega] [IsAlgClosed Omega]

attribute [local instance] NormedField.toValued

variable [IsDiscreteValuationRing (Valued.integer K)]
  [Finite (Valued.ResidueField K)]

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
set_option synthInstance.maxHeartbeats 100000 in
omit [IsGalois K Omega] in
/-- Proposition 7.50 and Example 7.54 supply the selected unramified base
needed in Remark 7.65 inside the chosen valued algebraic closure.

The degree-`m` finite residue extension is lifted inside `𝒪[Omega]`.  The
abstract finite unramified DVR produced by the lift is identified with the
norm-defined integer ring of its embedded fraction field, so all local-field
data required by Proposition 7.64 is obtained without a compatibility
hypothesis. -/
theorem selected_base_data
    (m : ℕ) (hm : 0 < m) :
    ∃ F : IntermediateField K Omega,
      Nonempty (SelectedBaseData m F) := by
  letI : IsUltrametricDist Omega := IsUltrametricDist.of_normedAlgebra K
  letI : Valuation.HasExtension
      (NormedField.valuation (K := K))
      (NormedField.valuation (K := Omega)) :=
    valuation_normed_algebra K Omega
  let A := Valued.integer K
  let B := Valued.integer Omega
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    valued_integer_complete K
  letI : HenselianLocalRing A := valued_henselian_ring K
  letI : HenselianLocalRing B :=
    valued_henselian_closed Omega
  letI : Algebra.IsIntegral A B := by
    letI : IsIntegralClosure B A Omega :=
      valued_integer_closure K Omega
    exact IsIntegralClosure.isIntegral_algebra A Omega
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A B)
  letI : IsAlgClosure (Valued.ResidueField K) (Valued.ResidueField Omega) :=
    residue_valued_closure K Omega
  let p := ringChar (Valued.ResidueField K)
  letI : Fact p.Prime :=
    ⟨CharP.char_is_prime (Valued.ResidueField K) p⟩
  letI : CharP (Valued.ResidueField K) p := ringChar.charP _
  letI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨U, hUfinite, hUunramified, hdegree, hUgalois,
      _hUcyclic, _hsplits⟩ :=
    unramified_intermediate_cyclic
      (p := p) (n := m) A B K Omega
  letI : Module.Finite A U := hUfinite
  letI : Algebra.FormallyUnramified A U := hUunramified
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalRing U := subalgebra_ring_integral A B U
  letI : IsDedekindDomainDvr U :=
    isDedekindDomainDvr.of_formallyUnramified A U
  have hmax : IsLocalRing.maximalIdeal U ≠ ⊥ := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := U)]
    exact (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective A U)).not.mpr
        (IsDiscreteValuationRing.not_a_field A)
  letI : IsDiscreteValuationRing U :=
    ((IsDiscreteValuationRing.TFAE U
      (IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmax)).out 2 0).mp
        (inferInstance : IsDedekindDomain U)
  let F := fractionFieldSubalgebra A B K Omega U
  let algUF : Algebra U F :=
    fractionIntermediateSubalgebra A B K Omega U
  letI : SMul U F := algUF.toSMul
  letI : Algebra U F := algUF
  letI : IsFractionRing U F :=
    fraction_intermediate_subalgebra A B K Omega U
  letI : IsScalarTower A U F := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap A Omega a = algebraMap B Omega (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B Omega a
  letI : Module.Finite K F := by
    apply Module.Finite.of_isLocalization A U (nonZeroDivisors A)
  letI : FiniteDimensional K F := by infer_instance
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : IsGalois K F := hUgalois
  let nontriviallyNormedFieldF : NontriviallyNormedField F :=
    { __ := SubfieldClass.toNormedField F
      non_trivial := by
        obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial K _
        use algebraMap K F k
        change 1 < ‖algebraMap K Omega k‖
        simpa only [norm_algebraMap'] using hk }
  letI : NontriviallyNormedField F := nontriviallyNormedFieldF
  letI : NormedAlgebra K F :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def]
        change ‖algebraMap K Omega r * (x : Omega)‖ ≤
          ‖r‖ * ‖(x : Omega)‖
        rw [norm_mul, norm_algebraMap'] }
  letI : IsUniformAddGroup F :=
    F.toSubalgebra.toSubmodule.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace F := FiniteDimensional.complete K F
  let isUltraF : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist F := isUltraF
  letI : Valued F NNReal :=
    @NormedField.toValued F inferInstance isUltraF
  letI : (Valued.v : Valuation F NNReal).RankOne :=
    @NormedField.instRankOneNNRealValuation F inferInstance isUltraF
  letI : Valuation.HasExtension
      (@NormedField.valuation K inferInstance inferInstance)
      (@NormedField.valuation F inferInstance isUltraF) :=
    valuation_normed_algebra K F
  letI : Module.Finite (Valued.integer K) (Valued.integer F) :=
    @valued_integer_module K F
      inferInstance inferInstance inferInstance inferInstance isUltraF
      inferInstance inferInstance inferInstance inferInstance
  letI : IsDiscreteValuationRing (Valued.integer F) :=
    @valued_discrete_valuation K F
      inferInstance inferInstance inferInstance inferInstance isUltraF
      inferInstance inferInstance inferInstance inferInstance
  have hclosedF : IsClosed (Valued.integer F : Set F) := by
    rw [show (Valued.integer F : Set F) = {x | ‖x‖ ≤ 1} by
      ext x
      simp [Valued.integer.mem_iff]]
    exact isClosed_le continuous_norm continuous_const
  letI : IsUniformAddGroup (Valued.integer F) :=
    (Valued.integer F).toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace (Valued.integer F) := hclosedF.completeSpace_coe
  letI : HenselianLocalRing (Valued.integer F) :=
    @valued_henselian_extension K F
      inferInstance inferInstance inferInstance inferInstance isUltraF
      inferInstance inferInstance inferInstance inferInstance
  letI : Finite (Valued.ResidueField F) :=
    Module.finite_of_finite (Valued.ResidueField K)
  let eRing : U ≃+* Valued.integer F :=
    @dvrValuedInteger K U F
      inferInstance inferInstance inferInstance inferInstance isUltraF
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
  have hcoeRing (u : U) : ((eRing u : Valued.integer F) : F) =
      algebraMap U F u := by
    dsimp only [eRing]
    exact @coe_dvr_valued K U F
      inferInstance inferInstance inferInstance inferInstance isUltraF
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance u
  let eUF : U ≃ₐ[A] Valued.integer F :=
    { eRing with
      commutes' := fun a ↦ by
        apply Subtype.ext
        calc
          ((eRing (algebraMap A U a) : Valued.integer F) : F) =
              algebraMap U F (algebraMap A U a) :=
            hcoeRing _
          _ = algebraMap A F a :=
            (IsScalarTower.algebraMap_apply A U F a).symm
          _ = algebraMap (Valued.integer F) F
              (algebraMap A (Valued.integer F) a) :=
            IsScalarTower.algebraMap_apply A (Valued.integer F) F a }
  letI : Algebra.FormallyUnramified A (Valued.integer F) :=
    Algebra.FormallyUnramified.of_equiv eUF
  have hresidueDegree : Module.finrank (Valued.ResidueField K)
      (Valued.ResidueField F) = m := by
    rw [← formally_unramified_fraction
      A (Valued.integer F) K F]
    exact hdegree
  let pi : Valued.integer F :=
    Classical.choose (IsDiscreteValuationRing.exists_irreducible
      (Valued.integer F))
  have hpi : Irreducible pi :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
      (Valued.integer F))
  let data : ILData F :=
    { completeSpace := inferInstance
      isUltrametricDist := inferInstance
      norm_coe := fun _ ↦ rfl
      rankOne := inferInstance
      valuationRingComplete := inferInstance
      valuationRingDVR := inferInstance
      finiteResidueField := inferInstance
      algebraicAmbient := inferInstance
      galoisAmbient := by
        letI : Normal F Omega := normal_iff.mpr fun x ↦
          ⟨Algebra.IsAlgebraic.isIntegral.isIntegral x,
            IsAlgClosed.splits _⟩
        exact IsGalois.mk
      uniformizer := pi
      uniformizer_irreducible := hpi }
  refine ⟨F, ⟨{
    toILData := data
    finiteDimensional := inferInstance
    normal := inferInstance
    valuationRingFinite := inferInstance
    valuationRingHenselian := inferInstance
    unramified := ?_ }⟩⟩
  exact ⟨inferInstance, hresidueDegree⟩

/-- An opaque copy of a finite extension, used to install its canonical
spectral norm without colliding with the metric inherited by an embedded
intermediate field. -/
@[irreducible] def ExtensionSpectralCopy (E : Type*) := E

/-- The underlying equivalence from the spectral copy. -/
def extensionSpectralCopy (E : Type*) :
    ExtensionSpectralCopy E ≃ E := by
  rw [ExtensionSpectralCopy]

set_option maxHeartbeats 1000000 in
-- The arbitrary embedded extension requires several dependent valuation-ring towers.
set_option synthInstance.maxHeartbeats 100000 in
-- The same construction requires a larger local typeclass-search budget.
omit [IsGalois K Omega] [IsAlgClosed Omega] in
/-- The maximal-unramified construction supplies the divisor-indexed
Eisenstein presentation required in Remark 7.65 for an arbitrary embedded
finite extension.  Proposition 7.50 identifies the canonical fraction field
of the maximal unramified integral subalgebra with the selected normal
unramified base of the same residue degree. -/
theorem selected_eisenstein_presentation
    (n : ℕ) (E : IntermediateField K Omega)
    [FiniteDimensional K E]
    (hdegree : Module.finrank K E = n)
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ m ∈ n.divisors,
      SelectedBaseData m (unramifiedBase m)) :
    ∃ m, ∃ hm : m ∈ n.divisors, ∃ hFE : unramifiedBase m ≤ E,
      let F := unramifiedBase m
      let data := (baseData m hm).toILData
      letI : CompleteSpace F := data.completeSpace
      letI : IsUltrametricDist F := data.isUltrametricDist
      letI : Valued F NNReal :=
        @NormedField.toValued F inferInstance data.isUltrametricDist
      letI : (Valued.v : Valuation F NNReal).RankOne := data.rankOne
      letI : CompleteSpace (Valued.integer F) := data.valuationRingComplete
      letI : IsDiscreteValuationRing (Valued.integer F) := data.valuationRingDVR
      letI : Finite (Valued.ResidueField F) := data.finiteResidueField
      letI : NormedAlgebra F Omega :=
        { norm_smul_le := fun r x ↦ by
            rw [Algebra.smul_def, norm_mul,
              IntermediateField.algebraMap_apply, data.norm_coe] }
      letI : Algebra.IsAlgebraic F Omega := data.algebraicAmbient
      letI : IsGalois F Omega := data.galoisAmbient
      @EisensteinPresentedExtension F inferInstance
        data.isUltrametricDist data.valuationRingDVR Omega inferInstance
        inferInstance (n / m - 1)
          (IntermediateField.extendScalars (F := F) (E := E) hFE) := by
  let L := ExtensionSpectralCopy E
  let e : L ≃ E := extensionSpectralCopy E
  letI : Field L := Equiv.field e
  letI : Algebra K L := Equiv.algebra K e
  let ealg : L ≃ₐ[K] E := Equiv.algEquiv K e
  letI : FiniteDimensional K L :=
    ealg.symm.toLinearEquiv.finiteDimensional
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : CompleteSpace L := FiniteDimensional.complete K L
  letI : Valuation.HasExtension
      (NormedField.valuation (K := K))
      (NormedField.valuation (K := L)) :=
    valuation_normed_algebra K L
  let B := Valued.integer L
  letI : Module.Finite (Valued.integer K) B := valued_integer_module K L
  letI : IsDiscreteValuationRing B :=
    valued_discrete_valuation K L
  letI : HenselianLocalRing (Valued.integer K) := valued_henselian_ring K
  letI : HenselianLocalRing B :=
    valued_henselian_extension K L
  let algBE : Algebra B E :=
    (ealg.toRingHom.comp (algebraMap B L)).toAlgebra
  letI : Algebra B E := algBE
  let eBE : L ≃ₐ[B] E :=
    { ealg with commutes' := fun _ ↦ rfl }
  letI : IsFractionRing B E :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors B) eBE
  letI : Module.IsTorsionFree (Valued.integer K) B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (Valued.integer K) B)
  letI : Algebra.IsIntegral (Valued.integer K) B := Algebra.IsIntegral.of_finite _ _
  letI : IsLocalHom (algebraMap (Valued.integer K) B) :=
    Algebra.IsIntegral.isLocalHom (Valued.integer K) B
  letI : IsScalarTower (Valued.integer K) B E :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro a
      change algebraMap (Valued.integer K) E a =
        ealg (algebraMap B L (algebraMap (Valued.integer K) B a))
      rw [← IsScalarTower.algebraMap_apply (Valued.integer K) B L]
      rw [IsScalarTower.algebraMap_apply (Valued.integer K) K L]
      rw [ealg.commutes]
      exact (IsScalarTower.algebraMap_apply (Valued.integer K) K E a).symm
  let U := maximalUnramifiedSubalgebra (Valued.integer K) B
  letI : Module.Finite (Valued.integer K) U :=
    maximal_subalgebra_finite (Valued.integer K) B
  letI : IsLocalRing U :=
    maximal_subalgebra_ring (Valued.integer K) B
  letI : IsDiscreteValuationRing U :=
    subalgebra_discrete_valuation (Valued.integer K) B
  letI : Algebra.FormallyUnramified (Valued.integer K) U :=
    maximal_subalgebra_formally (Valued.integer K) B
  let KU := fractionFieldSubalgebra (Valued.integer K) B K E U
  let algUKU : Algebra U KU :=
    fractionIntermediateSubalgebra (Valued.integer K) B K E U
  letI : SMul U KU := algUKU.toSMul
  letI : Algebra U KU := algUKU
  letI : IsFractionRing U KU :=
    fraction_intermediate_subalgebra (Valued.integer K) B K E U
  let m := Module.finrank K KU
  letI : Module.IsTorsionFree (Valued.integer K) U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (Valued.integer K) U)
  letI : Algebra.IsIntegral (Valued.integer K) U :=
    Algebra.IsIntegral.of_finite _ _
  letI : IsLocalHom (algebraMap (Valued.integer K) U) :=
    Algebra.IsIntegral.isLocalHom (Valued.integer K) U
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (Valued.integer K)) (Valued.integer K) :=
    valued_integer_complete K
  letI : HenselianLocalRing U :=
    henselian_formally_unramified
      (Valued.integer K) U
  letI : Module.IsTorsionFree U B := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    exact Subtype.val_injective
  letI : Module.Finite U B :=
    Module.Finite.of_restrictScalars_finite (Valued.integer K) U B
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.of_finite U B
  letI : Algebra U E :=
    ((algebraMap B E).comp (algebraMap U B)).toAlgebra
  let hUBE : IsScalarTower U B E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U B E := hUBE
  let hUKUE : IsScalarTower U KU E := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    rfl
  letI : IsScalarTower U KU E := hUKUE
  letI : IsScalarTower (Valued.integer K) U KU :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro a
      apply KU.val.injective
      change algebraMap (Valued.integer K) E a =
        algebraMap B E (algebraMap (Valued.integer K) B a)
      exact IsScalarTower.algebraMap_apply (Valued.integer K) B E a
  letI : IsScalarTower (Valued.integer K) K KU :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext a
      rfl
  have hdecomp :
      TotallyRamified U B (IsLocalRing.maximalIdeal U) ∧
        Module.finrank K KU ∣ Module.finrank K E :=
    maximal_subalgebra_decomposition
      (Valued.integer K) B K KU E
  have hmdvd : m ∣ n := by
    rw [← hdegree]
    exact hdecomp.2
  have hn0 : n ≠ 0 := by
    rw [← hdegree]
    exact Module.finrank_pos.ne'
  have hm : m ∈ n.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hn0⟩
  let algUB' : Algebra U B := inferInstance
  letI : SMul U B := algUB'.toSMul
  letI : Algebra U B := algUB'
  let algUE' : Algebra U E :=
    ((algebraMap B E).comp (algebraMap U B)).toAlgebra
  letI : SMul U E := algUE'.toSMul
  letI : Algebra U E := algUE'
  letI : IsScalarTower U B E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U KU E := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    rfl
  let F := unramifiedBase m
  let selected := baseData m hm
  let data := selected.toILData
  letI : CompleteSpace F := data.completeSpace
  letI : IsUltrametricDist F := data.isUltrametricDist
  letI : Valued F NNReal :=
    @NormedField.toValued F inferInstance data.isUltrametricDist
  letI : (Valued.v : Valuation F NNReal).RankOne := data.rankOne
  letI : CompleteSpace (Valued.integer F) := data.valuationRingComplete
  letI : IsDiscreteValuationRing (Valued.integer F) := data.valuationRingDVR
  letI : Finite (Valued.ResidueField F) := data.finiteResidueField
  letI : NormedAlgebra F Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, data.norm_coe] }
  letI : Algebra.IsAlgebraic F Omega := data.algebraicAmbient
  letI : IsGalois F Omega := data.galoisAmbient
  letI : FiniteDimensional K F := selected.finiteDimensional
  letI : Normal K F := selected.normal
  letI : Valuation.HasExtension
      (@NormedField.valuation K inferInstance inferInstance)
      (@NormedField.valuation F inferInstance data.isUltrametricDist) :=
    data.valuationHasExtension
  letI : Module.Finite (Valued.integer K) (Valued.integer F) :=
    selected.valuationRingFinite
  letI : HenselianLocalRing (Valued.integer F) :=
    selected.valuationRingHenselian
  letI : Module.IsTorsionFree (Valued.integer K) (Valued.integer F) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K F).injective
      have hxyF := congrArg (fun z : Valued.integer F => (z : F)) hxy
      exact hxyF)
  letI : Algebra.IsIntegral (Valued.integer K) (Valued.integer F) :=
    Algebra.IsIntegral.of_finite _ _
  letI : IsLocalHom
      (algebraMap (Valued.integer K) (Valued.integer F)) :=
    Algebra.IsIntegral.isLocalHom (Valued.integer K) (Valued.integer F)
  have hselected := selected.unramified
  change Algebra.FormallyUnramified
      (Valued.integer K) (Valued.integer F) ∧
    Module.finrank (Valued.ResidueField K) (Valued.ResidueField F) = m
      at hselected
  letI : Algebra.FormallyUnramified
      (Valued.integer K) (Valued.integer F) := hselected.1
  have hresU : Module.finrank (Valued.ResidueField K)
      (IsLocalRing.ResidueField U) = m := by
    rw [← formally_unramified_fraction
      (Valued.integer K) U K KU]
  let p := ringChar (Valued.ResidueField K)
  letI : Fact p.Prime :=
    ⟨CharP.char_is_prime (Valued.ResidueField K) p⟩
  obtain ⟨eFU⟩ :=
    nonempty_formally_finrank
      (Valued.integer K) (Valued.integer F) U p
        (hselected.2.trans hresU.symm)
  let eField : F ≃ₐ[K] KU :=
    IsFractionRing.fieldEquivOfAlgEquiv K F KU eFU
  let eMap : F ≃ₐ[K] KU.map E.val :=
    eField.trans (IntermediateField.equivMap KU E.val)
  have hEq : F = KU.map E.val :=
    intermediate_normal_alg eMap
  obtain ⟨hFE, algUF, hfrac, htower, heis⟩ :=
    totally_transport_selected
      (K := K) (Omega := Omega) (F := F) (E₀ := E)
      (U := U) (B := B) (KU := KU) hEq data.norm_coe hdecomp.1
  refine ⟨m, hm, hFE, ?_⟩
  letI : Algebra U F := algUF
  letI : IsFractionRing U F := hfrac
  letI : IsScalarTower (Valued.integer K) U F := htower
  let EF := IntermediateField.extendScalars (F := F) (E := E) hFE
  letI : Algebra.EssFiniteType K E := inferInstance
  have hEfg : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  have hEFfg : (EF : IntermediateField F Omega).FG := by
    apply IntermediateField.FG.of_restrictScalars (K := K)
    simpa [EF] using hEfg
  letI : Algebra.EssFiniteType F EF :=
    IntermediateField.essFiniteType_iff.mpr hEFfg
  letI : Module.Finite F EF :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hFdegree : Module.finrank K F = m := by
    calc
      Module.finrank K F = Module.finrank (Valued.ResidueField K)
          (Valued.ResidueField F) :=
        formally_unramified_fraction
          (Valued.integer K) (Valued.integer F) K F
      _ = m := hselected.2
  have hKE : Module.finrank K EF = n := by
    change Module.finrank K (EF.restrictScalars K) = n
    rw [IntermediateField.extendScalars_restrictScalars hFE, hdegree]
  have hEFdegree : Module.finrank F EF = n / m := by
    apply Nat.eq_div_of_mul_eq_left Module.finrank_pos.ne'
    calc
      Module.finrank F EF * m =
          Module.finrank K F * Module.finrank F EF := by
        rw [hFdegree]
        exact Nat.mul_comm _ _
      _ = Module.finrank K EF :=
        Module.finrank_mul_finrank K F EF
      _ = n := hKE
  rw [hEFdegree] at heis
  exact heis

/-- The degree-`m` Eisenstein family over a selected unramified base, viewed
again as intermediate fields over `K`. -/
def selectedEisensteinFields
    (n m : ℕ) (hm : m ∈ n.divisors)
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ d ∈ n.divisors,
      SelectedBaseData d (unramifiedBase d)) :
    Set (IntermediateField K Omega) := by
  let F := unramifiedBase m
  let data := (baseData m hm).toILData
  letI : CompleteSpace F := data.completeSpace
  letI : IsUltrametricDist F := data.isUltrametricDist
  letI : Valued F NNReal :=
    @NormedField.toValued F inferInstance data.isUltrametricDist
  letI : (Valued.v : Valuation F NNReal).RankOne := data.rankOne
  letI : CompleteSpace (Valued.integer F) := data.valuationRingComplete
  letI : IsDiscreteValuationRing (Valued.integer F) := data.valuationRingDVR
  letI : Finite (Valued.ResidueField F) := data.finiteResidueField
  letI : NormedAlgebra F Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, data.norm_coe] }
  letI : Algebra.IsAlgebraic F Omega := data.algebraicAmbient
  letI : IsGalois F Omega := data.galoisAmbient
  exact (fun EF : IntermediateField F Omega ↦ EF.restrictScalars K) ''
    {EF | @EisensteinPresentedExtension F inferInstance
      data.isUltrametricDist data.valuationRingDVR Omega inferInstance
      inferInstance (n / m - 1) EF}

omit [CompleteSpace K] [CharZero K] [IsGalois K Omega] [IsDiscreteValuationRing ↥𝒪[K]]
  [Finite 𝓀[K]] in
/-- Each selected-base Eisenstein family is finite by Proposition 7.64. -/
theorem selected_eisenstein_fields
    (n m : ℕ) (hm : m ∈ n.divisors)
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ d ∈ n.divisors,
      SelectedBaseData d (unramifiedBase d))
    (hna : IsNonarchimedean (norm : Omega → ℝ)) :
    (selectedEisensteinFields
      n m hm unramifiedBase baseData).Finite := by
  let F := unramifiedBase m
  let data := (baseData m hm).toILData
  letI : CompleteSpace F := data.completeSpace
  letI : IsUltrametricDist F := data.isUltrametricDist
  letI : Valued F NNReal :=
    @NormedField.toValued F inferInstance data.isUltrametricDist
  letI : (Valued.v : Valuation F NNReal).RankOne := data.rankOne
  letI : CompleteSpace (Valued.integer F) := data.valuationRingComplete
  letI : IsDiscreteValuationRing (Valued.integer F) := data.valuationRingDVR
  letI : Finite (Valued.ResidueField F) := data.finiteResidueField
  letI : NormedAlgebra F Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, data.norm_coe] }
  letI : Algebra.IsAlgebraic F Omega := data.algebraicAmbient
  letI : IsGalois F Omega := data.galoisAmbient
  change ((fun EF : IntermediateField F Omega ↦ EF.restrictScalars K) ''
    {EF | @EisensteinPresentedExtension F inferInstance
      data.isUltrametricDist data.valuationRingDVR Omega inferInstance
      inferInstance (n / m - 1) EF}).Finite
  exact (@eisenstein_presented_fields F inferInstance
    data.completeSpace data.isUltrametricDist data.rankOne
    data.valuationRingComplete data.valuationRingDVR data.finiteResidueField
    Omega inferInstance inferInstance data.algebraicAmbient
    data.galoisAmbient inferInstance (n / m - 1) data.uniformizer
    data.uniformizer_irreducible hna).image _

omit [IsGalois K Omega] in
/-- Milne, Remark 7.65: inside a fixed algebraic closure, there are only
finitely many local extensions of a prescribed positive degree.  The
maximal-unramified construction places every such extension in one of the
finitely many Eisenstein families indexed by a divisor of the degree. -/
theorem embedded_extensions_fixed
    (n : ℕ) (hn : n ≠ 0)
    (unramifiedBase : ℕ → IntermediateField K Omega)
    (baseData : ∀ m ∈ n.divisors,
      SelectedBaseData m (unramifiedBase m))
    (hna : IsNonarchimedean (norm : Omega → ℝ)) :
    {E : IntermediateField K Omega | Module.finrank K E = n}.Finite := by
  let classes : ℕ → Set (IntermediateField K Omega) := fun m ↦
    {E | ∃ hm : m ∈ n.divisors,
      E ∈ selectedEisensteinFields
        n m hm unramifiedBase baseData}
  have hfinite : ∀ m ∈ n.divisors, (classes m).Finite := by
    intro m hm
    apply (selected_eisenstein_fields
      n m hm unramifiedBase baseData hna).subset
    rintro E ⟨hm', hE⟩
    have hhm : hm' = hm := Subsingleton.elim _ _
    subst hm'
    exact hE
  apply (extension_classes_divisors
    n classes hfinite).subset
  intro E hdegree
  letI : FiniteDimensional K E := FiniteDimensional.of_finrank_pos (by
    rw [hdegree]
    exact Nat.pos_of_ne_zero hn)
  obtain ⟨m, hm, hFE, hE⟩ :=
    selected_eisenstein_presentation
      n E hdegree unramifiedBase baseData
  refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, ⟨hm, ?_⟩⟩⟩
  let F := unramifiedBase m
  let data := (baseData m hm).toILData
  letI : CompleteSpace F := data.completeSpace
  letI : IsUltrametricDist F := data.isUltrametricDist
  letI : Valued F NNReal :=
    @NormedField.toValued F inferInstance data.isUltrametricDist
  letI : (Valued.v : Valuation F NNReal).RankOne := data.rankOne
  letI : CompleteSpace (Valued.integer F) := data.valuationRingComplete
  letI : IsDiscreteValuationRing (Valued.integer F) := data.valuationRingDVR
  letI : Finite (Valued.ResidueField F) := data.finiteResidueField
  letI : NormedAlgebra F Omega :=
    { norm_smul_le := fun r x ↦ by
        rw [Algebra.smul_def, norm_mul,
          IntermediateField.algebraMap_apply, data.norm_coe] }
  letI : Algebra.IsAlgebraic F Omega := data.algebraicAmbient
  letI : IsGalois F Omega := data.galoisAmbient
  change E ∈ (fun EF : IntermediateField F Omega ↦ EF.restrictScalars K) ''
    {EF | @EisensteinPresentedExtension F inferInstance
      data.isUltrametricDist data.valuationRingDVR Omega inferInstance
      inferInstance (n / m - 1) EF}
  refine ⟨IntermediateField.extendScalars (F := F) (E := E) hFE, hE, ?_⟩
  exact IntermediateField.extendScalars_restrictScalars hFE

omit [IsGalois K Omega] in
/-- Milne, Remark 7.65, with the dependent family of selected unramified
bases chosen internally.  Thus callers need only prove existence of an
embedded unramified degree-`m` base for each divisor `m` of `n`; no coherent
choice of fields or of their dependent local-field structures is exported.

The remaining existence hypothesis is precisely the valuation-prolongation
step: Proposition 7.50 constructs the finite unramified extension from its
residue extension once a compatible valued algebraic closure has been fixed. -/
theorem embedded_extensions_base
    (n : ℕ) (hn : n ≠ 0)
    (hbase : ∀ m ∈ n.divisors,
      ∃ U : IntermediateField K Omega, Nonempty (SelectedBaseData m U))
    (hna : IsNonarchimedean (norm : Omega → ℝ)) :
    {E : IntermediateField K Omega | Module.finrank K E = n}.Finite := by
  classical
  let unramifiedBase : ℕ → IntermediateField K Omega := fun m ↦
    if hm : m ∈ n.divisors then (hbase m hm).choose else ⊥
  have baseData : ∀ m ∈ n.divisors,
      SelectedBaseData m (unramifiedBase m) := by
    intro m hm
    simpa only [unramifiedBase, dif_pos hm] using (hbase m hm).choose_spec.some
  exact embedded_extensions_fixed
    n hn unramifiedBase baseData hna

omit [IsGalois K Omega] in
/-- Milne, Remark 7.65, with no selected-base or compatibility hypothesis:
inside one valued algebraic closure there are only finitely many embedded
local extensions of any prescribed positive degree.

For each divisor `m` of `n`, Proposition 7.50 and the finite-field
degree-`m` construction provide the required unramified base internally. -/
theorem embedded_extensions_unconditional
    (n : ℕ) (hn : n ≠ 0) :
    {E : IntermediateField K Omega | Module.finrank K E = n}.Finite := by
  letI : IsUltrametricDist Omega := IsUltrametricDist.of_normedAlgebra K
  apply embedded_extensions_base
    n hn
  · intro m hm
    have hmdvd : m ∣ n := (Nat.mem_divisors.mp hm).1
    exact selected_base_data m
      (Nat.pos_of_dvd_of_pos hmdvd (Nat.pos_of_ne_zero hn))
  · exact IsUltrametricDist.isNonarchimedean_norm

end ArbitraryFiniteExtensionDecomposition

end Submission.NumberTheory.Milne
