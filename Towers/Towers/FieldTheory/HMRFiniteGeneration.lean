import Towers.FieldTheory.HMRProThree
import Towers.FieldTheory.GaloisIdealAction
import Towers.FieldTheory.RestrictNormal
import Towers.NumberTheory.HigherRamification
import Towers.Topology.OpenNormal


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers
namespace TBluepr
namespace STBuild

/- We isolate the openness of the Zassenhaus terms into a short local pipeline. The substantive
inputs are:

1. `Gal(Q_S^(3) / ℚ)` is topologically finitely generated.
2. `Gal(Q_S^(3) / ℚ)` is pro-`3`.
3. Zassenhaus filtration terms of topologically finitely generated pro-`p` groups are open.

The Jennings-Lazard packaging below remains useful for constructing explicit finite discrete
quotients, but the final openness proof uses the standard pro-`p` theorem directly. -/
section InitialZassenhausOpen

abbrev InitialProComponent :=
  {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
    IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes}

/-- A finite stage of the defining compositum for `Q_S^(3)`. This is the specialized finite
compositum whose ramification control is the next missing input for the tower argument. -/
noncomputable def proFinsetCompositum
    (T : Finset InitialProComponent) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E ∈ T, E.1.toIntermediateField

noncomputable instance instRatPro
    (T : Finset InitialProComponent) :
    Algebra ℚ ↥(proFinsetCompositum T) :=
  (proFinsetCompositum T).algebra

instance instRatFinset
    (T : Finset InitialProComponent) :
    Module ℚ ↥(proFinsetCompositum T) := by
  let _ := instRatPro T
  infer_instance

instance instDimensionalRat
    (T : Finset InitialProComponent) :
    FiniteDimensional ℚ ↥(proFinsetCompositum T) := by
  change FiniteDimensional ℚ ↥(⨆ E ∈ T, E.1.toIntermediateField)
  exact IntermediateField.finiteDimensional_iSup_of_finset'
    (t := fun E : InitialProComponent => E.1.toIntermediateField)
    (s := T) (fun E _ => inferInstance)

instance instProFinset
    (T : Finset InitialProComponent) :
    NumberField ↥(proFinsetCompositum T) := by
  letI : FiniteDimensional ℚ ↥(proFinsetCompositum T) :=
    instDimensionalRat T
  exact NumberField.of_module_finite ℚ ↥(proFinsetCompositum T)

instance integers_scalar_tower
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] :
    IsScalarTower ℤ (𝓞 K) K := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  simp

theorem pro_i_sup
    (T : Finset InitialProComponent) :
    let ι := {E // E ∈ T}
    let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
      fun E => E.1.1.toIntermediateField
    proFinsetCompositum T = ⨆ E : ι, t E := by
  classical
  unfold proFinsetCompositum
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun hE => ?_
    exact le_iSup_of_le ⟨E, hE⟩ le_rfl
  · refine iSup_le fun E => ?_
    exact le_iSup_of_le E.1 <| le_iSup_of_le E.2 le_rfl

theorem pro_finset_galois
    (T : Finset InitialProComponent) :
    IsGalois ℚ ↥(proFinsetCompositum T) := by
  classical
  let ι := {E // E ∈ T}
  let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.1.toIntermediateField
  have hEq :
      proFinsetCompositum T = ⨆ E : ι, t E := by
    simpa [ι, t] using pro_i_sup T
  have hnormal :
      Normal ℚ ↥(⨆ E : ι, t E) := by
    simpa [t] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
        (h := fun E => by
          letI : IsGalois ℚ E.1.1 := E.1.1.isGalois
          simpa using (IsGalois.to_normal (F := ℚ) (E := E.1.1))))
  have hsep :
      Algebra.IsSeparable ℚ ↥(⨆ E : ι, t E) := by
    simpa [t] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
        (h := fun E => by
          letI : IsGalois ℚ E.1.1 := E.1.1.isGalois
          simpa using (IsGalois.to_isSeparable (F := ℚ) (E := E.1.1))))
  letI : Algebra ℚ ↥(⨆ E : ι, t E) := (⨆ E : ι, t E).algebra
  have hgal : IsGalois ℚ ↥(⨆ E : ι, t E) := { to_isSeparable := hsep, to_normal := hnormal }
  letI : IsGalois ℚ ↥(⨆ E : ι, t E) := hgal
  exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hEq.symm)

instance instFinsetCompositum
    (T : Finset InitialProComponent) :
    IsGalois ℚ ↥(proFinsetCompositum T) :=
  pro_finset_galois T

noncomputable def proFinsetComponent
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    IntermediateField ℚ ↥(proFinsetCompositum T) :=
  let t : {E // E ∈ T} → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.1.toIntermediateField
  (t i).restrict
    (show t i ≤ proFinsetCompositum T by
      exact le_iSup_of_le i.1 <| le_iSup_of_le i.2 le_rfl)

noncomputable def initial_finset_component
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    i.1.1 ≃ₐ[ℚ] ↥(proFinsetComponent T i) := by
  exact IntermediateField.restrict_algEquiv
    (show i.1.1.toIntermediateField ≤ proFinsetCompositum T by
      exact le_iSup_of_le i.1 <| le_iSup_of_le i.2 le_rfl)

instance instDimensionalComponent
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    FiniteDimensional ℚ ↥(proFinsetComponent T i) := by
  let e :=
    initial_finset_component T i
  exact FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective

instance instFinsetComponent
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    NumberField ↥(proFinsetComponent T i) := by
  exact NumberField.of_module_finite ℚ
    ↥(proFinsetComponent T i)

theorem pro_component_galois
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    IsGalois ℚ ↥(proFinsetComponent T i) := by
  letI : IsGalois ℚ i.1.1 := i.1.1.isGalois
  exact IsGalois.of_algEquiv
    (initial_finset_component T i)

instance instProComponent
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    IsGalois ℚ ↥(proFinsetComponent T i) :=
  pro_component_galois T i

theorem pro_compositum_component
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    (i : {E // E ∈ T}) :
    RationalPrimeUnramified
      (S := 𝓞 ↥(proFinsetComponent T i)) q := by
  exact
    rational_unramified_alg
      (initial_finset_component T i)
      (i.1.2.2 q hq hqS)

theorem pro_finset_component
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    IsGaloisGroup
      (Gal(↥(proFinsetComponent T i)/ℚ))
      ℤ
      (𝓞 ↥(proFinsetComponent T i)) := by
  let E := proFinsetComponent T i
  let hst : IsScalarTower ℤ (𝓞 ↥E) ↥E :=
    integers_scalar_tower (K := ↥E)
  exact
    @IsGaloisGroup.of_isFractionRing
      (Gal(↥E/ℚ))
      ℤ
      (𝓞 ↥E)
      ℚ
      ↥E
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hst
      _ _ _ _ _

theorem pro_component_normal
    (T : Finset InitialProComponent)
    (i : {E // E ∈ T}) :
    Normal ℚ ↥(proFinsetComponent T i) := by
  letI : IsGalois ℚ ↥(proFinsetComponent T i) :=
    pro_component_galois T i
  infer_instance

set_option maxHeartbeats 800000 in
-- Restricting inertia through the finite compositum generates a large elaboration term.
set_option synthInstance.maxHeartbeats 200000 in
-- Restricting inertia through the finite compositum generates a large elaboration term.
theorem component_restrict_inertia
    (T : Finset InitialProComponent)
    {q : ℕ}
    {P : Ideal (𝓞 ↥(proFinsetCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(↥(proFinsetCompositum T)/ℚ))
    (hσ : σ ∈ P.inertia (Gal(↥(proFinsetCompositum T)/ℚ)))
    (i : {E // E ∈ T}) :
    AlgEquiv.restrictNormalHom (proFinsetComponent T i) σ ∈
      (P.under (𝓞 ↥(proFinsetComponent T i))).inertia
        (Gal(↥(proFinsetComponent T i)/ℚ)) := by
  let E := proFinsetComponent T i
  letI : IsGalois ℚ ↥E := pro_component_galois T i
  letI : Normal ℚ ↥E := IsGalois.to_normal
  letI : Normal ℚ ↥(proFinsetComponent T i) :=
    pro_component_normal T i
  letI : IsScalarTower ℤ (𝓞 ↥E) ↥E := integers_scalar_tower (K := ↥E)
  letI : IsGalois ℚ ↥(proFinsetCompositum T) :=
    pro_finset_galois T
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  intro x
  change
    MulSemiringAction.toAlgHom ℤ (𝓞 ↥E)
      (AlgEquiv.restrictNormalHom E σ) x - x ∈ Q
  rw [Ideal.mem_of_liesOver
    (A := 𝓞 ↥E)
    (B := 𝓞 ↥(proFinsetCompositum T))
    (p := Q)
    (P := P)]
  rw [map_sub]
  have hmap :
      algebraMap (𝓞 ↥E) (𝓞 ↥(proFinsetCompositum T))
        (MulSemiringAction.toAlgHom ℤ
          (𝓞 ↥E) (σ.restrictNormalHom E) x) =
      MulSemiringAction.toAlgHom ℤ
        (𝓞 ↥(proFinsetCompositum T)) σ
          (algebraMap (𝓞 ↥E)
            (𝓞 ↥(proFinsetCompositum T)) x) := by
    apply Subtype.ext
    change
      algebraMap ↥(proFinsetComponent T i)
          ↥(proFinsetCompositum T)
          (((AlgEquiv.restrictNormalHom
              (proFinsetComponent T i)) σ)
            (algebraMap
              (𝓞 ↥(proFinsetComponent T i))
              ↥(proFinsetComponent T i)
              x)) =
        σ
          (algebraMap ↥(proFinsetComponent T i)
            ↥(proFinsetCompositum T)
            (algebraMap
              (𝓞 ↥(proFinsetComponent T i))
              ↥(proFinsetComponent T i)
              x))
    simpa using
      (@AlgEquiv.restrictNormalHom_apply
        ℚ
        _
        ↥(proFinsetCompositum T)
        _
        _
        (proFinsetComponent T i)
        (pro_component_normal T i)
        σ
        (algebraMap
          (𝓞 ↥(proFinsetComponent T i))
          ↥(proFinsetComponent T i)
          x))
  rw [hmap]
  simpa using hσ
    (algebraMap
      (𝓞 ↥E)
      (𝓞 ↥(proFinsetCompositum T)) x)

theorem finset_compositum_component
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(proFinsetCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (i : {E // E ∈ T}) :
    Nat.card
      ((P.under (𝓞 ↥(proFinsetComponent T i))).inertia
        (Gal(↥(proFinsetComponent T i)/ℚ))) = 1 := by
  let E := proFinsetComponent T i
  letI : IsGalois ℚ ↥E := pro_component_galois T i
  letI :
      IsGaloisGroup
        (Gal(↥E/ℚ))
        ℤ
        (𝓞 ↥E) :=
    pro_finset_component T i
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  have hQmem : Q ∈ Ideal.primesOver qI (𝓞 ↥E) := by
    refine ⟨inferInstance, inferInstance⟩
  have hQram : Ideal.ramificationIdx qI Q = 1 := by
    exact
      pro_compositum_component
        T hq hqS i Q hQmem
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 Q
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal (show Q.IsPrime by infer_instance) hQ0
  letI : Field ((𝓞 ↥E) ⧸ Q) := Ideal.Quotient.field Q
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((𝓞 ↥E) ⧸ Q) := by
    infer_instance
  have hramIn : qI.ramificationIdxIn (𝓞 ↥E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 ↥E) = Ideal.ramificationIdx qI Q := by
        exact Ideal.ramificationIdxIn_eq_ramificationIdx
          (p := qI) (P := Q) (G := Gal(↥E/ℚ))
      _ = 1 := hQram
  calc
    Nat.card (Q.inertia (Gal(↥E/ℚ))) = qI.ramificationIdxIn (𝓞 ↥E) := by
      exact Ideal.card_inertia_eq_ramificationIdxIn
        (G := Gal(↥E/ℚ)) qI hqI0 Q
    _ = 1 := hramIn

set_option synthInstance.maxHeartbeats 200000 in
-- Restriction across the profinite component requires a deeper instance search.
theorem pro_component_restriction
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(proFinsetCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(↥(proFinsetCompositum T)/ℚ))
    (hσ : σ ∈ P.inertia (Gal(↥(proFinsetCompositum T)/ℚ)))
    (i : {E // E ∈ T}) :
    AlgEquiv.restrictNormalHom (proFinsetComponent T i) σ = 1
     := by
  let E := proFinsetComponent T i
  letI : IsGalois ℚ ↥E := pro_component_galois T i
  let σE : Gal(↥E/ℚ) := AlgEquiv.restrictNormalHom E σ
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  have hσE :
      σE ∈ Q.inertia (Gal(↥E/ℚ)) := by
    exact
      component_restrict_inertia
        (q := q) (P := P) T σ hσ i
  have hcard :
      Nat.card (Q.inertia (Gal(↥E/ℚ))) = 1 := by
    exact
      finset_compositum_component
        T hq hqS i
  have hsub :
      Subsingleton ↥(Q.inertia (Gal(↥E/ℚ))) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : Subsingleton ↥(Q.inertia (Gal(↥E/ℚ))) := hsub
  have hσEeq :
      (⟨σE, hσE⟩ : Q.inertia (Gal(↥E/ℚ))) = 1 := by
    exact Subsingleton.elim _ _
  exact congrArg Subtype.val hσEeq

theorem components_sup_top
    (T : Finset InitialProComponent) :
    let ι := {E // E ∈ T}
    (⨆ i ∈ (Finset.univ : Finset ι),
      proFinsetComponent T i) = ⊤ := by
  classical
  let ι := {E // E ∈ T}
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    proFinsetCompositum T
  let A : IntermediateField ℚ ↥K :=
    ⨆ i ∈ (Finset.univ : Finset ι), proFinsetComponent T i
  change A = ⊤
  apply (IntermediateField.lift_injective K)
  change IntermediateField.lift A = IntermediateField.lift (⊤ : IntermediateField ℚ ↥K)
  rw [show IntermediateField.lift (⊤ : IntermediateField ℚ ↥K) = K by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩]
  refine le_antisymm (IntermediateField.lift_le A) ?_
  change proFinsetCompositum T ≤ IntermediateField.lift A
  rw [pro_i_sup T]
  refine iSup_le fun i => ?_
  have hi : proFinsetComponent T i ≤ A := by
    exact le_iSup_of_le i <| le_iSup_of_le (by simp) le_rfl
  have hmap :
      IntermediateField.lift (proFinsetComponent T i) ≤
        IntermediateField.lift A := by
    exact IntermediateField.map_mono (IntermediateField.val K) hi
  simpa [K, proFinsetComponent] using hmap

set_option maxHeartbeats 800000 in
-- Triviality across every component produces a large finite-compositum proof term.
set_option synthInstance.maxHeartbeats 200000 in
-- Triviality across every component produces a large finite-compositum proof term.
theorem pro_finset_trivial
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(proFinsetCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∀ σ : P.inertia (Gal(↥(proFinsetCompositum T)/ℚ)), σ = 1 := by
  intro σ
  classical
  let ι := {E // E ∈ T}
  have hfix :
      ∀ i : ι,
        (σ : Gal(↥(proFinsetCompositum T)/ℚ)) ∈
          (proFinsetComponent T i).fixingSubgroup := by
    intro i
    letI : IsGalois ℚ ↥(proFinsetComponent T i) :=
      pro_component_galois T i
    letI : Normal ℚ ↥(proFinsetComponent T i) :=
      IsGalois.to_normal
    have hrestrict :
        AlgEquiv.restrictNormalHom (proFinsetComponent T i)
            (σ : Gal(↥(proFinsetCompositum T)/ℚ)) =
          1 :=
      pro_component_restriction
        T hq hqS (σ : Gal(↥(proFinsetCompositum T)/ℚ)) σ.2 i
    rw [IntermediateField.mem_fixingSubgroup_iff
      (K := proFinsetComponent T i)]
    intro x hx
    have hsub :
        (AlgEquiv.restrictNormalHom (proFinsetComponent T i)
            (σ : Gal(↥(proFinsetCompositum T)/ℚ))) ⟨x, hx⟩ =
          ⟨x, hx⟩ := by
      simpa using congrArg (fun τ => τ ⟨x, hx⟩) hrestrict
    calc
      (σ : Gal(↥(proFinsetCompositum T)/ℚ)) x =
          ↑((AlgEquiv.restrictNormalHom
            (proFinsetComponent T i)
            (σ : Gal(↥(proFinsetCompositum T)/ℚ)))
            ⟨x, hx⟩) := by
        symm
        change
          ↑(((σ : Gal(↥(proFinsetCompositum T)/ℚ)).restrictNormal
              ↥(proFinsetComponent T i)) ⟨x, hx⟩) =
            (σ : Gal(↥(proFinsetCompositum T)/ℚ)) x
        exact
          AlgEquiv.restrictNormal_commutes
            (χ := (σ : Gal(↥(proFinsetCompositum T)/ℚ)))
            (E := proFinsetComponent T i) ⟨x, hx⟩
      _ = x := congrArg Subtype.val hsub
  have hsup :
      (σ : Gal(↥(proFinsetCompositum T)/ℚ)) ∈
        (⨆ i : ι, proFinsetComponent T i).fixingSubgroup := by
    have hs :
        ∀ s : Finset ι,
          (σ : Gal(↥(proFinsetCompositum T)/ℚ)) ∈
            (s.sup fun i => proFinsetComponent
             T i).fixingSubgroup
            := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha hs
        rw [Finset.sup_insert, IntermediateField.fixingSubgroup_sup]
        exact ⟨hfix a, hs⟩
    simpa [Finset.sup_eq_iSup] using hs Finset.univ
  have hsup_eq_top :
      (⨆ i : ι, proFinsetComponent T i) = ⊤ := by
    simpa [ι, Finset.sup_eq_iSup] using
      (components_sup_top T)
  have htop :
      (σ : Gal(↥(proFinsetCompositum T)/ℚ)) ∈
        (⊤ : IntermediateField ℚ
          ↥(proFinsetCompositum T)).fixingSubgroup := by
    rwa [hsup_eq_top] at hsup
  have hσ : (σ : Gal(↥(proFinsetCompositum T)/ℚ)) = 1 := by
    rwa [IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at htop
  exact Subtype.ext hσ

set_option maxHeartbeats 800000 in
-- The compositum ramification calculation requires extended normalization.
theorem pro_finset_compositum
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes) :
    (Ideal.rationalPrimeIdeal q).ramificationIdxIn
      (𝓞 ↥(proFinsetCompositum T)) = 1 := by
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  let hst : IsScalarTower ℤ (𝓞 ↥(proFinsetCompositum T))
      ↥(proFinsetCompositum T) :=
    integers_scalar_tower
      (K := ↥(proFinsetCompositum T))
  letI : IsGaloisGroup Gal(↥(proFinsetCompositum T)/ℚ) ℤ
      (𝓞 ↥(proFinsetCompositum T)) :=
    by
      exact
        @IsGaloisGroup.of_isFractionRing
          (Gal(↥(proFinsetCompositum T)/ℚ))
          ℤ (𝓞 ↥(proFinsetCompositum T)) ℚ
          ↥(proFinsetCompositum T)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst _ _ _ _ _
  obtain ⟨P, hP⟩ :
      Set.Nonempty
        (Ideal.primesOver qI (𝓞 ↥(proFinsetCompositum T))) :=
    Set.nonempty_of_ncard_ne_zero <|
      IsDedekindDomain.primesOver_ncard_ne_zero qI
        (𝓞 ↥(proFinsetCompositum T))
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 P
  letI : P.IsMaximal := hP.1.isMaximal hP0
  letI : Field ((𝓞 ↥(proFinsetCompositum T)) ⧸ P) :=
    Ideal.Quotient.field P
  letI : Algebra.IsSeparable (ℤ ⧸ qI)
      ((𝓞 ↥(proFinsetCompositum T)) ⧸ P) := by
    infer_instance
  have hcard :
      Nat.card
        (P.inertia (Gal(↥(proFinsetCompositum T)/ℚ))) = 1 := by
    have hsub :
        Subsingleton
          ↥(P.inertia (Gal(↥(proFinsetCompositum T)/ℚ))) := by
      refine ⟨?_⟩
      intro σ τ
      calc
        σ = 1 := pro_finset_trivial T hq hqS σ
        _ = τ := by
          symm
          exact pro_finset_trivial T hq hqS τ
    letI :
        Subsingleton
          ↥(P.inertia (Gal(↥(proFinsetCompositum T)/ℚ))) := hsub
    letI :
        Fintype
          ↥(P.inertia (Gal(↥(proFinsetCompositum T)/ℚ))) :=
      Fintype.ofSubsingleton
        (1 : P.inertia (Gal(↥(proFinsetCompositum T)/ℚ)))
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofSubsingleton
      (1 : P.inertia (Gal(↥(proFinsetCompositum T)/ℚ)))
  calc
    qI.ramificationIdxIn (𝓞 ↥(proFinsetCompositum T)) =
        Nat.card
          (P.inertia (Gal(↥(proFinsetCompositum T)/ℚ))) := by
      symm
      exact Ideal.card_inertia_eq_ramificationIdxIn
        (G := Gal(↥(proFinsetCompositum T)/ℚ)) qI hqI0 P
    _ = 1 := hcard

theorem pro_finset_unramified
    (T : Finset InitialProComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes) :
    RationalPrimeUnramified
      (S := 𝓞 ↥(proFinsetCompositum T)) q := by
  simpa [RationalPrimeUnramified, RationalRamificationIdx] using
    fun P hP => by
      rw [rational_idx_primes
        (L := ↥(proFinsetCompositum T)) (hr := hq) hP]
      exact pro_finset_compositum T hq hqS

/-- The first missing ramification lemma for the tower: a finite compositum of the defining
finite Galois `3`-extensions is still unramified outside `initialRamifiedPrimes`. -/
theorem pro_finset_outside
    (T : Finset InitialProComponent) :
    UnramifiedOutside
      ↥(proFinsetCompositum T) initialRamifiedPrimes := by
  intro q hq hqS
  exact pro_finset_unramified T hq hqS

set_option maxHeartbeats 800000 in
-- Trapping a finite subextension inside a finite stage of the ambient `iSup` needs extra
-- reduction budget for the basis-and-restriction bookkeeping.
set_option synthInstance.maxHeartbeats 100000 in
/-- Once the finite-stage composita are controlled, every finite Galois subextension of
`Q_S^(3)` should inherit the same unramified-outside condition by passing through a finite
stage of the defining `iSup`. -/
theorem pro_subextension_outside
    (E : FiniteGaloisIntermediateField ℚ initialProExtension) :
    UnramifiedOutside E initialRamifiedPrimes := by
  classical
  letI : IsGalois ℚ ↥E := E.isGalois
  let b := Module.finBasis ℚ E
  let supports :
      Fin (Module.finrank ℚ E) → Finset InitialProComponent := fun i =>
    Classical.choose <|
      IntermediateField.exists_finset_of_mem_iSup
        (f := fun F : InitialProComponent => F.1.toIntermediateField)
        (show (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
            initialProIntermediate from
          (((b i : E) : initialProExtension)).2)
  let T : Finset InitialProComponent := Finset.univ.biUnion supports
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    proFinsetCompositum T
  have hbasis_mem_K :
      ∀ i : Fin (Module.finrank ℚ E),
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈ K := by
    intro i
    have hi :
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
          ⨆ F ∈ supports i, F.1.toIntermediateField :=
      Classical.choose_spec <|
        IntermediateField.exists_finset_of_mem_iSup
          (f := fun F : InitialProComponent => F.1.toIntermediateField)
          (show (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
              initialProIntermediate from
            (((b i : E) : initialProExtension)).2)
    have hle : (⨆ F ∈ supports i, F.1.toIntermediateField) ≤ K := by
      unfold K proFinsetCompositum
      refine iSup_le fun F => iSup_le fun hF => ?_
      exact
        le_iSup_of_le F <|
          le_iSup_of_le
            (by
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hF⟩)
            le_rfl
    exact hle hi
  have hKle : K ≤ initialProIntermediate := by
    unfold K proFinsetCompositum initialProIntermediate
    refine iSup_le fun F => iSup_le fun hF => ?_
    exact le_iSup_of_le F le_rfl
  let K' : IntermediateField ℚ initialProExtension := K.restrict hKle
  have hbasis_mem_K' :
      ∀ i : Fin (Module.finrank ℚ E), ((b i : E) : initialProExtension) ∈ K' := by
    intro i
    exact
      (IntermediateField.mem_restrict hKle (((b i : E) : initialProExtension))).2
        (hbasis_mem_K i)
  have hE_le_K' : E ≤ K' := by
    intro x hx
    let xE : E := ⟨x, hx⟩
    have hxsumE : ∑ i, (b.repr xE i : ℚ) • (b i : E) = xE := b.sum_repr xE
    have hcoe :
        (((∑ i, (b.repr xE i : ℚ) • (b i : E)) : E) : initialProExtension) =
          ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) := by
      simpa using
        (IntermediateField.coe_sum (f := fun i =>
          (b.repr xE i : ℚ) • (b i : E)))
    have hxsum :
        ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) = x := by
      exact hcoe.symm.trans (congrArg Subtype.val hxsumE)
    have hxmem :
        ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) ∈ K' := by
      simpa using
        K'.sum_mem (t := Finset.univ) (fun i _ => K'.smul_mem (hbasis_mem_K' i))
    exact hxsum.symm ▸ hxmem
  let E' : IntermediateField ℚ K' := E.restrict hE_le_K'
  let eE : E ≃ₐ[ℚ] ↥E' := IntermediateField.restrict_algEquiv hE_le_K'
  let ι := {F // F ∈ T}
  let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) := fun F => F.1.1.toIntermediateField
  let K0 : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ F : ι, t F
  letI : Algebra ℚ ↥K0 := K0.algebra
  have hK_eq : K = K0 := by
    unfold K proFinsetCompositum
    apply le_antisymm
    · refine iSup_le fun F => iSup_le fun hF => ?_
      exact le_iSup_of_le ⟨F, hF⟩ le_rfl
    · refine iSup_le fun F => ?_
      exact le_iSup_of_le F.1 <| le_iSup_of_le F.2 le_rfl
  have hK_normal : Normal ℚ ↥K0 := by
    change Normal ℚ ↥(⨆ F : ι, t F)
    simpa [K0, t] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
        (h := fun F => by
          letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
          simpa using (IsGalois.to_normal (F := ℚ) (E := ↥(F.1.1)))))
  have hK_sep : Algebra.IsSeparable ℚ ↥K0 := by
    change Algebra.IsSeparable ℚ ↥(⨆ F : ι, t F)
    simpa [K0, t] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
        (h := fun F => by
          letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
          simpa using (IsGalois.to_isSeparable (F := ℚ) (E := ↥(F.1.1)))))
  have hK_galois_aux : IsGalois ℚ ↥K0 := by
    exact { to_normal := hK_normal, to_isSeparable := hK_sep }
  letI : IsGalois ℚ ↥K0 := hK_galois_aux
  letI : IsGalois ℚ ↥K := IsGalois.of_algEquiv (IntermediateField.equivOfEq hK_eq).symm
  let eK : ↥K ≃ₐ[ℚ] ↥K' := IntermediateField.restrict_algEquiv hKle
  letI : FiniteDimensional ℚ ↥K' :=
    FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.surjective
  letI : NumberField ↥K' := NumberField.of_module_finite ℚ ↥K'
  letI : IsGalois ℚ ↥K' := IsGalois.of_algEquiv eK
  letI : FiniteDimensional ℚ ↥E' :=
    FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.surjective
  letI : NumberField ↥E' := NumberField.of_module_finite ℚ ↥E'
  letI : IsGalois ℚ ↥E' := IsGalois.of_algEquiv eE
  have hK'_unram : UnramifiedOutside ↥K' initialRamifiedPrimes := by
    intro q hq hqS
    exact
      rational_unramified_alg eK
        (pro_finset_outside T q hq hqS)
  have hE'_unram : UnramifiedOutside ↥E' initialRamifiedPrimes := by
    intro q hq hqS
    exact
      rational_unramified_intermediate
        (K := ↥K') E' hq (hK'_unram q hq hqS)
  intro q hq hqS
  exact rational_unramified_alg eE.symm (hE'_unram q hq hqS)

/-- A finite Galois number field embedding into `Q_S^(3)` should therefore already be
unramified outside `initialRamifiedPrimes`. This is the wrapper `tower_unramified_outside`
will use after moving to the field range of the embedding. -/
theorem outside_embeds_pro
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : EmbedsIntoExtension K initialProExtension) :
    UnramifiedOutside K initialRamifiedPrimes := by
  rw [UnramifiedOutside, RamifiedOnlyAt]
  intro q hq hqS
  rcases hK with ⟨f⟩
  let E : IntermediateField ℚ initialProExtension := f.fieldRange
  let e : K ≃ₐ[ℚ] ↥E := by
    simpa [E, AlgHom.fieldRange_toSubalgebra f] using (AlgEquiv.ofInjectiveField f)
  letI : FiniteDimensional ℚ ↥E :=
    FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  have hE_gal : IsGalois ℚ ↥E := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField ℚ initialProExtension :=
    @FiniteGaloisIntermediateField.mk ℚ initialProExtension _ _ _ E inferInstance hE_gal
  have hE_unram : RationalPrimeUnramified (S := 𝓞 ↥E) q := by
    simpa [UnramifiedOutside, RamifiedOnlyAt, Efg] using
      (pro_subextension_outside Efg) q hq hqS
  exact rational_unramified_alg e.symm hE_unram

local notation "G" => initialGaloisGroup

section UniformTopologicalGeneration

/-- The tuple of quotient classes induced by an open normal quotient. -/
def quotientTupleMap
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (d : ℕ) (N : OpenNormalSubgroup Γ) :
    (Fin d → Γ) → (Fin d → Γ ⧸ (N : Subgroup Γ)) :=
  fun s i => ((s i : Γ) : Γ ⧸ (N : Subgroup Γ))

/-- Tuples whose images generate the finite quotient `Γ ⧸ N`. -/
def quotientGeneratingTuples
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (d : ℕ) (N : OpenNormalSubgroup Γ) :
    Set (Fin d → Γ) :=
  {s | Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N s)) = ⊤}

lemma quotient_tuple_continuous
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (d : ℕ) (N : OpenNormalSubgroup Γ) :
    Continuous (quotientTupleMap (Γ := Γ) d N) := by
  classical
  refine continuous_pi fun i => ?_
  exact QuotientGroup.continuous_mk.comp (continuous_apply i)

lemma closed_generating_tuples
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (d : ℕ) (N : OpenNormalSubgroup Γ) :
    IsClosed (quotientGeneratingTuples (Γ := Γ) d N) := by
  classical
  let T : Set (Fin d → Γ ⧸ (N : Subgroup Γ)) :=
    {t | Subgroup.closure (Set.range t) = ⊤}
  have hclosedT : IsClosed T := isClosed_discrete T
  simpa [quotientGeneratingTuples, T, quotientTupleMap] using
    hclosedT.preimage (quotient_tuple_continuous (Γ := Γ) d N)

/-- Passing to a coarser open normal quotient preserves the property of generating the quotient. -/
lemma generating_tuples_mono
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {d : ℕ}
    {N₁ N₂ : OpenNormalSubgroup Γ} (h : (N₁ : Subgroup Γ) ≤ N₂) :
    quotientGeneratingTuples (Γ := Γ) d N₁ ⊆
      quotientGeneratingTuples (Γ := Γ) d N₂ := by
  intro s hs
  let q : Γ ⧸ (N₁ : Subgroup Γ) →* Γ ⧸ (N₂ : Subgroup Γ) :=
    QuotientGroup.map (N := (N₁ : Subgroup Γ)) (M := (N₂ : Subgroup Γ))
      (MonoidHom.id Γ) h
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N₂ : Subgroup Γ) x
    refine ⟨((g : Γ) : Γ ⧸ (N₁ : Subgroup Γ)), ?_⟩
    simp [q, QuotientGroup.map_mk]
  have hmap_top :
      Subgroup.map q
        (Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N₁ s))) = ⊤ := by
    rw [hs, Subgroup.map_top_of_surjective q hq_surj]
  have hle :
      Subgroup.map q
          (Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N₁ s))) ≤
        Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N₂ s)) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨i, rfl⟩
    exact ⟨i, by simp [quotientTupleMap, q, QuotientGroup.map_mk]⟩
  exact top_unique <| by simpa [hmap_top] using hle

lemma generating_tuples_intersection
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (d : ℕ)
    (hgen : ∀ N : OpenNormalSubgroup Γ,
      (quotientGeneratingTuples (Γ := Γ) d N).Nonempty)
    (S : Finset (OpenNormalSubgroup Γ)) :
    (⋂ N ∈ S, quotientGeneratingTuples (Γ := Γ) d N).Nonempty := by
  classical
  let M : OpenNormalSubgroup Γ := S.inf id
  rcases hgen M with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simp only [Set.mem_iInter]
  intro N hN
  exact generating_tuples_mono (Γ := Γ) (d := d)
    (N₁ := M) (N₂ := N) (show M ≤ N from Finset.inf_le hN) hs

/-- Compactness produces a single tuple that generates every open normal quotient at once. -/
lemma tuple_generating_quotients
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (d : ℕ)
    (hgen : ∀ N : OpenNormalSubgroup Γ,
      (quotientGeneratingTuples (Γ := Γ) d N).Nonempty) :
    ∃ s : Fin d → Γ,
      ∀ N : OpenNormalSubgroup Γ,
        s ∈ quotientGeneratingTuples (Γ := Γ) d N := by
  classical
  have hnonempty :
      (⋂ N : OpenNormalSubgroup Γ, quotientGeneratingTuples (Γ := Γ) d N).Nonempty := by
    refine CompactSpace.iInter_nonempty
      (fun N => closed_generating_tuples (Γ := Γ) d N) ?_
    intro S
    simpa using generating_tuples_intersection
      (Γ := Γ) d hgen S
  rcases hnonempty with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simpa [Set.mem_iInter] using hs

/-- If a tuple generates every finite quotient by an open normal subgroup, then it is dense. -/
lemma topological_generates_quotients
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : ∀ N : OpenNormalSubgroup Γ,
      s ∈ quotientGeneratingTuples (Γ := Γ) d N) :
    Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤ := by
  classical
  let H : ClosedSubgroup Γ :=
    ⟨Subgroup.topologicalClosure (Subgroup.closure (Set.range s)),
      Subgroup.isClosed_topologicalClosure _⟩
  by_contra hH
  have hH' : ((H : ClosedSubgroup Γ) : Subgroup Γ) ≠ ⊤ := hH
  have hH'' : ¬ ∀ g : Γ, g ∈ (H : Subgroup Γ) := by
    simpa [Subgroup.eq_top_iff'] using hH'
  push Not at hH''
  obtain ⟨g, hgH⟩ := hH''
  have hH_eq :
      (H : Subgroup Γ) =
        sInf {U : Subgroup Γ | IsOpen (U : Set Γ) ∧ (H : Subgroup Γ) ≤ U} := by
    simpa using (ProfiniteGrp.closedSubgroup_eq_sInf_open H)
  have hg_sInf :
      g ∉ sInf {U : Subgroup Γ | IsOpen (U : Set Γ) ∧ (H : Subgroup Γ) ≤ U} := by
    rw [← hH_eq]
    exact hgH
  rw [Subgroup.mem_sInf] at hg_sInf
  push Not at hg_sInf
  obtain ⟨U, hU, hgU⟩ := hg_sInf
  rcases hU with ⟨hUopen, hHU⟩
  obtain ⟨N, hNU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hUopen U.one_mem
  have hNleU : (N : Subgroup Γ) ≤ U := fun x hx => hNU hx
  have hsU : ∀ i, s i ∈ U := by
    intro i
    exact hHU <|
      (Subgroup.le_topologicalClosure (Subgroup.closure (Set.range s))) <|
        Subgroup.subset_closure (Set.mem_range_self i)
  have hclosure_le :
      Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N s)) ≤
        Subgroup.map (QuotientGroup.mk' (N : Subgroup Γ)) U := by
    apply (Subgroup.closure_le
      (K := Subgroup.map (QuotientGroup.mk' (N : Subgroup Γ)) U)).2
    rintro _ ⟨i, rfl⟩
    exact ⟨s i, hsU i, rfl⟩
  have hmap_top : Subgroup.map (QuotientGroup.mk' (N : Subgroup Γ)) U = ⊤ := by
    have hgenN :
        Subgroup.closure (Set.range (quotientTupleMap (Γ := Γ) d N s)) = ⊤ := hs N
    exact top_unique <| by simpa [hgenN] using hclosure_le
  have hg_not_map :
      ((g : Γ) : Γ ⧸ (N : Subgroup Γ)) ∉
        Subgroup.map (QuotientGroup.mk' (N : Subgroup Γ)) U := by
    intro hgmap
    rcases hgmap with ⟨u, huU, huq⟩
    have huN : u⁻¹ * g ∈ (N : Subgroup Γ) := by
      exact inv_mul_quotient (N := N) (by simpa using huq)
    have huU' : u⁻¹ * g ∈ U := hNleU huN
    have hgU' : g ∈ U := by
      have : u * (u⁻¹ * g) ∈ U := U.mul_mem huU huU'
      simpa [mul_assoc] using this
    exact hgU hgU'
  have : ((g : Γ) : Γ ⧸ (N : Subgroup Γ)) ∈
      Subgroup.map (QuotientGroup.mk' (N : Subgroup Γ)) U := by
    simp [hmap_top]
  exact hg_not_map this

/-- Uniform generation of all finite open-normal quotients implies topological finite generation. -/
lemma topologically_uniformly_quotients
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (d : ℕ)
    (hgen : ∀ N : OpenNormalSubgroup Γ,
      (quotientGeneratingTuples (Γ := Γ) d N).Nonempty) :
    ∃ s : Fin d → Γ,
      Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤ := by
  obtain ⟨s, hs⟩ :=
    tuple_generating_quotients (Γ := Γ) d hgen
  exact ⟨s, topological_generates_quotients
    (Γ := Γ) s hs⟩

end UniformTopologicalGeneration

/-- Concatenating the five local pairs amounts to taking the supremum of the subgroups they
individually generate. -/
lemma pair_i_sup
    {Q : Type*} [Group Q]
    (H : {s // s ∈ initialRamifiedPrimes} → Subgroup Q)
    (y : (r : {s // s ∈ initialRamifiedPrimes}) → Fin 2 → Q)
    (hy : ∀ r i, y r i ∈ H r)
    (hygen : ∀ r, Subgroup.closure (Set.range (y r)) = H r) :
    Subgroup.closure
        (Set.range (fun a : ({s // s ∈ initialRamifiedPrimes} × Fin 2) => y a.1 a.2)) =
      ⨆ r, H r := by
  apply le_antisymm
  · apply (Subgroup.closure_le (K := ⨆ r, H r)).2
    rintro _ ⟨⟨r, i⟩, rfl⟩
    exact (le_iSup H r) (hy r i)
  · refine iSup_le fun r => ?_
    rw [← hygen r]
    apply (Subgroup.closure_le
      (K := Subgroup.closure
        (Set.range (fun a : ({s // s ∈ initialRamifiedPrimes} × Fin 2) => y a.1 a.2)))).2
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨(r, i), rfl⟩

/-- If the five local subgroups already generate the quotient and each is generated by a pair,
then the concatenated ten elements generate the whole quotient. -/
lemma closure_i_sup
    {Q : Type*} [Group Q]
    (H : {s // s ∈ initialRamifiedPrimes} → Subgroup Q)
    (y : (r : {s // s ∈ initialRamifiedPrimes}) → Fin 2 → Q)
    (hy : ∀ r i, y r i ∈ H r)
    (hygen : ∀ r, Subgroup.closure (Set.range (y r)) = H r)
    (hHtop : (⨆ r, H r) = ⊤) :
    Subgroup.closure
        (Set.range (fun a : ({s // s ∈ initialRamifiedPrimes} × Fin 2) => y a.1 a.2)) = ⊤ := by
  rw [pair_i_sup H y hy hygen, hHtop]

/-- The remaining arithmetic input for the main theorem is exactly the construction of five local
subgroups in the quotient whose supremum is `⊤`, together with two generators for each one. -/
lemma generated_ten_images
    (N : OpenNormalSubgroup G)
    (H : {s // s ∈ initialRamifiedPrimes} → Subgroup (G ⧸ (N : Subgroup G)))
    (y : (r : {s // s ∈ initialRamifiedPrimes}) → Fin 2 → G ⧸ (N : Subgroup G))
    (hy : ∀ r i, y r i ∈ H r)
    (hygen : ∀ r, Subgroup.closure (Set.range (y r)) = H r)
    (hHtop : (⨆ r, H r) = ⊤) :
    ∃ x : ({s // s ∈ initialRamifiedPrimes} × Fin 2) → G ⧸ (N : Subgroup G),
      Subgroup.closure (Set.range x) = ⊤ := by
  refine ⟨fun a => y a.1 a.2, ?_⟩
  exact closure_i_sup H y hy hygen hHtop

/- The five ramified primes, each contributing a tame decomposition group that is generated by two
elements, give a uniform set of ten generators in every finite quotient `G ⧸ N`.

This packages the arithmetic heart of the Shafarevich argument:

1. the finite quotient is generated by the images of the decomposition groups at
   `7, 13, 19, 31, 37`;
2. each of those decomposition-group images is 2-generated because the residue-field Frobenius
   quotient is cyclic and tame inertia is cyclic in the local pro-`3` situation.
-/
/-- A subgroup is metacyclic when it contains a cyclic normal subgroup with cyclic quotient.

This is the abstract local group-theoretic shape expected from the image of a tame decomposition
group in a finite quotient. -/
def IMSubgro
    {Q : Type*} [Group Q] (H : Subgroup Q) : Prop :=
  ∃ I : Subgroup H, ∃ _ : I.Normal,
    IsCyclic I ∧ IsCyclic (H ⧸ I)

lemma IMSubgro.map_subgroup_mulequiv
    {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (H : Subgroup Q)
    (hH : IMSubgro H) :
    IMSubgro (e.mapSubgroup H) := by
  classical
  rcases hH with ⟨I, hI_normal, hI_cyclic, hquot_cyclic⟩
  let eH : H ≃* e.mapSubgroup H := e.subgroupMap H
  let J : Subgroup (e.mapSubgroup H) := I.map eH.toMonoidHom
  have hJ_normal : J.Normal := by
    exact hI_normal.map eH.toMonoidHom eH.surjective
  have hJ_cyclic : IsCyclic J := by
    exact (eH.subgroupMap I).isCyclic.mp hI_cyclic
  have hquot_cyclic' : IsCyclic ((e.mapSubgroup H) ⧸ J) := by
    have hIJ : I ≤ J.comap eH.toMonoidHom := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    let qmap : H ⧸ I →* (e.mapSubgroup H) ⧸ J :=
      QuotientGroup.map I J eH.toMonoidHom hIJ
    have hmk_surjective :
        Function.Surjective
          (QuotientGroup.mk' J ∘ eH.toMonoidHom :
            H → (e.mapSubgroup H) ⧸ J) := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective J y
      obtain ⟨x, rfl⟩ := eH.surjective z
      exact ⟨x, rfl⟩
    exact isCyclic_of_surjective qmap
      (QuotientGroup.map_surjective_of_surjective
        (N := I) (M := J) eH.toMonoidHom hmk_surjective hIJ)
  exact ⟨J, hJ_normal, hJ_cyclic, hquot_cyclic'⟩

/--
The automorphism group of a finite residue-field extension is cyclic.

For the local decomposition subgroup, the quotient by inertia is identified with this group via
`Ideal.Quotient.stabilizerQuotientInertiaEquiv`. Finite fields have cyclic Galois groups generated
by Frobenius, so this is the residue-field half of metacyclicity.
-/
lemma galois_group_cyclic
    {k K : Type*} [Field k] [Field K] [Finite K] [Algebra k K] :
    IsCyclic (Gal(K/k)) := by
  classical
  -- Mathlib proves that automorphisms of a finite field extension of a finite field are generated
  -- by Frobenius. The instance is stated with finiteness of the top field.
  have hFiniteTop : Finite K := inferInstance
  letI : Finite K := hFiniteTop
  exact inferInstance

/-- The rational prime ideal `(q)` is nonzero. -/
lemma rational_ne_bot {q : ℕ} (hq : Nat.Prime q) :
    Ideal.rationalPrimeIdeal q ≠ ⊥ := by
  dsimp [Ideal.rationalPrimeIdeal]
  refine mt Ideal.span_singleton_eq_bot.mp ?_
  exact_mod_cast hq.ne_zero

/-- The rational prime ideal `(q)` is maximal in `ℤ`. -/
lemma rational_ideal_maximal {q : ℕ} (hq : Nat.Prime q) :
    (Ideal.rationalPrimeIdeal q).IsMaximal := by
  have hp_ne_bot : Ideal.rationalPrimeIdeal q ≠ ⊥ :=
    rational_ne_bot hq
  letI : (Ideal.rationalPrimeIdeal q).IsPrime :=
    rational_prime_ideal hq
  exact Ring.HasFiniteQuotients.maximalOfPrime hp_ne_bot

/-- A prime of the ring of integers above a rational prime is maximal. -/
lemma number_above_maximal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.IsMaximal := by
  have hp_ne_bot : Ideal.rationalPrimeIdeal q ≠ ⊥ :=
    rational_ne_bot hq
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  exact Ring.DimensionLEOne.maximalOfPrime hP_ne_bot inferInstance

/-- The residue-field units at a number-field prime are cyclic. -/
lemma number_residue_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  have hFiniteResidue :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hFiniteResidue
  exact inferInstance

/--
Any group that injects into the units of the finite residue field at a number-field prime is
cyclic.
-/
lemma cyclic_injective_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ]
    (χ : Γ →* (NumberField.RingOfIntegers L ⧸ P)ˣ)
    (hχ : Function.Injective χ) :
    IsCyclic Γ := by
  classical
  have hUnits :
      IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    number_residue_cyclic (L := L) hq P
  letI : IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    hUnits
  exact isCyclic_of_injective χ hχ

/-- For a finite Galois number field, inertia has cardinality equal to the ramification index. -/
lemma inertia_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.card (P.inertia (Gal(L/ℚ))) =
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P := by
  classical
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsPrime := by
    simpa [p] using rational_prime_ideal hq
  letI : P.LiesOver p := by
    simpa [p] using (inferInstance : P.LiesOver (Ideal.rationalPrimeIdeal q))
  have hp_ne_bot : p ≠ ⊥ := by
    simpa [p] using rational_ne_bot hq
  letI : p.IsMaximal := by
    simpa [p] using rational_ideal_maximal hq
  letI : P.IsMaximal := by
    simpa [p] using
      number_above_maximal (L := L) hq P
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  have hBaseFinite : Finite (ℤ ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp_ne_bot
  letI : Finite (ℤ ⧸ p) := hBaseFinite
  letI : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  have hResidueFinite :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hResidueFinite
  letI : Module.Finite (ℤ ⧸ p) (NumberField.RingOfIntegers L ⧸ P) :=
    Module.Finite.of_finite
  letI : Algebra.IsSeparable (ℤ ⧸ p)
      (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : IsGaloisGroup (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing
      (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) ℚ L
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdxIn p (NumberField.RingOfIntegers L) :=
    Ideal.card_inertia_eq_ramificationIdxIn p hp_ne_bot P
  have hIdx :
      Ideal.ramificationIdxIn p (NumberField.RingOfIntegers L) =
        Ideal.ramificationIdx p P :=
    Ideal.ramificationIdxIn_eq_ramificationIdx p P (Gal(L/ℚ))
  simpa [p] using hCard.trans hIdx

/-- Tameness makes the inertia order prime to the residue characteristic. -/
lemma tame_inertia_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))) := by
  classical
  have hP_mem :
      P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q)
        (NumberField.RingOfIntegers L) :=
    ⟨inferInstance, inferInstance⟩
  have hRamificationCoprime :
      Nat.Coprime q
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) :=
    hTame P hP_mem
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    inertia_ramification_idx (L := L) hq P
  rw [hCard]
  exact hRamificationCoprime

/--
A `p`-subgroup of a group whose cardinal is prime to `p` is trivial.

This is the purely group-theoretic part of the tame inertia argument.  The statement is written
using `Nat.card`, so it also rules out the impossible infinite cases: an infinite ambient group
would have cardinal `0`, which cannot be coprime to a prime `p`.
-/
lemma p_card_coprime
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ]
    (H : Subgroup Γ)
    (hH : IsPGroup p H)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Nat.card H = 1 := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp_not_dvd_card :
      ¬ p ∣ Nat.card Γ := by
    exact (hp.coprime_iff_not_dvd).mp hCardCoprime
  have hH_card_cases :
      Nat.card H = 1 ∨ p ∣ Nat.card H := by
    exact hH.card_eq_or_dvd
  rcases hH_card_cases with hH_card_one | hp_dvd_H
  · exact hH_card_one
  · have hH_dvd_card :
        Nat.card H ∣ Nat.card Γ := by
      exact Subgroup.card_subgroup_dvd_card H
    have hp_dvd_card :
        p ∣ Nat.card Γ := by
      exact dvd_trans hp_dvd_H hH_dvd_card
    exact False.elim (hp_not_dvd_card hp_dvd_card)

/--
The preceding cardinal statement as a subgroup equality.

This is the form needed for kernels: once the kernel subgroup has cardinal `1`, Mathlib's
`Subgroup.eq_bot_of_card_eq` identifies it with the bottom subgroup.
-/
lemma bot_coprime_card
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ]
    (H : Subgroup Γ)
    (hH : IsPGroup p H)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    H = ⊥ := by
  classical
  have hH_card_one :
      Nat.card H = 1 := by
    exact
      p_card_coprime
        H hH hCardCoprime
  exact H.eq_bot_of_card_eq hH_card_one

/--
A homomorphism whose kernel is a `p`-group is injective if the source has order prime to `p`.

For tame inertia, the kernel of the tame character is wild inertia.  The local ramification
theorem says that kernel is a `q`-group, and the tame hypothesis says the whole inertia group has
order prime to `q`; this lemma is the formal bridge from those two facts to injectivity.
-/
lemma monoid_coprime_card
    {p : ℕ} [Fact p.Prime]
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ)
    (hKer : IsPGroup p χ.ker)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Function.Injective χ := by
  classical
  have hKer_bot :
      χ.ker = ⊥ := by
    exact
      bot_coprime_card
        χ.ker hKer hCardCoprime
  exact (MonoidHom.ker_eq_bot_iff χ).mp hKer_bot

/--
The ordinary quotient by a maximal ideal agrees with Mathlib's local residue field.

`Ideal.ResidueField I` is defined as the residue field of the localization at `I`.  For maximal
`I`, the localization has the same residue field as the quotient `R ⧸ I`; this packages the
bijective algebra map as a ring equivalence.
-/
noncomputable def idealResidueMaximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal] :
    R ⧸ I ≃+* I.ResidueField :=
  RingEquiv.ofBijective
    (algebraMap (R ⧸ I) I.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField I)

/--
The unit groups of `R ⧸ I` and `I.ResidueField` are equivalent when `I` is maximal.

The eventual tame character is naturally constructed after localizing at `P`; this equivalence
lets us transport it back to the quotient-unit target used by the global number-field lemmas.
-/
noncomputable def unitsResidueMaximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal] :
    (R ⧸ I)ˣ ≃* I.ResidueFieldˣ :=
  Units.mapEquiv (idealResidueMaximal I).toMulEquiv

@[simp]
lemma units_residue_maximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal]
    (u : (R ⧸ I)ˣ) :
    (unitsResidueMaximal I u : I.ResidueField) =
      algebraMap (R ⧸ I) I.ResidueField u := by
  rfl

/--
Postcomposing a group homomorphism with a multiplicative equivalence does not change its kernel.

This small group-theoretic fact is useful here because changing from the local residue-field unit
group to the quotient-residue unit group should not alter the wild-inertia kernel.
-/
lemma monoid_ker_comp
    {Γ Δ Δ' : Type*} [Group Γ] [Group Δ] [Group Δ']
    (e : Δ ≃* Δ') (χ : Γ →* Δ) :
    (e.toMonoidHom.comp χ).ker = χ.ker := by
  ext γ
  simp [MonoidHom.mem_ker]

/--
The `p`-group property for a kernel survives postcomposition by a multiplicative equivalence.

This is the exact kernel-transport step needed after replacing `P.ResidueFieldˣ` by
`(𝓞 L ⧸ P)ˣ`.
-/
lemma p_ker_comp
    {p : ℕ}
    {Γ Δ Δ' : Type*} [Group Γ] [Group Δ] [Group Δ']
    (e : Δ ≃* Δ') (χ : Γ →* Δ)
    (hχ : IsPGroup p χ.ker) :
    IsPGroup p (e.toMonoidHom.comp χ).ker := by
  rw [monoid_ker_comp e χ]
  exact hχ

/--
A subgroup contained in a Sylow `p`-subgroup is a `p`-group.

This is the finite-group endpoint of the wild-inertia argument: once local ramification theory
places the kernel of the tame character inside the wild Sylow subgroup, no more arithmetic is
needed to know that the kernel is a `p`-group.
-/
lemma p_group_sylow
    {p : ℕ} {Γ : Type*} [Group Γ]
    (S : Sylow p Γ) (H : Subgroup Γ)
    (hH : H ≤ (S : Subgroup Γ)) :
    IsPGroup p H := by
  classical
  have hSylow :
      IsPGroup p (S : Subgroup Γ) := by
    exact S.isPGroup'
  have hH' :
      IsPGroup p H := by
    exact hSylow.to_le hH
  exact hH'

/--
If the kernel of a homomorphism is contained in a Sylow `p`-subgroup of the source, then the
kernel is a `p`-group.

This packages the previous lemma in the form used by tame characters.
-/
lemma p_ker_sylow
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (S : Sylow p Γ)
    (hKer : χ.ker ≤ (S : Subgroup Γ)) :
    IsPGroup p χ.ker := by
  classical
  have hKerP :
      IsPGroup p χ.ker := by
    exact p_group_sylow S χ.ker hKer
  exact hKerP

/--
Every `p`-subgroup is contained in a Sylow `p`-subgroup.

This is Mathlib's `IsPGroup.exists_le_sylow`, named here in the direction needed by the tame
inertia argument.  It is the converse group-theoretic move to `p_group_sylow`.
-/
lemma sylow_p_group
    {p : ℕ} {Γ : Type*} [Group Γ]
    (H : Subgroup Γ) (hH : IsPGroup p H) :
    ∃ S : Sylow p Γ, H ≤ (S : Subgroup Γ) := by
  classical
  have hExists :
      ∃ S : Sylow p Γ, H ≤ (S : Subgroup Γ) := by
    exact hH.exists_le_sylow
  exact hExists

/--
If the kernel of a homomorphism is a `p`-group, then it lies in some Sylow `p`-subgroup of the
source.

For tame inertia this is the finite-group part of passing from “wild inertia is a `q`-group” to
“wild inertia is contained in a Sylow `q`-subgroup”.
-/
lemma monoid_sylow_p
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (hKer : IsPGroup p χ.ker) :
    ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
  classical
  have hExists :
      ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
    exact sylow_p_group χ.ker hKer
  exact hExists

/--
For a homomorphism kernel, being a `p`-group is equivalent to being contained in some Sylow
`p`-subgroup of the source.

This equivalence is useful because the local arithmetic naturally proves the left-hand side,
whereas the cyclicity argument downstream consumes the right-hand side.
-/
lemma monoid_p_sylow
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) :
    IsPGroup p χ.ker ↔
      ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
  constructor
  · intro hKer
    exact monoid_sylow_p χ hKer
  · rintro ⟨S, hKerS⟩
    exact p_ker_sylow χ S hKerS

/--
The Sylow-containment form implies injectivity under a coprime-cardinality hypothesis.

For tame inertia, this is the statement that a wild kernel cannot survive once the whole inertia
group has order prime to the residue characteristic.
-/
lemma monoid_sylow_coprime
    {p : ℕ} [Fact p.Prime]
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (S : Sylow p Γ)
    (hKer : χ.ker ≤ (S : Subgroup Γ))
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Function.Injective χ := by
  classical
  have hKerP :
      IsPGroup p χ.ker := by
    exact p_ker_sylow χ S hKer
  have hInjective :
      Function.Injective χ := by
    exact
      monoid_coprime_card
        χ hKerP hCardCoprime
  exact hInjective

/--
The local residue field at a prime above `q` has characteristic `q`.

The proof is just the lying-over condition: `q` lies in `(q)`, hence its image lies in `P`,
so it vanishes in the residue field.  Since `q` is prime and the residue field is nontrivial,
this pins down the characteristic.
-/
lemma number_char_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    CharP P.ResidueField q := by
  classical
  have hq_mem_base :
      (q : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact Ideal.subset_span (by simp)
  have hq_mem_P :
      algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈ P := by
    exact
      (Ideal.mem_of_liesOver
        (B := NumberField.RingOfIntegers L)
        (p := Ideal.rationalPrimeIdeal q)
        (P := P)
        (x := (q : ℤ))).mp hq_mem_base
  have hq_zero_alg :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ)) = 0 := by
    rw [Ideal.algebraMap_residueField_eq_zero]
    exact hq_mem_P
  have hq_zero : (q : P.ResidueField) = 0 := by
    simpa [Int.cast_natCast,
      IsScalarTower.algebraMap_apply ℤ
        (NumberField.RingOfIntegers L) P.ResidueField] using hq_zero_alg
  exact (CharP.charP_iff_prime_eq_zero hq).mpr hq_zero

/--
The local residue field at a number-field prime is finite.

For a maximal ideal, Mathlib identifies `P.ResidueField` with `𝓞 L ⧸ P`; the
latter is already a finite ring for number fields.
-/
lemma number_local_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Finite P.ResidueField := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  have hQuotFinite :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hQuotFinite
  exact
    Finite.of_equiv
      (NumberField.RingOfIntegers L ⧸ P)
      (idealResidueMaximal P).toEquiv

/-- The units of the local residue field at a number-field prime are cyclic. -/
lemma number_units_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic P.ResidueFieldˣ := by
  classical
  have hResidueFinite :
      Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Finite P.ResidueField :=
    hResidueFinite
  exact inferInstance

/--
Any group that injects into the units of the local residue field at a number-field prime is
cyclic.
-/
lemma cyclic_residue_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ]
    (χ : Γ →* P.ResidueFieldˣ)
    (hχ : Function.Injective χ) :
    IsCyclic Γ := by
  classical
  have hUnits :
      IsCyclic P.ResidueFieldˣ :=
    number_units_cyclic (L := L) hq P
  letI : IsCyclic P.ResidueFieldˣ :=
    hUnits
  exact isCyclic_of_injective χ hχ

/--
The Sylow-containment form of a local tame character already gives cyclic inertia in the tame
case.

This lemma does not construct the character; it records the formal endpoint once the local
uniformizer argument has supplied the Sylow containment.
-/
lemma cyclic_character_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))))
    (S : Sylow q (P.inertia (Gal(L/ℚ))))
    (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ)
    (hKer : χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ))))) :
    IsCyclic (P.inertia (Gal(L/ℚ))) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hχ :
      Function.Injective χ := by
    exact
      monoid_sylow_coprime
        χ S hKer hCardCoprime
  exact
    cyclic_residue_units
      (L := L) hq P χ hχ

/--
Equality modulo an ideal gives equality in the quotient by that ideal.

This is just `Ideal.Quotient.eq`, but the named wrapper keeps the later ramification
arguments phrased in terms of congruences `x - y ∈ I`.
-/
lemma ideal_sub
    {R : Type*} [CommRing R] (I : Ideal R) {x y : R}
    (hxy : x - y ∈ I) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  have hquot :
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
    exact Ideal.Quotient.eq
  exact hquot.2 hxy

/--
Equality in the quotient by an ideal is equivalent to the corresponding difference lying in
the ideal.
-/
lemma ideal_quotient_sub
    {R : Type*} [CommRing R] (I : Ideal R) {x y : R} :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
  have hquot :
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
    exact Ideal.Quotient.eq
  exact hquot

/--
Equality modulo a prime ideal gives equality after mapping to the residue field.

The kernel of `R → I.ResidueField` is exactly `I`, so the proof reduces to applying the
quotient-kernel criterion to `x - y`.
-/
lemma residue_field_sub
    {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {x y : R}
    (hxy : x - y ∈ I) :
    algebraMap R I.ResidueField x = algebraMap R I.ResidueField y := by
  have hzero :
      algebraMap R I.ResidueField (x - y) = 0 := by
    exact (Ideal.algebraMap_residueField_eq_zero (I := I)).2 hxy
  have hsub :
      algebraMap R I.ResidueField x - algebraMap R I.ResidueField y = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.mp hsub

/--
The residue-field equality criterion for two representatives.

This is the residue-field analogue of `Ideal.Quotient.eq`, and is the form needed when
passing from the defining congruence of inertia to a pointwise statement over `P.ResidueField`.
-/
lemma ideal_residue_sub
    {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {x y : R} :
    algebraMap R I.ResidueField x = algebraMap R I.ResidueField y ↔ x - y ∈ I := by
  constructor
  · intro hxy
    have hzero :
        algebraMap R I.ResidueField (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact (Ideal.algebraMap_residueField_eq_zero (I := I)).1 hzero
  · intro hxy
    exact residue_field_sub (I := I) hxy

/--
Unpack the defining congruence of the inertia subgroup.

An element of inertia fixes every residue class modulo `P`; this lemma records the raw
congruence before passing to a quotient or residue field.
-/
lemma number_smul_sub
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
  have hσ :
      (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ)) := by
    exact σ.property
  exact hσ x

/--
Inertia acts trivially on the quotient `𝓞_L ⧸ P`.

This is the quotient form of `number_smul_sub`.
-/
lemma number_mk_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk P (((σ : Gal(L/ℚ)) • x)) =
      Ideal.Quotient.mk P x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  exact ideal_sub P hcong

/--
Inertia acts trivially after mapping representatives to the residue field `P.ResidueField`.

This is the residue-field form used by the tame-character construction: the residue of an
inertia translate of an integral element is the original residue.
-/
lemma number_residue_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (((σ : Gal(L/ℚ)) • x)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  exact residue_field_sub (I := P) hcong

/--
Every inertia element lies in the stabilizer of the prime ideal.

The tame local argument can therefore regard inertia elements as acting on the quotient
`𝓞_L ⧸ P` through `Ideal.Quotient.stabilizerHom`.
-/
lemma field_inertia_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (σ : Gal(L/ℚ)) ∈ MulAction.stabilizer (Gal(L/ℚ)) P := by
  have hσ :
      (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ)) := by
    exact σ.property
  exact (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) P) hσ

/--
An inertia element preserves the prime ideal itself.

This is the one-ideal version of the square-stability statement below.  It is the basic
membership fact needed to let inertia act on the cotangent ideal `P / P ^ 2`.
-/
lemma number_smul_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P) :
    ((σ : Gal(L/ℚ)) • x) ∈ P := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • P := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x P hx
  simpa [hStab] using hMem

/--
Viewed through the stabilizer action on the residue quotient, an inertia element acts as the
identity.

This packages the preceding pointwise quotient statement in the canonical Mathlib homomorphism
from the decomposition/stabilizer subgroup to automorphisms of the residue quotient.
-/
lemma number_inertia_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    Ideal.Quotient.stabilizerHom P (Ideal.rationalPrimeIdeal q) (Gal(L/ℚ))
        ⟨(σ : Gal(L/ℚ)), field_inertia_stabilizer (L := L) P σ⟩ = 1 := by
  classical
  apply MonoidHom.mem_ker.mp
  rw [Ideal.Quotient.ker_stabilizerHom]
  change (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ))
  exact σ.property

/--
An inertia element preserves the square of the prime ideal.

The proof uses two facts already formalized above: inertia lies in the stabilizer of `P`, and
the pointwise action on ideals is multiplicative.  This is the basic stability needed to make
the first ramification subgroup a subgroup.
-/
lemma number_inertia_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P ^ 2) :
    ((σ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  have hPow :
      (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
    calc
      (σ : Gal(L/ℚ)) • (P ^ 2) =
          ((σ : Gal(L/ℚ)) • P) ^ 2 := by
        simp [pow_two]
      _ = P ^ 2 := by
        rw [hStab]
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • (P ^ 2) := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x (P ^ 2) hx
  simpa [hPow] using hMem

/--
An inertia element fixes the ideal `P ^ 2` as a set.

This is the ideal-level version of `number_inertia_sq`; it is useful when
constructing quotient actions by functoriality of quotient rings.
-/
lemma smul_prime_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  calc
    (σ : Gal(L/ℚ)) • (P ^ 2) =
        ((σ : Gal(L/ℚ)) • P) ^ 2 := by
      simp [pow_two]
    _ = P ^ 2 := by
      rw [hStab]

/--
The square-stability statement in the exact form required by `Ideal.quotientEquiv`.
-/
lemma number_field_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P ^ 2 =
      (P ^ 2).map
        ((MulSemiringAction.toRingEquiv (Gal(L/ℚ))
          (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ))) :
            NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  have hPow :
      (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
    exact smul_prime_sq (L := L) P σ
  change P ^ 2 =
    (P ^ 2).map
      (MulSemiringAction.toRingHom (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
  rw [Ideal.map_pow]
  simpa [Ideal.pointwise_smul_def] using hPow.symm

/--
The first, or wild, ramification subgroup inside inertia.

An inertia element is in this subgroup if it acts trivially modulo `P ^ 2` on the ring of
integers.  In a local DVR this is equivalent to acting trivially on the cotangent line
`P / P ^ 2`, and it is the kernel of the usual tame inertia character.
-/
noncomputable def number_wild_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Subgroup (P.inertia (Gal(L/ℚ))) where
  carrier :=
    {σ | ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτx :
        ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
      exact hτ x
    have hστx :
        (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) ∈ P ^ 2 := by
      exact number_inertia_sq (L := L) P σ hτx
    have hσx :
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
      exact hσ x
    have hdecomp :
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
          (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
            (((σ : Gal(L/ℚ)) • x) - x) := by
      calc
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
            ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) - x := by
          simp [mul_smul]
        _ =
            (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
              (((σ : Gal(L/ℚ)) • x) - x) := by
          rw [smul_sub]
          abel
    rw [hdecomp]
    exact Ideal.add_mem (P ^ 2) hστx hσx
  inv_mem' := by
    intro σ hσ x
    let τ : P.inertia (Gal(L/ℚ)) := σ⁻¹
    have hσ_on_inv :
        ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) -
            ((τ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
      exact hσ ((τ : Gal(L/ℚ)) • x)
    have hx_sub :
        x - ((τ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
      simpa [τ, mul_smul] using hσ_on_inv
    have hneg :
        - (x - ((τ : Gal(L/ℚ)) • x)) ∈ P ^ 2 := by
      exact (P ^ 2).neg_mem hx_sub
    change ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ 2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-- Membership in the wild inertia subgroup, unfolded. -/
lemma wild_inertia_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ number_wild_subgroup (L := L) P ↔
      ∀ x : NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  rfl

/--
Wild inertia elements act trivially on the quotient by `P ^ 2`.

This is the quotient formulation of the previous definition, and it is the shape needed for
connecting the subgroup to the cotangent-line action.
-/
lemma number_wild_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ number_wild_subgroup (L := L) P)
    (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
      Ideal.Quotient.mk (P ^ 2) x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
    exact
      (wild_inertia_subgroup (L := L) P σ).1 hσ x
  exact ideal_sub (P ^ 2) hcong

/--
Conversely, pointwise triviality on `𝓞_L ⧸ P ^ 2` is exactly membership in wild inertia.
-/
lemma wild_sq_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
        Ideal.Quotient.mk (P ^ 2) x) :
    σ ∈ number_wild_subgroup (L := L) P := by
  rw [wild_inertia_subgroup (L := L) P σ]
  intro x
  exact (ideal_quotient_sub (P ^ 2)).1 (hσ x)

/--
The ring automorphism of `𝓞_L ⧸ P ^ 2` induced by an inertia element.

The previous lemma shows that inertia preserves `P ^ 2`, so the Galois action descends to the
square quotient.
-/
noncomputable def number_inertia_square
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
      (NumberField.RingOfIntegers L ⧸ P ^ 2) := by
  exact
    Ideal.quotientEquiv (P ^ 2) (P ^ 2)
      (MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (number_field_sq (L := L) P σ)

/-- The quotient-square action on representatives. -/
lemma number_square_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    number_inertia_square (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
  exact
    Ideal.quotientEquiv_mk
      (I := P ^ 2) (J := P ^ 2)
      (f := MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (hIJ := number_field_sq (L := L) P σ) x

/--
The action of inertia on `𝓞_L ⧸ P ^ 2` as a group representation.

This representation is not yet the tame character, but its kernel is exactly the subgroup that
will become the kernel of the tame character after reducing the uniformizer ratio.
-/
noncomputable def number_square_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    P.inertia (Gal(L/ℚ)) →*
      ((NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
        (NumberField.RingOfIntegers L ⧸ P ^ 2)) where
  toFun σ :=
    number_inertia_square (L := L) P σ
  map_one' := by
    classical
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_inertia_square (L := L) P 1
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) := by
          exact number_square_mk (L := L) P 1 x
      _ = Ideal.Quotient.mk (P ^ 2) x := by
          simp
      _ = (1 :
            (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
              (NumberField.RingOfIntegers L ⧸ P ^ 2))
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl
  map_mul' := by
    classical
    intro σ τ
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_inertia_square (L := L) P (σ * τ)
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2)
          ((((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x)) := by
          exact
            number_square_mk
              (L := L) P (σ * τ) x
      _ = Ideal.Quotient.mk (P ^ 2)
          ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
          have hmul :
              (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) =
                ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
            simpa using
              (mul_smul (σ : Gal(L/ℚ)) (τ : Gal(L/ℚ)) x)
          exact congrArg (Ideal.Quotient.mk (P ^ 2)) hmul
      _ = number_inertia_square (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) ((τ : Gal(L/ℚ)) • x)) := by
          exact
            (number_square_mk
              (L := L) P σ ((τ : Gal(L/ℚ)) • x)).symm
      _ = number_inertia_square (L := L) P σ
          (number_inertia_square (L := L) P τ
            (Ideal.Quotient.mk (P ^ 2) x)) := by
          exact
            congrArg
              (number_inertia_square (L := L) P σ)
              (number_square_mk
                (L := L) P τ x).symm
      _ =
          (number_inertia_square (L := L) P σ *
            number_inertia_square (L := L) P τ)
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl

/-- The quotient-square representation acts on representatives by applying the inertia element. -/
lemma square_representation_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    number_square_representation (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
  exact number_square_mk (L := L) P σ x

/--
Wild inertia is exactly the kernel of the action on `𝓞_L ⧸ P ^ 2`.

This repackages the definition of `number_wild_subgroup` as a kernel, which is the
form needed for the tame-character construction.
-/
lemma square_representation_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (number_square_representation (L := L) P).ker =
      number_wild_subgroup (L := L) P := by
  classical
  ext σ
  constructor
  · intro hσ
    rw [MonoidHom.mem_ker] at hσ
    apply
      wild_sq_mk
        (L := L) P
    intro x
    have hApply :=
      congrArg
        (fun e : (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
            (NumberField.RingOfIntegers L ⧸ P ^ 2) =>
          e (Ideal.Quotient.mk (P ^ 2) x)) hσ
    have hfixed :
        number_square_representation (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) x) =
          Ideal.Quotient.mk (P ^ 2) x := by
      simpa using hApply
    calc
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) =
          number_square_representation (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) x) := by
        exact
          (square_representation_mk
            (L := L) P σ x).symm
      _ = Ideal.Quotient.mk (P ^ 2) x := hfixed
  · intro hσ
    rw [MonoidHom.mem_ker]
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_square_representation (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
          exact square_representation_mk (L := L) P σ x
      _ = Ideal.Quotient.mk (P ^ 2) x := by
          exact
            number_wild_mk
              (L := L) P hσ x
      _ = (1 :
            (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
              (NumberField.RingOfIntegers L ⧸ P ^ 2))
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl

/--
The quotient-square action of inertia preserves the cotangent ideal `P / P ^ 2`.

The proof is deliberately pointwise: choose a representative in `𝓞_L`, use Mathlib's
criterion for membership in `Ideal.cotangentIdeal`, and reduce to the fact that inertia
preserves `P`.
-/
lemma number_square_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {z : NumberField.RingOfIntegers L ⧸ P ^ 2}
    (hz : z ∈ P.cotangentIdeal) :
    number_inertia_square (L := L) P σ z ∈
      P.cotangentIdeal := by
  classical
  obtain ⟨x, rfl⟩ :=
    Ideal.Quotient.mk_surjective z
  rw [number_square_mk]
  rw [Ideal.mk_mem_cotangentIdeal] at hz ⊢
  exact number_smul_prime (L := L) P σ hz

/--
The induced self-map of the cotangent ideal `P / P ^ 2`.

At this stage the important point is the invariant subobject: the tame character will later
extract the scalar by which inertia acts on this one-dimensional residue-field vector space.
-/
noncomputable def field_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P.cotangentIdeal → P.cotangentIdeal :=
  fun z =>
    ⟨number_inertia_square (L := L) P σ z,
      number_square_cotangent
        (L := L) P σ z.property⟩

/-- The induced cotangent-ideal map is the restriction of the quotient-square action. -/
lemma number_inertia_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    ↑(field_cotangent_ideal (L := L) P σ z) =
      number_inertia_square (L := L) P σ
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) := by
  rfl

/--
On a cotangent representative, the induced map is given by applying the inertia element to
that representative.
-/
lemma number_cotangent_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L)
    (hx : x ∈ P) :
    field_cotangent_ideal (L := L) P σ
        ⟨Ideal.Quotient.mk (P ^ 2) x, by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact hx⟩ =
      ⟨Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x), by
        rw [Ideal.mk_mem_cotangentIdeal]
        exact number_smul_prime (L := L) P σ hx⟩ := by
  ext
  exact number_square_mk (L := L) P σ x

/-- The induced cotangent-ideal map sends zero to zero. -/
lemma number_cotangent_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    field_cotangent_ideal (L := L) P σ 0 = 0 := by
  ext
  change
    number_inertia_square (L := L) P σ 0 = 0
  exact map_zero (number_inertia_square (L := L) P σ)

/-- The induced cotangent-ideal map is additive. -/
lemma number_cotangent_add
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z w : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ (z + w) =
      field_cotangent_ideal (L := L) P σ z +
        field_cotangent_ideal (L := L) P σ w := by
  ext
  change
    number_inertia_square (L := L) P σ
        ((z : NumberField.RingOfIntegers L ⧸ P ^ 2) + w) =
      number_inertia_square (L := L) P σ z +
        number_inertia_square (L := L) P σ w
  exact
    map_add
      (number_inertia_square (L := L) P σ)
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
      (w : NumberField.RingOfIntegers L ⧸ P ^ 2)

/-- The identity inertia element acts as the identity on the cotangent ideal. -/
lemma number_cotangent_one
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P 1 z = z := by
  ext
  change
    number_inertia_square (L := L) P 1
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  calc
    number_inertia_square (L := L) P 1
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2)
        (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) := by
        exact number_square_mk (L := L) P 1 x
    _ = Ideal.Quotient.mk (P ^ 2) x := by
        simp

/--
Cotangent-ideal maps compose according to multiplication in inertia.

The order is the same as for function composition: `(σ * τ)` acts by first applying `τ` and
then applying `σ`.
-/
lemma number_cotangent_mul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ τ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P (σ * τ) z =
      field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P τ z) := by
  ext
  change
    number_inertia_square (L := L) P (σ * τ)
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      number_inertia_square (L := L) P σ
        (number_inertia_square (L := L) P τ
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2))
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  calc
    number_inertia_square (L := L) P (σ * τ)
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2)
        ((((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x)) := by
        exact
          number_square_mk
            (L := L) P (σ * τ) x
    _ = Ideal.Quotient.mk (P ^ 2)
        ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
        have hmul :
            (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) =
              ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
          simpa using
            (mul_smul (σ : Gal(L/ℚ)) (τ : Gal(L/ℚ)) x)
        exact congrArg (Ideal.Quotient.mk (P ^ 2)) hmul
    _ = number_inertia_square (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) ((τ : Gal(L/ℚ)) • x)) := by
        exact
          (number_square_mk
            (L := L) P σ ((τ : Gal(L/ℚ)) • x)).symm
    _ = number_inertia_square (L := L) P σ
        (number_inertia_square (L := L) P τ
          (Ideal.Quotient.mk (P ^ 2) x)) := by
        exact
          congrArg
            (number_inertia_square (L := L) P σ)
            (number_square_mk
              (L := L) P τ x).symm

/-- Applying an inertia element and then its inverse is the identity on the cotangent ideal. -/
lemma number_cotangent_inv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ⁻¹
        (field_cotangent_ideal (L := L) P σ z) = z := by
  calc
    field_cotangent_ideal (L := L) P σ⁻¹
        (field_cotangent_ideal (L := L) P σ z) =
      field_cotangent_ideal (L := L) P (σ⁻¹ * σ) z := by
        exact
          (number_cotangent_mul
            (L := L) P σ⁻¹ σ z).symm
    _ = field_cotangent_ideal (L := L) P 1 z := by
        rw [inv_mul_cancel]
    _ = z := by
        exact number_cotangent_one (L := L) P z

/-- Applying the inverse and then the inertia element is the identity on the cotangent ideal. -/
lemma inertia_cotangent_inv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P σ⁻¹ z) = z := by
  calc
    field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P σ⁻¹ z) =
      field_cotangent_ideal (L := L) P (σ * σ⁻¹) z := by
        exact
          (number_cotangent_mul
            (L := L) P σ σ⁻¹ z).symm
    _ = field_cotangent_ideal (L := L) P 1 z := by
        rw [mul_inv_cancel]
    _ = z := by
        exact number_cotangent_one (L := L) P z

/-- The cotangent action of an inertia element as a bundled equivalence of the cotangent ideal. -/
noncomputable def inertia_cotangent_equiv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P.cotangentIdeal ≃ P.cotangentIdeal where
  toFun := field_cotangent_ideal (L := L) P σ
  invFun := field_cotangent_ideal (L := L) P σ⁻¹
  left_inv := by
    intro z
    exact number_cotangent_inv (L := L) P σ z
  right_inv := by
    intro z
    exact inertia_cotangent_inv (L := L) P σ z

/-- The bundled cotangent equivalence has the expected underlying function. -/
lemma inertia_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    inertia_cotangent_equiv (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

/-- The cotangent action of an inertia element as a bundled additive automorphism. -/
noncomputable def number_cotangent_equiv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    AddAut P.cotangentIdeal where
  toFun := field_cotangent_ideal (L := L) P σ
  invFun := field_cotangent_ideal (L := L) P σ⁻¹
  left_inv := by
    intro z
    exact number_cotangent_inv (L := L) P σ z
  right_inv := by
    intro z
    exact inertia_cotangent_inv (L := L) P σ z
  map_add' := by
    intro z w
    exact number_cotangent_add (L := L) P σ z w

/-- The bundled additive cotangent automorphism has the expected underlying function. -/
lemma number_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    number_cotangent_equiv (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

/--
The cotangent action as a genuine representation of inertia on the additive group `P / P ^ 2`.

This is the precise representation-theoretic object from which the tame character will be
extracted after identifying the cotangent ideal as a one-dimensional residue-field vector
space.
-/
noncomputable def cotangent_add_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    P.inertia (Gal(L/ℚ)) →* AddAut P.cotangentIdeal where
  toFun σ := number_cotangent_equiv (L := L) P σ
  map_one' := by
    apply AddEquiv.ext
    intro z
    exact number_cotangent_one (L := L) P z
  map_mul' := by
    intro σ τ
    apply AddEquiv.ext
    intro z
    exact number_cotangent_mul (L := L) P σ τ z

/-- The additive cotangent representation acts by the previously defined cotangent map. -/
lemma number_inertia_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    cotangent_add_representation (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

/--
Membership in the kernel of the additive cotangent representation is exactly pointwise
triviality on the cotangent ideal.
-/
lemma cotangent_representation_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ (cotangent_add_representation (L := L) P).ker ↔
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z := by
  constructor
  · intro hσ z
    rw [MonoidHom.mem_ker] at hσ
    have hApply :=
      congrArg
        (fun e : AddAut P.cotangentIdeal => e z) hσ
    simpa [number_inertia_representation]
      using hApply
  · intro hσ
    rw [MonoidHom.mem_ker]
    apply AddEquiv.ext
    intro z
    exact hσ z

/-- The kernel of the additive cotangent representation, written as a fixed-point subgroup. -/
lemma number_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (cotangent_add_representation (L := L) P).ker =
      {σ : P.inertia (Gal(L/ℚ)) |
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z} := by
  ext σ
  exact cotangent_representation_ker
    (L := L) P σ

/--
Wild inertia acts trivially on the cotangent ideal.

This is the easy direction of the standard identification of wild inertia with the kernel of
the action on `P / P ^ 2`: our definition of wild inertia already says that every integral
representative is fixed modulo `P ^ 2`.
-/
lemma wild_cotangent_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ number_wild_subgroup (L := L) P)
    (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ z = z := by
  ext
  change
    number_inertia_square (L := L) P σ
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  exact number_wild_mk (L := L) P hσ x

/-- Wild inertia is contained in the kernel of the additive cotangent representation. -/
lemma wild_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    number_wild_subgroup (L := L) P ≤
      (cotangent_add_representation (L := L) P).ker := by
  intro σ hσ
  rw [cotangent_representation_ker
    (L := L) P σ]
  intro z
  exact wild_cotangent_fixed (L := L) P hσ z

/--
Pointwise fixedness on the cotangent ideal is equivalent to fixing every element of `P`
modulo `P ^ 2`.

This is a purely quotient-level reformulation.  The forward direction applies the fixedness
hypothesis to the cotangent class of an element of `P`; the reverse direction chooses an integral
representative of an arbitrary element of the cotangent ideal and uses the membership criterion
for `Ideal.cotangentIdeal`.
-/
lemma number_cotangent_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z) ↔
      ∀ x : P,
        ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
          (x : NumberField.RingOfIntegers L) ∈ P ^ 2 := by
  constructor
  · intro hfixed x
    let z : P.cotangentIdeal :=
      ⟨Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L), by
        rw [Ideal.mk_mem_cotangentIdeal]
        exact x.property⟩
    have hzfixed :
        field_cotangent_ideal (L := L) P σ z = z := by
      exact hfixed z
    have hquot :
        Ideal.Quotient.mk (P ^ 2)
            ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) =
          Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L) := by
      have hzval :=
        congrArg
          (fun y : P.cotangentIdeal =>
            (y : NumberField.RingOfIntegers L ⧸ P ^ 2)) hzfixed
      change
        number_inertia_square (L := L) P σ
            (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2) at hzval
      change
        number_inertia_square (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L)) =
          Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L) at hzval
      rw [number_square_mk] at hzval
      exact hzval
    exact (ideal_quotient_sub (P ^ 2)).1 hquot
  · intro hP z
    ext
    change
      number_inertia_square (L := L) P σ
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
    obtain ⟨x, hxz⟩ :=
      Ideal.Quotient.mk_surjective
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
    have hxP : x ∈ P := by
      have hzmem : (z : NumberField.RingOfIntegers L ⧸ P ^ 2) ∈ P.cotangentIdeal :=
        z.property
      rw [← hxz] at hzmem
      rwa [Ideal.mk_mem_cotangentIdeal] at hzmem
    have hquot :
        Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
          Ideal.Quotient.mk (P ^ 2) x := by
      exact ideal_sub (P ^ 2) (hP ⟨x, hxP⟩)
    rw [← hxz]
    calc
      number_inertia_square (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) := by
          exact number_square_mk (L := L) P σ x
      _ = Ideal.Quotient.mk (P ^ 2) x := hquot

/--
The cardinality of the residue field maps to zero, hence lies in the prime ideal.

This is the finite-field input for the Frobenius-style reconstruction argument: if
`N = # P.ResidueField`, then `N` vanishes in `P.ResidueField`, so the integral element `N`
belongs to the kernel of `𝓞_L → P.ResidueField`, namely `P`.
-/
lemma number_cast_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (Nat.card P.ResidueField : NumberField.RingOfIntegers L) ∈ P := by
  classical
  haveI : Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField :=
    Fintype.ofFinite P.ResidueField
  rw [← Ideal.algebraMap_residueField_eq_zero (I := P)]
  simp [Nat.card_eq_fintype_card]

/--
Every integral element satisfies the finite-residue-field Frobenius congruence.

For `N = # P.ResidueField`, the residue of `x` is fixed by the `N`th-power map in the finite
field `P.ResidueField`.  Pulling this equality back through the residue map says
`x ^ N - x ∈ P`.
-/
lemma number_sub_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (x : NumberField.RingOfIntegers L) :
    x ^ Nat.card P.ResidueField - x ∈ P := by
  classical
  haveI : Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField :=
    Fintype.ofFinite P.ResidueField
  have hpow :
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) ^
          Nat.card P.ResidueField =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField x := by
    simpa [Nat.card_eq_fintype_card] using
      (FiniteField.pow_card
        (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x))
  exact
    (ideal_residue_sub
      (I := P) (x := x ^ Nat.card P.ResidueField) (y := x)).1
      (by simpa using hpow)

/--
The power of a square-zero perturbation has only its first-order term.

This elementary commutative-ring lemma is the binomial theorem specialized to an element `d`
with `d ^ 2 = 0`: all terms of degree at least two in `d` vanish, leaving the linear term
`n * x ^ (n - 1) * d`.
-/
lemma sq_cast_mul
    {R : Type*} [CommRing R] {n : ℕ} {x d : R}
    (hd2 : d ^ 2 = 0) :
    (x + d) ^ n = x ^ n + (n : R) * x ^ (n - 1) * d := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', ih]
      cases n with
      | zero =>
          simp
      | succ n =>
          simp [pow_succ, Nat.cast_add, Nat.cast_one]
          ring_nf
          rw [hd2]
          simp

/--
The binomial congruence needed for the square quotient.

If `d ∈ I` and the exponent `n` itself lies in `I`, then all terms of
`(x + d) ^ n - x ^ n` lie in `I ^ 2`: the linear term has coefficient `n`, while every higher
term has at least two factors of `d`.  This is the now-isolated local algebra/combinatorial
piece needed by the reconstruction lemma.
-/
lemma sub_sq_cast
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} {x d : R}
    (hd : d ∈ I) (hn : (n : R) ∈ I) :
    (x + d) ^ n - x ^ n ∈ I ^ 2 := by
  classical
  let Q : Type _ := R ⧸ I ^ 2
  let mk : R →+* Q := Ideal.Quotient.mk (I ^ 2)
  have hd2mem :
      d ^ 2 ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hd hd
  have hndmem :
      (n : R) * d ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hn hd
  have hd2quot :
      (mk d : Q) ^ 2 = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hd2mem
  have hndquot :
      (n : Q) * mk d = 0 := by
    have hmk :
        mk ((n : R) * d) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hndmem
    simpa [mk] using hmk
  have hpoweq :
      (mk (x + d) : Q) ^ n = (mk x : Q) ^ n := by
    have haux :
        ((mk x : Q) + mk d) ^ n =
          (mk x : Q) ^ n + (n : Q) * (mk x : Q) ^ (n - 1) * mk d := by
      exact
        sq_cast_mul
          (R := Q) (n := n) (x := mk x) (d := mk d) hd2quot
    have hterm :
        (n : Q) * (mk x : Q) ^ (n - 1) * mk d = 0 := by
      calc
        (n : Q) * (mk x : Q) ^ (n - 1) * mk d =
            (mk x : Q) ^ (n - 1) * ((n : Q) * mk d) := by
              ring
        _ = 0 := by
          rw [hndquot, mul_zero]
    rw [map_add]
    rw [haux, hterm, add_zero]
  have hzero :
      mk ((x + d) ^ n - x ^ n) = 0 := by
    rw [map_sub, map_pow, map_pow, hpoweq, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/--
Subtracting two compatible power congruences extracts the first-order congruence.

This is the algebraic end of the Frobenius reconstruction argument.  If the transformed
`N`th-power-minus-identity expression agrees with the original one modulo `I ^ 2`, and the
pure `N`th powers agree modulo `I ^ 2`, then the elements themselves agree modulo `I ^ 2`.
-/
lemma sub_sq_self
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} {x y : R}
    (hpowdiff : y ^ n - y - (x ^ n - x) ∈ I ^ 2)
    (hpows : y ^ n - x ^ n ∈ I ^ 2) :
    y - x ∈ I ^ 2 := by
  have hsub :
      (y ^ n - y - (x ^ n - x)) - (y ^ n - x ^ n) ∈ I ^ 2 := by
    exact (I ^ 2).sub_mem hpowdiff hpows
  have hneg :
      -(y - x) ∈ I ^ 2 := by
    convert hsub using 1
    ring
  simpa using (I ^ 2).neg_mem hneg

/--
The remaining local reconstruction step for the square quotient.

The proof uses the finite residue field rather than an abstract square-zero derivation
argument.  For `N = # P.ResidueField`, every integral element satisfies `x ^ N - x ∈ P`.
Applying the hypothesis on `P / P ^ 2` to this element and comparing with the binomial
congruence for `σ x = x + (σ x - x)` forces `σ x - x ∈ P ^ 2`.
-/
lemma number_smul_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ)))
    (hP : ∀ x : P,
      ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
        (x : NumberField.RingOfIntegers L) ∈ P ^ 2) :
    ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  classical
  intro x
  let N : ℕ := Nat.card P.ResidueField
  have hdelta :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  have hcardP :
      (N : NumberField.RingOfIntegers L) ∈ P := by
    simpa [N] using
      number_cast_prime (L := L) hq P
  have hpowP :
      x ^ N - x ∈ P := by
    simpa [N] using
      number_sub_prime (L := L) hq P x
  have hPpow :
      ((σ : Gal(L/ℚ)) • (x ^ N - x)) - (x ^ N - x) ∈ P ^ 2 := by
    exact hP ⟨x ^ N - x, hpowP⟩
  have hpowdiff :
      (((σ : Gal(L/ℚ)) • x) ^ N - ((σ : Gal(L/ℚ)) • x)) -
          (x ^ N - x) ∈ P ^ 2 := by
    simpa [smul_sub, smul_pow'] using hPpow
  have hpows :
      ((σ : Gal(L/ℚ)) • x) ^ N - x ^ N ∈ P ^ 2 := by
    have hbinom :
        (x + (((σ : Gal(L/ℚ)) • x) - x)) ^ N - x ^ N ∈ P ^ 2 := by
      exact
        sub_sq_cast
          (I := P) (n := N) (x := x)
          (d := ((σ : Gal(L/ℚ)) • x) - x) hdelta hcardP
    convert hbinom using 1
    ring
  exact
    sub_sq_self
      (I := P) (n := N) (x := x) (y := ((σ : Gal(L/ℚ)) • x))
      hpowdiff hpows

/--
The hard local direction: if inertia acts trivially on the cotangent ideal, then it is wild.

Equivalently, the kernel of the additive action on `P / P ^ 2` is contained in the subgroup
acting trivially on all of `𝓞_L ⧸ P ^ 2`.  This is the point where one uses the local
Dedekind/DVR structure: inertia already fixes the residue quotient `𝓞_L ⧸ P`, and a
cotangent-trivial lift must be trivial on the whole square-zero thickening.
-/
lemma number_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (cotangent_add_representation (L := L) P).ker ≤
      number_wild_subgroup (L := L) P := by
  intro σ hσ
  rw [wild_inertia_subgroup (L := L) P σ]
  have hfixed :
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z := by
    exact
      (cotangent_representation_ker
        (L := L) P σ).1 hσ
  have hP :
      ∀ x : P,
        ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
          (x : NumberField.RingOfIntegers L) ∈ P ^ 2 := by
    exact
      (number_cotangent_sq
        (L := L) P σ).1 hfixed
  exact
    number_smul_sq
      (L := L) hq P σ hP

/--
The additive cotangent representation has wild inertia as its kernel.

This joins the easy inclusion, already proved from the definition of wild inertia, with the
local-DVR converse isolated in
`number_cotangent_wild`.
-/
lemma cotangent_representation_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (cotangent_add_representation (L := L) P).ker =
      number_wild_subgroup (L := L) P := by
  apply le_antisymm
  · exact
      number_cotangent_wild
        (L := L) hq P
  · exact
      wild_cotangent_representation
        (L := L) P

/--
Equivalently, membership in the quotient-square kernel gives trivial action on the cotangent
ideal.  This form is useful when passing through the representation-theoretic packaging.
-/
lemma representation_cotangent_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ (number_square_representation (L := L) P).ker)
    (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ z = z := by
  have hWild :
      σ ∈ number_wild_subgroup (L := L) P := by
    simpa [square_representation_ker (L := L) P] using hσ
  exact
    wild_cotangent_fixed
      (L := L) P hWild z

/--
The scalar by which a linear automorphism of a one-dimensional vector space moves a chosen
nonzero generator.
-/
noncomputable def dimensionalRepresentationScalar
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) : K :=
  Classical.choose (hv_span (ρ g v))

/-- The defining equation for `dimensionalRepresentationScalar`. -/
lemma dimensional_representation_smul
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    dimensionalRepresentationScalar ρ v hv_span g • v = ρ g v := by
  exact Classical.choose_spec (hv_span (ρ g v))

/-- The scalar attached to a linear automorphism of a one-dimensional space is nonzero. -/
lemma dimensional_representation_scalar
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    dimensionalRepresentationScalar ρ v hv_span g ≠ 0 := by
  intro hzero
  have hmap_zero : ρ g v = 0 := by
    calc
      ρ g v =
          dimensionalRepresentationScalar ρ v hv_span g • v := by
            exact (dimensional_representation_smul ρ v hv_span g).symm
      _ = 0 := by
            rw [hzero, zero_smul]
  have hv_zero : v = 0 := by
    exact (ρ g).injective (by simpa using hmap_zero)
  exact hv_ne_zero hv_zero

/--
A linear representation on a one-dimensional vector space gives a character to the units of
the scalar field.

This is the abstract linear algebra behind the tame character: after the cotangent ideal is
identified with a one-dimensional residue-field vector space, the inertia action is by
multiplication by a unique nonzero scalar.
-/
noncomputable def dimensionalLinearCharacter
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) : G0 →* Kˣ where
  toFun g :=
    Units.mk0
      (dimensionalRepresentationScalar ρ v hv_span g)
      (dimensional_representation_scalar ρ v hv_ne_zero hv_span g)
  map_one' := by
    apply Units.ext
    change dimensionalRepresentationScalar ρ v hv_span 1 = 1
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span 1 • v =
          ρ 1 v := by
            exact dimensional_representation_smul ρ v hv_span 1
      _ = v := by
            simp
      _ = (1 : K) • v := by
            simp
  map_mul' := by
    intro g h
    apply Units.ext
    change
      dimensionalRepresentationScalar ρ v hv_span (g * h) =
        dimensionalRepresentationScalar ρ v hv_span g *
          dimensionalRepresentationScalar ρ v hv_span h
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span (g * h) • v =
          ρ (g * h) v := by
            exact dimensional_representation_smul ρ v hv_span (g * h)
      _ = ρ g (ρ h v) := by
            rw [map_mul]
            rfl
      _ = ρ g (dimensionalRepresentationScalar ρ v hv_span h • v) := by
            rw [dimensional_representation_smul]
      _ = dimensionalRepresentationScalar ρ v hv_span h • ρ g v := by
            exact map_smul (ρ g)
              (dimensionalRepresentationScalar ρ v hv_span h) v
      _ =
          dimensionalRepresentationScalar ρ v hv_span h •
            (dimensionalRepresentationScalar ρ v hv_span g • v) := by
            rw [dimensional_representation_smul]
      _ =
          (dimensionalRepresentationScalar ρ v hv_span h *
            dimensionalRepresentationScalar ρ v hv_span g) • v := by
            rw [mul_smul]
      _ =
          (dimensionalRepresentationScalar ρ v hv_span g *
            dimensionalRepresentationScalar ρ v hv_span h) • v := by
            rw [mul_comm]

/-- The scalar character acts on the chosen generator as the representation does. -/
lemma dimensional_character_smul
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    ((dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) • v) = ρ g v := by
  exact dimensional_representation_smul ρ v hv_span g

/--
The scalar character is trivial exactly when the original one-dimensional representation is
trivial.
-/
lemma dimensional_character_ker
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) :
    (dimensionalLinearCharacter ρ v hv_ne_zero hv_span).ker = ρ.ker := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearEquiv.ext
    intro w
    obtain ⟨a, ha⟩ := hv_span w
    have hscalar :
        (dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) = 1 := by
      exact congrArg Units.val hg
    calc
      ρ g w = ρ g (a • v) := by
          rw [ha]
      _ = a • ρ g v := by
          exact map_smul (ρ g) a v
      _ = a • ((dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) • v) := by
          rw [dimensional_character_smul]
      _ = a • ((1 : K) • v) := by
          rw [hscalar]
      _ = a • v := by
          rw [one_smul]
      _ = w := ha
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply Units.ext
    change
      dimensionalRepresentationScalar ρ v hv_span g = 1
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span g • v =
          ρ g v := by
            exact dimensional_representation_smul ρ v hv_span g
      _ = (1 : V ≃ₗ[K] V) v := by
            rw [hg]
      _ = (1 : K) • v := by
            simp

/--
Constructing a character from a one-dimensional linear representation, packaged as an
existence theorem with the desired kernel.
-/
lemma dimensional_linear_character
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) :
    ∃ χ : G0 →* Kˣ, χ.ker = ρ.ker := by
  refine ⟨dimensionalLinearCharacter ρ v hv_ne_zero hv_span, ?_⟩
  exact dimensional_character_ker ρ v hv_ne_zero hv_span

/--
An element spans a module for a specified module structure.  This keeps later local-algebra
statements from asking typeclass search to rediscover a complicated residue-field action while
elaborating the theorem statement.
-/
def dimensionalSpansElement
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V]
    (moduleInst : Module K V) (v : V) : Prop :=
  letI : Module K V := moduleInst
  ∀ w : V, ∃ a : K, a • v = w

/--
An additive representation is linear for a specified module structure if every group element
commutes with scalar multiplication.  The module instance is explicit to keep local residue-field
actions from becoming difficult typeclass-search problems in specialized theorem statements.
-/
def additiveRepresentationModule
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V]
    (moduleInst : Module K V) (ρadd : G0 →* AddAut V) : Prop :=
  letI : Module K V := moduleInst
  ∀ g : G0, ∀ a : K, ∀ v : V, ρadd g (a • v) = a • ρadd g v

/--
The scalar-character existence theorem, with the spanning hypothesis packaged using an explicit
module instance.
-/
lemma dimensional_spans_element
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : dimensionalSpansElement
      (K := K) (V := V) (inferInstance : Module K V) v) :
    ∃ χ : G0 →* Kˣ, χ.ker = ρ.ker := by
  have hv_span' : ∀ w : V, ∃ a : K, a • v = w := by
    dsimp [dimensionalSpansElement] at hv_span
    exact hv_span
  exact dimensional_linear_character ρ v hv_ne_zero hv_span'

/--
An additive representation whose operators are linear for a scalar action upgrades to a linear
representation with the same kernel.

This separates the formal representation-theory bookkeeping from the local arithmetic statement
that inertia acts `P.ResidueField`-linearly on `P / P ^ 2`.
-/
lemma additive_representation_linear
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρadd : G0 →* AddAut V)
    (hsmul : additiveRepresentationModule
      (K := K) (G0 := G0) (V := V) (inferInstance : Module K V) ρadd) :
    ∃ ρlin : G0 →* V ≃ₗ[K] V, ρlin.ker = ρadd.ker := by
  have hsmul_linear : ∀ g : G0, ∀ a : K, ∀ v : V, ρadd g (a • v) = a • ρadd g v := by
    dsimp [additiveRepresentationModule] at hsmul
    exact hsmul
  let ρlin : G0 →* V ≃ₗ[K] V := {
    toFun := fun g => AddEquiv.toLinearEquiv (R := K) (ρadd g) (hsmul_linear g)
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change ρadd 1 v = v
      simp
    map_mul' := by
      intro g h
      apply LinearEquiv.ext
      intro v
      change ρadd (g * h) v = (ρadd g * ρadd h) v
      exact congrArg (fun e : AddAut V => e v) (ρadd.map_mul g h)
  }
  refine ⟨ρlin, ?_⟩
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply AddEquiv.ext
    intro v
    have hApply :=
      congrArg (fun e : V ≃ₗ[K] V => e v) hg
    simpa [ρlin] using hApply
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearEquiv.ext
    intro v
    have hApply :=
      congrArg (fun e : AddAut V => e v) hg
    simpa [ρlin] using hApply

/--
The quotient model `P.Cotangent = P / P ^ 2` is naturally a module over the local residue field.

Mathlib gives `P.Cotangent` a module structure over `𝓞_L / P`.  Since a prime of the ring of
integers over `(q)` is maximal, `𝓞_L / P` is ring-equivalent to `P.ResidueField`; composing
scalars along the inverse equivalence gives the desired residue-field action.
-/
@[reducible]
noncomputable def cotangent_residue_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Module P.ResidueField P.Cotangent := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    Module.compHom P.Cotangent
      ((idealResidueMaximal P).symm.toRingHom)

/--
The ideal model of the cotangent space inherits the same residue-field module structure.

This is obtained by transporting the preceding structure across Mathlib's additive equivalence
`P.cotangentEquivIdeal : P.Cotangent ≃ₗ[R] P.cotangentIdeal`.
-/
@[reducible]
noncomputable def number_residue_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Module P.ResidueField P.cotangentIdeal := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  exact P.cotangentEquivIdeal.symm.toAddEquiv.module P.ResidueField

/--
With the transported module structure, the ideal model and quotient model of the cotangent space
are linearly equivalent over the residue field.

This will be useful for later generator arguments, where Mathlib's DVR cotangent-space results
are stated for `P.Cotangent` while the inertia action in this file is on `P.cotangentIdeal`.
-/
noncomputable def number_cotangent_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  exact P.cotangentEquivIdeal.symm.toAddEquiv.linearEquiv P.ResidueField

/--
The cotangent ideal carries the natural residue-field module structure.

Mathematically this is the scalar action of `𝓞_L / P` on `P / P ^ 2`, transported across
Mathlib's equivalence from `𝓞_L / P` to `P.ResidueField`.  It is a strictly smaller local
algebra task than constructing the tame character: it only supplies scalars on the cotangent
line, without discussing inertia or generators.
-/
lemma number_cotangent_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ _moduleInst : Module P.ResidueField P.cotangentIdeal, True := by
  exact
    ⟨number_residue_module (L := L) _hq P, trivial⟩

/-- Every residue-field element has an integral representative. -/
lemma number_residue_surjective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Function.Surjective
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  intro a
  obtain ⟨abar, habar⟩ :=
    (idealResidueMaximal P).surjective a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective abar
  refine ⟨r, ?_⟩
  rw [← habar, ← hr]
  change algebraMap (NumberField.RingOfIntegers L) P.ResidueField r =
    algebraMap (NumberField.RingOfIntegers L ⧸ P) P.ResidueField
      (Ideal.Quotient.mk P r)
  simp

/--
The cotangent action transported from the ideal model to Mathlib's quotient model
`P.Cotangent`.

This is only a change of model: apply the ideal-model action and then move across the linear
equivalence `P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent`.
-/
noncomputable def field_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.Cotangent → P.Cotangent := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let e :=
    number_cotangent_residue (L := L) hq P
  exact fun y =>
    e (cotangent_add_representation (L := L) P σ (e.symm y))

/-- The transported cotangent action agrees with the ideal-model action after applying `e`. -/
lemma number_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ
        (number_cotangent_residue (L := L) hq P z) =
      number_cotangent_residue (L := L) hq P
        (cotangent_add_representation (L := L) P σ z) := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  simp [field_inertia_cotangent]

/--
Integral representatives act on `P.Cotangent` by the usual scalar multiplication before
passing to the quotient.  This is the bridge from the residue-field scalar used in the tame
character argument back to Mathlib's `R`-linear quotient map `P.toCotangent`.
-/
lemma residue_smul_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • P.toCotangent x =
      P.toCotangent (r • x) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  have hscalar :
      (idealResidueMaximal P).symm
          (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) =
        algebraMap (NumberField.RingOfIntegers L)
          (NumberField.RingOfIntegers L ⧸ P) r := by
    rw [RingEquiv.symm_apply_eq]
    change algebraMap (NumberField.RingOfIntegers L) P.ResidueField r =
      algebraMap (NumberField.RingOfIntegers L ⧸ P) P.ResidueField
        (Ideal.Quotient.mk P r)
    simp
  change
    (idealResidueMaximal P).symm
        (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) •
        P.toCotangent x =
      P.toCotangent (r • x)
  rw [hscalar]
  rfl

/--
On `P.Cotangent`, multiplying by an integral representative is the same as multiplying by its
residue-field class.

This is the global form of `residue_smul_cotangent`: instead of checking only
on a chosen representative in `P`, it uses the quotient map `P.toCotangent` to reduce an arbitrary
cotangent vector to such a representative.  It is the scalar-compatibility input needed for the
denominator-removal step below.
-/
lemma number_smul_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) (y : P.Cotangent) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • y =
      r • y := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨x, rfl⟩ := P.toCotangent_surjective y
  rw [residue_smul_cotangent (L := L) hq P r x]
  rfl

/--
An element outside `P` maps to a nonzero element of the residue field.

This is the small residue-field fact behind denominator removal: the localization denominators
are exactly the elements of `P.primeCompl`, and such elements become units after passing to the
field `P.ResidueField`.
-/
lemma number_compl_ne
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (s : NumberField.RingOfIntegers L) ≠ 0 := by
  classical
  change
    ¬ algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (s : NumberField.RingOfIntegers L) = 0
  rw [Ideal.algebraMap_residueField_eq_zero]
  exact s.property

/--
Each localization denominator acts bijectively on the cotangent quotient.

Mathematically, this says that `P.Cotangent` is already local with respect to `P.primeCompl`.
Indeed, a denominator `s ∉ P` has a nonzero image in the field `P.ResidueField`; its inverse in
that field gives an inverse operator on the residue-vector space `P / P ^ 2`.
-/
lemma cotangent_compl_bijective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    Function.Bijective
      (fun y : P.Cotangent => (s : NumberField.RingOfIntegers L) • y) := by
  classical
  let R := NumberField.RingOfIntegers L
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let a : P.ResidueField := algebraMap R P.ResidueField (s : R)
  have ha : a ≠ 0 := by
    exact number_compl_ne (L := L) hq P s
  have hscalar :
      ∀ y : P.Cotangent, (s : R) • y = a • y := by
    intro y
    exact
      (number_smul_cotangent
        (L := L) hq P (s : R) y).symm
  constructor
  · intro x y hxy
    have hxy_residue : a • x = a • y := by
      simpa [hscalar x, hscalar y] using hxy
    calc
      x = (a⁻¹ * a) • x := by
        rw [inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • (a • x) := by
        rw [smul_smul]
      _ = a⁻¹ • (a • y) := by
        rw [hxy_residue]
      _ = (a⁻¹ * a) • y := by
        rw [smul_smul]
      _ = y := by
        rw [inv_mul_cancel₀ ha, one_smul]
  · intro y
    refine ⟨a⁻¹ • y, ?_⟩
    calc
      (s : R) • (a⁻¹ • y) = a • (a⁻¹ • y) := by
        rw [hscalar]
      _ = (a * a⁻¹) • y := by
        rw [smul_smul]
      _ = y := by
        rw [mul_inv_cancel₀ ha, one_smul]

/--
The bijective action of a denominator is an automorphism of the residue-vector space.

This packages the preceding bijectivity in the form used by localization: scalar multiplication by
any `s ∈ P.primeCompl` is an invertible `P.ResidueField`-linear map on `P.Cotangent`.
-/
noncomputable def cotangent_compl_aut
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.Cotangent ≃ₗ[P.ResidueField] P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let a : P.ResidueField := algebraMap R P.ResidueField (s : R)
  have hscalar :
      ∀ y : P.Cotangent, (s : R) • y = a • y := by
    intro y
    exact
      (number_smul_cotangent
        (L := L) hq P (s : R) y).symm
  have hbij_a : Function.Bijective (fun y : P.Cotangent => a • y) := by
    have hbij_s :=
      cotangent_compl_bijective (L := L) hq P s
    constructor
    · intro x y hxy
      exact hbij_s.1 (by simpa [hscalar x, hscalar y] using hxy)
    · intro y
      obtain ⟨x, hx⟩ := hbij_s.2 y
      exact ⟨x, by simpa [hscalar x] using hx⟩
  let f : P.Cotangent →ₗ[P.ResidueField] P.Cotangent := {
    toFun := fun y => a • y
    map_add' := by
      intro x y
      simp [smul_add]
    map_smul' := by
      intro b y
      simp [smul_smul, mul_comm]
  }
  exact LinearEquiv.ofBijective f hbij_a

/--
The identity map realizes `P.Cotangent` as its own localization away from `P`.

This is the formal localization version of the previous denominator calculation.  The only
nontrivial field of `IsLocalizedModule` is `map_units`: every denominator in `P.primeCompl` acts
bijectively on `P.Cotangent`, so the corresponding endomorphism is a unit.  Surjectivity and the
kernel condition are immediate for the identity map.
-/
lemma cotangent_localized_id
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    IsLocalizedModule P.primeCompl (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) := by
  classical
  let R := NumberField.RingOfIntegers L
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    simpa [Module.algebraMap_end_apply] using
      (cotangent_compl_bijective (L := L) hq P s)
  · intro y
    exact ⟨⟨y, 1⟩, by simp⟩
  · intro x₁ x₂ h
    exact ⟨1, by simpa using h⟩

/--
The natural map from `P.Cotangent` to its localized module is an `R`-linear equivalence.

After the preceding `IsLocalizedModule` instance, this is just Mathlib's uniqueness statement for
localized modules applied to the identity map.  It packages the denominator-removal fact before
base-changing to the tensor product.
-/
noncomputable def number_localized_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    P.Cotangent ≃ₗ[R] LocalizedModule P.primeCompl P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  haveI :
      IsLocalizedModule P.primeCompl
        (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) :=
    cotangent_localized_id (L := L) hq P
  exact
    (IsLocalizedModule.iso P.primeCompl
      (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent)).symm

/--
The localized-module equivalence sends a cotangent vector to the fraction with denominator `1`.
-/
lemma cotangent_localized_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (y : P.Cotangent) :
    number_localized_module (L := L) hq P y =
      LocalizedModule.mk y (1 : P.primeCompl) := by
  classical
  let R := NumberField.RingOfIntegers L
  haveI :
      IsLocalizedModule P.primeCompl
        (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) :=
    cotangent_localized_id (L := L) hq P
  simpa [number_localized_module] using
    (IsLocalizedModule.iso_symm_apply
      (S := P.primeCompl)
      (f := (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent))
      y)

/--
The denominator-removal equivalence after rewriting the localization as a tensor product.

This is still only an `R`-linear statement, not yet the final semilinear residue-field statement.
It is nevertheless the exact additive equivalence underlying the missing proof: a cotangent class
is sent to `1 ⊗ y`.
-/
noncomputable def cotangent_tensor_localization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    P.Cotangent ≃ₗ[R] TensorProduct R Rₚ P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let eLoc : P.Cotangent ≃ₗ[R] LocalizedModule P.primeCompl P.Cotangent :=
    number_localized_module (L := L) hq P
  let eTensor :
      LocalizedModule P.primeCompl P.Cotangent ≃ₗ[Rₚ] TensorProduct R Rₚ P.Cotangent :=
    LocalizedModule.equivTensorProduct P.primeCompl P.Cotangent
  exact eLoc.trans (eTensor.restrictScalars R)

/-- The tensor-product denominator-removal equivalence is the expected map `y ↦ 1 ⊗ y`. -/
lemma number_cotangent_localization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (y : P.Cotangent) :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    cotangent_tensor_localization (L := L) hq P y =
      (1 : Rₚ) ⊗ₜ[R] y := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  simp [
    cotangent_tensor_localization,
    cotangent_localized_module,
    Localization.mk_one_eq_algebraMap]

/-- The transported inertia action sends a cotangent representative to the translated one. -/
lemma number_field_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ (P.toCotangent x) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_smul_prime (L := L) P σ x.property⟩ := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  change
    P.cotangentEquivIdeal.symm
        (field_cotangent_ideal (L := L) P σ
          (P.cotangentEquivIdeal (P.toCotangent x))) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_smul_prime (L := L) P σ x.property⟩
  have hsource :
      P.cotangentEquivIdeal (P.toCotangent x) =
        ⟨Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L), by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact x.property⟩ := by
    ext
    simp
  rw [hsource]
  rw [number_cotangent_mk
    (L := L) P σ (x : NumberField.RingOfIntegers L) x.property]
  exact
    Ideal.cotangentEquivIdeal_symm_apply
      (I := P) ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L))
      (number_smul_prime (L := L) P σ x.property)

/--
The concrete error term in the scalar-compatibility calculation lies in `P ^ 2`.

The difference between applying inertia to `r * x` and multiplying the translated `x` by `r`
is `(σ r - r) * σ x`; the first factor lies in `P` because `σ` is inertia, and the second
factor lies in `P` because inertia stabilizes `P`.
-/
lemma inertia_smul_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (r : NumberField.RingOfIntegers L) (x : P) :
    ((σ : Gal(L/ℚ)) • (r * (x : NumberField.RingOfIntegers L))) -
        r * ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2 := by
  classical
  have hσr :
      ((σ : Gal(L/ℚ)) • r) - r ∈ P := by
    exact number_smul_sub (L := L) P σ r
  have hσx :
      ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P := by
    exact number_smul_prime (L := L) P σ x.property
  have hprod :
      (((σ : Gal(L/ℚ)) • r) - r) *
          ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hσr hσx
  convert hprod using 1
  rw [smul_mul']
  ring

/--
Representative-level scalar compatibility for the transported cotangent action.

This is the remaining concrete local calculation for linearity: for an integral scalar `r` and
an element `x ∈ P`, inertia fixes the residue of `r`, so its action on `r • x` agrees modulo
`P ^ 2` with multiplying the transformed cotangent vector by the same residue scalar.
-/
lemma inertia_cotangent_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (r : NumberField.RingOfIntegers L) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ
        ((algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • P.toCotangent x) =
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) •
        field_inertia_cotangent (L := L) hq P σ (P.toCotangent x) := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  rw [residue_smul_cotangent (L := L) hq P r x]
  rw [number_field_cotangent (L := L) hq P σ (r • x)]
  rw [number_field_cotangent (L := L) hq P σ x]
  rw [residue_smul_cotangent]
  apply (P.toCotangent_eq).mpr
  change
    ((σ : Gal(L/ℚ)) • (r * (x : NumberField.RingOfIntegers L))) -
        r * ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2
  exact inertia_smul_sq (L := L) P σ r x

/-- The transported cotangent action is residue-field linear on `P.Cotangent`. -/
lemma number_cotangent_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (a : P.ResidueField) (y : P.Cotangent) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ (a • y) =
      a • field_inertia_cotangent (L := L) hq P σ y := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨r, rfl⟩ :=
    number_residue_surjective (L := L) hq P a
  obtain ⟨x, hx⟩ := P.toCotangent_surjective y
  rw [← hx]
  exact
    inertia_cotangent_smul
      (L := L) hq P σ r x

/--
The additive cotangent representation is linear for the natural residue-field scalar action.

The mathematical input is that inertia acts trivially on `𝓞_L / P`; hence applying an inertia
element to a scalar times a cotangent vector gives the same residue scalar times the transformed
cotangent vector.
-/
lemma cotangent_representation_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    additiveRepresentationModule
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal)
      (number_residue_module (L := L) _hq P)
      (cotangent_add_representation (L := L) P) := by
  classical
  letI : AddCommGroup P.cotangentIdeal :=
    Submodule.addCommGroup P.cotangentIdeal
  let moduleInstIdeal : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) _hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInstIdeal
  letI : SMul P.ResidueField P.cotangentIdeal := moduleInstIdeal.toSMul
  let moduleInstCotangent : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) _hq P
  letI : Module P.ResidueField P.Cotangent := moduleInstCotangent
  letI : SMul P.ResidueField P.Cotangent := moduleInstCotangent.toSMul
  change
    ∀ σ : P.inertia (Gal(L/ℚ)), ∀ a : P.ResidueField, ∀ z : P.cotangentIdeal,
    cotangent_add_representation (L := L) P σ (a • z) =
      a • cotangent_add_representation (L := L) P σ z
  intro σ a z
  let e : P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent :=
    number_cotangent_residue (L := L) _hq P
  apply e.injective
  calc
    e (cotangent_add_representation (L := L) P σ (a • z)) =
        field_inertia_cotangent (L := L) _hq P σ (e (a • z)) := by
          exact
            (number_inertia_cotangent
              (L := L) _hq P σ (a • z)).symm
    _ =
        field_inertia_cotangent (L := L) _hq P σ (a • e z) := by
          exact congrArg (field_inertia_cotangent (L := L) _hq P σ)
            (map_smul e a z)
    _ =
        a • field_inertia_cotangent (L := L) _hq P σ (e z) := by
          exact
            number_cotangent_smul
              (L := L) _hq P σ a (e z)
    _ =
        a • e (cotangent_add_representation (L := L) P σ z) := by
          exact congrArg (fun y => a • y)
            (number_inertia_cotangent
              (L := L) _hq P σ z)
    _ =
        e (a • cotangent_add_representation (L := L) P σ z) := by
          exact (map_smul e a
            (cotangent_add_representation (L := L) P σ z)).symm

/--
The additive cotangent representation, after installing the residue-field module structure, is a
linear representation with the same kernel.
-/
lemma inertia_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    ∃ ρlin :
        P.inertia (Gal(L/ℚ)) →*
          P.cotangentIdeal ≃ₗ[P.ResidueField] P.cotangentIdeal,
      ρlin.ker =
        (cotangent_add_representation (L := L) P).ker := by
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have hsmul :
      additiveRepresentationModule
        (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
        (V := P.cotangentIdeal)
        (number_residue_module (L := L) hq P)
        (cotangent_add_representation (L := L) P) := by
    exact
      cotangent_representation_smul
        (L := L) hq P
  exact
    additive_representation_linear
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal)
      (cotangent_add_representation (L := L) P)
      hsmul

/--
In a one-dimensional vector space, any nonzero vector spans.

This is the abstract linear-algebra part of the cotangent-generator argument.  The local
arithmetic input should only have to prove that the cotangent space has dimension one; once that
is known, this lemma turns any nonzero cotangent vector into the spanning vector needed for the
one-dimensional character construction.
-/
lemma dimensional_module_spans
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hfinrank : Module.finrank K V = 1) {v : V} (hv : v ≠ 0) :
    dimensionalSpansElement
      (K := K) (V := V) (inferInstance : Module K V) v := by
  intro w
  exact exists_smul_eq_of_finrank_eq_one (K := K) (V := V) hfinrank hv w

/--
A one-dimensional vector space has a nonzero spanning vector.

This packages the preceding lemma with the existence of a nonzero vector when the finrank is
positive.  It is deliberately independent of any number-field facts, so the remaining arithmetic
work can focus solely on proving the cotangent finrank computation.
-/
lemma dimensional_spans_finrank
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hfinrank : Module.finrank K V = 1) :
    ∃ v : V,
      v ≠ 0 ∧
        dimensionalSpansElement
          (K := K) (V := V) (inferInstance : Module K V) v := by
  classical
  have hpos : 0 < Module.finrank K V := by
    rw [hfinrank]
    exact zero_lt_one
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := K) (M := V) hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨v, ?_, ?_⟩
  · exact hv
  · exact dimensional_module_spans hfinrank hv

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/--
Finrank is unchanged by a semilinear equivalence over an isomorphism of scalar rings.

Mathlib has the corresponding cardinal-rank statement
`lift_rank_eq_of_equiv_equiv`.  This wrapper is the exact finite-dimensional form needed for
transporting the cotangent-space computation from the residue field of `P` to the residue field
of the localization at `P`.
-/
lemma finrank_semilinear_equiv
    {K K' V V' : Type*}
    [Semiring K] [Semiring K'] [AddCommMonoid V] [Module K V]
    [AddCommMonoid V'] [Module K' V']
    (σ : K ≃+* K') (e : V ≃ₛₗ[(σ : K →+* K')] V') :
    Module.finrank K V = Module.finrank K' V' := by
  unfold Module.finrank
  simpa only [Cardinal.toNat_lift] using
    congrArg Cardinal.toNat
      (lift_rank_eq_of_equiv_equiv (fun x : K => σ x) e.toAddEquiv σ.bijective
        (by
          intro r x
          exact e.map_smulₛₗ r x))

/--
The global residue field agrees with the residue field of the localization at `P`.

Mathlib provides the quotient equivalence `𝓞_L / P ≃ (𝓞_L)_P / P(𝓞_L)_P`; this definition
composes it with the existing identification of `𝓞_L / P` with `P.ResidueField`.  This is the
scalar-field part of transporting the local DVR cotangent computation back to the global
quotient `P / P ^ 2`.
-/
noncomputable def number_localization_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.ResidueField ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    (idealResidueMaximal P).symm.trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P))

/--
The residue-field equivalence sends an integral residue class to the corresponding local residue
class.

This is the scalar-field compatibility needed when comparing `P / P ^ 2` with the local cotangent
space: the class of `r ∈ 𝓞_L` in `P.ResidueField` becomes the class of `r / 1` in the residue
field of `(𝓞_L)_P`.
-/
lemma number_localization_algebra
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    number_localization_prime (L := L) hq P
        (algebraMap R P.ResidueField r) =
      algebraMap Rₚ (IsLocalRing.ResidueField Rₚ) (algebraMap R Rₚ r) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  change
    number_localization_prime (L := L) hq P
        (algebraMap R P.ResidueField r) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rₚ) (algebraMap R Rₚ r)
  rw [number_localization_prime]
  change
    IsLocalization.AtPrime.equivQuotMaximalIdeal P Rₚ
        ((idealResidueMaximal P).symm
          (algebraMap R P.ResidueField r)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rₚ) (algebraMap R Rₚ r)
  have hpre :
      (idealResidueMaximal P).symm
          (algebraMap R P.ResidueField r) =
        Ideal.Quotient.mk P r := by
    rw [RingEquiv.symm_apply_eq]
    change algebraMap R P.ResidueField r =
      algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P r)
    rfl
  rw [hpre]
  rfl

/--
On the local cotangent space, a scalar from the local residue field represented
by `x : Rₚ` acts as multiplication by `x`.

This is just the standard scalar tower
`Rₚ → IsLocalRing.ResidueField Rₚ → IsLocalRing.CotangentSpace Rₚ`, but it is
useful to have the exact statement available for the semilinearity calculation.
-/
lemma smul_cotangent_space
    (R : Type*) [CommRing R] [IsLocalRing R]
    (x : R) (z : IsLocalRing.CotangentSpace R) :
    (algebraMap R (IsLocalRing.ResidueField R) x) • z = x • z := by
  exact algebraMap_smul (IsLocalRing.ResidueField R) x z

/--
The extension of `P` to the localization at `P` is the maximal ideal of the local ring.

This is the ideal-theoretic anchor for the cotangent comparison: after localizing at `P`, the
local cotangent space is the quotient of exactly the extension of the original prime ideal.
-/
lemma number_localization_maximal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    P.map (algebraMap (NumberField.RingOfIntegers L) Rₚ) =
      IsLocalRing.maximalIdeal Rₚ := by
  classical
  let Rₚ := Localization.AtPrime P
  exact Localization.AtPrime.map_eq_maximalIdeal (I := P)

/--
After localizing the ring of integers at a prime above `(q)`, the local cotangent space has
dimension one.

This is the actual DVR theorem supplied by Mathlib.  The prime `P` is nonzero because it lies
over the nonzero rational prime ideal `(q)`, and the localization of the Dedekind domain
`𝓞_L` at such a prime is a discrete valuation ring.
-/
lemma localization_cotangent_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
  classical
  let Rₚ := Localization.AtPrime P
  have hp_ne_bot :
      Ideal.rationalPrimeIdeal q ≠ ⊥ := by
    exact rational_ne_bot hq
  have hP_ne_bot :
      P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers L) hP_ne_bot Rₚ
  exact IsLocalRing.finrank_CotangentSpace_eq_one Rₚ

/--
Equal ideals have canonically linearly equivalent cotangent quotients.

This is a small bookkeeping lemma for moving between Mathlib's literal local cotangent space
`(maximalIdeal R).Cotangent` and an equal ideal presented in a different way, such as the image of
`P` in the localization at `P`.
-/
noncomputable def idealCotangentLinear
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst h
  exact LinearEquiv.refl R I.Cotangent

/--
An algebra equivalence carries an ideal cotangent quotient to the cotangent quotient of the
image ideal.

This is the functoriality of `I / I ^ 2` for an isomorphism of ambient algebras.  The proof uses
Mathlib's `Ideal.mapCotangent` in both directions and checks the two maps on representatives
coming from `Ideal.toCotangent`.
-/
noncomputable def idealCotangentAlg
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map (e : A →+* B)).Cotangent := by
  classical
  let J : Ideal B := I.map (e : A →+* B)
  let f : I.Cotangent →ₗ[R] J.Cotangent :=
    Ideal.mapCotangent I J e.toAlgHom Ideal.le_comap_map
  have hJ_le : J ≤ I.comap (e.symm : B →+* A) := by
    rw [← Ideal.map_le_iff_le_comap]
    have hmap : J.map (e.symm : B →+* A) = I := by
      dsimp [J]
      rw [Ideal.map_map]
      have hcomp : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by
        ext x
        exact e.left_inv x
      rw [hcomp, Ideal.map_id]
    exact hmap.le
  let g : J.Cotangent →ₗ[R] I.Cotangent :=
    Ideal.mapCotangent J I e.symm.toAlgHom hJ_le
  refine LinearEquiv.ofLinear f g ?_ ?_
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective J x
    simp [f, g, J, Ideal.mapCotangent_toCotangent]
  · ext y
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I y
    simp [f, g, J, Ideal.mapCotangent_toCotangent]

/--
The cotangent quotient of the extended prime ideal is the local cotangent space.

The proof is only the ideal equality `P.map = maximalIdeal`; no localization exactness is hidden
here.  This separates the easy ideal-identification part of the cotangent comparison from the
harder base-change statement.
-/
noncomputable def localization_mapped_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    (P.map (algebraMap R Rₚ)).Cotangent ≃ₗ[Rₚ] IsLocalRing.CotangentSpace Rₚ := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  exact
    idealCotangentLinear
      (P.map (algebraMap R Rₚ))
      (IsLocalRing.maximalIdeal Rₚ)
      (number_localization_maximal (L := L) hq P)

/--
Mathlib's flat base-change theorem gives the cotangent quotient after tensoring with the
localization.

The target is still written as an ideal of `Rₚ ⊗[R] R`; the separate right-identity transport
from that tensor product ring to `Rₚ` is the next algebraic bookkeeping step.
-/
noncomputable def cotangent_localization_change
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P;
    TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
      (P.map
        (Algebra.TensorProduct.includeRight.toRingHom :
          NumberField.RingOfIntegers L →+*
            TensorProduct
              (NumberField.RingOfIntegers L) Rₚ (NumberField.RingOfIntegers L))).Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  haveI : Module.Flat R Rₚ := IsLocalization.flat Rₚ P.primeCompl
  exact P.tensorCotangentEquiv R Rₚ

/--
Base-changing `P / P ^ 2` to the localization gives the local cotangent space.

Compared with the final semilinear comparison below, this statement has no
residue-field scalar transport from `P.ResidueField`; it only says that the
localized tensor product computes the local cotangent space over `Rₚ`. The
remaining proof is the right-identity transport `Rₚ ⊗[R] R ≃ Rₚ` applied to the
base-changed ideal.
-/
lemma tensor_cotangent_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P;
    Nonempty
      (TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let eTensor :
      TensorProduct R Rₚ P.Cotangent ≃ₗ[Rₚ]
        (P.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            R →+* TensorProduct R Rₚ R)).Cotangent :=
    cotangent_localization_change (L := L) hq P
  let eMax :
      (P.map (algebraMap R Rₚ)).Cotangent ≃ₗ[Rₚ] IsLocalRing.CotangentSpace Rₚ :=
    localization_mapped_space
      (L := L) hq P
  let eRid : TensorProduct R Rₚ R ≃ₐ[Rₚ] Rₚ :=
    Algebra.TensorProduct.rid R Rₚ Rₚ
  let J : Ideal (TensorProduct R Rₚ R) :=
    P.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* TensorProduct R Rₚ R)
  let eRidCotangent :
      J.Cotangent ≃ₗ[Rₚ]
        (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ)).Cotangent :=
    idealCotangentAlg eRid J
  have hRidMap :
      J.map (eRid : TensorProduct R Rₚ R →+* Rₚ) =
        P.map (algebraMap R Rₚ) := by
    dsimp [J, eRid]
    rw [Ideal.map_map]
    congr 1
    ext x
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
  let eRidMap :
      (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ)).Cotangent ≃ₗ[Rₚ]
        (P.map (algebraMap R Rₚ)).Cotangent :=
    idealCotangentLinear
      (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ))
      (P.map (algebraMap R Rₚ))
      hRidMap
  exact ⟨eTensor.trans (eRidCotangent.trans (eRidMap.trans eMax))⟩

/--
The original quotient `P / P ^ 2` is the same residue-vector space as its localization.

This isolates the second remaining ingredient in the localization comparison.  Once a linear
equivalence from the localized tensor product to the local cotangent space is fixed, it transports
the residue-field scalar action back to the tensor product; the missing claim is that the map
`x ↦ 1 ⊗ x` is then semilinearly bijective over the standard residue-field equivalence.
-/
lemma localization_semilinear_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (eBase :
      let Rₚ := Localization.AtPrime P;
      TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
        IsLocalRing.CotangentSpace Rₚ) :
    let Rₚ := Localization.AtPrime P;
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P;
    letI : Module (IsLocalRing.ResidueField Rₚ)
        (TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent) :=
      eBase.toAddEquiv.module (IsLocalRing.ResidueField Rₚ);
    Nonempty
      (P.Cotangent ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent) := by
  /-
  This is the denominator-removal part of localization.  Since every `s ∉ P` maps to a unit in
  both residue fields, and `P` annihilates `P.Cotangent`, the localization map
  `x ↦ 1 ⊗ x` is bijective after transporting scalars through the local cotangent equivalence.
  -/
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let Kₚ := IsLocalRing.ResidueField Rₚ
  let σ : P.ResidueField ≃+* Kₚ :=
    number_localization_prime (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  letI : Module Kₚ (TensorProduct R Rₚ P.Cotangent) :=
    eBase.toAddEquiv.module Kₚ
  let eTensor : P.Cotangent ≃ₗ[R] TensorProduct R Rₚ P.Cotangent :=
    cotangent_tensor_localization (L := L) hq P
  let eSemilinear :
      P.Cotangent ≃ₛₗ[(σ : P.ResidueField →+* Kₚ)]
        TensorProduct R Rₚ P.Cotangent := {
    toFun := eTensor
    invFun := eTensor.symm
    left_inv := eTensor.left_inv
    right_inv := eTensor.right_inv
    map_add' := eTensor.map_add
    map_smul' := by
      intro a y
      obtain ⟨r, hr⟩ :=
        number_residue_surjective (L := L) hq P a
      rw [← hr]
      apply eBase.injective
      calc
        eBase
            (eTensor
              ((algebraMap R P.ResidueField r) • y)) =
            eBase (eTensor (r • y)) := by
              rw [number_smul_cotangent (L := L) hq P r y]
        _ = eBase (r • eTensor y) := by
              rw [map_smul]
        _ = eBase ((algebraMap R Rₚ r) • eTensor y) := by
              rw [algebraMap_smul Rₚ r (eTensor y)]
        _ = (algebraMap R Rₚ r) • eBase (eTensor y) := by
              rw [map_smul]
        _ =
            (algebraMap Rₚ Kₚ (algebraMap R Rₚ r)) •
              eBase (eTensor y) := by
              rw [smul_cotangent_space]
        _ =
            σ (algebraMap R P.ResidueField r) •
              eBase (eTensor y) := by
              rw [
                number_localization_algebra
                  (L := L) hq P r]
        _ =
            eBase
              (σ (algebraMap R P.ResidueField r) •
                eTensor y) := by
              simp [Equiv.smul_def]
  }
  exact ⟨eSemilinear⟩

/--
The quotient model `P.Cotangent` identifies with the cotangent space of the local ring at `P`,
semilinearly over the natural residue-field equivalence.

This is now the only remaining localization-transport input in the cotangent finrank argument.
It is smaller than the previous transport statement because it no longer mentions the ideal model
`P.cotangentIdeal` or finrank at all.  The intended construction is:

1. Use flat base change for cotangent spaces to compare
   `Localization.AtPrime P ⊗[𝓞_L] P.Cotangent` with the cotangent space of
   `P.map (algebraMap _ (Localization.AtPrime P))`.
2. Replace that extended ideal by the maximal ideal using
   `number_localization_maximal`.
3. Use that `P` annihilates `P.Cotangent`, so localizing away from `P` only changes scalars from
   `𝓞_L / P` to the residue field of the localization.
4. Compose the scalar-field identification with
   `number_localization_prime`.

Each of these ingredients is a standard exactness/localization fact; packaging them here isolates
the actual missing algebra from the surrounding linear-algebra bookkeeping.
-/
lemma localization_space_semilinear
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    Nonempty
      (P.Cotangent ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  obtain ⟨eBase⟩ :=
    tensor_cotangent_nonempty
      (L := L) hq P
  letI : Module (IsLocalRing.ResidueField Rₚ) (TensorProduct R Rₚ P.Cotangent) :=
    eBase.toAddEquiv.module (IsLocalRing.ResidueField Rₚ)
  obtain ⟨eSource⟩ :=
    localization_semilinear_nonempty
      (L := L) hq P eBase
  let eBaseResidue :
      TensorProduct R Rₚ P.Cotangent ≃ₗ[IsLocalRing.ResidueField Rₚ]
        IsLocalRing.CotangentSpace Rₚ :=
    eBase.toAddEquiv.linearEquiv (IsLocalRing.ResidueField Rₚ)
  exact ⟨eSource.trans eBaseResidue⟩

/--
The ideal model `P.cotangentIdeal` identifies with the local cotangent space, semilinearly over the
natural residue-field equivalence.

This is just the previous localization comparison composed with Mathlib's equivalence between the
quotient model `P.Cotangent` and the ideal model `P.cotangentIdeal`.  Keeping this as a separate
lemma records that the quotient-localization comparison is now complete before the finrank
transport step.
-/
lemma space_semilinear_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Nonempty
      (P.cotangentIdeal ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨eCotangent⟩ :=
    localization_space_semilinear
      (L := L) hq P
  let eIdeal : P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent :=
    number_cotangent_residue (L := L) hq P
  exact ⟨eIdeal.trans eCotangent⟩

/--
The global cotangent quotient and the localized cotangent space have the same dimension.

The residue fields are identified by
`number_localization_prime`; the module comparison sends the
class of `x ∈ P` in `P / P ^ 2` to the class of `x / 1` in the maximal ideal of
`(𝓞_L)_P` modulo its square.  Since all denominators outside `P` are already units modulo `P`,
localization does not change this one-step cotangent quotient.
-/
lemma cotangent_localization_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal =
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  let σ : P.ResidueField ≃+* IsLocalRing.ResidueField Rₚ :=
    number_localization_prime (L := L) hq P
  obtain ⟨e⟩ :=
    space_semilinear_nonempty
      (L := L) hq P
  exact finrank_semilinear_equiv σ e

/--
The cotangent ideal has residue-field dimension at most one.

This is the principal-maximal-ideal half of the DVR input.  After localizing the ring of
integers at `P`, Mathlib's local-ring theorem
`IsLocalRing.finrank_cotangentSpace_le_one_iff` reduces this to the fact that a nonzero prime of
a Dedekind domain has principal maximal ideal after localization.
-/
lemma cotangent_residue_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal ≤ 1 := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have htransport :
      Module.finrank P.ResidueField P.cotangentIdeal =
        Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
    exact
      cotangent_localization_space
        (L := L) hq P
  have hlocal :
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
    exact localization_cotangent_space (L := L) hq P
  rw [htransport, hlocal]

/--
The cotangent ideal is nonzero over the residue field.

This is the non-idempotence half of the DVR input.  Equivalently, `P ≠ P ^ 2`: after localizing
at the nonzero prime `P`, the maximal ideal of the DVR is not zero, so a uniformizer gives a
class in `P / P ^ 2` that does not vanish.
-/
lemma number_cotangent_pos
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    0 < Module.finrank P.ResidueField P.cotangentIdeal := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have htransport :
      Module.finrank P.ResidueField P.cotangentIdeal =
        Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
    exact
      cotangent_localization_space
        (L := L) hq P
  have hlocal :
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
    exact localization_cotangent_space (L := L) hq P
  rw [htransport, hlocal]
  exact zero_lt_one

/--
The cotangent ideal has residue-field dimension exactly one.

The two preceding local inputs are the two independent DVR facts needed here: principal maximal
ideal gives the upper bound, and non-idempotence gives nonzero cotangent.  This lemma is the
precise arithmetic statement from which the generator exists by pure linear algebra.
-/
lemma number_cotangent_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal = 1 := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have hle :
      Module.finrank P.ResidueField P.cotangentIdeal ≤ 1 := by
    exact cotangent_residue_finrank (L := L) hq P
  have hpos :
      0 < Module.finrank P.ResidueField P.cotangentIdeal := by
    exact number_cotangent_pos (L := L) hq P
  exact le_antisymm hle (Nat.succ_le_of_lt hpos)

/--
The cotangent ideal is one-dimensional and nonzero over the residue field.

Equivalently, `P / P ^ 2` has a nonzero generator as a vector space over
`𝓞_L / P`. This is the Dedekind-domain/DVR input that a nonzero prime of the
ring of integers becomes principal after localizing at itself.
-/
lemma cotangent_residue_generator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ v : P.cotangentIdeal,
      v ≠ 0 ∧
        dimensionalSpansElement
          (K := P.ResidueField) (V := P.cotangentIdeal)
          (number_residue_module (L := L) _hq P) v := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) _hq P
  have hfinrank :
      Module.finrank P.ResidueField P.cotangentIdeal = 1 := by
    exact number_cotangent_finrank (L := L) _hq P
  exact
    dimensional_spans_finrank
      (K := P.ResidueField) (V := P.cotangentIdeal) hfinrank

/--
The local data needed to view the cotangent action as a one-dimensional linear
representation over the residue field.

This is the remaining local algebra behind the scalar construction: build the
natural `P.ResidueField`-module structure on `P / P ^ 2`, prove the inertia
action is linear for it, and choose a nonzero spanning cotangent vector.
-/
lemma cotangent_line_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ moduleInst : Module P.ResidueField P.cotangentIdeal,
      letI : Module P.ResidueField P.cotangentIdeal := moduleInst
      ∃ ρlin :
          P.inertia (Gal(L/ℚ)) →*
            P.cotangentIdeal ≃ₗ[P.ResidueField] P.cotangentIdeal,
        ρlin.ker =
            (cotangent_add_representation (L := L) P).ker ∧
          ∃ v : P.cotangentIdeal,
            v ≠ 0 ∧
              dimensionalSpansElement
                (K := P.ResidueField) (V := P.cotangentIdeal) moduleInst v := by
  let moduleInst : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  refine ⟨moduleInst, ?_⟩
  letI : Module P.ResidueField P.cotangentIdeal := moduleInst
  obtain ⟨ρlin, hρlinKer⟩ :=
    inertia_cotangent_representation
      (L := L) hq P
  obtain ⟨v, hv_ne_zero, hv_span⟩ :=
    cotangent_residue_generator
      (L := L) hq P
  exact ⟨ρlin, hρlinKer, v, hv_ne_zero, hv_span⟩

/--
The scalar character attached to the additive cotangent representation.

The remaining construction is linear algebra over the residue field: identify `P / P ^ 2` as
a one-dimensional `P.ResidueField`-vector space and show every additive automorphism coming
from inertia is multiplication by a unique nonzero scalar.  The resulting scalar is the tame
inertia character, and this statement records that its kernel is exactly the kernel of the
additive cotangent representation.
-/
lemma tame_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      χ.ker =
        (cotangent_add_representation (L := L) P).ker := by
  obtain ⟨moduleInst, hdata⟩ :=
    cotangent_line_representation (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInst
  obtain ⟨ρlin, hρlinKer, v, hv_ne_zero, hv_span⟩ := hdata
  obtain ⟨χ, hχKer⟩ :=
    dimensional_spans_element
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal) ρlin v hv_ne_zero hv_span
  refine ⟨χ, ?_⟩
  rw [hχKer, hρlinKer]

/--
The cotangent-line tame character.

The intended construction is the scalar by which an inertia element acts on the one-dimensional
`P.ResidueField`-vector space `P / P ^ 2`.  The kernel is therefore the subgroup acting
trivially on the cotangent ideal.  This isolates the linear-algebra/Dedekind-domain part of
the usual uniformizer construction from the separate ramification-filtration statement that
identifies this fixed subgroup with wild inertia.
-/
lemma tame_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      ∀ σ : P.inertia (Gal(L/ℚ)),
        σ ∈ χ.ker ↔
          ∀ z : P.cotangentIdeal,
            field_cotangent_ideal (L := L) P σ z = z := by
  obtain ⟨χ, hχKer⟩ :=
    tame_cotangent_representation
      (L := L) hq P
  refine ⟨χ, ?_⟩
  intro σ
  rw [hχKer]
  exact
    cotangent_representation_ker
      (L := L) P σ

/--
For inertia, fixing the cotangent ideal is equivalent to being wild.

The reverse implication is already formalized in
`wild_cotangent_fixed`.  The forward implication is the
standard local fact that the first ramification group is the kernel of the action on
`P / P ^ 2`; equivalently, an inertia element whose action on the residue field and cotangent
line is trivial acts trivially on `𝓞_L ⧸ P ^ 2`.
-/
lemma inertia_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    (∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z) ↔
      σ ∈ number_wild_subgroup (L := L) P := by
  constructor
  · intro hσ
    have hKer :
        σ ∈ (cotangent_add_representation (L := L) P).ker := by
      exact
        (cotangent_representation_ker
          (L := L) P σ).2 hσ
    exact
      (number_cotangent_wild
        (L := L) hq P) hKer
  · intro hσ
    have hKer :
        σ ∈ (cotangent_add_representation (L := L) P).ker := by
      exact
        wild_cotangent_representation
          (L := L) P hσ
    exact
      (cotangent_representation_ker
        (L := L) P σ).1 hKer

/--
If the cotangent-line character has the expected fixed-action kernel, then its kernel is wild.

This is just the assembly step joining the scalar character on `P / P ^ 2` with the local
identification of cotangent-fixed inertia and wild inertia.
-/
lemma tame_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ)
    (hχ : ∀ σ : P.inertia (Gal(L/ℚ)),
      σ ∈ χ.ker ↔
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z) :
    χ.ker = number_wild_subgroup (L := L) P := by
  ext σ
  constructor
  · intro hσ
    have hfixed :
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z := by
      exact (hχ σ).1 hσ
    exact
      (inertia_cotangent_wild
        (L := L) hq P σ).1 hfixed
  · intro hσ
    have hfixed :
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z := by
      exact
        (inertia_cotangent_wild
          (L := L) hq P σ).2 hσ
    exact (hχ σ).2 hfixed

/--
The tame inertia character has wild inertia as its kernel.

This is the uniformizer construction: choose a uniformizer `π` in `Localization.AtPrime P` and
send `σ` to the residue of the unit `σ(π) / π`.  The kernel condition says precisely that `σ`
acts trivially on `P / P ^ 2`, equivalently that it lies in
`number_wild_subgroup`.
-/
lemma tame_uniformizer_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      χ.ker = number_wild_subgroup (L := L) P := by
  obtain ⟨χ, hχ⟩ :=
    tame_inertia_cotangent
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    tame_cotangent_wild
      (L := L) hq P χ hχ

/-- Membership of a natural number in the rational prime ideal `(q)`. -/
lemma rational_nat_cast {q n : ℕ} :
    (n : ℤ) ∈ Ideal.rationalPrimeIdeal q ↔ q ∣ n := by
  rw [Ideal.rationalPrimeIdeal]
  rw [Ideal.mem_span_singleton]
  exact Int.natCast_dvd_natCast

/--
If `P` lies over `(q)`, then the element `q` of the ring of integers lies in `P`.

This is the elementary bridge from the global rational prime to the local maximal ideal.
-/
lemma number_rational_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (q : ℕ)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (q : NumberField.RingOfIntegers L) ∈ P := by
  have hqInt :
      (q : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact rational_nat_cast.mpr dvd_rfl
  have hqAlg :
      algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈ P := by
    exact
      (Ideal.mem_of_liesOver
        (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (q : ℤ))).1 hqInt
  simpa [Int.cast_natCast] using hqAlg

/--
The kernel of `ℕ → P.ResidueField` is exactly the divisibility relation by `q`.

This is the residue-field characteristic statement in its most useful computational form.
-/
lemma number_cast_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q n : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (n : P.ResidueField) = 0 ↔ q ∣ n := by
  have hInt :
      algebraMap ℤ P.ResidueField (n : ℤ) = 0 ↔ q ∣ n := by
    rw [IsScalarTower.algebraMap_apply
      ℤ (NumberField.RingOfIntegers L) P.ResidueField]
    rw [Ideal.algebraMap_residueField_eq_zero]
    rw [← Ideal.mem_of_liesOver
      (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (n : ℤ))]
    exact rational_nat_cast
  simpa [Int.cast_natCast] using hInt

/--
Membership of a natural number in a prime of `𝓞_L` above `(q)` is the same as divisibility by
`q`.

This is the integral, pre-residue-field version of
`number_cast_zero`.  It is useful for localizing at `P`: a natural
number prime to `q` belongs to the prime complement, hence becomes a unit in
`Localization.AtPrime P`.
-/
lemma number_nat_cast
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q n : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (n : NumberField.RingOfIntegers L) ∈ P ↔ q ∣ n := by
  have hmem :
      algebraMap ℤ (NumberField.RingOfIntegers L) (n : ℤ) ∈ P ↔
        (n : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact
      (Ideal.mem_of_liesOver
        (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (n : ℤ))).symm
  simpa [Int.cast_natCast] using hmem.trans rational_nat_cast

/--
A rational prime `ℓ ≠ q` is not contained in any prime of `𝓞_L` above `(q)`.

Mathematically this says that `ℓ` is a unit in the local ring at `P`.  It is the basic
prime-to-residue-characteristic input needed in the remaining wild-inertia argument.
-/
lemma number_cast_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (ℓ : NumberField.RingOfIntegers L) ∉ P := by
  rw [number_nat_cast (L := L) (q := q) (n := ℓ) P]
  intro hdiv
  have hq_eq_l : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).1 hdiv
  exact hℓ_ne_q hq_eq_l.symm

/--
The class of a rational prime `ℓ ≠ q` in the residue field at `P | (q)` is nonzero.

This is the residue-field form of `number_cast_not`; it packages the
fact that multiplication by `ℓ` is invertible in characteristic `q`.
-/
lemma number_ne_cast
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (ℓ : P.ResidueField) ≠ 0 := by
  intro hzero
  have hdiv : q ∣ ℓ := by
    exact
      (number_cast_zero
        (L := L) (q := q) (n := ℓ) P).1 hzero
  have hq_eq_l : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).1 hdiv
  exact hℓ_ne_q hq_eq_l.symm

/--
The residue class of a rational prime `ℓ ≠ q` as an explicit unit of `P.ResidueField`.

The remaining local ramification proof needs to divide by `ℓ` after reducing modulo `P`; this
definition records that division operation without repeatedly rebuilding the nonzero proof.
-/
noncomputable def number_ne_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.ResidueFieldˣ :=
  Units.mk0 (ℓ : P.ResidueField)
    (number_ne_cast
      (L := L) hq hℓ hℓ_ne_q P)

/-- The unit above really has underlying residue-field element `ℓ`. -/
lemma number_ne_coe
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ((number_ne_unit
      (L := L) hq hℓ hℓ_ne_q P : P.ResidueFieldˣ) : P.ResidueField) = ℓ := by
  simp [number_ne_unit]

/--
A rational prime `ℓ ≠ q` maps to a unit in the localization at any prime above `(q)`.

This is the local-ring version of the same prime-to-residue-characteristic fact: since
`ℓ ∉ P`, it lies in `P.primeCompl`, and localization at `P` inverts it.
-/
lemma number_localization_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsUnit
      (algebraMap (NumberField.RingOfIntegers L) (Localization.AtPrime P)
        (ℓ : NumberField.RingOfIntegers L)) := by
  let R := NumberField.RingOfIntegers L
  have hnot :
      (ℓ : R) ∉ P := by
    exact number_cast_not (L := L) hq hℓ hℓ_ne_q P
  exact
    IsLocalization.map_units (M := P.primeCompl)
      (Localization.AtPrime P) ⟨(ℓ : R), hnot⟩

/-- The residue field at a prime of `𝓞_L` above `(q)` has characteristic `q`. -/
lemma residue_char_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    CharP P.ResidueField q where
  cast_eq_zero_iff n :=
    number_cast_zero (L := L) (q := q) (n := n) P

/--
The additive group of the residue field is a `q`-group, written multiplicatively.

The ramification-filtration argument compares quotients of principal-unit groups with this
additive group, so this packages the characteristic computation in the form needed by
`IsPGroup`.
-/
lemma number_additive_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (Multiplicative P.ResidueField) := by
  haveI : CharP P.ResidueField q :=
    residue_char_p (L := L) hq P
  letI : Algebra (ZMod q) P.ResidueField :=
    ZMod.algebra P.ResidueField q
  exact ZModModule.isPGroup_multiplicative

/--
The cotangent ideal `P / P ^ 2` is killed by the rational prime `q`.

Indeed, `q ∈ P` and every cotangent representative lies in `P`, so their product lies in
`P ^ 2`.  This is the integral version of the fact that `P / P ^ 2` is a vector space over the
residue field of characteristic `q`.
-/
lemma cotangent_cast_nsmul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (z : P.cotangentIdeal) :
    q • z = 0 := by
  classical
  have hqP :
      (q : NumberField.RingOfIntegers L) ∈ P := by
    exact number_rational_lies (L := L) q P
  ext
  change q • (z : NumberField.RingOfIntegers L ⧸ P ^ 2) = 0
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  have hxP : x ∈ P := by
    have hzMem : (z : NumberField.RingOfIntegers L ⧸ P ^ 2) ∈
        P.cotangentIdeal := z.property
    rw [← hxz] at hzMem
    rwa [Ideal.mk_mem_cotangentIdeal] at hzMem
  have hmem :
      q • x ∈ P ^ 2 := by
    rw [nsmul_eq_mul]
    simpa [pow_two] using Ideal.mul_mem_mul hqP hxP
  have hzero :
      Ideal.Quotient.mk (P ^ 2) (q • x) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa using hzero

/--
The additive group of the cotangent ideal is a `q`-group, written multiplicatively.

This is the finite-level algebra behind the wild-inertia theorem: the successive quotients in
the first ramification filtration are modeled on additive residue-field or cotangent pieces,
and hence are `q`-groups.
-/
lemma number_cotangent_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (Multiplicative P.cotangentIdeal) := by
  have hkill :
      ∀ z : P.cotangentIdeal, q • z = 0 := by
    intro z
    exact cotangent_cast_nsmul (L := L) (q := q) P z
  letI : Module (ZMod q) P.cotangentIdeal :=
    AddCommGroup.zmodModule (n := q) hkill
  exact ZModModule.isPGroup_multiplicative

/--
A finite group is a `p`-group once all of its prime-order elements have order `p`.

This isolates the purely finite-group reduction used below.  By Cauchy's theorem, any prime
dividing the cardinality of a finite group occurs as the order of an element.  Thus excluding
prime-order elements away from `p` forces every prime factor of the group cardinality to be
`p`, and the cardinality criterion for `IsPGroup` applies.
-/
lemma p_no_ne
    {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : Nat.Prime p)
    (hno : ∀ {ℓ : ℕ}, Nat.Prime ℓ → ℓ ≠ p →
      ¬ ∃ g : Γ, g ≠ 1 ∧ orderOf g = ℓ) :
    IsPGroup p Γ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_card]
  have hΓ : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  suffices hprimeFactors :
      ∀ ℓ ∈ (Nat.card Γ).primeFactorsList, ℓ = p by
    refine ⟨(Nat.card Γ).primeFactorsList.length, ?_⟩
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem hprimeFactors,
      Nat.prod_primeFactorsList hΓ]
  intro ℓ hℓmem
  obtain ⟨hℓprime, hℓdvd⟩ := (Nat.mem_primeFactorsList hΓ).mp hℓmem
  by_contra hℓ_ne_p
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  obtain ⟨g, hg_order⟩ :=
    @exists_prime_orderOf_dvd_card' Γ _ _ ℓ ⟨hℓprime⟩ hℓdvd
  have hg_ne_one : g ≠ 1 := by
    intro hg_one
    have horder_one : orderOf g = 1 := by
      simp [hg_one]
    exact hℓprime.ne_one (hg_order.symm.trans horder_one)
  exact hno hℓprime hℓ_ne_p ⟨g, hg_ne_one, hg_order⟩

/--
The intersection of all powers of a prime of the ring of integers is zero.

This is the Krull-intersection input behind the separatedness of the `P`-adic congruence
filtration.  Mathlib states this as `Ideal.iInf_pow_eq_bot_of_isDomain` for Noetherian domains;
the ring of integers is a Noetherian domain, and a prime ideal is proper.
-/
lemma number_i_inf
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] :
    (⨅ n : ℕ, P ^ n) = (⊥ : Ideal (NumberField.RingOfIntegers L)) := by
  exact Ideal.iInf_pow_eq_bot_of_isDomain (I := P) (Ideal.IsPrime.ne_top inferInstance)

/--
An element lying in every power of a prime ideal of `𝓞_L` is zero.

This is the elementwise form of `number_i_inf`, and it is the precise
bridge from congruences modulo all powers of `P` to equality in the ring of integers.
-/
lemma all_prime_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    {x : NumberField.RingOfIntegers L}
    (hx : ∀ n : ℕ, x ∈ P ^ n) :
    x = 0 := by
  have hx_iInf :
      x ∈ (⨅ n : ℕ, P ^ n) := by
    exact Ideal.mem_iInf.mpr hx
  have hx_bot :
      x ∈ (⊥ : Ideal (NumberField.RingOfIntegers L)) := by
    simpa [number_i_inf (L := L) P] using hx_iInf
  simpa using hx_bot

/--
Congruence to the identity modulo all powers of `P` fixes every algebraic integer.

This is the ring-of-integers half of separatedness.  Once the difference
`σ(x) - x` lies in every `P ^ n`, Krull intersection makes the difference zero.
-/
lemma number_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    (x : NumberField.RingOfIntegers L) :
    ((σ : Gal(L/ℚ)) • x) = x := by
  have hdiff_zero :
      ((σ : Gal(L/ℚ)) • x) - x = 0 := by
    exact
      all_prime_powers (L := L) P
        (x := ((σ : Gal(L/ℚ)) • x) - x) (fun n => hσ n x)
  exact sub_eq_zero.mp hdiff_zero

/--
An inertia element fixing every algebraic integer fixes the integral basis of `L`.

The basis vector `NumberField.integralBasis L i` is the image in `L` of the algebraic integer
`NumberField.RingOfIntegers.basis L i`, so this is just the fixed-integral-elements hypothesis
transported through the canonical embedding `𝓞_L → L`.
-/
lemma number_inertia_forall
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) = x)
    (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L)) :
    ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L) (NumberField.integralBasis L i) =
      NumberField.integralBasis L i := by
  have hbasis_fixed :
      ((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i) =
        NumberField.RingOfIntegers.basis L i := by
    exact hσ (NumberField.RingOfIntegers.basis L i)
  have hbasis_fixed_field :
      (((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i :
          NumberField.RingOfIntegers L) : L) =
        (NumberField.RingOfIntegers.basis L i : L) := by
    exact congr_arg (fun x : NumberField.RingOfIntegers L => (x : L)) hbasis_fixed
  rw [NumberField.integralBasis_apply]
  change
    (((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i :
        NumberField.RingOfIntegers L) : L) =
      (NumberField.RingOfIntegers.basis L i : L)
  exact hbasis_fixed_field

/--
A ring automorphism of a number field fixing the integral basis is the identity.

This lemma deliberately avoids an ambient `[Algebra ℚ L]` hypothesis.  The basis
`NumberField.integralBasis L` uses the canonical rational vector-space structure on `L`,
and every ring automorphism of a characteristic-zero field is linear for that canonical
structure because it fixes the embedded rationals.
-/
lemma number_refl_fixed
    (L : Type*) [Field L] [NumberField L]
    (e : L ≃+* L)
    (he : ∀ i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L),
      e (NumberField.integralBasis L i) = NumberField.integralBasis L i) :
    e = RingEquiv.refl L := by
  let eLin : L →ₗ[ℚ] L :=
    { toFun := fun x => e x
      map_add' := by
        intro x y
        exact e.map_add x y
      map_smul' := by
        intro c x
        have hc : e (algebraMap ℚ L c) = algebraMap ℚ L c := by
          exact map_ratCast e c
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
        rfl }
  have hlin : eLin = LinearMap.id := by
    exact (NumberField.integralBasis L).ext (f₁ := eLin) (f₂ := LinearMap.id) he
  ext x
  have hx := congr_arg (fun f : L →ₗ[ℚ] L => f x) hlin
  simpa [eLin] using hx

/--
An inertia element that fixes every vector in the integral basis is the identity.

This is the remaining linear-algebra spanning step.  Since `NumberField.integralBasis L` is a
`ℚ`-basis of `L`, a `ℚ`-algebra automorphism fixing each basis vector fixes every element of
`L`, hence is the identity automorphism and therefore the identity element of the inertia
subgroup.
-/
lemma number_inertia_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L),
      ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L) (NumberField.integralBasis L i) =
        NumberField.integralBasis L i) :
    σ = 1 := by
  have hring :
      ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L).toRingEquiv = RingEquiv.refl L := by
    refine
      number_refl_fixed (L := L)
        ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L).toRingEquiv ?_
    intro i
    exact hσ i
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have hx := congr_arg (fun e : L ≃+* L => e x) hring
  simpa using hx

/--
An inertia element fixing every algebraic integer is the identity.

This is the remaining field-spanning step for separatedness.  The proof should use the integral
basis `NumberField.integralBasis L`: its basis vectors are images of elements of `𝓞_L`, so an
`ℚ`-linear automorphism fixing all algebraic integers fixes that basis and therefore fixes every
element of `L`.
-/
lemma number_forall_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) = x) :
    σ = 1 := by
  refine number_inertia_fixed (L := L) P σ ?_
  intro i
  exact
    number_inertia_forall
      (L := L) P σ hσ i

/--
Separatedness of the `P`-adic congruence filtration for inertia.

If an inertia element acts trivially modulo every power of `P` on the ring of integers, then it
is the identity.  The intended proof has two independent pieces.  First, the Krull intersection
theorem in the Dedekind domain `𝓞_L` says that
`⋂ n, P ^ n = 0` for the nonzero prime `P` above `(q)`.  Hence every integral element is fixed.
Second, an automorphism of a number field that fixes all algebraic integers is the identity:
every element of `L` becomes integral after multiplication by a nonzero integer.

This is deliberately separated from the prime-to-`q` ramification bootstrap below.  It is a
pure separatedness statement for the `P`-adic topology, and does not use the order of the
automorphism.
-/
lemma inertia_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n) :
    σ = 1 := by
  refine number_forall_fixed (L := L) P σ ?_
  intro x
  exact number_all_powers
    (L := L) P σ hσ x

/--
The prime-order hypothesis gives an `ℓ`th-power identity after forgetting from wild inertia to
ordinary inertia.

This is a small but useful bookkeeping bridge for the ramification bootstrap below: the
bootstrap uses the equality `σ ^ ℓ = 1` in the actual automorphism group, while the order
hypothesis naturally lives on the subgroup `number_wild_subgroup`.
-/
lemma number_wild_inertia
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ) :
    ((σ : P.inertia (Gal(L/ℚ))) ^ ℓ) = 1 := by
  have hpow_subgroup : σ ^ ℓ = 1 := by
    have hpow_order : σ ^ orderOf σ = 1 := by
      exact pow_orderOf_eq_one σ
    rw [hσ_order] at hpow_order
    exact hpow_order
  exact
    congr_arg
      (fun τ : number_wild_subgroup (L := L) P =>
        (τ : P.inertia (Gal(L/ℚ))))
      hpow_subgroup

/--
The same prime-order identity as a pointwise statement on integral elements.

In the local calculation, applying the equality `σ ^ ℓ = 1` to an integral element is what
turns an orbit sum into zero.  This lemma packages the coercion through inertia into
`Gal(L/ℚ)` and the final action on `𝓞_L`.
-/
lemma wild_iterate_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    (x : NumberField.RingOfIntegers L) :
    (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) ^ ℓ) • x = x := by
  have hpow_inertia :
      ((σ : P.inertia (Gal(L/ℚ))) ^ ℓ) = 1 := by
    exact
      number_wild_inertia
        (L := L) P σ hσ_order
  have hpow_gal :
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) ^ ℓ) = 1 := by
    simpa using
      congr_arg
        (fun τ : P.inertia (Gal(L/ℚ)) => (τ : Gal(L/ℚ)))
        hpow_inertia
  simp [hpow_gal]

/--
Telescoping identity for the orbit of an additive group action.

For the ramification bootstrap, this rewrites `τ ^ ℓ x - x` as the sum of the conjugate
increments `τ ^ i (τ x - x)`.  When `τ ^ ℓ = 1`, the left hand side vanishes and the orbit sum
is zero.
-/
lemma smul_sub_range
    {gtype : Type*} {atype : Type*}
    [Group gtype] [AddCommGroup atype] [DistribMulAction gtype atype]
    (g : gtype) (n : ℕ) (x : atype) :
    (g ^ n) • x - x =
      ∑ i ∈ Finset.range n, (g ^ i) • (g • x - x) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (g ^ (n + 1)) • x - x =
            ((g ^ n) • x - x) + (g ^ n) • (g • x - x) := by
          rw [pow_succ, mul_smul, smul_sub]
          abel
        _ = (∑ i ∈ Finset.range n, (g ^ i) • (g • x - x)) +
            (g ^ n) • (g • x - x) := by
          rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1), (g ^ i) • (g • x - x) := by
          exact (Finset.sum_range_succ (fun i => (g ^ i) • (g • x - x)) n).symm

/--
Cancellation in a prime-power ideal of a Dedekind domain by an element outside the prime.

Equivalently, multiplication by an element of the complement of `P` is injective on each graded
piece `R / P ^ n`.  This is the formal version of the "divide by the prime-to-`P` scalar"
operation used in the ramification bootstrap.
-/
lemma ideal_cancel_not
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] {a x : R} {n : ℕ}
    (ha : a ∉ P) (hax : a * x ∈ P ^ n) :
    x ∈ P ^ n := by
  exact (Ideal.IsPrime.mul_mem_pow P hax).resolve_left ha

/--
An inertia element preserves every power of the prime ideal.

This generalizes the earlier square-stability lemma from `P ^ 2` to the whole `P`-adic
filtration, which is needed to state the induction step for the remaining bootstrap.
-/
lemma inertia_smul_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (n : ℕ) :
    (σ : Gal(L/ℚ)) • (P ^ n) = P ^ n := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  calc
    (σ : Gal(L/ℚ)) • (P ^ n) = ((σ : Gal(L/ℚ)) • P) ^ n := by
      simp [smul_pow']
    _ = P ^ n := by
      rw [hStab]

/--
Pointwise membership form of preservation of `P ^ n` by inertia.
-/
lemma number_smul_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (n : ℕ)
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P ^ n) :
    ((σ : Gal(L/ℚ)) • x) ∈ P ^ n := by
  classical
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • (P ^ n) := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x (P ^ n) hx
  simpa [inertia_smul_pow (L := L) P σ n] using hMem

/--
Multiplication by a rational prime `ℓ ≠ q` can be cancelled from membership in `P ^ n`.

This is the integral ideal-power form of the fact that `ℓ` is a unit in the local ring at
`P | (q)`.
-/
lemma number_ne_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} {x : NumberField.RingOfIntegers L}
    (hmem : (ℓ : NumberField.RingOfIntegers L) * x ∈ P ^ n) :
    x ∈ P ^ n := by
  have hnot :
      (ℓ : NumberField.RingOfIntegers L) ∉ P := by
    exact number_cast_not (L := L) hq hℓ hℓ_ne_q P
  exact ideal_cancel_not P hnot hmem

/--
The prime-order identity makes the orbit sum of the first difference vanish.

This is the additive telescoping part of the ramification bootstrap.  It isolates the only use
of the equality `σ ^ ℓ = 1`: after telescoping along the orbit, the sum of all translates of
`σ x - x` is zero.
-/
lemma number_wild_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    (x : NumberField.RingOfIntegers L) :
    let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
    (∑ i ∈ Finset.range ℓ, ((τ ^ i) • ((τ • x) - x))) = 0 := by
  let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
  have htel :
      ((τ ^ ℓ) • x) - x =
        ∑ i ∈ Finset.range ℓ, ((τ ^ i) • ((τ • x) - x)) := by
    exact smul_sub_range τ ℓ x
  have hpowx :
      ((τ ^ ℓ) • x) = x := by
    simpa [τ] using
      wild_iterate_smul
        (L := L) P σ hσ_order x
  have hleft :
      ((τ ^ ℓ) • x) - x = 0 := by
    simp [hpowx]
  rw [hleft] at htel
  simpa [τ] using htel.symm

/--
If an inertia element is congruent to the identity modulo `P ^ n` on the whole ring, then on
elements already in `P ^ m` it is congruent to the identity modulo `P ^ (n + m - 1)`.

This is the product-rule estimate behind the ramification bootstrap.  It is proved by induction
on membership in the ideal power `P ^ m`: a generator in `P` gives the base congruence, and
multiplying by another element of `P` increases the congruence level by one.
-/
lemma inertia_smul_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {n m : ℕ}
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (hm : 0 < m) :
    ((σ : Gal(L/ℚ)) • y) - y ∈ P ^ (n + m - 1) := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change τ • y - y ∈ P ^ (n + m - 1)
  suffices hmain : ∀ {m : ℕ} {y : NumberField.RingOfIntegers L},
      y ∈ P ^ m → 0 < m → τ • y - y ∈ P ^ (n + m - 1) from
    hmain hy hm
  intro m y hy
  refine Submodule.pow_induction_on_left' (M := P)
    (C := fun i z _hz => 0 < i → τ • z - z ∈ P ^ (n + i - 1)) ?base ?add ?mul hy
  · intro r hpos
    omega
  · intro x z i _hx _hz hxprop hzprop hpos
    rw [smul_add, add_sub_add_comm]
    exact (P ^ (n + i - 1)).add_mem (hxprop hpos) (hzprop hpos)
  · intro a ha i z hz hzprop _hpos_succ
    cases i with
    | zero =>
        simpa [τ] using hcong (a * z)
    | succ i =>
        have hpos : 0 < i.succ := Nat.succ_pos i
        have hdiff_z : τ • z - z ∈ P ^ (n + i) := by
          simpa using hzprop hpos
        have hτaP : τ • a ∈ P := by
          exact number_smul_prime (L := L) P σ ha
        have hterm1 : (τ • a) * (τ • z - z) ∈ P ^ (n + i.succ) := by
          have hmul : (τ • a) * (τ • z - z) ∈ P * P ^ (n + i) := by
            exact Ideal.mul_mem_mul hτaP hdiff_z
          have hpoweq : P ^ (n + i.succ) = P * P ^ (n + i) := by
            rw [show n + i.succ = (n + i) + 1 by omega, pow_succ']
          rwa [hpoweq]
        have hterm2 : (τ • a - a) * z ∈ P ^ (n + i.succ) := by
          have hdiff_a : τ • a - a ∈ P ^ n := by
            simpa [τ] using hcong a
          have hmul : (τ • a - a) * z ∈ P ^ n * P ^ i.succ := by
            exact Ideal.mul_mem_mul hdiff_a hz
          simpa [pow_add] using hmul
        have hdecomp :
            τ • (a * z) - a * z =
              (τ • a) * (τ • z - z) + (τ • a - a) * z := by
          rw [smul_mul']
          ring
        rw [hdecomp]
        exact (P ^ (n + i.succ)).add_mem hterm1 hterm2

/--
Every iterate of an inertia element preserves every power of the prime ideal.
-/
lemma number_inertia_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (m : ℕ)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (k : ℕ) :
    (((σ : Gal(L/ℚ)) ^ k) • y) ∈ P ^ m := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change (τ ^ k) • y ∈ P ^ m
  induction k with
  | zero =>
      simpa using hy
  | succ k ih =>
      have hmem :
          τ • ((τ ^ k) • y) ∈ P ^ m := by
        exact number_smul_pow (L := L) P σ m ih
      simpa [τ, pow_succ', mul_smul] using hmem

/--
The previous congruence estimate is stable under iterating the same inertia element.

This is the form needed for orbit sums: if `y ∈ P ^ m`, then every translate `σ ^ k y` is
congruent to `y` modulo `P ^ (n + m - 1)`.
-/
lemma number_smul_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {n m : ℕ}
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (hm : 0 < m) (k : ℕ) :
    (((σ : Gal(L/ℚ)) ^ k) • y) - y ∈ P ^ (n + m - 1) := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change (τ ^ k) • y - y ∈ P ^ (n + m - 1)
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hpow_mem : (τ ^ k) • y ∈ P ^ m := by
        simpa [τ] using
          number_inertia_smul (L := L) P σ m hy k
      have hstep :
          τ • ((τ ^ k) • y) - ((τ ^ k) • y) ∈ P ^ (n + m - 1) := by
        simpa [τ] using
          inertia_smul_pred
            (L := L) P σ hcong hpow_mem hm
      have hdecomp :
          (τ ^ (k + 1)) • y - y =
            (τ • ((τ ^ k) • y) - ((τ ^ k) • y)) + ((τ ^ k) • y - y) := by
        rw [pow_succ', mul_smul]
        abel
      rw [hdecomp]
      exact (P ^ (n + m - 1)).add_mem hstep ih

/--
The single induction step in the prime-to-residue-characteristic bootstrap.

Assume `σ` is already congruent to the identity modulo `P ^ n`, with `2 ≤ n`.  The orbit-sum
lemma gives `ℓ * (σ x - x)` modulo `P ^ (n + 1)`, and
`number_ne_pow` cancels `ℓ` because `ℓ ∉ P`.  The remaining
still-unformalized local calculation is that every translate of `σ x - x` is congruent to
`σ x - x` modulo `P ^ (n + 1)`; this follows by applying the induction hypothesis to products
generating `P ^ n`.
-/
lemma number_wild_congruence
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    {n : ℕ} (hn : 2 ≤ n)
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n) :
    ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1) := by
  intro x
  let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
  let d : NumberField.RingOfIntegers L := τ • x - x
  have hd : d ∈ P ^ n := by
    simpa [τ, d] using hcong x
  have hn_pos : 0 < n := by
    omega
  have htranslate :
      ∀ i ∈ Finset.range ℓ, (τ ^ i) • d - d ∈ P ^ (n + 1) := by
    intro i _hi
    have hhigh :
        (τ ^ i) • d - d ∈ P ^ (n + n - 1) := by
      simpa [τ] using
        number_smul_pred
          (L := L) P (σ : P.inertia (Gal(L/ℚ))) hcong hd hn_pos i
    exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n - 1) hhigh
  have horbit :
      (∑ i ∈ Finset.range ℓ, (τ ^ i) • d) = 0 := by
    simpa [τ, d] using
      number_wild_zero
        (L := L) P σ hσ_order x
  have hsum_sub :
      (∑ i ∈ Finset.range ℓ, (τ ^ i) • d) -
          (∑ i ∈ Finset.range ℓ, d) ∈ P ^ (n + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem (P ^ (n + 1)) htranslate
  have hsum_const :
      (∑ _i ∈ Finset.range ℓ, d) =
        (ℓ : NumberField.RingOfIntegers L) * d := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hneg :
      -((ℓ : NumberField.RingOfIntegers L) * d) ∈ P ^ (n + 1) := by
    simpa [horbit, hsum_const] using hsum_sub
  have hlmul :
      (ℓ : NumberField.RingOfIntegers L) * d ∈ P ^ (n + 1) := by
    simpa using (P ^ (n + 1)).neg_mem hneg
  exact
    number_ne_pow
      (L := L) hq hℓ hℓ_ne_q P hlmul

/--
The all-powers congruence follows formally from the one-step upgrade.

The base levels are: `P ^ 0` is trivial, `P ^ 1` is the definition of inertia, and `P ^ 2`
is the definition of wild inertia.  All higher levels are obtained by repeatedly applying the
prime-to-residue-characteristic congruence step.
-/
lemma wild_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hstep : ∀ {n : ℕ}, 2 ≤ n →
      (∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n) →
      ∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih x
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simpa using
            number_smul_sub
              (L := L) P (σ : P.inertia (Gal(L/ℚ))) x
      | succ n =>
          cases n with
          | zero =>
              exact
                (wild_inertia_subgroup
                  (L := L) P (σ : P.inertia (Gal(L/ℚ)))).1 σ.property x
          | succ n =>
              have hprev :
                  ∀ y : NumberField.RingOfIntegers L,
                    (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • y) - y ∈
                      P ^ n.succ.succ := by
                exact ih n.succ.succ (by omega)
              exact hstep (n := n.succ.succ) (by omega) hprev x

/--
Prime-to-residue-characteristic wild elements are arbitrarily highly congruent to the identity.

This is the ramification-filtration bootstrap. Starting from the defining wild
congruence `σ(x) - x ∈ P ^ 2`, assume `σ` has prime order `ℓ` with `ℓ ≠ q`.
Since `ℓ` is a unit in the local ring at `P`, the identity `σ ^ ℓ = 1` upgrades
congruence modulo `P ^ n` to congruence modulo `P ^ (n + 1)`. Iterating gives
congruence modulo every power of `P`.

The previous lemmas
`number_ne_unit` and
`number_localization_unit` provide the formal unit input needed to divide
by `ℓ` in the residue/cotangent calculation.
-/
lemma number_wild_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ) :
    ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
  refine
    wild_all_powers
      (L := L) P σ ?_
  intro n hn hcong
  exact
    number_wild_congruence
      (L := L) hq hℓ hℓ_ne_q P σ hσ_order hn hcong

/--
Prime-to-residue-characteristic wild inertia has no nontrivial element of prime order.

This is the local ramification fact still to be formalized: if an automorphism
of prime order `ℓ ≠ q` acts trivially modulo `P ^ 2`, then it is trivial.
Equivalently, the first ramification group has no prime-to-`q` torsion. The
usual proof localizes at `P`, writes
`σ(π) = π + a` with `a ∈ (π ^ 2)`, and uses the identity
`σ ^ ℓ(π) - π = ℓ * a` modulo `π ^ 3`; because `ℓ` is a unit in residue
characteristic `q`, this forces `a` into higher and higher powers of the
maximal ideal, hence `a = 0`, and then the standard separation argument gives
`σ = 1`.
-/
lemma wild_no_char
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ¬ ∃ σ : number_wild_subgroup (L := L) P,
      σ ≠ 1 ∧ orderOf σ = ℓ := by
  rintro ⟨σ, hσ_ne_one, hσ_order⟩
  have h_all_powers :
      ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
    exact
      number_wild_powers
        (L := L) hq hℓ hℓ_ne_q P σ hσ_order
  have h_inertia_one :
      (σ : P.inertia (Gal(L/ℚ))) = 1 := by
    exact
      inertia_all_powers
        (L := L) hq P (σ : P.inertia (Gal(L/ℚ))) h_all_powers
  have h_wild_one : σ = 1 := by
    exact Subtype.ext h_inertia_one
  exact hσ_ne_one h_wild_one

/--
Wild inertia is a `q`-group above the rational prime `q`.

This is the standard local ramification theorem for the first ramification group: the successive
principal-unit quotients have the residue-field additive characteristic, so the finite subgroup
acting trivially on the cotangent line is a group of residue characteristic power order.
-/
lemma number_wild_group
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (number_wild_subgroup (L := L) P) := by
  classical
  refine p_no_ne
    (Γ := number_wild_subgroup (L := L) P) hq ?_
  intro ℓ hℓ hℓ_ne_q
  exact wild_no_char
    (L := L) hq hℓ hℓ_ne_q P

/--
The genuine local arithmetic construction of the tame inertia character.

The intended character is built in the local DVR `Localization.AtPrime P`: choose a
uniformizer `π`, send an inertia element `σ` to the residue of the unit `σ(π) / π`, and prove
that the kernel is the first ramification group.  Since the residue characteristic is `q`, that
first ramification group is a `q`-group.

This lemma is now the only remaining local-field input for the Sylow-containment theorem below.
It is strictly smaller than that theorem: it produces the tame character with a `q`-group
kernel, while the passage from `q`-group kernel to Sylow containment is handled separately by
`monoid_sylow_p`.
-/
lemma tame_inertia_arithmetic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      IsPGroup q χ.ker := by
  classical
  obtain ⟨χ, hχKer⟩ :=
    tame_uniformizer_wild
      (L := L) hq P
  refine ⟨χ, ?_⟩
  have hWild :
      IsPGroup q (number_wild_subgroup (L := L) P) := by
    exact number_wild_group (L := L) hq P
  rw [hχKer]
  exact hWild

/--
The local arithmetic `q`-group-kernel statement implies the Sylow-containment form.

This lemma isolates the purely group-theoretic endpoint: once the tame character has
`q`-group kernel, Sylow's theorem supplies a Sylow subgroup containing that kernel.
-/
lemma tame_inertia_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hχ :
      ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
        IsPGroup q χ.ker) :
    ∃ (S : Sylow q (P.inertia (Gal(L/ℚ))))
      (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ),
        χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ)))) := by
  classical
  obtain ⟨χ, hKerP⟩ := hχ
  obtain ⟨S, hKerS⟩ :=
    monoid_sylow_p χ hKerP
  exact ⟨S, χ, hKerS⟩

/--
The local tame character with its kernel controlled by the wild Sylow subgroup.

This is the next local ramification theorem to formalize.  After choosing a uniformizer `π` in
`Localization.AtPrime P`, the tame character sends `σ` to the residue of `σ(π) / π`.  Its kernel
is wild inertia, so in the finite inertia group it is contained in a Sylow subgroup for the
residue characteristic `q`.
-/
lemma tame_character_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ (S : Sylow q (P.inertia (Gal(L/ℚ))))
      (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ),
        χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ)))) := by
  classical
  have hχ :
      ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
        IsPGroup q χ.ker := by
    exact
      tame_inertia_arithmetic
        (L := L) hq P
  exact
    tame_inertia_sylow
      (L := L) hq P hχ

/--
The local-residue-field form of the tame inertia character.

This is the genuinely local construction: work in `Localization.AtPrime P`, choose a
uniformizer, send an inertia element to the residue of `σ(π) / π`, and identify the kernel with
wild inertia.  The wrapper below transports this local character to `(𝓞 L ⧸ P)ˣ`.
-/
lemma tame_inertia_character
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      IsPGroup q χ.ker := by
  classical
  exact
    tame_inertia_arithmetic
      (L := L) hq P

/--
Once the local tame character has `q`-group kernel, the prime-to-`q` inertia-card hypothesis makes
it injective.

This is the local-residue-field analogue of `tame_units_embedding`; the only
remaining arithmetic input is the construction of the tame character itself.
-/
lemma tame_inertia_embedding
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ))))) :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      Function.Injective χ := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχKer⟩ :=
    tame_inertia_character
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    monoid_coprime_card
      χ hχKer hCardCoprime

/--
Local tame ramification supplies a residue-unit-valued character whose kernel is wild inertia.

After localizing `𝓞 L` at `P` and choosing a uniformizer `π`, an inertia element `σ` acts by
`σ π = uσ π` up to higher valuation.  Reducing `uσ` modulo `P` gives a multiplicative character
from inertia to the residue-field units.  Its kernel is the first wild ramification group, hence
a `q`-group when `P` lies above the rational prime `q`.
-/
lemma tame_inertia_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →*
        (NumberField.RingOfIntegers L ⧸ P)ˣ,
      IsPGroup q χ.ker := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  obtain ⟨χlocal, hχlocal⟩ :=
    tame_inertia_character
      (L := L) hq P
  let eUnits :
      (NumberField.RingOfIntegers L ⧸ P)ˣ ≃* P.ResidueFieldˣ :=
    unitsResidueMaximal P
  let χ : P.inertia (Gal(L/ℚ)) →*
      (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    eUnits.symm.toMonoidHom.comp χlocal
  refine ⟨χ, ?_⟩
  exact p_ker_comp eUnits.symm χlocal hχlocal

/--
The tame inertia character embeds inertia into the multiplicative group of the residue field.

Mathematically, after choosing a uniformizer `π` at `P`, an inertia element `σ` is sent to the
residue class of `σ(π) / π`.  The prime-to-`q` hypothesis kills the wild inertia kernel, so this
character is injective.
-/
lemma tame_units_embedding
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ))))) :
    ∃ χ : P.inertia (Gal(L/ℚ)) →*
        (NumberField.RingOfIntegers L ⧸ P)ˣ,
      Function.Injective χ := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχKer⟩ :=
    tame_inertia_units
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    monoid_coprime_card
      χ hχKer hCardCoprime

/--
The tame inertia subgroup at a prime above `q` is cyclic.

This is the inertia half of the local metacyclicity theorem. The hypothesis is exactly the
prime-to-`q` ramification condition. Since the residue characteristic is `q`, the usual tame
inertia embedding into the multiplicative group of the residue field makes the inertia group
cyclic.
-/
lemma tame_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic (P.inertia (Gal(L/ℚ))) := by
  classical
  have hCardCoprime :
      Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))) :=
    tame_inertia_coprime (L := L) hq hTame P
  obtain ⟨χ, hχ⟩ :=
    tame_units_embedding
      (L := L) hq P hCardCoprime
  exact
    cyclic_injective_units
      (L := L) hq P χ hχ

/--
The residue-field quotient of a decomposition subgroup is cyclic.

Mathlib already provides the quotient equivalence
`Ideal.Quotient.stabilizerQuotientInertiaEquiv`; this lemma packages the cyclicity conclusion
so the main local theorem can focus on the extension structure.
-/
lemma decomposition_inertia_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic
      (MulAction.stabilizer (Gal(L/ℚ)) P ⧸
        (P.inertia (Gal(L/ℚ))).subgroupOf
          (MulAction.stabilizer (Gal(L/ℚ)) P)) := by
  /-
  Under `Ideal.Quotient.stabilizerQuotientInertiaEquiv`, this quotient is the Galois group of
  the residue field extension
  `(𝓞 L / P) / (ℤ / (q))`. The target is cyclic by `galois_group_cyclic`.
  -/
  classical
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsPrime := rational_prime_ideal hq
  letI : P.LiesOver p := by
    simpa [p] using (inferInstance : P.LiesOver (Ideal.rationalPrimeIdeal q))
  have hp_ne_bot : p ≠ ⊥ := by
    dsimp [p, Ideal.rationalPrimeIdeal]
    exact mt Ideal.span_singleton_eq_bot.mp (by exact_mod_cast hq.ne_zero)
  letI : p.IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hp_ne_bot
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne_bot inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) := Ideal.Quotient.field P
  have hResidueFinite : Finite (NumberField.RingOfIntegers L ⧸ P) := inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) := hResidueFinite
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : IsGaloisGroup (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing
      (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) ℚ L
  letI : Algebra.IsInvariant ℤ (NumberField.RingOfIntegers L) (Gal(L/ℚ)) :=
    inferInstance
  let e :
      MulAction.stabilizer (Gal(L/ℚ)) P ⧸
          (P.inertia (Gal(L/ℚ))).subgroupOf
            (MulAction.stabilizer (Gal(L/ℚ)) P) ≃*
        Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p)) :=
    Ideal.Quotient.stabilizerQuotientInertiaEquiv (Gal(L/ℚ)) p P
  have hResidue :
      IsCyclic (Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p))) :=
    galois_group_cyclic
      (k := ℤ ⧸ p) (K := NumberField.RingOfIntegers L ⧸ P)
  exact e.isCyclic.mpr hResidue

/--
For a finite Galois number field, the decomposition subgroup at a tamely ramified rational prime
is metacyclic.

This is now the precise local arithmetic theorem needed by
`initial_open_metacyclic`: inertia is cyclic, and
the decomposition quotient by inertia is cyclic.
-/
lemma tame_decomposition_metacyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IMSubgro (MulAction.stabilizer (Gal(L/ℚ)) P) := by
  classical
  let D : Subgroup (Gal(L/ℚ)) := MulAction.stabilizer (Gal(L/ℚ)) P
  let I : Subgroup D :=
    (P.inertia (Gal(L/ℚ))).subgroupOf D
  have hI_normal : I.Normal := by
    change
      ((P.inertia (Gal(L/ℚ))).subgroupOf
        (MulAction.stabilizer (Gal(L/ℚ)) P)).Normal
    infer_instance
  have hI_cyclic_as_subgroup :
      IsCyclic (P.inertia (Gal(L/ℚ))) :=
    tame_cyclic (L := L) hq hTame P
  have hI_cyclic : IsCyclic I := by
    let eI : I ≃* P.inertia (Gal(L/ℚ)) :=
      Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer P)
    exact eI.isCyclic.mpr hI_cyclic_as_subgroup
  have hquot_cyclic :
      IsCyclic (D ⧸ I) := by
    simpa [D, I] using
      decomposition_inertia_cyclic (L := L) hq P
  exact ⟨I, hI_normal, hI_cyclic, hquot_cyclic⟩

/--
In a finite Galois number field, every local ramification index divides the Galois group order.
-/
lemma number_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P ∣
      Nat.card (Gal(L/ℚ)) := by
  classical
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    inertia_ramification_idx (L := L) hq P
  have hDiv :
      Nat.card (P.inertia (Gal(L/ℚ))) ∣
        Nat.card (Gal(L/ℚ)) :=
    Subgroup.card_subgroup_dvd_card (P.inertia (Gal(L/ℚ)))
  rw [← hCard]
  exact hDiv

/--
If the order of the finite Galois group is prime to `q`, then the extension is tame at primes
above `(q)`.
-/
lemma primes_coprime_card
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hCardCoprime : Nat.Coprime q (Nat.card (Gal(L/ℚ)))) :
    RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q := by
  classical
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
  have hRamificationDivides :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P ∣
        Nat.card (Gal(L/ℚ)) :=
    number_ramification_idx (L := L) hq P
  exact hCardCoprime.coprime_dvd_right hRamificationDivides

/-- The order of a finite `3`-group is coprime to each prime in `initialRamifiedPrimes`. -/
lemma p_coprime_ramified
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup 3 Γ)
    (r : {s // s ∈ initialRamifiedPrimes}) :
    Nat.Coprime r.1 (Nat.card Γ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hcard⟩ :=
    IsPGroup.iff_card.mp hΓ
  have hr_prime : Nat.Prime r.1 :=
    ramified_primes_prime r.1 r.2
  have hr_ne_three : r.1 ≠ 3 :=
    ramified_primes_ne r.1 r.2
  have hcop :
      Nat.Coprime (r.1 ^ 1) (3 ^ n) :=
    Nat.coprime_pow_primes 1 n hr_prime Nat.prime_three hr_ne_three
  simpa [hcard] using hcop

/-- For each ramified prime in `initialRamifiedPrimes`, choose the corresponding local subgroup
of the finite quotient `G ⧸ N`.

The intended arithmetic choice is the image of a distinguished decomposition subgroup at that
prime. We isolate the choice itself from the two properties used later: global generation and
local metacyclicity. -/
noncomputable def initial_open_family
    (N : OpenNormalSubgroup G) :
    {s // s ∈ initialRamifiedPrimes} → Subgroup (G ⧸ (N : Subgroup G)) := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  have hKNfix : KN.fixingSubgroup = Nclosed.1 := by
    simpa [KN] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) Nclosed)
  have hKNfg :
      FiniteDimensional ℚ KN ∧ IsGalois ℚ KN :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := ℚ) (K := initialProExtension) KN).mp <| by
        rw [hKNfix]
        refine ⟨N.isOpen', ?_⟩
        change (N : Subgroup G).Normal
        infer_instance
  letI : FiniteDimensional ℚ KN := hKNfg.1
  letI : IsGalois ℚ KN := hKNfg.2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  let e : G ⧸ (N : Subgroup G) ≃* Gal(KN/ℚ) := by
    simpa [KN, Nclosed] using
      (galoisFixedField
        (F := ℚ) (L := initialProExtension) Nclosed)
  intro r
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
  letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
  let P0 : Ideal.primesOver p (𝓞 KN) := Classical.choice inferInstance
  let P : Ideal (𝓞 KN) := P0.1
  letI : P.IsPrime := P0.2.1
  letI : P.LiesOver p := P0.2.2
  exact e.symm.mapSubgroup (MulAction.stabilizer (Gal(KN/ℚ)) P)

/-- Transporting a generating family of subgroups across a group isomorphism preserves generation.

This is the purely group-theoretic part of descending the decomposition subgroups from the finite
Galois group of the fixed field to the open-normal quotient of the profinite Galois group. -/
lemma i_subgroup_top
    {Q R ι : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (H : ι → Subgroup R)
    (hH : (⨆ i, H i) = ⊤) :
    (⨆ i, e.symm.mapSubgroup (H i)) = ⊤ := by
  classical
  let S : Subgroup Q := ⨆ i, e.symm.mapSubgroup (H i)
  have hmap_top : Subgroup.map e.toMonoidHom S = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← hH]
      refine iSup_le ?_
      intro i x hx
      refine ⟨e.symm x, ?_, by simp⟩
      exact (le_iSup (fun i => e.symm.mapSubgroup (H i)) i) (by simpa using hx)
  apply top_unique
  intro x hx
  have hxmap : e x ∈ Subgroup.map e.toMonoidHom S := by
    rw [hmap_top]
    exact Subgroup.mem_top (e x)
  rcases hxmap with ⟨y, hyS, hyx⟩
  have hy_eq : y = x := e.injective hyx
  simpa [S, hy_eq] using hyS

/-- The open-normal quotient is identified with the Galois group of its fixed finite field.

This helper records the finite Galois fixed-field package that is needed before invoking the
Shafarevich/decomposition-group generation input. It is intentionally separated from the
arithmetic generation statement below: this part is formal Galois descent and is already proved. -/
lemma initial_galois_open
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    FiniteDimensional ℚ KN ∧ IsGalois ℚ KN := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  have hKNfix : KN.fixingSubgroup = Nclosed.1 := by
    simpa [KN] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) Nclosed)
  exact
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := ℚ) (K := initialProExtension) KN).mp <| by
        rw [hKNfix]
        refine ⟨N.isOpen', ?_⟩
        change (N : Subgroup G).Normal
        infer_instance

/-- The quotient by `N` is the Galois group of the fixed field attached to `N`.

This is the second formal descent step used by the local-generation argument: after replacing the
open-normal quotient by a finite fixed-field Galois group, local decomposition subgroups can be
described as stabilizers of primes above the rational ramified primes. -/
lemma initial_open_fixed
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    Nonempty (G ⧸ (N : Subgroup G) ≃* Gal(KN/ℚ)) := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  have hKNfg : FiniteDimensional ℚ KN ∧ IsGalois ℚ KN := by
    simpa [KN, Nclosed] using
      (initial_galois_open N)
  letI : FiniteDimensional ℚ KN := hKNfg.1
  letI : IsGalois ℚ KN := hKNfg.2
  exact ⟨by
    simpa [KN, Nclosed] using
      (galoisFixedField
        (F := ℚ) (L := initialProExtension) Nclosed)⟩

/-
Arithmetic Shafarevich input on the finite fixed field attached to `N`.

For the fixed finite Galois quotient `KN / ℚ`, the decomposition groups at the five initially
ramified rational primes generate the whole finite Galois group.  The prime above each rational
prime is the same choice used in `initial_open_family`.
-/
/-- The fixed field attached to an open normal subgroup is a genuine subfield of the ambient
initial pro-`3` extension. -/
lemma embeds_pro_extension
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    letI : FiniteDimensional ℚ KN :=
      (initial_galois_open N).1
    letI : IsGalois ℚ KN :=
      (initial_galois_open N).2
    letI : NumberField KN := NumberField.of_module_finite ℚ KN
    EmbedsIntoExtension KN initialProExtension := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  letI : FiniteDimensional ℚ KN :=
    (initial_galois_open N).1
  letI : IsGalois ℚ KN :=
    (initial_galois_open N).2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  refine ⟨{ toRingHom := KN.subtype, commutes' := ?_ }⟩
  intro q
  rfl

/-- Every finite fixed-field quotient of the initial pro-`3` extension is unramified outside the
five initially ramified rational primes. -/
lemma initial_unramified_outside
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    letI : FiniteDimensional ℚ KN :=
      (initial_galois_open N).1
    letI : IsGalois ℚ KN :=
      (initial_galois_open N).2
    letI : NumberField KN := NumberField.of_module_finite ℚ KN
    UnramifiedOutside KN initialRamifiedPrimes := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  letI : FiniteDimensional ℚ KN :=
    (initial_galois_open N).1
  letI : IsGalois ℚ KN :=
    (initial_galois_open N).2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  exact
    outside_embeds_pro
      (embeds_pro_extension N)

lemma integers_smul_algebra
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (σ : Gal(L/K))
    (x : NumberField.RingOfIntegers E) :
    σ • (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) x) =
      algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L)
        ((σ.restrictNormalHom E) • x) := by
  apply Subtype.ext
  let y : NumberField.RingOfIntegers L :=
    algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) x
  calc
    algebraMap (NumberField.RingOfIntegers L) L
        (σ • (algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) x))
      = σ (algebraMap (NumberField.RingOfIntegers L) L y) := by
          exact
            (congrArg Subtype.val
              (alg_gal_restrict
                (K := K) (E := L) (σ := σ) (x := y))).trans
              (algebraMap_galRestrict_apply
                (A := NumberField.RingOfIntegers K) (K := K) (L := L)
                (B := NumberField.RingOfIntegers L) σ y)
    _ =
        σ (algebraMap E L (algebraMap (NumberField.RingOfIntegers E) E x)) := by
          rfl
    _ =
        algebraMap E L
          ((σ.restrictNormalHom E) (algebraMap (NumberField.RingOfIntegers E) E x)) := by
            simpa using
              (AlgEquiv.restrictNormalHom_apply
                (L := E) σ (algebraMap (NumberField.RingOfIntegers E) E x)).symm
    _ =
        algebraMap E L
          (algebraMap (NumberField.RingOfIntegers E) E
            ((σ.restrictNormalHom E) • x)) := by
              rfl
    _ =
        algebraMap (NumberField.RingOfIntegers L) L
          (algebraMap (NumberField.RingOfIntegers E)
            (NumberField.RingOfIntegers L)
            ((σ.restrictNormalHom E) • x)) := by
              rfl

lemma under_eq_under
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (σ : Gal(L/K))
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Ideal.under (NumberField.RingOfIntegers E) (σ • P) =
      (σ.restrictNormalHom E) • Ideal.under (NumberField.RingOfIntegers E) P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  change
    (σ⁻¹ •
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) x) ∈ P ↔
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L)
        ((σ.restrictNormalHom E)⁻¹ • x) ∈ P
  have h :=
    integers_smul_algebra
      (E := E) (σ := σ⁻¹) (x := x)
  constructor <;> intro hx
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L)
          ((σ⁻¹).restrictNormalHom E • x) ∈ P := by
        exact h ▸ hx
    simpa using hx'
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L)
          ((σ⁻¹).restrictNormalHom E • x) ∈ P := by
        simpa using hx
    exact h.symm ▸ hx'

lemma splits_completely_fixing
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (E : IntermediateField ℚ L) [FiniteDimensional ℚ ↥E] [IsGalois ℚ ↥E]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hPstab :
      MulAction.stabilizer (Gal(L/ℚ)) P ≤ E.fixingSubgroup) :
    splitsCompletely ↥E q := by
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  let hstRatE : IsScalarTower ℤ ℚ ↥E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  let hstRatL : IsScalarTower ℤ ℚ L := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  let hstE : IsScalarTower ℤ (𝓞 ↥E) ↥E :=
    integers_scalar_tower (K := ↥E)
  let hstL : IsScalarTower ℤ (𝓞 L) L :=
    integers_scalar_tower (K := L)
  letI : IsGaloisGroup Gal(↥E/ℚ) ℤ (NumberField.RingOfIntegers E) := by
    exact
      @IsGaloisGroup.of_isFractionRing
        (Gal(↥E/ℚ))
        ℤ
        (𝓞 ↥E)
        ℚ
        ↥E
        _ _ _ _ _ _ _ _ _ _ _ _ _
        hstRatE
        hstE
        _ _ _ _ _
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) := by
    exact
      @IsGaloisGroup.of_isFractionRing
        (Gal(L/ℚ))
        ℤ
        (𝓞 L)
        ℚ
        L
        _ _ _ _ _ _ _ _ _ _ _ _ _
        hstRatL
        hstL
        _ _ _ _ _
  letI : Finite (Gal(↥E/ℚ)) := by
    infer_instance
  letI : Finite (Gal(L/ℚ)) := by
    infer_instance
  letI : IsGaloisGroup ↥E.fixingSubgroup ↥E L := by
    exact
      @IsGaloisGroup.intermediateField
        (Gal(L/ℚ))
        ℚ
        L
        _ _ _ _ _
        E
        inferInstance
        inferInstance
  letI : Finite ↥(E.fixingSubgroup) := by
    infer_instance
  letI := IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers E) E L
    (NumberField.RingOfIntegers L)
  let hstEL : IsScalarTower (𝓞 ↥E) ↥E L := by
    infer_instance
  let hstOEL : IsScalarTower (𝓞 ↥E) (𝓞 L) L := by
    infer_instance
  letI : IsGaloisGroup E.fixingSubgroup
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) :=
    by
      exact
        @IsGaloisGroup.of_isFractionRing
          E.fixingSubgroup
          (𝓞 ↥E)
          (𝓞 L)
          ↥E
          L
          _ _ _ _ _ _ _ _ _ _ _ _ _
          hstEL
          hstOEL
          _ _ _ _ _
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 P
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := P)
  letI : Field ((NumberField.RingOfIntegers L) ⧸ P) := Ideal.Quotient.field P
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((NumberField.RingOfIntegers L) ⧸ P) := by
    infer_instance
  let Q : Ideal (NumberField.RingOfIntegers E) := P.under (NumberField.RingOfIntegers E)
  letI : Q.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    simpa [Q, Ideal.liesOver_iff] using (show P.LiesOver qI by infer_instance)
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 Q
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := Q)
  letI : P.LiesOver Q := by
    simp [Q, Ideal.liesOver_iff]
  letI : Field ((NumberField.RingOfIntegers E) ⧸ Q) := Ideal.Quotient.field Q
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((NumberField.RingOfIntegers E) ⧸ Q) := by
    infer_instance
  let H : Subgroup (Gal(L/ℚ)) := MulAction.stabilizer (Gal(L/ℚ)) P
  have hHfull :
      Nat.card H =
        qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
          qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
    simpa [H] using
      (@Ideal.card_stabilizer_eq
        ℤ
        (NumberField.RingOfIntegers L)
        (Gal(L/ℚ))
        _ _ _ _ _ _ _ _ _ _ _
        qI
        hqI0
        P
        inferInstance
        inferInstance
        inferInstance)
  letI : Algebra.IsSeparable ((NumberField.RingOfIntegers E) ⧸ Q)
      ((NumberField.RingOfIntegers L) ⧸ P) := by
    infer_instance
  have hHrel_eq :
      MulAction.stabilizer E.fixingSubgroup P = H.subgroupOf E.fixingSubgroup := by
    ext σ
    rfl
  have hHrel :
      Nat.card H =
        Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) := by
    calc
      Nat.card H = Nat.card (H.subgroupOf E.fixingSubgroup) := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPstab).symm.toEquiv
      _ = Nat.card (MulAction.stabilizer E.fixingSubgroup P) := by
        rw [hHrel_eq]
      _ = Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
            Q.inertiaDegIn (NumberField.RingOfIntegers L) := by
              simpa using
                (@Ideal.card_stabilizer_eq
                  (𝓞 ↥E)
                  (𝓞 L)
                  ↥(E.fixingSubgroup)
                  _ _ _ _ _ _ _ _ _ _ _
                  Q
                  hQ0
                  P
                  inferInstance
                  inferInstance
                  inferInstance)
  have hramMul :
      qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
          Q.ramificationIdxIn (NumberField.RingOfIntegers L) =
        qI.ramificationIdxIn (NumberField.RingOfIntegers L) := by
    simpa using
      (Ideal.ramificationIdxIn_mul_ramificationIdxIn'
        (p := qI) Q (Gal(↥E/ℚ)) (NumberField.RingOfIntegers L)
        (Gal(L/ℚ)) E.fixingSubgroup)
  have hinMul :
      qI.inertiaDegIn (NumberField.RingOfIntegers E) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) =
        qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
    simpa using
      (Ideal.inertiaDegIn_mul_inertiaDegIn
        (p := qI) Q (Gal(↥E/ℚ)) (NumberField.RingOfIntegers L)
        (Gal(L/ℚ)) E.fixingSubgroup)
  have hQprod_ne_zero :
      Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) ≠ 0 := by
    rw [← hHrel]
    letI : Finite H := inferInstance
    have hHnonempty : Nonempty ↥H := ⟨⟨1, by simp [H]⟩⟩
    exact Nat.pos_iff_ne_zero.mp <| Nat.card_pos_iff.mpr ⟨hHnonempty, inferInstance⟩
  have hmul :
      qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
          qI.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    let b :=
      Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
        Q.inertiaDegIn (NumberField.RingOfIntegers L)
    have hb_ne_zero : b ≠ 0 := hQprod_ne_zero
    have hprod :
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b = b := by
      calc
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b
          =
            (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
              Q.ramificationIdxIn (NumberField.RingOfIntegers L)) *
              (qI.inertiaDegIn (NumberField.RingOfIntegers E) *
                Q.inertiaDegIn (NumberField.RingOfIntegers L)) := by
                  dsimp [b]
                  ring
        _ =
            qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
              qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
                rw [hramMul, hinMul]
        _ = Nat.card H := by rw [hHfull]
        _ = b := by simpa [b] using hHrel
    have hprod' :
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b = 1 * b := by
      simpa using hprod.trans (one_mul b).symm
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb_ne_zero) hprod'
  have hramIn : qI.ramificationIdxIn (NumberField.RingOfIntegers E) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_right hmul
  have hinIn : qI.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_left hmul
  have hQe : Ideal.ramificationIdx qI Q = 1 := by
    calc
      Ideal.ramificationIdx qI Q
        = qI.ramificationIdxIn (NumberField.RingOfIntegers E) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              qI Q (Gal(↥E/ℚ))
      _ = 1 := hramIn
  have hQf : Ideal.inertiaDeg qI Q = 1 := by
    calc
      Ideal.inertiaDeg qI Q
        = qI.inertiaDegIn (NumberField.RingOfIntegers E) := by
            symm
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              qI Q (Gal(↥E/ℚ))
      _ = 1 := hinIn
  exact splits_completely_conditions ↥E hq Q hQe hQf

theorem restrict_normal_implies
    {M : Type*} [Field M] [Algebra ℚ M]
    (S : IntermediateField ℚ M) [IsGalois ℚ ↥S] [Normal ℚ ↥S]
    [IsScalarTower ℚ ↥S M]
    {σ τ : Gal(M/ℚ)} {y : M} (hy : y ∈ S)
    (hrest :
      ((((AlgEquiv.restrictNormalHom S) σ) ⟨y, hy⟩ : M) =
        (((AlgEquiv.restrictNormalHom S) τ) ⟨y, hy⟩ : M))) :
    σ y = τ y := by
  letI : Normal ℚ ↥S := inferInstance
  have hσ : (((AlgEquiv.restrictNormalHom S) σ) ⟨y, hy⟩ : M) = σ y := by
    change ↑((σ.restrictNormal S) ⟨y, hy⟩) = σ y
    exact AlgEquiv.restrictNormal_commutes (χ := σ) (E := S) ⟨y, hy⟩
  have hτ : (((AlgEquiv.restrictNormalHom S) τ) ⟨y, hy⟩ : M) = τ y := by
    change ↑((τ.restrictNormal S) ⟨y, hy⟩) = τ y
    exact AlgEquiv.restrictNormal_commutes (χ := τ) (E := S) ⟨y, hy⟩
  exact hσ.symm.trans (hrest.trans hτ)

set_option maxHeartbeats 2000000 in
-- Constructing the initial pro-subextension combines several expensive Galois towers.
set_option synthInstance.maxHeartbeats 200000 in
-- Constructing the initial pro-subextension combines several expensive Galois towers.
theorem initial_pro_subextension
    (E : IntermediateField ℚ initialProExtension)
    [FiniteDimensional ℚ E] [IsGalois ℚ E] :
    IsPGroup 3 (Gal(E/ℚ)) := by
  classical
  have hsup_pgroup :
      ∀ {K L : IntermediateField ℚ (AlgebraicClosure ℚ)}
        [FiniteDimensional ℚ K] [IsGalois ℚ K]
        [FiniteDimensional ℚ L] [IsGalois ℚ L],
        IsPGroup 3 (Gal(K/ℚ)) →
        IsPGroup 3 (Gal(L/ℚ)) →
        IsPGroup 3 (Gal(↥(K ⊔ L)/ℚ)) := by
    intro K L _ _ _ _ hK hL
    let M : IntermediateField ℚ (AlgebraicClosure ℚ) := K ⊔ L
    let Ksub : IntermediateField ℚ M :=
      IntermediateField.restrict (show K ≤ M by exact le_sup_left)
    let Lsub : IntermediateField ℚ M :=
      IntermediateField.restrict (show L ≤ M by exact le_sup_right)
    have hKsub : IsPGroup 3 (Gal(Ksub/ℚ)) := by
      let eK : K ≃ₐ[ℚ] Ksub :=
        IntermediateField.restrict_algEquiv (show K ≤ M by exact le_sup_left)
      exact IsPGroup.of_equiv hK (AlgEquiv.autCongr eK)
    have hLsub : IsPGroup 3 (Gal(Lsub/ℚ)) := by
      let eL : L ≃ₐ[ℚ] Lsub :=
        IntermediateField.restrict_algEquiv (show L ≤ M by exact le_sup_right)
      exact IsPGroup.of_equiv hL (AlgEquiv.autCongr eL)
    let eK : K ≃ₐ[ℚ] Ksub :=
      IntermediateField.restrict_algEquiv (show K ≤ M by exact le_sup_left)
    let eL : L ≃ₐ[ℚ] Lsub :=
      IntermediateField.restrict_algEquiv (show L ≤ M by exact le_sup_right)
    letI : IsGalois ℚ ↥Ksub := (AlgEquiv.transfer_galois eK).mp inferInstance
    letI : IsGalois ℚ ↥Lsub := (AlgEquiv.transfer_galois eL).mp inferInstance
    letI : Finite (Gal(Ksub/ℚ)) := by
      infer_instance
    letI : Finite (Gal(Lsub/ℚ)) := by
      infer_instance
    letI : Normal ℚ ↥Ksub := IsGalois.to_normal (F := ℚ) (E := ↥Ksub)
    letI : Normal ℚ ↥Lsub := IsGalois.to_normal (F := ℚ) (E := ↥Lsub)
    letI : IsScalarTower ℚ ↥Ksub ↥M :=
      IntermediateField.isScalarTower_mid' (K := ℚ) (S := Ksub) (L := ↥M)
    letI : IsScalarTower ℚ ↥Lsub ↥M :=
      IntermediateField.isScalarTower_mid' (K := ℚ) (S := Lsub) (L := ↥M)
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hprod : IsPGroup 3 (Gal(Ksub/ℚ) × Gal(Lsub/ℚ)) := by
      obtain ⟨nK, hnK⟩ := IsPGroup.iff_card.mp hKsub
      obtain ⟨nL, hnL⟩ := IsPGroup.iff_card.mp hLsub
      apply IsPGroup.of_card (p := 3) (n := nK + nL)
      rw [Nat.card_prod, hnK, hnL, pow_add]
    let φ : Gal(M/ℚ) →* (Gal(Ksub/ℚ) × Gal(Lsub/ℚ)) :=
      { toFun := fun σ => (AlgEquiv.restrictNormalHom Ksub σ, AlgEquiv.restrictNormalHom Lsub σ)
        map_one' := by
          apply Prod.ext
          · exact (AlgEquiv.restrictNormalHom Ksub).map_one
          · exact (AlgEquiv.restrictNormalHom Lsub).map_one
        map_mul' := by
          intro σ τ
          apply Prod.ext
          · exact (AlgEquiv.restrictNormalHom Ksub).map_mul σ τ
          · exact (AlgEquiv.restrictNormalHom Lsub).map_mul σ τ }
    have hφinj : Function.Injective φ := by
      intro σ τ hστ
      have htop : Ksub ⊔ Lsub = ⊤ := by
        apply top_unique
        intro x hx
        have hlift : IntermediateField.lift (F := M) (Ksub ⊔ Lsub) = M := by
          simp [Ksub, Lsub, M, IntermediateField.lift_sup]
        have hx' : x.1 ∈ IntermediateField.lift (F := M) (Ksub ⊔ Lsub) := by
          simp [hlift]
        exact (IntermediateField.mem_lift (E := Ksub ⊔ Lsub) x).mp hx'
      apply AlgEquiv.ext
      intro x
      have hx :
          x ∈ IntermediateField.adjoin ℚ ((Ksub : Set M) ∪ (Lsub : Set M)) := by
        simp [htop, IntermediateField.adjoin_union]
      exact
        IntermediateField.adjoin_induction
          (s := ((Ksub : Set M) ∪ (Lsub : Set M)))
          (p := fun y _ => σ y = τ y)
          (mem := fun y hy => by
            rw [Set.mem_union] at hy
            rcases hy with hy | hy
            · have hfst := congrArg Prod.fst hστ
              have hfst_eval :
                  (((φ σ).1) ⟨y, hy⟩ : M) = ((((φ τ).1) ⟨y, hy⟩ : Ksub) : M) := by
                exact congrArg (fun z : Ksub => (z : M)) (congrArg (fun f => f ⟨y, hy⟩) hfst)
              have hfst' :
                  (((AlgEquiv.restrictNormalHom Ksub) σ) ⟨y, hy⟩ : M) =
                    (((AlgEquiv.restrictNormalHom Ksub) τ) ⟨y, hy⟩ : M) := by
                simpa [φ] using hfst_eval
              exact
                restrict_normal_implies (M := ↥M) (S := Ksub) hy hfst'
            · have hsnd := congrArg Prod.snd hστ
              have hsnd_eval :
                  (((φ σ).2) ⟨y, hy⟩ : M) = ((((φ τ).2) ⟨y, hy⟩ : Lsub) : M) := by
                exact congrArg (fun z : Lsub => (z : M)) (congrArg (fun f => f ⟨y, hy⟩) hsnd)
              have hsnd' :
                  (((AlgEquiv.restrictNormalHom Lsub) σ) ⟨y, hy⟩ : M) =
                    (((AlgEquiv.restrictNormalHom Lsub) τ) ⟨y, hy⟩ : M) := by
                simpa [φ] using hsnd_eval
              exact
                restrict_normal_implies (M := ↥M) (S := Lsub) hy hsnd')
          (algebraMap := fun q => by simp)
          (add := fun y z _ _ hσy hσz => by simpa using congrArg₂ (· + ·) hσy hσz)
          (inv := fun y _ hσy => by simpa using congrArg Inv.inv hσy)
          (mul := fun y z _ _ hσy hσz => by simpa using congrArg₂ (· * ·) hσy hσz)
          (h := hx)
    exact hprod.of_injective φ hφinj
  have hfinset_mono :
      ∀ {T₁ T₂ : Finset InitialProComponent},
        T₁ ⊆ T₂ →
        proFinsetCompositum T₁ ≤
          proFinsetCompositum T₂ := by
    intro T₁ T₂ hT
    simpa [proFinsetCompositum] using
      (show (⨆ C ∈ T₁, C.1.toIntermediateField) ≤
          (⨆ C ∈ T₂, C.1.toIntermediateField) from
        iSup₂_le fun C hC => le_iSup_of_le C (le_iSup_of_le (hT hC) le_rfl))
  have hstage :
      ∀ T : Finset InitialProComponent,
        IsGalois ℚ ↥(proFinsetCompositum T) ∧
          IsPGroup 3 (Gal(↥(proFinsetCompositum T)/ℚ)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · constructor
      · exact pro_finset_galois ∅
      · have hRat : IsPGroup 3 (Gal(ℚ/ℚ)) := by
          intro σ
          refine ⟨0, ?_⟩
          ext q
          exact σ.commutes q
        let eEmpty :
            proFinsetCompositum ∅ ≃ₐ[ℚ]
              (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
          IntermediateField.equivOfEq
            (by simp [proFinsetCompositum])
        have hBot :
            IsPGroup 3 (Gal(↥(⊥ : IntermediateField ℚ (AlgebraicClosure ℚ))/ℚ)) :=
          IsPGroup.of_equiv hRat
            ((AlgEquiv.autCongr (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ))).symm)
        exact IsPGroup.of_equiv hBot ((AlgEquiv.autCongr eEmpty).symm)
    · intro a T ha hT
      rcases hT with ⟨_, hPT⟩
      letI : IsGalois ℚ ↥(a.1.toIntermediateField) := a.1.isGalois
      letI : IsGalois ℚ ↥(proFinsetCompositum T) :=
        pro_finset_galois T
      let Ksup : IntermediateField ℚ (AlgebraicClosure ℚ) :=
        a.1.toIntermediateField ⊔ proFinsetCompositum T
      have hInsert :
          proFinsetCompositum (insert a T) = Ksup := by
        unfold proFinsetCompositum
        apply le_antisymm
        · refine iSup_le fun C => iSup_le fun hC => ?_
          rcases Finset.mem_insert.mp hC with rfl | hC
          · exact le_sup_left
          · have hCT :
                C.1.toIntermediateField ≤ proFinsetCompositum T := by
              exact le_iSup_of_le C <| le_iSup_of_le hC le_rfl
            exact hCT.trans le_sup_right
        · refine sup_le ?_ ?_
          · exact le_iSup_of_le a <| le_iSup_of_le (Finset.mem_insert_self a T) le_rfl
          · refine iSup_le fun C => iSup_le fun hC => ?_
            exact le_iSup_of_le C <| le_iSup_of_le (Finset.mem_insert_of_mem hC) le_rfl
      constructor
      · simpa
          [proFinsetCompositum, ha, sup_assoc, sup_comm,
            sup_left_comm] using
          pro_finset_galois (insert a T)
      · let eInsert :
            proFinsetCompositum (insert a T) ≃ₐ[ℚ] Ksup :=
          IntermediateField.equivOfEq hInsert
        have hGalSup : IsGalois ℚ ↥Ksup :=
          (AlgEquiv.transfer_galois eInsert).mp
            (pro_finset_galois (insert a T))
        letI : IsGalois ℚ ↥Ksup := hGalSup
        have hSup : IsPGroup 3 (Gal(Ksup/ℚ)) := by
          let Lstage : IntermediateField ℚ (AlgebraicClosure ℚ) :=
            proFinsetCompositum T
          have hLstageGal : IsGalois ℚ ↥Lstage := by
            simpa [Lstage] using pro_finset_galois T
          letI : IsGalois ℚ ↥Lstage := hLstageGal
          have hPT' : IsPGroup 3 (Gal(Lstage/ℚ)) := by
            simpa [Lstage] using hPT
          have hSupStage :
              IsPGroup 3 (Gal(↥(a.1.toIntermediateField ⊔ Lstage)/ℚ)) :=
            @hsup_pgroup (K := a.1.toIntermediateField) (L := Lstage)
              inferInstance inferInstance inferInstance hLstageGal
              a.2.1 hPT'
          simpa [Ksup, Lstage] using hSupStage
        exact IsPGroup.of_equiv hSup ((AlgEquiv.autCongr eInsert).symm)
  let b := Module.finBasis ℚ E
  have hbasis_mem :
      ∀ i, ∃ T : Finset InitialProComponent,
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
          proFinsetCompositum T := by
    intro i
    have hbi :
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
          initialProIntermediate :=
      ((b i : E) : initialProExtension).2
    have hbi' :
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
          ⨆ C : InitialProComponent, C.1.toIntermediateField := by
      simp [initialProIntermediate]
    simpa [proFinsetCompositum] using
      (IntermediateField.exists_finset_of_mem_iSup
        (f := fun C : InitialProComponent => C.1.toIntermediateField) hbi')
  choose Tmem hbmem using hbasis_mem
  let T : Finset InitialProComponent := Finset.univ.biUnion Tmem
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    proFinsetCompositum T
  have hbT :
      ∀ i, (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈ K := by
    intro i
    exact
      hfinset_mono
        (fun C hC => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hC⟩)
        (hbmem i)
  have hKle : K ≤ initialProIntermediate := by
    unfold K proFinsetCompositum initialProIntermediate
    refine iSup_le fun F => iSup_le fun hF => ?_
    exact le_iSup_of_le F le_rfl
  let K' : IntermediateField ℚ initialProExtension := K.restrict hKle
  have hbT' :
      ∀ i, ((b i : E) : initialProExtension) ∈ K' := by
    intro i
    exact
      (IntermediateField.mem_restrict hKle (((b i : E) : initialProExtension))).2
        (hbT i)
  have hET : E ≤ K' := by
    intro x hx
    let xE : E := ⟨x, hx⟩
    have hx_repr :
        x = ∑ i, algebraMap ℚ initialProExtension (b.repr xE i) *
          ((b i : E) : initialProExtension) := by
      simpa [xE, Algebra.smul_def] using (congrArg Subtype.val (b.sum_repr xE)).symm
    rw [hx_repr]
    exact K'.sum_mem fun i _ =>
      K'.mul_mem
        (K'.algebraMap_mem (b.repr xE i))
        (hbT' i)
  let Esub : IntermediateField ℚ K' := IntermediateField.restrict hET
  let eSub : E ≃ₐ[ℚ] Esub := IntermediateField.restrict_algEquiv hET
  let eK : ↥K ≃ₐ[ℚ] ↥K' := IntermediateField.restrict_algEquiv hKle
  letI : FiniteDimensional ℚ ↥K' :=
    FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.surjective
  letI : IsGalois ℚ ↥K := (hstage T).1
  letI : IsGalois ℚ ↥K' := IsGalois.of_algEquiv eK
  letI : FiniteDimensional ℚ ↥Esub :=
    FiniteDimensional.of_surjective eSub.toLinearEquiv.toLinearMap eSub.surjective
  letI : IsGalois ℚ ↥Esub := (AlgEquiv.transfer_galois eSub).mp inferInstance
  have hPK : IsPGroup 3 (Gal(↥K/ℚ)) := (hstage T).2
  have hPK' : IsPGroup 3 (Gal(↥K'/ℚ)) := by
    exact IsPGroup.of_equiv hPK (AlgEquiv.autCongr eK)
  have hPEsub : IsPGroup 3 (Gal(Esub/ℚ)) := by
    let ψ : Gal(↥K'/ℚ) →* Gal(Esub/ℚ) := AlgEquiv.restrictNormalHom Esub
    have hψsurj : Function.Surjective ψ := by
      simpa [ψ] using
        (AlgEquiv.restrictNormalHom_surjective
          (F := ℚ) (K₁ := ↥Esub) (E := ↥K'))
    exact hPK'.of_surjective ψ hψsurj
  exact IsPGroup.of_equiv hPEsub ((AlgEquiv.autCongr eSub).symm)

/-- The remaining blocker: transporting Hermite-Minkowski to the fixed field attached to an
index-`3` subgroup without getting stuck on instance bookkeeping. -/
lemma fixed_abs_discriminant
    {L : Type} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    {M : Subgroup (Gal(L/ℚ))} [M.Normal]
    (hMidx : M.index = 3) :
    2 < absDiscriminant ↥(IntermediateField.fixedField M) := by
  classical
  let E : IntermediateField ℚ L := IntermediateField.fixedField M
  letI : Algebra ℚ ↥E := E.algebra'
  have hEdeg_module : Module.finrank ℚ ↥E = 3 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index
      (L := E), IntermediateField.fixingSubgroup_fixedField, hMidx]
  have h_algE :
      (DivisionRing.toRatAlgebra : Algebra ℚ ↥E) = E.algebra' :=
    Subsingleton.elim _ _
  have hdeg_gt_one_module : 1 < Module.finrank ℚ ↥E := by
    rw [hEdeg_module]
    norm_num
  have hdisc_int : (2 : ℤ) < |NumberField.discr ↥E| := by
    apply NumberField.abs_discr_gt_two (K := ↥E)
    convert hdeg_gt_one_module using 1
    rw [h_algE]
  have hdisc_real : (2 : ℝ) < |(NumberField.discr ↥E : ℝ)| := by
    exact_mod_cast hdisc_int
  simpa [absDiscriminant, E] using hdisc_real

set_option maxHeartbeats 5000000 in
-- The global generation argument expands all local inertia contributions.
set_option synthInstance.maxHeartbeats 500000 in
-- The global generation argument expands all local inertia contributions.
lemma shafarevich_generates_outside
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ L]
    (hPGroup : IsPGroup 3 (Gal(L/ℚ)))
    (hUnram : UnramifiedOutside L initialRamifiedPrimes) :
    let H : {s // s ∈ initialRamifiedPrimes} → Subgroup (Gal(L/ℚ)) := fun r =>
      let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
      letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
      let P0 : Ideal.primesOver p (NumberField.RingOfIntegers L) := Classical.choice inferInstance
      let P : Ideal (NumberField.RingOfIntegers L) := P0.1
      letI : P.IsPrime := P0.2.1
      letI : P.LiesOver p := P0.2.2
      MulAction.stabilizer (Gal(L/ℚ)) P
    (⨆ r, H r) = ⊤ := by
  classical
  let H : {s // s ∈ initialRamifiedPrimes} → Subgroup (Gal(L/ℚ)) := fun r =>
    let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
    letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
    let P0 : Ideal.primesOver p (NumberField.RingOfIntegers L) := Classical.choice inferInstance
    let P : Ideal (NumberField.RingOfIntegers L) := P0.1
    letI : P.IsPrime := P0.2.1
    letI : P.LiesOver p := P0.2.2
    MulAction.stabilizer (Gal(L/ℚ)) P
  let S : Subgroup (Gal(L/ℚ)) := ⨆ r, H r
  by_contra hS
  have hSneq : S ≠ ⊤ := by
    simpa [S] using hS
  obtain ⟨M, hM, hSM⟩ := (eq_top_or_exists_le_coatom S).resolve_left hSneq
  letI : Group.IsNilpotent (Gal(L/ℚ)) := hPGroup.isNilpotent
  have hnc : NormalizerCondition (Gal(L/ℚ)) := Group.normalizerCondition_of_isNilpotent
  letI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M hnc hM
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Algebra ℚ ↥(IntermediateField.fixedField M) :=
    (IntermediateField.fixedField M).algebra'
  haveI : IsGalois ℚ ↥(IntermediateField.fixedField M) :=
    IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := L) M
  have hEfix : (IntermediateField.fixedField M).fixingSubgroup = M := by
    exact IntermediateField.fixingSubgroup_fixedField M
  have hMidx : M.index = 3 := by
    rw [Subgroup.index_eq_card]
    exact coatom_p_group hPGroup hM
  have hEdeg : Module.finrank ℚ ↥(IntermediateField.fixedField M) = 3 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index
      (L := IntermediateField.fixedField M),
      IntermediateField.fixingSubgroup_fixedField, hMidx]
  have hsplit :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        splitsCompletely ↥(IntermediateField.fixedField M) r.1 := by
    intro r
    letI : Algebra ℚ ↥(IntermediateField.fixedField M) :=
      (IntermediateField.fixedField M).algebra'
    have h_algE0 :
        (DivisionRing.toRatAlgebra : Algebra ℚ ↥(IntermediateField.fixedField M)) =
          (IntermediateField.fixedField M).algebra' :=
      Subsingleton.elim _ _
    have hGalE0 :
        @IsGalois ℚ Rat.instField ↥(IntermediateField.fixedField M)
          (IntermediateField.fixedField M).toField DivisionRing.toRatAlgebra := by
      exact
        Eq.ndrec
          (motive := fun A =>
            @IsGalois ℚ Rat.instField ↥(IntermediateField.fixedField M)
              (IntermediateField.fixedField M).toField A)
          (IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := L) M)
          h_algE0.symm
    let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
    letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
    let P0 : Ideal.primesOver p (NumberField.RingOfIntegers L) := Classical.choice inferInstance
    let P : Ideal (NumberField.RingOfIntegers L) := P0.1
    letI : P.IsPrime := P0.2.1
    letI : P.LiesOver p := P0.2.2
    have hPstab :
        MulAction.stabilizer (Gal(L/ℚ)) P ≤
          (IntermediateField.fixedField M).fixingSubgroup := by
      rw [hEfix]
      have hHr : H r ≤ M := (le_iSup H r).trans hSM
      simpa [H, p, P0, P] using hHr
    exact
      @splits_completely_fixing
        L _ _ _ _ (IntermediateField.fixedField M) inferInstance hGalE0
        r.1 (ramified_primes_prime r.1 r.2) P inferInstance inferInstance hPstab
  have hE_unram :
      UnramifiedOutside ↥(IntermediateField.fixedField M) initialRamifiedPrimes := by
    letI : Algebra ℚ ↥(IntermediateField.fixedField M) :=
      (IntermediateField.fixedField M).algebra'
    have h_algE0 :
        (DivisionRing.toRatAlgebra : Algebra ℚ ↥(IntermediateField.fixedField M)) =
          (IntermediateField.fixedField M).algebra' :=
      Subsingleton.elim _ _
    have hGalE0 :
        @IsGalois ℚ Rat.instField ↥(IntermediateField.fixedField M)
          (IntermediateField.fixedField M).toField DivisionRing.toRatAlgebra := by
      exact
        Eq.ndrec
          (motive := fun A =>
            @IsGalois ℚ Rat.instField ↥(IntermediateField.fixedField M)
              (IntermediateField.fixedField M).toField A)
          (IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := L) M)
          h_algE0.symm
    intro q hq hqS
    simpa using
      (@rational_unramified_intermediate
        L _ _ _ _ (IntermediateField.fixedField M) inferInstance hGalE0 q hq (hUnram q hq hqS))
  have hE_idx :
      ∀ q, Nat.Prime q →
        RationalRamificationIdx
          (S := NumberField.RingOfIntegers ↥(IntermediateField.fixedField M)) q 1 := by
    intro q hq
    by_cases hqS : q ∈ initialRamifiedPrimes
    · let r : {s // s ∈ initialRamifiedPrimes} := ⟨q, hqS⟩
      intro P hP
      exact (hsplit r).2 P hP |>.1
    · exact hE_unram q hq hqS
  have hAbsDisc_one : absDiscriminant ↥(IntermediateField.fixedField M) = 1 := by
    let E0 : IntermediateField ℚ L := IntermediateField.fixedField M
    letI : Algebra ℚ ↥E0 := E0.algebra'
    have h_algE0 : (DivisionRing.toRatAlgebra : Algebra ℚ ↥E0) = E0.algebra' :=
      Subsingleton.elim _ _
    have hGalE0 :
        @IsGalois ℚ Rat.instField ↥E0 E0.toField DivisionRing.toRatAlgebra := by
      exact
        Eq.ndrec
          (motive := fun A => @IsGalois ℚ Rat.instField ↥E0 E0.toField A)
          (by
            simpa [E0] using
              (IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := L) M :
                IsGalois ℚ ↥(IntermediateField.fixedField M)))
          h_algE0.symm
    have hNorm_one :
        Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers ↥E0)) = 1 := by
      apply (Nat.eq_one_iff_not_exists_prime_dvd).2
      intro p hp
      exact
        @not_abs_different
          ↥E0 _ _ DivisionRing.toRatAlgebra hGalE0
          (∅ : Finset ℕ) (fun _ => 1) hE_idx (fun {_} _ => rfl) p hp (by simp)
    calc
      absDiscriminant ↥(IntermediateField.fixedField M)
        = (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers ↥E0)) : ℝ) := by
            simpa [E0] using abs_discriminant_different (L := ↥E0)
      _ = 1 := by exact_mod_cast hNorm_one
  have hgt : 2 < absDiscriminant ↥(IntermediateField.fixedField M) := by
    exact fixed_abs_discriminant (L := L) (M := M) hMidx
  linarith [hgt, hAbsDisc_one]

/- Finite Shafarevich generation over `ℚ`, in the exact decomposition-subgroup form needed
for fixed-field quotients of `Q_S^(3)`.

The intended proof is the global argument that an element outside the subgroup generated by these
local stabilizers would give a nontrivial finite quotient unramified away from `S` and with the
chosen local decomposition data killed at every prime in `S`, contradicting the corresponding
Shafarevich/global reciprocity input over `ℚ`. -/
/-- The chosen decomposition subgroup at an initially ramified rational prime. -/
noncomputable def ramifiedDecompositionSubgroup
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (r : {s // s ∈ initialRamifiedPrimes}) : Subgroup (Gal(K/ℚ)) :=
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
  letI : p.IsPrime := rational_prime_ideal
    (ramified_primes_prime r.1 r.2)
  let P0 : Ideal.primesOver p (𝓞 K) := Classical.choice inferInstance
  let P : Ideal (𝓞 K) := P0.1
  letI : P.IsPrime := P0.2.1
  letI : P.LiesOver p := P0.2.2
  MulAction.stabilizer (Gal(K/ℚ)) P

/-- Each local decomposition subgroup lies in the subgroup generated by all of them. -/
lemma ramified_i_sup
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (r : {s // s ∈ initialRamifiedPrimes}) :
    ramifiedDecompositionSubgroup K r ≤
      ⨆ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r :=
  le_iSup (fun r : {s // s ∈ initialRamifiedPrimes} =>
    ramifiedDecompositionSubgroup K r) r

/-- If every subgroup containing the five selected decomposition groups is already the whole
Galois group, then the supremum of those decomposition groups is the whole Galois group. -/
lemma subgroups_every_overgroup
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (h :
      ∀ H : Subgroup (Gal(K/ℚ)),
        (∀ r : {s // s ∈ initialRamifiedPrimes},
          ramifiedDecompositionSubgroup K r ≤ H) →
        H = ⊤) :
    (⨆ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r) = ⊤ := by
  refine h (⨆ r : {s // s ∈ initialRamifiedPrimes},
    ramifiedDecompositionSubgroup K r) ?_
  intro r
  exact ramified_i_sup K r

/-
Global reciprocity/Shafarevich input in quotient form.

For a finite Galois subextension of the initial pro-`3` extension that is unramified outside the
five initial primes, there is no proper quotient in which all chosen decomposition subgroups at
`7, 13, 19, 31, 37` become trivial. Equivalently, any subgroup of `Gal(K/ℚ)` containing those
five decomposition subgroups is already all of `Gal(K/ℚ)`.

This is the precise class-field-theoretic/global-reciprocity bridge still missing from the local
formalization: such a quotient would be everywhere unramified over `ℚ`, hence trivial. -/
/-- The fixed field cut out by a subgroup that contains the selected decomposition groups. -/
noncomputable abbrev ramifiedFixedField
    (K : Type) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (H : Subgroup (Gal(K/ℚ))) : IntermediateField ℚ K :=
  IntermediateField.fixedField H

/-- If the fixed field of a subgroup is just the base field, the subgroup is the whole Galois
group. This is the final formal Galois-correspondence step after the arithmetic quotient
obstruction has ruled out a nontrivial fixed field. -/
lemma ramified_top_bot
    (K : Type) [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {H : Subgroup (Gal(K/ℚ))}
    (hfixed : ramifiedFixedField K H = ⊥) :
    H = ⊤ := by
  have hfix :
      (ramifiedFixedField K H).fixingSubgroup = H := by
    simpa [ramifiedFixedField] using
      (IntermediateField.fixingSubgroup_fixedField H)
  calc
    H = (ramifiedFixedField K H).fixingSubgroup := hfix.symm
    _ = (⊥ : IntermediateField ℚ K).fixingSubgroup := by rw [hfixed]
    _ = ⊤ := by simp

/-- Unramifiedness at a rational prime descends from a finite Galois number
field to an arbitrary finite intermediate field. -/
theorem rational_intermediate_galois
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    (E : IntermediateField ℚ K) [FiniteDimensional ℚ ↥E]
    {q : ℕ} (hq : Nat.Prime q)
    (hK_unram : RationalPrimeUnramified (S := 𝓞 K) q) :
    RationalPrimeUnramified (S := 𝓞 ↥E) q := by
  letI : Algebra ℚ ↥E := E.algebra'
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  obtain ⟨⟨Q, hQprime, hQoverP⟩⟩ := P.nonempty_primesOver (S := 𝓞 K)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver P := hQoverP
  letI : Q.LiesOver qI := Ideal.LiesOver.trans Q P qI
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) Q
  letI : Algebra.IsUnramifiedAt ℤ Q := by
    have hramQ :
        Ideal.ramificationIdx (Ideal.under ℤ Q) Q = 1 := by
      rw [← Ideal.LiesOver.over (P := Q) (p := qI)]
      exact hK_unram Q ⟨hQprime, inferInstance⟩
    exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := 𝓞 K) (p := Q) hQ0).2 hramQ
  letI : Algebra.IsUnramifiedAt ℤ P :=
    Algebra.IsUnramifiedAt.of_liesOver (R := ℤ) P Q
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) P
  have hramP :
      Ideal.ramificationIdx (Ideal.under ℤ P) P = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := 𝓞 ↥E) (p := P) hP0).1
        (show Algebra.IsUnramifiedAt ℤ P from inferInstance)
  rw [← Ideal.LiesOver.over (P := P) (p := qI)] at hramP
  exact hramP

/-- Passing from `K` to the fixed field of any subgroup cannot introduce new ramified rational
primes. This is the field-theoretic part of constructing the quotient/fixed-field obstruction:
the only primes that can still ramify in the fixed field lie in the original set
`initialRamifiedPrimes`. -/
lemma ramified_fixed_outside
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (H : Subgroup (Gal(K/ℚ))) :
    let L : IntermediateField ℚ K := ramifiedFixedField K H
    letI : Field L := L.toField
    letI : Algebra ℚ L := L.algebra'
    letI : NumberField L := NumberField.of_module_finite ℚ L
    UnramifiedOutside L initialRamifiedPrimes := by
  classical
  let L : IntermediateField ℚ K := ramifiedFixedField K H
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  change UnramifiedOutside L initialRamifiedPrimes
  intro q hq hqS
  exact rational_intermediate_galois
    (K := K) (q := q) L hq (hK q hq hqS)

/-- The fixed-field quotient still embeds in the initial pro-`3` extension. Formally, this is the
composition of the subtype embedding `K^H ↪ K` with the given embedding of `K` into the ambient
extension. -/
lemma ramified_embeds_extension
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (H : Subgroup (Gal(K/ℚ))) :
    let L : IntermediateField ℚ K := ramifiedFixedField K H
    letI : Field L := L.toField
    letI : Algebra ℚ L := L.algebra'
    letI : NumberField L := NumberField.of_module_finite ℚ L
    EmbedsIntoExtension L initialProExtension := by
  classical
  let L : IntermediateField ℚ K := ramifiedFixedField K H
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  rcases hKemb with ⟨f⟩
  let i : L →ₐ[ℚ] K := { toRingHom := L.subtype, commutes' := by intro q; rfl }
  exact ⟨f.comp i⟩

/-
Sharp global reciprocity/class-field input for the fixed-field quotient.

The subgroup containment says that each selected local decomposition group acts trivially on the
fixed field `K^H`; equivalently the selected prime over each `r ∈ initialRamifiedPrimes` has
trivial decomposition in that quotient. The previous lemma supplies unramifiedness outside
`initialRamifiedPrimes`. The missing global input is that a finite subextension of the initial
pro-`3` extension with this local behavior at all five initial primes must be the base field.

This is deliberately stated on the constructed fixed field rather than as an opaque dependency on
the original target, so the remaining gap is exactly the global reciprocity/class-field-theory
vanishing statement for the quotient extension. -/
/-- Elements of the subgroup defining the fixed field act trivially on that fixed field. -/
lemma initial_ramified_fixed
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (H : Subgroup (Gal(K/ℚ))) {σ : Gal(K/ℚ)} (hσ : σ ∈ H) :
    ∀ x : ramifiedFixedField K H, σ x.1 = x.1 := by
  intro x
  exact (IntermediateField.mem_fixedField_iff H x.1).1 x.2 σ hσ

/-- If a subgroup contains the selected local decomposition groups, then each of those local
groups acts trivially on the fixed field of the subgroup. -/
lemma ramified_decomposition_fixing
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (H : Subgroup (Gal(K/ℚ)))
    (hH : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ H) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤
        (ramifiedFixedField K H).fixingSubgroup := by
  intro r σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff H x).1 hx σ (hH r hσ)

/-
The remaining global class-field-theory input, stated at the intermediate-field level.

A finite intermediate field of `K` that embeds into the initial pro-`3` extension, is unramified
away from the five initial ramified primes, and on which the selected decomposition groups at
those five primes act trivially, must be the base field. This is the precise vanishing theorem
needed after the local fixed-field reductions. -/
/-- A finite Galois-correspondence reduction: if every automorphism of `K / ℚ` fixes an
intermediate field `L`, then `L` is the base field. -/
lemma ramified_fixing_top
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hfix : L.fixingSubgroup = ⊤) :
    L = ⊥ := by
  rw [← IsGalois.fixedField_fixingSubgroup L, hfix]
  simp

/-- The decomposition-subgroup containment hypothesis says, pointwise, that each selected local
decomposition element fixes every element of the intermediate field. -/
lemma ramified_subgroups_fix
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : K, x ∈ L → σ x = x := by
  intro r σ hσ x hx
  exact (IntermediateField.mem_fixingSubgroup_iff (K := L) σ).1 (hlocal r hσ) x hx

/-- Equivalently, the selected local decomposition groups act trivially on `L` itself. -/
lemma subgroups_act_trivially
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : L, σ x.1 = x.1 := by
  intro r σ hσ x
  exact
    ramified_subgroups_fix
      K L hlocal r σ hσ x.1 x.2

/-- Pointwise trivial action of a selected decomposition group on `L` is exactly membership in
`L.fixingSubgroup`. This is the formal direction used to convert the current target's hypothesis
into the subgroup-containment form of the global reciprocity obstruction. -/
lemma ramified_fixing_pointwise
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hpointwise : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : L, σ x.1 = x.1) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup := by
  intro r σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact hpointwise r σ hσ ⟨x, hx⟩

/-- The subgroup-containment and pointwise-action formulations of local triviality are
equivalent for the five selected decomposition groups. -/
lemma subgroups_fixing_pointwise
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K) :
    (∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) ↔
    (∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : L, σ x.1 = x.1) := by
  constructor
  · intro hlocal
    exact
      subgroups_act_trivially
        K L hlocal
  · intro hpointwise
    exact
      ramified_fixing_pointwise
        K L hpointwise

/- Narrow global reciprocity/Shafarevich helper in local-containment form.

The purely formal part of the target now reduces to this statement: a finite subfield of the
initial pro-`3` extension, unramified away from `initialRamifiedPrimes`, has no nontrivial
quotient on which the five selected decomposition subgroups act trivially. Equivalently, once the
five local decomposition subgroups are contained in `L.fixingSubgroup`, global reciprocity forces
every automorphism of `K / ℚ` to fix `L`.

This helper is narrower than the original target because it removes the pointwise action
translation; the remaining gap is exactly the arithmetic generation/reciprocity assertion for
the selected local subgroups. -/
/-- Final Galois-correspondence step for the narrowed global-reciprocity helper:
once the intermediate field has been shown to be the base field, its fixing subgroup is the
whole finite Galois group. -/
lemma ramified_fixing_bot
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hL : L = ⊥) :
    L.fixingSubgroup = ⊤ := by
  rw [hL]
  simp

/-- Local ramification reduction at the initially ramified primes.

If the chosen decomposition subgroup over `r ∈ initialRamifiedPrimes` acts trivially on an
intermediate field `L`, and `L / ℚ` is Galois, then the rational prime `r` is unramified at every
prime of `L` above `r`.  Mathematically this is the finite-level local statement that the
decomposition group in the Galois closure surjects onto the decomposition group in the subextension;
killing the former on `L` kills inertia at the selected lower prime, and Galoisness of `L / ℚ`
transports that conclusion to all primes above `r`. -/
lemma ramified_ramification_idx
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hL_gal :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      IsGalois ℚ L)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup)
    {r : ℕ} (hrS : r ∈ initialRamifiedPrimes)
    (P : Ideal (𝓞 L))
    (hP : P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r) (𝓞 L)) :
    letI : Field L := L.toField
    letI : Algebra ℚ L := L.algebra'
    letI : NumberField L := NumberField.of_module_finite ℚ L
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P = 1 := by
  classical
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  letI : IsGalois ℚ L := hL_gal
  let r0 : {s // s ∈ initialRamifiedPrimes} := ⟨r, hrS⟩
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal r
  letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r hrS)
  let P0 : Ideal.primesOver p (𝓞 K) := Classical.choice inferInstance
  let PK : Ideal (𝓞 K) := P0.1
  letI : PK.IsPrime := P0.2.1
  letI : PK.LiesOver p := P0.2.2
  have hPstab :
      MulAction.stabilizer (Gal(K/ℚ)) PK ≤ L.fixingSubgroup := by
    simpa [ramifiedDecompositionSubgroup, r0, p, P0, PK] using
      hlocal r0
  have h_algL0 : (DivisionRing.toRatAlgebra : Algebra ℚ L) = L.algebra' :=
    Subsingleton.elim _ _
  have hGalL0 :
      @IsGalois ℚ Rat.instField L L.toField DivisionRing.toRatAlgebra := by
    exact
      Eq.ndrec
        (motive := fun A => @IsGalois ℚ Rat.instField L L.toField A)
        hL_gal
        h_algL0.symm
  have hsplit : splitsCompletely L r := by
    exact
      @splits_completely_fixing
        K _ _ _ _ L inferInstance hGalL0 r
        (ramified_primes_prime r hrS) PK inferInstance inferInstance hPstab
  exact (hsplit.2 P hP).1

lemma ramified_unramified_decomposition
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hL_gal :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      IsGalois ℚ L)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup)
    {r : ℕ} (hrS : r ∈ initialRamifiedPrimes) :
    letI : Field L := L.toField
    letI : Algebra ℚ L := L.algebra'
    letI : NumberField L := NumberField.of_module_finite ℚ L
    RationalPrimeUnramified (S := 𝓞 L) r := by
  classical
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  letI : IsGalois ℚ L := hL_gal
  let _ := hL_unram
  let _ := hL_emb
  intro P hP
  exact
    ramified_ramification_idx
      K L hL_gal hlocal hrS P hP

/-- No finite subfield of the initial pro-`3` extension can be unramified at every rational
prime unless it is the base field.

This is the Hermite-Minkowski/class-field-theory end of the argument: after the local
decomposition hypothesis has removed ramification at the five primes in
`initialRamifiedPrimes`, the field has no finite ramification at all, and over `ℚ` that forces
the extension to be trivial. -/
lemma dvd_different_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (hunram : RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r)
    {P : Ideal (NumberField.RingOfIntegers L)}
    (hP : P ∈ (Ideal.rationalPrimeIdeal r).primesOver (NumberField.RingOfIntegers L)) :
    ¬ P ∣ differentIdeal ℤ (NumberField.RingOfIntegers L) := by
  letI : P.IsPrime := hP.1
  have hP0 : P ≠ ⊥ := prime_ne_bot (L := L) hr hP
  have hunramP : Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ)
      (S := NumberField.RingOfIntegers L) (p := P) hP0]
    rw [← hP.2.over]
    exact hunram P hP
  exact not_dvd_differentIdeal_iff.2 hunramP

lemma abs_different_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {r : ℕ} (hr : Nat.Prime r)
    (hunram : RationalPrimeUnramified (S := NumberField.RingOfIntegers L) r) :
    ¬ r ∣ Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
  have hsup :
      Ideal.map
          (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.rationalPrimeIdeal r) ⊔
        differentIdeal ℤ (NumberField.RingOfIntegers L) = ⊤ := by
    exact sup_different_dvd
      (L := L) hr
      (fun P hP =>
        dvd_different_unramified
          (L := L) hr hunram hP)
  have hunit :
      IsUnit
        ((Ideal.Quotient.mk (differentIdeal ℤ (NumberField.RingOfIntegers L)))
          (r : NumberField.RingOfIntegers L)) := by
    exact r_different_top
      (L := L) hsup
  exact not_abs_r
    (O := NumberField.RingOfIntegers L)
    (I := differentIdeal ℤ (NumberField.RingOfIntegers L))
    (abs_different_ne (L := L)) hr hunit

lemma abs_different_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (hall :
      ∀ q : ℕ, Nat.Prime q →
        RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q)
    (r : ℕ) :
    (Ideal.absNorm
      (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r = 0 := by
  by_cases hr : Nat.Prime r
  · exact factorization_zero_dvd hr
      (abs_different_ne (L := L))
      (abs_different_unramified
        (L := L) hr (hall r hr))
  · exact Nat.factorization_eq_zero_of_not_prime
      (Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L))) hr

lemma abs_all_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (hall :
      ∀ q : ℕ, Nat.Prime q →
        RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q) :
    Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) = 1 := by
  have hfactor :
      Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) =
        Finset.prod (∅ : Finset ℕ) (fun r =>
          r ^
            (Ideal.absNorm
              (differentIdeal ℤ (NumberField.RingOfIntegers L))).factorization r) :=
    factorization_support_subset
      (n := Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)))
      (abs_different_ne (L := L)) ∅
      (fun r _ =>
        abs_different_primes
          (L := L) hall r)
  simpa using hfactor

lemma abs_discriminant_primes
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (hall :
      ∀ q : ℕ, Nat.Prime q →
        RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q) :
    absDiscriminant L = 1 := by
  calc
    absDiscriminant L
        = Ideal.absNorm (differentIdeal ℤ (NumberField.RingOfIntegers L)) := by
          exact abs_discriminant_different (L := L)
    _ = (1 : ℝ) := by
          exact_mod_cast
            abs_all_primes
              (L := L) hall

lemma ramified_intermediate_primes
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hall :
      ∀ q : ℕ, Nat.Prime q →
        letI : Field L := L.toField
        letI : Algebra ℚ L := L.algebra'
        letI : NumberField L := NumberField.of_module_finite ℚ L
        RationalPrimeUnramified (S := 𝓞 L) q) :
    L = ⊥ := by
  let _ := hL_emb
  classical
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hallL :
      ∀ q : ℕ, Nat.Prime q →
        RationalPrimeUnramified (S := NumberField.RingOfIntegers L) q := by
    intro q hq
    exact hall q hq
  have hdisc : absDiscriminant L = 1 :=
    abs_discriminant_primes (L := L) hallL
  by_contra hL_ne
  set n : ℕ := Module.finrank ℚ L with hn
  have hfin_ne_one : n ≠ 1 := by
    intro hfin
    have hfin' : Module.finrank ℚ L = 1 := by
      simpa [hn] using hfin
    exact hL_ne ((IntermediateField.finrank_eq_one_iff).1 hfin')
  have hfin_gt_one_current : 1 < n := by
    refine Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨?_, ?_⟩
    · have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
      simpa [hn] using (Nat.ne_of_lt hpos).symm
    · exact hfin_ne_one
  letI : Algebra ℚ L := DivisionRing.toRatAlgebra
  letI : Module ℚ L := Algebra.toModule
  have hfin_eq : n = Module.finrank ℚ L := by
    rw [hn]
    exact
      @Algebra.finrank_eq_of_equiv_equiv ℚ L _ _ L.algebra' ℚ L _ _
        DivisionRing.toRatAlgebra (RingEquiv.refl ℚ) (RingEquiv.refl L) (by
          ext q
          simp)
  have hfin_gt_one : 1 < Module.finrank ℚ L := by
    simpa [hfin_eq] using hfin_gt_one_current
  have hdisc_gt_int : (2 : ℤ) < |NumberField.discr L| :=
    NumberField.abs_discr_gt_two (K := L) hfin_gt_one
  have hdisc_gt : 2 < absDiscriminant L := by
    have hdisc_gt_real : (2 : ℝ) < (|NumberField.discr L| : ℝ) := by
      exact_mod_cast hdisc_gt_int
    simpa [absDiscriminant, Int.cast_abs] using hdisc_gt_real
  linarith

/-- Galois intermediate-field version of the global-reciprocity reduction.

When `L / ℚ` is Galois, the local decomposition-subgroup containment removes ramification at
the five primes in `initialRamifiedPrimes`; outside that set, unramifiedness is already supplied
by `hL_unram`.  Thus the all-primes vanishing helper applies directly. -/
lemma ramified_intermediate_subgroups
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K)
    (hL_gal :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      IsGalois ℚ L)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    L = ⊥ := by
  classical
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  letI : IsGalois ℚ L := hL_gal
  refine
    ramified_intermediate_primes
      K L hL_emb ?_
  intro q hq
  by_cases hqS : q ∈ initialRamifiedPrimes
  · exact
      ramified_unramified_decomposition
        K L hL_gal hL_unram hL_emb hlocal hqS
  · exact hL_unram q hq hqS

/- Finite Shafarevich generation in the precise form needed by arbitrary intermediate fields.

The Galois-intermediate-field path above explains the local ramification mechanism.  For a
non-normal intermediate field `L`, however, the chosen decomposition subgroup over each rational
prime need not control all conjugate primes over that rational prime.  The remaining global input
is therefore the finite generation statement itself: in every finite Galois subextension of the
initial pro-`3` extension, the five selected decomposition subgroups generate `Gal(K/ℚ)`. -/
/-- Sharper finite Shafarevich/global-reciprocity input in fixed-field form.

If a subgroup of `Gal(K/ℚ)` contains all five selected decomposition subgroups, then its fixed
field is trivial.  This is stronger than the generation statement below because it keeps the
global-reciprocity obstruction at the field level: the fixed field is a finite subextension of
the initial pro-`3` extension, unramified away from `initialRamifiedPrimes`, and locally split at
the five selected ramified primes.  The remaining arithmetic content is exactly that such a
field has no nontrivial quotient over `ℚ`. -/
lemma ramified_embeds_pro
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension) :
    IsPGroup 3 (Gal(K/ℚ)) := by
  classical
  have h_algK : (DivisionRing.toRatAlgebra : Algebra ℚ K) = ‹Algebra ℚ K› :=
    Subsingleton.elim _ _
  cases h_algK
  let _ := hK
  rcases hKemb with ⟨f⟩
  let E : IntermediateField ℚ initialProExtension := f.fieldRange
  let eDefault :
      @AlgEquiv ℚ K ↥E (inferInstance : CommSemiring ℚ)
        (inferInstance : Semiring K) (inferInstance : Semiring ↥E)
        DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra := by
    let g :
        @AlgHom ℚ K ↥E (inferInstance : CommSemiring ℚ)
          (inferInstance : Semiring K) (inferInstance : Semiring ↥E)
          DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra :=
      { toFun := fun x => ⟨f x, by exact ⟨x, rfl⟩⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp
        map_zero' := by
          ext
          simp
        map_add' := by
          intro x y
          ext
          simp
        commutes' := by
          intro q
          ext
          simp }
    have hg_bij : Function.Bijective g := by
      constructor
      · intro x y hxy
        exact f.toRingHom.injective (by simpa [g] using congrArg Subtype.val hxy)
      · intro y
        rcases y.2 with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        ext
        simpa [g] using hx
    exact AlgEquiv.ofBijective g hg_bij
  have hEgal_base :
      @IsGalois ℚ Rat.instField ↥E E.toField DivisionRing.toRatAlgebra :=
    IsGalois.of_algEquiv eDefault
  have hEfin : FiniteDimensional ℚ ↥E := by
    let localAlg : Algebra ℚ ↥E := E.algebra'
    have eLocal :
        @AlgEquiv ℚ K ↥E (inferInstance : CommSemiring ℚ)
          (inferInstance : Semiring K) (inferInstance : Semiring ↥E)
          DivisionRing.toRatAlgebra localAlg := by
      letI : Algebra ℚ ↥E := localAlg
      simpa [E, AlgHom.fieldRange_toSubalgebra f] using
        (AlgEquiv.ofInjectiveField f)
    exact FiniteDimensional.of_surjective eLocal.toLinearEquiv.toLinearMap eLocal.surjective
  have hEbase :=
    @initial_pro_subextension E hEfin hEgal_base
  exact IsPGroup.of_equiv hEbase ((AlgEquiv.autCongr eDefault).symm)

lemma coatom_ne_top
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup 3 Γ) {H : Subgroup Γ} (hH : H ≠ ⊤) :
    ∃ M : Subgroup Γ, IsCoatom M ∧ H ≤ M ∧ M.Normal := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  letI : Group.IsNilpotent Γ := hΓ.isNilpotent
  have hnc : NormalizerCondition Γ := Group.normalizerCondition_of_isNilpotent
  have hMnorm : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M hnc hM
  exact ⟨M, hM, hHM, hMnorm⟩

lemma ramified_coatom_reciprocity
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (M : Subgroup (Gal(K/ℚ))) [M.Normal] (_hM : IsCoatom M)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ M) :
    M = ⊤ := by
  classical
  let L : IntermediateField ℚ K := ramifiedFixedField K M
  have hL_gal :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      IsGalois ℚ L := by
    dsimp [L, ramifiedFixedField]
    infer_instance
  have hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes := by
    simpa [L] using ramified_fixed_outside K hK M
  have hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension := by
    simpa [L] using ramified_embeds_extension K hKemb M
  have hfixM : L.fixingSubgroup = M := by
    simpa [L, ramifiedFixedField] using
      (IntermediateField.fixingSubgroup_fixedField M)
  have hlocalL : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup := by
    intro r
    rw [hfixM]
    exact hlocal r
  have hLbot : L = ⊥ :=
    ramified_intermediate_subgroups
      K L hL_gal hL_unram hL_emb hlocalL
  exact ramified_top_bot K hLbot

lemma ramified_bot_reciprocity
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (H : Subgroup (Gal(K/ℚ)))
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤
        (ramifiedFixedField K H).fixingSubgroup) :
    ramifiedFixedField K H = ⊥ := by
  classical
  have hK_three : IsPGroup 3 (Gal(K/ℚ)) :=
    ramified_embeds_pro
      K hK hKemb
  have hfixH :
      (ramifiedFixedField K H).fixingSubgroup = H := by
    simpa [ramifiedFixedField] using
      (IntermediateField.fixingSubgroup_fixedField H)
  have hlocalH : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ H := by
    intro r
    rw [← hfixH]
    exact hlocal r
  by_cases hHtop : H = ⊤
  · simp [ramifiedFixedField, hHtop]
  · obtain ⟨M, hMcoatom, hHM, hMnormal⟩ :=
      coatom_ne_top
        (Γ := Gal(K/ℚ)) hK_three hHtop
    letI : M.Normal := hMnormal
    have hlocalM : ∀ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r ≤ M := by
      intro r
      exact (hlocalH r).trans hHM
    have hMtop : M = ⊤ :=
      ramified_coatom_reciprocity
        K hK hKemb M hMcoatom hlocalM
    exact False.elim (hMcoatom.1 hMtop)

/-- Subgroup form of the fixed-field reciprocity obstruction.

The only non-formal ingredient is the fixed-field lemma above; after that, finite Galois
correspondence converts `K^H = ℚ` into `H = Gal(K/ℚ)`. -/
lemma ramified_global_reciprocity
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (H : Subgroup (Gal(K/ℚ)))
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ H) :
    H = ⊤ := by
  have hfix :
      (ramifiedFixedField K H).fixingSubgroup = H := by
    simpa [ramifiedFixedField] using
      (IntermediateField.fixingSubgroup_fixedField H)
  apply ramified_top_bot
  exact
    ramified_bot_reciprocity
      K hK hKemb H (by
        intro r
        rw [hfix]
        exact hlocal r)

/-- Finite Shafarevich generation in the precise form needed by arbitrary intermediate fields. -/
lemma subgroups_i_reciprocity
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension) :
    (⨆ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r) = ⊤ := by
  apply subgroups_every_overgroup
  intro H hlocal
  exact
    ramified_global_reciprocity
      K hK hKemb H hlocal

lemma ramified_decomposition_subgroups
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (L : IntermediateField ℚ K)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    L = ⊥ := by
  classical
  let _ := hL_unram
  let _ := hL_emb
  have hDtop :
      (⨆ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r) = ⊤ :=
    subgroups_i_reciprocity
      K hK hKemb
  have hsup_le :
      (⨆ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r) ≤ L.fixingSubgroup :=
    iSup_le hlocal
  have hfix : L.fixingSubgroup = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← hDtop]
      exact hsup_le
  exact ramified_fixing_top K L hfix

/-- Pointwise local triviality is just the elementwise form of the same global-reciprocity
obstruction.  This bridge keeps the arithmetic gap in one place while allowing downstream code
to use the more explicit action-on-`L` formulation. -/
lemma ramified_reciprocity_pointwise
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (L : IntermediateField ℚ K)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hpointwise : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : L, σ x.1 = x.1) :
    L = ⊥ := by
  exact
    ramified_decomposition_subgroups
      K hK hKemb L hL_unram hL_emb
      (ramified_fixing_pointwise
        K L hpointwise)

lemma ramified_fixing_decomp
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (L : IntermediateField ℚ K)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    L.fixingSubgroup = ⊤ := by
  exact
    ramified_fixing_bot K L
      (ramified_decomposition_subgroups
        K hK hKemb L hL_unram hL_emb hlocal)

/-- Sharp global reciprocity input for the current reduction.

The local hypothesis has already been reduced to pointwise trivial action of the selected
decomposition groups on `L`. The remaining class-field-theoretic assertion is that such a finite
subextension of the initial pro-`3` extension has full fixing subgroup in `Gal(K/ℚ)`. -/
lemma ramified_fixing_reciprocity
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (L : IntermediateField ℚ K)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hpointwise : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
        ∀ x : L, σ x.1 = x.1) :
    L.fixingSubgroup = ⊤ := by
  exact
    ramified_fixing_decomp
      K hK hKemb L hL_unram hL_emb
      (ramified_fixing_pointwise
        K L hpointwise)

lemma ramified_decomp_trivial
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (L : IntermediateField ℚ K)
    (hL_unram :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      UnramifiedOutside L initialRamifiedPrimes)
    (hL_emb :
      letI : Field L := L.toField
      letI : Algebra ℚ L := L.algebra'
      letI : NumberField L := NumberField.of_module_finite ℚ L
      EmbedsIntoExtension L initialProExtension)
    (hlocal : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup) :
    L = ⊥ := by
  classical
  have hpointwise :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        ∀ σ : Gal(K/ℚ), σ ∈ ramifiedDecompositionSubgroup K r →
          ∀ x : L, σ x.1 = x.1 :=
    subgroups_act_trivially
      K L hlocal
  exact
    ramified_fixing_top K L
      (ramified_fixing_reciprocity
        K hK hKemb L hL_unram hL_emb hpointwise)

lemma ramified_bot_subgroups
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension)
    (H : Subgroup (Gal(K/ℚ)))
    (hH : ∀ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r ≤ H) :
    ramifiedFixedField K H = ⊥ := by
  classical
  let L : IntermediateField ℚ K := ramifiedFixedField K H
  letI : Field L := L.toField
  letI : Algebra ℚ L := L.algebra'
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hL_unram :
      UnramifiedOutside L initialRamifiedPrimes := by
    simpa [L] using
      (ramified_fixed_outside K hK H)
  have hL_emb :
      EmbedsIntoExtension L initialProExtension := by
    simpa [L] using
      (ramified_embeds_extension K hKemb H)
  have hlocal :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r ≤ L.fixingSubgroup := by
    simpa [L] using
      (ramified_decomposition_fixing K H hH)
  exact
    ramified_decomp_trivial
      K hK hKemb L hL_unram hL_emb hlocal

lemma proper_killing_decomp
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension) :
    ∀ H : Subgroup (Gal(K/ℚ)),
      (∀ r : {s // s ∈ initialRamifiedPrimes},
        ramifiedDecompositionSubgroup K r ≤ H) →
      H = ⊤ := by
  classical
  intro H hH
  exact ramified_top_bot K
    (ramified_bot_subgroups
      K hK hKemb H hH)

/-- Finite Shafarevich generation over `ℚ`, in the exact decomposition-subgroup form needed
for fixed-field quotients of `Q_S^(3)`. -/
lemma outside_subgroups_generate
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : UnramifiedOutside K initialRamifiedPrimes)
    (hKemb : EmbedsIntoExtension K initialProExtension) :
    (⨆ r : {s // s ∈ initialRamifiedPrimes},
      let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
      letI : p.IsPrime := rational_prime_ideal
        (ramified_primes_prime r.1 r.2)
      let P0 : Ideal.primesOver p (𝓞 K) := Classical.choice inferInstance
      let P : Ideal (𝓞 K) := P0.1
      letI : P.IsPrime := P0.2.1
      letI : P.LiesOver p := P0.2.2
      MulAction.stabilizer (Gal(K/ℚ)) P) = ⊤ := by
  classical
  change
    (⨆ r : {s // s ∈ initialRamifiedPrimes},
      ramifiedDecompositionSubgroup K r) = ⊤
  exact
    subgroups_i_reciprocity
      K hK hKemb

/-- Arithmetic Shafarevich input on the finite fixed field attached to `N`.

For the fixed finite Galois quotient `KN / ℚ`, the decomposition groups at the five initially
ramified rational primes generate the whole finite Galois group.  The prime above each rational
prime is the same choice used in `initial_open_family`. -/
lemma decomposition_subgroups_generate
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    letI : FiniteDimensional ℚ KN :=
      (initial_galois_open N).1
    letI : IsGalois ℚ KN :=
      (initial_galois_open N).2
    letI : NumberField KN := NumberField.of_module_finite ℚ KN
    (⨆ r : {s // s ∈ initialRamifiedPrimes},
      let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
      letI : p.IsPrime := rational_prime_ideal
        (ramified_primes_prime r.1 r.2)
      let P0 : Ideal.primesOver p (𝓞 KN) := Classical.choice inferInstance
      let P : Ideal (𝓞 KN) := P0.1
      letI : P.IsPrime := P0.2.1
      letI : P.LiesOver p := P0.2.2
      MulAction.stabilizer (Gal(KN/ℚ)) P) = ⊤ := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  letI : FiniteDimensional ℚ KN :=
    (initial_galois_open N).1
  letI : IsGalois ℚ KN :=
    (initial_galois_open N).2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  exact
    outside_subgroups_generate KN
      (initial_unramified_outside N)
      (embeds_pro_extension N)

/-- Descending the finite fixed-field decomposition subgroups gives the local quotient family. -/
lemma initial_descended_stabilizers
    (N : OpenNormalSubgroup G) :
    let Nclosed : ClosedSubgroup G :=
      { toSubgroup := (N : Subgroup G)
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let KN : IntermediateField ℚ initialProExtension :=
      IntermediateField.fixedField Nclosed.1
    letI : Algebra ℚ KN := KN.algebra'
    letI : FiniteDimensional ℚ KN :=
      (initial_galois_open N).1
    letI : IsGalois ℚ KN :=
      (initial_galois_open N).2
    letI : NumberField KN := NumberField.of_module_finite ℚ KN
    let e : G ⧸ (N : Subgroup G) ≃* Gal(KN/ℚ) := by
      simpa [KN, Nclosed] using
        (galoisFixedField
          (F := ℚ) (L := initialProExtension) Nclosed)
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      initial_open_family N r =
        e.symm.mapSubgroup
          (let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
           letI : p.IsPrime := rational_prime_ideal
             (ramified_primes_prime r.1 r.2)
           let P0 : Ideal.primesOver p (𝓞 KN) := Classical.choice inferInstance
           let P : Ideal (𝓞 KN) := P0.1
           letI : P.IsPrime := P0.2.1
           letI : P.LiesOver p := P0.2.2
           MulAction.stabilizer (Gal(KN/ℚ)) P) := by
  classical
  dsimp [initial_open_family]
  intro r
  rfl

/-- Finite Shafarevich generation input for this particular open-normal quotient.

After the quotient is identified with the finite Galois group of the fixed field, the
decomposition subgroups at the five initially ramified primes should generate that finite group.
The family `initial_open_family` is precisely the descent of
those stabilizers along the quotient equivalence. This is the remaining arithmetic theorem needed
for the local-subgroup generation step. -/
lemma initial_shafarevich_generates
    (N : OpenNormalSubgroup G) :
    (⨆ r, initial_open_family N r) = ⊤ := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  have hKNfg : FiniteDimensional ℚ KN ∧ IsGalois ℚ KN := by
    simpa [KN, Nclosed] using
      (initial_galois_open N)
  letI : FiniteDimensional ℚ KN := hKNfg.1
  letI : IsGalois ℚ KN := hKNfg.2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  let e : G ⧸ (N : Subgroup G) ≃* Gal(KN/ℚ) := by
    simpa [KN, Nclosed] using
      (galoisFixedField
        (F := ℚ) (L := initialProExtension) Nclosed)
  let H : {s // s ∈ initialRamifiedPrimes} → Subgroup (Gal(KN/ℚ)) := fun r =>
    let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
    letI : p.IsPrime := rational_prime_ideal
      (ramified_primes_prime r.1 r.2)
    let P0 : Ideal.primesOver p (𝓞 KN) := Classical.choice inferInstance
    let P : Ideal (𝓞 KN) := P0.1
    letI : P.IsPrime := P0.2.1
    letI : P.LiesOver p := P0.2.2
    MulAction.stabilizer (Gal(KN/ℚ)) P
  have hHtop : (⨆ r, H r) = ⊤ := by
    have hPGroup : IsPGroup 3 (Gal(KN/ℚ)) := by
      exact @initial_pro_subextension KN hKNfg.1 hKNfg.2
    have hUnram : UnramifiedOutside KN initialRamifiedPrimes := by
      exact initial_unramified_outside N
    exact
      shafarevich_generates_outside
        (L := KN) hPGroup hUnram
  have hdesc :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        initial_open_family N r =
          e.symm.mapSubgroup (H r) := by
    simpa [H, KN, Nclosed, e] using
      (initial_descended_stabilizers N)
  rw [show (⨆ r, initial_open_family N r) =
      ⨆ r, e.symm.mapSubgroup (H r) by
        refine iSup_congr fun r => ?_
        exact hdesc r]
  exact i_subgroup_top e H hHtop

/-- Shafarevich generation step for the chosen local quotient subgroup family.

After descending the distinguished decomposition subgroups to `G ⧸ N`, their supremum should be
the whole quotient. This is the precise finite-quotient output needed for the later topological
generation argument. -/
lemma i_sup_top
    (N : OpenNormalSubgroup G) :
    (⨆ r, initial_open_family N r) = ⊤ := by
  exact initial_shafarevich_generates N

/-- Tame local arithmetic makes each chosen local quotient subgroup metacyclic.

The local subgroup should have cyclic inertia, and the corresponding Frobenius quotient should
also be cyclic, so the whole subgroup is metacyclic. -/
lemma initial_open_metacyclic
    (N : OpenNormalSubgroup G) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      IMSubgro (initial_open_family N r) := by
  classical
  let Nclosed : ClosedSubgroup G :=
    { toSubgroup := (N : Subgroup G)
      isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
  let KN : IntermediateField ℚ initialProExtension :=
    IntermediateField.fixedField Nclosed.1
  letI : Algebra ℚ KN := KN.algebra'
  have hKNfix : KN.fixingSubgroup = Nclosed.1 := by
    simpa [KN] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) Nclosed)
  have hKNfg :
      FiniteDimensional ℚ KN ∧ IsGalois ℚ KN :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := ℚ) (K := initialProExtension) KN).mp <| by
        rw [hKNfix]
        refine ⟨N.isOpen', ?_⟩
        change (N : Subgroup G).Normal
        infer_instance
  letI : FiniteDimensional ℚ KN := hKNfg.1
  letI : IsGalois ℚ KN := hKNfg.2
  letI : NumberField KN := NumberField.of_module_finite ℚ KN
  let e : G ⧸ (N : Subgroup G) ≃* Gal(KN/ℚ) := by
    simpa [KN, Nclosed] using
      (galoisFixedField
        (F := ℚ) (L := initialProExtension) Nclosed)
  have hTame :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        RationalTamePrimes
          (S := NumberField.RingOfIntegers KN) r.1 := by
    intro r
    have hPGroup : IsPGroup 3 (Gal(KN/ℚ)) := by
      exact @initial_pro_subextension KN hKNfg.1 hKNfg.2
    have hCardCoprime : Nat.Coprime r.1 (Nat.card (Gal(KN/ℚ))) :=
      p_coprime_ramified hPGroup r
    exact
      primes_coprime_card
        (L := KN) (ramified_primes_prime r.1 r.2) hCardCoprime
  intro r
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
  letI : p.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
  let P0 : Ideal.primesOver p (𝓞 KN) := Classical.choice inferInstance
  let P : Ideal (𝓞 KN) := P0.1
  letI : P.IsPrime := P0.2.1
  letI : P.LiesOver p := P0.2.2
  have hLocal :
      IMSubgro (MulAction.stabilizer (Gal(KN/ℚ)) P) := by
    exact
      tame_decomposition_metacyclic
        (L := KN) (q := r.1)
        (ramified_primes_prime r.1 r.2) (hTame r) P
  simpa [initial_open_family,
    Nclosed, KN, e, p, P] using
    IMSubgro.map_subgroup_mulequiv e.symm
      (MulAction.stabilizer (Gal(KN/ℚ)) P) hLocal

/-- The missing global arithmetic input: the finite quotient has a family of local quotient
subgroups indexed by `initialRamifiedPrimes` whose supremum is `⊤` and whose members are
metacyclic.

The intended arithmetic construction takes `H r` to be the image of a distinguished decomposition
subgroup at `r`; the statement below records exactly the subgroup-theoretic consequences used later
without yet formalizing those decomposition groups themselves. -/
lemma initial_generating_subgroups
    (N : OpenNormalSubgroup G) :
    ∃ H : {s // s ∈ initialRamifiedPrimes} → Subgroup (G ⧸ (N : Subgroup G)),
      (⨆ r, H r) = ⊤ ∧
      ∀ r : {s // s ∈ initialRamifiedPrimes}, IMSubgro (H r) := by
  refine ⟨initial_open_family N, ?_, ?_⟩
  · exact i_sup_top N
  · exact initial_open_metacyclic N

/-- Group-theoretic reduction for the local Shafarevich input.

If a subgroup `H` contains a cyclic normal subgroup `I` and the quotient
`H ⧸ I` is cyclic, then `H` is generated by two elements: one generator of inertia and one lift
of a Frobenius generator of the cyclic quotient. -/
lemma pair_generating_cyclic
    {Q : Type*} [Group Q]
    (H : Subgroup Q) (I : Subgroup H) [I.Normal]
    (hI_cyclic : IsCyclic I)
    (hquot_cyclic : IsCyclic (H ⧸ I)) :
    ∃ y : Fin 2 → Q,
      (∀ i, y i ∈ H) ∧
      Subgroup.closure (Set.range y) = H := by
  obtain ⟨τ, hτgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top I).mp hI_cyclic
  obtain ⟨σbar, hσbargen⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp hquot_cyclic
  obtain ⟨σ, hσeq⟩ := QuotientGroup.mk'_surjective I σbar
  let y : Fin 2 → Q := Fin.cases (τ : Q) (fun _ => (σ : Q))
  refine ⟨y, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (τ : H).2
    · exact σ.2
  · apply le_antisymm
    · apply (Subgroup.closure_le (K := H)).2
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact (τ : H).2
      · exact σ.2
    · intro q hq
      let qH : H := ⟨q, hq⟩
      have hqbar_mem : (QuotientGroup.mk' I) qH ∈ (⊤ : Subgroup (H ⧸ I)) := by
        simp
      rw [← hσbargen] at hqbar_mem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqbar_mem
      have hdiff_mem : qH * σ ^ (-n) ∈ I := by
        have hqeq : (qH : H ⧸ I) = σbar ^ n := by
          simpa using hn.symm
        have hσeq' : (σ : H ⧸ I) = σbar := by
          simpa using hσeq
        apply (QuotientGroup.eq_one_iff _).mp
        change ((qH : H ⧸ I) * (σ : H ⧸ I) ^ (-n)) = 1
        calc
          (qH : H ⧸ I) * (σ : H ⧸ I) ^ (-n) = σbar ^ n * σbar ^ (-n) := by
            rw [hqeq, hσeq']
          _ = 1 := by simp
      rw [← hτgen] at hdiff_mem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdiff_mem
      have hy0 : y 0 ∈ Subgroup.closure (Set.range y) :=
        Subgroup.subset_closure ⟨0, rfl⟩
      have hy1 : y 1 ∈ Subgroup.closure (Set.range y) :=
        Subgroup.subset_closure ⟨1, rfl⟩
      have hτpow_mem : (τ : Q) ^ m ∈ Subgroup.closure (Set.range y) :=
        (Subgroup.zpowers_le.2 (by simpa [y] using hy0))
          (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
      have hσpow_mem : (σ : Q) ^ n ∈ Subgroup.closure (Set.range y) :=
        (Subgroup.zpowers_le.2 (by simpa [y] using hy1))
          (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
      have hqeqH : qH = τ ^ m * σ ^ n := by
        calc
          qH = (qH * σ ^ (-n)) * σ ^ n := by simp [mul_assoc]
          _ = τ ^ m * σ ^ n := by rw [← hm]
      have hqeq : q = (τ : Q) ^ m * (σ : Q) ^ n := by
        simpa using congrArg Subtype.val hqeqH
      exact hqeq ▸ Subgroup.mul_mem _ hτpow_mem hσpow_mem
/-- Any local family satisfying the metacyclic hypothesis is pointwise 2-generated. -/
lemma initial_open_generated
    (N : OpenNormalSubgroup G)
    (H : {s // s ∈ initialRamifiedPrimes} → Subgroup (G ⧸ (N : Subgroup G)))
    (hHmeta :
      ∀ r : {s // s ∈ initialRamifiedPrimes}, IMSubgro (H r)) :
    ∀ r : {s // s ∈ initialRamifiedPrimes},
      ∃ y : Fin 2 → G ⧸ (N : Subgroup G),
        (∀ i, y i ∈ H r) ∧
        Subgroup.closure (Set.range y) = H r := by
  intro r
  rcases hHmeta r with
    ⟨I, hI_normal, hI_cyclic, hquot_cyclic⟩
  letI := hI_normal
  exact
    pair_generating_cyclic
      (H := H r) (I := I) hI_cyclic hquot_cyclic
/-- Once each local subgroup comes with a generating pair, we can assemble them into the global
family indexed by ramified primes and `Fin 2`. -/
lemma initial_pair_family
    (N : OpenNormalSubgroup G)
    (H : {s // s ∈ initialRamifiedPrimes} → Subgroup (G ⧸ (N : Subgroup G)))
    (hpair :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        ∃ y : Fin 2 → G ⧸ (N : Subgroup G),
          (∀ i, y i ∈ H r) ∧
          Subgroup.closure (Set.range y) = H r) :
    ∃ y : (r : {s // s ∈ initialRamifiedPrimes}) → Fin 2 → G ⧸ (N : Subgroup G),
      (∀ r i, y r i ∈ H r) ∧
      (∀ r, Subgroup.closure (Set.range (y r)) = H r) := by
  classical
  choose y hy using hpair
  refine ⟨y, ?_, ?_⟩
  · intro r i
    exact (hy r).1 i
  · intro r
    exact (hy r).2

lemma initial_ten_images
    (N : OpenNormalSubgroup G) :
    ∃ x : ({s // s ∈ initialRamifiedPrimes} × Fin 2) → G ⧸ (N : Subgroup G),
      Subgroup.closure (Set.range x) = ⊤ := by
  rcases initial_generating_subgroups N with
    ⟨H, hHtop, hHmeta⟩
  have hpair :
      ∀ r : {s // s ∈ initialRamifiedPrimes},
        ∃ y : Fin 2 → G ⧸ (N : Subgroup G),
          (∀ i, y i ∈ H r) ∧
          Subgroup.closure (Set.range y) = H r :=
    initial_open_generated N H hHmeta
  rcases initial_pair_family N H hpair with
    ⟨y, hy, hygen⟩
  refine ⟨fun a => y a.1 a.2, ?_⟩
  exact closure_i_sup H y hy hygen hHtop
noncomputable def initialRamifiedTen :
    ({s // s ∈ initialRamifiedPrimes} × Fin 2) ≃ Fin 10 := by
  classical
  have hcard :
      Fintype.card ({s // s ∈ initialRamifiedPrimes} × Fin 2) = 10 := by
    rw [Fintype.card_prod, ramified_primes_card]
    norm_num
  exact Fintype.equivFinOfCardEq hcard

/-- Lift the ten quotient generators to actual elements of `G`, reindexing by `Fin 10`. -/
lemma generated_ten_lifts
    (N : OpenNormalSubgroup G) :
    (quotientGeneratingTuples (Γ := G) 10 N).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := initial_ten_images N
  choose y hy using fun a : ({s // s ∈ initialRamifiedPrimes} × Fin 2) =>
    QuotientGroup.mk'_surjective (N : Subgroup G) (x a)
  let e : ({s // s ∈ initialRamifiedPrimes} × Fin 2) ≃ Fin 10 :=
    initialRamifiedTen
  refine ⟨fun i => y (e.symm i), ?_⟩
  have hrange :
      Set.range (quotientTupleMap (Γ := G) 10 N (fun i => y (e.symm i))) = Set.range x := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simpa [quotientTupleMap] using (hy (e.symm i)).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, by simpa [quotientTupleMap] using hy a⟩
  simpa [quotientGeneratingTuples, hrange] using hx

lemma initial_topologically_fg :
    ∃ d : ℕ, ∃ s : Fin d → G,
      Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤ := by
  refine ⟨10, ?_⟩
  exact topologically_uniformly_quotients
    (Γ := G) 10 generated_ten_lifts

end InitialZassenhausOpen

end STBuild
end TBluepr
end Towers
