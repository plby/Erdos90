import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.FieldTheory.Blueprint
import Submission.NumberTheory.UnramifiedInertia
import Submission.FieldTheory.HMRProThree.FiniteLayer
import Submission.FieldTheory.PrimeKernelBridge
import Submission.ClassField.NormCorrespondence.LocalUnitsInertia
import Submission.ClassField.Reciprocity.ArtinMapStatements
import Submission.NumberTheory.Locals.InertiaGaloisEquiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Ramification-cleanup bridges for finite Galois quotients
-/

noncomputable section

open scoped Pointwise

namespace Submission
namespace TBluepr

universe u

open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip

section ramificationCleanup

/-- Conjugating an automorphism in the inertia group at `g • P` back by `g`
puts it in the inertia group at `P`. -/
theorem inertia_conj_mem
    {R G : Type*} [CommRing R] [Group G] [MulSemiringAction G R]
    (P : Ideal R) (g sigma : G)
    (hsigma : sigma ∈ (g • P).inertia G) :
    g⁻¹ * sigma * g ∈ P.inertia G := by
  intro x
  have h := hsigma (g • x)
  have h' : g • ((g⁻¹ * sigma * g) • x - x) ∈ g • P := by
    simpa [smul_sub, mul_smul] using h
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h'
  simpa [smul_sub, mul_smul] using h'

/-- Conjugating inertia at `P` by `g` gives inertia at the conjugate prime
`g • P`. -/
theorem inertia_mem_conj
    {R G : Type*} [CommRing R] [Group G] [MulSemiringAction G R]
    (P : Ideal R) (g sigma : G)
    (hsigma : sigma ∈ P.inertia G) :
    g * sigma * g⁻¹ ∈ (g • P).inertia G := by
  have hprem : sigma ∈ (g⁻¹ • (g • P)).inertia G := by
    simpa [smul_smul] using hsigma
  simpa only [inv_inv] using
    (inertia_conj_mem (g • P) g⁻¹ sigma hprem)

/-- For a Galois number field, a finite homomorphism that kills inertia at
one prime above `q` kills inertia at every prime above `q`. -/
theorem number_all_inertia
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {E : Type*} [Group E]
    (f : Gal(K/ℚ) →* E) {q : ℕ}
    (P0 : Ideal (NumberField.RingOfIntegers K))
    [P0.IsPrime] [P0.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hP0 : ∀ sigma : P0.inertia Gal(K/ℚ), f sigma.1 = 1)
    (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (sigma : P.inertia Gal(K/ℚ)) :
    f sigma.1 = 1 := by
  letI : IsGaloisGroup Gal(K/ℚ) ℤ
      (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ
      (NumberField.RingOfIntegers K) ℚ K
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (Ideal.rationalPrimeIdeal q) P0 P Gal(K/ℚ)
  have hsigma : sigma.1 ∈ (g • P0).inertia Gal(K/ℚ) := by
    rw [hg]
    exact sigma.2
  let tau : P0.inertia Gal(K/ℚ) :=
    ⟨g⁻¹ * sigma.1 * g, inertia_conj_mem P0 g sigma.1 hsigma⟩
  have htau := hP0 tau
  have hsigmaEq : sigma.1 = g * tau.1 * g⁻¹ := by
    simp [tau, mul_assoc]
  rw [hsigmaEq, map_mul, map_mul, map_inv, htau]
  simp

/-- The valuation-unit subgroup of the finite-place completion, transported
to the adic-completion model used by the idele embedding. -/
noncomputable def placeAdicSubgroup
    (K : Type u) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    Subgroup (P.adicCompletion K)ˣ := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨Submission.CField.Ideles.absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    Submission.CField.Ideles.placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    Submission.CField.Ideles.placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    Submission.CField.Ideles.placeValuativeRel P
  let e :=
    Submission.CField.Ideles.placeCompletionAdic P
  exact (localUnitSubgroup v.Completion).map (Units.map e.toRingHom)

/-- An equivariant equivalence of local integral rings transports integral
inertia. -/
theorem local_ring_inertia
    {R B G H : Type*} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B]
    [Group G] [Group H]
    [MulSemiringAction G R] [MulSemiringAction H B]
    (eG : G ≃* H) (eR : R ≃+* B)
    (hsmul : ∀ sigma x, eR (sigma • x) = eG sigma • eR x)
    (sigma : G) :
    sigma ∈ (IsLocalRing.maximalIdeal R).inertia G ↔
      eG sigma ∈ (IsLocalRing.maximalIdeal B).inertia H := by
  let eResidue : (R ⧸ IsLocalRing.maximalIdeal R) ≃+*
      (B ⧸ IsLocalRing.maximalIdeal B) :=
    IsLocalRing.ResidueField.mapEquiv eR
  have haction : ∀ tau x,
      eG tau • eR.toRingHom x = eR.toRingHom (tau • x) := by
    intro tau x
    exact (hsmul tau x).symm
  have hstable : ∀ (tau : H) (z : B),
      z ∈ IsLocalRing.maximalIdeal B →
        tau • z ∈ IsLocalRing.maximalIdeal B := by
    intro tau z hz
    let etau : B ≃+* B := MulSemiringAction.toRingAut _ _ tau
    have hmap : (IsLocalRing.maximalIdeal B).map etau =
        IsLocalRing.maximalIdeal B :=
      IsLocalRing.map_ringEquiv_maximalIdeal etau
    rw [← hmap]
    exact Ideal.mem_map_of_mem etau hz
  exact inertia_quotient_equiv
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal B)
    eG eR.toRingHom haction hstable eResidue (fun _ => rfl) sigma

local instance cleanupFiniteGaloisIntermediateFieldFiniteDimensional
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ K :=
  K.finiteDimensional

local instance cleanupFiniteGaloisIntermediateFieldIsGalois
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ K :=
  K.isGalois

local instance cleanupAlgebraicClosureAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isAlgebraic ℚ (AlgebraicClosure ℚ) inferInstance
    inferInstance inferInstance inferInstance (AlgebraicClosure.instIsAlgClosure ℚ)

local instance cleanupAlgebraicClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) := by
  rw [normal_iff]
  intro x
  exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

/-- The base prime ideals at which a finite number-field extension has a
ramified prime above them. -/
def ramifiedBaseIdeals
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    Set (Ideal (NumberField.RingOfIntegers K)) :=
  {p | ∃ P : Ideal (NumberField.RingOfIntegers L),
    Ideal.IsPrime P ∧ P ≠ ⊥ ∧
      P.under (NumberField.RingOfIntegers K) = p ∧
        Ideal.ramificationIdx p P ≠ 1}

/-- A finite extension of number fields has only finitely many ramified base prime ideals. -/
theorem ramified_base_ideals
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (ramifiedBaseIdeals K L).Finite := by
  simpa [ramifiedBaseIdeals] using
    (ramified_base_primes
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L))

/-- A concrete finite set containing exactly the ramified base prime ideals. -/
noncomputable def ramifiedBaseFinset
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Finset (Ideal (NumberField.RingOfIntegers K)) :=
  (ramified_base_ideals K L).toFinset

@[simp]
theorem ramified_ideals_finset
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : Ideal (NumberField.RingOfIntegers K)) :
    p ∈ ramifiedBaseFinset K L ↔
      p ∈ ramifiedBaseIdeals K L := by
  simp [ramifiedBaseFinset]

/-- For an injective finite Galois quotient, being unramified outside `S` is
equivalent to every inertia subgroup outside `S` mapping trivially. -/
theorem outside_inertia_ker
    (S : Finset ℕ)
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {E : Type*} [Group E]
    (f : Gal(L/ℚ) →* E) (hf : Function.Injective f) :
    UnramifiedOutside L S ↔
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers L)),
          P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
            P.inertia Gal(L/ℚ) ≤ f.ker := by
  constructor
  · intro hunram q hq hqS P hPprime hPover
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPover
    have hbot : P.inertia Gal(L/ℚ) = ⊥ :=
      number_bot_unramified
        L hq (hunram q hq hqS) P
    rw [hbot]
    exact bot_le
  · intro hinertia q hq hqS P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
    apply ramification_idx_bot L hq P
    apply le_antisymm
    · intro sigma hsigma
      have hsigmaKer : sigma ∈ f.ker :=
        hinertia q hq hqS P inferInstance inferInstance hsigma
      have hsigmaOne : sigma = 1 := by
        apply hf
        simpa using hsigmaKer
      simp [hsigmaOne]
    · exact bot_le

/-- The finite homomorphism induced on the Galois group of the exact fixed
field of an absolute homomorphism. -/
noncomputable def absoluteHomFactor
    {E : Type*} [Group E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup) :
    Gal(K/ℚ) →* E := by
  let restriction : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hsurj : Function.Surjective restriction :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hker : restriction.ker ≤ phi.ker := by
    rw [show restriction.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restriction] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [← hphiKer]
  exact restriction.liftOfSurjective hsurj ⟨phi, hker⟩

/-- The finite factor composes with absolute restriction to the original
homomorphism. -/
theorem absolute_factor_comp
    {E : Type*} [Group E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup) :
    (absoluteHomFactor phi K hphiKer).comp
        (AlgEquiv.restrictNormalHom K.toIntermediateField) = phi := by
  let restriction : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hsurj : Function.Surjective restriction :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hker : restriction.ker ≤ phi.ker := by
    rw [show restriction.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restriction] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [← hphiKer]
  unfold absoluteHomFactor
  exact restriction.liftOfRightInverse_comp
    (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)
    ⟨phi, hker⟩

/-- The finite factor through the exact fixed field is injective. -/
theorem absolute_factor_injective
    {E : Type*} [Group E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup) :
    Function.Injective (absoluteHomFactor phi K hphiKer) := by
  let restriction : Gal(AlgebraicClosure ℚ/ℚ) →* Gal(K/ℚ) :=
    AlgEquiv.restrictNormalHom K.toIntermediateField
  have hsurj : Function.Surjective restriction :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ)
  have hcomp := absolute_factor_comp phi K hphiKer
  apply (injective_iff_map_eq_one _).2
  intro sigma hsigma
  obtain ⟨tau, rfl⟩ := hsurj sigma
  have hphiTau : phi tau = 1 := by
    rw [← DFunLike.congr_fun hcomp tau]
    exact hsigma
  have htauKer : tau ∈ restriction.ker := by
    rw [show restriction.ker = K.toIntermediateField.fixingSubgroup by
      simpa [restriction] using
        (IntermediateField.restrictNormalHom_ker K.toIntermediateField)]
    rw [← hphiKer]
    exact hphiTau
  exact htauKer

/-- An absolute finite homomorphism is unramified outside `S` exactly when
its induced faithful finite quotient kills every inertia subgroup outside
`S`. -/
theorem absolute_outside_ker
    (S : Finset ℕ)
    {E : Type*} [Group E]
    (phi : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hphiKer : phi.ker = K.toIntermediateField.fixingSubgroup) :
    UnramifiedOutside K S ↔
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers K)),
          P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
            P.inertia Gal(K/ℚ) ≤
              (absoluteHomFactor phi K hphiKer).ker :=
  outside_inertia_ker
    S K (absoluteHomFactor phi K hphiKer)
      (absolute_factor_injective phi K hphiKer)

/-- A character obtained by restricting to an intermediate Galois field is
trivial on upper inertia whenever that intermediate field is unramified. This
is the no-new-ramification half of the cubic cleanup construction. -/
theorem character_restriction_unramified
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {A : Type*} [Group A]
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A)
    {q : ℕ} (hq : Nat.Prime q)
    (hCunramified :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      RationalPrimeUnramified
        (S := NumberField.RingOfIntegers C) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (sigma : P.inertia Gal(L/ℚ)) :
    letI : Algebra ℚ C := C.algebra'
    chi ((numberInertiaRestriction C hCgal.to_normal q P sigma :
      (P.under (NumberField.RingOfIntegers C)).inertia Gal(C/ℚ)) :
        Gal(C/ℚ)) = 1 := by
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let Q : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := by
    rw [Ideal.liesOver_iff]
    simpa [Q, Ideal.liesOver_iff] using
      (show P.LiesOver (Ideal.rationalPrimeIdeal q) by infer_instance)
  have hbot : Q.inertia Gal(C/ℚ) = ⊥ :=
    number_bot_unramified
      C hq hCunramified Q
  let res := numberInertiaRestriction C hCgal.to_normal q P
  have hresmem : (res sigma : Gal(C/ℚ)) ∈ Q.inertia Gal(C/ℚ) :=
    (res sigma).property
  have hresone : (res sigma : Gal(C/ℚ)) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hbot]
    exact hresmem
  change chi (res sigma : Gal(C/ℚ)) = 1
  rw [hresone, map_one]

/-- A homomorphism on a subgroup that factors through a surjective quotient
can be cancelled by the inverse of its descended character. -/
noncomputable def inverseFactorCharacter
    {I G A : Type*} [Group I] [Group G] [CommGroup A]
    (restriction : I →* G) (hrestriction : Function.Surjective restriction)
    (lift : I →* A) (hker : restriction.ker ≤ lift.ker) :
    G →* A :=
  invMonoidHom.comp
    (restriction.liftOfSurjective hrestriction ⟨lift, hker⟩)

/-- The inverse descended character cancels the original homomorphism
pointwise on the source. -/
theorem inverse_character_mul
    {I G A : Type*} [Group I] [Group G] [CommGroup A]
    (restriction : I →* G) (hrestriction : Function.Surjective restriction)
    (lift : I →* A) (hker : restriction.ker ≤ lift.ker)
    (sigma : I) :
    inverseFactorCharacter restriction hrestriction lift hker
        (restriction sigma) * lift sigma = 1 := by
  let descended : G →* A :=
    restriction.liftOfSurjective hrestriction ⟨lift, hker⟩
  have hcomp : descended.comp restriction = lift := by
    exact restriction.liftOfRightInverse_comp
      (Function.surjInv hrestriction)
      (Function.rightInverse_surjInv hrestriction)
      ⟨lift, hker⟩
  change (descended (restriction sigma))⁻¹ * lift sigma = 1
  rw [show descended (restriction sigma) = lift sigma by
    exact DFunLike.congr_fun hcomp sigma]
  exact inv_mul_cancel (lift sigma)

/-- If an intermediate cubic field is totally ramified at `q`, every
automorphism of that cubic field has an upper inertia lift. -/
theorem preimage_totally_ramified
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    (tau : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ)) :
    letI : Algebra ℚ C := C.algebra'
    ∃ sigma : P.inertia Gal(L/ℚ),
      AlgEquiv.restrictNormalHom C sigma.1 = tau := by
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let Q : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := by
    rw [Ideal.liesOver_iff]
    simpa [Q, Ideal.liesOver_iff] using
      (show P.LiesOver (Ideal.rationalPrimeIdeal q) by infer_instance)
  have hcardInertia : Nat.card (Q.inertia Gal(C/ℚ)) = 3 :=
    (inertia_ramification_idx (L := C) hq Q).trans hram
  have htop : Q.inertia Gal(C/ℚ) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact hcardInertia.trans hcard.symm
  let tauI : Q.inertia Gal(C/ℚ) :=
    ⟨tau, by rw [htop]; exact Subgroup.mem_top tau⟩
  obtain ⟨sigma, hsigma⟩ :=
    number_restriction_preimage
      C hCfin hCgal hq P tauI
  refine ⟨sigma, ?_⟩
  exact congrArg Subtype.val hsigma

/-- If two homomorphic coordinates jointly detect a group element and both
coordinates have exponent three, then the source has exponent three. -/
theorem cube_injective_prod
    {I G H : Type*} [Group I] [Group G] [Group H]
    (f : I →* G) (g : I →* H)
    (hfg : Function.Injective (f.prod g))
    (hf : ∀ x : I, f x ^ 3 = 1)
    (hg : ∀ x : I, g x ^ 3 = 1)
  (x : I) :
    x ^ 3 = 1 := by
  apply hfg
  change (f (x ^ 3), g (x ^ 3)) = (f 1, g 1)
  simp only [map_pow, map_one]
  exact Prod.ext (hf x) (hg x)

/-- A surjection from a finite cyclic group of exponent three onto a group of
order three is injective. -/
theorem injective_cyclic_cube
    {I G : Type*} [Group I] [Group G] [Finite I]
    (restriction : I →* G)
    (hrestriction : Function.Surjective restriction)
    (hcyclic : IsCyclic I)
    (hcube : ∀ x : I, x ^ 3 = 1)
    (hcard : Nat.card G = 3) :
    Function.Injective restriction := by
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyclic
  have horder : orderOf x = Nat.card I := by
    exact orderOf_eq_card_of_forall_mem_zpowers (fun y => by
      rw [hx]
      exact Subgroup.mem_top y)
  have horderDvd : orderOf x ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (hcube x)
  have hleThree : Nat.card I ≤ 3 := by
    rw [← horder]
    exact Nat.le_of_dvd (by norm_num) horderDvd
  have hle : Nat.card I ≤ Nat.card G := by
    simpa [hcard] using hleThree
  exact (hrestriction.bijective_of_nat_card_le hle).1

/-- Let `C` be a totally ramified cubic intermediate field of `L` at `q`.
Suppose a second coordinate together with restriction to `C` detects upper
inertia, and that the second coordinate has exponent three. Away from `3`,
restriction of inertia to `C` is then an isomorphism. -/
theorem number_restriction_pair
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    {G : Type*} [Group G]
    (other : P.inertia Gal(L/ℚ) →* G)
    (hother : ∀ sigma : P.inertia Gal(L/ℚ), other sigma ^ 3 = 1)
    (hpair :
      letI : Algebra ℚ C := C.algebra'
      Function.Injective
        (other.prod
          (numberInertiaRestriction C hCgal.to_normal q P))) :
    letI : Algebra ℚ C := C.algebra'
    Function.Injective
      (numberInertiaRestriction C hCgal.to_normal q P) := by
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let Q : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  let restriction :=
    numberInertiaRestriction C hCgal.to_normal q P
  have htargetCard : Nat.card (Q.inertia Gal(C/ℚ)) = 3 :=
    (inertia_ramification_idx (L := C) hq Q).trans hram
  have hrestrictionCube :
      ∀ sigma : P.inertia Gal(L/ℚ), restriction sigma ^ 3 = 1 := by
    intro sigma
    have hpow := pow_card_eq_one'
      (G := Q.inertia Gal(C/ℚ)) (x := restriction sigma)
    rwa [htargetCard] at hpow
  have hsourceCube :
      ∀ sigma : P.inertia Gal(L/ℚ), sigma ^ 3 = 1 := by
    intro sigma
    exact cube_injective_prod
      other restriction hpair hother hrestrictionCube sigma
  have hsourcePGroup : IsPGroup 3 (P.inertia Gal(L/ℚ)) := by
    intro sigma
    exact ⟨1, by simpa using hsourceCube sigma⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hsourceCard⟩ := IsPGroup.iff_card.mp hsourcePGroup
  have hcardCoprime :
      Nat.Coprime q (Nat.card (P.inertia Gal(L/ℚ))) := by
    have hcop : Nat.Coprime (q ^ 1) (3 ^ n) :=
      Nat.coprime_pow_primes 1 n hq Nat.prime_three hqne
    rw [hsourceCard]
    simpa using hcop
  obtain ⟨chi, hchi⟩ :=
    tame_units_embedding
      (L := L) hq P hcardCoprime
  have hcyclic : IsCyclic (P.inertia Gal(L/ℚ)) :=
    cyclic_injective_units
      (L := L) hq P chi hchi
  have hsurjective : Function.Surjective restriction :=
    number_restriction_surjective C hCfin hCgal hq P
  exact injective_cyclic_cube
    restriction hsurjective hcyclic hsourceCube htargetCard

/-- Restriction to two normal intermediate fields jointly detects upper
inertia whenever those fields generate the ambient field. -/
theorem restriction_sup_top
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (E C : IntermediateField ℚ L)
    (hEgal : letI : Algebra ℚ E := E.algebra'; IsGalois ℚ E)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    (hsup : E ⊔ C = ⊤)
    (q : ℕ)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Algebra ℚ E := E.algebra'
    letI : Algebra ℚ C := C.algebra'
    Function.Injective
      ((numberInertiaRestriction E hEgal.to_normal q P).prod
        (numberInertiaRestriction C hCgal.to_normal q P)) := by
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra ℚ C := C.algebra'
  letI : IsGalois ℚ E := hEgal
  letI : IsGalois ℚ C := hCgal
  let fullE : Gal(L/ℚ) →* Gal(E/ℚ) := AlgEquiv.restrictNormalHom E
  let fullC : Gal(L/ℚ) →* Gal(C/ℚ) := AlgEquiv.restrictNormalHom C
  have hfull : Function.Injective (fullE.prod fullC) := by
    apply (injective_iff_map_eq_one _).2
    intro sigma hsigma
    have hEone : fullE sigma = 1 := by
      have h := congrArg Prod.fst hsigma
      simpa using h
    have hCone : fullC sigma = 1 := by
      have h := congrArg Prod.snd hsigma
      simpa using h
    have hfixE : sigma ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E]
      exact hEone
    have hfixC : sigma ∈ C.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker C]
      exact hCone
    have hfix : sigma ∈ (E ⊔ C).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hfixE, hfixC⟩
    rw [hsup, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hfix
    exact hfix
  intro sigma tau hsigmaTau
  apply Subtype.ext
  apply hfull
  change (fullE sigma.1, fullC sigma.1) =
    (fullE tau.1, fullC tau.1)
  exact congrArg (fun z => (z.1.1, z.2.1)) hsigmaTau

/-- Under the tame cubic-pair hypotheses, the inverse of the upper-inertia
lift descends to an honest character of the whole cubic Galois group. Thus
this character cancels the lift on every upper inertia element. -/
theorem cubic_cancels_pair
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (C : IntermediateField ℚ L)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A G : Type*} [CommGroup A] [Group G]
    (lift : P.inertia Gal(L/ℚ) →* A)
    (other : P.inertia Gal(L/ℚ) →* G)
    (hother : ∀ sigma : P.inertia Gal(L/ℚ), other sigma ^ 3 = 1)
    (hpair :
      letI : Algebra ℚ C := C.algebra'
      Function.Injective
        (other.prod
          (numberInertiaRestriction C hCgal.to_normal q P))) :
    letI : Algebra ℚ C := C.algebra'
    ∃ chi : Gal(C/ℚ) →* A,
      ∀ sigma : P.inertia Gal(L/ℚ),
        chi (AlgEquiv.restrictNormalHom C sigma.1) * lift sigma = 1 := by
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let Q : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  let restrictionI :=
    numberInertiaRestriction C hCgal.to_normal q P
  have htargetCard : Nat.card (Q.inertia Gal(C/ℚ)) = 3 :=
    (inertia_ramification_idx (L := C) hq Q).trans hram
  have htop : Q.inertia Gal(C/ℚ) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact htargetCard.trans hcard.symm
  have hinjectiveI : Function.Injective restrictionI :=
    number_restriction_pair
      C hCfin hCgal hq hqne P hram other hother hpair
  have hsurjectiveI : Function.Surjective restrictionI :=
    number_restriction_surjective C hCfin hCgal hq P
  let restriction : P.inertia Gal(L/ℚ) →* Gal(C/ℚ) :=
    (Q.inertia Gal(C/ℚ)).subtype.comp restrictionI
  have hinjective : Function.Injective restriction :=
    Subtype.coe_injective.comp hinjectiveI
  have hsurjective : Function.Surjective restriction := by
    intro tau
    let tauI : Q.inertia Gal(C/ℚ) :=
      ⟨tau, by rw [htop]; exact Subgroup.mem_top tau⟩
    obtain ⟨sigma, hsigma⟩ := hsurjectiveI tauI
    refine ⟨sigma, ?_⟩
    exact congrArg Subtype.val hsigma
  have hker : restriction.ker ≤ lift.ker := by
    intro sigma hsigma
    have hsigmaOne : sigma = 1 := by
      apply hinjective
      simpa using hsigma
    simp [hsigmaOne]
  refine ⟨inverseFactorCharacter restriction hsurjective lift hker, ?_⟩
  intro sigma
  exact inverse_character_mul
    restriction hsurjective lift hker sigma

/-- Restriction from a finite Galois field to one of its normal intermediate
fields, with all tower instances internalized. -/
noncomputable def finiteIntermediateRestriction
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCnormal : letI : Algebra ℚ C := C.algebra'; Normal ℚ C) :
    Gal(K/ℚ) →* Gal(C/ℚ) :=
  @AlgEquiv.restrictNormalHom ℚ _ K _ _ C _
    C.algebra' C.toAlgebra (IsScalarTower.of_algebraMap_eq' rfl) hCnormal

/-- Inflate a character of an intermediate field of a finite Galois field to
an absolute character by the two restriction maps. -/
noncomputable def absoluteThroughIntermediate
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCnormal : letI : Algebra ℚ C := C.algebra'; Normal ℚ C)
    {A : Type*} [Group A]
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A) :
    Gal(AlgebraicClosure ℚ/ℚ) →* A := by
  letI : Algebra ℚ C := C.algebra'
  letI : Algebra C K := C.toAlgebra
  letI : IsScalarTower ℚ C K := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal ℚ C := hCnormal
  exact (chi.comp (finiteIntermediateRestriction K C hCnormal)).comp
    (AlgEquiv.restrictNormalHom K.toIntermediateField)

@[simp]
theorem character_through_intermediate
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCnormal : letI : Algebra ℚ C := C.algebra'; Normal ℚ C)
    {A : Type*} [Group A]
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    absoluteThroughIntermediate K C hCnormal chi sigma =
      letI : Algebra ℚ C := C.algebra'
      chi (finiteIntermediateRestriction K C hCnormal
        (AlgEquiv.restrictNormalHom K.toIntermediateField sigma)) := by
  rfl

/-- A finite-level character inflated through a finite Galois field is a
continuous absolute character. -/
theorem absolute_through_continuous
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCnormal : letI : Algebra ℚ C := C.algebra'; Normal ℚ C)
    {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A) :
    Continuous (absoluteThroughIntermediate K C hCnormal chi) := by
  letI : Algebra ℚ C := C.algebra'
  letI : Algebra C K := C.toAlgebra
  letI : IsScalarTower ℚ C K := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal ℚ C := hCnormal
  have hfinite : Continuous
      ((chi.comp (finiteIntermediateRestriction K C hCnormal)) : Gal(K/ℚ) → A) :=
    continuous_of_discreteTopology
  exact hfinite.comp
    (InfiniteGalois.restrictNormalHom_continuous
      (k := ℚ) (K := AlgebraicClosure ℚ) (L := K.toIntermediateField))

/-- Finite-compositum cancellation on upper inertia remains cancellation after
inflating both the character and the lift to the absolute Galois group. -/
theorem absolute_through_inertia
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCnormal : letI : Algebra ℚ C := C.algebra'; Normal ℚ C)
    {A E : Type*} [Group A] [Group E]
    (includeA : A →* E)
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A)
    (liftFinite : Gal(K/ℚ) →* E)
    (liftAbs : Gal(AlgebraicClosure ℚ/ℚ) →* E)
    (hlift : liftFinite.comp
        (AlgEquiv.restrictNormalHom K.toIntermediateField) = liftAbs)
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hcancel :
      letI : Algebra ℚ C := C.algebra'
      ∀ tau : P.inertia Gal(K/ℚ),
        includeA (chi (finiteIntermediateRestriction K C hCnormal tau.1)) *
          liftFinite tau.1 = 1)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ))
    (hsigma : AlgEquiv.restrictNormalHom K.toIntermediateField sigma ∈
      P.inertia Gal(K/ℚ)) :
    includeA (absoluteThroughIntermediate K C hCnormal chi sigma) *
      liftAbs sigma = 1 := by
  letI : Algebra ℚ C := C.algebra'
  letI : Algebra C K := C.toAlgebra
  letI : IsScalarTower ℚ C K := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal ℚ C := hCnormal
  let tau : P.inertia Gal(K/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom K.toIntermediateField sigma, hsigma⟩
  have hliftSigma := DFunLike.congr_fun hlift sigma
  change includeA
      (chi (finiteIntermediateRestriction K C hCnormal
        (AlgEquiv.restrictNormalHom K.toIntermediateField sigma))) *
      liftAbs sigma = 1
  rw [← hliftSigma]
  exact hcancel tau

/-- Inflating a character through `C` introduces no ramification at a rational
prime where `C` is unramified. -/
theorem absolute_through_intermediate
    (K : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ K)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {A : Type*} [Group A]
    (chi : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A)
    {q : ℕ} (hq : Nat.Prime q)
    (hCunramified :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      RationalPrimeUnramified
        (S := NumberField.RingOfIntegers C) q)
    (P : Ideal (NumberField.RingOfIntegers K))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (sigma : Gal(AlgebraicClosure ℚ/ℚ))
    (hsigma : AlgEquiv.restrictNormalHom K.toIntermediateField sigma ∈
      P.inertia Gal(K/ℚ)) :
    absoluteThroughIntermediate K C hCgal.to_normal chi sigma = 1 := by
  letI : Algebra ℚ C := C.algebra'
  letI : Algebra C K := C.toAlgebra
  letI : IsScalarTower ℚ C K := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let tau : P.inertia Gal(K/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom K.toIntermediateField sigma, hsigma⟩
  change chi (finiteIntermediateRestriction K C hCgal.to_normal tau.1) = 1
  unfold finiteIntermediateRestriction
  exact character_restriction_unramified
    C hCfin hCgal chi hq hCunramified P tau

/-- The pointwise product of a finite family of characters. -/
noncomputable def finiteCharacterProduct
    {ι Γ A : Type*} [Group Γ] [CommGroup A]
    (s : Finset ι) (chi : ι → Γ →* A) :
    Γ →* A :=
  s.prod chi

@[simp]
theorem finite_character_product
    {ι Γ A : Type*} [Group Γ] [CommGroup A]
    (s : Finset ι) (chi : ι → Γ →* A) (gamma : Γ) :
    finiteCharacterProduct s chi gamma = s.prod (fun i => chi i gamma) := by
  simp [finiteCharacterProduct]

/-- A finite product of continuous characters is continuous. -/
theorem character_product_continuous
    {ι Γ A : Type*} [Group Γ] [TopologicalSpace Γ]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (s : Finset ι) (chi : ι → Γ →* A)
    (hchi : ∀ i ∈ s, Continuous (chi i)) :
    Continuous (finiteCharacterProduct s chi) := by
  change Continuous (fun gamma => (s.prod chi) gamma)
  simp only [MonoidHom.finsetProd_apply]
  exact continuous_finsetProd s (fun i hi => hchi i hi)

/-- If every factor is trivial at an element, so is their finite product. -/
theorem character_product_one
    {ι Γ A : Type*} [Group Γ] [CommGroup A]
    (s : Finset ι) (chi : ι → Γ →* A) (gamma : Γ)
    (hone : ∀ i ∈ s, chi i gamma = 1) :
    finiteCharacterProduct s chi gamma = 1 := by
  rw [finite_character_product]
  exact Finset.prod_eq_one (fun i hi => hone i hi)

/-- If exactly one relevant factor supplies a prescribed value and all the
other factors are trivial, the finite character product has that value. -/
theorem character_product_single
    {ι Γ A : Type*} [Group Γ] [CommGroup A]
    (s : Finset ι) (chi : ι → Γ →* A) (gamma : Γ)
    (j : ι) (hj : j ∈ s)
    (hother : ∀ i ∈ s, i ≠ j → chi i gamma = 1) :
    finiteCharacterProduct s chi gamma = chi j gamma := by
  simp only [finite_character_product]
  rw [Finset.prod_eq_single j]
  · intro i hi hij
    exact hother i hi hij
  · exact fun h => (h hj).elim

/-- A finite family of independent local corrections cancels a lift at the
chosen prime. -/
theorem character_include_single
    {ι Γ A E : Type*} [Group Γ] [CommGroup A] [Group E]
    (includeA : A →* E)
    (s : Finset ι) (chi : ι → Γ →* A)
    (lift : Γ → E) (gamma : Γ)
    (j : ι) (hj : j ∈ s)
    (hcancel : includeA (chi j gamma) * lift gamma = 1)
    (hother : ∀ i ∈ s, i ≠ j → chi i gamma = 1) :
    includeA (finiteCharacterProduct s chi gamma) * lift gamma = 1 := by
  rw [character_product_single s chi gamma j hj hother]
  exact hcancel

/-- Later tame corrections preserve a correction already made at `3` when
every tame character is unramified at `3`. -/
theorem preserves_prior_cancellation
    {ι Γ A E : Type*} [Group Γ] [CommGroup A] [Group E]
    (includeA : A →* E)
    (s : Finset ι) (chi : ι → Γ →* A)
    (prior : Γ →* A) (lift : Γ → E) (gamma : Γ)
    (htrivial : ∀ i ∈ s, chi i gamma = 1)
    (hprior : includeA (prior gamma) * lift gamma = 1) :
    includeA
        (finiteCharacterProduct s chi gamma * prior gamma) *
      lift gamma = 1 := by
  rw [map_mul, character_product_one s chi gamma htrivial,
    map_one, one_mul]
  exact hprior

/-- In a group of prime order, any subgroup containing a nonidentity element
is the whole group. -/
theorem subgroup_top_ne
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) (hcard : Nat.card G = p)
    (H : Subgroup G)
    (hne : ∃ x : G, x ∈ H ∧ x ≠ 1) :
    H = ⊤ := by
  letI : Fact (Nat.card G).Prime := ⟨hcard ▸ hp⟩
  rcases H.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · obtain ⟨x, hxH, hxne⟩ := hne
    rw [hbot] at hxH
    exact (hxne (Subgroup.mem_bot.mp hxH)).elim
  · exact htop

/-- For a cubic local Galois group, a nontrivial reciprocity-unit image
contained in integral inertia forces both subgroups to be all of the group. -/
theorem cubic_reciprocity_nontrivial
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 3)
    (H I : Subgroup G) (hHI : H ≤ I)
    (hne : ∃ x : G, x ∈ H ∧ x ≠ 1) :
    H = I := by
  have hHtop : H = ⊤ :=
    subgroup_top_ne
      Nat.prime_three hcard H hne
  have hItop : I = ⊤ := by
    apply top_unique
    rw [← hHtop]
    exact hHI
  exact hHtop.trans hItop.symm

/-- Restriction to a lifted intermediate field is detected by restricting
first to its containing finite Galois extension. -/
theorem fixing_restrict_galois
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    (L : FiniteGaloisIntermediateField K Omega)
    (E : IntermediateField K L)
    (sigma : Gal(Omega/K)) :
    sigma ∈ (IntermediateField.lift E).fixingSubgroup ↔
      AlgEquiv.restrictNormalHom L.toIntermediateField sigma ∈
        E.fixingSubgroup := by
  letI : Normal K L := L.isGalois.to_normal
  simp only [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    apply Subtype.ext
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      h x.1 ((IntermediateField.mem_lift x).2 hx)
  · intro h x hx
    have hxL : x ∈ L.toIntermediateField := IntermediateField.lift_le E hx
    let y : L := ⟨x, hxL⟩
    have hyE : y ∈ E := (IntermediateField.mem_lift y).1 hx
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (h y hyE)

/-- Restriction to a lifted intermediate field is detected by restricting
first to its containing finite abelian extension. -/
theorem fixing_lift_restrict
    {K : Type*} [Field K]
    (L : FASubext K)
    (E : IntermediateField K L.finiteIntermediateField)
    (sigma : LocalAbsoluteGalois K) :
    sigma ∈ (IntermediateField.lift E).fixingSubgroup ↔
      AlgEquiv.restrictNormalHom
          L.finiteIntermediateField.toIntermediateField sigma ∈
        E.fixingSubgroup := by
  simp only [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    apply Subtype.ext
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      h x.1 ((IntermediateField.mem_lift x).2 hx)
  · intro h x hx
    have hxL : x ∈
        L.finiteIntermediateField.toIntermediateField :=
      IntermediateField.lift_le E hx
    let y : L.finiteIntermediateField := ⟨x, hxL⟩
    have hyE : y ∈ E := (IntermediateField.mem_lift y).1 hx
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      congrArg Subtype.val (h y hyE)

set_option maxHeartbeats 2000000 in
-- Local reciprocity unfolds the finite fixed-field norm subgroup.
/-- If every local unit is a norm from the field fixed by `I`, finite local
reciprocity sends local units into `I`. -/
theorem reciprocity_inertia_fixed
    (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (L : FASubext K)
    (I : Subgroup Gal(L.finiteIntermediateField/K))
    [I.Normal]
    (hnorm : localUnitSubgroup K ≤
      normSubgroup K (IntermediateField.fixedField I)) :
    reciprocityInertiaSubgroup K rec L ≤ I := by
  let E0 : IntermediateField K L.finiteIntermediateField :=
    IntermediateField.fixedField I
  letI : CommGroup Gal(L.finiteIntermediateField/K) :=
    { (inferInstance : Group Gal(L.finiteIntermediateField/K)) with
      mul_comm := mul_comm' }
  letI : FiniteDimensional K E0 :=
    Module.Finite.of_injective E0.val.toLinearMap Subtype.val_injective
  letI : IsGalois K E0 := IsGalois.of_fixedField_normal_subgroup I
  let qAut : Gal(L.finiteIntermediateField/K) ⧸ I ≃*
      Gal(E0/K) := IsGalois.normalAutEquivQuotient I
  letI : IsMulCommutative Gal(E0/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply qAut.symm.injective
    simpa only [map_mul] using mul_comm (qAut.symm sigma) (qAut.symm tau)
  letI : CommGroup Gal(E0/K) :=
    { (inferInstance : Group Gal(E0/K)) with
      mul_comm := mul_comm' }
  let Efield : IntermediateField K (SeparableClosure K) :=
    IntermediateField.lift E0
  let e : E0 ≃ₐ[K] Efield := IntermediateField.liftAlgEquiv E0
  letI : Module.Finite K Efield := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K Efield := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := Efield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let eAut : Gal(E0/K) ≃* Gal(Efg/K) := e.autCongr
  letI : IsMulCommutative Gal(Efg/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using mul_comm (eAut.symm sigma) (eAut.symm tau)
  let E : FASubext K :=
    { finiteIntermediateField := Efg }
  rintro _ ⟨u, hu, rfl⟩
  have huNorm : (u : Kˣ) ∈ E.normGroup := by
    change (u : Kˣ) ∈ normSubgroup K Efield
    rw [← norm_alg_equiv K E0 Efield e]
    exact hnorm hu
  have huKer : (u : Kˣ) ∈ (finiteReciprocityHom rec E).ker := by
    rw [reciprocity_hom_ker rec hrec.2 E]
    exact huNorm
  have hEone : finiteReciprocityHom rec E (u : Kˣ) = 1 := huKer
  have hrestriction :
      finiteReciprocityHom rec E (u : Kˣ) = 1 ↔
        finiteReciprocityHom rec L (u : Kˣ) ∈ I := by
    obtain ⟨sigma, hsigma⟩ :=
      QuotientGroup.mk'_surjective
        (Subgroup.topologicalClosure
          (commutator (LocalAbsoluteGalois K)))
        (rec (u : Kˣ))
    change localAbelianRestriction E (rec (u : Kˣ)) = 1 ↔
      localAbelianRestriction L (rec (u : Kˣ)) ∈ I
    rw [← hsigma]
    change localAbelianRestriction E (localAbelianizationMap K sigma) = 1 ↔
      localAbelianRestriction L (localAbelianizationMap K sigma) ∈ I
    rw [abelian_restriction_quotient,
      abelian_restriction_quotient]
    change (AlgEquiv.restrictNormalHom E.intermediateField sigma = 1) ↔
      AlgEquiv.restrictNormalHom
        L.finiteIntermediateField.toIntermediateField sigma ∈ I
    rw [← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker]
    change sigma ∈ Efield.fixingSubgroup ↔ _
    rw [fixing_lift_restrict L E0 sigma,
      IntermediateField.fixingSubgroup_fixedField]
  exact hrestriction.mp hEone

/-- In a cubic local extension, inertia-fixed norm surjectivity and one
nontrivial unit Artin symbol identify reciprocity inertia with integral
inertia. -/
theorem cubic_reciprocity_inertia
    (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (L : FASubext K)
    (hcard : Nat.card Gal(L.finiteIntermediateField/K) = 3)
    (I : Subgroup Gal(L.finiteIntermediateField/K))
    [I.Normal]
    (hnorm : localUnitSubgroup K ≤
      normSubgroup K (IntermediateField.fixedField I))
    (hnontrivial : ∃ u : localUnitSubgroup K,
      finiteReciprocityHom rec L (u : Kˣ) ≠ 1) :
    reciprocityInertiaSubgroup K rec L = I := by
  have hle : reciprocityInertiaSubgroup K rec L ≤ I :=
    reciprocity_inertia_fixed
      K rec hrec L I hnorm
  obtain ⟨u, hu⟩ := hnontrivial
  have hne : ∃ x : Gal(L.finiteIntermediateField/K),
      x ∈ reciprocityInertiaSubgroup K rec L ∧ x ≠ 1 := by
    refine ⟨finiteReciprocityHom rec L (u : Kˣ), ?_, hu⟩
    exact ⟨u, u.property, rfl⟩
  exact cubic_reciprocity_nontrivial
    hcard (reciprocityInertiaSubgroup K rec L) I hle hne

set_option maxHeartbeats 2000000 in
-- The norm-subgroup proof expands local-field unit and fixed-field structures.
/-- The local norm equation packages as inclusion of the base local-unit
subgroup in the norm subgroup of the integral-inertia fixed field. -/
theorem local_inertia_fixed
    (K F : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField F] [NormedAlgebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    [IsUltrametricDist F] [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F)))]
    [Algebra (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsFractionRing (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) K F]
    [IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := F)))
      (Valuation.integer (ValuativeRel.valuation K)) F]
    [MulSemiringAction Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F)))]
    [SMulDistribClass Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F))) F]
    (I : Subgroup Gal(F/K)) [I.Normal]
    (hI : I =
      (IsLocalRing.maximalIdeal
        (Valuation.integer (NormedField.valuation (K := F)))).inertia
          Gal(F/K))
    (y : Gal(F/K)) (f : ℕ) (hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' I y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤)
    (hunitOrder : ∀ a : localUnitSubgroup K,
      localOrderHom F
        (Units.map (algebraMap K F).toMonoidHom (a : Kˣ)) = 1) :
    localUnitSubgroup K ≤
      normSubgroup K (IntermediateField.fixedField I) := by
  cases hI
  let I : Subgroup Gal(F/K) :=
    (IsLocalRing.maximalIdeal
      (Valuation.integer (NormedField.valuation (K := F)))).inertia
        Gal(F/K)
  letI : I.Normal := by
    dsimp [I]
    infer_instance
  intro a ha
  let c : Fˣ := Units.map (algebraMap K F).toMonoidHom a
  have hcfixed : ∀ g : Gal(F/K), g • c = c := by
    intro g
    apply Units.ext
    exact g.commutes (a : K)
  obtain ⟨b, hbfixed, hbprod⟩ :=
    inertia_fixed_equation K F inferInstance y f hf
      horder hgen c hcfixed (hunitOrder ⟨a, ha⟩)
  let bval : IntermediateField.fixedField I :=
    ⟨(b : F), by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg Units.val (hbfixed ⟨g, hg⟩)⟩
  let binv : IntermediateField.fixedField I :=
    ⟨((b⁻¹ : Fˣ) : F), by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      have hb := hbfixed ⟨g, hg⟩
      have hbinv := congrArg (fun z : Fˣ => z⁻¹) hb
      exact congrArg Units.val hbinv⟩
  have hbmul : bval * binv = 1 := by
    apply Subtype.ext
    exact b.val_inv
  let bFix : (IntermediateField.fixedField I)ˣ :=
    Units.mkOfMulEqOne bval binv hbmul
  have hbambient : fixedUnitAmbient K F I bFix = b := by
    apply Units.ext
    rfl
  have hnorm := galois_fixed_product
    K F _ y f horder hgen bFix
  rw [hbambient, hbprod] at hnorm
  refine ⟨bFix, ?_⟩
  apply Units.ext
  apply (algebraMap K F).injective
  change algebraMap K F
      (Algebra.norm K (bFix : IntermediateField.fixedField I)) =
    algebraMap K F (a : K)
  simpa [c] using hnorm

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Integral inertia and spectral local-field instances form a large telescope.
/-- In a finite Galois extension of nonarchimedean local fields, base-field
valuation units are norms from the field fixed by integral inertia.  This
packages the cyclic residue-quotient generator required by the preceding
explicit norm-equation lemma. -/
theorem inertia_fixed_norm
    (K F : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField F] [NormedAlgebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    [IsUltrametricDist F] [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F)))]
    [Algebra (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsFractionRing (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) K F]
    [IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := F)))
      (Valuation.integer (ValuativeRel.valuation K)) F]
    [MulSemiringAction Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F)))]
    [SMulDistribClass Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F))) F] :
    let I :=
      (IsLocalRing.maximalIdeal
        (Valuation.integer (NormedField.valuation (K := F)))).inertia
          Gal(F/K)
    localUnitSubgroup K ≤
      normSubgroup K (IntermediateField.fixedField I) := by
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valuation.integer (NormedField.valuation (K := F))
  let p := IsLocalRing.maximalIdeal A
  let P := IsLocalRing.maximalIdeal B
  let I := P.inertia Gal(F/K)
  letI : Module.Finite A B := IsIntegralClosure.finite A K F B
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 <| by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective A K
      apply (algebraMap K F).injective
      rw [← IsScalarTower.algebraMap_apply A K F a,
        ← IsScalarTower.algebraMap_apply A K F b,
        IsScalarTower.algebraMap_apply A B F a,
        IsScalarTower.algebraMap_apply A B F b]
      exact congrArg (algebraMap B F) hab
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  have hBF : Valuation.integer (ValuativeRel.valuation F) = B := by
    ext x
    simp only [B, Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation F).vle_one_iff,
      ← (NormedField.valuation (K := F)).vle_one_iff]
  letI : IsDiscreteValuationRing B := by
    rw [← hBF]
    exact discrete_valuation_ring F
  letI : HenselianLocalRing B := by
    rw [← hBF]
    exact integer_henselian_ring F
  letI : IsGaloisGroup Gal(F/K) A B :=
    IsGaloisGroup.of_isFractionRing Gal(F/K) A B K F
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : P.LiesOver p := by
    change (IsLocalRing.maximalIdeal B).LiesOver
      (IsLocalRing.maximalIdeal A)
    exact (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  let hInormal : I.Normal :=
    maximal_inertia_normal (G := Gal(F/K)) p hp
  letI : I.Normal := hInormal
  let e : Gal(F/K) ⧸ I ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P) :=
    inertiaResidueGalois (G := Gal(F/K)) p hp
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  letI : Finite (A ⧸ p) := by
    dsimp [A, p]
    infer_instance
  letI : Fintype (A ⧸ p) := Fintype.ofFinite _
  letI : Module.Finite (A ⧸ p) (B ⧸ P) := by
    infer_instance
  letI : Finite (B ⧸ P) := by
    exact Module.finite_of_finite (A ⧸ p)
  letI : Fintype (B ⧸ P) := Fintype.ofFinite _
  have hcyclicResidue : IsCyclic ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) := by
    exact Submission.galois_group_cyclic
      (k := A ⧸ p) (K := B ⧸ P)
  have hcyclic : IsCyclic (Gal(F/K) ⧸ I) :=
    e.isCyclic.mpr hcyclicResidue
  obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyclic
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective I z
  let f := orderOf z
  have hf : 0 < f := orderOf_pos z
  have horder : orderOf (QuotientGroup.mk' I y) = f := by
    rw [hy]
  have hgen : Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤ := by
    rw [hy]
    exact hz
  apply local_inertia_fixed
    K F I rfl y f hf horder hgen
  intro a
  have haVal : ValuativeRel.valuation K ((a : Kˣ) : K) = 1 :=
    (local_subgroup K (a : Kˣ)).1 a.property
  have haNorm : ‖((a : Kˣ) : K)‖₊ = 1 := by
    rw [← NormedField.valuation_apply]
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
      (NormedField.valuation (K := K))).eq_one_iff_eq_one.mp haVal
  let aF : Fˣ := Units.map (algebraMap K F).toMonoidHom (a : Kˣ)
  have haFNorm : ‖(aF : F)‖₊ = 1 := by
    calc
      ‖(aF : F)‖₊ = ‖((a : Kˣ) : K)‖₊ :=
        nnnorm_algebraMap' F (((a : Kˣ) : K))
      _ = 1 := haNorm
  have haFVal : ValuativeRel.valuation F (aF : F) = 1 := by
    apply (ValuativeRel.isEquiv (ValuativeRel.valuation F)
      (NormedField.valuation (K := F))).eq_one_iff_eq_one.mpr
    simpa only [NormedField.valuation_apply] using haFNorm
  apply Multiplicative.toAdd.injective
  change localUnitOrder F (Additive.ofMul aF) = 0
  apply le_antisymm
  · have h := (local_order_valuation F aF 1).2
        (by simp [haFVal])
    simpa using h
  · have h := (local_order_valuation F 1 aF).2
        (by simp [haFVal])
    simpa using h

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The cubic reciprocity comparison synthesizes the full spectral field tower.
/-- For a cubic finite abelian layer with its canonical spectral local-field
structure, local reciprocity units are exactly integral inertia as soon as
one unit has nontrivial Artin symbol. -/
theorem cubic_reciprocity_integral
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (L : FASubext K)
    (hcard : Nat.card Gal(L.finiteIntermediateField/K) = 3)
    (hnontrivial : ∃ a : localUnitSubgroup K,
      finiteReciprocityHom rec L (a : Kˣ) ≠ 1) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    let A := Valuation.integer (ValuativeRel.valuation K)
    let B := Valuation.integer (NormedField.valuation (K := L.1))
    letI : Algebra A B := valuativeSpectralAlgebra K L.1
    letI : Algebra B L.1 := B.subtype.toAlgebra
    letI : IsScalarTower A B L.1 :=
      valuativeSpectralTower K L.1
    letI : IsIntegralClosure B A L.1 :=
      spectral_integer_valuative K L.1
    letI : MulSemiringAction Gal(L.1/K) B :=
      IsIntegralClosure.MulSemiringAction A K L.1 B
    reciprocityInertiaSubgroup K rec L =
      (IsLocalRing.maximalIdeal
        (Valuation.integer (NormedField.valuation (K := L.1)))).inertia
          Gal(L.1/K) := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valuation.integer (NormedField.valuation (K := L.1))
  letI : Algebra A B := valuativeSpectralAlgebra K L.1
  letI : Algebra B L.1 := B.subtype.toAlgebra
  letI : IsFractionRing B L.1 :=
    (Valuation.integer.integers
      (NormedField.valuation (K := L.1))).isFractionRing
  letI : IsScalarTower A B L.1 :=
    valuativeSpectralTower K L.1
  letI : IsScalarTower A K L.1 :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A L.1 :=
    spectral_integer_valuative K L.1
  letI : MulSemiringAction Gal(L.1/K) B :=
    IsIntegralClosure.MulSemiringAction A K L.1 B
  let I := (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K)
  letI : I.Normal := by
    dsimp [I]
    infer_instance
  have hnorm : localUnitSubgroup K ≤
      normSubgroup K (IntermediateField.fixedField I) :=
    inertia_fixed_norm K L.1
  exact cubic_reciprocity_inertia
    K rec hrec L hcard I hnorm hnontrivial

set_option maxHeartbeats 3000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The finite abelian layer carries a large synthesized local-field structure.
/-- For any finite abelian layer with its canonical spectral local-field
structure, local reciprocity sends valuation units into integral inertia. -/
theorem reciprocity_subgroup_integral
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (rec : Kˣ →* AbsoluteAbelianGalois K)
    (hrec : IsReciprocityMap K rec)
    (L : FASubext K) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    let A := Valuation.integer (ValuativeRel.valuation K)
    let B := Valuation.integer (NormedField.valuation (K := L.1))
    letI : Algebra A B := valuativeSpectralAlgebra K L.1
    letI : Algebra B L.1 := B.subtype.toAlgebra
    letI : IsScalarTower A B L.1 :=
      valuativeSpectralTower K L.1
    letI : IsIntegralClosure B A L.1 :=
      spectral_integer_valuative K L.1
    letI : MulSemiringAction Gal(L.1/K) B :=
      IsIntegralClosure.MulSemiringAction A K L.1 B
    reciprocityInertiaSubgroup K rec L ≤
      (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K) := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  let A := Valuation.integer (ValuativeRel.valuation K)
  let B := Valuation.integer (NormedField.valuation (K := L.1))
  letI : Algebra A B := valuativeSpectralAlgebra K L.1
  letI : Algebra B L.1 := B.subtype.toAlgebra
  letI : IsFractionRing B L.1 :=
    (Valuation.integer.integers
      (NormedField.valuation (K := L.1))).isFractionRing
  letI : IsScalarTower A B L.1 :=
    valuativeSpectralTower K L.1
  letI : IsScalarTower A K L.1 := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A L.1 :=
    spectral_integer_valuative K L.1
  letI : MulSemiringAction Gal(L.1/K) B :=
    IsIntegralClosure.MulSemiringAction A K L.1 B
  let I := (IsLocalRing.maximalIdeal B).inertia Gal(L.1/K)
  letI : I.Normal := by dsimp [I]; infer_instance
  apply reciprocity_inertia_fixed
    K rec hrec L I
  exact inertia_fixed_norm K L.1

/- The stronger local-Artin/global-inertia transport below is not needed by
the explicit cyclotomic cleanup route.  Keep the work-in-progress out of the
compiled API until its expensive integral-closure transport is streamlined.
set_option maxHeartbeats 5000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
/-- A finite-layer local Artin map sends the transported adic local-unit
subgroup into the global inertia subgroup at the chosen upper prime. -/
theorem artin_adic_inertia
    (K : Type u) [Field K] [NumberField K]
    (L : FASubext K) [NumberField L.1]
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (phi : (P.adicCompletion K)ˣ →* Gal(L.1/K))
    (hphi : LayerLocalArtin L P Q phi) :
    (placeAdicSubgroup K P).map phi ≤
      (upperPrime (K := K) (L := L.1) P Q).asIdeal.inertia Gal(L.1/K) := by
  let v := (FinitePlace.mk P).val
  let q := upperPrime (K := K) (L := L.1) P Q
  dsimp [LayerLocalArtin] at hphi
  rcases hphi with ⟨w, hwv, hwq, M, e, rec, hrec, hformula⟩
  let wAbove :
      Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L.1) v := ⟨w, hwv⟩
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  have hw : w.IsNontrivial :=
    absolute_extension_nontrivial v wAbove
  have hwna : IsNonarchimedean w :=
    absolute_extension_nonarchimedean v wAbove
  let Qw := nonarchimedeanHeightSpectrum w hw hwna
  have hQwq : Qw = q := by
    apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    ext x
    change x ∈ nonarchimedeanPrimeIdeal w hwna ↔ x ∈ q.asIdeal
    rw [nonarchimedean_prime_ideal,
      ← FinitePlace.norm_lt_one_iff_mem L.1 q]
    exact hwq.lt_one_iff
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact w.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (AbsoluteValue.LiesOver w v) := ⟨hwv⟩
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : FiniteDimensional v.Completion w.Completion :=
    placeCompletionDimensional v wAbove
  letI : Finite
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L.1) v) :=
    completion_above_pretransitive P
  letI : IsGalois v.Completion w.Completion :=
    placeCompletionGalois v wAbove
  let A := completionIntegerRing v
  let B := completionIntegerRing w
  letI : Algebra A v.Completion := A.subtype.toAlgebra
  letI : Algebra A B := completionIntegerLies v w hwv
  letI : Algebra B w.Completion := B.subtype.toAlgebra
  letI : Algebra A w.Completion :=
    ((completionLies v w hwv).comp A.subtype).toAlgebra
  letI : IsScalarTower A B w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A v.Completion w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing A v.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := v.Completion))).isFractionRing
  letI : IsIntegralClosure B A w.Completion :=
    completion_integer_closure v w hwv
      (Algebra.IsAlgebraic.of_finite v.Completion w.Completion)
  letI : MulSemiringAction Gal(w.Completion/v.Completion) B :=
    IsIntegralClosure.MulSemiringAction A v.Completion w.Completion B
  -- Canonical spectral local structure on the finite abelian layer `M`.
  letI : Algebra.IsAlgebraic v.Completion M.1 :=
    Algebra.IsAlgebraic.of_finite v.Completion M.1
  letI : NontriviallyNormedField M.1 :=
    FLExt.nontriviallyNormedField v.Completion M.1
  letI : NormedAlgebra v.Completion M.1 :=
    spectralNorm.normedAlgebra v.Completion M.1
  letI : IsUltrametricDist M.1 :=
    IsUltrametricDist.of_normedAlgebra v.Completion
  letI : ValuativeRel M.1 :=
    FLExt.valuativeRel v.Completion M.1
  letI : Valuation.Compatible (NormedField.valuation (K := M.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M.1))
  letI : IsNonarchimedeanLocalField M.1 :=
    FLExt.nonarchimedeanLocalField v.Completion M.1
  let BM := Valuation.integer (NormedField.valuation (K := M.1))
  letI : Algebra A BM := valuativeSpectralAlgebra v.Completion M.1
  letI : Algebra BM M.1 := BM.subtype.toAlgebra
  letI : IsScalarTower A BM M.1 :=
    valuativeSpectralTower v.Completion M.1
  letI : IsIntegralClosure BM A M.1 :=
    spectral_integer_valuative v.Completion M.1
  letI : MulSemiringAction Gal(M.1/v.Completion) BM :=
    IsIntegralClosure.MulSemiringAction A v.Completion M.1 BM
  have hrecInertia : reciprocityInertiaSubgroup v.Completion rec M ≤
      (IsLocalRing.maximalIdeal BM).inertia Gal(M.1/v.Completion) :=
    reciprocity_subgroup_integral
      v.Completion rec hrec M
  -- Transport spectral integers along `e` via the uniqueness of integral
  -- closures, then transport inertia equivariantly.
  let CM := integralClosure A M.1
  let CW := integralClosure A w.Completion
  let eA : M.1 ≃ₐ[A] w.Completion := e.restrictScalars A
  let eBMCM : BM ≃ₐ[A] CM := IsIntegralClosure.equiv A BM M.1 CM
  let eCMCW : CM ≃ₐ[A] CW := eA.mapIntegralClosure
  let eCWB : CW ≃ₐ[A] B := IsIntegralClosure.equiv A CW w.Completion B
  let eB : BM ≃ₐ[A] B := (eBMCM.trans eCMCW).trans eCWB
  have heB (x : BM) : algebraMap B w.Completion (eB x) =
      e (algebraMap BM M.1 x) := by
    simp [eB, eBMCM, eCMCW, eCWB, eA]
  have heBsmul (tau : Gal(M.1/v.Completion)) (x : BM) :
      eB (tau • x) = (e.autCongr tau) • eB x := by
    apply (algebraMap B w.Completion).injective
    rw [heB, heB]
    rfl
  rintro sigma ⟨x, hxU, rfl⟩
  rcases hxU with ⟨u, hu, rfl⟩
  let eAdic := placeCompletionAdic P
  let tauM : Gal(M.1/v.Completion) :=
    finiteReciprocityHom rec M (u : v.Completionˣ)
  have htauMrec : tauM ∈ reciprocityInertiaSubgroup
      v.Completion rec M := ⟨u, hu, rfl⟩
  have htauMint : tauM ∈
      (IsLocalRing.maximalIdeal BM).inertia Gal(M.1/v.Completion) :=
    hrecInertia htauMrec
  have htauWint : e.autCongr tauM ∈
      (IsLocalRing.maximalIdeal B).inertia
        Gal(w.Completion/v.Completion) :=
    (local_ring_inertia e.autCongr eB.toRingEquiv
      heBsmul tauM).mp htauMint
  let sigmaD : absoluteValueDecomposition v w :=
    (decompositionCompletionExtension v w).symm
      (e.autCongr tauM)
  have hsigmaGlobal : (sigmaD : Gal(L.1/K)) ∈ Qw.asIdeal.inertia Gal(L.1/K) :=
    (decomposition_completion_inertia
      v (by exact_mod_cast finitePlaceAbsoluteValue_isNonarchimedean P)
      wAbove sigmaD).mpr htauWint
  rw [hQwq] at hsigmaGlobal
  have hphiApply := hformula (eAdic (u : v.Completionˣ))
  change phi (eAdic (u : v.Completionˣ)) = sigmaD at hphiApply
  simpa [tauM, sigmaD, eAdic] using hphiApply ▸ hsigmaGlobal

-/

/-!
## Extending a local-unit character
-/

/-- A fixed element of normalized local order one. -/
noncomputable def cleanupLocalUniformizer
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))] : Kˣ :=
  (Classical.choose (local_order_surjective K (1 : ℤ))).toMul

@[simp]
theorem cleanup_uniformizer_order
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))] :
    localUnitOrder K
      (Additive.ofMul (cleanupLocalUniformizer K)) = 1 :=
  Classical.choose_spec (local_order_surjective K (1 : ℤ))

/-- An element of a local field is a valuation unit exactly when its
normalized additive order is zero. -/
theorem local_order_zero
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (x : Kˣ) :
    x ∈ localUnitSubgroup K ↔
      localUnitOrder K (Additive.ofMul x) = 0 := by
  constructor
  · intro hx
    have hxval : ValuativeRel.valuation K (x : K) = 1 :=
      (local_subgroup K x).1 hx
    apply le_antisymm
    · have h := (local_order_valuation K x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation K 1 x).2
          (by simp [hxval])
      simpa using h
  · intro hx
    apply (local_subgroup K x).2
    have hone :
        localUnitOrder K (Additive.ofMul (1 : Kˣ)) = 0 :=
      map_zero (localUnitOrder K)
    apply le_antisymm
    · have hle : localUnitOrder K (Additive.ofMul (1 : Kˣ)) ≤
          localUnitOrder K (Additive.ofMul x) := by
        simp [hx]
      simpa using
        (local_order_valuation K (1 : Kˣ) x).1 hle
    · have hle : localUnitOrder K (Additive.ofMul x) ≤
          localUnitOrder K (Additive.ofMul (1 : Kˣ)) := by
        simp [hx]
      simpa using
        (local_order_valuation K x (1 : Kˣ)).1 hle

/-- Remove the uniformizer power from a nonzero local-field element. -/
noncomputable def localPartValue
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (x : Kˣ) : Kˣ :=
  x * cleanupLocalUniformizer K ^
    (-localUnitOrder K (Additive.ofMul x))

theorem local_part_value
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (x : Kˣ) :
    localPartValue K x ∈ localUnitSubgroup K := by
  rw [local_order_zero]
  change localUnitOrder K
      (Additive.ofMul
        (x * cleanupLocalUniformizer K ^
          (-localUnitOrder K (Additive.ofMul x)))) = 0
  rw [show Additive.ofMul
      (x * cleanupLocalUniformizer K ^
        (-localUnitOrder K (Additive.ofMul x))) =
      Additive.ofMul x +
        (-localUnitOrder K (Additive.ofMul x)) •
          Additive.ofMul (cleanupLocalUniformizer K) by rfl]
  rw [map_add, map_zsmul, cleanup_uniformizer_order]
  simp

/-- Projection to the local-unit factor in the splitting
`Kˣ = local units × uniformizer powers`. -/
noncomputable def localUnitPart
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))] :
    Kˣ →* localUnitSubgroup K where
  toFun x := ⟨localPartValue K x, local_part_value K x⟩
  map_one' := by
    apply Subtype.ext
    simp [localPartValue]
  map_mul' x y := by
    apply Subtype.ext
    change x * y * cleanupLocalUniformizer K ^
        (-localUnitOrder K (Additive.ofMul (x * y))) =
      (x * cleanupLocalUniformizer K ^
        (-localUnitOrder K (Additive.ofMul x))) *
      (y * cleanupLocalUniformizer K ^
        (-localUnitOrder K (Additive.ofMul y)))
    have hord := map_add (localUnitOrder K)
      (Additive.ofMul x) (Additive.ofMul y)
    change localUnitOrder K (Additive.ofMul (x * y)) =
      localUnitOrder K (Additive.ofMul x) +
        localUnitOrder K (Additive.ofMul y) at hord
    rw [hord, neg_add_rev, zpow_add]
    ac_rfl

/-- Extend a character of the local-unit subgroup to all of `Kˣ`, choosing
the normalized uniformizer to have value one. -/
noncomputable def extendUnitCharacter
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {A : Type*} [Group A]
    (psi : localUnitSubgroup K →* A) : Kˣ →* A :=
  psi.comp (localUnitPart K)

@[simp]
theorem extend_unit_character
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {A : Type*} [Group A]
    (psi : localUnitSubgroup K →* A)
    (u : localUnitSubgroup K) :
    extendUnitCharacter K psi (u : Kˣ) = psi u := by
  change psi (localUnitPart K (u : Kˣ)) = psi u
  apply congrArg psi
  apply Subtype.ext
  change (u : Kˣ) * cleanupLocalUniformizer K ^
      (-localUnitOrder K (Additive.ofMul (u : Kˣ))) = (u : Kˣ)
  rw [(local_order_zero
    K (u : Kˣ)).1 u.property]
  simp

@[simp]
theorem extend_character_uniformizer
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {A : Type*} [Group A]
    (psi : localUnitSubgroup K →* A) :
    extendUnitCharacter K psi (cleanupLocalUniformizer K) = 1 := by
  change psi (localUnitPart K (cleanupLocalUniformizer K)) = 1
  rw [show localUnitPart K (cleanupLocalUniformizer K) = 1 by
    apply Subtype.ext
    change cleanupLocalUniformizer K * cleanupLocalUniformizer K ^
      (-localUnitOrder K
        (Additive.ofMul (cleanupLocalUniformizer K))) = 1
    rw [cleanup_uniformizer_order]
    simp]
  exact map_one psi

/-- The standard faithful cubic character from multiplicative `ZMod 3` to
the complex unit circle. -/
noncomputable def zmodCircleHom :
    Multiplicative (ZMod 3) →* Circle where
  toFun x := ZMod.toCircle x.toAdd
  map_one' := ZMod.toCircle.map_zero_eq_one
  map_mul' x y := ZMod.toCircle.map_add_eq_mul x.toAdd y.toAdd

theorem zmod_circle_injective :
    Function.Injective zmodCircleHom :=
  ZMod.injective_toCircle.comp Multiplicative.toAdd.injective

/-- A nontrivial cubic local-unit character remains of exact order three
after extension to `Kˣ` and the faithful embedding into `Circle`. -/
theorem zmod_circle_extend
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (psi : localUnitSubgroup K →* Multiplicative (ZMod 3))
    (hpsi : psi ≠ 1) :
    orderOf
      (zmodCircleHom.comp (extendUnitCharacter K psi)) = 3 := by
  let chi : Kˣ →* Circle :=
    zmodCircleHom.comp (extendUnitCharacter K psi)
  have hcube : chi ^ 3 = 1 := by
    apply MonoidHom.ext
    intro x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    change zmodCircleHom (extendUnitCharacter K psi x) ^ 3 = 1
    rw [← map_pow]
    have hp : extendUnitCharacter K psi x ^ 3 = 1 := by
      simpa using
        (pow_card_eq_one'
          (G := Multiplicative (ZMod 3))
          (x := extendUnitCharacter K psi x))
    rw [hp, map_one]
  have hchi_ne : chi ≠ 1 := by
    have hexists : ∃ u : localUnitSubgroup K, psi u ≠ 1 := by
      by_contra h
      push Not at h
      apply hpsi
      ext u
      simpa using h u
    obtain ⟨u, hu⟩ := hexists
    intro hchi
    have hv := DFunLike.congr_fun hchi (u : Kˣ)
    change zmodCircleHom
        (extendUnitCharacter K psi (u : Kˣ)) = 1 at hv
    rw [extend_unit_character] at hv
    apply hu
    apply zmod_circle_injective
    simpa using hv
  have hdvd : orderOf chi ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with horder | horder
  · exact (hchi_ne (orderOf_eq_one_iff.mp horder)).elim
  · exact horder

/-- A group homomorphism into a discrete group is continuous when its kernel
is open. -/
theorem continuous_monoid_discrete
    {Γ : Type u} {Λ : Type v} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ]
    [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (phi : Γ →* Λ)
    (hker : IsOpen ((phi.ker : Subgroup Γ) : Set Γ)) :
    Continuous phi := by
  classical
  have hsingle : ∀ y : Λ,
      IsOpen ((fun x : Γ => phi x) ⁻¹' ({y} : Set Λ)) := by
    intro y
    by_cases hy : ∃ a : Γ, phi a = y
    · rcases hy with ⟨a, ha⟩
      have hfiber_eq :
          ((fun x : Γ => phi x) ⁻¹' ({y} : Set Λ)) =
            (fun x : Γ => a⁻¹ * x) ⁻¹' (phi.ker : Set Γ) := by
        ext x
        constructor
        · intro hx
          change phi x = y at hx
          change phi (a⁻¹ * x) = 1
          simp [ha, hx]
        · intro hx
          change phi (a⁻¹ * x) = 1 at hx
          have hmul : y⁻¹ * phi x = 1 := by
            calc
              y⁻¹ * phi x = (phi a)⁻¹ * phi x := by rw [ha]
              _ = phi (a⁻¹ * x) := by simp
              _ = 1 := hx
          exact (inv_mul_eq_one.mp hmul).symm
      have hshift : Continuous (fun x : Γ => a⁻¹ * x) := by
        fun_prop
      rw [hfiber_eq]
      exact hker.preimage hshift
    · have hfiber_empty :
          ((fun x : Γ => phi x) ⁻¹' ({y} : Set Λ)) = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hy ⟨x, by simpa using hx⟩).elim
        · intro hx
          exact hx.elim
      rw [hfiber_empty]
      exact isOpen_empty
  rw [continuous_def]
  intro U _
  have hpre_eq :
      ((fun x : Γ => phi x) ⁻¹' U) =
        ⋃ y : U, ((fun x : Γ => phi x) ⁻¹' ({(y : Λ)} : Set Λ)) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨⟨phi x, hx⟩, by simp⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
      have hxy : phi x = (y : Λ) := by simpa using hy
      change phi x ∈ U
      rw [hxy]
      exact y.property
  rw [hpre_eq]
  exact isOpen_iUnion (fun y : U => hsingle (y : Λ))

/-- The explicit extension is continuous whenever an open subgroup of
`Kˣ`, lying in the local units, is killed by the original unit character. -/
theorem extend_character_continuous
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (psi : localUnitSubgroup K →* A)
    (N : Subgroup Kˣ) (hNopen : IsOpen (N : Set Kˣ))
    (hNunit : N ≤ localUnitSubgroup K)
    (hNker : ∀ x : N, psi ⟨x.1, hNunit x.2⟩ = 1) :
    Continuous (extendUnitCharacter K psi) := by
  apply continuous_monoid_discrete
  apply Subgroup.isOpen_mono
      (H₁ := N) (H₂ := (extendUnitCharacter K psi).ker)
  · intro x hx
    rw [MonoidHom.mem_ker]
    let u : localUnitSubgroup K := ⟨x, hNunit hx⟩
    change extendUnitCharacter K psi (u : Kˣ) = 1
    rw [extend_unit_character]
    exact hNker ⟨x, hx⟩
  · exact hNopen

/-- Local existence supplies the open subgroup needed for continuity: take
the intersection of a norm group killed by `psi` with the local units. -/
theorem extend_continuous_existence
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (hI14 : LocalExistenceTheorem K)
    (psi : localUnitSubgroup K →* A)
    (N : Subgroup Kˣ) (hNnorm : LGroup K N)
    (hNker : ∀ x : ↥(N ⊓ (localUnitSubgroup K : Subgroup Kˣ)),
      psi ⟨x.1, x.2.2⟩ = 1) :
    Continuous (extendUnitCharacter K psi) := by
  have hNopen : IsOpen (N : Set Kˣ) := (hI14 N).1 hNnorm |>.1
  have hUopen : IsOpen (localUnitSubgroup K : Set Kˣ) :=
    local_unit_open K
  let NI : Subgroup Kˣ := N ⊓ (localUnitSubgroup K : Subgroup Kˣ)
  refine extend_character_continuous K psi NI ?_ ?_ ?_
  · change IsOpen ((N : Set Kˣ) ∩ (localUnitSubgroup K : Set Kˣ))
    exact hNopen.inter hUopen
  · exact inf_le_right
  · intro x
    simpa [NI] using hNker x

end ramificationCleanup

end TBluepr
end Submission
