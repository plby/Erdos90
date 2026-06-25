import Towers.FieldTheory.CyclotomicCleanupAssembly

/-!
# Final ramification-cleanup assembly

This file contains the field-independent bookkeeping used to combine the
cyclotomic corrections away from `3` with the conductor-nine correction at
`3`.  It deliberately does not import the Koch--Shafarevich Part 2 file.
-/

open scoped Pointwise Topology

noncomputable section

namespace Towers
namespace TBluepr

universe v

local instance finalCleanupFiniteDimensional
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ D := D.finiteDimensional

local instance finalCleanupIsGalois
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ D := D.isGalois

local instance finalCleanupNormal
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Normal ℚ D := D.isGalois.to_normal

local instance finalCleanupAlgebraicClosureAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isAlgebraic ℚ (AlgebraicClosure ℚ) inferInstance
    inferInstance inferInstance inferInstance
      (AlgebraicClosure.instIsAlgClosure ℚ)

local instance finalCleanupAlgebraicClosureNormal :
    Normal ℚ (AlgebraicClosure ℚ) := by
  rw [normal_iff]
  intro x
  exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

/-- Pointwise product of two characters with commutative codomain. -/
def binaryCharacterProduct
    {G A : Type*} [Group G] [CommGroup A]
    (f g : G →* A) : G →* A where
  toFun x := f x * g x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul]
    ac_rfl

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Finite tame corrections synthesize the entire cyclotomic compositum tower.
/-- The tame cyclotomic construction with its finite character retained.
The absolute character is explicitly its inflation from the canonical common
compositum. -/
theorem tame_injective_lift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    [TopologicalSpace E] [DiscreteTopology E] [IsTopologicalGroup E]
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hliftFinite : Function.Injective liftFinite)
    (hkernelCube : ∀ z : pi.ker, z ^ 3 = 1)
    (hbaseInertia : ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        pi (liftFinite
          (tameCyclotomicRestriction D0 hD0three S sigma.1)) = 1) :
    let D := tameCorrectionCompositum D0 hD0three S
    let P := tameCyclotomicAbove D0 hD0three S
    let liftI := tameLiftInertia
      D0 hD0three S pi liftFinite hbaseInertia
    ∃ chiFinite : Gal(D/ℚ) →* pi.ker,
      ∃ chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker,
        chiFinite.comp
            (AlgEquiv.restrictNormalHom D.toIntermediateField) = chiAbs ∧
          Continuous chiAbs ∧
          (∀ i (sigma : (P i).inertia Gal(D/ℚ)),
            chiFinite sigma.1 * liftI i sigma = 1) ∧
          ∀ (q : ℕ) (_hq : Nat.Prime q)
            (_hqAway : ∀ i : TRIndex D0 S, q ≠ i.prime)
            (Pq : Ideal (NumberField.RingOfIntegers D)),
            Pq.IsPrime → Pq.LiesOver (Ideal.rationalPrimeIdeal q) →
              ∀ sigma : Pq.inertia Gal(D/ℚ), chiFinite sigma.1 = 1 := by
  dsimp only
  letI : CommGroup pi.ker :=
    centralExtensionComm pi hcentral
  let D := tameCorrectionCompositum D0 hD0three S
  let C := cyclotomicCubicCompositum D0 hD0three S
  let P := tameCyclotomicAbove D0 hD0three S
  let liftI := tameLiftInertia
    D0 hD0three S pi liftFinite hbaseInertia
  let otherFinite := liftFinite.comp
    (tameCyclotomicRestriction D0 hD0three S)
  letI (i : TRIndex D0 S) : (P i).IsPrime :=
    tame_cyclotomic_above D0 hD0three S i
  letI (i : TRIndex D0 S) :
      (P i).LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
    tame_above_lies D0 hD0three S i
  have hother : ∀ i (sigma : (P i).inertia Gal(D/ℚ)),
      otherFinite sigma.1 ^ 3 = 1 := by
    intro i sigma
    have hcube := congrArg Subtype.val (hkernelCube (liftI i sigma))
    simpa [liftI, otherFinite, tameLiftInertia] using hcube
  have hpair : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      Function.Injective
        (((otherFinite.comp ((P i).inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction (C i)
            (tame_compositum_galois
              D0 hD0three S i).to_normal i.prime (P i)))) := by
    intro i sigma tau h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    apply tame_restriction_injective D0 hD0three S i
    apply Prod.ext
    · apply hliftFinite
      exact hfst
    · exact hsnd
  have hexists (i : TRIndex D0 S) :
      ∃ chiC : letI : Algebra ℚ (C i) := (C i).algebra';
          Gal(C i/ℚ) →* pi.ker,
        let chi := absoluteThroughIntermediate D (C i)
          (tame_compositum_galois
            D0 hD0three S i).to_normal chiC
        Continuous chi ∧
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma : AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
              (P i).inertia Gal(D/ℚ)),
            chi sigma * liftI i ⟨_, hsigma⟩ = 1 :=
    intermediate_cancels_pair
      D (C i)
      (tame_compositum_dimensional
        D0 hD0three S i)
      (tame_compositum_galois D0 hD0three S i)
      i.prime_isPrime i.prime_ne_three (P i)
      (tame_compositum_idx
        D0 hD0three S i)
      (tame_compositum_card D0 hD0three S i)
      (liftI i) otherFinite (hother i) (hpair i)
  choose chiC hchiContinuous hchiCancel using hexists
  let chiFamily : TRIndex D0 S → Gal(D/ℚ) →* pi.ker :=
    fun i => (chiC i).comp (finiteIntermediateRestriction D (C i)
      (tame_compositum_galois
        D0 hD0three S i).to_normal)
  let chiFinite : Gal(D/ℚ) →* pi.ker :=
    finiteCharacterProduct Finset.univ chiFamily
  let chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker := chiFinite.comp
    (AlgEquiv.restrictNormalHom D.toIntermediateField)
  refine ⟨chiFinite, chiAbs, rfl, ?_, ?_, ?_⟩
  · let chiAbsFamily : TRIndex D0 S →
        Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker := fun i =>
      absoluteThroughIntermediate D (C i)
        (tame_compositum_galois
          D0 hD0three S i).to_normal (chiC i)
    have heq : chiAbs = finiteCharacterProduct Finset.univ chiAbsFamily := by
      ext sigma
      simp [chiAbs, chiFinite, chiFamily, chiAbsFamily,
        finite_character_product,
        character_through_intermediate]
      rfl
    rw [heq]
    exact character_product_continuous Finset.univ chiAbsFamily
      (fun i _ => hchiContinuous i)
  · intro i sigma
    obtain ⟨tau, htau⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := D) (E := AlgebraicClosure ℚ) sigma.1
    let I : TRIndex D0 S →
        Subgroup Gal(AlgebraicClosure ℚ/ℚ) := fun j =>
      Subgroup.comap (AlgEquiv.restrictNormalHom D.toIntermediateField)
        ((P j).inertia Gal(D/ℚ))
    have htauI : tau ∈ I i := by simp [I, htau]
    have hcross : ∀ j k, j ≠ k →
        ∀ rho, rho ∈ I k →
          absoluteThroughIntermediate D (C j)
            (tame_compositum_galois
              D0 hD0three S j).to_normal (chiC j) rho = 1 := by
      intro j k hjk rho hrho
      have hprime : k.prime ≠ j.prime := by
        intro h
        exact hjk (TRIndex.prime_injective h).symm
      have hunramified := rational_unramified_alg
        (tameCubicCompositum D0 hD0three S j)
        (rational_unramified_away j.prime
          j.prime_isPrime (j.prime_mod_eqone hD0three)
          k.prime_isPrime hprime)
      exact absolute_through_intermediate
        D (C j)
        (tame_compositum_dimensional
          D0 hD0three S j)
        (tame_compositum_galois D0 hD0three S j)
        (chiC j) k.prime_isPrime hunramified (P k) rho hrho
    have hcancelAbs := character_inertia_family
      I
      (fun j => absoluteThroughIntermediate D (C j)
        (tame_compositum_galois
          D0 hD0three S j).to_normal (chiC j))
      (fun j => (liftI j).comp
        { toFun := fun rho => ⟨AlgEquiv.restrictNormalHom
              D.toIntermediateField rho.1, rho.2⟩
          map_one' := by ext; simp
          map_mul' := by intro x y; ext; simp })
      (fun j rho hrho => hchiCancel j rho hrho)
      hcross i tau htauI
    simpa [chiFinite, chiFamily, finite_character_product, htau] using
      hcancelAbs
  · intro q hq hqAway Pq hPqprime hPqlies sigma
    letI : Pq.IsPrime := hPqprime
    letI : Pq.LiesOver (Ideal.rationalPrimeIdeal q) := hPqlies
    rw [finite_character_product]
    apply Finset.prod_eq_one
    intro i hi
    have hunramified := rational_unramified_alg
      (tameCubicCompositum D0 hD0three S i)
      (rational_unramified_away i.prime
        i.prime_isPrime (i.prime_mod_eqone hD0three)
        hq (hqAway i))
    exact character_restriction_unramified
      (C i)
      (tame_compositum_dimensional
        D0 hD0three S i)
      (tame_compositum_galois D0 hD0three S i)
      (chiC i) hq hunramified Pq sigma

/-- The common finite field containing the tame correction compositum and
the conductor-nine correction compositum. -/
noncomputable def rationalFullCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  tameCorrectionCompositum D0 hD0three S ⊔
    Dthree

/-- Restriction from a larger bundled finite Galois field to a contained
bundled finite Galois field. -/
noncomputable def finiteGaloisRestriction
    (K L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hKL : K.toIntermediateField ≤ L.toIntermediateField) :
    Gal(L/ℚ) →* Gal(K/ℚ) := by
  let K' : IntermediateField ℚ L := K.toIntermediateField.restrict hKL
  let eK : K ≃ₐ[ℚ] K' := IntermediateField.restrict_algEquiv hKL
  letI : IsGalois ℚ K' := IsGalois.of_algEquiv eK
  exact (AlgEquiv.autCongr eK).symm.toMonoidHom.comp
    (finiteIntermediateRestriction L K' (inferInstance : Normal ℚ K'))

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Restriction along bundled finite Galois fields has a large instance tower.
/-- Restriction along an inclusion of bundled finite Galois fields agrees
with direct restriction of an absolute automorphism. -/
theorem restriction_restrict_hom
    (K L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hKL : K.toIntermediateField ≤ L.toIntermediateField)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    finiteGaloisRestriction K L hKL
        (AlgEquiv.restrictNormalHom L.toIntermediateField sigma) =
      AlgEquiv.restrictNormalHom K.toIntermediateField sigma := by
  let K' : IntermediateField ℚ L := K.toIntermediateField.restrict hKL
  let eK : K ≃ₐ[ℚ] K' := IntermediateField.restrict_algEquiv hKL
  letI : IsGalois ℚ K' := IsGalois.of_algEquiv eK
  change (AlgEquiv.autCongr eK).symm
      (AlgEquiv.restrictNormalHom K'
        (AlgEquiv.restrictNormalHom L.toIntermediateField sigma)) =
    AlgEquiv.restrictNormalHom K.toIntermediateField sigma
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let rhoL := AlgEquiv.restrictNormalHom L.toIntermediateField sigma
  let rhoK := AlgEquiv.restrictNormalHom K' rhoL
  have he (y : K') :
      ((eK.symm y : K) : AlgebraicClosure ℚ) =
        (((y : K') : L) : AlgebraicClosure ℚ) := by
    have h := eK.apply_symm_apply y
    exact congrArg
      (fun z : K' => (((z : K') : L) : AlgebraicClosure ℚ)) h
  calc
    (((AlgEquiv.autCongr eK).symm rhoK x : K) : AlgebraicClosure ℚ) =
        ((eK.symm (rhoK (eK x)) : K) : AlgebraicClosure ℚ) := rfl
    _ = (((rhoK (eK x) : K') : L) : AlgebraicClosure ℚ) :=
      he (rhoK (eK x))
    _ = ((rhoL ((eK x : K') : L) : L) : AlgebraicClosure ℚ) := by
      exact congrArg (fun z : L => (z : AlgebraicClosure ℚ))
        (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance L
          inferInstance inferInstance K' (inferInstance : Normal ℚ K')
            rhoL (eK x))
    _ = sigma ((((eK x : K') : L) : AlgebraicClosure ℚ)) := by
      exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance L
          L.isGalois.to_normal sigma ((eK x : K') : L)
    _ = sigma (x : AlgebraicClosure ℚ) := by rfl
    _ = ((AlgEquiv.restrictNormalHom K.toIntermediateField sigma x : K) :
          AlgebraicClosure ℚ) :=
      (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance K
          K.isGalois.to_normal sigma x).symm

/-- Canonical finite restriction is transitive. -/
theorem galois_restriction_trans
    (K L M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hKL : K.toIntermediateField ≤ L.toIntermediateField)
    (hLM : L.toIntermediateField ≤ M.toIntermediateField) :
    finiteGaloisRestriction K M (hKL.trans hLM) =
      (finiteGaloisRestriction K L hKL).comp
        (finiteGaloisRestriction L M hLM) := by
  ext rho
  obtain ⟨sigma, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := M) (E := AlgebraicClosure ℚ)
      rho
  rw [MonoidHom.comp_apply,
    restriction_restrict_hom,
    restriction_restrict_hom,
    restriction_restrict_hom]

/-- A nontrivial inertia element of the lift field at a rational prime
outside `S` and distinct from `3` determines one of the tame ramified-prime
indices. -/
theorem ramified_nontrivial_inertia
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (S : Finset ℕ) (q : ℕ) (hq : Nat.Prime q)
    (hqS : q ∉ S) (hq3 : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers D0))
    (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.rationalPrimeIdeal q))
    (sigma : P.inertia Gal(D0/ℚ)) (hsigma : sigma.1 ≠ 1) :
    ∃ i : TRIndex D0 S, q = i.prime := by
  let p0 := P.under (NumberField.RingOfIntegers ℚ)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPover
  have hPne : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) P
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
  have hp0ne : p0 ≠ ⊥ :=
    Ideal.under_ne_bot (NumberField.RingOfIntegers ℚ) hPne
  have hp0prime : p0.IsPrime := inferInstance
  letI : p0.IsPrime := hp0prime
  letI : p0.IsMaximal := Ideal.IsPrime.isMaximal hp0prime hp0ne
  letI : Field (NumberField.RingOfIntegers ℚ ⧸ p0) :=
    Ideal.Quotient.field p0
  letI : Field (NumberField.RingOfIntegers D0 ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (NumberField.RingOfIntegers ℚ ⧸ p0) := inferInstance
  letI : PerfectField (NumberField.RingOfIntegers ℚ ⧸ p0) :=
    PerfectField.ofFinite
  letI : Finite (NumberField.RingOfIntegers D0 ⧸ P) := inferInstance
  letI : Module.Finite (NumberField.RingOfIntegers ℚ ⧸ p0)
      (NumberField.RingOfIntegers D0 ⧸ P) := Module.Finite.of_finite
  letI : Algebra.IsSeparable (NumberField.RingOfIntegers ℚ ⧸ p0)
      (NumberField.RingOfIntegers D0 ⧸ P) := inferInstance
  letI : IsGaloisGroup Gal(D0/ℚ) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers D0) :=
    IsGaloisGroup.of_isFractionRing Gal(D0/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers D0) ℚ D0
  have hram : Ideal.ramificationIdx p0 P ≠ 1 := by
    intro hramOne
    have hcard : Nat.card (P.inertia Gal(D0/ℚ)) =
        Ideal.ramificationIdx p0 P := by
      calc
        _ = Ideal.ramificationIdxIn p0
            (NumberField.RingOfIntegers D0) :=
          Ideal.card_inertia_eq_ramificationIdxIn
            (G := Gal(D0/ℚ)) p0 hp0ne P
        _ = _ := Ideal.ramificationIdxIn_eq_ramificationIdx
          (G := Gal(D0/ℚ)) (p := p0) (P := P)
    have hsub : Subsingleton (P.inertia Gal(D0/ℚ)) :=
      (Nat.card_eq_one_iff_unique.mp (hcard.trans hramOne)).1
    apply hsigma
    exact congrArg Subtype.val (hsub.elim sigma 1)
  have hp0map : p0.map Rat.ringOfIntegersEquiv =
      Ideal.rationalPrimeIdeal q := by
    calc
      p0.map Rat.ringOfIntegersEquiv = P.under ℤ := by
        let e0 := Rat.ringOfIntegersEquiv
        have halg : (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) =
            e0.symm.toRingHom := Subsingleton.elim _ _
        rw [← Ideal.under_under
          (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
            (C := NumberField.RingOfIntegers D0)]
        change p0.map e0 = p0.comap
          (algebraMap ℤ (NumberField.RingOfIntegers ℚ))
        rw [halg]
        exact Ideal.map_comap_of_equiv (I := p0) e0
      _ = Ideal.rationalPrimeIdeal q := hPover.over.symm
  have hp0ram : p0 ∈ ramifiedBaseIdeals ℚ D0 :=
    ⟨P, hPprime, hPne, rfl, hram⟩
  have hp0mem : p0 ∈ ramifiedIdealsFinset D0 S := by
    rw [ramifiedIdealsFinset, Finset.mem_filter,
      ramified_ideals_finset]
    refine ⟨hp0ram, ?_, ?_⟩
    · simpa [hp0map, abs_rational_ideal] using hqS
    · simpa [hp0map, abs_rational_ideal] using hq3
  let i : TRIndex D0 S := ⟨p0, hp0mem⟩
  refine ⟨i, ?_⟩
  change q = Ideal.absNorm (p0.map Rat.ringOfIntegersEquiv)
  rw [hp0map, abs_rational_ideal]

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Transporting inertia through finite field inclusions unfolds integral closures.
/-- The canonical finite restriction sends inertia at an upper prime into
inertia at the transported prime below. -/
theorem restriction_maps_inertia
    (K L : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hKL : K.toIntermediateField ≤ L.toIntermediateField)
    (q : ℕ) (_hq : Nat.Prime q)
    (Q : Ideal (NumberField.RingOfIntegers L))
    (hQprime : Q.IsPrime)
    (hQover : Q.LiesOver (Ideal.rationalPrimeIdeal q)) :
    ∃ P : Ideal (NumberField.RingOfIntegers K),
      P.IsPrime ∧ P.LiesOver (Ideal.rationalPrimeIdeal q) ∧
        ∀ sigma : Q.inertia Gal(L/ℚ),
          finiteGaloisRestriction K L hKL sigma.1 ∈
            P.inertia Gal(K/ℚ) := by
  let K' : IntermediateField ℚ L := K.toIntermediateField.restrict hKL
  let eK : K ≃ₐ[ℚ] K' := IntermediateField.restrict_algEquiv hKL
  letI : IsGalois ℚ K' := IsGalois.of_algEquiv eK
  letI : FiniteDimensional ℚ K' := Module.Finite.equiv eK.toLinearEquiv
  letI : NumberField K' := NumberField.of_module_finite ℚ K'
  let eO : NumberField.RingOfIntegers K ≃ₐ[ℤ]
      NumberField.RingOfIntegers K' :=
    (eK.restrictScalars ℤ).mapIntegralClosure
  let P' := Q.under (NumberField.RingOfIntegers K')
  let P := P'.comap eO
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := hQover
  have hP'prime : P'.IsPrime := inferInstance
  have hP'over : P'.LiesOver (Ideal.rationalPrimeIdeal q) := inferInstance
  have hPprime : P.IsPrime := Ideal.comap_isPrime eO P'
  have hPover : P.LiesOver (Ideal.rationalPrimeIdeal q) := by
    rw [Ideal.liesOver_iff]
    symm
    change Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers K))
        (P'.comap eO) = Ideal.rationalPrimeIdeal q
    have halg : eO.toRingHom.comp
        (algebraMap ℤ (NumberField.RingOfIntegers K)) =
        algebraMap ℤ (NumberField.RingOfIntegers K') := by
      exact RingHom.ext_int _ _
    calc
      Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers K))
          (P'.comap eO) =
          P'.comap (eO.toRingHom.comp
            (algebraMap ℤ (NumberField.RingOfIntegers K))) :=
        Ideal.comap_comap _ _
      _ = P'.comap (algebraMap ℤ
          (NumberField.RingOfIntegers K')) := by rw [halg]
      _ = Ideal.rationalPrimeIdeal q := hP'over.over.symm
  refine ⟨P, hPprime, hPover, ?_⟩
  intro sigma
  let res' := numberInertiaRestriction K'
    (inferInstance : Normal ℚ K') q Q sigma
  change (AlgEquiv.autCongr eK).symm res'.1 ∈ P.inertia Gal(K/ℚ)
  intro x
  change MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K)
      ((AlgEquiv.autCongr eK).symm res'.1) x - x ∈ P
  change eO (MulSemiringAction.toAlgHom ℤ
      (NumberField.RingOfIntegers K)
      ((AlgEquiv.autCongr eK).symm res'.1) x - x) ∈ P'
  rw [map_sub]
  have hequiv : eO (MulSemiringAction.toAlgHom ℤ
      (NumberField.RingOfIntegers K)
      ((AlgEquiv.autCongr eK).symm res'.1) x) =
      MulSemiringAction.toAlgHom ℤ (NumberField.RingOfIntegers K')
        res'.1 (eO x) := by
    apply Subtype.ext
    change eK ((AlgEquiv.autCongr eK).symm res'.1 x) = res'.1 (eK x)
    have heq := (AlgEquiv.autCongr eK).apply_symm_apply res'.1
    have hx := DFunLike.congr_fun heq (eK x)
    rw [AlgEquiv.autCongr_apply] at hx
    simpa only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using hx
  rw [hequiv]
  exact res'.2 (eO x)

noncomputable def fullRestrictionTame
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(rationalFullCompositum
      D0 hD0three S Dthree/ℚ) →*
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) :=
  finiteGaloisRestriction _ _ le_sup_left

noncomputable def fullRestrictionNine
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(rationalFullCompositum
      D0 hD0three S Dthree/ℚ) →* Gal(Dthree/ℚ) :=
  finiteGaloisRestriction _ _ le_sup_right

noncomputable def fullRestrictionLift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    Gal(rationalFullCompositum
      D0 hD0three S Dthree/ℚ) →*
      Gal(D0/ℚ) :=
  finiteGaloisRestriction D0
    (rationalFullCompositum D0 hD0three S Dthree)
    (le_trans (show D0.toIntermediateField ≤
      (tameCorrectionCompositum D0 hD0three S).toIntermediateField
        from tame_cyclotomic_compositum
          D0 hD0three S none) le_sup_left)

/-- The canonical restriction used by the tame construction is the generic
restriction attached to the inclusion of the lift field. -/
theorem tame_restriction_galois
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ) :
    tameCyclotomicRestriction D0 hD0three S =
      finiteGaloisRestriction D0
        (tameCorrectionCompositum D0 hD0three S)
        (tame_cyclotomic_compositum
          D0 hD0three S none) := by
  let Dtame := tameCorrectionCompositum D0 hD0three S
  apply MonoidHom.ext
  intro rho
  obtain ⟨sigma, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := Dtame) (E := AlgebraicClosure ℚ) rho
  rw [tame_restriction_restrict,
    restriction_restrict_hom]

/-- If the second correction field also contains the lift field, restriction
from the full compositum to the lift field may be computed through it. -/
theorem full_restriction_lift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0le : D0.toIntermediateField ≤ Dthree.toIntermediateField) :
    fullRestrictionLift D0 hD0three S Dthree =
      (finiteGaloisRestriction D0 Dthree hD0le).comp
        (fullRestrictionNine D0 hD0three S Dthree) := by
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  apply MonoidHom.ext
  intro rho
  obtain ⟨sigma, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := Dfull) (E := AlgebraicClosure ℚ)
      rho
  rw [MonoidHom.comp_apply]
  change finiteGaloisRestriction D0 Dfull _
      (AlgEquiv.restrictNormalHom Dfull.toIntermediateField sigma) =
    finiteGaloisRestriction D0 Dthree hD0le
      (finiteGaloisRestriction Dthree Dfull le_sup_right
        (AlgEquiv.restrictNormalHom Dfull.toIntermediateField sigma))
  rw [restriction_restrict_hom,
    restriction_restrict_hom,
    restriction_restrict_hom]

/-- Restriction from the full compositum to the lift field may equivalently
be computed through the canonical tame correction compositum. -/
theorem full_restriction_tame
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    fullRestrictionLift D0 hD0three S Dthree =
      (tameCyclotomicRestriction D0 hD0three S).comp
        (fullRestrictionTame D0 hD0three S Dthree) := by
  let Dtame := tameCorrectionCompositum D0 hD0three S
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  apply MonoidHom.ext
  intro rho
  obtain ⟨sigma, rfl⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := Dfull) (E := AlgebraicClosure ℚ) rho
  rw [MonoidHom.comp_apply]
  change finiteGaloisRestriction D0 Dfull _
      (AlgEquiv.restrictNormalHom Dfull.toIntermediateField sigma) =
    tameCyclotomicRestriction D0 hD0three S
      (finiteGaloisRestriction Dtame Dfull le_sup_left
        (AlgEquiv.restrictNormalHom Dfull.toIntermediateField sigma))
  rw [restriction_restrict_hom,
    restriction_restrict_hom,
    tame_restriction_restrict]

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Going-up and restriction compatibility require both correction field towers.
/-- Source-field inertia identities pull back to the full correction
compositum.  This is the going-up/restriction compatibility needed by the
final two-correction assembly. -/
theorem full_compositum_conditions
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A)
    (liftFinite : Gal(D0/ℚ) →* E)
    (chiTame :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0le : D0.toIntermediateField ≤ Dthree.toIntermediateField)
    (chiThree : Gal(Dthree/ℚ) →* pi.ker)
    (q : ℕ) (hq : Nat.Prime q)
    (htame : ∀ (P : Ideal (NumberField.RingOfIntegers
        (tameCorrectionCompositum D0 hD0three S))),
      P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
        ∀ sigma : P.inertia
          Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
            chiTame sigma.1 = 1)
    (hthree : ∀ (P : Ideal (NumberField.RingOfIntegers Dthree)),
      P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
        ∀ sigma : P.inertia Gal(Dthree/ℚ),
          (chiThree sigma.1 : E) *
            liftFinite (finiteGaloisRestriction D0 Dthree hD0le sigma.1) = 1) :
    let Dfull := rationalFullCompositum
      D0 hD0three S Dthree
    let liftFull := liftFinite.comp
      (fullRestrictionLift D0 hD0three S Dthree)
    let chiTameFull := chiTame.comp
      (fullRestrictionTame D0 hD0three S Dthree)
    let chiThreeFull := chiThree.comp
      (fullRestrictionNine D0 hD0three S Dthree)
    ∃ Q : Ideal (NumberField.RingOfIntegers Dfull),
      Q.IsPrime ∧ Q.LiesOver (Ideal.rationalPrimeIdeal q) ∧
        ∀ sigma : Q.inertia Gal(Dfull/ℚ),
          chiTameFull sigma.1 = 1 ∧
            (chiThreeFull sigma.1 : E) * liftFull sigma.1 = 1 := by
  dsimp only
  let Dtame := tameCorrectionCompositum D0 hD0three S
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsMaximal := rational_ideal_maximal hq
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral p
      (S := NumberField.RingOfIntegers Dfull)
  have hQprime : Q.IsPrime := hQmax.isPrime
  have hQover' : Q.LiesOver (Ideal.rationalPrimeIdeal q) := by
    simpa [p] using hQover
  obtain ⟨Ptame, hPtamePrime, hPtameOver, hPtameMap⟩ :=
    restriction_maps_inertia Dtame Dfull le_sup_left
      q hq Q hQprime hQover'
  obtain ⟨Pthree, hPthreePrime, hPthreeOver, hPthreeMap⟩ :=
    restriction_maps_inertia Dthree Dfull le_sup_right
      q hq Q hQprime hQover'
  refine ⟨Q, hQprime, hQover', ?_⟩
  intro sigma
  let sigmaTame : Ptame.inertia Gal(Dtame/ℚ) :=
    ⟨fullRestrictionTame D0 hD0three S Dthree sigma.1,
      hPtameMap sigma⟩
  let sigmaThree : Pthree.inertia Gal(Dthree/ℚ) :=
    ⟨fullRestrictionNine D0 hD0three S Dthree sigma.1,
      hPthreeMap sigma⟩
  refine ⟨htame Ptame hPtamePrime hPtameOver sigmaTame, ?_⟩
  change (chiThree sigmaThree.1 : E) *
    liftFinite
      (fullRestrictionLift D0 hD0three S Dthree sigma.1) = 1
  rw [DFunLike.congr_fun
    (full_restriction_lift
      D0 hD0three S Dthree hD0le) sigma.1]
  exact hthree Pthree hPthreePrime hPthreeOver sigmaThree

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The prime-over-three transport expands both correction composita.
/-- Build the prime-over-`3` hypothesis for the final assembly from the
support of the tame character and cancellation at one prime in the
conductor-nine source field. -/
theorem full_compositum_hkill
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (chiTame :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker)
    (htameSupportThree :
      ∀ (P : Ideal (NumberField.RingOfIntegers
          (tameCorrectionCompositum D0 hD0three S))),
        P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal 3) →
          ∀ sigma : P.inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
              chiTame sigma.1 = 1)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0le : D0.toIntermediateField ≤ Dthree.toIntermediateField)
    (chiThree : Gal(Dthree/ℚ) →* pi.ker)
    (P3 : Ideal (NumberField.RingOfIntegers Dthree))
    (hP3prime : P3.IsPrime)
    (hP3over : P3.LiesOver (Ideal.rationalPrimeIdeal 3))
    (hthreeCancel : ∀ sigma : P3.inertia Gal(Dthree/ℚ),
      (chiThree sigma.1 : E) *
        liftFinite (finiteGaloisRestriction D0 Dthree hD0le sigma.1) = 1) :
    let Dfull := rationalFullCompositum
      D0 hD0three S Dthree
    let liftFull := liftFinite.comp
      (fullRestrictionLift D0 hD0three S Dthree)
    let chiTameFull := chiTame.comp
      (fullRestrictionTame D0 hD0three S Dthree)
    let chiThreeFull := chiThree.comp
      (fullRestrictionNine D0 hD0three S Dthree)
    ∃ Q : Ideal (NumberField.RingOfIntegers Dfull),
      Q.IsPrime ∧ Q.LiesOver (Ideal.rationalPrimeIdeal 3) ∧
        ∀ sigma : Q.inertia Gal(Dfull/ℚ),
          chiTameFull sigma.1 = 1 ∧
            (chiThreeFull sigma.1 : E) * liftFull sigma.1 = 1 := by
  let liftThree := liftFinite.comp
    (finiteGaloisRestriction D0 Dthree hD0le)
  let correctedThree :=
    centralKernelTwist pi liftThree chiThree hcentral
  letI : P3.IsPrime := hP3prime
  letI : P3.LiesOver (Ideal.rationalPrimeIdeal 3) := hP3over
  have hcorrectedP3 : ∀ sigma : P3.inertia Gal(Dthree/ℚ),
      correctedThree sigma.1 = 1 := by
    intro sigma
    exact hthreeCancel sigma
  apply full_compositum_conditions
    D0 hD0three S pi liftFinite chiTame Dthree hD0le chiThree
      3 Nat.prime_three htameSupportThree
  intro P hPprime hPover sigma
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (Ideal.rationalPrimeIdeal 3) := hPover
  have h := number_all_inertia
    Dthree correctedThree (q := 3) P3 hcorrectedP3 P sigma
  exact h

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Away-from-three transport expands both correction composita.
/-- Build the away-from-`3` inertia hypothesis in the full compositum from
the corrected tame identity and the support of the conductor-nine
character in their respective source fields. -/
theorem full_hkill_away
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (liftFinite : Gal(D0/ℚ) →* E)
    (chiTame :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (chiThree : Gal(Dthree/ℚ) →* pi.ker)
    (htame : ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S → q ≠ 3 →
      ∀ (P : Ideal (NumberField.RingOfIntegers
          (tameCorrectionCompositum D0 hD0three S))),
        P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
          ∀ sigma : P.inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
            (chiTame sigma.1 : E) *
              liftFinite (tameCyclotomicRestriction
                D0 hD0three S sigma.1) = 1)
    (hthree : ∀ (q : ℕ) (_hq : Nat.Prime q), q ≠ 3 →
      ∀ (P : Ideal (NumberField.RingOfIntegers Dthree)),
        P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
          ∀ sigma : P.inertia Gal(Dthree/ℚ), chiThree sigma.1 = 1) :
    let Dfull := rationalFullCompositum
      D0 hD0three S Dthree
    let liftFull := liftFinite.comp
      (fullRestrictionLift D0 hD0three S Dthree)
    let chiTameFull := chiTame.comp
      (fullRestrictionTame D0 hD0three S Dthree)
    let chiThreeFull := chiThree.comp
      (fullRestrictionNine D0 hD0three S Dthree)
    ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S → q ≠ 3 →
      ∃ Q : Ideal (NumberField.RingOfIntegers Dfull),
        Q.IsPrime ∧ Q.LiesOver (Ideal.rationalPrimeIdeal q) ∧
          ∀ sigma : Q.inertia Gal(Dfull/ℚ),
            chiThreeFull sigma.1 = 1 ∧
              (chiTameFull sigma.1 : E) * liftFull sigma.1 = 1 := by
  dsimp only
  intro q hq hqS hq3
  let Dtame := tameCorrectionCompositum D0 hD0three S
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsMaximal := rational_ideal_maximal hq
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral p
      (S := NumberField.RingOfIntegers Dfull)
  have hQprime : Q.IsPrime := hQmax.isPrime
  have hQover' : Q.LiesOver (Ideal.rationalPrimeIdeal q) := by
    simpa [p] using hQover
  obtain ⟨Ptame, hPtamePrime, hPtameOver, hPtameMap⟩ :=
    restriction_maps_inertia Dtame Dfull le_sup_left
      q hq Q hQprime hQover'
  obtain ⟨Pthree, hPthreePrime, hPthreeOver, hPthreeMap⟩ :=
    restriction_maps_inertia Dthree Dfull le_sup_right
      q hq Q hQprime hQover'
  refine ⟨Q, hQprime, hQover', ?_⟩
  intro sigma
  let sigmaTame : Ptame.inertia Gal(Dtame/ℚ) :=
    ⟨fullRestrictionTame D0 hD0three S Dthree sigma.1,
      hPtameMap sigma⟩
  let sigmaThree : Pthree.inertia Gal(Dthree/ℚ) :=
    ⟨fullRestrictionNine D0 hD0three S Dthree sigma.1,
      hPthreeMap sigma⟩
  refine ⟨hthree q hq hq3 Pthree hPthreePrime hPthreeOver sigmaThree, ?_⟩
  change (chiTame sigmaTame.1 : E) *
    liftFinite
      (fullRestrictionLift D0 hD0three S Dthree sigma.1) = 1
  rw [DFunLike.congr_fun
    (full_restriction_tame
      D0 hD0three S Dthree) sigma.1]
  exact htame q hq hqS hq3 Ptame hPtamePrime hPtameOver sigmaTame

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The tame support argument unfolds the canonical correction compositum.
/-- The cancellation and support clauses returned by the finite tame
construction imply that the tame-corrected lift kills inertia at every
rational prime outside `S` and distinct from `3`. -/
theorem kills_inertia_away
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ)) (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hbaseInertia : ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        pi (liftFinite
          (tameCyclotomicRestriction D0 hD0three S sigma.1)) = 1)
    (chiTame :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker)
    (hcancel : ∀ i (sigma :
        (tameCyclotomicAbove D0 hD0three S i).inertia
          Gal(tameCorrectionCompositum D0 hD0three S/ℚ)),
      chiTame sigma.1 *
        tameLiftInertia
          D0 hD0three S pi liftFinite hbaseInertia i sigma = 1)
    (hsupport : ∀ (q : ℕ) (_hq : Nat.Prime q)
        (_hqAway : ∀ i : TRIndex D0 S, q ≠ i.prime)
        (P : Ideal (NumberField.RingOfIntegers
          (tameCorrectionCompositum D0 hD0three S))),
      P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
        ∀ sigma : P.inertia
          Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
            chiTame sigma.1 = 1) :
    ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S → q ≠ 3 →
      ∀ (P : Ideal (NumberField.RingOfIntegers
          (tameCorrectionCompositum D0 hD0three S))),
        P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
          ∀ sigma : P.inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
            (chiTame sigma.1 : E) *
              liftFinite (tameCyclotomicRestriction
                D0 hD0three S sigma.1) = 1 := by
  let Dtame := tameCorrectionCompositum D0 hD0three S
  let liftTame := liftFinite.comp
    (tameCyclotomicRestriction D0 hD0three S)
  let correctedTame := centralKernelTwist
    pi liftTame chiTame hcentral
  intro q hq hqS hq3 P hPprime hPover sigma
  by_cases hindex : ∃ i : TRIndex D0 S, q = i.prime
  · obtain ⟨i, hi⟩ := hindex
    let Pi := tameCyclotomicAbove D0 hD0three S i
    letI : Pi.IsPrime :=
      tame_cyclotomic_above D0 hD0three S i
    letI : Pi.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
      tame_above_lies D0 hD0three S i
    have hcorrectedPi : ∀ tau : Pi.inertia Gal(Dtame/ℚ),
        correctedTame tau.1 = 1 := by
      intro tau
      have h := congrArg Subtype.val (hcancel i tau)
      exact h
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) := by
      simpa [← hi] using hPover
    have h := number_all_inertia
      Dtame correctedTame (q := i.prime) Pi hcorrectedPi P sigma
    exact h
  · have hqAway : ∀ i : TRIndex D0 S, q ≠ i.prime := by
      intro i hi
      exact hindex ⟨i, hi⟩
    have hchi := hsupport q hq hqAway P hPprime hPover sigma
    let hD0le := tame_cyclotomic_compositum
      D0 hD0three S none
    obtain ⟨P0, hP0prime, hP0over, hP0map⟩ :=
      restriction_maps_inertia D0 Dtame hD0le
        q hq P hPprime hPover
    let sigma0 : P0.inertia Gal(D0/ℚ) :=
      ⟨finiteGaloisRestriction D0 Dtame hD0le sigma.1,
        hP0map sigma⟩
    have hres : tameCyclotomicRestriction
        D0 hD0three S sigma.1 = 1 := by
      by_contra hne
      have hgenericNe : sigma0.1 ≠ 1 := by
        simpa [sigma0,
          tame_restriction_galois]
          using hne
      obtain ⟨i, hi⟩ :=
        ramified_nontrivial_inertia
          D0 S q hq hqS hq3 P0 hP0prime hP0over sigma0 hgenericNe
      exact hindex ⟨i, hi⟩
    rw [hchi, hres, map_one]
    simp

/-- For a finite Galois homomorphism it is enough to kill inertia at one
prime above each rational prime.  Galois conjugacy supplies every other
upper prime, after which the fixed field of the kernel is unramified. -/
theorem fixed_outside_killed
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset ℕ) {E : Type*} [Group E]
    (corrected : Gal(K/ℚ) →* E)
    (hone :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∃ P0 : Ideal (NumberField.RingOfIntegers K),
          P0.IsPrime ∧
            P0.LiesOver (Ideal.rationalPrimeIdeal q) ∧
              ∀ sigma : P0.inertia Gal(K/ℚ), corrected sigma.1 = 1) :
    let H := corrected.ker
    let F := IntermediateField.fixedField H
    letI : Algebra ℚ F := F.algebra'
    letI : FiniteDimensional ℚ F := inferInstance
    letI : NumberField F := NumberField.of_module_finite ℚ F
    UnramifiedOutside F S := by
  apply outside_inertia_killed K S corrected
  intro q hq hqS P hPprime hPlies sigma
  obtain ⟨P0, hP0prime, hP0lies, hP0kill⟩ := hone q hq hqS
  letI : P0.IsPrime := hP0prime
  letI : P0.LiesOver (Ideal.rationalPrimeIdeal q) := hP0lies
  letI : P.IsPrime := hPprime
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPlies
  exact number_all_inertia
    K corrected (q := q) P0 hP0kill P sigma

/-- Combine a correction supported away from `3` and a correction supported
at `3`.  The hypotheses are stated at one selected upper prime over each
rational prime; the preceding theorem performs all conjugate-prime
bookkeeping.

Both corrections remain finite characters on the common ambient field.
Their absolute inflation is recorded explicitly, which is the factorization
needed by the final Part 2 assembly. -/
theorem corrections_fixed_outside
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D/ℚ) →* E)
    (chiTameFinite chiThreeFinite : Gal(D/ℚ) →* pi.ker)
    (chiFinite : Gal(D/ℚ) →* pi.ker)
    (hchiFinite : ∀ sigma,
      chiFinite sigma = chiTameFinite sigma * chiThreeFinite sigma)
    (P3 : Ideal (NumberField.RingOfIntegers D))
    (hP3prime : P3.IsPrime)
    (hP3lies : P3.LiesOver (Ideal.rationalPrimeIdeal 3))
    (hkill3 : ∀ sigma : P3.inertia Gal(D/ℚ),
      chiTameFinite sigma.1 = 1 ∧
        (chiThreeFinite sigma.1 : E) * liftFinite sigma.1 = 1)
    (hkillAway :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S → q ≠ 3 →
        ∃ Pq : Ideal (NumberField.RingOfIntegers D),
          Pq.IsPrime ∧
            Pq.LiesOver (Ideal.rationalPrimeIdeal q) ∧
              ∀ sigma : Pq.inertia Gal(D/ℚ),
                chiThreeFinite sigma.1 = 1 ∧
                  (chiTameFinite sigma.1 : E) * liftFinite sigma.1 = 1) :
    let chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker :=
      chiFinite.comp
        (AlgEquiv.restrictNormalHom D.toIntermediateField)
    let corrected : Gal(D/ℚ) →* E :=
      centralKernelTwist pi liftFinite chiFinite hcentral
    chiFinite.comp
        (AlgEquiv.restrictNormalHom D.toIntermediateField) = chiAbs ∧
      (let H := corrected.ker
       let F := IntermediateField.fixedField H
       letI : Algebra ℚ F := F.algebra'
       letI : FiniteDimensional ℚ F := inferInstance
       letI : NumberField F := NumberField.of_module_finite ℚ F
       UnramifiedOutside F S) := by
  dsimp only
  let corrected : Gal(D/ℚ) →* E :=
    centralKernelTwist pi liftFinite chiFinite hcentral
  refine ⟨rfl, ?_⟩
  apply fixed_outside_killed
    D S corrected
  intro q hq hqS
  by_cases hq3 : q = 3
  · subst q
    refine ⟨P3, hP3prime, hP3lies, ?_⟩
    intro sigma
    obtain ⟨htame, hthree⟩ := hkill3 sigma
    dsimp only [corrected, centralKernelTwist]
    change (chiFinite sigma.1 : E) * liftFinite sigma.1 = 1
    rw [hchiFinite sigma.1]
    simpa [htame] using hthree
  · obtain ⟨Pq, hPqprime, hPqlies, hkill⟩ :=
      hkillAway q hq hqS hq3
    refine ⟨Pq, hPqprime, hPqlies, ?_⟩
    intro sigma
    obtain ⟨hthree, htame⟩ := hkill sigma
    dsimp only [corrected, centralKernelTwist]
    change (chiFinite sigma.1 : E) * liftFinite sigma.1 = 1
    rw [hchiFinite sigma.1]
    simpa [hthree] using htame

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Final inflation and twisting synthesize all three finite field towers.
/-- Inflate finite tame and conductor-nine corrections to their canonical
common compositum and perform the final central twist.

The two inertia hypotheses are precisely the remaining compatibility
bookkeeping for primes chosen in the full compositum.  They can be discharged
from the cancellation and support clauses returned by
`tame_injective_lift` and
`canonical_nine_artin` once the
chosen upper primes are related by going-up. -/
theorem full_inflated_corrections
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (chiTame :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker)
    (Dthree : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (chiThree : Gal(Dthree/ℚ) →* pi.ker)
    (hkill3 :
      let Dfull := rationalFullCompositum
        D0 hD0three S Dthree
      let liftFull := liftFinite.comp
        (fullRestrictionLift D0 hD0three S Dthree)
      let chiTameFull := chiTame.comp
        (fullRestrictionTame D0 hD0three S Dthree)
      let chiThreeFull := chiThree.comp
        (fullRestrictionNine D0 hD0three S Dthree)
      ∃ P3 : Ideal (NumberField.RingOfIntegers Dfull),
        P3.IsPrime ∧ P3.LiesOver (Ideal.rationalPrimeIdeal 3) ∧
          ∀ sigma : P3.inertia Gal(Dfull/ℚ),
            chiTameFull sigma.1 = 1 ∧
              (chiThreeFull sigma.1 : E) * liftFull sigma.1 = 1)
    (hkillAway :
      let Dfull := rationalFullCompositum
        D0 hD0three S Dthree
      let liftFull := liftFinite.comp
        (fullRestrictionLift D0 hD0three S Dthree)
      let chiTameFull := chiTame.comp
        (fullRestrictionTame D0 hD0three S Dthree)
      let chiThreeFull := chiThree.comp
        (fullRestrictionNine D0 hD0three S Dthree)
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S → q ≠ 3 →
        ∃ Pq : Ideal (NumberField.RingOfIntegers Dfull),
          Pq.IsPrime ∧ Pq.LiesOver (Ideal.rationalPrimeIdeal q) ∧
            ∀ sigma : Pq.inertia Gal(Dfull/ℚ),
              chiThreeFull sigma.1 = 1 ∧
                (chiTameFull sigma.1 : E) * liftFull sigma.1 = 1) :
    let Dfull := rationalFullCompositum
      D0 hD0three S Dthree
    let liftFull := liftFinite.comp
      (fullRestrictionLift D0 hD0three S Dthree)
    let chiTameFull := chiTame.comp
      (fullRestrictionTame D0 hD0three S Dthree)
    let chiThreeFull := chiThree.comp
      (fullRestrictionNine D0 hD0three S Dthree)
    ∃ chiFinite : Gal(Dfull/ℚ) →* pi.ker,
      ∃ corrected : Gal(Dfull/ℚ) →* E,
        (∀ sigma,
          chiFinite sigma = chiTameFull sigma * chiThreeFull sigma) ∧
        let chiAbs : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker := chiFinite.comp
          (AlgEquiv.restrictNormalHom Dfull.toIntermediateField)
        chiFinite.comp
            (AlgEquiv.restrictNormalHom Dfull.toIntermediateField) = chiAbs ∧
          corrected = centralKernelTwist
            pi liftFull chiFinite hcentral ∧
          (∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
            ∀ (P : Ideal (NumberField.RingOfIntegers Dfull)),
              P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
                ∀ sigma : P.inertia Gal(Dfull/ℚ),
                  corrected sigma.1 = 1) ∧
          (let H := corrected.ker
           let F := IntermediateField.fixedField H
           letI : Algebra ℚ F := F.algebra'
           letI : FiniteDimensional ℚ F := inferInstance
           letI : NumberField F := NumberField.of_module_finite ℚ F
           UnramifiedOutside F S) := by
  dsimp only at hkill3 hkillAway ⊢
  let Dfull := rationalFullCompositum
    D0 hD0three S Dthree
  let liftFull := liftFinite.comp
    (fullRestrictionLift D0 hD0three S Dthree)
  let chiTameFull := chiTame.comp
    (fullRestrictionTame D0 hD0three S Dthree)
  let chiThreeFull := chiThree.comp
    (fullRestrictionNine D0 hD0three S Dthree)
  letI : CommGroup pi.ker :=
    centralExtensionComm pi hcentral
  let chiFinite : Gal(Dfull/ℚ) →* pi.ker :=
    binaryCharacterProduct chiTameFull chiThreeFull
  let corrected : Gal(Dfull/ℚ) →* E :=
    centralKernelTwist pi liftFull chiFinite hcentral
  obtain ⟨P3, hP3prime, hP3lies, hkill3⟩ := hkill3
  have hvalues : ∀ sigma,
      chiFinite sigma = chiTameFull sigma * chiThreeFull sigma := by
    intro sigma
    rfl
  have hone : ∀ (q : ℕ) (hq : Nat.Prime q), q ∉ S →
      ∃ P : Ideal (NumberField.RingOfIntegers Dfull),
        P.IsPrime ∧ P.LiesOver (Ideal.rationalPrimeIdeal q) ∧
          ∀ sigma : P.inertia Gal(Dfull/ℚ), corrected sigma.1 = 1 := by
    intro q hq hqS
    by_cases hq3 : q = 3
    · subst q
      refine ⟨P3, hP3prime, hP3lies, ?_⟩
      intro sigma
      obtain ⟨htame, hthree⟩ := hkill3 sigma
      have htameE : (chiTameFull sigma.1 : E) = 1 := by
        exact congrArg Subtype.val htame
      change (chiFinite sigma.1 : E) * liftFull sigma.1 = 1
      rw [hvalues sigma.1]
      simpa [htameE] using hthree
    · obtain ⟨Pq, hPqprime, hPqover, hkill⟩ :=
        hkillAway q hq hqS hq3
      refine ⟨Pq, hPqprime, hPqover, ?_⟩
      intro sigma
      obtain ⟨hthree, htame⟩ := hkill sigma
      have hthreeE : (chiThreeFull sigma.1 : E) = 1 := by
        exact congrArg Subtype.val hthree
      change (chiFinite sigma.1 : E) * liftFull sigma.1 = 1
      rw [hvalues sigma.1]
      simpa [hthreeE] using htame
  have hall : ∀ (q : ℕ) (hq : Nat.Prime q), q ∉ S →
      ∀ (P : Ideal (NumberField.RingOfIntegers Dfull)),
        P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
          ∀ sigma : P.inertia Gal(Dfull/ℚ), corrected sigma.1 = 1 := by
    intro q hq hqS P hPprime hPover sigma
    obtain ⟨P0, hP0prime, hP0over, hP0kill⟩ := hone q hq hqS
    letI : P0.IsPrime := hP0prime
    letI : P0.LiesOver (Ideal.rationalPrimeIdeal q) := hP0over
    letI : P.IsPrime := hPprime
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPover
    exact number_all_inertia
      Dfull corrected (q := q) P0 hP0kill P sigma
  refine ⟨chiFinite, corrected, hvalues, rfl, rfl, hall, ?_⟩
  exact fixed_outside_killed
    Dfull S corrected hone

end TBluepr
end Towers
