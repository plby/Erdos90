import Submission.FieldTheory.TameThreeKoch.CentralCubicSolvability

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v

open NumberField
open Submission.CField.Ideles


/--
Central cubic Shafarevich-Koch embedding-problem solvability, in the form
needed for an induction on finite `3`-group quotients.

Here `π : E →* A` is a finite central extension whose kernel has order `3`.
The map `βA` is an already-solved finite quotient of `G_S(ℚ)(3)`, while
`αE` is the prescribed lift on the free source.  The compatibility condition
says that projecting `αE` to `A` gives the known solution, and the tame
relation hypothesis says that the prescribed inertia/Frobenius images define
locally solvable tame cubic data.

The conclusion is a global lift `βE` of `βA` to `E` that realizes exactly the
prescribed free-source lift `αE`.
-/
theorem shafarevich_problem_solvable
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (π : E →* A)
    (hπ : Function.Surjective π)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card π.ker = 3)
    (αE : free.Carrier →* E)
    (hαE : Continuous αE)
    (hkill :
      ∀ i : Fin d,
        αE
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1)
    (βA : rationalTameGalois S →* A)
    (hcompat : βA.comp quotientMap = π.comp αE) :
    ∃ βE : rationalTameGalois S →* E,
      π.comp βE = βA ∧
        βE.comp quotientMap = αE := by
  classical
  rcases
      rational_cft_solvable
        (hsetup := hsetup)
        (pi := π)
        hπ
        hE
        hA
        hkernel_central
        hkernel_card
        αE
        hαE
        hkill
        βA
        hcompat with
    ⟨βE, hβE_continuous, hπβE, hβE_generators⟩
  refine ⟨βE, hπβE, ?_⟩
  letI : IsTopologicalGroup E := inferInstance
  letI : T2Space E := inferInstance
  let left : ProP.ContinuousHom free.Carrier E :=
    { toMonoidHom := βE.comp quotientMap
      continuous_toFun :=
        hβE_continuous.comp hsetup.quotientMap_continuous }
  let right : ProP.ContinuousHom free.Carrier E :=
    { toMonoidHom := αE
      continuous_toFun := hαE }
  have hleft_right : left = right := by
    apply ext_topologically_generates
      free.dense_generator
    intro i
    simpa [left, right] using hβE_generators i
  apply MonoidHom.ext
  intro x
  have hx :=
    congrArg (fun φ : ProP.ContinuousHom free.Carrier E => φ x) hleft_right
  simpa [left, right] using hx

/--
Finite Shafarevich-Koch embedding-problem solvability, in the quotient form
attached to one finite `3`-group shadow of the free source.

Given a finite discrete `3`-group quotient `α` of the free source that kills
the chosen tame Koch relators, the corresponding finite embedding problem over
`G_S(ℚ)(3)` has a global solution.  The returned homomorphism is that global
solution, expressed as an exact factorization of `α` through the arithmetic
quotient map.
-/
theorem embedding_problem_solvable
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {P : Type v}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : free.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill :
      ∀ i : Fin d,
        α
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1) :
    ∃ β : rationalTameGalois S →* P,
      β.comp quotientMap = α := by
  classical
  let relator : Fin d → free.Carrier :=
    fun i =>
      rationalTameRelator
        free
        prime
        frobeniusLift
        i
  have hmain :
      ∀ n : ℕ,
        ∀ {P : Type v}
          [Group P]
          [TopologicalSpace P]
          [DiscreteTopology P]
          [Finite P],
          Nat.card P = n →
          (α : free.Carrier →* P) →
          Continuous α →
          IsPGroup 3 P →
          (∀ i : Fin d, α (relator i) = 1) →
          ∃ β : rationalTameGalois S →* P,
            β.comp quotientMap = α := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro P _ _ _ _ hcard α hα hP hkill
        by_cases hcard_one : Nat.card P = 1
        · haveI : Subsingleton P :=
            (Nat.card_eq_one_iff_unique.mp hcard_one).1
          refine ⟨1, ?_⟩
          ext x
          exact Subsingleton.elim _ _
        · have hcard_gt_one : 1 < Nat.card P := by
            have hcard_pos : 0 < Nat.card P := Nat.card_pos
            omega
          haveI : Nontrivial P :=
            Finite.one_lt_card_iff_nontrivial.mp hcard_gt_one
          obtain ⟨C, hCcenter, hCcard⟩ :=
            central_order_subgroup (P := P) hP
          haveI : C.Normal := subgroup_normal_center C hCcenter
          let A := P ⧸ C
          letI : TopologicalSpace A := ⊥
          haveI : DiscreteTopology A := discreteTopology_bot A
          haveI : Finite A := inferInstance
          let π : P →* A := QuotientGroup.mk' C
          have hπ_surj : Function.Surjective π :=
            QuotientGroup.mk'_surjective C
          have hA : IsPGroup 3 A := by
            dsimp [A]
            exact hP.to_quotient C
          have hcardP :
              Nat.card P = Nat.card A * Nat.card C := by
            simpa [A] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup C)
          have hn : n = Nat.card A * 3 := by
            rw [← hcard, hcardP, hCcard]
          have hA_lt : Nat.card A < n := by
            rw [hn]
            exact lt_mul_of_one_lt_right
              (Nat.card_pos (α := A))
              (by norm_num : 1 < 3)
          let αA : free.Carrier →* A := π.comp α
          have hπ_cont : Continuous π :=
            continuous_of_discreteTopology
          have hαA : Continuous αA :=
            hπ_cont.comp hα
          have hkillA :
              ∀ i : Fin d, αA (relator i) = 1 := by
            intro i
            dsimp [αA, relator]
            rw [hkill i]
            simp
          obtain ⟨βA, hβA⟩ :=
            ih (Nat.card A) hA_lt
              (P := A) rfl αA hαA hA hkillA
          have hkernel_central : π.ker ≤ Subgroup.center P := by
            change (QuotientGroup.mk' C).ker ≤ Subgroup.center P
            rw [QuotientGroup.ker_mk']
            exact hCcenter
          have hkernel_card : Nat.card π.ker = 3 := by
            change Nat.card (QuotientGroup.mk' C).ker = 3
            rw [QuotientGroup.ker_mk']
            exact hCcard
          have hcompat : βA.comp quotientMap = π.comp α := by
            simpa [αA] using hβA
          obtain ⟨βE, _hπβE, hβE⟩ :=
            shafarevich_problem_solvable
              (hsetup := hsetup)
              (A := A)
              (E := P)
              (π := π)
              hπ_surj
              hP
              hA
              hkernel_central
              hkernel_card
              α
              hα
              hkill
              βA
              hcompat
          exact ⟨βE, hβE⟩
  exact hmain (Nat.card P) rfl α hα hP (by
    intro i
    exact hkill i)

/--
Weak pointwise finite Shafarevich-Koch embedding theorem, in exactly the form
needed for the rational tame pro-`3` presentation.

Once the tame inertia generators and Frobenius lifts have been chosen and the
local Koch relators vanish in `G_S(ℚ)(3)`, any single continuous finite
`3`-group quotient of the free source that kills those relators already
descends to the arithmetic quotient.  This deliberately avoids packaging the
result as an induced map `G_S(ℚ)(3) →* P`, and it does not assert the existence
of the Frobenius lifts; both are separate formal steps.
-/
theorem rational_shafarevich_embedding
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {P : Type v}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : free.Carrier →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill :
      ∀ i : Fin d,
        α
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1) :
    quotientMap.ker ≤ α.ker := by
  rcases
      embedding_problem_solvable
        hsetup
        α
        hα
        hP
        hkill with
    ⟨β, hβ⟩
  intro x hx
  change α x = 1
  change quotientMap x = 1 at hx
  calc
    α x = (β.comp quotientMap) x := by
      rw [hβ]
    _ = β (quotientMap x) := rfl
    _ = β 1 := by
      rw [hx]
    _ = 1 := by
      exact β.map_one

set_option maxHeartbeats 2000000 in
-- The compactness proof repeatedly unfolds fixed-field quotient equivalences
-- and finite-layer arithmetic Frobenius instances.
set_option synthInstance.maxHeartbeats 200000 in
/--
Arithmetic input one, in quotient-side form: choose Frobenius elements in
`G_S(ℚ)(3)` with the required finite-layer Frobenius provenance and tame local
relation.

This is weaker and cleaner than choosing free-source lifts directly.  The
next theorem performs that lift formally using surjectivity of `quotientMap`.
-/
theorem rational_shafarevich_data
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    (hsetup :
      RationalTameSetup
        S
        free
        quotientMap
        prime) :
    Nonempty
      (RationalTameData hsetup) := by
  classical
  let frobeniusSet :
      OpenNormalSubgroup (rationalTameGalois S) →
        Fin d → Set (rationalTameGalois S) :=
    fun N i =>
      {frobenius |
        IsArithFrobAt ℤ
          (rationalTameEquiv S N
            (rationalTameQuotient S N frobenius))
      ((hsetup.generators_tame_inertia i).primeAbove N)}
  have hfrobeniusSetClosed :
      ∀ (N : OpenNormalSubgroup (rationalTameGalois S)) (i : Fin d),
        IsClosed (frobeniusSet N i) := by
    intro N i
    letI : DiscreteTopology (rationalTameGalois S ⧸ N.toSubgroup) :=
      pro_discrete_topology N
    letI : Finite (rationalTameGalois S ⧸ N.toSubgroup) :=
      pro_p_open N
    change
      IsClosed
        ((rationalTameQuotient S N) ⁻¹'
          {x |
            IsArithFrobAt ℤ
              (rationalTameEquiv S N x)
              ((hsetup.generators_tame_inertia i).primeAbove N)})
    exact
      (Set.toFinite
        {x : rationalTameGalois S ⧸ N.toSubgroup |
          IsArithFrobAt ℤ
            (rationalTameEquiv S N x)
            ((hsetup.generators_tame_inertia i).primeAbove N)}).isClosed.preimage
        (pro_open_continuous N)
  have hfrobeniusSetFiniteIntersection :
      ∀ (i : Fin d)
        (s : Finset (OpenNormalSubgroup (rationalTameGalois S))),
        (⋂ N ∈ s, frobeniusSet N i).Nonempty := by
    intro i s
    let M : OpenNormalSubgroup (rationalTameGalois S) :=
      s.inf (fun N : OpenNormalSubgroup (rationalTameGalois S) => N)
    let PM :=
      (hsetup.generators_tame_inertia i).primeAbove M
    have hPMmem :=
      (hsetup.generators_tame_inertia i).primeAbove_mem M
    letI : PM.IsPrime :=
      hPMmem.1
    letI : PM.LiesOver (Ideal.rationalPrimeIdeal (prime i)) :=
      hPMmem.2
    have hPMne :
        PM ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot
        (rational_ne_bot (hsetup.prime_isPrime i))
        PM
    letI :
        Finite
          (NumberField.RingOfIntegers (rationalTameLayer S M) ⧸ PM) :=
      Ideal.finiteQuotientOfFreeOfNeBot
        PM
        hPMne
    let σM : Gal(rationalTameLayer S M / ℚ) :=
      arithFrobAt
        ℤ
        (Gal(rationalTameLayer S M / ℚ))
        PM
    have hσM :
        IsArithFrobAt ℤ σM PM := by
      simpa [σM] using
        (IsArithFrobAt.arithFrobAt
          (R := ℤ)
          (S := NumberField.RingOfIntegers (rationalTameLayer S M))
          (G := Gal(rationalTameLayer S M / ℚ))
          (Q := PM))
    obtain ⟨frobenius, hfrobenius⟩ :=
      (QuotientGroup.mk'_surjective M.toSubgroup)
        ((rationalTameEquiv S M).symm σM)
    refine
      ⟨frobenius, Set.mem_iInter₂.mpr ?_⟩
    intro N hN
    have hMN :
        M ≤ N := by
      dsimp [M]
      exact Finset.inf_le hN
    have hfieldMN :
        (IntermediateField.fixedField
            (rationalTameClosed S N).1) ≤
          IntermediateField.fixedField
            (rationalTameClosed S M).1 :=
      IntermediateField.fixedField_le hMN
    letI :
        Algebra (rationalTameLayer S N)
          (rationalTameLayer S M) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hfieldMN).toRingHom
    letI :
        Module (rationalTameLayer S N)
          (rationalTameLayer S M) :=
      Algebra.toModule
    letI :
        IsScalarTower ℚ
          (rationalTameLayer S N)
          (rationalTameLayer S M) :=
      IsScalarTower.of_algebraMap_eq
        (fun _ => rfl)
    letI :
        IsScalarTower
          (rationalTameLayer S N)
          (rationalTameLayer S M)
          (rationalTameExtension S) :=
      IsScalarTower.of_algebraMap_eq'
        rfl
    let PN :=
      (hsetup.generators_tame_inertia i).primeAbove N
    have hPNmem :=
      (hsetup.generators_tame_inertia i).primeAbove_mem N
    letI : PN.IsPrime :=
      hPNmem.1
    letI : PN.LiesOver (Ideal.rationalPrimeIdeal (prime i)) :=
      hPNmem.2
    have hPMunder :
        PM.under (NumberField.RingOfIntegers (rationalTameLayer S N)) =
          PN := by
      simpa [PM, PN, Ideal.under,
        rationalIntegersInclusion] using
        ((hsetup.generators_tame_inertia i).primeAbove_comap hMN)
    have hσMN :
        IsArithFrobAt ℤ
          (σM.restrictNormalHom (rationalTameLayer S N))
          PN := by
      simpa [hPMunder] using
        (arith_frob_int
          (E := rationalTameLayer S N)
          (L := rationalTameLayer S M)
          hσM)
    change
      IsArithFrobAt ℤ
        (rationalTameEquiv S N
          (rationalTameQuotient S N frobenius))
        PN
    have hfrobeniusM :
        rationalTameEquiv S M
            (rationalTameQuotient S M frobenius) =
          σM := by
      change
        rationalTameEquiv S M
            ((QuotientGroup.mk' M.toSubgroup) frobenius) =
          σM
      rw [hfrobenius]
      simp
    have hrestrict :
        (rationalTameEquiv S M
            (rationalTameQuotient S M frobenius)).restrictNormalHom
              (rationalTameLayer S N) =
          rationalTameEquiv S N
            (rationalTameQuotient S N frobenius) := by
      change
        (AlgEquiv.restrictNormalHom (rationalTameLayer S N))
            ((AlgEquiv.restrictNormalHom (rationalTameLayer S M))
              frobenius) =
          (AlgEquiv.restrictNormalHom (rationalTameLayer S N))
            frobenius
      exact
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
          (rationalTameLayer S N)
          (rationalTameLayer S M)
          frobenius).symm
    rw [← hrestrict, hfrobeniusM]
    exact hσMN
  have hfrobeniusExists :
      ∀ i : Fin d,
        ∃ frobenius : rationalTameGalois S,
          ∀ N : OpenNormalSubgroup (rationalTameGalois S),
            frobenius ∈ frobeniusSet N i := by
    intro i
    obtain ⟨frobenius, hfrobenius⟩ :=
      CompactSpace.iInter_nonempty
        (fun N => hfrobeniusSetClosed N i)
        (hfrobeniusSetFiniteIntersection i)
    exact
      ⟨frobenius, Set.mem_iInter.mp hfrobenius⟩
  choose frobenius hfrobenius using hfrobeniusExists
  refine
    ⟨{
      frobenius := frobenius
      frobenius_maps_arithmetic :=
        fun i N => hfrobenius i N
      tameRelation := ?_
    }⟩
  intro i
  let relator : rationalTameGalois S :=
    quotientMap (free.generator i) ^ (prime i - 1) *
      ⁅quotientMap (free.generator i), frobenius i⁆
  change relator = 1
  by_contra hrelator
  obtain ⟨N, hN⟩ :=
    open_normal_not
      (Γ := rationalTameGalois S)
      hrelator
  let D :=
    hsetup.generators_tame_inertia i
  let P :=
    D.primeAbove N
  have hPmem :=
    D.primeAbove_mem N
  letI : P.IsPrime :=
    hPmem.1
  letI : P.LiesOver (Ideal.rationalPrimeIdeal (prime i)) :=
    hPmem.2
  have hPGroupQuot :
      IsPGroup 3 (rationalTameGalois S ⧸ N.toSubgroup) :=
    hsetup.target_pro_three N
  have hPGroup :
      IsPGroup 3 (Gal(rationalTameLayer S N / ℚ)) :=
    hPGroupQuot.of_equiv
      (rationalTameEquiv S N)
  have hprime_ne_three :
      prime i ≠ 3 := by
    intro h
    have hnot : ¬ 3 ≡ 1 [MOD 3] := by
      decide
    exact hnot (by simpa [h] using hsetup.prime_mod_three i)
  have hCardCoprime :
      Nat.Coprime (prime i)
        (Nat.card (Gal(rationalTameLayer S N / ℚ))) :=
    coprime_card_p
      (hsetup.prime_isPrime i)
      Nat.prime_three
      hPGroup
      hprime_ne_three
  have hTame :
      RationalTamePrimes
        (S := NumberField.RingOfIntegers (rationalTameLayer S N))
        (prime i) :=
    tamely_ramified_gal
      (L := rationalTameLayer S N)
      (hsetup.prime_isPrime i)
      hCardCoprime
  have hσ :
      IsArithFrobAt ℤ
        (rationalTameEquiv S N
          (rationalTameQuotient S N (frobenius i)))
        P := by
    exact hfrobenius i N
  have hconj :
      rationalTameEquiv S N
            (rationalTameQuotient S N (frobenius i)) *
          (D.inertiaGenerator N :
            Gal(rationalTameLayer S N / ℚ)) *
          (rationalTameEquiv S N
            (rationalTameQuotient S N (frobenius i)))⁻¹ =
        (D.inertiaGenerator N :
          Gal(rationalTameLayer S N / ℚ)) ^ prime i :=
    Submission.arith_frob_inertia
      (L := rationalTameLayer S N)
      (hsetup.prime_isPrime i)
      hTame
      P
      (rationalTameEquiv S N
        (rationalTameQuotient S N (frobenius i)))
      hσ
      (D.inertiaGenerator N)
  have hgenerator :
      rationalTameEquiv S N
            (rationalTameQuotient S N
              (quotientMap (free.generator i))) =
          (D.inertiaGenerator N :
            Gal(rationalTameLayer S N / ℚ)) := by
    exact
      D.mapsFiniteLayer N
  have hfiniteRelation :
      (D.inertiaGenerator N :
            Gal(rationalTameLayer S N / ℚ)) ^
          (prime i - 1) *
        ⁅(D.inertiaGenerator N :
            Gal(rationalTameLayer S N / ℚ)),
          rationalTameEquiv S N
            (rationalTameQuotient S N (frobenius i))⁆ =
        1 := by
    rw [commutatorElement_def]
    calc
      (D.inertiaGenerator N :
              Gal(rationalTameLayer S N / ℚ)) ^ (prime i - 1) *
            ((D.inertiaGenerator N :
                  Gal(rationalTameLayer S N / ℚ)) *
              rationalTameEquiv S N
                (rationalTameQuotient S N (frobenius i)) *
              (D.inertiaGenerator N :
                Gal(rationalTameLayer S N / ℚ))⁻¹ *
              (rationalTameEquiv S N
                (rationalTameQuotient S N (frobenius i)))⁻¹) =
          (((D.inertiaGenerator N :
                  Gal(rationalTameLayer S N / ℚ)) ^ (prime i - 1) *
              (D.inertiaGenerator N :
                Gal(rationalTameLayer S N / ℚ))) *
            rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)) *
            (D.inertiaGenerator N :
              Gal(rationalTameLayer S N / ℚ))⁻¹ *
            (rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)))⁻¹) := by
                group
      _ =
          (D.inertiaGenerator N :
                Gal(rationalTameLayer S N / ℚ)) ^ prime i *
            rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)) *
            (D.inertiaGenerator N :
              Gal(rationalTameLayer S N / ℚ))⁻¹ *
            (rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)))⁻¹ := by
                rw [← pow_succ, Nat.sub_add_cancel (hsetup.prime_isPrime i).one_le]
      _ =
          (rationalTameEquiv S N
                (rationalTameQuotient S N (frobenius i)) *
              (D.inertiaGenerator N :
                Gal(rationalTameLayer S N / ℚ)) *
              (rationalTameEquiv S N
                (rationalTameQuotient S N (frobenius i)))⁻¹) *
            rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)) *
            (D.inertiaGenerator N :
              Gal(rationalTameLayer S N / ℚ))⁻¹ *
            (rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i)))⁻¹ := by
                rw [hconj]
      _ = 1 := by
        simp [mul_assoc]
  apply hN
  apply
    (QuotientGroup.eq_one_iff
      (N := (N : Subgroup (rationalTameGalois S)))
      relator).mp
  apply
    (rationalTameEquiv S N).injective
  calc
    rationalTameEquiv S N
          (rationalTameQuotient S N relator) =
        (rationalTameEquiv S N
              (rationalTameQuotient S N
                (quotientMap (free.generator i)))) ^
            (prime i - 1) *
          ⁅rationalTameEquiv S N
              (rationalTameQuotient S N
                (quotientMap (free.generator i))),
            rationalTameEquiv S N
              (rationalTameQuotient S N (frobenius i))⁆ := by
                dsimp [relator]
                rw [
                  map_mul,
                  map_pow,
                  map_commutatorElement,
                  map_mul,
                  map_pow,
                  map_commutatorElement
                ]
    _ = 1 := by
      rw [hgenerator]
      exact hfiniteRelation
    _ =
        rationalTameEquiv S N
          (rationalTameQuotient S N 1) := by
            simp

/--
Formal lift step: quotient-side Frobenius relation data can be lifted to the
displayed free pro-`3` source, because `quotientMap` is surjective.
-/
theorem shafarevich_frobenius_lifts
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    (hsetup :
      RationalTameSetup
        S
        free
        quotientMap
        prime)
    (D : RationalTameData hsetup) :
    ∃ (frobeniusLift : Fin d → free.Carrier)
      (_hsetup : RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift),
      True := by
  let frobeniusLift : Fin d → free.Carrier :=
    fun i =>
      Classical.choose
        (hsetup.quotientMap_surjective (D.frobenius i))
  have hfrobenius :
      ∀ i : Fin d,
        quotientMap (frobeniusLift i) =
          D.frobenius i := by
    intro i
    exact
      Classical.choose_spec
        (hsetup.quotientMap_surjective (D.frobenius i))
  refine
    ⟨frobeniusLift, ?_, trivial⟩
  refine
    {
      prime_range := hsetup.prime_range
      prime_injective := hsetup.prime_injective
      prime_isPrime := hsetup.prime_isPrime
      prime_mod_three := hsetup.prime_mod_three
      quotientMap_continuous := hsetup.quotientMap_continuous
      quotientMap_surjective := hsetup.quotientMap_surjective
      target_pro_three := hsetup.target_pro_three
      generators_tame_inertia :=
        hsetup.generators_tame_inertia
      frobenius_lift_arithmetic := ?_
      tame_maps_one := ?_
    }
  · intro i N
    simpa [hfrobenius i] using
      D.frobenius_maps_arithmetic i N
  · intro i
    simpa [
      rationalTameRelator,
      map_commutatorElement,
      hfrobenius i
    ] using
      D.tameRelation i

/--
Weak Frobenius-lift existence theorem for the rational tame pro-`3`
Koch-Shafarevich setup.

This is the local arithmetic half of the construction: starting from the base
choice of tame inertia generators, choose compatible Frobenius lifts in the
free source such that their finite-layer images are arithmetic Frobenii and
the corresponding tame Koch relators vanish in `G_S(ℚ)(3)`.
-/
theorem rational_shafarevich_lifts
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    (hsetup :
      RationalTameSetup
        S
        free
        quotientMap
        prime) :
    ∃ (frobeniusLift : Fin d → free.Carrier)
      (_hsetup : RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift),
      True := by
  exact
    shafarevich_frobenius_lifts
      hsetup
      (Classical.choice
        (rational_shafarevich_data hsetup))

/--
Step three in kernel form: once the arithmetic Koch setup has been chosen, the
finite embedding theorem is exactly the desired finite-quotient
factorization property.
-/
theorem shafarevich_factorization_setup
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift) :
    RationalTameFactorization
      S
      free
      quotientMap
      prime
      frobeniusLift := by
  intro P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP
      α hα hP hkill
  exact
    rational_shafarevich_embedding
      hsetup
      α
      hα
      hP
      hkill

/--
Koch-Shafarevich, finite quotient form, for `k = ℚ`, `p = 3`, `T = ∅`, and an
arbitrary finite tame set `S` of rational primes with every prime congruent to
`1` modulo `3`.

This existential form asserts that there are Frobenius lifts in the displayed
free pro-`3` source for which any finite `3`-group quotient killing the
resulting tame local relators factors through the corresponding maximal
pro-`3` Galois group.
-/
theorem rational_shafarevich_factorization
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    (hsetup :
      RationalTameSetup
        S
        free
        quotientMap
        prime) :
    ∃ (frobeniusLift : Fin d → free.Carrier)
      (_hsetup : RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift),
      RationalTameFactorization
        S
        free
        quotientMap
        prime
        frobeniusLift := by
  rcases
      rational_shafarevich_lifts
        hsetup with
    ⟨frobeniusLift, hkochSetup, _⟩
  refine
    ⟨frobeniusLift, hkochSetup, ?_⟩
  exact
    shafarevich_factorization_setup
      hkochSetup

end TBluepr
end Submission
