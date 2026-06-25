import Submission.ClassField.LocalBrauer.CanonicalCarryInflation
import Submission.ClassField.LocalBrauer.ConcreteInflationBasic

/-!
# Chapter IV, Section 4: concrete and Brauer-theoretic inflation

Corollary 3.16 defines inflation abstractly by transporting inclusion of
relative Brauer groups through the crossed-product classification.  This file
constructs the usual cochain-level inflation along Galois restriction and
coefficient inclusion, then isolates the exact crossed-product comparison
needed to identify the two definitions.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u) [Field K]
variable {F E : FiniteGaloisIntermediateField K (SeparableClosure K)}

/-- Agreement of abstract inflation with concrete cochain inflation is
equivalent to equality of the corresponding relative Brauer classes. -/
theorem inflation_mk_cocycle
    (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ)) :
    inflationHom K hFE (MHTwo.mk c) =
        MHTwo.mk (concreteInflationCocycle K hFE c) ↔
      relativeBrauerInclusion K hFE
          (CProduc.relativeBrauerClass K F c) =
        CProduc.relativeBrauerClass K E
          (concreteInflationCocycle K hFE c) := by
  constructor
  · intro h
    calc
      relativeBrauerInclusion K hFE
          (CProduc.relativeBrauerClass K F c) =
        CProduc.hRelativeBrauer K E
          (inflationHom K hFE (MHTwo.mk c)) := by
            rw [relative_brauer_inflation]
            rfl
      _ = CProduc.hRelativeBrauer K E
          (MHTwo.mk (concreteInflationCocycle K hFE c)) :=
        congrArg (CProduc.hRelativeBrauer K E) h
      _ = CProduc.relativeBrauerClass K E
          (concreteInflationCocycle K hFE c) := rfl
  · intro h
    apply (CProduc.hRelativeBrauer K E).injective
    rw [relative_brauer_inflation]
    simpa using h

/-- The sole algebraic input needed to identify the abstract and concrete
inflations is Brauer equivalence of their crossed products. -/
theorem inflation_cocycle_equivalent
    (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))
    (hBrauer : IsBrauerEquivalent
      (CProduc.centralSimpleCSA K F c)
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFE c))) :
    inflationHom K hFE (MHTwo.mk c) =
      MHTwo.mk (concreteInflationCocycle K hFE c) := by
  rw [inflation_mk_cocycle]
  apply Subtype.ext
  change BGroups.brauerClass K
      (CProduc.centralSimpleCSA K F c) =
    BGroups.brauerClass K
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFE c))
  exact (BGroups.brauer_class _ _ _).2 hBrauer

/-- A matrix-algebra comparison is a concrete sufficient form of the
Brauer equivalence required above.  In the standard inflation theorem one
takes `q = [E : F]`. -/
theorem inflation_cocycle_matrix
    (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))
    (q : ℕ) (hq : q ≠ 0)
    (e : CProduc (concreteInflationCocycle K hFE c) ≃ₐ[K]
      Matrix (Fin q) (Fin q) (CProduc c)) :
    inflationHom K hFE (MHTwo.mk c) =
      MHTwo.mk (concreteInflationCocycle K hFE c) := by
  apply inflation_cocycle_equivalent
  refine ⟨q, 1, hq, one_ne_zero, ?_⟩
  exact ⟨e.symm.trans
    (BGroups.matrixFinAlg K
      (CProduc (concreteInflationCocycle K hFE c))).symm⟩

/-- Conversely, agreement of abstract and concrete inflation forces exactly
the crossed-product Brauer equivalence displayed above. -/
theorem equivalent_inflation_cocycle
    (hFE : F ≤ E)
    (c : NMCocycl₂ (G := Gal(F/K)) (M := Fˣ))
    (h : inflationHom K hFE (MHTwo.mk c) =
      MHTwo.mk (concreteInflationCocycle K hFE c)) :
    IsBrauerEquivalent
      (CProduc.centralSimpleCSA K F c)
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFE c)) := by
  have hrel :=
    (inflation_mk_cocycle K hFE c).1 h
  have habs := congrArg Subtype.val hrel
  change CProduc.brauerClass K F c =
    CProduc.brauerClass K E (concreteInflationCocycle K hFE c) at habs
  exact (BGroups.brauer_class _ _ _).1 habs

section Carry

/-- A base-field unit, viewed as an invariant coefficient in a pulled-back
cyclic Galois action. -/
def cyclicBaseInvariant {L : Type u} [Field L] [Algebra K L]
    {d : ℕ} (eGal : Multiplicative (ZMod d) ≃* Gal(L/K))
    (a : Kˣ) :
    letI : MulDistribMulAction (Multiplicative (ZMod d)) Lˣ :=
      GroupH2.pulledAction eGal
    CyclicH2.invariants (n := d) (M := Lˣ) := by
  letI : MulDistribMulAction (Multiplicative (ZMod d)) Lˣ :=
    GroupH2.pulledAction eGal
  refine ⟨Units.map (algebraMap K L) a, ?_⟩
  intro g
  apply Units.ext
  simp [MulAction.compHom_smul_def]

/-- The transported cyclic carry cocycle, stated without the unused local
field hypotheses of `unramifiedCarryCocycle`. -/
def galoisCarryCocycle {L : Type u} [Field L] [Algebra K L]
    {d : ℕ} [NeZero d]
    (eGal : Multiplicative (ZMod d) ≃* Gal(L/K))
    (a : Kˣ) :
    NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) := by
  letI : MulDistribMulAction (Multiplicative (ZMod d)) Lˣ :=
    GroupH2.pulledAction eGal
  let pi := cyclicBaseInvariant K eGal a
  exact MHTrans.cocycleMap eGal (MulEquiv.refl Lˣ)
    (by intro g x; rfl) (CCarry.factorSet pi.1 pi.2)

/-- For cyclic identifications commuting with Galois restriction and
reduction of indices, concrete inflation carries the small carry class to
the prescribed power of the large carry class.  This is the unconditional
cochain calculation; no Brauer-theoretic inflation comparison is used. -/
theorem inflation_carry_cocycle
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (hFE : F ≤ E)
    (eR : Multiplicative (ZMod n) ≃* Gal(F/K))
    (eS : Multiplicative (ZMod m) ≃* Gal(E/K))
    (hcompat : ∀ z,
      galoisRestrictionHom K hFE (eS z) =
        eR (CCarry.indexReduction hnm z))
    (varpiK : Kˣ) :
    MHTwo.mk
        (concreteInflationCocycle K hFE
          (galoisCarryCocycle K eR varpiK)) =
      MHTwo.mk
          (galoisCarryCocycle K eS varpiK) ^ (m / n) := by
  letI : MulDistribMulAction (Multiplicative (ZMod m)) Eˣ :=
    GroupH2.pulledAction eS
  let piE := cyclicBaseInvariant K eS varpiK
  have hcyc := CCarry.mk_set_carry
    (M := Eˣ) hnm piE.1 piE.2
  let transport := MHTrans.h2Equiv
    eS (MulEquiv.refl Eˣ) (by intro g x; rfl)
  have ht := congrArg transport hcyc
  rw [map_pow] at ht
  have hbig :
      transport (MHTwo.mk
        (CCarry.factorSet piE.1 piE.2)) =
      MHTwo.mk (galoisCarryCocycle K eS varpiK) := by
    rw [MHTrans.h_2_mk]
    rfl
  have hsmallCocycle :
      MHTrans.cocycleMap eS (MulEquiv.refl Eˣ)
          (by intro g x; rfl)
          (CCarry.reductionFactorSet hnm piE.1 piE.2) =
        concreteInflationCocycle K hFE
          (galoisCarryCocycle K eR varpiK) := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    have hg : eR.symm (galoisRestrictionHom K hFE g) =
        CCarry.indexReduction hnm (eS.symm g) := by
      apply eR.injective
      rw [eR.apply_symm_apply, ← hcompat, eS.apply_symm_apply]
    have hh : eR.symm (galoisRestrictionHom K hFE h) =
        CCarry.indexReduction hnm (eS.symm h) := by
      apply eR.injective
      rw [eR.apply_symm_apply, ← hcompat, eS.apply_symm_apply]
    rw [MHTrans.cocycleMap_apply,
      concrete_inflation_cocycle]
    dsimp only [galoisCarryCocycle]
    change piE.1 ^ CCarry.carry
          (ZMod.cast (eS.symm g).toAdd : ZMod n)
          (ZMod.cast (eS.symm h).toAdd : ZMod n) =
      coefficientUnitsHom K hFE
        ((Units.map (algebraMap K F) varpiK) ^
          CCarry.carry
            (eR.symm (galoisRestrictionHom K hFE g)).toAdd
            (eR.symm (galoisRestrictionHom K hFE h)).toAdd)
    rw [map_pow, hg, hh]
    rfl
  calc
    MHTwo.mk
        (concreteInflationCocycle K hFE
          (galoisCarryCocycle K eR varpiK)) =
      transport (MHTwo.mk
        (CCarry.reductionFactorSet hnm piE.1 piE.2)) := by
          rw [MHTrans.h_2_mk, hsmallCocycle]
          rfl
    _ = transport (MHTwo.mk
        (CCarry.factorSet piE.1 piE.2)) ^ (m / n) := ht
    _ = MHTwo.mk
        (galoisCarryCocycle K eS varpiK) ^ (m / n) :=
      congrArg (fun x ↦ x ^ (m / n)) hbig

/-- Once the standard crossed-product Brauer comparison is supplied,
abstract inflation satisfies the carry-power formula for every compatible
pair of cyclic identifications. -/
theorem inflation_carry_equivalent
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m)
    (hFE : F ≤ E)
    (eR : Multiplicative (ZMod n) ≃* Gal(F/K))
    (eS : Multiplicative (ZMod m) ≃* Gal(E/K))
    (hcompat : ∀ z,
      galoisRestrictionHom K hFE (eS z) =
        eR (CCarry.indexReduction hnm z))
    (a : Kˣ)
    (hBrauer : IsBrauerEquivalent
      (CProduc.centralSimpleCSA K F
        (galoisCarryCocycle K eR a))
      (CProduc.centralSimpleCSA K E
        (concreteInflationCocycle K hFE
          (galoisCarryCocycle K eR a)))) :
    inflationHom K hFE
        (MHTwo.mk (galoisCarryCocycle K eR a)) =
      MHTwo.mk (galoisCarryCocycle K eS a) ^ (m / n) := by
  exact
    (inflation_cocycle_equivalent
      K hFE (galoisCarryCocycle K eR a) hBrauer).trans
    (inflation_carry_cocycle
      K hnm hFE eR eS hcompat a)

end Carry

/-- The algebraic carry cocycle above is definitionally the carry cocycle
used by the local-field development. -/
theorem carry_cocycle_unramified
    (k L : Type u) [NontriviallyNormedField k]
    [NontriviallyNormedField L] [Algebra k L]
    {d : ℕ} [NeZero d]
    (eGal : Multiplicative (ZMod d) ≃* Gal(L/k)) (a : kˣ) :
    galoisCarryCocycle k eGal a =
      unramifiedCarryCocycle k L eGal a := by
  rfl

section CanonicalFactorialTower

variable (k : Type u) [NontriviallyNormedField k] [IsUltrametricDist k]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]

set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate fields require deeper scalar-tower instance search.
/-- The generic restriction homomorphism specializes to the restriction map
used for the canonical factorial tower. -/
theorem galois_restriction_factorial
    {r s : ℕ} (h : r ≤ s) :
    galoisRestrictionHom k
        (factorial_level_monotone k h) =
      factorialRestrictionHom k h := by
  change (finGaloisGroupMap ((CategoryTheory.homOfLE
    (factorial_level_monotone k h)).op)).hom.hom = _
  rfl

/-- Every pair of canonical factorial levels admits cyclic identifications
commuting with the generic restriction map used by concrete inflation. -/
theorem factorial_gal_z
    {r s : ℕ} (h : r ≤ s) :
    ∃ eS : Multiplicative (ZMod (invariantLevelDegree s)) ≃*
        Gal(unramifiedFactorialLevel k s/k),
      ∃ eR : Multiplicative (ZMod (invariantLevelDegree r)) ≃*
        Gal(unramifiedFactorialLevel k r/k),
        ∀ z,
          galoisRestrictionHom k
              (factorial_level_monotone k h) (eS z) =
            eR (CCarry.indexReduction
              (invariant_level_dvd h) z) := by
  simpa [galois_restriction_factorial k h] using
    factorial_gal_mod k h

end CanonicalFactorialTower

end

end Submission.CField.LBrauer
