import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Tactic.FinCases
import Submission.NumberTheory.Density.QuarticChebotarevDensities

/-!
# Milne, Chapter 8, Example 8.37: the small quartic groups

This file proves the cycle tables and conditional Chebotarev densities for
the `C₂`, `V₄`, `C₄`, and `A₄` rows of Milne's quartic table.  It also
records the second faithful degree-four `V₄` action, omitted by the printed
classification when "no linear factor" is read literally.  The existing
companion files handle `D₈` and `S₄`.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField

noncomputable section

abbrev QuarticCyclicGroup := Multiplicative (ZMod 4)

/-- The regular action of `C₄` on four points. -/
def quarticCyclicAction : QuarticCyclicGroup →* Equiv.Perm (ZMod 4) where
  toFun i := Equiv.addRight i.toAdd
  map_one' := by
    ext x
    simp
  map_mul' i j := by
    ext x
    simp
    ring

theorem quartic_cyclic_injective : Function.Injective quarticCyclicAction := by
  intro i j hij
  apply Multiplicative.ext
  have h := DFunLike.congr_fun hij (0 : ZMod 4)
  change (0 : ZMod 4) + i.toAdd = 0 + j.toAdd at h
  simpa using h

theorem quartic_cycle_types :
    (quarticCyclicAction (.ofAdd 1)).cycleType = {4} ∧
      (quarticCyclicAction (.ofAdd 2)).cycleType = {2, 2} ∧
      (quarticCyclicAction (.ofAdd 3)).cycleType = {4} := by
  decide

@[simp]
theorem quartic_cyclic_card : Nat.card QuarticCyclicGroup = 4 := by
  simp [QuarticCyclicGroup]

abbrev QuarticKleinGroup := Multiplicative (ZMod 2 × ZMod 2)

/-- The regular action of the Klein four group. -/
def quarticKleinAction : QuarticKleinGroup →* Equiv.Perm (ZMod 2 × ZMod 2) where
  toFun i := Equiv.addRight i.toAdd
  map_one' := by
    change Equiv.addRight (0 : ZMod 2 × ZMod 2) = 1
    ext x <;> simp
  map_mul' i j := by
    ext x <;> simp <;> ring

theorem klein_action_injective : Function.Injective quarticKleinAction := by
  intro i j hij
  apply Multiplicative.ext
  have h := DFunLike.congr_fun hij (0 : ZMod 2 × ZMod 2)
  change (0 : ZMod 2 × ZMod 2) + i.toAdd = 0 + j.toAdd at h
  simpa using h

theorem klein_cycle_types :
    (quarticKleinAction (.ofAdd (1, 0))).cycleType = {2, 2} ∧
      (quarticKleinAction (.ofAdd (0, 1))).cycleType = {2, 2} ∧
      (quarticKleinAction (.ofAdd (1, 1))).cycleType = {2, 2} := by
  decide

@[simp]
theorem quartic_klein_card : Nat.card QuarticKleinGroup = 4 := by
  simp [QuarticKleinGroup]

/-- The other faithful degree-four action of the Klein four group: each
coordinate translates one of two two-point orbits.  This action occurs for a
product of two independent irreducible quadratic polynomials. -/
def quarticKleinQuadratic : QuarticKleinGroup →*
    Equiv.Perm (ZMod 2 ⊕ ZMod 2) where
  toFun i := Equiv.sumCongr
    (Equiv.addRight i.toAdd.1) (Equiv.addRight i.toAdd.2)
  map_one' := by
    ext x
    rcases x with x | x <;> simp
  map_mul' i j := by
    ext x
    rcases x with x | x <;> simp <;> ring

theorem quartic_klein_injective :
    Function.Injective quarticKleinQuadratic := by
  intro i j hij
  apply Multiplicative.ext
  apply Prod.ext
  · have h := DFunLike.congr_fun hij (Sum.inl (0 : ZMod 2))
    simpa [quarticKleinQuadratic] using h
  · have h := DFunLike.congr_fun hij (Sum.inr (0 : ZMod 2))
    simpa [quarticKleinQuadratic] using h

/-- The two coordinate generators are transpositions and their product is a
double transposition. -/
theorem quartic_klein_types :
    (quarticKleinQuadratic (.ofAdd (1, 0))).cycleType = {2} ∧
      (quarticKleinQuadratic (.ofAdd (0, 1))).cycleType = {2} ∧
      (quarticKleinQuadratic (.ofAdd (1, 1))).cycleType = {2, 2} := by
  decide

/-- Although this action has two orbits, it has no point fixed by the whole
group, matching the condition that the quartic polynomial has no linear
factor. -/
theorem quartic_klein_point :
    ¬ ∃ x : ZMod 2 ⊕ ZMod 2, ∀ g : QuarticKleinGroup,
      quarticKleinQuadratic g x = x := by
  decide

/-- This faithful Klein-four action is not contained in `A₄`: either
coordinate generator acts as an odd transposition. -/
theorem quartic_klein_odd :
    (quarticKleinQuadratic (.ofAdd (1, 0))).sign = -1 := by
  decide

abbrev QuarticOrderGroup := Multiplicative (ZMod 2)

/-- The fixed-point-free action of `C₂` on four points. -/
def quarticOrderAction : QuarticOrderGroup →*
    Equiv.Perm (ZMod 2 × ZMod 2) where
  toFun i := Equiv.addRight (i.toAdd, i.toAdd)
  map_one' := by
    change Equiv.addRight (0 : ZMod 2 × ZMod 2) = 1
    ext x <;> simp
  map_mul' i j := by
    ext x <;> simp <;> ring

theorem quartic_action_injective :
    Function.Injective quarticOrderAction := by
  intro i j hij
  apply Multiplicative.ext
  simpa [quarticOrderAction] using
    congrArg (fun f : Equiv.Perm (ZMod 2 × ZMod 2) ↦
      (f (0 : ZMod 2 × ZMod 2)).1) hij

theorem quartic_cycle_type :
    (quarticOrderAction (.ofAdd 1)).cycleType = {2, 2} := by
  decide

@[simp]
theorem quartic_nat_card : Nat.card QuarticOrderGroup = 2 := by
  simp [QuarticOrderGroup]

abbrev QuarticAlternatingGroup := alternatingGroup (Fin 4)

/-- The natural action of `A₄` on four points. -/
def quarticAlternatingAction : QuarticAlternatingGroup →* Equiv.Perm (Fin 4) :=
  (alternatingGroup (Fin 4)).subtype

theorem quartic_alternating_injective :
    Function.Injective quarticAlternatingAction :=
  Subtype.val_injective

@[simp]
theorem quartic_alternating_card : Nat.card QuarticAlternatingGroup = 12 := by
  rw [nat_card_alternatingGroup]
  norm_num

theorem quartic_double_transposition :
    Fintype.card {g : QuarticAlternatingGroup //
      (quarticAlternatingAction g).cycleType = {2, 2}} = 3 := by
  decide

theorem quartic_alternating_cycle :
    Fintype.card {g : QuarticAlternatingGroup //
      (quarticAlternatingAction g).cycleType = {3}} = 8 := by
  decide

def quarticDoubleTransposition : QuarticAlternatingGroup :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

def quarticAlternatingCycle : QuarticAlternatingGroup :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem double_transposition_type :
    (quarticAlternatingAction quarticDoubleTransposition).cycleType =
      {2, 2} := by
  decide

theorem quartic_alternating_type :
    (quarticAlternatingAction quarticAlternatingCycle).cycleType = {3} := by
  decide

theorem double_transposition_ncard :
    (ConjClasses.mk quarticDoubleTransposition).carrier.ncard = 3 := by
  rw [Set.ncard_eq_toFinset_card']
  change Fintype.card
    (ConjClasses.mk quarticDoubleTransposition).carrier = 3
  rw [ConjClasses.card_carrier]
  have hstab : Fintype.card
      (MulAction.stabilizer (ConjAct QuarticAlternatingGroup)
        quarticDoubleTransposition) = 4 := by decide
  have hcard : Fintype.card QuarticAlternatingGroup = 12 := by
    simpa only [Nat.card_eq_fintype_card] using quartic_alternating_card
  rw [hstab, hcard]

theorem quartic_conjugacy_ncard :
    (ConjClasses.mk quarticAlternatingCycle).carrier.ncard = 4 := by
  rw [Set.ncard_eq_toFinset_card']
  change Fintype.card
    (ConjClasses.mk quarticAlternatingCycle).carrier = 4
  rw [ConjClasses.card_carrier]
  have hstab : Fintype.card
      (MulAction.stabilizer (ConjAct QuarticAlternatingGroup)
        quarticAlternatingCycle) = 3 := by decide
  have hcard : Fintype.card QuarticAlternatingGroup = 12 := by
    simpa only [Nat.card_eq_fintype_card] using quartic_alternating_card
  rw [hstab, hcard]

theorem quartic_alternating_ncard :
    (ConjClasses.mk quarticAlternatingCycle⁻¹).carrier.ncard = 4 := by
  rw [Set.ncard_eq_toFinset_card']
  change Fintype.card
    (ConjClasses.mk quarticAlternatingCycle⁻¹).carrier = 4
  rw [ConjClasses.card_carrier]
  have hstab : Fintype.card
      (MulAction.stabilizer (ConjAct QuarticAlternatingGroup)
        quarticAlternatingCycle⁻¹) = 3 := by decide
  have hcard : Fintype.card QuarticAlternatingGroup = 12 := by
    simpa only [Nat.card_eq_fintype_card] using quartic_alternating_card
  rw [hstab, hcard]

theorem quartic_alternating_classes :
    ConjClasses.mk quarticAlternatingCycle ≠
      ConjClasses.mk quarticAlternatingCycle⁻¹ := by
  decide

variable (K : Type*) [Field K] [NumberField K]

/-- The identity type has density `1/4` in the `C₄` row. -/
theorem c_4_identity
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticCyclicGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 4) := by
  simpa [quartic_cyclic_card] using
    identity_frobenius_density K hcheb

/-- The double-transposition type has density `1/4` in the `C₄` row. -/
theorem c_4_double
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticCyclicGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass
        (ConjClasses.mk (.ofAdd 2 : QuarticCyclicGroup)))
      (1 / 4) := by
  simpa [quartic_cyclic_card] using
    abelian_density_chebotarev K hcheb
      (.ofAdd 2 : QuarticCyclicGroup)

/-- The two four-cycles together have density `1/2` in the `C₄` row. -/
theorem c_4_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticCyclicGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk (.ofAdd 1 : QuarticCyclicGroup)) ∪
        primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk (.ofAdd 3 : QuarticCyclicGroup)))
      (1 / 2) := by
  have hne :
      ConjClasses.mk (.ofAdd 1 : QuarticCyclicGroup) ≠
        ConjClasses.mk (.ofAdd 3 : QuarticCyclicGroup) := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h
    exact (show (.ofAdd 1 : QuarticCyclicGroup) ≠ .ofAdd 3 by decide) h
  have h1 := abelian_density_chebotarev K hcheb
    (.ofAdd 1 : QuarticCyclicGroup)
  have h3 := abelian_density_chebotarev K hcheb
    (.ofAdd 3 : QuarticCyclicGroup)
  have h := h1.union_of_disjoint K h3
    (disjoint_primes_frobenius K hne)
  rw [quartic_cyclic_card] at h
  convert h using 1 ; norm_num

/-- The identity type has density `1/2` in the quartic `C₂` row. -/
theorem c_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticOrderGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 2) := by
  simpa [quartic_nat_card] using
    identity_frobenius_density K hcheb

/-- The double-transposition type has density `1/2` in the quartic `C₂`
row. -/
theorem c_double_transposition
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticOrderGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass
        (ConjClasses.mk (.ofAdd 1 : QuarticOrderGroup)))
      (1 / 2) := by
  simpa [quartic_nat_card] using
    abelian_density_chebotarev K hcheb
      (.ofAdd 1 : QuarticOrderGroup)

/-- The identity type has density `1/4` in the `V₄` row. -/
theorem v_4_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticKleinGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 4) := by
  simpa [quartic_klein_card] using
    identity_frobenius_density K hcheb

/-- Every individual class in `V₄` has density `1/4`. -/
theorem v_4_each
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticKleinGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (sigma : QuarticKleinGroup) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma))
      (1 / 4) := by
  simpa [quartic_klein_card] using
    abelian_density_chebotarev K hcheb sigma

/-- The three nonidentity double transpositions together have density `3/4`
in the `V₄` row. -/
theorem v_4_double
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticKleinGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      ((primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk (.ofAdd (1, 0) : QuarticKleinGroup)) ∪
        primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk (.ofAdd (0, 1) : QuarticKleinGroup))) ∪
        primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk (.ofAdd (1, 1) : QuarticKleinGroup)))
      (3 / 4) := by
  let a : QuarticKleinGroup := .ofAdd (1, 0)
  let b : QuarticKleinGroup := .ofAdd (0, 1)
  let c : QuarticKleinGroup := .ofAdd (1, 1)
  have hab : ConjClasses.mk a ≠ ConjClasses.mk b := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h
    exact (show a ≠ b by decide) h
  have hac : ConjClasses.mk a ≠ ConjClasses.mk c := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h
    exact (show a ≠ c by decide) h
  have hbc : ConjClasses.mk b ≠ ConjClasses.mk c := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq] at h
    exact (show b ≠ c by decide) h
  have ha := abelian_density_chebotarev K hcheb a
  have hb := abelian_density_chebotarev K hcheb b
  have hc := abelian_density_chebotarev K hcheb c
  have habDensity := ha.union_of_disjoint K hb
    (disjoint_primes_frobenius K hab)
  have habcDensity := habDensity.union_of_disjoint K hc
    ((disjoint_primes_frobenius K hac).union_left
      (disjoint_primes_frobenius K hbc))
  rw [quartic_klein_card] at habcDensity
  dsimp [a, b, c] at habcDensity ⊢
  convert habcDensity using 1 ; norm_num

/-- The identity type has density `1/12` in the `A₄` row. -/
theorem identity_frobenius_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticAlternatingGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 12) := by
  simpa [quartic_alternating_card] using
    identity_frobenius_density K hcheb

/-- The double-transposition type has density `1/4` in the `A₄` row. -/
theorem double_transposition_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticAlternatingGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass
        (ConjClasses.mk quarticDoubleTransposition))
      (1 / 4) := by
  have h := hcheb (ConjClasses.mk quarticDoubleTransposition)
  rw [double_transposition_ncard,
    quartic_alternating_card] at h
  convert h using 1 ; norm_num

/-- The two `A₄` conjugacy classes of three-cycles together have density
`2/3`. -/
theorem cycle_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses QuarticAlternatingGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk quarticAlternatingCycle) ∪
        primesFrobeniusClass K frobeniusClass
          (ConjClasses.mk quarticAlternatingCycle⁻¹))
      (2 / 3) := by
  have h := (hcheb (ConjClasses.mk quarticAlternatingCycle)).union_of_disjoint K
    (hcheb (ConjClasses.mk quarticAlternatingCycle⁻¹))
    (disjoint_primes_frobenius K
      quartic_alternating_classes)
  rw [quartic_conjugacy_ncard,
    quartic_alternating_ncard,
    quartic_alternating_card] at h
  convert h using 1 ; norm_num

end

end Submission.NumberTheory.Milne
