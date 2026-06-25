import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Galois.Profinite
import Submission.ClassField.LocalBrauer.FiniteInvariantCompatibility

/-!
# Chapter IV, Section 4: inflation of cyclic carry classes

For `n | m`, indexReduction gives the quotient from the cyclic group of order
`m` to the cyclic group of order `n`.  Pulling the order-`n` carry cocycle
back along this quotient differs from the `(m / n)`-th power of the order-`m`
carry cocycle by the explicit coboundary `a |-> pi ^ (a.val / n)`.

This is the group-cohomological calculation underlying the carry-class
inflation formula in Proposition 4.3.  It is stated independently of local
fields so that the only remaining comparison is between this concrete
cochain inflation and the Brauer-theoretic `inflationHom` of Corollary 3.16.
-/

namespace Submission.CField.LBrauer

noncomputable section

open CProduca
open CategoryTheory Opposite

attribute [local instance] Units.mulDistribMulActionRight

namespace CCarry

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Reduction of cyclic indices along a divisibility `n | m`. -/
def indexReduction (hnm : n ∣ m) :
    Multiplicative (ZMod m) →* Multiplicative (ZMod n) :=
  (ZMod.castHom hnm (ZMod n)).toAddMonoidHom.toMultiplicative

omit [NeZero n] [NeZero m] in
@[simp]
theorem reduction_toAdd (hnm : n ∣ m) (a : Multiplicative (ZMod m)) :
    (indexReduction hnm a).toAdd = ZMod.cast a.toAdd :=
  rfl

omit [NeZero n] in
private theorem val_reduction (_hnm : n ∣ m) (a : ZMod m) :
    (ZMod.cast a : ZMod n).val = a.val % n := by
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

/-- The elementary quotient-and-remainder identity behind carry inflation. -/
theorem div_carry_reduction (hnm : n ∣ m) (a b : ZMod m) :
    a.val / n + b.val / n +
        carry (ZMod.cast a : ZMod n) (ZMod.cast b : ZMod n) =
      (m / n) * carry a b + (a + b).val / n := by
  have hn : 0 < n := NeZero.pos n
  have hm : 0 < m := NeZero.pos m
  have hmn : n * (m / n) = m := Nat.mul_div_cancel' hnm
  have ha := Nat.mod_add_div a.val n
  have hb := Nat.mod_add_div b.val n
  have hab := val_add_carry a b
  have hred := val_add_carry
    (ZMod.cast a : ZMod n) (ZMod.cast b : ZMod n)
  have habmod := Nat.mod_add_div (a + b).val n
  rw [val_reduction hnm, val_reduction hnm] at hred
  have hredadd :
      ((ZMod.cast (a + b) : ZMod n).val) = (a + b).val % n :=
    val_reduction hnm (a + b)
  rw [← ZMod.cast_add hnm, hredadd] at hred
  apply Nat.eq_of_mul_eq_mul_left hn
  simp only [Nat.mul_add, ← Nat.mul_assoc, hmn]
  omega

variable {M : Type*} [CommGroup M]
  [MulDistribMulAction (Multiplicative (ZMod m)) M]

/-- Pullback of the order-`n` carry cocycle along indexReduction of cyclic
indices.  Only invariance of `pi` for the order-`m` action is needed. -/
def reductionFactorSet (hnm : n ∣ m) (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod m), g • pi = pi) :
    NMCocycl₂ (G := Multiplicative (ZMod m)) (M := M) where
  toFun p := pi ^ carry (ZMod.cast p.1.toAdd : ZMod n)
    (ZMod.cast p.2.toAdd : ZMod n)
  isMulCocycle₂ := by
    intro g h j
    rw [show g • pi ^ carry (ZMod.cast h.toAdd : ZMod n)
        (ZMod.cast j.toAdd : ZMod n) =
        pi ^ carry (ZMod.cast h.toAdd : ZMod n)
          (ZMod.cast j.toAdd : ZMod n) by
      change (MulDistribMulAction.toMonoidHom M g)
          (pi ^ carry (ZMod.cast h.toAdd : ZMod n)
            (ZMod.cast j.toAdd : ZMod n)) = _
      rw [map_pow]
      change (g • pi) ^ carry (ZMod.cast h.toAdd : ZMod n)
        (ZMod.cast j.toAdd : ZMod n) = _
      rw [hpi g]]
    rw [← pow_add, ← pow_add]
    apply congrArg (pi ^ ·)
    simpa only [toAdd_mul, ZMod.cast_add hnm] using
      carry_cocycle (ZMod.cast g.toAdd : ZMod n)
        (ZMod.cast h.toAdd : ZMod n) (ZMod.cast j.toAdd : ZMod n)
  map_one_fst := by
    intro g
    simp [carry, ZMod.val_lt]
  map_one_snd := by
    intro g
    simp [carry, ZMod.val_lt]

omit [NeZero m] in
@[simp]
theorem reduction_factor_set (hnm : n ∣ m) (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod m), g • pi = pi)
    (a b : Multiplicative (ZMod m)) :
    reductionFactorSet hnm pi hpi (a, b) =
      pi ^ carry (ZMod.cast a.toAdd : ZMod n)
        (ZMod.cast b.toAdd : ZMod n) :=
  rfl

/-- The pulled-back small carry cocycle and the appropriate power of the
large carry cocycle differ by the coboundary `a |-> pi ^ (a.val / n)`. -/
theorem reduction_set_cohomologous
    (hnm : n ∣ m) (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod m), g • pi = pi) :
    MHTwo.IsCohomologous
      ((factorSet pi hpi) ^ (m / n))
      (reductionFactorSet hnm pi hpi) := by
  refine ⟨fun a ↦ pi ^ (a.toAdd.val / n), ?_⟩
  intro a b
  have hid := div_carry_reduction hnm a.toAdd b.toAdd
  have hsmul : a • pi ^ (b.toAdd.val / n) =
      pi ^ (b.toAdd.val / n) := by
    change (MulDistribMulAction.toMonoidHom M a)
      (pi ^ (b.toAdd.val / n)) = _
    rw [map_pow]
    change (a • pi) ^ (b.toAdd.val / n) = _
    rw [hpi a]
  rw [hsmul]
  dsimp only
  rw [NMCocycl₂.pow_apply]
  change pi ^ (b.toAdd.val / n) / pi ^ ((a * b).toAdd.val / n) *
      pi ^ (a.toAdd.val / n) =
    (pi ^ carry a.toAdd b.toAdd) ^ (m / n) /
      pi ^ carry (ZMod.cast a.toAdd : ZMod n)
        (ZMod.cast b.toAdd : ZMod n)
  have hid' :
      a.toAdd.val / n + b.toAdd.val / n +
          carry (ZMod.cast a.toAdd : ZMod n)
            (ZMod.cast b.toAdd : ZMod n) =
        carry a.toAdd b.toAdd * (m / n) + (a * b).toAdd.val / n := by
    simpa [Nat.mul_comm] using hid
  have hpow := congrArg (pi ^ ·) hid'
  simp only [pow_add, pow_mul] at hpow
  have hcancel := congrArg (fun x : M ↦
    x * (pi ^ carry (ZMod.cast a.toAdd : ZMod n)
      (ZMod.cast b.toAdd : ZMod n))⁻¹ *
      (pi ^ ((a * b).toAdd.val / n))⁻¹) hpow
  simpa [div_eq_mul_inv, pow_mul,
    mul_assoc, mul_left_comm, mul_comm] using hcancel

/-- Consequently the pulled-back carry class is the prescribed power of
the carry class at the larger cyclic level. -/
theorem mk_set_carry
    (hnm : n ∣ m) (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod m), g • pi = pi) :
    MHTwo.mk (reductionFactorSet hnm pi hpi) =
      MHTwo.mk (factorSet pi hpi) ^ (m / n) := by
  rw [← MHTwo.mk_pow, MHTwo.mk_eq_iff]
  exact MHTwo.isCohomologous_symm
    (reduction_set_cohomologous hnm pi hpi)

end CCarry

namespace CCohere

/-- Cyclic automorphisms of the multiplicative copy of `ZMod d` are units
of `ZMod d`. -/
noncomputable def mulAutUnits (d : ℕ) :
    MulAut (Multiplicative (ZMod d)) ≃* (ZMod d)ˣ :=
  (MulAutMultiplicative (ZMod d)).trans (ZMod.AddAutEquivUnits d)

@[simp]
theorem aut_symm_add (d : ℕ) (u : (ZMod d)ˣ)
    (z : Multiplicative (ZMod d)) :
    ((mulAutUnits d).symm u z).toAdd = (u : ZMod d) * z.toAdd := by
  rfl

/-- Lifting a unit along `ZMod m -> ZMod n` lifts the associated cyclic
automorphism and makes it commute with indexReduction. -/
theorem reduction_aut_symm
    {n m : ℕ} [NeZero n] [NeZero m]
    (hnm : n ∣ m) (uM : (ZMod m)ˣ) (uN : (ZMod n)ˣ)
    (hu : ZMod.unitsMap hnm uM = uN)
    (z : Multiplicative (ZMod m)) :
    CCarry.indexReduction hnm ((mulAutUnits m).symm uM z) =
      (mulAutUnits n).symm uN (CCarry.indexReduction hnm z) := by
  apply Multiplicative.toAdd.injective
  rw [CCarry.reduction_toAdd, aut_symm_add,
    aut_symm_add, CCarry.reduction_toAdd]
  rw [ZMod.cast_mul hnm, ← ZMod.unitsMap_val hnm, hu]

end CCohere

section CanonicalFactorialTower

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Restriction of Galois automorphisms along an inclusion in the canonical
factorial unramified tower. -/
noncomputable def factorialRestrictionHom
    {r s : ℕ} (h : r ≤ s) :
    Gal(unramifiedFactorialLevel K s / K) →*
      Gal(unramifiedFactorialLevel K r / K) :=
  (finGaloisGroupMap ((homOfLE
    (factorial_level_monotone K h)).op)).hom.hom

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing the scalar tower between factorial levels needs extra depth.
set_option maxHeartbeats 1000000 in
-- Nested intermediate-field scalar structures need deeper instance search.
/-- Restriction between two canonical factorial levels is surjective. -/
theorem factorial_restriction_surjective
    {r s : ℕ} (h : r ≤ s) :
    Function.Surjective
      (factorialRestrictionHom K h) := by
  let S : (FiniteGaloisIntermediateField K (SeparableClosure K))ᵒᵖ :=
    op (unramifiedFactorialLevel K s)
  let R : (FiniteGaloisIntermediateField K (SeparableClosure K))ᵒᵖ :=
    op (unramifiedFactorialLevel K r)
  let f : S ⟶ R :=
    (homOfLE (factorial_level_monotone K h)).op
  letI : Normal K R.unop := IsGalois.to_normal
  letI : Algebra R.unop S.unop :=
    RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom f.1)
  letI : IsScalarTower K R.unop S.unop :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  change Function.Surjective (finGaloisGroupMap f).hom.hom
  unfold finGaloisGroupMap
  exact AlgEquiv.restrictNormalHom_surjective S.unop

set_option synthInstance.maxHeartbeats 100000 in
-- Unfolding restriction through subtype fields needs deeper instance search.
@[simp]
theorem factorial_restriction_refl (r : ℕ) :
    factorialRestrictionHom K (le_refl r) =
      MonoidHom.id Gal(unramifiedFactorialLevel K r / K) := by
  let L := unramifiedFactorialLevel K r
  let f : op L ⟶ op L := (homOfLE (le_refl L)).op
  change (finGaloisGroupMap f).hom.hom = MonoidHom.id Gal(L / K)
  rw [show f = 𝟙 (op L) from Subsingleton.elim _ _, finGaloisGroupMap.map_id]
  rfl

/-- Restriction along the canonical factorial tower is transitive. -/
theorem factorial_restriction_trans
    {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    factorialRestrictionHom K (hrs.trans hst) =
      (factorialRestrictionHom K hrs).comp
        (factorialRestrictionHom K hst) := by
  let hrs' := factorial_level_monotone K hrs
  let hst' := factorial_level_monotone K hst
  let hrt' := factorial_level_monotone K (hrs.trans hst)
  let f : op (unramifiedFactorialLevel K t) ⟶
      op (unramifiedFactorialLevel K s) := (homOfLE hst').op
  let g : op (unramifiedFactorialLevel K s) ⟶
      op (unramifiedFactorialLevel K r) := (homOfLE hrs').op
  let q : op (unramifiedFactorialLevel K t) ⟶
      op (unramifiedFactorialLevel K r) := (homOfLE hrt').op
  change (finGaloisGroupMap q).hom.hom =
    (finGaloisGroupMap f ≫ finGaloisGroupMap g).hom.hom
  rw [show q = f ≫ g from Subsingleton.elim _ _, finGaloisGroupMap.map_comp]

/-- Reduction of cyclic factorial indices is transitive. -/
theorem cyclic_carry_trans
    {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t)
    (z : Multiplicative (ZMod (invariantLevelDegree t))) :
    CCarry.indexReduction (invariant_level_dvd (hrs.trans hst)) z =
      CCarry.indexReduction (invariant_level_dvd hrs)
        (CCarry.indexReduction (invariant_level_dvd hst) z) := by
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  letI : NeZero (invariantLevelDegree s) :=
    ⟨(invariant_level_pos s).ne'⟩
  letI : NeZero (invariantLevelDegree t) :=
    ⟨(invariant_level_pos t).ne'⟩
  apply Multiplicative.toAdd.injective
  change ZMod.cast z.toAdd = ZMod.cast (ZMod.cast z.toAdd)
  have hcomp := ZMod.castHom_comp
    (invariant_level_dvd hrs)
    (invariant_level_dvd hst)
  exact DFunLike.congr_fun hcomp.symm z.toAdd

@[simp]
theorem cyclic_carry_refl (r : ℕ)
    (z : Multiplicative (ZMod (invariantLevelDegree r))) :
    CCarry.indexReduction
        (invariant_level_dvd (le_refl r)) z = z := by
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  apply Multiplicative.toAdd.injective
  exact ZMod.cast_id _ z.toAdd

private theorem multiplicative_zmod_generator
    (d : ℕ) [NeZero d] :
    ∀ z : Multiplicative (ZMod d),
      z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod d)) := by
  intro z
  refine ⟨(z.toAdd.val : ℤ), ?_⟩
  change (Multiplicative.ofAdd (1 : ZMod d)) ^ (z.toAdd.val : ℤ) = z
  rw [zpow_natCast]
  apply Multiplicative.toAdd.injective
  simp

/-- For every inclusion of two canonical factorial levels, the cyclic
identifications can be chosen compatibly with restriction and indexReduction of
indices.  Thus the arbitrary generators selected by
`galZMod` do not create a mathematical
obstruction: a compatible pair always exists. -/
theorem factorial_gal_mod
    {r s : ℕ} (h : r ≤ s) :
    ∃ eS : Multiplicative (ZMod (invariantLevelDegree s)) ≃*
        Gal(unramifiedFactorialLevel K s / K),
      ∃ eR : Multiplicative (ZMod (invariantLevelDegree r)) ≃*
        Gal(unramifiedFactorialLevel K r / K),
        ∀ z,
          factorialRestrictionHom K h (eS z) =
            eR (CCarry.indexReduction
              (invariant_level_dvd h) z) := by
  let ns := invariantLevelDegree s
  let nr := invariantLevelDegree r
  letI : NeZero ns := ⟨(invariant_level_pos s).ne'⟩
  letI : NeZero nr := ⟨(invariant_level_pos r).ne'⟩
  let eS := galZMod K ns
  let sigmaS := eS (Multiplicative.ofAdd (1 : ZMod ns))
  let res := factorialRestrictionHom K h
  have hsigmaS : ∀ x, x ∈ Subgroup.zpowers sigmaS := by
    intro x
    obtain ⟨z, rfl⟩ := eS.surjective x
    obtain ⟨i, hi⟩ := multiplicative_zmod_generator ns z
    refine ⟨i, ?_⟩
    change sigmaS ^ i = eS z
    calc
      sigmaS ^ i = eS ((Multiplicative.ofAdd (1 : ZMod ns)) ^ i) := by
        rw [map_zpow]
      _ = eS z := congrArg eS hi
  have hresSigma : ∀ x, x ∈ Subgroup.zpowers (res sigmaS) := by
    intro x
    obtain ⟨y, rfl⟩ :=
      factorial_restriction_surjective K h x
    obtain ⟨i, hi⟩ := hsigmaS y
    refine ⟨i, ?_⟩
    change (res sigmaS) ^ i = res y
    calc
      (res sigmaS) ^ i = res (sigmaS ^ i) :=
        (map_zpow res sigmaS i).symm
      _ = res y := congrArg res hi
  have hcardR :
      Nat.card Gal(unramifiedFactorialLevel K r / K) = nr := by
    rw [IsGalois.card_aut_eq_finrank,
      factorial_level_finrank K r]
  let eR : Multiplicative (ZMod nr) ≃*
      Gal(unramifiedFactorialLevel K r / K) :=
    zmodMulEquivOfGenerator hresSigma hcardR
  refine ⟨eS, eR, ?_⟩
  intro z
  have hz : z =
      (Multiplicative.ofAdd (1 : ZMod ns)) ^ z.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  have hredz : CCarry.indexReduction
      (invariant_level_dvd h) z =
      (Multiplicative.ofAdd (1 : ZMod nr)) ^ z.toAdd.val := by
    calc
      CCarry.indexReduction
          (invariant_level_dvd h) z =
        CCarry.indexReduction
          (invariant_level_dvd h)
            ((Multiplicative.ofAdd (1 : ZMod ns)) ^ z.toAdd.val) :=
        congrArg _ hz
      _ = (CCarry.indexReduction
          (invariant_level_dvd h)
            (Multiplicative.ofAdd (1 : ZMod ns))) ^ z.toAdd.val :=
        map_pow _ _ _
      _ = (Multiplicative.ofAdd (1 : ZMod nr)) ^ z.toAdd.val := by
        congr 1
        apply Multiplicative.toAdd.injective
        change ZMod.cast (1 : ZMod ns) = (1 : ZMod nr)
        exact ZMod.cast_one (invariant_level_dvd h)
  calc
    factorialRestrictionHom K h (eS z) =
        res (eS ((Multiplicative.ofAdd (1 : ZMod ns)) ^ z.toAdd.val)) := by
      exact congrArg res (congrArg eS hz)
    _ = res (sigmaS ^ z.toAdd.val) := by
      exact congrArg res (map_pow eS _ _)
    _ = (res sigmaS) ^ z.toAdd.val := map_pow res _ _
    _ = (eR (Multiplicative.ofAdd (1 : ZMod nr))) ^ z.toAdd.val := by
      rw [zmodMulEquivOfGenerator_apply_ofAdd_one]
    _ = eR ((Multiplicative.ofAdd (1 : ZMod nr)) ^ z.toAdd.val) := by
      exact (map_pow eR _ _).symm
    _ = eR (CCarry.indexReduction
        (invariant_level_dvd h) z) := by rw [hredz]

/-- A compatible upper cyclic identification can be chosen over any fixed
identification at the lower level. -/
theorem compatible_factorial_gal
    {r s : ℕ} (h : r ≤ s)
    (eR : Multiplicative (ZMod (invariantLevelDegree r)) ≃*
      Gal(unramifiedFactorialLevel K r/K)) :
    ∃ eS : Multiplicative (ZMod (invariantLevelDegree s)) ≃*
        Gal(unramifiedFactorialLevel K s / K),
      ∀ z,
        factorialRestrictionHom K h (eS z) =
          eR (CCarry.indexReduction
            (invariant_level_dvd h) z) := by
  let nr := invariantLevelDegree r
  let ns := invariantLevelDegree s
  letI : NeZero nr := ⟨(invariant_level_pos r).ne'⟩
  letI : NeZero ns := ⟨(invariant_level_pos s).ne'⟩
  obtain ⟨eS0, eR0, h0⟩ :=
    factorial_gal_mod K h
  let phiR : MulAut (Multiplicative (ZMod nr)) := eR.trans eR0.symm
  let uR : (ZMod nr)ˣ := CCohere.mulAutUnits nr phiR
  obtain ⟨uS, huS⟩ := ZMod.unitsMap_surjective
    (invariant_level_dvd h) uR
  let phiS : MulAut (Multiplicative (ZMod ns)) :=
    (CCohere.mulAutUnits ns).symm uS
  let eS : Multiplicative (ZMod ns) ≃*
      Gal(unramifiedFactorialLevel K s / K) := phiS.trans eS0
  refine ⟨eS, ?_⟩
  intro z
  calc
    factorialRestrictionHom K h (eS z) =
        eR0 (CCarry.indexReduction
          (invariant_level_dvd h) (phiS z)) := h0 (phiS z)
    _ = eR0 ((CCohere.mulAutUnits nr).symm uR
          (CCarry.indexReduction
            (invariant_level_dvd h) z)) := by
      apply congrArg eR0
      exact CCohere.reduction_aut_symm
        (invariant_level_dvd h) uS uR huS z
    _ = eR (CCarry.indexReduction
          (invariant_level_dvd h) z) := by
      rw [show (CCohere.mulAutUnits nr).symm uR = phiR from
        (CCohere.mulAutUnits nr).symm_apply_apply phiR]
      change eR0 (eR0.symm
        (eR (CCarry.indexReduction
          (invariant_level_dvd h) z))) = _
      rw [eR0.apply_symm_apply]

/-- A single recursively chosen family of cyclic identifications for the
entire canonical factorial tower. -/
noncomputable def factorialCoherentGal :
    (r : ℕ) → Multiplicative (ZMod (invariantLevelDegree r)) ≃*
      Gal(unramifiedFactorialLevel K r / K)
  | 0 => by
      letI : NeZero (invariantLevelDegree 0) :=
        ⟨(invariant_level_pos 0).ne'⟩
      exact galZMod K
        (invariantLevelDegree 0)
  | r + 1 => Classical.choose
      (compatible_factorial_gal K
        (Nat.le_succ r) (factorialCoherentGal r))

/-- Consecutive members of the recursively chosen family commute with
Galois restriction and cyclic indexReduction. -/
theorem coherent_gal_z
    (r : ℕ) (z : Multiplicative
      (ZMod (invariantLevelDegree (r + 1)))) :
    factorialRestrictionHom K (Nat.le_succ r)
        (factorialCoherentGal K (r + 1) z) =
      factorialCoherentGal K r
        (CCarry.indexReduction
          (invariant_level_dvd (Nat.le_succ r)) z) := by
  exact Classical.choose_spec
    (compatible_factorial_gal K
      (Nat.le_succ r) (factorialCoherentGal K r)) z

/-- The recursively chosen cyclic identifications commute with restriction
and indexReduction for every pair of levels in the canonical factorial tower. -/
theorem factorial_coherent_gal
    {r s : ℕ} (hrs : r ≤ s)
    (z : Multiplicative (ZMod (invariantLevelDegree s))) :
    factorialRestrictionHom K hrs
        (factorialCoherentGal K s z) =
      factorialCoherentGal K r
        (CCarry.indexReduction
          (invariant_level_dvd hrs) z) := by
  induction s, hrs using Nat.le_induction with
  | base =>
      rw [factorial_restriction_refl,
        MonoidHom.id_apply, cyclic_carry_refl]
  | succ s hrs ih =>
      rw [factorial_restriction_trans K hrs (Nat.le_succ s),
        MonoidHom.comp_apply,
        coherent_gal_z K]
      rw [ih]
      apply congrArg (factorialCoherentGal K r)
      exact (cyclic_carry_trans hrs (Nat.le_succ s) z).symm

/-- Factorial-degree specialization of the explicit carry-class formula. -/
theorem factorial_mk_carry
    {r s : ℕ} (h : r ≤ s)
    {M : Type*} [CommGroup M]
    [MulDistribMulAction
      (Multiplicative (ZMod (invariantLevelDegree s))) M]
    (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod (invariantLevelDegree s)),
      g • pi = pi) :
    letI : NeZero (invariantLevelDegree r) :=
      ⟨(invariant_level_pos r).ne'⟩
    letI : NeZero (invariantLevelDegree s) :=
      ⟨(invariant_level_pos s).ne'⟩
    MHTwo.mk
        (CCarry.reductionFactorSet
          (invariant_level_dvd h) pi hpi) =
      MHTwo.mk (CCarry.factorSet pi hpi) ^
        (invariantLevelDegree s / invariantLevelDegree r) := by
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  letI : NeZero (invariantLevelDegree s) :=
    ⟨(invariant_level_pos s).ne'⟩
  exact CCarry.mk_set_carry
    (invariant_level_dvd h) pi hpi

end CanonicalFactorialTower

end

end Submission.CField.LBrauer
