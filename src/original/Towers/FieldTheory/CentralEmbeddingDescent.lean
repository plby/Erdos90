import Towers.ClassField.CohomologyOps.RestrictionCompatibility
import Towers.FieldTheory.CentralFactorSet

/-!
# Coprime descent for central embedding obstructions

This file supplies the finite-group descent step used after adjoining a
primitive cube root of unity.  Restriction to an index-two subgroup detects a
central obstruction with cubic coefficients because restriction followed by
corestriction is multiplication by two.
-/

noncomputable section

namespace Towers
namespace TBluepr

open CategoryTheory Representation
open Towers.CField.COps
open Towers.CField.CProduca

/-- The multiplicative identity represents the zero ordinary cohomology
class. -/
theorem MHTwo.group_cohomology_one
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    MHTwo.toGroupCohomology (1 : MHTwo G M) = 0 :=
  (MHTwo.group_cohomology_zero 1).2 rfl

/-- The comparison from normalized multiplicative `H²` to ordinary group
cohomology carries products to sums. -/
theorem MHTwo.group_cohomology_mul
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (x y : MHTwo G M) :
    MHTwo.toGroupCohomology (x * y) =
      MHTwo.toGroupCohomology x +
        MHTwo.toGroupCohomology y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      change groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
          (groupCohomology.cocyclesOfIsMulCocycle₂
            (NMCocycl₂.isMulCocycle₂ (c * d))) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
            (groupCohomology.cocyclesOfIsMulCocycle₂ c.isMulCocycle₂) +
          groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
            (groupCohomology.cocyclesOfIsMulCocycle₂ d.isMulCocycle₂)
      rw [← map_add]
      congr 1

/-- Consequently, powers of a multiplicative class correspond to natural
multiples of its ordinary cohomology class. -/
theorem MHTwo.group_cohomology_pow
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (x : MHTwo G M) (n : ℕ) :
    MHTwo.toGroupCohomology (x ^ n) =
      n • MHTwo.toGroupCohomology x := by
  induction n with
  | zero =>
      simpa using
        (MHTwo.group_cohomology_one (G := G) (M := M))
  | succ n ih =>
      rw [pow_succ, MHTwo.group_cohomology_mul, ih, succ_nsmul]

/-- A coefficient group of exponent `n` gives multiplicative `H²` exponent
dividing `n`. -/
theorem MHTwo.poweq_onecoeffs_poweqone
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (n : ℕ) (hM : ∀ m : M, m ^ n = 1)
    (x : MHTwo G M) :
    x ^ n = 1 := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change MHTwo.mk c ^ n =
        MHTwo.mk (1 : NMCocycl₂ (G := G) (M := M))
      rw [← MHTwo.mk_pow]
      apply congrArg MHTwo.mk
      ext p
      simpa only [NMCocycl₂.pow_apply,
        NMCocycl₂.one_apply] using hM (c p)

/-- Restricting a normalized multiplicative class to a subgroup agrees with
ordinary group-cohomology restriction after applying the comparison map. -/
theorem MHTwo.group_cohomology_restricsubgrou
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (H : Subgroup G) (x : MHTwo G M) :
    letI : MulDistribMulAction H M :=
      (inferInstance : MulDistribMulAction G M).compHom M H.subtype
    MHTwo.toGroupCohomology
        (MHTwo.restrictionHom H.subtype (fun _ _ => rfl) x) =
      restriction (Rep.ofMulDistribMulAction G M) H 2
        (MHTwo.toGroupCohomology x) := by
  letI : MulDistribMulAction H M :=
    (inferInstance : MulDistribMulAction G M).compHom M H.subtype
  induction x using Quotient.inductionOn with
  | _ c =>
      change groupCohomology.H2π (Rep.ofMulDistribMulAction H M) _ =
        groupCohomology.map H.subtype (𝟙 _) 2
          (groupCohomology.H2π (Rep.ofMulDistribMulAction G M) _)
      rw [groupCohomology.H2π_comp_map_apply]
      congr 1

/-- If a multiplicative class has exponent dividing `n`, and its restriction
to a finite-index subgroup is trivial with index coprime to `n`, then the
class itself is trivial. -/
theorem MHTwo.eqone_restricteq_onecoprimeindex
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) (hcoprime : Nat.Coprime H.index n)
    (hM : ∀ m : M, m ^ n = 1)
    (x : MHTwo G M)
    (hxH :
      letI : MulDistribMulAction H M :=
        (inferInstance : MulDistribMulAction G M).compHom M H.subtype
      MHTwo.restrictionHom H.subtype (fun _ _ => rfl) x = 1) :
    x = 1 := by
  letI : MulDistribMulAction H M :=
    (inferInstance : MulDistribMulAction G M).compHom M H.subtype
  let y := MHTwo.toGroupCohomology x
  have hyH : restriction (Rep.ofMulDistribMulAction G M) H 2 y = 0 := by
    rw [← MHTwo.group_cohomology_restricsubgrou H x, hxH]
    exact MHTwo.group_cohomology_one
  have hindex : H.index • y = 0 := by
    have htransfer := shapiro_restriction_corestriction
      (Rep.ofMulDistribMulAction G M) H 2
    rw [← restriction_shapiro] at htransfer
    have happ := congrArg (fun f => f y) htransfer
    simpa [hyH] using happ.symm
  have hn : n • y = 0 := by
    rw [← MHTwo.group_cohomology_pow]
    rw [MHTwo.poweq_onecoeffs_poweqone n hM x]
    exact MHTwo.group_cohomology_one
  have hindexZ : (H.index : ℤ) • y = 0 := by
    simpa using hindex
  have hnZ : (n : ℤ) • y = 0 := by
    simpa using hn
  let a : ℤ := Nat.gcdA H.index n
  let b : ℤ := Nat.gcdB H.index n
  have hy : y = 0 := by
    have hbezout : (a : ℤ) * H.index + (b : ℤ) * n = 1 := by
      dsimp [a, b]
      rw [mul_comm (Nat.gcdA H.index n), mul_comm (Nat.gcdB H.index n),
        ← Nat.gcd_eq_gcd_ab, hcoprime.gcd_eq_one]
      norm_num
    calc
      y = (1 : ℤ) • y := (one_zsmul _).symm
      _ = ((a : ℤ) * H.index + (b : ℤ) * n) • y := by rw [hbezout]
      _ = (a : ℤ) • ((H.index : ℤ) • y) +
          (b : ℤ) • ((n : ℤ) • y) := by
        rw [add_zsmul, mul_smul, mul_smul]
      _ = 0 := by rw [hindexZ, hnZ]; simp only [zsmul_zero, add_zero]
  exact (MHTwo.group_cohomology_zero x).mp hy

/-- A central extension with `n`-torsion kernel splits if it admits a lift on
a finite-index subgroup whose index is coprime to `n`. -/
theorem splits_coprime_lift
    {E G : Type} [Group E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) (hcoprime : Nat.Coprime H.index n)
    (hkernel : ∀ z : q.ker, z ^ n = 1)
    (lift : H →* E) (hlift : q.comp lift = H.subtype) :
    ∃ splitting : G →* E, q.comp splitting = MonoidHom.id G := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker :=
    (inferInstance : MulDistribMulAction G q.ker).compHom q.ker H.subtype
  let obstruction : MHTwo G q.ker :=
    extensionObstructionClass q hq hcentral
  have hrestricted :
      MHTwo.restrictionHom H.subtype (fun _ _ => rfl)
          obstruction = 1 :=
    obstruction_restrict_lift
      q hq hcentral H.subtype lift hlift
  have hobstruction : obstruction = 1 :=
    MHTwo.eqone_restricteq_onecoprimeindex
      H n hcoprime hkernel obstruction hrestricted
  exact (splits_set_trivial q hq hcentral).2
    ((set_trivial_obstruction
      q hq hcentral).2 hobstruction)

/-- A lift of a homomorphism on a finite-index subgroup descends when the
index is coprime to the exponent of the central kernel. -/
theorem extension_lift_coprime
    {E G Γ : Type} [Group E] [Group G] [Group Γ]
    (q : E →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center E)
    (f : Γ →* G)
    (H : Subgroup Γ) [H.FiniteIndex]
    (n : ℕ) (hcoprime : Nat.Coprime H.index n)
    (hkernel : ∀ z : q.ker, z ^ n = 1)
    (lift : H →* E)
    (hlift : q.comp lift = f.comp H.subtype) :
    ∃ t : Γ →* E, q.comp t = f := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Γ q.ker :=
    trivialDistribAction Γ q.ker
  letI : MulDistribMulAction H q.ker :=
    (inferInstance : MulDistribMulAction Γ q.ker).compHom q.ker H.subtype
  let obstruction : MHTwo G q.ker :=
    extensionObstructionClass q hq hcentral
  let restricted : MHTwo Γ q.ker :=
    MHTwo.restrictionHom f (fun _ _ => rfl) obstruction
  have hrestrictedH :
      MHTwo.restrictionHom H.subtype (fun _ _ => rfl)
          restricted = 1 := by
    rw [MHTwo.restrictionHom_comp
      (f := f) (g := H.subtype)
      (hf := fun _ _ => rfl) (hg := fun _ _ => rfl)
      (hfg := fun _ _ => rfl)]
    exact obstruction_restrict_lift
      q hq hcentral (f.comp H.subtype) lift hlift
  have hrestricted : restricted = 1 :=
    MHTwo.eqone_restricteq_onecoprimeindex
      H n hcoprime hkernel restricted hrestrictedH
  exact lift_obstruction_restrict
    q hq hcentral f hrestricted

end TBluepr
end Towers
