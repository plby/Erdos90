import Towers.Group.Zassenhaus.ScaledSources

/-!
# High-weight scaled sources for symbolic Hall powers

If the initial nonzero Hall weight is `r` and `n ≤ 2 * r`, every commutator
between surviving input factors vanishes in `F / gamma_n(F)`.  Thus the
coordinatewise-scaled atomic endpoint is already the power of the entire
collected Hall block.  This file constructs the resulting symbolic run and
the Claim 5 data in that terminal region.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped IsMulCommutative

/--
Inside `F / gamma_n(F)`, the lower-central term `gamma_r` is commutative as
soon as `n ≤ 2 * r`.
-/
@[reducible] def truncation_commutative_n
    {d n r : ℕ}
    (hcutoff : n ≤ 2 * r) :
    IsMulCommutative
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (r - 1)) := by
  exact
    ⟨⟨fun x y => by
      apply Subtype.ext
      apply commutatorElement_eq_one_iff_mul_comm.mp
      apply eq_bot_iff.mp
        SPFactora.trunc_last_bot
      exact Subgroup.lowerCentralSeries_antitone (by omega)
        (element_lower_series x.property y.property)⟩⟩

/--
Exponent scaling distributes over a finite product whose factors belong to a
chosen commutative subgroup.
-/
lemma zpow_cast_pow
    {G α : Type*}
    [Group G]
    (S : Subgroup G)
    [IsMulCommutative S]
    (g : α → G)
    (hg : ∀ i, g i ∈ S)
    (e : α → ℤ)
    (L : List α)
    (q : ℕ) :
    (L.map fun i => g i ^ (e i * (q : ℤ))).prod =
      (L.map fun i => g i ^ e i).prod ^ q := by
  simpa using congrArg Subtype.val
    (zpow_nat_cast
      (fun i => (⟨g i, hg i⟩ : S)) e L q)

/--
If coordinates vanish below `inputWeight`, every fixed Hall-weight segment
belongs to `gamma_inputWeight`.
-/
lemma BCWta.collec_produ_lowec
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (s : ℕ) :
    (H s).collectedWeightProduct (n := n) (e s) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inputWeight - 1) := by
  by_cases hs : inputWeight ≤ s
  · exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hs 1)
      ((H s).collectedweight_productmem_lowecentseri (n := n) (e s))
  · rw [heBelow s (Nat.lt_of_not_ge hs),
      BCWta.collected_weight_productzero]
    exact Subgroup.one_mem _

/--
If coordinates vanish below `inputWeight`, every collected prefix belongs to
`gamma_inputWeight`.
-/
lemma collected_initial_series
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (k : ℕ) :
    collectedPrefixProduct (n := n) H e k ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inputWeight - 1) := by
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ]
      exact Subgroup.mul_mem _ ih
        (BCWta.collec_produ_lowec
          e heBelow (k + 1))

/--
At high initial weight, coordinatewise exponent scaling distributes over one
fixed Hall-weight layer.
-/
lemma BCWta.collweigprod_scalhallexpo_famhighweight
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q s : ℕ) :
    (H s).collectedWeightProduct (n := n) (scaledExponentFamily e q s) =
      (H s).collectedWeightProduct (n := n) (e s) ^ q := by
  by_cases hs : inputWeight ≤ s
  · letI :
        IsMulCommutative
          (Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (s - 1)) :=
      truncation_commutative_n
        (by omega)
    simp only [BCWta.collectedWeightProduct,
      BCWta.collected_lower_centralterm,
      BCWt.evalin_freelower_centtrunterm,
      scaledExponentFamily]
    exact congrArg Subtype.val
      (zpow_nat_cast
      (fun i =>
        ((H s).commutator i).evalin_freelower_centtrunterm (n := n))
      (e s) (Finset.univ.sort fun i i' : (H s).index => i ≤ i') q)
  · have he : e s = 0 := heBelow s (Nat.lt_of_not_ge hs)
    have hscaled : scaledExponentFamily e q s = 0 := by
      funext i
      simp [scaledExponentFamily, he]
    simp [he, hscaled,
      BCWta.collected_weight_productzero]

/--
At high initial weight, coordinatewise exponent scaling distributes over every
collected Hall prefix.
-/
lemma collected_scaled_high
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q k : ℕ) :
    collectedPrefixProduct (n := n) H (scaledExponentFamily e q) k =
      collectedPrefixProduct (n := n) H e k ^ q := by
  let S :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (inputWeight - 1)
  letI : IsMulCommutative S :=
    truncation_commutative_n
      hcutoff
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ, collected_prefix_succ, ih,
        BCWta.collweigprod_scalhallexpo_famhighweight
          hcutoff e heBelow]
      have hprefix :
          collectedPrefixProduct (n := n) H e k ∈ S :=
        collected_initial_series e heBelow k
      have hsegment :
          (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) ∈ S :=
        BCWta.collec_produ_lowec
          e heBelow (k + 1)
      have hcommute :
          Commute
            (collectedPrefixProduct (n := n) H e k)
            ((H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))) := by
        exact congrArg Subtype.val
          (mul_comm
            (⟨collectedPrefixProduct (n := n) H e k, hprefix⟩ : S)
            (⟨(H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)),
              hsegment⟩ : S))
      exact (hcommute.mul_pow q).symm

/--
At high initial weight, coordinatewise scaling is the power of the whole
collected Hall block.
-/
lemma scaled_exponent_high
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    collectedHallProduct (n := n) H (scaledExponentFamily e q) =
      collectedHallProduct (n := n) H e ^ q :=
  collected_scaled_high
    hcutoff e heBelow q (n - 1)

namespace TCRun

/--
When `n ≤ 2 * inputWeight`, the normalized scaled atomic endpoint is already a
complete symbolic repeated-power run.
-/
noncomputable def of_highWeight
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e :=
  scaled_hall_coordinates e heBelow
    (scaled_exponent_high
      hcutoff e heBelow)

end TCRun

/-- Claim 5 explicit expansion data is fully constructed in the high-weight region. -/
theorem collected_expansion_high
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hcutoff : n ≤ 2 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CEData (n := n) H e inputWeight :=
  (TCRun.of_highWeight
    hcutoff e heBelow).coordinateExpansionData

/-- Claim 5 polynomial data is fully constructed in the high-weight region. -/
theorem collected_high_weight
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 2 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  (TCRun.of_highWeight
    hcutoff e heBelow).coordinatePolynomialData hinputWeight

end TCTex
end Towers
