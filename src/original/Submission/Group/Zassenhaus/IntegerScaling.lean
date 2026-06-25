import Submission.Group.Zassenhaus.HighWeightSources

/-!
# Integer scaling in high Hall weights

In a high-weight lower-central region, Hall-coordinate products commute.  The
existing power-collection layer uses this for natural scaling.  Retained
class-two correction factors have integer-valued symbolic exponents, so this
file records the corresponding integer-scaling statements.
-/

namespace Submission
namespace TCTex

universe u

open scoped IsMulCommutative

def zscaledExponentFamily
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (e : HEFam H)
    (z : ℤ) :
    HEFam H :=
  fun s i => e s i * z

lemma list_zpow_mul
    {G α : Type*}
    [Group G]
    [IsMulCommutative G]
    (g : α → G)
    (e : α → ℤ)
    (L : List α)
    (z : ℤ) :
    (L.map fun i => g i ^ (e i * z)).prod =
      (L.map fun i => g i ^ e i).prod ^ z := by
  induction L with
  | nil => simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      have hi : g i ^ (e i * z) = (g i ^ e i) ^ z := by
        rw [zpow_mul]
      calc
        g i ^ (e i * z) * (L.map fun j => g j ^ (e j * z)).prod =
            (g i ^ e i) ^ z * (L.map fun j => g j ^ e j).prod ^ z := by
              rw [ih, hi]
        _ = (g i ^ e i * (L.map fun j => g j ^ e j).prod) ^ z := by
              rw [mul_zpow]

lemma BCWta.collweigprod_zscahallexpo_famhighweight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s, s < inputWeight → e s = 0)
    (z : ℤ)
    (s : ℕ) :
    (H s).collectedWeightProduct (n := n) (zscaledExponentFamily e z s) =
      (H s).collectedWeightProduct (n := n) (e s) ^ z := by
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
      zscaledExponentFamily]
    exact congrArg Subtype.val
      (list_zpow_mul
        (fun i =>
          ((H s).commutator i).evalin_freelower_centtrunterm (n := n))
        (e s)
        (Finset.univ.sort fun i i' : (H s).index => i ≤ i')
        z)
  · have he : e s = 0 := heBelow s (Nat.lt_of_not_ge hs)
    have hscaled : zscaledExponentFamily e z s = 0 := by
      funext i
      simp [zscaledExponentFamily, he]
    simp [he, hscaled, BCWta.collected_weight_productzero]

lemma collected_zscaled_high
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s, s < inputWeight → e s = 0)
    (z : ℤ)
    (k : ℕ) :
    collectedPrefixProduct (n := n) H (zscaledExponentFamily e z) k =
      collectedPrefixProduct (n := n) H e k ^ z := by
  let S :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (inputWeight - 1)
  letI : IsMulCommutative S :=
    truncation_commutative_n
      hcutoff
  induction k with
  | zero => simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ, collected_prefix_succ, ih]
      rw [
        BCWta.collweigprod_zscahallexpo_famhighweight
          hcutoff e heBelow z]
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
      exact (hcommute.mul_zpow z).symm

lemma zscaled_exponent_high
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s, s < inputWeight → e s = 0)
    (z : ℤ) :
    collectedHallProduct (n := n) H (zscaledExponentFamily e z) =
      collectedHallProduct (n := n) H e ^ z := by
  exact collected_zscaled_high
    hcutoff e heBelow z (n - 1)

end TCTex
end Submission
