import Submission.ClassField.ArtinReciprocity.NormLimitation
import Submission.ClassField.PrimeDensities.IsGaloisClosure
import Submission.ClassField.DirichletDensity.PolarLogBridge
import Submission.ClassField.DirichletDensity.ChebotarevDensityClauses
import Submission.ClassField.DirichletDensity.CongruenceClassQuotient

/-!
# Chapter VI, Section 4, Theorem 4.9: the second inequality
-/

namespace Submission.CField.DDensit

open IsDedekindDomain NumberField
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.PDensit
open Submission.NumberTheory.Milne

noncomputable section

universe u

/-- The algebraic ideal-norm step in Milne's proof: a completely split
prime is the norm of any prime above it and therefore belongs to the
ray-principal-times-norm subgroup.  The current prime-generator norm model
does not yet package this comparison as a theorem. -/
def SplittingRayBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K),
    IsGalois K L.carrier →
      splittingPrimes K L.carrier \ (m.finiteSupport :
        Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) ⊆
        idealsCongruenceSubgroup K m
          (extensionRaySubgroup L m)

/-- Removing finitely many primes does not change Dirichlet density. -/
theorem dirichlet_diff_finset
    (K : Type u) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (F : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (delta : ℝ) (hT : PrimeDirichletDensity K T delta) :
    PrimeDirichletDensity K (T \ (F : Set _)) delta := by
  let D : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    T ∩ (F : Set _)
  have hDfinite : D.Finite := F.finite_toSet.inter_of_right T
  have hDzero : PrimeDirichletDensity K D 0 :=
    chebotarev_density_clauses K D hDfinite
  have hdecomp : T = (T \ (F : Set _)) ∪ D := by
    ext p
    simp only [D, Set.mem_union, Set.mem_diff, Set.mem_inter_iff,
      Finset.mem_coe]
    tauto
  have hdisjoint : Disjoint (T \ (F : Set _)) D := by
    exact Set.disjoint_left.2 fun _ hp hq ↦ hp.2 hq.2
  have hdiff :=
    ((disjoint_union K T (T \ (F : Set _)) D delta delta 0
      hdecomp hdisjoint).2.2 ⟨hT, hDzero⟩)
  simpa using hdiff

/-- The nonvanishing conclusion established inside the density proof of
Theorem 4.9.  It is exposed separately because Corollary 4.10 applies it to
the character obtained by descending a ray-class character through the ray
norm subgroup. -/
theorem congruence_l_values
    (hSplitDensity : PolarDensityBridge.{u})
    (h41a : PolarImpliesDirichlet.{u})
    (h48 : CongruenceDensityFormula.{u})
    (hNorm : SplittingRayBridge.{u})
    (K : Type u) [Field K] [NumberField K]
    (L : NFExt K) (m : Modulus K)
    (hGalois : IsGalois K L.carrier) :
    LValuesNonzero K m
      (extensionRaySubgroup L m) := by
  letI : IsGalois K L.carrier := hGalois
  let H := extensionRaySubgroup L m
  let P : Prop := LValuesNonzero K m H
  letI : Decidable P := Classical.propDecidable P
  have hHray : rayPrincipalSubgroup K m ≤ H := by
    exact le_sup_left
  have hHdensity : PrimeDirichletDensity K
      (idealsCongruenceSubgroup K m H)
      (if P then (1 : ℝ) / H.index else 0) :=
    h48 K m H hHray
  have hsplitPolar : PrimePolarDensity K
      (splittingPrimes K L.carrier)
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    hSplitDensity K L.carrier
  have hsplitDirichlet : PrimeDirichletDensity K
      (splittingPrimes K L.carrier)
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    h41a K _ _ hsplitPolar
  have hsplitAwayDirichlet : PrimeDirichletDensity K
      (splittingPrimes K L.carrier \ (m.finiteSupport : Set _))
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    dirichlet_diff_finset K
      (splittingPrimes K L.carrier) m.finiteSupport _ hsplitDirichlet
  have hle : (1 / (Module.finrank K L.carrier : ℝ)) ≤
      (if P then (1 : ℝ) / H.index else 0) :=
    chebotarevClausesMonotone K _ _ _ _ (hNorm K L m hGalois)
      hsplitAwayDirichlet hHdensity
  have hdegreePos : 0 < (Module.finrank K L.carrier : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L.carrier))
  have hP : P := by
    by_contra hnP
    rw [if_neg hnP] at hle
    exact (not_lt_of_ge hle) (one_div_pos.mpr hdegreePos)
  exact hP

/-- The density proof of the second inequality.  Apart from the explicit
split-prime norm-membership bridge, every input is one of the source results
proved immediately before Theorem 4.9. -/
theorem second_inequality_density
    (hSplitDensity : PolarDensityBridge.{u})
    (h41a : PolarImpliesDirichlet.{u})
    (h48 : CongruenceDensityFormula.{u})
    (hfinite : CongruenceFinitenessBridge.{u})
    (hNorm : SplittingRayBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier) := by
  intro K _ _ L m hGalois
  letI : IsGalois K L.carrier := hGalois
  let H := extensionRaySubgroup L m
  let P : Prop := LValuesNonzero K m H
  letI : Decidable P := Classical.propDecidable P
  have hHray : rayPrincipalSubgroup K m ≤ H := by
    exact le_sup_left
  have hHdensity : PrimeDirichletDensity K
      (idealsCongruenceSubgroup K m H)
      (if P then (1 : ℝ) / H.index else 0) :=
    h48 K m H hHray
  have hsplitPolar : PrimePolarDensity K
      (splittingPrimes K L.carrier)
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    hSplitDensity K L.carrier
  have hsplitDirichlet : PrimeDirichletDensity K
      (splittingPrimes K L.carrier)
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    h41a K _ _ hsplitPolar
  have hsplitAwayDirichlet : PrimeDirichletDensity K
      (splittingPrimes K L.carrier \ (m.finiteSupport : Set _))
      (1 / (Module.finrank K L.carrier : ℝ)) :=
    dirichlet_diff_finset K
      (splittingPrimes K L.carrier) m.finiteSupport _ hsplitDirichlet
  have hle : (1 / (Module.finrank K L.carrier : ℝ)) ≤
      (if P then (1 : ℝ) / H.index else 0) :=
    chebotarevClausesMonotone K _ _ _ _ (hNorm K L m hGalois)
      hsplitAwayDirichlet hHdensity
  have hdegreePos : 0 < (Module.finrank K L.carrier : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L.carrier))
  have hP : P := by
    by_contra hnP
    rw [if_neg hnP] at hle
    exact (not_lt_of_ge hle) (one_div_pos.mpr hdegreePos)
  refine ⟨hfinite K m H le_sup_left, ?_⟩
  rw [if_pos hP] at hle
  have hindexCast : (H.index : ℝ) ≤ Module.finrank K L.carrier :=
    le_of_one_div_le_one_div hdegreePos hle
  exact_mod_cast hindexCast

end

end Submission.CField.DDensit
