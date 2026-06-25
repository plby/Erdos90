import Submission.ClassField.LocalClass.CanonicalClassReduction
import Submission.ClassField.LocalClass.TotallyCarrySplitting

/-!
# Lemma III.2.2 for totally ramified extensions

The direct carry calculation shows that the canonical invariant-`1/n`
Brauer class is relative to every totally ramified degree-`n` extension.
-/

namespace Submission.CField.LClass

noncomputable section

open ValuativeRel
open Submission.NumberTheory.Milne
open BGroups LBrauer

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [FiniteDimensional K L]
  [Algebra 𝒪[K] 𝒪[L]] [Module.Finite 𝒪[K] 𝒪[L]]
  [Module.IsTorsionFree 𝒪[K] 𝒪[L]]
  [IsScalarTower 𝒪[K] K L] [IsScalarTower 𝒪[K] 𝒪[L] L]

/-- The canonical degree class is split by a totally ramified extension of
the matching degree. -/
theorem relative_totally_ramified
    (n : ℕ) [NeZero n]
    (hdegree : Module.finrank K L = n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[L]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    canonicalBrauerClass K n ∈ relativeBrauerGroup K L := by
  obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hclass, hDdim⟩ :=
    division_brauer_class K n
  letI : DivisionRing D := hDdiv
  letI : Algebra K D := hDalg
  letI : Algebra.IsCentral K D := hDcentral
  letI : Module.Finite K D := hDfinite
  have hsqrt : Nat.sqrt (Module.finrank K D) = n := by
    rw [hDdim]
    simp
  have hsplit : ISBy K L D :=
    split_totally_ramified K L D
      (hdegree.trans hsqrt.symm) htotal
  rw [← hclass]
  exact (brauer_relative_split
    K L (centralDivisionCSA K D)).2 hsplit

/-- Hence the full `n`-torsion invariant subgroup injects into the relative
Brauer group in the totally ramified case. -/
noncomputable def torsionTotallyRamified
    (n : ℕ) [NeZero n]
    (hdegree : Module.finrank K L = n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[L]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    invariantPowTorsion n →* relativeBrauerGroup K L :=
  torsionBrauerCanonical K L n
    (relative_totally_ramified
      K L n hdegree htotal)

theorem totally_ramified_injective
    (n : ℕ) [NeZero n]
    (hdegree : Module.finrank K L = n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[L]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    Function.Injective
      (torsionTotallyRamified
        K L n hdegree htotal) :=
  torsion_relative_injective K L n _

end

end Submission.CField.LClass
