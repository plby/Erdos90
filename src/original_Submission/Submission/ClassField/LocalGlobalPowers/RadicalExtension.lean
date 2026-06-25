import Submission.ClassField.LocalGlobalPowers.LocalRootSplitting
import Submission.ClassField.KummerTheory.KummerRadicalExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Chapter VIII, Section 1, Theorem 1.1: constructing the radical extension

We choose an `n`th root in an algebraic closure and take the subfield it
generates.  The one-generator Kummer theorems make this extension finite
Galois with abelian, hence solvable, Galois group.
-/

namespace Submission.CField.LGPowers

open IsDedekindDomain NumberField Polynomial
open Submission.NumberTheory.Milne
open Submission.CField.KTheory
open Submission.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The radical extension used in Theorem 1.1 exists without an additional
bridge assumption. -/
theorem radicalExtensionData
    (n : ℕ) (K : Type u) [Field K] [NumberField K] (a : Kˣ)
    (hroots : (primitiveRoots n K).Nonempty) :
    Nonempty (REData K n a) := by
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    simp [primitiveRoots_zero] at hroots
  let Ω := AlgebraicClosure K
  let q : K[X] := X ^ n - C (a : K)
  have hqdeg : (q.map (algebraMap K Ω)).degree ≠ 0 := by
    rw [degree_map, degree_X_pow_sub_C hn]
    simp [hn.ne']
  obtain ⟨alpha, halphaRoot⟩ :=
    IsAlgClosed.exists_root (q.map (algebraMap K Ω)) hqdeg
  have halpha : alpha ^ n = algebraMap K Ω (a : K) := by
    simpa [q, IsRoot, eval_map, sub_eq_zero] using halphaRoot
  let L : IntermediateField K Ω := IntermediateField.adjoin K {alpha}
  let beta : L :=
    ⟨alpha, IntermediateField.subset_adjoin K {alpha} (Set.mem_singleton alpha)⟩
  have hbeta : beta ^ n = algebraMap K L (a : K) := by
    apply Subtype.ext
    exact halpha
  have hfinite : FiniteDimensional K L := by
    apply dimensional_adjoin_pow n hn {alpha}
      (Set.finite_singleton alpha)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [IntermediateField.mem_bot]
    exact ⟨(a : K), halpha.symm⟩
  letI : FiniteDimensional K L := hfinite
  have hgen : IntermediateField.adjoin K {beta} = ⊤ := by
    apply IntermediateField.map_injective L.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    change IntermediateField.adjoin K (Subtype.val '' {beta}) = L
    rw [Set.image_singleton]
  have hpow : ∀ x ∈ ({beta} : Set L),
      x ^ n ∈ Set.range (algebraMap K L) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨(a : K), hbeta.symm⟩
  let zeta := hroots.choose
  have hzeta : IsPrimitiveRoot zeta n :=
    (mem_primitiveRoots hn).mp hroots.choose_spec
  have hgalois : IsGalois K L :=
    adjoin_nth_roots hn hzeta {beta} hgen hpow
  letI : IsGalois K L := hgalois
  have hsolvable : IsSolvable Gal(L/K) :=
    isSolvable_of_comm fun sigma tau ↦
      aut_commute_nth hn hzeta {beta} hgen hpow sigma tau
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  letI : NumberField L := {}
  exact ⟨
    { L := L
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := inferInstance
      finiteDimensionalKL := hfinite
      isGaloisKL := hgalois
      isSolvableGal := hsolvable
      root := beta
      root_pow := hbeta
      adjoin_root_top := hgen }⟩

/-- **Theorem VIII.1.1**, reduced only to the actual preceding
Proposition VII.4.6.  Both radical-extension bridges are discharged by the
concrete constructions in this and the preceding file. -/
theorem radicalExtensionStatement
    (h46 : NontrivialNonsplitPrimes.{u}) :
    ∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
    (primitiveRoots n K).Nonempty →
    ∀ (a : Kˣ),
      (∃ S : Finset (HeightOneSpectrum (OK K)),
        ∀ P, P ∉ S → ∃ x : P.adicCompletion K,
          x ^ n = algebraMap K (P.adicCompletion K) (a : K)) →
      a ∈ (powMonoidHom n : Kˣ →* Kˣ).range
  := by
  intro n K _ _ hroots a hplaces
  obtain ⟨S, hS⟩ := hplaces
  obtain ⟨data⟩ := radicalExtensionData n K a hroots
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  letI : IsSolvable Gal(data.L/K) := data.isSolvableGal
  have hsplitOutside : ∀ P : HeightOneSpectrum (OK K), P ∉ S →
      SplitsCompletelyAt K data.L P := by
    intro P hP
    apply splits_completely_completion K data.L P
    exact local_splits_completely n K a data P hroots (hS P hP)
  have hdegree : Module.finrank K data.L = 1 := by
    by_contra hne
    have hinfinite : (splittingPrimes K data.L)ᶜ.Infinite :=
      h46 K data.L hne
    apply hinfinite
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    exact hP (hsplitOutside P hPS)
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp [primitiveRoots_zero] at hroots
  have hroot0 : data.root ≠ 0 := by
    intro hzero
    apply a.ne_zero
    apply (algebraMap K data.L).injective
    simpa [hzero, zero_pow hn] using data.root_pow.symm
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (K := K) (1 : data.L) one_ne_zero).mp
      hdegree data.root
  have hc' : algebraMap K data.L c = data.root := by
    simpa [Algebra.smul_def] using hc
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hroot0
    rw [← hc', hzero, map_zero]
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  change c ^ n = (a : K)
  apply (algebraMap K data.L).injective
  rw [map_pow, hc', data.root_pow]

end

end Submission.CField.LGPowers
