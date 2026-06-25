import Submission.ClassField.KummerNormIndex.NthPowerPlace
import Submission.ClassField.KummerTheory.KummerFiniteDegree
import Submission.ClassField.KummerTheory.KummerRadicalExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The radical extension in Proposition VII.6.10

We choose an `n`th root in an algebraic closure and take the subfield it
generates.  Since the base contains a primitive `n`th root of unity, this
simple radical extension is finite Galois with abelian, hence solvable,
Galois group.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField Polynomial
open Submission.CField.KTheory

noncomputable section

universe u

/-- The concrete Kummer extension required in Proposition VII.6.10. -/
theorem kummerExtensionBridge :
    KummerExtensionBridge.{u} := by
  intro n K _ _ b hroots
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    simp [primitiveRoots_zero] at hroots
  let Ω := AlgebraicClosure K
  let q : K[X] := X ^ n - C (b : K)
  have hqdeg : (q.map (algebraMap K Ω)).degree ≠ 0 := by
    rw [degree_map, degree_X_pow_sub_C hn]
    simp [hn.ne']
  obtain ⟨alpha, halphaRoot⟩ :=
    IsAlgClosed.exists_root (q.map (algebraMap K Ω)) hqdeg
  have halpha : alpha ^ n = algebraMap K Ω (b : K) := by
    simpa [q, IsRoot, eval_map, sub_eq_zero] using halphaRoot
  let L : IntermediateField K Ω := IntermediateField.adjoin K {alpha}
  let beta : L :=
    ⟨alpha, IntermediateField.subset_adjoin K {alpha}
      (Set.mem_singleton alpha)⟩
  have hbeta : beta ^ n = algebraMap K L (b : K) := by
    apply Subtype.ext
    exact halpha
  have hfinite : FiniteDimensional K L := by
    apply dimensional_adjoin_pow n hn {alpha}
      (Set.finite_singleton alpha)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [IntermediateField.mem_bot]
    exact ⟨(b : K), halpha.symm⟩
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
    exact ⟨(b : K), hbeta.symm⟩
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

end

end Submission.CField.KNIndex
