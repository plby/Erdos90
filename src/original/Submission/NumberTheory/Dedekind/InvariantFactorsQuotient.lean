import Submission.NumberTheory.Dedekind.InvariantFactorsLocal
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Milne, Algebraic Number Theory, invariant factors through the quotient

The invariant-factor proof may be organized by first decomposing the torsion quotient and then
lifting cyclic generators to the ambient torsion-free module.  This file records the PID quotient
decomposition and the generator-lifting step.  The remaining global Dedekind-domain argument is
the patching of the local cyclic factors into a nested family of integral ideals.
-/

namespace Submission.NumberTheory.Milne

open Module

universe u v

/-- The quotient form of the same-rank diagonal-basis theorem over a PID: a full-rank quotient is
a finite product of cyclic modules, with nonzero defining elements. -/
theorem pid_same_pi
    (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (n : ℕ) (a : Fin n → R),
      (∀ i, a i ≠ 0) ∧
        Nonempty ((M ⧸ N) ≃ₗ[R]
          ∀ i, R ⧸ Ideal.span ({a i} : Set R)) := by
  let ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  let a : Fin n → R := N.smithNormalFormCoeffs b h
  refine ⟨n, a, ?_, ⟨N.quotientEquivPiSpan b h⟩⟩
  intro i
  exact N.smithNormalFormCoeffs_ne_zero b h i

/-- A finite product of quotient rings is generated, as an `R`-module, by its coordinate copies
of `1`.  This is the elementary fact needed to lift cyclic quotient generators. -/
theorem pi_single_top
    (R : Type u) [CommRing R]
    (ι : Type v) [Finite ι] [DecidableEq ι]
    (I : ι → Ideal R) :
    Submodule.span R
        (Set.range fun i : ι ↦
          Pi.single i (Ideal.Quotient.mk (I i) 1) :
            Set (∀ i, R ⧸ I i)) = ⊤ := by
  letI := Fintype.ofFinite ι
  rw [eq_top_iff]
  intro x _
  choose r hr using fun i ↦ Ideal.Quotient.mk_surjective (x i)
  have hx : x = ∑ i, r i •
      (Pi.single i (Ideal.Quotient.mk (I i) 1) :
        ∀ i, R ⧸ I i) := by
    ext j
    rw [← hr j]
    rw [Finset.sum_apply]
    rw [Fintype.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same]
      change Ideal.Quotient.mk (I j) (r j) =
        Ideal.Quotient.mk (I j) (r j * 1)
      rw [mul_one]
    · intro i hij
      simp [hij]
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

/-- Coordinate generators of a cyclic decomposition of `M/N` can be lifted to elements of `M`.
Their images generate the whole quotient. -/
theorem lifts_quotient_pi
    (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M]
    (ι : Type u) [Finite ι] [DecidableEq ι]
    (N : Submodule R M) (I : ι → Ideal R)
    (q : (M ⧸ N) ≃ₗ[R] ∀ i, R ⧸ I i) :
    ∃ e : ι → M,
      (∀ i, q (Submodule.Quotient.mk (e i)) =
        Pi.single i (Ideal.Quotient.mk (I i) 1)) ∧
      Submodule.map N.mkQ (Submodule.span R (Set.range e)) = ⊤ := by
  have hsurj : ∀ i : ι, ∃ x : M,
      q (Submodule.Quotient.mk x) =
        Pi.single i (Ideal.Quotient.mk (I i) 1) := by
    intro i
    obtain ⟨x, hx⟩ := N.mkQ_surjective
      (q.symm (Pi.single i (Ideal.Quotient.mk (I i) 1)))
    refine ⟨x, ?_⟩
    change q (N.mkQ x) = _
    rw [hx, q.apply_symm_apply]
  choose e he using hsurj
  refine ⟨e, he, ?_⟩
  let S := Submodule.map N.mkQ (Submodule.span R (Set.range e))
  have hset :
      (fun x ↦ q (N.mkQ x)) '' Set.range e =
        Set.range (fun i : ι ↦ Pi.single i (Ideal.Quotient.mk (I i) 1)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (he i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, ⟨i, rfl⟩, he i⟩
  have hmap : Submodule.map q.toLinearMap S = ⊤ := by
    dsimp [S]
    rw [Submodule.map_span, Submodule.map_span, Set.image_image]
    change Submodule.span R ((fun x ↦ q (N.mkQ x)) '' Set.range e) = ⊤
    rw [hset, pi_single_top]
  rw [eq_top_iff]
  intro x _
  have hx : q x ∈ Submodule.map q.toLinearMap S := by
    rw [hmap]
    exact Submodule.mem_top
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
  rwa [q.injective hxy] at hy

end Submission.NumberTheory.Milne
