import Submission.NumberTheory.Galois.GaloisOrbitFactorization

/-!
# Milne, Chapter 8, Corollary 8.22: the full factor-cycle partition

For a polynomial over a finite field, a factorization into distinct monic
irreducibles indexes all cycles of arithmetic Frobenius on its roots.  The
cycles are pairwise disjoint, cover the root set, and their lengths are the
degrees of the corresponding factors.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

noncomputable section

variable (k l : Type*) [Field k] [Field l] [Fintype k] [Finite l]
  [Algebra k l]

/-- The complete finite-field factor-cycle correspondence in the explicitly
indexed form used by Dedekind's theorem. -/
theorem cycles_partition_set
    {ι : Type*} [Fintype ι]
    (f : k[X]) (g : ι → k[X])
    (hfactor : f = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hsplits : ∀ i, ((g i).map (algebraMap k l)).Splits)
    (hinj : Function.Injective g) :
    ∃ x : ι → l,
      (∀ i, x i ∈ (g i).rootSet l ∧ minpoly k (x i) = g i ∧
        Set.ncard (frobeniusCycle k l (x i)) = (g i).natDegree) ∧
      (Pairwise fun i j => Disjoint
        (frobeniusCycle k l (x i)) (frobeniusCycle k l (x j))) ∧
      f.rootSet l = ⋃ i, frobeniusCycle k l (x i) := by
  classical
  have hfmonic : f.Monic := by
    rw [hfactor]
    exact monic_prod_of_monic Finset.univ g fun i _ => hmonic i
  obtain ⟨x, hx, hdisj⟩ :=
    pairwise_disjoint_cycles k l g
      hirr hmonic hsplits hinj
  refine ⟨x, hx, hdisj, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    have hyzero : ∏ i, aeval y (g i) = 0 := by
      have := (mem_rootSet.mp hy).2
      simpa only [hfactor, map_prod] using this
    rw [Finset.prod_eq_zero_iff] at hyzero
    obtain ⟨i, -, hi⟩ := hyzero
    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    apply (same_irreducible_cycle k l (x i) y).mp
    rw [(hx i).2.1]
    exact minpoly.eq_of_irreducible_of_monic (hirr i) hi (hmonic i)
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hyi⟩ := hy
    have hyfactor : y ∈ (g i).rootSet l :=
      frobenius_cycle_set (k := k) (l := l) (hx i).1 hyi
    rw [hfmonic.mem_rootSet, hfactor, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      ((hmonic i).mem_rootSet.mp hyfactor)

end

end Submission.NumberTheory.Milne
