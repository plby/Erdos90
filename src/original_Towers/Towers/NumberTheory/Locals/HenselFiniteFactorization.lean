import Towers.NumberTheory.Locals.HenselFactorization
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Finite Hensel factorization

This file proves the finite-factor extension in Milne's Remark 7.36. A finite
pairwise-coprime factorization over the residue field of a complete local
domain lifts uniquely to a monic factorization over the ring.
-/

namespace Towers.NumberTheory.Milne

open Function IsLocalRing Polynomial

noncomputable section

private theorem hensel_finset_factorization
    {A ι : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (s : Finset ι) (f : A[X]) (hf : f.Monic)
    (g0 : ι → (ResidueField A)[X])
    (hg0 : ∀ i ∈ s, (g0 i).Monic)
    (hfactor0 : f.map (residue A) = ∏ i ∈ s, g0 i)
    (hcoprime0 : (s : Set ι).Pairwise (IsCoprime on g0)) :
    ∃ g : ι → A[X],
      (∀ i ∈ s, (g i).Monic) ∧
        f = ∏ i ∈ s, g i ∧
          ∀ i ∈ s, (g i).map (residue A) = g0 i := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      have hdegree : f.natDegree = 0 := by
        rw [← hf.natDegree_map (residue A), hfactor0]
        simp
      have hf_one : f = 1 := eq_one_of_monic_natDegree_zero hf hdegree
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · simp
      · simpa using hf_one
      · simp
  | @insert i s hi ih =>
      let h0 : (ResidueField A)[X] := ∏ j ∈ s, g0 j
      have hh0 : h0.Monic := by
        apply monic_prod_of_monic
        intro j hj
        exact hg0 j (Finset.mem_insert_of_mem hj)
      have hcoprime_i : IsCoprime (g0 i) h0 := by
        apply IsCoprime.prod_right
        intro j hj
        exact hcoprime0 (by simp) (by simp [hj])
          (ne_of_mem_of_not_mem hj hi).symm
      have hfactor_insert : f.map (residue A) = g0 i * h0 := by
        simpa [h0, Finset.prod_insert hi] using hfactor0
      obtain ⟨gi, h, hgi, hh, hfh, hgimap, hhmap, _⟩ :=
        adic_hensel_factorization
          f hf (g0 i) h0 (hg0 i (Finset.mem_insert_self i s)) hh0
            hfactor_insert hcoprime_i
      have hcoprime_s : (s : Set ι).Pairwise (IsCoprime on g0) := by
        exact hcoprime0.mono (by
          intro j hj
          exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hj)))
      obtain ⟨g, hg, hprod, hgmap⟩ :=
        ih h hh (fun j hj => hg0 j (Finset.mem_insert_of_mem hj)) hhmap hcoprime_s
      let G : ι → A[X] := Function.update g i gi
      refine ⟨G, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [G] using hgi
        · have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
          simpa [G, Function.update_of_ne hji] using hg j hj
      · calc
          f = gi * h := hfh
          _ = gi * ∏ j ∈ s, g j := by rw [hprod]
          _ = ∏ j ∈ insert i s, G j := by
            rw [Finset.prod_insert hi]
            simp only [G, Function.update_self]
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            exact (Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [G] using hgimap
        · have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
          simpa [G, Function.update_of_ne hji] using hgmap j hj

/-- Milne, Remark 7.36: a finite pairwise-coprime monic factorization over
the residue field lifts uniquely to a pairwise-coprime monic factorization
over a local domain complete for its maximal-ideal-adic topology. -/
theorem complete_hensel_unique
    {A ι : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Fintype ι]
    (f : A[X]) (hf : f.Monic)
    (g0 : ι → (ResidueField A)[X])
    (hg0 : ∀ i, (g0 i).Monic)
    (hfactor0 : f.map (residue A) = ∏ i, g0 i)
    (hcoprime0 : Pairwise (IsCoprime on g0)) :
    ∃! g : ι → A[X],
      (∀ i, (g i).Monic) ∧
        f = ∏ i, g i ∧
          (∀ i, (g i).map (residue A) = g0 i) ∧
            Pairwise (IsCoprime on g) := by
  classical
  obtain ⟨g, hg, hprod, hgmap⟩ :=
    hensel_finset_factorization
      Finset.univ f hf g0 (fun i _ => hg0 i) (by simpa using hfactor0)
        (hcoprime0.set_pairwise _)
  have hg_coprime : Pairwise (IsCoprime on g) := by
    intro i j hij
    apply coprime_monic_residue (hg i (by simp)) (hg j (by simp))
    simpa [hgmap i (by simp), hgmap j (by simp)] using hcoprime0 hij
  refine ⟨g, ⟨fun i => hg i (by simp), by simpa using hprod,
    fun i => hgmap i (by simp), hg_coprime⟩, ?_⟩
  intro g' hg'
  rcases hg' with ⟨hg'monic, hg'prod, hg'map, _⟩
  funext i
  let rest : (ι → A[X]) → A[X] := fun q => ∏ j ∈ Finset.univ.erase i, q j
  have hrest_monic : (rest g).Monic := by
    apply monic_prod_of_monic
    intro j hj
    exact hg j (by simp)
  have hrest'_monic : (rest g').Monic := by
    apply monic_prod_of_monic
    intro j hj
    exact hg'monic j
  have hfactor : g i * rest g = g' i * rest g' := by
    calc
      g i * rest g = ∏ j, g j := Finset.mul_prod_erase Finset.univ g (by simp)
      _ = f := hprod.symm
      _ = ∏ j, g' j := hg'prod
      _ = g' i * rest g' := (Finset.mul_prod_erase Finset.univ g' (by simp)).symm
  have hmap_rest : (rest g).map (residue A) = (rest g').map (residue A) := by
    simp only [rest, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hgmap j (by simp), hg'map j]
  have hcoprime_rest :
      IsCoprime ((g i).map (residue A)) ((rest g).map (residue A)) := by
    rw [hgmap i (by simp)]
    simp only [rest, Polynomial.map_prod]
    apply IsCoprime.prod_right
    intro j hj
    rw [hgmap j (by simp)]
    exact hcoprime0 (Finset.mem_erase.mp hj).1.symm
  exact (monic_unique_residue
    (hg i (by simp)) hrest_monic (hg'monic i) hrest'_monic hfactor
    ((hgmap i (by simp)).trans (hg'map i).symm) hmap_rest hcoprime_rest).1.symm

end

end Towers.NumberTheory.Milne
