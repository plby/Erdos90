import Towers.NumberTheory.Galois.DedekindPermutationCycles


/-!
# Cycle partitions from a Dedekind factorization

A squarefree factorization of a reduction supplies all cycles of one
arithmetic Frobenius permutation, not just one selected cycle.
-/

namespace Towers.NumberTheory.Milne

open Equiv Finset Polynomial Set

noncomputable section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDomain S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  {p : Ideal R} {Q : Ideal S} [p.IsPrime] [Q.IsPrime]
  [p.IsMaximal] [Q.IsMaximal] [Q.LiesOver p]
  [Finite (R ⧸ p)] [Finite (S ⧸ Q)]
  [Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q)]

attribute [local instance] Ideal.Quotient.field

noncomputable local instance : Fintype (R ⧸ p) := Fintype.ofFinite (R ⧸ p)

set_option maxHeartbeats 2000000 in
-- The semilocal root-reduction instance search is substantially deeper than
-- Mathlib's default heartbeat allowance.
omit [IsDomain R] in
/-- A complete factorization of the reduction into distinct monic
irreducibles gives a partition of the integral roots into the corresponding
arithmetic-Frobenius cycles. -/
theorem arithmetic_cycle_partition
    {iota : Type*} [Fintype iota] [DecidableEq S]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (g : iota → (R ⧸ p)[X])
    (hfac : f.map (Ideal.Quotient.mk p) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g) :
    ∃ sigma : G, ∃ s : iota → Finset (f.rootSet S),
      IsArithFrobAt R sigma Q ∧
      (∀ i, (arithmeticRootPerm f sigma).IsCycleOn
        (s i : Set (f.rootSet S))) ∧
      (∀ i, (s i).card = (g i).natDegree) ∧
      (Finset.univ.biUnion s = Finset.univ) := by
  classical
  let red := f.map (Ideal.Quotient.mk p)
  have hredmonic : red.Monic := hf.map _
  have hsplitsRed :
      (red.map (algebraMap (R ⧸ p) (S ⧸ Q))).Splits := by
    have h := hsplits.map (Ideal.Quotient.mk Q)
    convert h using 1
    ext n
    simp only [red, Polynomial.coeff_map, Polynomial.coeff_map,
      Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hgdvd (i : iota) : g i ∣ red := by
    change g i ∣ f.map (Ideal.Quotient.mk p)
    rw [hfac]
    exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  have hgsplits (i : iota) :
      ((g i).map (algebraMap (R ⧸ p) (S ⧸ Q))).Splits :=
    hsplitsRed.of_dvd (map_ne_zero hredmonic.ne_zero)
      ((map_dvd_map' (algebraMap (R ⧸ p) (S ⧸ Q))).mpr (hgdvd i))
  obtain ⟨x, hx, hdisj⟩ :=
    pairwise_disjoint_cycles
      (R ⧸ p) (S ⧸ Q) g hirr hmonic hgsplits hinj
  have hxred (i : iota) : x i ∈ red.rootSet (S ⧸ Q) := by
    rw [hredmonic.mem_rootSet]
    have hroot : aeval (x i) (g i) = 0 :=
      (hmonic i).mem_rootSet.mp (hx i).1
    obtain ⟨q, hq⟩ := hgdvd i
    rw [hq, map_mul, hroot, zero_mul]
  let xr : iota → red.rootSet (S ⧸ Q) := fun i => ⟨x i, hxred i⟩
  let sigma : G := arithFrobAt R G Q
  have hsigma : IsArithFrobAt R sigma Q := IsArithFrobAt.arithFrobAt R G Q
  let s : iota → Finset (f.rootSet S) := fun i =>
    liftedFrobeniusCycle (p := p) (Q := Q)
      f hf hsplits hsep (xr i)
  have hcycle (i : iota) :
      (arithmeticRootPerm f sigma).IsCycleOn
        (s i : Set (f.rootSet S)) :=
    by
      change (arithmeticRootPerm f sigma).IsCycleOn
        (liftedFrobeniusCycle (p := p) (Q := Q)
          f hf hsplits hsep (xr i) : Set (f.rootSet S))
      exact arithmetic_cycle_lifted
        f hf hsplits hsep hsigma (xr i)
  have hcard (i : iota) : (s i).card = (g i).natDegree := by
    rw [card_lifted_cycle]
    exact (hx i).2.2
  have hsdisj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro y hyi hyj
    have hyi' : ((rootReductionEquiv (p := p) (Q := Q)
        f hf hsplits hsep y : red.rootSet (S ⧸ Q)) : S ⧸ Q) ∈
          frobeniusCycle (R ⧸ p) (S ⧸ Q) (x i) := by
      simpa [s, liftedFrobeniusCycle, xr] using hyi
    have hyj' : ((rootReductionEquiv (p := p) (Q := Q)
        f hf hsplits hsep y : red.rootSet (S ⧸ Q)) : S ⧸ Q) ∈
          frobeniusCycle (R ⧸ p) (S ⧸ Q) (x j) := by
      simpa [s, liftedFrobeniusCycle, xr] using hyj
    exact Set.disjoint_left.1 (hdisj hij) hyi' hyj'
  have hdegree : ∑ i, (g i).natDegree = red.natDegree := by
    change ∑ i, (g i).natDegree =
      (f.map (Ideal.Quotient.mk p)).natDegree
    rw [hfac, natDegree_prod_of_monic Finset.univ g]
    intro i _
    exact hmonic i
  have hrootcard : Fintype.card (f.rootSet S) = red.natDegree := by
    rw [Fintype.card_congr
      (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hsep)]
    exact card_rootSet_eq_natDegree hsep hsplitsRed
  have hcover : Finset.univ.biUnion s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => hcard i), hdegree]
      exact hrootcard.symm
    · intro i _ j _ hij
      exact hsdisj hij
  exact ⟨sigma, s, hsigma, hcycle, hcard, hcover⟩

end

end Towers.NumberTheory.Milne
