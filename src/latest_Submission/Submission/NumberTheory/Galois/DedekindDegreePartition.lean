import Submission.NumberTheory.Galois.DedekindCyclePartition


/-!
# Factor degrees as the full Frobenius cycle partition

This file assembles the cycle-by-cycle form of Dedekind's theorem into the
usual partition statement.  We use `Equiv.Perm.partition` rather than
`Equiv.Perm.cycleType`: the former includes singleton fixed-point cycles,
which correspond to linear factors of the reduced polynomial.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset Polynomial Set

noncomputable section

section PermutationPartition

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

private theorem support_cycle
    (sigma : Equiv.Perm α) (s : Finset α) (hs : s.Nontrivial)
    (hcycle : sigma.IsCycleOn (s : Set α)) (x : α) (hx : x ∈ s) :
    (sigma.cycleOf x).support = s := by
  have hxmove : sigma x ≠ x := hcycle.apply_ne hs hx
  ext y
  rw [Equiv.Perm.mem_support_cycleOf_iff' hxmove]
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy
    have hrange := hcycle.range_zpow hx
    have : y ∈ (s : Set α) := by
      rw [← hrange]
      exact ⟨n, hn⟩
    exact this
  · intro hy
    exact hcycle.2 hx hy

private theorem cycle_type_cards
    (sigma : Equiv.Perm α) (s : ι → Finset α)
    (hne : ∀ i, (s i).Nonempty)
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    (hcycle : ∀ i, sigma.IsCycleOn (s i : Set α))
    (hcover : Finset.univ.biUnion s = Finset.univ) :
    sigma.cycleType =
      (Finset.univ.filter fun i => 1 < (s i).card).1.map fun i => (s i).card := by
  classical
  let J := {i : ι // 1 < (s i).card}
  let x : J → α := fun i => Classical.choose (hne i)
  have hx (i : J) : x i ∈ s i := Classical.choose_spec (hne i)
  have hnontrivial (i : J) : (s i).Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp i.2
  let c : J → Equiv.Perm α := fun i => sigma.cycleOf (x i)
  have hcsupport (i : J) : (c i).support = s i := by
    exact support_cycle sigma (s i) (hnontrivial i)
      (hcycle i) (x i) (hx i)
  have hcinj : Function.Injective c := by
    intro i j hij
    apply Subtype.ext
    by_contra hneij
    have hsets : s i = s j := by
      rw [← hcsupport i, ← hcsupport j, hij]
    obtain ⟨y, hy⟩ := hne i
    have hydisj := Finset.disjoint_left.mp (hdisj hneij) hy
    exact hydisj (hsets ▸ hy)
  let ce : J ↪ Equiv.Perm α := ⟨c, hcinj⟩
  have hcycles : sigma.cycleFactorsFinset = Finset.univ.map ce := by
    ext d
    constructor
    · intro hd
      obtain ⟨y, hy⟩ :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hd).1.nonempty_support
      have hycover : y ∈ Finset.univ.biUnion s := by simp [hcover]
      obtain ⟨i, -, hyi⟩ := Finset.mem_biUnion.mp hycover
      have hdy : d y = sigma y :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hd).2 y hy
      have hymove : sigma y ≠ y := by
        rw [← hdy]
        exact Equiv.Perm.mem_support.mp hy
      have hsigma_y : sigma y ∈ s i :=
        (hcycle i).1.mapsTo hyi
      have hi : 1 < (s i).card := Finset.one_lt_card.mpr
        ⟨y, hyi, sigma y, hsigma_y, hymove.symm⟩
      let ji : J := ⟨i, hi⟩
      have hsame : sigma.SameCycle (x ji) y := (hcycle i).2 (hx ji) hyi
      have hd_eq : d = c ji := by
        calc
          d = sigma.cycleOf y :=
            (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
              sigma d hd y).mpr hy
          _ = sigma.cycleOf (x ji) := hsame.cycleOf_eq.symm
          _ = c ji := rfl
      rw [Finset.mem_map]
      exact ⟨ji, Finset.mem_univ ji, hd_eq.symm⟩
    · intro hd
      rw [Finset.mem_map] at hd
      obtain ⟨i, -, rfl⟩ := hd
      change sigma.cycleOf (x i) ∈ sigma.cycleFactorsFinset
      rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        Equiv.Perm.mem_support]
      exact (hcycle i).apply_ne (hnontrivial i) (hx i)
  rw [Equiv.Perm.cycleType_def, hcycles]
  change
    (Finset.univ.map ce).1.map (Finset.card ∘ Equiv.Perm.support) = _
  rw [Finset.map_val, Multiset.map_map]
  rw [← Finset.univ_val_map_subtype_val (fun i => 1 < (s i).card),
    Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  exact congrArg Finset.card (hcsupport i)

/-- If nonempty, pairwise-disjoint blocks cover a finite type and a
permutation is cyclic on every block, then the full cycle partition consists
of exactly the block cardinalities.  Singleton blocks are retained as parts
of size one. -/
theorem partition_parts_cards
    (sigma : Equiv.Perm α) (s : ι → Finset α)
    (hne : ∀ i, (s i).Nonempty)
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    (hcycle : ∀ i, sigma.IsCycleOn (s i : Set α))
    (hcover : Finset.univ.biUnion s = Finset.univ) :
    sigma.partition.parts = Finset.univ.1.map fun i => (s i).card := by
  classical
  let large : Finset ι := Finset.univ.filter fun i => 1 < (s i).card
  let single : Finset ι := Finset.univ.filter fun i => (s i).card = 1
  have hpos (i : ι) : 0 < (s i).card := Finset.card_pos.mpr (hne i)
  have hlarge_single : large ∪ single = Finset.univ := by
    ext i
    simp only [large, single, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    have := hpos i
    omega
  have hlarge_disjoint_single : Disjoint large single := by
    apply Finset.disjoint_left.mpr
    intro i hi hsi
    simp only [large, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [single, Finset.mem_filter, Finset.mem_univ, true_and] at hsi
    omega
  have hcycleType : sigma.cycleType = large.1.map fun i => (s i).card := by
    simpa only [large] using
      cycle_type_cards sigma s hne hdisj hcycle hcover
  have htotal : ∑ i, (s i).card = Fintype.card α := by
    rw [← Finset.card_biUnion]
    · rw [hcover, Finset.card_univ]
    · intro i hi j hj hij
      exact hdisj hij
  have hlargeSum : ∑ i ∈ large, (s i).card = sigma.support.card := by
    rw [← Equiv.Perm.sum_cycleType, hcycleType]
    simp
  have hsingleSum : ∑ i ∈ single, (s i).card = single.card := by
    calc
      ∑ i ∈ single, (s i).card = ∑ _i ∈ single, 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ = single.card := by simp
  have hsplitSum :
      (∑ i ∈ large, (s i).card) + (∑ i ∈ single, (s i).card) =
        ∑ i, (s i).card := by
    rw [← Finset.sum_union hlarge_disjoint_single, hlarge_single]
  have hfixed : Fintype.card α - sigma.support.card = single.card := by
    omega
  have hsingleDegrees :
      single.1.map (fun i => (s i).card) =
        Multiset.replicate single.card 1 := by
    rw [Multiset.eq_replicate]
    constructor
    · simp
    · intro n hn
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hn
      exact (Finset.mem_filter.mp (Finset.mem_def.mp hi)).2
  have hdegreesSplit :
      Finset.univ.1.map (fun i => (s i).card) =
        large.1.map (fun i => (s i).card) +
          single.1.map (fun i => (s i).card) := by
    rw [← hlarge_single]
    rw [Finset.union_val_nd,
      Multiset.Disjoint.ndunion_eq (Finset.disjoint_val.mpr hlarge_disjoint_single)]
    simp only [Finset.nodup, Multiset.dedup_eq_self.mpr, Multiset.map_add]
  rw [Equiv.Perm.parts_partition, hcycleType, hfixed, ← hsingleDegrees]
  exact hdegreesSplit.symm

end PermutationPartition

section DedekindPartition

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
-- Constructing the full root partition repeats the deep residue-field and
-- integral-closure instance search from `DedekindCyclePartition`.
omit [IsDomain R] in
/-- Dedekind's theorem in full partition form: the parts of arithmetic
Frobenius on the integral roots are exactly the degrees of the distinct
monic irreducible factors of the reduction. -/
theorem frob_partition_degrees
    {ι : Type*} [Fintype ι] [DecidableEq S]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (g : ι → (R ⧸ p)[X])
    (hfac : f.map (Ideal.Quotient.mk p) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g) :
    (arithmeticRootPerm (S := S) (G := G) f
      (arithFrobAt R G Q)).partition.parts =
        Finset.univ.1.map fun i => (g i).natDegree := by
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
  have hgdvd (i : ι) : g i ∣ red := by
    change g i ∣ f.map (Ideal.Quotient.mk p)
    rw [hfac]
    exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  have hgsplits (i : ι) :
      ((g i).map (algebraMap (R ⧸ p) (S ⧸ Q))).Splits :=
    hsplitsRed.of_dvd (map_ne_zero hredmonic.ne_zero)
      ((map_dvd_map' (algebraMap (R ⧸ p) (S ⧸ Q))).mpr (hgdvd i))
  obtain ⟨x, hx, hxdisj⟩ :=
    pairwise_disjoint_cycles
      (R ⧸ p) (S ⧸ Q) g hirr hmonic hgsplits hinj
  have hxred (i : ι) : x i ∈ red.rootSet (S ⧸ Q) := by
    rw [hredmonic.mem_rootSet]
    have hroot : aeval (x i) (g i) = 0 :=
      (hmonic i).mem_rootSet.mp (hx i).1
    obtain ⟨q, hq⟩ := hgdvd i
    rw [hq, map_mul, hroot, zero_mul]
  let xr : ι → red.rootSet (S ⧸ Q) := fun i => ⟨x i, hxred i⟩
  let sigma : G := arithFrobAt R G Q
  have hsigma : IsArithFrobAt R sigma Q := IsArithFrobAt.arithFrobAt R G Q
  let s : ι → Finset (f.rootSet S) := fun i =>
    liftedFrobeniusCycle (p := p) (Q := Q)
      f hf hsplits hsep (xr i)
  have hcycle (i : ι) :
      (arithmeticRootPerm (S := S) (G := G) f sigma).IsCycleOn
        (s i : Set (f.rootSet S)) := by
    exact arithmetic_cycle_lifted
      f hf hsplits hsep hsigma (xr i)
  have hcard (i : ι) : (s i).card = (g i).natDegree := by
    rw [card_lifted_cycle]
    exact (hx i).2.2
  have hsnonempty (i : ι) : (s i).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact (hirr i).natDegree_pos
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
    exact Set.disjoint_left.1 (hxdisj hij) hyi' hyj'
  have hdegree : ∑ i, (g i).natDegree = red.natDegree := by
    change ∑ i, (g i).natDegree =
      (f.map (Ideal.Quotient.mk p)).natDegree
    rw [hfac, natDegree_prod_of_monic Finset.univ g]
    intro i hi
    exact hmonic i
  have hrootcard : Fintype.card (f.rootSet S) = red.natDegree := by
    rw [Fintype.card_congr
      (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hsep)]
    exact card_rootSet_eq_natDegree hsep hsplitsRed
  have hcover : Finset.univ.biUnion s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i hi => hcard i), hdegree]
      exact hrootcard.symm
    · intro i hi j hj hij
      exact hsdisj hij
  change (arithmeticRootPerm (S := S) (G := G) f sigma).partition.parts = _
  rw [partition_parts_cards
    (arithmeticRootPerm (S := S) (G := G) f sigma) s
      hsnonempty hsdisj hcycle hcover]
  apply Multiset.map_congr rfl
  intro i hi
  exact hcard i

omit [IsDomain R] in
/-- Existential form of the full Dedekind factor-degree partition theorem. -/
theorem arithmetic_perm_degrees
    {ι : Type*} [Fintype ι] [DecidableEq S]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (g : ι → (R ⧸ p)[X])
    (hfac : f.map (Ideal.Quotient.mk p) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g) :
    ∃ sigma : G,
      IsArithFrobAt R sigma Q ∧
      (arithmeticRootPerm (S := S) (G := G) f sigma).partition.parts =
        Finset.univ.1.map fun i => (g i).natDegree := by
  refine ⟨arithFrobAt R G Q, IsArithFrobAt.arithFrobAt R G Q, ?_⟩
  exact frob_partition_degrees
    (R := R) (S := S) (G := G) (p := p) (Q := Q)
    f hf hsplits hsep g hfac hirr hmonic hinj

/-- The multiset of degrees of the normalized irreducible factors of the
reduction of `f` modulo `p`. -/
noncomputable def reductionFactorDegrees
    (f : R[X]) (p : Ideal R) [p.IsPrime] [p.IsMaximal] : Multiset ℕ := by
  classical
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  exact (UniqueFactorizationMonoid.normalizedFactors
    (f.map (Ideal.Quotient.mk p))).map Polynomial.natDegree

set_option maxHeartbeats 2000000 in
-- Normalized factorization triggers the same deep residue-field instance search.
omit [IsDomain R] in
/-- At a prime of separable reduction, the full arithmetic-Frobenius
partition is the literal multiset of degrees of the normalized irreducible
factors of the reduction. -/
theorem arithmetic_partition_degrees
    [DecidableEq S]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable) :
    (arithmeticRootPerm (S := S) (G := G) f
      (arithFrobAt R G Q)).partition.parts = reductionFactorDegrees f p := by
  classical
  let red := f.map (Ideal.Quotient.mk p)
  let factors := UniqueFactorizationMonoid.normalizedFactors red
  have hredmonic : red.Monic := hf.map _
  have hredne : red ≠ 0 := hredmonic.ne_zero
  have hnodup : factors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hredne).mp
      hsep.squarefree
  let indices := factors.toFinset
  let g : indices → (R ⧸ p)[X] := fun i => i.1
  have hindexval : indices.1 = factors := by
    simp only [indices, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
  have hfac : red = ∏ i, g i := by
    have hprod : factors.prod = red := by
      rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hredne,
        hredmonic.normalize_eq_self]
    have hindexprod : (∏ i : indices, (i.1 : (R ⧸ p)[X])) = factors.prod := by
      calc
        (∏ i : indices, (i.1 : (R ⧸ p)[X])) =
            ∏ x ∈ indices, x :=
          Finset.prod_coe_sort indices (fun x : (R ⧸ p)[X] => x)
        _ = indices.1.prod := (Finset.prod_val indices).symm
        _ = factors.prod := congrArg Multiset.prod hindexval
    exact hprod.symm.trans hindexprod.symm
  have hirr (i : indices) : Irreducible (g i) := by
    have hi : (i.1 : (R ⧸ p)[X]) ∈ factors :=
      Multiset.mem_toFinset.mp i.2
    exact (Polynomial.mem_normalizedFactors_iff hredne).mp hi |>.1
  have hmonic (i : indices) : (g i).Monic := by
    have hi : (i.1 : (R ⧸ p)[X]) ∈ factors :=
      Multiset.mem_toFinset.mp i.2
    exact (Polynomial.mem_normalizedFactors_iff hredne).mp hi |>.2.1
  have hinj : Function.Injective g := fun i j hij => Subtype.ext hij
  have hpartition :=
    frob_partition_degrees
      (R := R) (S := S) (G := G) (p := p) (Q := Q)
      f hf hsplits hsep g hfac hirr hmonic hinj
  refine hpartition.trans ?_
  have hunivval :
      Finset.univ.1.map ((↑) : indices → (R ⧸ p)[X]) = indices.1 := by
    have hfinset :
        (Finset.univ : Finset indices).map
            (Function.Embedding.subtype
              (fun x : (R ⧸ p)[X] => x ∈ indices)) = indices := by
      rw [Finset.univ_eq_attach, Finset.attach_map_val]
    exact congrArg Finset.val hfinset
  unfold reductionFactorDegrees
  change Finset.univ.1.map
      (Polynomial.natDegree ∘ ((↑) : indices → (R ⧸ p)[X])) =
    factors.map Polynomial.natDegree
  rw [← Multiset.map_map, hunivval, hindexval]

omit [IsDomain R] in
/-- Existential form of the normalized factor-degree partition theorem. -/
theorem perm_partition_degrees
    [DecidableEq S]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable) :
    ∃ sigma : G,
      IsArithFrobAt R sigma Q ∧
      (arithmeticRootPerm (S := S) (G := G) f sigma).partition.parts =
        reductionFactorDegrees f p := by
  refine ⟨arithFrobAt R G Q, IsArithFrobAt.arithFrobAt R G Q, ?_⟩
  exact arithmetic_partition_degrees
    (R := R) (S := S) (G := G) (p := p) (Q := Q) f hf hsplits hsep

end DedekindPartition

end

end Submission.NumberTheory.Milne
