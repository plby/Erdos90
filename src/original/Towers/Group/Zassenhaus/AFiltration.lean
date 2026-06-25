import Towers.Group.Zassenhaus.CommutatorPowers
import Towers.Group.Zassenhaus.MultiplicativelyDescending
import Towers.Group.Zassenhaus.RecursiveMagnus
import Towers.Algebra.Magnus.WeightedConverse
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card


/-!
# The A-filtration

This file defines the filtration from Section 7 of Efrat--Chapman and
proves Lemma 7.3: the term obtained after finitely many steps is unchanged
when those exponents are permuted.
-/

namespace EChapma

variable {G : Type*} [Group G]

/-- A subgroup bundled together with a proof of normality. -/
private abbrev NormalSubgroupData (G : Type*) [Group G] :=
  {H : Subgroup G // H.Normal}

/-- One step `H ↦ H^a[H,G]` of the A-filtration, on bundled normal
subgroups. -/
private def normalRelativeStep
    (H : NormalSubgroupData G) (a : ℕ) :
    NormalSubgroupData G := by
  letI : H.1.Normal := H.2
  exact ⟨relativePowerCommutator H.1 a, inferInstance⟩

private instance normal_relative_commutative :
    RightCommutative (@normalRelativeStep G _) where
  right_comm H a b := by
    apply Subtype.ext
    letI : H.1.Normal := H.2
    exact relative_power_swap H.1 a b

/-- Apply a finite list of A-filtration exponents, starting at `G`. -/
def filtrationList (exponents : List ℕ) : Subgroup G :=
  (exponents.foldl normalRelativeStep
    (⟨⊤, inferInstance⟩ : NormalSubgroupData G)).1

instance filtration_list_normal (exponents : List ℕ) :
    (filtrationList (G := G) exponents).Normal := by
  exact
    (exponents.foldl normalRelativeStep
      (⟨⊤, inferInstance⟩ : NormalSubgroupData G)).2

@[simp]
theorem filtration_list_nil :
    filtrationList (G := G) [] = ⊤ :=
  rfl

@[simp]
theorem filtration_append_singleton
    (exponents : List ℕ) (a : ℕ) :
    filtrationList (G := G) (exponents ++ [a]) =
      relativePowerCommutator
        (filtrationList (G := G) exponents) a := by
  simp [filtrationList, normalRelativeStep]

/-- The finite A-filtration depends only on the multiset of exponents. -/
theorem filtration_list_perm
    {as bs : List ℕ} (h : as.Perm bs) :
    filtrationList (G := G) as =
      filtrationList (G := G) bs := by
  exact congrArg Subtype.val
    (h.foldl_eq
      (⟨⊤, inferInstance⟩ : NormalSubgroupData G))

/-- The lower-central term indexed by the number of completed steps is
contained in every finite A-filtration, independently of the exponents. -/
theorem lower_filtration_list
    (exponents : List ℕ) :
    Subgroup.lowerCentralSeries G exponents.length ≤
      filtrationList (G := G) exponents := by
  induction exponents using List.reverseRecOn with
  | nil => simp
  | append_singleton exponents a ih =>
      rw [List.length_append, List.length_singleton,
        Subgroup.lowerCentralSeries_succ, filtration_append_singleton]
      exact (Subgroup.commutator_mono ih le_rfl).trans le_sup_right

/-- Applying a suffix of A-filtration exponents contains the corresponding
iterated power subgroup of the starting term. -/
theorem subgroup_filtration_append
    (pre suffix : List ℕ) :
    subgroupPower (filtrationList (G := G) pre) suffix.prod ≤
      filtrationList (G := G) (pre ++ suffix) := by
  induction suffix using List.reverseRecOn with
  | nil =>
      simp [subgroupPower_one]
  | append_singleton suffix a ih =>
      rw [List.prod_append, List.prod_singleton, ← List.append_assoc,
        filtration_append_singleton]
      exact
        (subgroup_power_mul
          (filtrationList (G := G) pre) suffix.prod a).trans
          ((subgroupPower_mono ih a).trans le_sup_left)

/-- If a list is permuted so that `i-1` entries come first, the product
of the remaining exponents applied to `γ_i(G)` lies in the resulting
A-filtration. -/
theorem subgroup_filtration_perm
    (as pre suffix : List ℕ) (i : ℕ)
    (hperm : (pre ++ suffix).Perm as)
    (hlen : pre.length = i - 1) :
    subgroupPower (Subgroup.lowerCentralSeries G (i - 1)) suffix.prod ≤
      filtrationList (G := G) as := by
  rw [← filtration_list_perm hperm]
  exact
    (subgroupPower_mono
      (by
        rw [← hlen]
        exact lower_filtration_list pre)
      suffix.prod).trans
      (subgroup_filtration_append pre suffix)

/-- Apply a finite tuple of exponents. -/
def aFiltrationPrefix {m : ℕ} (A : Fin m → ℕ) : Subgroup G :=
  filtrationList (G := G) (List.ofFn A)

instance filtration_prefix_normal {m : ℕ} (A : Fin m → ℕ) :
    (aFiltrationPrefix (G := G) A).Normal := by
  unfold aFiltrationPrefix
  infer_instance

/-- Efrat--Chapman, Lemma 7.3, finite-prefix form: applying a
permutation to the exponents does not change the resulting subgroup. -/
theorem filtration_prefix_perm
    {m : ℕ} (A : Fin m → ℕ) (σ : Equiv.Perm (Fin m)) :
    aFiltrationPrefix (G := G) (A ∘ σ) =
      aFiltrationPrefix (G := G) A := by
  apply filtration_list_perm
  exact σ.ofFn_comp_perm A

/-- The paper's `A`-filtration.  The term at level `n` uses the exponents
`A 1, ..., A (n-1)`; level zero is harmlessly set equal to `G`. -/
def aFiltration (A : ℕ → ℕ) (n : ℕ) : Subgroup G :=
  aFiltrationPrefix (G := G)
    (fun i : Fin (n - 1) => A (i.1 + 1))

instance aFiltration_normal (A : ℕ → ℕ) (n : ℕ) :
    (aFiltration (G := G) A n).Normal := by
  unfold aFiltration
  infer_instance

@[simp]
theorem aFiltration_zero (A : ℕ → ℕ) :
    aFiltration (G := G) A 0 = ⊤ := by
  rfl

@[simp]
theorem aFiltration_one (A : ℕ → ℕ) :
    aFiltration (G := G) A 1 = ⊤ := by
  rfl

/-- The defining recursion
`G^(n+2,A) = (G^(n+1,A))^(A(n+1)) [G^(n+1,A),G]`. -/
theorem a_filtration_succ
    (A : ℕ → ℕ) (n : ℕ) :
    aFiltration (G := G) A (n + 2) =
      relativePowerCommutator
        (aFiltration (G := G) A (n + 1)) (A (n + 1)) := by
  unfold aFiltration aFiltrationPrefix
  have hleft : n + 2 - 1 = n + 1 := by omega
  have hright : n + 1 - 1 = n := by omega
  rw [show n + 2 - 1 = n + 1 from hleft,
    show n + 1 - 1 = n from hright]
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  rw [filtration_append_singleton]
  congr 1

/-- Lemma 7.3 in sequence notation: permuting the first `n-1`
exponents leaves the level-`n` filtration term unchanged. -/
theorem filtration_permute_prefix
    (A : ℕ → ℕ) (n : ℕ) (σ : Equiv.Perm (Fin (n - 1))) :
    aFiltrationPrefix (G := G)
        ((fun i : Fin (n - 1) => A (i.1 + 1)) ∘ σ) =
      aFiltration (G := G) A n :=
  filtration_prefix_perm _ σ

/-- The paper's list of indices `1, ..., n-1`. -/
private def paperIndexList (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n - 1) => i.1 + 1)

private theorem paper_index_finset (n : ℕ) :
    (paperIndexList n).toFinset = Finset.Icc 1 (n - 1) := by
  ext x
  simp only [paperIndexList, List.mem_toFinset, List.mem_ofFn,
    Finset.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨hx1, hx2⟩
    let i : Fin (n - 1) := ⟨x - 1, by omega⟩
    refine ⟨i, ?_⟩
    simp only [i]
    omega

private theorem paper_index_nodup (n : ℕ) :
    (paperIndexList n).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel hij

private theorem paper_perm_icc (n : ℕ) :
    (paperIndexList n).Perm (Finset.Icc 1 (n - 1)).toList := by
  apply (List.perm_ext_iff_of_nodup
    (paper_index_nodup n) (Finset.nodup_toList _)).2
  intro x
  rw [← List.mem_toFinset, paper_index_finset]
  simp

private theorem sdiff_append_perm
    (S J : Finset ℕ) (hJ : J ⊆ S) :
    ((S \ J).toList ++ J.toList).Perm S.toList := by
  have hn : ((S \ J).toList ++ J.toList).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro x hx y hy hxy
    subst y
    simp only [Finset.mem_toList] at hx hy
    exact (Finset.mem_sdiff.mp hx).2 hy
  apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList S)).2
  intro x
  simp only [List.mem_append, Finset.mem_toList, Finset.mem_sdiff]
  constructor
  · rintro (hx | hx)
    · exact hx.1
    · exact hJ hx
  · intro hx
    by_cases hxJ : x ∈ J
    · exact Or.inr hxJ
    · exact Or.inl ⟨hx, hxJ⟩

/-- The closed-form product from Theorem 7.4. -/
def sequenceLowerProduct
    (A : ℕ → ℕ) (n : ℕ) : Subgroup G :=
  ⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ n},
    subgroupPower (Subgroup.lowerCentralSeries G (i.1 - 1))
      (MDescen.sequenceCoefficient A n i.1)

/-- The group-theoretic inclusion in Efrat--Chapman, Theorem 7.4:
the closed-form product is contained in the recursively defined
A-filtration. -/
theorem sequence_lower_filtration
    (A : ℕ → ℕ) (n : ℕ) :
    sequenceLowerProduct (G := G) A n ≤
      aFiltration (G := G) A n := by
  unfold sequenceLowerProduct
  apply iSup_le
  intro i
  let S : Finset ℕ := Finset.Icc 1 (n - 1)
  let C : Finset (Finset ℕ) := S.powersetCard (n - i.1)
  let exponent : Finset ℕ → ℕ := fun J => ∏ j ∈ J, A j
  change
    subgroupPower (Subgroup.lowerCentralSeries G (i.1 - 1)) (C.gcd exponent) ≤ _
  apply subgroup_finset_gcd
  intro J hJ
  have hJdata := Finset.mem_powersetCard.mp hJ
  let pre := (S \ J).toList.map A
  let suffix := J.toList.map A
  have hsuffixprod : suffix.prod = exponent J := by
    dsimp [suffix, exponent]
    rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList]
    simp
  rw [← hsuffixprod]
  change
    subgroupPower (Subgroup.lowerCentralSeries G (i.1 - 1)) suffix.prod ≤
      filtrationList
        (List.ofFn (fun k : Fin (n - 1) => A (k.1 + 1)))
  apply subgroup_filtration_perm
    (as := List.ofFn (fun k : Fin (n - 1) => A (k.1 + 1)))
    (pre := pre) (suffix := suffix) (i := i.1)
  · have hsplit := sdiff_append_perm S J hJdata.1
    have hstandard := paper_perm_icc n
    simpa [pre, suffix, paperIndexList] using
      (hsplit.map A).trans (hstandard.symm.map A)
  · dsimp [pre]
    rw [List.length_map, Finset.length_toList, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hJdata.1, hJdata.2]
    simp only [S, Nat.card_Icc]
    omega

/-- The commutator pairs used by the recursive description of the
`A`-filtration. -/
def filtrationCommutatorPairs : Set (ℕ × ℕ) :=
  {st | st.2 = 1}

/-- The sequence coefficients satisfy condition (1) on the commutator
pairs used by the `A`-filtration. -/
theorem sequence_condition_filtration
    (A : ℕ → ℕ) :
    (MDescen.ofSequence A).CommutatorCondition
      filtrationCommutatorPairs := by
  intro s t i j hst hi his hj hjt
  change t = 1 at hst
  have ht : t = 1 := hst
  have hj1 : j = 1 := by omega
  subst t
  subst j
  exact dvd_mul_of_dvd_left
    (MDescen.sequence_commutator_condition A hi his)
    _

/-- The defining step of the `A`-filtration has the general recursive
form from Section 6. -/
theorem filtration_recursive_step
    (A : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) :
    aFiltration (G := G) A n ≤
      subgroupPower
          (aFiltration (G := G) A (n - 1)) (A (n - 1)) ⊔
        ⨆ st : {st : ℕ × ℕ //
            st ∈ filtrationCommutatorPairs ∧
              1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = n},
          ⁅aFiltration (G := G) A st.1.1,
            aFiltration (G := G) A st.1.2⁆ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [a_filtration_succ]
  unfold relativePowerCommutator
  apply sup_le
  · simp
  · let st : {st : ℕ × ℕ //
        st ∈ filtrationCommutatorPairs ∧
          1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = k + 2} :=
      ⟨(k + 1, 1), by
        simp [filtrationCommutatorPairs]⟩
    exact (le_iSup
      (fun st : {st : ℕ × ℕ //
          st ∈ filtrationCommutatorPairs ∧
            1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = k + 2} =>
        ⁅aFiltration (G := G) A st.1.1,
          aFiltration (G := G) A st.1.2⁆) st).trans le_sup_right

section FreeGroup

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

omit [Fintype X] [DecidableEq X] in
/-- The reverse inclusion in Theorem 7.4, obtained from Theorem 6.1 and
the integral equality of Theorem 4.3. -/
theorem filtration_sequence_lower
    [Finite X]
    (A : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := FreeGroup X) A n ≤
      sequenceLowerProduct (G := FreeGroup X) A n := by
  classical
  have hMagnus :
      aFiltration (G := FreeGroup X) A n ≤
        MSeries.magnusWeightedSubgroup
          (R := ℤ) (X := X)
          (MDescen.ofSequence A) n := by
    apply MSeries.recursive_sequence_magnus
      (Q := aFiltration (G := FreeGroup X) A)
      (T := filtrationCommutatorPairs)
      (f := fun m => A (m - 1))
      (g := fun m => m - 1)
      (hg := by
        intro m hm
        constructor <;> dsimp <;> omega)
      (e := MDescen.ofSequence A)
      (n := n)
    · exact sequence_condition_filtration A
    · exact MDescen.sequence_power_condition A
    · simp [MSeries.magnus_weighted_top]
    · intro m hm
      exact filtration_recursive_step A m hm
    · exact hn
  rw [← MSeries.weighted_magnus_int
    (MDescen.ofSequence A)
    (MDescen.sequence_binomial A) hn] at hMagnus
  exact hMagnus

omit [Fintype X] [DecidableEq X] in
/-- Efrat--Chapman, Theorem 7.4. -/
theorem filtration_sequence_product
    [Finite X]
    (A : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := FreeGroup X) A n =
      sequenceLowerProduct (G := FreeGroup X) A n :=
  le_antisymm
    (filtration_sequence_lower A n hn)
    (sequence_lower_filtration A n)

omit [Fintype X] [DecidableEq X] in
/-- Efrat--Chapman, Corollary 7.5 for free groups: the constant
`a`-filtration has the usual power-product formula. -/
theorem constant_filtration_product
    [Finite X]
    (a n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := FreeGroup X) (fun _ => a) n =
      ⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ n},
        subgroupPower (Subgroup.lowerCentralSeries (FreeGroup X) (i.1 - 1))
          (a ^ (n - i.1)) := by
  classical
  rw [filtration_sequence_product (fun _ => a) n hn]
  unfold sequenceLowerProduct
  congr 1
  funext i
  rw [MDescen.sequenceCoefficient_const
    a n i.1 i.property.1 i.property.2]

end FreeGroup

end EChapma
