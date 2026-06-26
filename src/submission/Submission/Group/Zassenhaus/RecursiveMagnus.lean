import Submission.Algebra.Magnus.MagnusWeighted
import Submission.Algebra.Magnus.RecursiveWeightedIdeals


/-!
# Recursive filtrations and the Magnus embedding

This file formalizes the recursive construction and Theorem 6.1 of
Efrat--Chapman.
-/

namespace EChapma

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The recursive filtration from equation (6.1) of the paper.  Level zero
is harmlessly set equal to the whole group. -/
noncomputable def recursiveFiltration
    (G : Type*) [Group G]
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n) :
    ℕ → Subgroup G
  | 0 => ⊤
  | 1 => ⊤
  | n + 2 =>
      subgroupPower
          (recursiveFiltration G T f g hg (g (n + 2))) (f (n + 2)) ⊔
        ⨆ st : {st : ℕ × ℕ //
            st ∈ T ∧ 1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = n + 2},
          ⁅recursiveFiltration G T f g hg st.1.1,
            recursiveFiltration G T f g hg st.1.2⁆
termination_by n => n
decreasing_by
  · exact (hg (n + 2) (by omega)).2
  · omega
  · omega

@[simp]
theorem recursiveFiltration_zero
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n) :
    recursiveFiltration G T f g hg 0 = ⊤ :=
  recursiveFiltration.eq_1 G T f g hg

@[simp]
theorem recursiveFiltration_one
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n) :
    recursiveFiltration G T f g hg 1 = ⊤ :=
  recursiveFiltration.eq_2 G T f g hg

theorem recursive_filtration_succ
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n)
    (n : ℕ) :
    recursiveFiltration G T f g hg (n + 2) =
      subgroupPower
          (recursiveFiltration G T f g hg (g (n + 2))) (f (n + 2)) ⊔
        ⨆ st : {st : ℕ × ℕ //
            st ∈ T ∧ 1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = n + 2},
          ⁅recursiveFiltration G T f g hg st.1.1,
            recursiveFiltration G T f g hg st.1.2⁆ :=
  recursiveFiltration.eq_3 G T f g hg n

namespace MSeries

variable {X : Type*}

/-- A two-sided ideal containing both ordered products of the two Magnus
differences contains the difference of their unit commutator. -/
private theorem units_commutator_sub
    {A : Type*} [Ring A]
    (J : Ideal A) [J.IsTwoSided]
    {u v : Aˣ}
    (hUV : ((u : A) - 1) * ((v : A) - 1) ∈ J)
    (hVU : ((v : A) - 1) * ((u : A) - 1) ∈ J) :
    (((⁅u, v⁆ : Aˣ) : A) - 1) ∈ J := by
  let U : A := (u : A) - 1
  let V : A := (v : A) - 1
  let uInv : A := ((u⁻¹ : Aˣ) : A)
  let vInv : A := ((v⁻¹ : Aˣ) : A)
  have hsub : U * V - V * U ∈ J := J.sub_mem hUV hVU
  have hright : ((U * V - V * U) * uInv) * vInv ∈ J :=
    Ideal.mul_mem_right vInv J (Ideal.mul_mem_right uInv J hsub)
  rw [show
      (((⁅u, v⁆ : Aˣ) : A) - 1) =
        ((U * V - V * U) * uInv) * vInv by
    dsimp [U, V, uInv, vInv]
    rw [commutatorElement_def]
    simp only [Units.val_mul]
    have huu : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
    have hvv : (v : A) * ((v⁻¹ : Aˣ) : A) = 1 := v.val_inv
    have hcancel :
        (v : A) * (u : A) * ((u⁻¹ : Aˣ) : A) *
            ((v⁻¹ : Aˣ) : A) = 1 := by
      calc
        (v : A) * (u : A) * ((u⁻¹ : Aˣ) : A) *
              ((v⁻¹ : Aˣ) : A) =
            (v : A) * ((u : A) * ((u⁻¹ : Aˣ) : A)) *
              ((v⁻¹ : Aˣ) : A) := by simp []
        _ = (v : A) * 1 * ((v⁻¹ : Aˣ) : A) := by rw [huu]
        _ = 1 := by simp
    calc
      (u : A) * (v : A) * ((u⁻¹ : Aˣ) : A) *
              ((v⁻¹ : Aˣ) : A) - 1 =
          (u : A) * (v : A) * ((u⁻¹ : Aˣ) : A) *
                ((v⁻¹ : Aˣ) : A) -
            ((v : A) * (u : A) * ((u⁻¹ : Aˣ) : A) *
              ((v⁻¹ : Aˣ) : A)) := by rw [hcancel]
      _ = (((u : A) - 1) * ((v : A) - 1) -
            ((v : A) - 1) * ((u : A) - 1)) *
            ((u⁻¹ : Aˣ) : A) *
          ((v⁻¹ : Aˣ) : A) := by noncomm_ring]
  exact hright

/-- At level one the weighted Magnus subgroup is the whole free group. -/
theorem magnus_weighted_top
    (e : MDescen) :
    magnusWeightedSubgroup (R := ℤ) (X := X) e 1 = ⊤ := by
  apply top_unique
  intro x _
  rw [magnus_weighted_subgroup, mem_weightedIdeal]
  have horder :
      magnusDifference (R := ℤ) x ∈
        (magnusAddFiltration (R := ℤ) (X := X)).term 1 :=
    magnus_vanishes_below x
  simpa [e.diagonal 1 le_rfl] using
    (magnusAddFiltration (R := ℤ) (X := X)).weightedGenerator_mem
      e le_rfl le_rfl horder

/-- The recursive power factor is sent into the target weighted Magnus
subgroup by condition (2). -/
theorem magnus_weighted_condition
    (e : MDescen)
    (f g : ℕ → ℕ)
    (hpower : e.HasPowerCondition f g)
    {n : ℕ} (hn : 2 ≤ n) :
    subgroupPower
        (magnusWeightedSubgroup (R := ℤ) (X := X) e (g n))
        (f n) ≤
      magnusWeightedSubgroup (R := ℤ) (X := X) e n := by
  unfold subgroupPower
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, hx, rfl⟩
  rw [magnus_weighted_subgroup] at hx
  change magnusDifference (R := ℤ) (x ^ f n) ∈
    weightedIdeal (R := ℤ) (X := X) e n
  let alpha : MSeries ℤ X := magnusDifference (R := ℤ) x
  have htail :
      MAFilt.powerConditionTail (f n) alpha ∈
        (magnusAddFiltration (R := ℤ) (X := X)).weightedSubgroup e n :=
    MAFilt.condition_weighted_subgroup
      (magnusAddFiltration (R := ℤ) (X := X))
        e f g hpower hn hx
  have hseries :
      magnusSeries (R := ℤ) x = 1 + alpha := by
    dsimp [alpha, magnusDifference]
    noncomm_ring
  have hdiff :
      magnusDifference (R := ℤ) (x ^ f n) =
        MAFilt.powerConditionTail (f n) alpha := by
    calc
      magnusDifference (R := ℤ) (x ^ f n) =
          magnusSeries (R := ℤ) x ^ f n - 1 := by
            simp [magnusDifference, map_pow, magnusSeries, magnusUnitHom]
      _ = (1 + alpha) ^ f n - 1 := by rw [hseries]
      _ = MAFilt.powerConditionTail (f n) alpha :=
        MAFilt.sub_condition_tail
          (f n) alpha
  rw [hdiff]
  exact htail

/-- A single instance of condition (1) sends the corresponding subgroup
commutator into the weighted Magnus subgroup at the sum level. -/
theorem magnus_dvd_condition
    (e : MDescen)
    (s t : ℕ)
    (hcomm : ∀ ⦃i j : ℕ⦄,
      1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
      e (s + t) (i + j) ∣ e s i * e t j) :
    ⁅magnusWeightedSubgroup (R := ℤ) (X := X) e s,
        magnusWeightedSubgroup (R := ℤ) (X := X) e t⁆ ≤
      magnusWeightedSubgroup (R := ℤ) (X := X) e (s + t) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [magnus_weighted_subgroup] at hx hy ⊢
  let U : MSeries ℤ X := magnusDifference (R := ℤ) x
  let V : MSeries ℤ X := magnusDifference (R := ℤ) y
  have hUV :
      U * V ∈ weightedIdeal (R := ℤ) (X := X) e (s + t) := by
    change U * V ∈
      (magnusAddFiltration (R := ℤ) (X := X)).weightedSubgroup e (s + t)
    exact
      MAFilt.weighted_dvd_condition
        (magnusAddFiltration (R := ℤ) (X := X)) e s t hcomm
        (Submodule.mul_mem_mul hx hy)
  have hVU :
      V * U ∈ weightedIdeal (R := ℤ) (X := X) e (s + t) := by
    change V * U ∈
      (magnusAddFiltration (R := ℤ) (X := X)).weightedSubgroup e (s + t)
    have hreverse :
        ∀ ⦃j i : ℕ⦄,
          1 ≤ j → j ≤ t → 1 ≤ i → i ≤ s →
          e (t + s) (j + i) ∣ e t j * e s i := by
      intro j i hj hjt hi his
      simpa [Nat.add_comm, Nat.mul_comm] using hcomm hi his hj hjt
    simpa [Nat.add_comm] using
      MAFilt.weighted_dvd_condition
        (magnusAddFiltration (R := ℤ) (X := X)) e t s hreverse
        (Submodule.mul_mem_mul hy hx)
  simpa [U, V, magnusDifference, magnusSeries, magnusUnitHom,
    map_commutatorElement] using
    units_commutator_sub
      (weightedIdeal (R := ℤ) (X := X) e (s + t))
      (u := magnusUnitHom (R := ℤ) (X := X) x)
      (v := magnusUnitHom (R := ℤ) (X := X) y)
      hUV hVU

/-- Efrat--Chapman, Theorem 6.1. -/
theorem recursive_filtration_magnus
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n)
    (e : MDescen)
    (hcomm : e.CommutatorCondition T)
    (hpower : e.HasPowerCondition f g)
    (n : ℕ) (hn : 1 ≤ n) :
    recursiveFiltration (FreeGroup X) T f g hg n ≤
      magnusWeightedSubgroup (R := ℤ) (X := X) e n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · omega
      · simp [magnus_weighted_top e]
      · rw [recursive_filtration_succ]
        apply sup_le
        · exact
            (subgroupPower_mono
              (ih (g (n + 2)) (hg (n + 2) (by omega)).2
                (hg (n + 2) (by omega)).1)
              (f (n + 2))).trans
              (magnus_weighted_condition
                e f g hpower (by omega))
        · apply iSup_le
          intro st
          have hs :
              recursiveFiltration (FreeGroup X) T f g hg st.1.1 ≤
                magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.1 :=
            ih st.1.1 (by omega) st.property.2.1
          have ht :
              recursiveFiltration (FreeGroup X) T f g hg st.1.2 ≤
                magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.2 :=
            ih st.1.2 (by omega) st.property.2.2.1
          have hc :
              ⁅magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.1,
                  magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.2⁆ ≤
                magnusWeightedSubgroup (R := ℤ) (X := X) e
                  (st.1.1 + st.1.2) := by
            apply magnus_dvd_condition
            intro i j hi his hj hjt
            exact hcomm st.property.1 hi his hj hjt
          exact (Subgroup.commutator_mono hs ht).trans <| by
            simpa [st.property.2.2.2] using hc

/-- Sequence-form interface to Theorem 6.1.  It is convenient when a
filtration has already been defined independently and its recursive step
has been proved separately. -/
theorem recursive_sequence_magnus
    (Q : ℕ → Subgroup (FreeGroup X))
    (T : Set (ℕ × ℕ)) (f g : ℕ → ℕ)
    (hg : ∀ n, 2 ≤ n → 1 ≤ g n ∧ g n < n)
    (e : MDescen)
    (hcomm : e.CommutatorCondition T)
    (hpower : e.HasPowerCondition f g)
    (hQone :
      Q 1 ≤ magnusWeightedSubgroup (R := ℤ) (X := X) e 1)
    (hQstep : ∀ n, 2 ≤ n →
      Q n ≤
        subgroupPower (Q (g n)) (f n) ⊔
          ⨆ st : {st : ℕ × ℕ //
              st ∈ T ∧ 1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = n},
            ⁅Q st.1.1, Q st.1.2⁆)
    (n : ℕ) (hn : 1 ≤ n) :
    Q n ≤ magnusWeightedSubgroup (R := ℤ) (X := X) e n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · simpa [hn1] using hQone
      · have hn2 : 2 ≤ n := by omega
        exact (hQstep n hn2).trans <| sup_le
          ((subgroupPower_mono
            (ih (g n) (hg n hn2).2 (hg n hn2).1)
            (f n)).trans
            (magnus_weighted_condition
              e f g hpower hn2))
          (by
            apply iSup_le
            intro st
            have hs := ih st.1.1 (by omega) st.property.2.1
            have ht := ih st.1.2 (by omega) st.property.2.2.1
            have hc :
                ⁅magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.1,
                    magnusWeightedSubgroup (R := ℤ) (X := X) e st.1.2⁆ ≤
                  magnusWeightedSubgroup (R := ℤ) (X := X) e
                    (st.1.1 + st.1.2) := by
              apply magnus_dvd_condition
              intro i j hi his hj hjt
              exact hcomm st.property.1 hi his hj hjt
            exact (Subgroup.commutator_mono hs ht).trans <| by
              simpa [st.property.2.2.2] using hc)

end MSeries

end EChapma
