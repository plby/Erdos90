import Towers.ClassField.CohomologyOps.CochainFormula
import Towers.ClassField.CohomologyOps.PrefixSucc

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open scoped BigOperators MonoidalCategory

variable {G : Type} [Group G]

theorem initial_tuple_cast {a b c d : ℕ} (h : a + b = c + d)
    (g : Fin (a + b) → G) :
    initialProduct c d (tupleCast h g) =
      Fin.partialProd g ⟨c, by omega⟩ := by
  unfold initialProduct Fin.partialProd tupleCast
  change ((List.ofFn (fun i : Fin (c + d) => g (Fin.cast h.symm i))).take c).prod =
    ((List.ofFn g).take c).prod
  rw [← List.ofFn_congr h g]

theorem initialProduct_tail (r s : ℕ) (g : Fin (r + s + 1) → G) :
    g 0 * initialProduct r s (fun i => g i.succ) =
      Fin.partialProd g ⟨r + 1, by omega⟩ := by
  unfold initialProduct
  symm
  simpa [Fin.tail] using
    (Fin.partialProd_succ' g ⟨r, by omega⟩)

/-- The inhomogeneous differential, exposed as an ordinary function. -/
def cochainDifferential (A : Rep ℤ G) (n : ℕ)
    (f : (Fin n → G) → A) : (Fin (n + 1) → G) → A :=
  (inhomogeneousCochains.d (k := ℤ) (G := G) A n).hom f

theorem cochainDifferential_apply (A : Rep ℤ G) (n : ℕ)
    (f : (Fin n → G) → A) (g : Fin (n + 1) → G) :
    cochainDifferential A n f g =
      A.ρ (g 0) (f fun i => g i.succ) +
        ∑ j : Fin (n + 1), A.hV2.smul ((-1 : ℤ) ^ ((j : ℕ) + 1))
          (f (Fin.contractNth j (· * ·) g)) := by
  simp only [cochainDifferential, inhomogeneousCochains.d_hom_apply]
  congr 1

theorem rep_smul_smul (A : Rep ℤ G) (a b : ℤ) (x : A) :
    A.hV2.smul a (A.hV2.smul b x) = A.hV2.smul (a * b) x := by
  calc
    A.hV2.smul a (A.hV2.smul b x) = a • (b • x) := by
      rw [int_smul_eq_zsmul A.hV2 a (A.hV2.smul b x),
        int_smul_eq_zsmul A.hV2 b x]
    _ = (a * b) • x := smul_smul a b x
    _ = A.hV2.smul (a * b) x :=
      (int_smul_eq_zsmul A.hV2 (a * b) x).symm

theorem cup_action_term (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (g : Fin (r + s + 1) → G) :
    (M ⊗ N : Rep ℤ G).ρ (g 0)
        (cochainCup M N r s φ ψ (fun i => g i.succ)) =
      tensorElement M N
        (M.ρ (tupleCast (by omega : r + s + 1 = (r + 1) + s) g
            (Fin.castAdd s 0))
          (φ fun i => tupleCast (by omega : r + s + 1 = (r + 1) + s) g
            (Fin.castAdd s i.succ)))
        (N.ρ (initialProduct (r + 1) s
            (tupleCast (by omega : r + s + 1 = (r + 1) + s) g))
          (ψ fun j => tupleCast (by omega : r + s + 1 = (r + 1) + s) g
            (Fin.natAdd (r + 1) j))) := by
  simp only [cochainCup, tensorElement_action, tupleCast_apply,
    initial_tuple_cast]
  rw [rep_action_mul, initialProduct_tail]
  congr 3
  all_goals
    funext i
    congr 1
  apply Fin.ext
  simp only [Fin.val_succ, Fin.natAdd]
  omega

theorem cup_left_face (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (g : Fin (r + s + 1) → G) (j : Fin r) :
    (M ⊗ N : Rep ℤ G).hV2.smul
        ((-1 : ℤ) ^ ((leftIndex (s := s) j : ℕ) + 1))
        (cochainCup M N r s φ ψ
          (Fin.contractNth (leftIndex (s := s) j) (· * ·) g)) =
      tensorElement M N
        (M.hV2.smul ((-1 : ℤ) ^ ((j.castSucc : ℕ) + 1))
          (φ (Fin.contractNth j.castSucc (· * ·)
            (fun i : Fin (r + 1) =>
              tupleCast (by omega : r + s + 1 = (r + 1) + s) g
                (Fin.castAdd s i)))))
        (N.ρ (initialProduct (r + 1) s
            (tupleCast (by omega : r + s + 1 = (r + 1) + s) g))
          (ψ fun k => tupleCast (by omega : r + s + 1 = (r + 1) + s) g
            (Fin.natAdd (r + 1) k))) := by
  simp only [cochainCup, leftIndex_val, Fin.val_castSucc, tupleCast_apply,
    initial_tuple_cast]
  rw [tensor_element_rep]
  have hφ :
      φ (fun i => Fin.contractNth (leftIndex (s := s) j) (· * ·) g
          (Fin.castAdd s i)) =
        φ (Fin.contractNth j.castSucc (· * ·)
          (fun i : Fin (r + 1) =>
            g ⟨(Fin.castAdd s i : ℕ), by omega⟩)) := by
    apply congrArg φ
    calc
      (fun i => Fin.contractNth (leftIndex (s := s) j) (· * ·) g
          (Fin.castAdd s i)) =
          Fin.contractNth j.castSucc (· * ·) (prefixSucc g) :=
        contract_left_prefix (· * ·) g j
      _ = _ := by
        congr 1
  have hψ :
      ψ (fun i => Fin.contractNth (leftIndex (s := s) j) (· * ·) g
          (Fin.natAdd r i)) =
        ψ (fun i => g ⟨(Fin.natAdd (r + 1) i : ℕ), by omega⟩) := by
    apply congrArg ψ
    calc
      (fun i => Fin.contractNth (leftIndex (s := s) j) (· * ·) g
          (Fin.natAdd r i)) =
          (fun i : Fin s => g ⟨r + 1 + i, by omega⟩) :=
        contract_left_suffix (· * ·) g j
      _ = _ := by
        funext i
        congr 1
  have hp :
      initialProduct r s
          (Fin.contractNth (leftIndex (s := s) j) (· * ·) g) =
        Fin.partialProd g ⟨r + 1, by omega⟩ := by
    exact partial_contract_left g j
  rw [hφ, hp, hψ]

theorem cup_cancel_terms (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (g : Fin (r + s + 1) → G) :
    tensorElement M N
        (M.hV2.smul ((-1 : ℤ) ^ ((Fin.last r : ℕ) + 1))
          (φ (Fin.contractNth (Fin.last r) (· * ·)
            (fun i : Fin (r + 1) =>
              tupleCast (by omega : r + s + 1 = (r + 1) + s) g
                (Fin.castAdd s i)))))
        (N.ρ (initialProduct (r + 1) s
            (tupleCast (by omega : r + s + 1 = (r + 1) + s) g))
          (ψ fun k => tupleCast (by omega : r + s + 1 = (r + 1) + s) g
            (Fin.natAdd (r + 1) k))) +
      (M ⊗ N : Rep ℤ G).hV2.smul ((-1 : ℤ) ^ r)
        (tensorElement M N
          (φ fun i => tupleCast (by omega : r + s + 1 = r + (s + 1)) g
            (Fin.castAdd (s + 1) i))
          (N.ρ (initialProduct r (s + 1)
              (tupleCast (by omega : r + s + 1 = r + (s + 1)) g))
            (N.ρ (tupleCast (by omega : r + s + 1 = r + (s + 1)) g
                (Fin.natAdd r 0))
              (ψ fun i => tupleCast (by omega : r + s + 1 = r + (s + 1)) g
                (Fin.natAdd r i.succ))))) = 0 := by
  simp only [tupleCast_apply, initial_tuple_cast, Fin.val_last]
  rw [tensor_element_rep]
  have hφ :
      φ (Fin.contractNth (Fin.last r) (· * ·)
          (fun i : Fin (r + 1) => g ⟨(Fin.castAdd s i : ℕ), by omega⟩)) =
        φ (fun i => g ⟨(Fin.castAdd (s + 1) i : ℕ), by omega⟩) := by
    apply congrArg φ
    funext i
    rw [Fin.contractNth_apply_of_lt]
    · congr 1
    · simp only [Fin.val_last]
      omega
  have hψ :
      ψ (fun k => g ⟨(Fin.natAdd (r + 1) k : ℕ), by omega⟩) =
        ψ (fun i => g ⟨(Fin.natAdd r i.succ : ℕ), by omega⟩) := by
    apply congrArg ψ
    funext i
    congr 1
    apply Fin.ext
    simp only [Fin.natAdd, Fin.val_succ]
    omega
  have hp :
      Fin.partialProd g ⟨r + 1, by omega⟩ =
        Fin.partialProd g ⟨r, by omega⟩ * g ⟨r, by omega⟩ := by
    exact Fin.partialProd_succ g ⟨r, by omega⟩
  rw [hφ, hψ, hp, ← rep_action_mul]
  have hi :
      (⟨r, by omega⟩ : Fin (r + s + 1)) =
        ⟨(Fin.natAdd r (0 : Fin (s + 1)) : ℕ), by omega⟩ := by
    apply Fin.ext
    simp [Fin.natAdd]
  rw [hi]
  rw [int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2,
    int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2,
    ← add_smul, neg_succ_self, zero_smul]

theorem cup_right_face (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (g : Fin (r + s + 1) → G) (k : Fin (s + 1)) :
    (M ⊗ N : Rep ℤ G).hV2.smul
        ((-1 : ℤ) ^ ((rightIndex (r := r) k : ℕ) + 1))
        (cochainCup M N r s φ ψ
          (Fin.contractNth (rightIndex (r := r) k) (· * ·) g)) =
      (M ⊗ N : Rep ℤ G).hV2.smul ((-1 : ℤ) ^ r)
        (tensorElement M N
          (φ fun i => tupleCast (by omega : r + s + 1 = r + (s + 1)) g
            (Fin.castAdd (s + 1) i))
          (N.ρ (initialProduct r (s + 1)
              (tupleCast (by omega : r + s + 1 = r + (s + 1)) g))
            (N.hV2.smul ((-1 : ℤ) ^ ((k : ℕ) + 1))
              (ψ (Fin.contractNth k (· * ·)
                (fun j => tupleCast (by omega : r + s + 1 = r + (s + 1)) g
                  (Fin.natAdd r j))))))) := by
  simp only [cochainCup, tupleCast_apply, initial_tuple_cast]
  rw [rep_action_smul, tensor_rep_smul, rep_smul_smul,
    neg_right_index]
  have hφ :
      φ (fun i => Fin.contractNth (rightIndex (r := r) k) (· * ·) g
          (Fin.castAdd s i)) =
        φ (fun i => g ⟨(Fin.castAdd (s + 1) i : ℕ), by omega⟩) := by
    apply congrArg φ
    calc
      (fun i => Fin.contractNth (rightIndex (r := r) k) (· * ·) g
          (Fin.castAdd s i)) = prefixTuple g :=
        contract_right_prefix (· * ·) g k
      _ = _ := by
        funext i
        congr 1
  have hψ :
      ψ (fun i => Fin.contractNth (rightIndex (r := r) k) (· * ·) g
          (Fin.natAdd r i)) =
        ψ (Fin.contractNth k (· * ·)
          (fun j => g ⟨(Fin.natAdd r j : ℕ), by omega⟩)) := by
    apply congrArg ψ
    calc
      (fun i => Fin.contractNth (rightIndex (r := r) k) (· * ·) g
          (Fin.natAdd r i)) = Fin.contractNth k (· * ·) (suffixSucc g) :=
        contract_right_suffix (· * ·) g k
      _ = _ := by
        congr 1
  have hp :
      initialProduct r s
          (Fin.contractNth (rightIndex (r := r) k) (· * ·) g) =
        Fin.partialProd g ⟨r, by omega⟩ := by
    exact partial_contract_right g k
  rw [hφ, hp, hψ]

/-- The inhomogeneous cup formula satisfies the graded Leibniz identity. -/
theorem cochainCup_d (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s φ ψ) =
      cochainCast (by omega : (r + s) + 1 = (r + 1) + s)
          (cochainCup M N (r + 1) s
            (cochainDifferential M r φ) ψ) +
        (-1 : ℤ) ^ r •
          cochainCast (by omega : (r + s) + 1 = r + (s + 1))
            (cochainCup M N r (s + 1) φ
              (cochainDifferential N s ψ)) := by
  ext g
  simp only [cochainDifferential_apply, Pi.add_apply, Pi.smul_apply, cochainCast]
  rw [sum_faces_two (r := r) (s := s)]
  simp only [cochainCup, tensorElement_action, cochainDifferential_apply,
    map_add, element_add_left, tupleCast_apply,
    initial_tuple_cast]
  simp only [Fin.val_succ, Fin.natAdd, Fin.castAdd]
  simp only [Fin.sum_univ_castSucc,
    element_add_left, tensor_sum_left]
  simp only [map_add, rep_action_sum, rep_action_smul,
    tensor_element_add, tensor_element_sum,
    tensor_element_rep, tensor_rep_smul]
  have ha := cup_action_term M N r s φ ψ g
  simp only [cochainCup, tensorElement_action, tupleCast_apply,
    initial_tuple_cast, Fin.natAdd, Fin.castAdd] at ha
  rw [ha]
  have hl := congrArg
    (fun f : Fin r → (M ⊗ N : Rep ℤ G) => ∑ j, f j)
    (funext fun j => cup_left_face M N r s φ ψ g j)
  simp only [cochainCup, tupleCast_apply, initial_tuple_cast,
    Fin.natAdd, Fin.castAdd] at hl
  conv_lhs =>
    congr
    · skip
    · congr
      · change ∑ x, (M ⊗ N : Rep ℤ G).hV2.smul _ _
        rw [hl]
      · skip
  have hr := congrArg
    (fun f : Fin (s + 1) → (M ⊗ N : Rep ℤ G) => ∑ k, f k)
    (funext fun k => cup_right_face M N r s φ ψ g k)
  simp only [cochainCup, tupleCast_apply, initial_tuple_cast,
    Fin.natAdd, Fin.castAdd, Fin.sum_univ_castSucc] at hr
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      · change
          (∑ i, (M ⊗ N : Rep ℤ G).hV2.smul _ _) +
            (M ⊗ N : Rep ℤ G).hV2.smul _ _
        rw [hr]
  have hc := cup_cancel_terms M N r s φ ψ g
  simp only [tupleCast_apply, initial_tuple_cast,
    Fin.val_succ, Fin.natAdd, Fin.castAdd] at hc
  simp only [smul_add, Finset.smul_sum]
  simp only [Nat.add_assoc] at hc ⊢
  simp only [rep_action_smul, tensor_rep_smul] at hc ⊢
  simp only [tensor_element_rep] at hc ⊢
  simp only [int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2] at hc ⊢
  abel_nf at hc ⊢
  conv_rhs => rw [← add_assoc]
  rw [hc, zero_add]

end Towers.CField.COps.CPBuild
