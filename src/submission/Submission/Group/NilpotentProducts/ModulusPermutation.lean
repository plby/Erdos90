import Submission.Group.NilpotentProducts.GeneralResidues
import Mathlib.Order.Hom.PowersetCard


/-!
# Permutation invariance of equation-(18) coordinate moduli
-/

namespace Struik
namespace P1960

private def pairOrderEmbedding (t : ℕ) :
    Pair t ≃ (Fin 2 ↪o Fin t) := by
  let toOrderEmbedding : Pair t → (Fin 2 ↪o Fin t) :=
    fun q =>
      OrderEmbedding.ofStrictMono
        (fun i => Fin.cases q.i (fun _ => q.j) i)
        (by
          intro i j hij
          fin_cases i
          · fin_cases j
            · omega
            · simpa using q.lt
          · fin_cases j <;> norm_num at hij)
  let fromOrderEmbedding : (Fin 2 ↪o Fin t) → Pair t :=
    fun f => ⟨f 0, f 1, f.strictMono (by decide)⟩
  exact {
    toFun := toOrderEmbedding
    invFun := fromOrderEmbedding
    left_inv := by
      intro q
      cases q
      rfl
    right_inv := by
      intro f
      ext i
      fin_cases i <;> rfl }

private def tripleOrderEmbedding (t : ℕ) :
    Triple t ≃ (Fin 3 ↪o Fin t) := by
  let toOrderEmbedding : Triple t → (Fin 3 ↪o Fin t) :=
    fun q =>
      OrderEmbedding.ofStrictMono
        (fun i =>
          Fin.cases q.i
            (fun j => Fin.cases q.j (fun _ => q.k) j) i)
        (by
          intro i j hij
          fin_cases i
          · fin_cases j
            · omega
            · simpa using q.lt_ij
            · simpa using q.lt_ij.trans q.lt_jk
          · fin_cases j
            · norm_num at hij
            · norm_num at hij
            · simpa using q.lt_jk
          · fin_cases j <;> norm_num at hij)
  let fromOrderEmbedding : (Fin 3 ↪o Fin t) → Triple t :=
    fun f =>
      ⟨f 0, f 1, f 2,
        f.strictMono (by decide), f.strictMono (by decide)⟩
  exact {
    toFun := toOrderEmbedding
    invFun := fromOrderEmbedding
    left_inv := by
      intro q
      cases q
      rfl
    right_inv := by
      intro f
      ext i
      fin_cases i <;> rfl }

/-- Increasing pairs are the same as two-element subsets. -/
noncomputable def pairPowersetEquiv (t : ℕ) :
    Pair t ≃ Set.powersetCard (Fin t) 2 :=
  (pairOrderEmbedding t).trans
    Set.powersetCard.ofFinEmbEquiv

/-- Increasing triples are the same as three-element subsets. -/
noncomputable def triplePowersetEquiv (t : ℕ) :
    Triple t ≃ Set.powersetCard (Fin t) 3 :=
  (tripleOrderEmbedding t).trans
    Set.powersetCard.ofFinEmbEquiv

private theorem pair_powerset_val
    {t : ℕ} (q : Pair t) :
    (pairPowersetEquiv t q).val = {q.i, q.j} := by
  ext x
  change
    x ∈ Set.powersetCard.ofFinEmbEquiv
        (pairOrderEmbedding t q) ↔
      x ∈ ({q.i, q.j} : Finset (Fin t))
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change q.i ∈ ({q.i, q.j} : Finset (Fin t))
      simp
    · change q.j ∈ ({q.i, q.j} : Finset (Fin t))
      simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · refine ⟨0, ?_⟩
      rfl
    · refine ⟨1, ?_⟩
      change q.j = q.j
      rfl

private theorem triple_powerset_val
    {t : ℕ} (q : Triple t) :
    (triplePowersetEquiv t q).val =
      {q.i, q.j, q.k} := by
  ext x
  change
    x ∈ Set.powersetCard.ofFinEmbEquiv
        (tripleOrderEmbedding t q) ↔
      x ∈ ({q.i, q.j, q.k} : Finset (Fin t))
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · change q.i ∈ ({q.i, q.j, q.k} : Finset (Fin t))
      simp
    · change q.j ∈ ({q.i, q.j, q.k} : Finset (Fin t))
      simp
    · change q.k ∈ ({q.i, q.j, q.k} : Finset (Fin t))
      simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨0, ?_⟩
      simp [tripleOrderEmbedding]
    · refine ⟨1, ?_⟩
      change q.j = q.j
      rfl
    · refine ⟨2, ?_⟩
      change q.k = q.k
      rfl

@[simp] theorem pair_powerset_gcd
    {t : ℕ} (order : Fin t → ℕ) (q : Pair t) :
    (pairPowersetEquiv t q).val.gcd order =
      generalPairModulus order q := by
  rw [pair_powerset_val]
  simp [generalPairModulus, gcd_eq_nat_gcd]

@[simp] theorem exceptional_powerset_gcd
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (triplePowersetEquiv t q).val.gcd order =
      generalResiduesModulus order q := by
  rw [triple_powerset_val]
  simp [generalResiduesModulus, gcd_eq_nat_gcd,
    Nat.gcd_assoc]

/-- An equivalence maps fixed-cardinality subsets bijectively. -/
def powersetCardCongr
    {α β : Type*} (e : α ≃ β) (n : ℕ) :
    Set.powersetCard α n ≃ Set.powersetCard β n where
  toFun := Set.powersetCard.map n e.toEmbedding
  invFun := Set.powersetCard.map n e.symm.toEmbedding
  left_inv s := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]
  right_inv s := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]

@[simp] theorem powerset_congr_gcd
    {α β : Type*}
    (e : α ≃ β) (n : ℕ) (f : β → ℕ)
    (s : Set.powersetCard α n) :
    (powersetCardCongr e n s).val.gcd f =
      s.val.gcd (f ∘ e) := by
  classical
  change
    (Set.powersetCard.map n e.toEmbedding s).val.gcd f =
      s.val.gcd (f ∘ e)
  rw [Set.powersetCard.val_map,
    Finset.map_eq_image, Finset.gcd_image]
  rfl

theorem powerset_gcd_comp
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (n : ℕ) (f : β → ℕ) :
    (∏ s : Set.powersetCard α n, s.val.gcd (f ∘ e)) =
      ∏ s : Set.powersetCard β n, s.val.gcd f := by
  classical
  rw [← (powersetCardCongr e n).prod_comp
    (fun s => s.val.gcd f)]
  simp

end P1960
end Struik
