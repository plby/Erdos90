import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Milne, Class Field Theory, Proposition II.1.38: cochain formula

This file starts the construction of the group-cohomology cup product with
the exact inhomogeneous-cochain formula in Milne's proof.  The subsequent
step is the graded Leibniz identity, which makes this operation descend to
cohomology.
-/

namespace Submission.CField.COps.CPBuild

open CategoryTheory
open scoped MonoidalCategory TensorProduct

universe u

variable {G : Type u} [Group G]

/-- Reindex a tuple along an equality of its lengths.  Keeping this transport
named prevents associativity casts such as `(r+s)+1 = (r+1)+s` from obscuring
the cup-product identities. -/
def tupleCast {m n : ℕ} (h : m = n) (g : Fin m → G) : Fin n → G :=
  g ∘ Fin.cast h.symm

omit [Group G] in
@[simp]
theorem tupleCast_rfl {n : ℕ} (g : Fin n → G) :
    tupleCast rfl g = g := by
  rfl

omit [Group G] in
@[simp]
theorem tupleCast_apply {m n : ℕ} (h : m = n) (g : Fin m → G) (i : Fin n) :
    tupleCast h g i = g ⟨i, by omega⟩ := by
  unfold tupleCast
  congr 1

/-- Reindex an inhomogeneous cochain along an equality of degrees. -/
def cochainCast {A : Type*} {m n : ℕ} (h : m = n)
    (φ : (Fin n → G) → A) : (Fin m → G) → A :=
  fun g => φ (tupleCast h g)

omit [Group G] in
@[simp]
theorem cochainCast_rfl {A : Type*} {n : ℕ} (φ : (Fin n → G) → A) :
    cochainCast rfl φ = φ := by
  rfl

/-- The ordered product `g₁⋯gᵣ` of the first `r` entries of an
`(r+s)`-tuple. `Fin.partialProd` preserves the order because `G` need not be
commutative. -/
def initialProduct (r s : ℕ) (g : Fin (r + s) → G) : G :=
  Fin.partialProd g ⟨r, by omega⟩

@[simp]
theorem initialProduct_zero (s : ℕ) (g : Fin (0 + s) → G) :
    initialProduct 0 s g = 1 := by
  simp [initialProduct]

/-- A pure tensor in the underlying module of the tensor product
representation.  The explicit local instances ensure that the tensor product
uses the module structures stored in `M` and `N`. -/
def tensorElement (M N : Rep ℤ G) (m : M) (n : N) : (M ⊗ N : Rep ℤ G) := by
  letI := M.hV2
  letI := N.hV2
  exact m ⊗ₜ[ℤ] n

@[simp]
theorem tensor_element_zero (M N : Rep ℤ G) (n : N) :
    tensorElement M N 0 n = 0 := by
  letI := M.hV2
  letI := N.hV2
  change (0 : M) ⊗ₜ[ℤ] n = 0
  simp

@[simp]
theorem element_add_left (M N : Rep ℤ G) (m₁ m₂ : M) (n : N) :
    tensorElement M N (m₁ + m₂) n =
      tensorElement M N m₁ n + tensorElement M N m₂ n := by
  letI := M.hV2
  letI := N.hV2
  change (m₁ + m₂) ⊗ₜ[ℤ] n = m₁ ⊗ₜ[ℤ] n + m₂ ⊗ₜ[ℤ] n
  exact TensorProduct.add_tmul m₁ m₂ n

/-- Fixing the right tensor factor gives an additive homomorphism. -/
def tensorElementLeft (M N : Rep ℤ G) (n : N) :
    M →+ (M ⊗ N : Rep ℤ G) where
  toFun m := tensorElement M N m n
  map_zero' := tensor_element_zero M N n
  map_add' m₁ m₂ := element_add_left M N m₁ m₂ n

@[simp]
theorem tensor_sum_left {ι : Type*} (M N : Rep ℤ G)
    (t : Finset ι) (f : ι → M) (n : N) :
    tensorElement M N (∑ i ∈ t, f i) n =
      ∑ i ∈ t, tensorElement M N (f i) n :=
  map_sum (tensorElementLeft M N n) f t

@[simp]
theorem tensor_element_left (M N : Rep ℤ G) (a : ℤ) (m : M) (n : N) :
    tensorElement M N (a • m) n = a • tensorElement M N m n := by
  exact (tensorElementLeft M N n).map_zsmul a m

@[simp]
theorem tensor_element_rep (M N : Rep ℤ G) (a : ℤ) (m : M) (n : N) :
    tensorElement M N (M.hV2.smul a m) n =
      (M ⊗ N : Rep ℤ G).hV2.smul a (tensorElement M N m n) := by
  rw [int_smul_eq_zsmul M.hV2 a m,
    int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2 a (tensorElement M N m n)]
  exact tensor_element_left M N a m n

@[simp]
theorem tensor_element_right (M N : Rep ℤ G) (m : M) :
    tensorElement M N m 0 = 0 := by
  letI := M.hV2
  letI := N.hV2
  change m ⊗ₜ[ℤ] (0 : N) = 0
  simp

@[simp]
theorem tensor_element_add (M N : Rep ℤ G) (m : M) (n₁ n₂ : N) :
    tensorElement M N m (n₁ + n₂) =
      tensorElement M N m n₁ + tensorElement M N m n₂ := by
  letI := M.hV2
  letI := N.hV2
  change m ⊗ₜ[ℤ] (n₁ + n₂) = m ⊗ₜ[ℤ] n₁ + m ⊗ₜ[ℤ] n₂
  exact TensorProduct.tmul_add m n₁ n₂

/-- Fixing the left tensor factor gives an additive homomorphism. -/
def tensorElementRight (M N : Rep ℤ G) (m : M) :
    N →+ (M ⊗ N : Rep ℤ G) where
  toFun n := tensorElement M N m n
  map_zero' := tensor_element_right M N m
  map_add' n₁ n₂ := tensor_element_add M N m n₁ n₂

@[simp]
theorem tensor_element_sum {ι : Type*} (M N : Rep ℤ G)
    (t : Finset ι) (m : M) (f : ι → N) :
    tensorElement M N m (∑ i ∈ t, f i) =
      ∑ i ∈ t, tensorElement M N m (f i) :=
  map_sum (tensorElementRight M N m) f t

@[simp]
theorem tensor_element_smul (M N : Rep ℤ G) (a : ℤ) (m : M) (n : N) :
    tensorElement M N m (a • n) = a • tensorElement M N m n := by
  exact (tensorElementRight M N m).map_zsmul a n

@[simp]
theorem tensor_rep_smul (M N : Rep ℤ G) (a : ℤ) (m : M) (n : N) :
    tensorElement M N m (N.hV2.smul a n) =
      (M ⊗ N : Rep ℤ G).hV2.smul a (tensorElement M N m n) := by
  rw [int_smul_eq_zsmul N.hV2 a n,
    int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2 a (tensorElement M N m n)]
  exact tensor_element_smul M N a m n

@[simp]
theorem tensorElement_map
    {M N M' N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N')
    (m : M) (n : N) :
    (f ⊗ₘ g) (tensorElement M N m n) = tensorElement M' N' (f m) (g n) := by
  letI := M.hV2
  letI := N.hV2
  letI := M'.hV2
  letI := N'.hV2
  change (f.hom.tensor g.hom) (m ⊗ₜ[ℤ] n) = (f m) ⊗ₜ[ℤ] (g n)
  exact Representation.IntertwiningMap.tensor_apply f.hom g.hom m n

/-- The diagonal action on the tensor-product representation acts on both
pure tensor factors. -/
@[simp]
theorem tensorElement_action (M N : Rep ℤ G) (x : G) (m : M) (n : N) :
    (M ⊗ N : Rep ℤ G).ρ x (tensorElement M N m n) =
      tensorElement M N (M.ρ x m) (N.ρ x n) := by
  letI := M.hV2
  letI := N.hV2
  change TensorProduct.map (M.ρ x) (N.ρ x) (m ⊗ₜ[ℤ] n) =
    (M.ρ x m) ⊗ₜ[ℤ] (N.ρ x n)
  exact TensorProduct.map_tmul (M.ρ x) (N.ρ x) m n

/-- Multiplication in the group acts by composition.  This wrapper fixes the
module structure stored in a bundled representation, avoiding the competing
canonical integer-module instance. -/
@[simp]
theorem rep_action_mul (M : Rep ℤ G) (x y : G) (m : M) :
    M.ρ x (M.ρ y m) = M.ρ (x * y) m := by
  letI := M.hV2
  rw [← Module.End.mul_apply, ← M.ρ.map_mul]

@[simp]
theorem rep_action_sum {ι : Type*} (M : Rep ℤ G) (x : G)
    (t : Finset ι) (f : ι → M) :
    M.ρ x (∑ i ∈ t, f i) = ∑ i ∈ t, M.ρ x (f i) := by
  letI := M.hV2
  exact map_sum (M.ρ x) f t

@[simp]
theorem rep_action_smul (M : Rep ℤ G) (x : G) (a : ℤ) (m : M) :
    M.ρ x (M.hV2.smul a m) = M.hV2.smul a (M.ρ x m) := by
  letI := M.hV2
  exact (M.ρ x).map_smul a m

/-- Milne's inhomogeneous-cochain formula

`(φ ∪ ψ)(g₁,…,gᵣ₊ₛ) = φ(g₁,…,gᵣ) ⊗ (g₁⋯gᵣ) ψ(gᵣ₊₁,…,gᵣ₊ₛ)`.
-/
def cochainCup (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    (Fin (r + s) → G) → (M ⊗ N : Rep ℤ G) := fun g =>
  tensorElement M N (φ (fun i => g (Fin.castAdd s i)))
    (N.ρ (initialProduct r s g) (ψ fun j => g (Fin.natAdd r j)))

@[simp]
theorem cochain_cup_left (M N : Rep ℤ G) (r s : ℕ)
    (ψ : (Fin s → G) → N) :
    cochainCup M N r s 0 ψ = 0 := by
  ext g
  simp [cochainCup]

@[simp]
theorem cochain_add_left (M N : Rep ℤ G) (r s : ℕ)
    (φ₁ φ₂ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainCup M N r s (φ₁ + φ₂) ψ =
      cochainCup M N r s φ₁ ψ + cochainCup M N r s φ₂ ψ := by
  ext g
  simp [cochainCup]

@[simp]
theorem cochain_smul_left (M N : Rep ℤ G) (r s : ℕ)
    (a : ℤ) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainCup M N r s (a • φ) ψ = a • cochainCup M N r s φ ψ := by
  ext g
  simp [cochainCup]

@[simp]
theorem cochain_cup_right (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) :
    cochainCup M N r s φ 0 = 0 := by
  ext g
  simp [cochainCup]

@[simp]
theorem cochain_cup_add (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ₁ ψ₂ : (Fin s → G) → N) :
    cochainCup M N r s φ (ψ₁ + ψ₂) =
      cochainCup M N r s φ ψ₁ + cochainCup M N r s φ ψ₂ := by
  ext g
  simp [cochainCup]

@[simp]
theorem cochain_cup_smul (M N : Rep ℤ G) (r s : ℕ)
    (a : ℤ) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainCup M N r s φ (a • ψ) = a • cochainCup M N r s φ ψ := by
  ext g
  simp [cochainCup]

/-- The cup formula as a bilinear map on inhomogeneous cochains. -/
def cochainCupLinear (M N : Rep ℤ G) (r s : ℕ) :
    ((Fin r → G) → M) →ₗ[ℤ]
      ((Fin s → G) → N) →ₗ[ℤ]
        ((Fin (r + s) → G) → (M ⊗ N : Rep ℤ G)) where
  toFun φ :=
    { toFun := cochainCup M N r s φ
      map_add' := fun ψ₁ ψ₂ => cochain_cup_add M N r s φ ψ₁ ψ₂
      map_smul' := fun a ψ => cochain_cup_smul M N r s a φ ψ }
  map_add' φ₁ φ₂ := by
    ext ψ x
    exact congrFun (cochain_add_left M N r s φ₁ φ₂ ψ) x
  map_smul' a φ := by
    ext ψ x
    exact congrFun (cochain_smul_left M N r s a φ ψ) x

@[simp]
theorem cochain_cup_linear (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainCupLinear M N r s φ ψ = cochainCup M N r s φ ψ :=
  rfl

/-- In bidegree `(0,0)`, the cochain formula is the tensor product of the two
invariant candidates, exactly as required by Proposition II.1.38(b). -/
theorem cochain_cup_zero (M N : Rep ℤ G)
    (φ : (Fin 0 → G) → M) (ψ : (Fin 0 → G) → N)
    (g : Fin (0 + 0) → G) :
    cochainCup M N 0 0 φ ψ g =
      tensorElement M N (φ (fun i => i.elim0)) (ψ (fun i => i.elim0)) := by
  unfold cochainCup
  rw [initialProduct_zero]
  simp only [map_one]
  apply congrArg₂ (tensorElement M N)
  · apply congrArg φ
    funext i
    exact i.elim0
  · apply congrArg ψ
    funext i
    exact i.elim0

/-- The cochain formula is natural in both coefficient modules, which is the
cochain-level content of Proposition II.1.38(a). -/
theorem cochainCup_natural
    {M N M' N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N')
    (r s : ℕ) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    (fun x => (f ⊗ₘ g) (cochainCup M N r s φ ψ x)) =
      cochainCup M' N' r s (fun x => f (φ x)) (fun x => g (ψ x)) := by
  funext x
  simp only [cochainCup]
  rw [tensorElement_map, Rep.hom_comm_apply]

end Submission.CField.COps.CPBuild
