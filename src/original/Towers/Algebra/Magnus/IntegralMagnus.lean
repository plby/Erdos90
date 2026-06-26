import Towers.Algebra.Magnus.GroupAlgebraWeighted
import Towers.Group.HallBasic.StandardSequence


/-!
# The integral graded Magnus map

For a finite free basis, the Hall PBW theorem gives a basis of every
lower-central associated-graded layer. Its image under the integral Magnus
map is linearly independent in the corresponding augmentation layer. This
proves injectivity of the graded Magnus map and the integral
Magnus--Witt dimension-subgroup converse.
-/

namespace EChapma
namespace IMagnus

open Towers
open Towers.TBluepr

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

/-- A linear map is injective if it sends some basis to a linearly
independent family. -/
theorem linear_image_independent
    {R M N ι : Type*}
    [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M)
    (f : M →ₗ[R] N)
    (h :
      LinearIndependent R (fun i => f (b i))) :
    Function.Injective f := by
  intro x y hxy
  apply b.repr.injective
  apply h.finsuppLinearCombination_injective
  have heval (z : M) :
      Finsupp.linearCombination R (fun i => f (b i)) (b.repr z) =
        f z := by
    calc
      Finsupp.linearCombination R (fun i => f (b i)) (b.repr z) =
          f (Finsupp.linearCombination R b (b.repr z)) := by
            simp [Finsupp.linearCombination_apply, map_finsuppSum]
      _ = f z := by rw [b.linearCombination_repr]
  rw [heval, heval, hxy]

/-- A linear map is injective if a spanning family has linearly independent
images. -/
theorem top_image_independent
    {R M N ι : Type*}
    [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (v : ι → M)
    (hspan : Submodule.span R (Set.range v) = ⊤)
    (himage : LinearIndependent R (fun i => f (v i))) :
    Function.Injective f := by
  let b : Module.Basis ι R M :=
    Module.Basis.mk (LinearIndependent.of_comp f himage) hspan.ge
  apply linear_image_independent b f
  simpa only [b, Module.Basis.mk_apply] using himage

/-- The unconditional integral Hall PBW uniqueness input supplied by the
ordered foliage factorization theorem. -/
noncomputable def hallPBWInput :
    Towers.HallTree.HPUniq (α := X) ℤ :=
  Towers.HallTree.foliageFactorizationInput.pbwUniquenessInt

/-- The Hall basis of the zero-based lower-central layer
`γ_(n+1)(F)/γ_(n+2)(F)`. -/
noncomputable def lowerCentralBasis (n : ℕ) :
    Module.Basis
      (Towers.HallTree.BasicIndex (α := X) (n + 1)) ℤ
      (Additive
        (LowerGradedLayer (FreeGroup X) n)) :=
  Towers.HallTree.freePBWUniqueness
    (hallPBWInput (X := X)) (Nat.succ_pos n)

/-- The images of the indexed basic Hall classes under the fixed-weight
integral Magnus map are linearly independent. -/
theorem indexed_magnus_independent
    (n : ℕ) :
    LinearIndependent ℤ
      (fun i : Towers.HallTree.BasicIndex (α := X) (n + 1) =>
        Towers.HallTree.freeMagnusInt
            X (Nat.succ_pos n)
          ((Towers.HallTree.indexedBasicTree i).freeLowerWeight
            (Towers.HallTree.indexed_tree_weight i))) := by
  let P := hallPBWInput (X := X)
  have hpoly :=
    P.indexedbasic_treeword_polylinindep ℤ
      (r := n + 1)
  have hrealized :=
    Towers.HallTree.associative_realization_independent
      ℤ
      (tree := fun i : Towers.HallTree.BasicIndex (α := X) (n + 1) =>
        Towers.HallTree.indexedBasicTree i)
      (hweight := fun i =>
        Towers.HallTree.indexed_tree_weight i)
      hpoly
  convert hrealized using 1
  funext i
  exact
    Towers.HallTree.free_magnus_int
      (Nat.succ_pos n)
      (Towers.HallTree.indexedBasicTree i)
      (Towers.HallTree.indexed_tree_weight i)

omit [Fintype X] [DecidableEq X] in
/-- The fixed-weight integral Magnus map is injective. -/
theorem magnus_int_injective
    [Finite X]
    (n : ℕ) :
    Function.Injective
      (Towers.HallTree.freeMagnusInt
        X (Nat.succ_pos n)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  apply top_image_independent
    (Towers.HallTree.freeMagnusInt
      X (Nat.succ_pos n))
    (fun i : Towers.HallTree.BasicIndex (α := X) (n + 1) =>
      (Towers.HallTree.indexedBasicTree i).freeLowerWeight
        (Towers.HallTree.indexed_tree_weight i))
  · exact
      Towers.HallTree.indexed_basic_top
        (Nat.succ_pos n)
  · exact indexed_magnus_independent (X := X) n

omit [Fintype X] [DecidableEq X] in
/-- Every zero-based integral lower-central graded Magnus map is injective. -/
theorem associated_graded_injective
    [Finite X]
    (n : ℕ) :
    Function.Injective
      (associatedGradedMagnus
        (FreeGroup X) n) := by
  intro x y hxy
  apply
    magnus_int_injective
      (X := X) n
  change
    GroupAlgebra.augmentationLayerReindex ℤ (FreeGroup X)
        (Nat.sub_add_cancel (Nat.succ_pos n))
        (associatedGradedMagnus
          (FreeGroup X) n x) =
      GroupAlgebra.augmentationLayerReindex ℤ (FreeGroup X)
        (Nat.sub_add_cancel (Nat.succ_pos n))
        (associatedGradedMagnus
          (FreeGroup X) n y)
  rw [hxy]

omit [Fintype X] [DecidableEq X] in
/-- If an element of `γ_(n+1)` has augmentation difference one degree
deeper, it belongs to `γ_(n+2)`. -/
theorem lower_series_pow
    [Finite X]
    (n : ℕ) {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) n)
    (haug :
      MonoidAlgebra.of ℤ (FreeGroup X) g - 1 ∈
        Towers.GroupAlgebra.augmentationIdeal ℤ (FreeGroup X) ^ (n + 2)) :
    g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (n + 1) := by
  let x : Subgroup.lowerCentralSeries (FreeGroup X) n := ⟨g, hg⟩
  let q :
      Additive
        (LowerGradedLayer (FreeGroup X) n) :=
    Additive.ofMul
      (QuotientGroup.mk'
        ((Subgroup.lowerCentralSeries (FreeGroup X) (n + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup X) n)) x)
  have hmap :
      associatedGradedMagnus
          (FreeGroup X) n q =
        0 := by
    simp only [q, associated_graded_mk]
    rw [Submodule.Quotient.mk_eq_zero]
    exact haug
  have hq :
      q = 0 :=
    associated_graded_injective
      (X := X) n (hmap.trans (map_zero _).symm)
  have hquot :
      QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries (FreeGroup X) (n + 1)).subgroupOf
            (Subgroup.lowerCentralSeries (FreeGroup X) n)) x =
        1 := by
    apply Additive.ofMul.injective
    exact hq
  exact
    (QuotientGroup.eq_one_iff
      (N :=
        (Subgroup.lowerCentralSeries (FreeGroup X) (n + 1)).subgroupOf
          (Subgroup.lowerCentralSeries (FreeGroup X) n))
      x).mp hquot

omit [Fintype X] [DecidableEq X] in
/-- Integral Magnus--Witt dimension-subgroup converse:
`g - 1 ∈ I^(n+1)` implies `g ∈ γ_(n+1)(F)`. -/
theorem lower_central_pow
    [Finite X]
    (n : ℕ) {g : FreeGroup X}
    (haug :
      MonoidAlgebra.of ℤ (FreeGroup X) g - 1 ∈
        Towers.GroupAlgebra.augmentationIdeal ℤ (FreeGroup X) ^ (n + 1)) :
    g ∈ Subgroup.lowerCentralSeries (FreeGroup X) n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      apply lower_series_pow
        (X := X) n
      · apply ih
        exact Ideal.pow_le_pow_right (by omega) haug
      · simpa [Nat.add_assoc] using haug

end IMagnus
end EChapma
