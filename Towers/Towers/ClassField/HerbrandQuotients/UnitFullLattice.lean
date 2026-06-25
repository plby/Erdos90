import Towers.ClassField.HerbrandQuotients.UnitLogDiscrete

/-!
# The full logarithmic lattice in Proposition VII.3.1

Discreteness identifies the real dimension of the span of `M⁰` with its
integral rank.  The `T`-unit rank theorem makes this a codimension-one
subspace, and the product formula shows that the constant vector is outside
it.  Hence `M = M⁰ + ℤe` is a full real lattice.
-/

namespace Towers.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped TensorProduct

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Adding the constant vector to the real span of `M⁰` fills the ambient
function space. -/
theorem upper_log_top
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Submodule.span ℝ
        (upperLogLattice (K := K) (L := L) S :
          Set (upperPlacesAt (K := K) (L := L) S → ℝ)) ⊔
      ℝ ∙ upperConstantVector (K := K) (L := L) S = ⊤ := by
  let T := upperPlacesAt (K := K) (L := L) S
  letI : Fintype T := Fintype.ofFinite T
  let M0 := upperLogLattice (K := K) (L := L) S
  let W : Submodule ℝ (T → ℝ) := Submodule.span ℝ (M0 : Set (T → ℝ))
  let e : T → ℝ := upperConstantVector (K := K) (L := L) S
  letI : Module.Finite ℤ M0 :=
    log_lattice_module (K := K) (L := L) S
  have hdiscM0 : DiscreteTopology M0 :=
    lattice_discrete_topology (K := K) (L := L) S hSinf
  have hdiscSpan : DiscreteTopology
      (Submodule.span ℤ (M0 : Set (T → ℝ))) := by
    rw [M0.span_eq]
    exact hdiscM0
  have hWrankInt : Module.finrank ℝ W = Module.finrank ℤ M0 := by
    have h := Real.finrank_eq_int_finrank_of_discrete
      (s := (M0 : Set (T → ℝ))) hdiscSpan
    change
      Module.finrank ℝ (Submodule.span ℝ (M0 : Set (T → ℝ))) =
        Module.finrank ℤ (Submodule.span ℤ (M0 : Set (T → ℝ))) at h
    rw [M0.span_eq] at h
    simpa only [W] using h
  have hWrank : Module.finrank ℝ W = Nat.card T - 1 := by
    rw [hWrankInt]
    exact log_lattice_finrank
      (K := K) (L := L) S hSinf
  have hVrank : Module.finrank ℝ (T → ℝ) = Nat.card T :=
    upper_function_space (K := K) (L := L) S
  let placeEquiv := upperPlacesInfinite
    (K := K) (L := L) S hSinf
  let w0 : InfinitePlace L := Classical.choice inferInstance
  letI : Nonempty T := ⟨placeEquiv.symm (Sum.inr w0)⟩
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hquotient : Module.finrank ℝ ((T → ℝ) ⧸ W) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank W
    rw [hWrank, hVrank] at h
    omega
  change W ⊔ ℝ ∙ e = ⊤
  exact (Submodule.sup_span_singleton_eq_top_iff
    (upper_log_real
      (K := K) (L := L) S hSinf)).mpr hquotient

/-- The real span of the integral augmented lattice is the entire ambient
space. -/
theorem augmented_lattice_top
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Submodule.span ℝ
        (upperAugmentedLattice (K := K) (L := L) S :
          Set (upperPlacesAt (K := K) (L := L) S → ℝ)) = ⊤ := by
  let M0 := upperLogLattice (K := K) (L := L) S
  let e := upperConstantVector (K := K) (L := L) S
  let W : Submodule ℝ
      (upperPlacesAt (K := K) (L := L) S → ℝ) :=
    Submodule.span ℝ (M0 : Set _)
  have hsup : W ⊔ ℝ ∙ e = ⊤ :=
    upper_log_top
      (K := K) (L := L) S hSinf
  rw [← hsup]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left (Submodule.subset_span ha)
    · apply Submodule.mem_sup_right
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hb
      apply Submodule.mem_span_singleton.mpr
      refine ⟨(n : ℝ), ?_⟩
      funext t
      simp [e, upperConstantVector]
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      apply Submodule.subset_span
      exact Submodule.mem_sup_left hx
    · apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      apply Submodule.subset_span
      apply Submodule.mem_sup_right
      exact Submodule.mem_span_singleton_self e

/-- Addition maps the external product `M⁰ × ℤ` to the internal augmented
lattice `M⁰ + ℤe`. -/
noncomputable def upperLogAugmented
    (S : Finset (NumberFieldPlace K)) :
    (upperLogLattice (K := K) (L := L) S × ℤ) →ₗ[ℤ]
      upperAugmentedLattice (K := K) (L := L) S where
  toFun x := ⟨(x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
      x.2 • upperConstantVector (K := K) (L := L) S, by
        apply Submodule.add_mem
        · exact Submodule.mem_sup_left x.1.property
        · exact Submodule.mem_sup_right
            (Submodule.smul_mem _ x.2
              (Submodule.mem_span_singleton_self
                (upperConstantVector (K := K) (L := L) S)))⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Pi.add_apply, Pi.mul_apply, Int.cast_add, zsmul_eq_mul]
    ring
  map_smul' n x := by
    apply Subtype.ext
    change
      n • (x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
          (n * x.2) • upperConstantVector (K := K) (L := L) S =
        n • ((x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
          x.2 • upperConstantVector (K := K) (L := L) S)
    rw [smul_add, mul_smul]

/-- The product-formula functional vanishes on every member of `M⁰`. -/
theorem upper_log_lattice
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (x : upperLogLattice (K := K) (L := L) S) :
    upperPlaceLog (K := K) (L := L) S hSinf x = 0 := by
  obtain ⟨a, ha⟩ := x.property
  rw [← ha]
  exact upper_log_linear
    (K := K) (L := L) S hSinf a

/-- The external-to-internal addition map is bijective.  Surjectivity is
the definition of the supremum; injectivity follows from the product
formula, which kills `M⁰` and is positive on `e`. -/
theorem log_augmented_bijective
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Function.Bijective
      (upperLogAugmented
        (K := K) (L := L) S) := by
  let ℓ := upperPlaceLog (K := K) (L := L) S hSinf
  let e := upperConstantVector (K := K) (L := L) S
  constructor
  · intro x y hxy
    have hxyval :
        ((upperLogAugmented
            (K := K) (L := L) S x :
              upperAugmentedLattice (K := K) (L := L) S) :
            upperPlacesAt (K := K) (L := L) S → ℝ) =
          ((upperLogAugmented
            (K := K) (L := L) S y :
              upperAugmentedLattice (K := K) (L := L) S) :
            upperPlacesAt (K := K) (L := L) S → ℝ) :=
      congrArg Subtype.val hxy
    have hxy' := congrArg ℓ hxyval
    have hx0 : ℓ (x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) = 0 :=
      upper_log_lattice
        (K := K) (L := L) S hSinf x.1
    have hy0 : ℓ (y.1 : upperPlacesAt (K := K) (L := L) S → ℝ) = 0 :=
      upper_log_lattice
        (K := K) (L := L) S hSinf y.1
    have he0 : ℓ e ≠ 0 := ne_of_gt
      (upper_log_pos
        (K := K) (L := L) S hSinf)
    have hnreal : (x.2 : ℝ) = (y.2 : ℝ) := by
      have hscaled :
          (x.2 : ℝ) * ℓ e = (y.2 : ℝ) * ℓ e := by
        change ℓ ((x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
            x.2 • e) =
          ℓ ((y.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
            y.2 • e) at hxy'
        rw [map_add, map_add, hx0, hy0, map_zsmul, map_zsmul] at hxy'
        simpa only [zero_add, zsmul_eq_mul] using hxy'
      exact mul_right_cancel₀ he0 hscaled
    have hn : x.2 = y.2 := by exact_mod_cast hnreal
    apply Prod.ext
    · apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      change
        (x.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
            x.2 • e =
          (y.1 : upperPlacesAt (K := K) (L := L) S → ℝ) +
            y.2 • e at hval
      rw [hn] at hval
      exact add_right_cancel hval
    · exact hn
  · rintro ⟨z, hz⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨(⟨a, ha⟩, n), ?_⟩
    apply Subtype.ext
    exact hab

private theorem full_lattice_realization
    {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V) [Module.Finite ℤ M]
    (hrank : Module.finrank ℤ M = Module.finrank ℝ V)
    (hspan : Submodule.span ℝ (M : Set V) = ⊤) :
    Function.Bijective (fullLatticeRealization M) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  letI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  letI : Module.IsTorsionFree ℤ V := inferInstance
  letI : Module.IsTorsionFree ℤ M := inferInstance
  letI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  have heq : fullLatticeRealization M =
      (Submodule.subtype (Submodule.span ℝ (M : Set V))).comp
        (M.tensorToSpan ℝ) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul r m =>
        rw [lattice_realization_tmul]
        rfl
  have hsurj : Function.Surjective (fullLatticeRealization M) := by
    rw [heq]
    intro v
    have hv : v ∈ Submodule.span ℝ (M : Set V) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨z, hz⟩ := M.surjective_tensorToSpan ℝ ⟨v, hv⟩
    refine ⟨z, ?_⟩
    exact congrArg Subtype.val hz
  have hfinrank :
      Module.finrank ℝ (ℝ ⊗[ℤ] M) = Module.finrank ℝ V := by
    rw [Module.finrank_baseChange, hrank]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hfinrank).mpr hsurj, hsurj⟩

/-- Milne's augmented logarithmic lattice `M = M⁰ + ℤe` is a full real
lattice. -/
theorem augmented_lattice_real
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    FullRealLattice
      (upperAugmentedLattice (K := K) (L := L) S) := by
  letI : Module.Finite ℤ
      (upperAugmentedLattice (K := K) (L := L) S) :=
    upper_augmented_lattice (K := K) (L := L) S
  let T := upperPlacesAt (K := K) (L := L) S
  let M0 := upperLogLattice (K := K) (L := L) S
  let M := upperAugmentedLattice (K := K) (L := L) S
  letI : Module.Finite ℤ M0 :=
    log_lattice_module (K := K) (L := L) S
  let productEquiv : (M0 × ℤ) ≃ₗ[ℤ] M :=
    LinearEquiv.ofBijective
      (upperLogAugmented
        (K := K) (L := L) S)
      (log_augmented_bijective
        (K := K) (L := L) S hSinf)
  let placeEquiv := upperPlacesInfinite
    (K := K) (L := L) S hSinf
  let w0 : InfinitePlace L := Classical.choice inferInstance
  letI : Nonempty T := ⟨placeEquiv.symm (Sum.inr w0)⟩
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hrank : Module.finrank ℤ M = Module.finrank ℝ (T → ℝ) := by
    calc
      Module.finrank ℤ M = Module.finrank ℤ (M0 × ℤ) :=
        productEquiv.finrank_eq.symm
      _ = Module.finrank ℤ M0 + Module.finrank ℤ ℤ :=
        Module.finrank_prod
      _ = (Nat.card T - 1) + 1 := by
        rw [log_lattice_finrank
          (K := K) (L := L) S hSinf, Module.finrank_self]
      _ = Nat.card T := by omega
      _ = Module.finrank ℝ (T → ℝ) :=
        (upper_function_space (K := K) (L := L) S).symm
  exact ⟨inferInstance,
    full_lattice_realization
      (upperAugmentedLattice (K := K) (L := L) S)
      hrank
      (augmented_lattice_top
        (K := K) (L := L) S hSinf)⟩

end

end Towers.CField.HQuotie
