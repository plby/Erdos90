import Towers.ClassField.HerbrandQuotients.UnitFullLattice
import Towers.ClassField.HerbrandQuotients.HerbrandIsogeny
import Towers.ClassField.HerbrandQuotients.UnitLogLattice

/-!
# The Herbrand quotient of the logarithmic lattice in Proposition VII.3.1

The logarithmic map identifies the `T`-units with `M⁰` up to its finite
roots-of-unity kernel.  Adjoining the Galois-fixed constant vector then gives
a short exact sequence

`0 → M⁰ → M⁰ + ℤ e → ℤ → 0`.

The isogeny invariance from Lemma VII.3.4 and multiplicativity in this short
exact sequence give `h(M) = |G| h(U(T))`.
-/

namespace Towers.CField.HQuotie

open CategoryTheory CategoryTheory.Limits
open IsDedekindDomain NumberField Representation
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The equivariant logarithmic map, with its codomain restricted to its
actual image `M⁰`. -/
noncomputable def upperLogRep
    (S : Finset (NumberFieldPlace K)) :
    unitsPlacesRepresentation (K := K) (L := L) S ⟶
      stableLatticeRepresentation
        (placeFunctionRepresentation (K := K) (L := L) S)
        (upperLogLattice (K := K) (L := L) S)
        (log_lattice_stable (K := K) (L := L) S) :=
  Rep.ofHom {
    toLinearMap :=
      (upperUnitLog (K := K) (L := L) S).codRestrict
        (upperLogLattice (K := K) (L := L) S)
        (fun x ↦ ⟨x, rfl⟩)
    isIntertwining' := fun g ↦ by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (upper_log_equivariant
        (K := K) (L := L) S g x).symm }

omit [FiniteDimensional K L] in
@[simp]
theorem log_range_rep
    (S : Finset (NumberFieldPlace K))
    (x : unitsPlacesRepresentation (K := K) (L := L) S) :
    (upperLogRep (K := K) (L := L) S).hom x =
      ⟨upperUnitLog (K := K) (L := L) S x, ⟨x, rfl⟩⟩ :=
  rfl

omit [FiniteDimensional K L] in
/-- The equivariant logarithmic map is onto `M⁰` by its definition as a
range. -/
theorem log_rep_surjective
    (S : Finset (NumberFieldPlace K)) :
    Function.Surjective
      (upperLogRep (K := K) (L := L) S).hom := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

/-- The categorical kernel of the equivariant logarithmic map is finite. -/
theorem upper_log_rep
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Finite ↑(kernel (upperLogRep (K := K) (L := L) S) :
      Rep ℤ Gal(L/K)) := by
  let f := upperLogRep (K := K) (L := L) S
  let kerToLinearKer : ↑(kernel f : Rep ℤ Gal(L/K)) →
      LinearMap.ker (upperUnitLog (K := K) (L := L) S) :=
    fun x ↦ ⟨(kernel.ι f).hom x, by
      have h := congrArg (fun h : (kernel f ⟶ _) ↦ h.hom x)
        (kernel.condition f)
      exact Subtype.ext_iff.mp h⟩
  have hinj : Function.Injective kerToLinearKer := by
    intro x y hxy
    apply (Rep.mono_iff_injective (kernel.ι f)).mp inferInstance
    exact congrArg Subtype.val hxy
  letI : Finite
      (LinearMap.ker (upperUnitLog (K := K) (L := L) S)) :=
    upper_log_ker (K := K) (L := L) S hSinf
  exact Finite.of_injective kerToLinearKer hinj

omit [FiniteDimensional K L] in
/-- The categorical cokernel is zero (and hence finite), since the
logarithmic map has already been restricted to its range. -/
theorem log_rep_cokernel
    (S : Finset (NumberFieldPlace K)) :
    Finite ↑(cokernel (upperLogRep (K := K) (L := L) S) :
      Rep ℤ Gal(L/K)) := by
  let f := upperLogRep (K := K) (L := L) S
  letI : Epi f := (Rep.epi_iff_surjective f).mpr
    (log_rep_surjective (K := K) (L := L) S)
  have hzero : IsZero (cokernel f) := isZero_cokernel_of_epi f
  letI : Subsingleton ↑(cokernel f : Rep ℤ Gal(L/K)) := by
    constructor
    intro x y
    have hid : 𝟙 (cokernel f) = 0 :=
      (IsZero.iff_id_eq_zero (cokernel f)).mp hzero
    have hx := congrArg (fun h : cokernel f ⟶ cokernel f ↦ h.hom x) hid
    have hy := congrArg (fun h : cokernel f ⟶ cokernel f ↦ h.hom y) hid
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    exact hx0.trans hy0.symm
  infer_instance

/-- Passing from the `T`-units to their logarithmic image does not change
the Herbrand quotient: its kernel is precisely the finite torsion subgroup,
and its cokernel is zero. -/
theorem herbrand_log_lattice
    [Finite Gal(L/K)] [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (q : ℚ) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
        (unitsPlacesRepresentation (K := K) (L := L) S) q ↔
      HerbrandQuotientValue
        (stableLatticeRepresentation
          (placeFunctionRepresentation (K := K) (L := L) S)
          (upperLogLattice (K := K) (L := L) S)
          (log_lattice_stable (K := K) (L := L) S)) q := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  exact herbrandIsogenyBridge Gal(L/K)
    (unitsPlacesRepresentation (K := K) (L := L) S)
    (stableLatticeRepresentation
      (placeFunctionRepresentation (K := K) (L := L) S)
      (upperLogLattice (K := K) (L := L) S)
      (log_lattice_stable (K := K) (L := L) S))
    (upperLogRep (K := K) (L := L) S)
    (upper_log_rep
      (K := K) (L := L) S hSinf)
    (log_rep_cokernel (K := K) (L := L) S) q

private abbrev upperLiftedInt : Type u := ULift.{u, 0} ℤ

/-- The direct product of `M⁰` and a trivial integral line, before it is
identified with the internal sum `M⁰ + ℤe`. -/
noncomputable def upperLogRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep.{u, 0, u} ℤ Gal(L/K) :=
  let R0 := stableLatticeRepresentation
    (placeFunctionRepresentation (K := K) (L := L) S)
    (upperLogLattice (K := K) (L := L) S)
    (log_lattice_stable (K := K) (L := L) S)
  Rep.of {
    toFun := fun g ↦
      { toFun := fun x : R0 × upperLiftedInt ↦ (R0.ρ g x.1, x.2)
        map_add' := fun x y ↦ by
          apply Prod.ext
          · exact map_add (R0.ρ g) x.1 y.1
          · rfl
        map_smul' := fun n x ↦ by
          apply Prod.ext
          · exact map_smul (R0.ρ g) n x.1
          · rfl }
    map_one' := by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · simp
      · rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · simp
      · rfl }

/-- Include `M⁰` as the first factor of `M⁰ × ℤ`. -/
noncomputable def upperLogInclusion
    (S : Finset (NumberFieldPlace K)) :
    stableLatticeRepresentation
        (placeFunctionRepresentation (K := K) (L := L) S)
        (upperLogLattice (K := K) (L := L) S)
        (log_lattice_stable (K := K) (L := L) S) ⟶
      upperLogRepresentation (K := K) (L := L) S :=
  Rep.ofHom {
    toLinearMap := LinearMap.inl ℤ _ upperLiftedInt
    isIntertwining' := fun g ↦ by
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> rfl }

/-- Project `M⁰ × ℤ` onto its trivial second factor. -/
noncomputable def upperLogProjection
    (S : Finset (NumberFieldPlace K)) :
    upperLogRepresentation (K := K) (L := L) S ⟶
      Rep.trivial ℤ Gal(L/K) upperLiftedInt :=
  Rep.ofHom {
    toLinearMap := LinearMap.snd ℤ _ upperLiftedInt
    isIntertwining' := fun g ↦ by
      apply LinearMap.ext
      intro x
      rfl }

/-- The split sequence `0 → M⁰ → M⁰ × ℤ → ℤ → 0`. -/
noncomputable def logShortComplex
    (S : Finset (NumberFieldPlace K)) :
    ShortComplex (Rep.{u, 0, u} ℤ Gal(L/K)) :=
  ShortComplex.mk
    (upperLogInclusion (K := K) (L := L) S)
    (upperLogProjection (K := K) (L := L) S) (by
      apply Rep.hom_ext
      change
        (upperLogProjection (K := K) (L := L) S).hom.comp
            (upperLogInclusion (K := K) (L := L) S).hom = 0
      ext x
      rfl)

omit [FiniteDimensional K L] in
/-- The product sequence is short exact. -/
theorem short_complex_exact
    (S : Finset (NumberFieldPlace K)) :
    (logShortComplex
      (K := K) (L := L) S).ShortExact := by
  let X : ShortComplex (Rep.{u, 0, u} ℤ Gal(L/K)) :=
    logShortComplex (K := K) (L := L) S
  letI intRepModule (A : Rep.{u, 0, u} ℤ Gal(L/K)) : Module ℤ A := A.hV2
  let Fgt : Rep.{u, 0, u} ℤ Gal(L/K) ⥤ ModuleCat.{u} ℤ :=
    forget₂ (Rep.{u, 0, u} ℤ Gal(L/K)) (ModuleCat.{u} ℤ)
  apply ShortComplex.ShortExact.mk'
  · exact Fgt.reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff (X.map Fgt)).2 (fun x hx ↦ by
          change x.2 = 0 at hx
          refine ⟨x.1, ?_⟩
          apply Prod.ext
          · rfl
          · exact hx.symm)
  · rw [Rep.mono_iff_injective]
    exact fun _ _ h ↦ congrArg Prod.fst h
  · rw [Rep.epi_iff_surjective]
    exact fun n ↦ ⟨(0, n), rfl⟩

/-- The lifted external product maps to the integral augmented lattice by
lowering the trivial line and then using external-to-internal addition. -/
noncomputable def logLiftedAugmented
    (S : Finset (NumberFieldPlace K)) :
    upperLogRepresentation (K := K) (L := L) S →ₗ[ℤ]
      upperAugmentedLattice (K := K) (L := L) S :=
  (upperLogAugmented
    (K := K) (L := L) S).comp
      (((LinearEquiv.refl ℤ
        (upperLogLattice (K := K) (L := L) S)).prodCongr
          (ULift.moduleEquiv (R := ℤ) (M := ℤ))).toLinearMap)

theorem lifted_augmented_bijective
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Function.Bijective
      (logLiftedAugmented
        (K := K) (L := L) S) :=
  (log_augmented_bijective
    (K := K) (L := L) S hSinf).comp
      (((LinearEquiv.refl ℤ
        (upperLogLattice (K := K) (L := L) S)).prodCongr
          (ULift.moduleEquiv (R := ℤ) (M := ℤ))).bijective)

/-- The direct product representation is equivariantly isomorphic to the
actual augmented logarithmic lattice. -/
noncomputable def logRepAugmented
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    upperLogRepresentation (K := K) (L := L) S ≅
      stableLatticeRepresentation
        (placeFunctionRepresentation (K := K) (L := L) S)
        (upperAugmentedLattice (K := K) (L := L) S)
        (augmented_lattice_stable (K := K) (L := L) S) :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective
      (logLiftedAugmented
        (K := K) (L := L) S)
      (lifted_augmented_bijective
        (K := K) (L := L) S hSinf))
    (fun g ↦ by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change
        ((placeFunctionRepresentation (K := K) (L := L) S g
            x.1.1) +
          x.2.down • upperConstantVector (K := K) (L := L) S) =
        placeFunctionRepresentation (K := K) (L := L) S g
          (x.1.1 +
            x.2.down • upperConstantVector (K := K) (L := L) S)
      rw [map_add, map_zsmul,
        function_representation_vector]))

/-- The trivial integral line is the permutation lattice on a singleton. -/
noncomputable def trivialRepIso
    (G : Type u) [Group G] :
    Rep.trivial ℤ G upperLiftedInt ≅
      orbitFunctionRepresentation G (ULift.{u, 0} PUnit.{1}) :=
  Rep.mkIso (Representation.Equiv.mk
    { toFun := fun n _ ↦ n.down
      invFun := fun f ↦ ULift.up
        (f (ULift.up PUnit.unit : ULift.{u, 0} PUnit.{1}))
      left_inv := fun _ ↦ by apply ULift.down_injective; rfl
      right_inv := fun f ↦ by funext x; cases x; rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (fun g ↦ by
      ext n x
      cases x
      rfl))

/-- The Herbrand quotient of the trivial integral line is the group order. -/
theorem trivial_herbrand_value
    (G : Type u) [CommGroup G] [Fintype G] :
    HerbrandQuotientValue.{u, u}
      (Rep.trivial ℤ G upperLiftedInt)
      (Fintype.card G : ℚ) := by
  apply (herbrand_value_iso
    (trivialRepIso G) (Fintype.card G : ℚ)).mpr
  simpa using
    (function_herbrand_value G
      (ULift.{u, 0} PUnit.{1})
      (ULift.up PUnit.unit : ULift.{u, 0} PUnit.{1}))

omit [FiniteDimensional K L] in
/-- Multiplicativity in the split product sequence computes the Herbrand
quotient of `M⁰ × ℤ`. -/
theorem upper_log_herbrand
    [Finite Gal(L/K)] [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K)) (q : ℚ) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue.{u, u}
        (upperLogRepresentation (K := K) (L := L) S) q ↔
      ∃ q0 : ℚ,
        HerbrandQuotientValue.{u, u}
          (stableLatticeRepresentation
            (placeFunctionRepresentation (K := K) (L := L) S)
            (upperLogLattice (K := K) (L := L) S)
            (log_lattice_stable (K := K) (L := L) S)) q0 ∧
        q = (Nat.card Gal(L/K) : ℚ) * q0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let R0 : Rep.{u, 0, u} ℤ Gal(L/K) := stableLatticeRepresentation
    (placeFunctionRepresentation (K := K) (L := L) S)
    (upperLogLattice (K := K) (L := L) S)
    (log_lattice_stable (K := K) (L := L) S)
  let P : Rep.{u, 0, u} ℤ Gal(L/K) :=
    upperLogRepresentation (K := K) (L := L) S
  let Z : Rep.{u, 0, u} ℤ Gal(L/K) :=
    Rep.trivial ℤ Gal(L/K) upperLiftedInt
  let X : ShortComplex (Rep.{u, 0, u} ℤ Gal(L/K)) :=
    logShortComplex (K := K) (L := L) S
  have hX : X.ShortExact :=
    short_complex_exact
      (K := K) (L := L) S
  have hZ : HerbrandQuotientValue Z (Fintype.card Gal(L/K) : ℚ) :=
    trivial_herbrand_value Gal(L/K)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  constructor
  · intro hP
    letI : Finite (tateZero P) := hP.1
    letI : Finite (tateNegOne P) := hP.2.1
    letI : Finite (tateZero Z) := hZ.1
    letI : Finite (tateNegOne Z) := hZ.2.1
    letI : Finite (tateZero X.X₂) := by
      simpa [X, P] using hP.1
    letI : Finite (tateNegOne X.X₂) := by
      simpa [X, P] using hP.2.1
    letI : Finite (tateZero X.X₃) := by
      simpa [X, Z] using hZ.1
    letI : Finite (tateNegOne X.X₃) := by
      simpa [X, Z] using hZ.2.1
    obtain ⟨hR0zero, hR0neg⟩ := tate_finite_left hX g hg
    letI : Finite (tateZero R0) := by
      simpa [X, R0] using hR0zero
    letI : Finite (tateNegOne R0) := by
      simpa [X, R0] using hR0neg
    let q0 : ℚ := (Nat.card (tateZero R0) : ℚ) /
      Nat.card (tateNegOne R0)
    have hR0 : HerbrandQuotientValue R0 q0 :=
      ⟨inferInstance, inferInstance, rfl⟩
    have hmul := tate_card_ratio hX g hg
    have hmul' :
        (Nat.card (tateZero P) : ℚ) /
            Nat.card (tateNegOne P) =
          ((Nat.card (tateZero R0) : ℚ) /
              Nat.card (tateNegOne R0)) *
            ((Nat.card (tateZero Z) : ℚ) /
              Nat.card (tateNegOne Z)) := by
      change
        (Nat.card (tateZero P) : ℚ) /
            Nat.card (tateNegOne P) =
          ((Nat.card (tateZero R0) : ℚ) /
              Nat.card (tateNegOne R0)) *
            ((Nat.card (tateZero Z) : ℚ) /
              Nat.card (tateNegOne Z)) at hmul
      exact hmul
    refine ⟨q0, hR0, ?_⟩
    calc
      q = (Nat.card (tateZero P) : ℚ) /
          Nat.card (tateNegOne P) := hP.2.2.symm
      _ = ((Nat.card (tateZero R0) : ℚ) /
            Nat.card (tateNegOne R0)) *
          ((Nat.card (tateZero Z) : ℚ) /
            Nat.card (tateNegOne Z)) := hmul'
      _ = q0 * (Fintype.card Gal(L/K) : ℚ) := by
        rw [hR0.2.2, hZ.2.2]
      _ = (Nat.card Gal(L/K) : ℚ) * q0 := by
        rw [Nat.card_eq_fintype_card]
        ring
  · rintro ⟨q0, hR0, hq⟩
    letI : Finite (tateZero R0) := hR0.1
    letI : Finite (tateNegOne R0) := hR0.2.1
    letI : Finite (tateZero Z) := hZ.1
    letI : Finite (tateNegOne Z) := hZ.2.1
    letI : Finite (tateZero X.X₁) := by
      simpa [X, R0] using hR0.1
    letI : Finite (tateNegOne X.X₁) := by
      simpa [X, R0] using hR0.2.1
    letI : Finite (tateZero X.X₃) := by
      simpa [X, Z] using hZ.1
    letI : Finite (tateNegOne X.X₃) := by
      simpa [X, Z] using hZ.2.1
    obtain ⟨hPzero, hPneg⟩ := tate_finite_middle hX g hg
    letI : Finite (tateZero P) := by
      simpa [X, P] using hPzero
    letI : Finite (tateNegOne P) := by
      simpa [X, P] using hPneg
    have hmul := tate_card_ratio hX g hg
    have hmul' :
        (Nat.card (tateZero P) : ℚ) /
            Nat.card (tateNegOne P) =
          ((Nat.card (tateZero R0) : ℚ) /
              Nat.card (tateNegOne R0)) *
            ((Nat.card (tateZero Z) : ℚ) /
              Nat.card (tateNegOne Z)) := by
      change
        (Nat.card (tateZero P) : ℚ) /
            Nat.card (tateNegOne P) =
          ((Nat.card (tateZero R0) : ℚ) /
              Nat.card (tateNegOne R0)) *
            ((Nat.card (tateZero Z) : ℚ) /
              Nat.card (tateNegOne Z)) at hmul
      exact hmul
    refine ⟨inferInstance, inferInstance, ?_⟩
    calc
      (Nat.card (tateZero P) : ℚ) /
          Nat.card (tateNegOne P) =
        ((Nat.card (tateZero R0) : ℚ) /
            Nat.card (tateNegOne R0)) *
          ((Nat.card (tateZero Z) : ℚ) /
            Nat.card (tateNegOne Z)) := hmul'
      _ = q0 * (Fintype.card Gal(L/K) : ℚ) := by
        rw [hR0.2.2, hZ.2.2]
      _ = (Nat.card Gal(L/K) : ℚ) * q0 := by
        rw [Nat.card_eq_fintype_card]
        ring
      _ = q := hq.symm

/-- The actual augmented lattice has quotient `|G|` times that of `M⁰`. -/
theorem augmented_herbrand_log
    [Finite Gal(L/K)] [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (q : ℚ) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
        (stableLatticeRepresentation
          (placeFunctionRepresentation (K := K) (L := L) S)
          (upperAugmentedLattice (K := K) (L := L) S)
          (augmented_lattice_stable (K := K) (L := L) S)) q ↔
      ∃ q0 : ℚ,
        HerbrandQuotientValue
          (stableLatticeRepresentation
            (placeFunctionRepresentation (K := K) (L := L) S)
            (upperLogLattice (K := K) (L := L) S)
            (log_lattice_stable (K := K) (L := L) S)) q0 ∧
        q = (Nat.card Gal(L/K) : ℚ) * q0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let e := logRepAugmented
    (K := K) (L := L) S hSinf
  rw [← upper_log_herbrand
    (K := K) (L := L) S q]
  exact (herbrand_value_iso e q).symm

/-- Milne's augmented logarithmic lattice has Herbrand quotient
`[L : K] h(U(T))`.  No auxiliary arithmetic hypotheses beyond those in the
source statement are used. -/
theorem augmented_lattice_herbrand
    [Finite Gal(L/K)] [IsCyclic Gal(L/K)]
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (q : ℚ) :
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
        (stableLatticeRepresentation
          (placeFunctionRepresentation (K := K) (L := L) S)
          (upperAugmentedLattice (K := K) (L := L) S)
          (augmented_lattice_stable (K := K) (L := L) S)) q ↔
      ∃ qU : ℚ,
        HerbrandQuotientValue
          (unitsPlacesRepresentation (K := K) (L := L) S) qU ∧
        q = (Module.finrank K L : ℚ) * qU := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  have hcard : Nat.card Gal(L/K) = Module.finrank K L :=
    IsGalois.card_aut_eq_finrank K L
  have hcardFintype : Fintype.card Gal(L/K) = Module.finrank K L :=
    Fintype.card_eq_nat_card.trans hcard
  constructor
  · intro hM
    obtain ⟨q0, hM0, hq⟩ :=
      (augmented_herbrand_log
        (K := K) (L := L) S hSinf q).mp hM
    have hU : HerbrandQuotientValue
        (unitsPlacesRepresentation (K := K) (L := L) S) q0 :=
      (herbrand_log_lattice
        (K := K) (L := L) S hSinf q0).mpr hM0
    refine ⟨q0, hU, ?_⟩
    simpa [hcardFintype] using hq
  · rintro ⟨qU, hU, hq⟩
    have hM0 : HerbrandQuotientValue
        (stableLatticeRepresentation
          (placeFunctionRepresentation (K := K) (L := L) S)
          (upperLogLattice (K := K) (L := L) S)
          (log_lattice_stable (K := K) (L := L) S)) qU :=
      (herbrand_log_lattice
        (K := K) (L := L) S hSinf qU).mp hU
    apply
      (augmented_herbrand_log
        (K := K) (L := L) S hSinf q).mpr
    exact ⟨qU, hM0, by simpa [hcardFintype] using hq⟩

/-- The remaining logarithmic-lattice bridge in Proposition VII.3.1. -/
theorem logLatticeBridge :
    LogLatticeBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ S hSinf
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  refine ⟨upperAugmentedLattice (K := K) (L := L) S,
    augmented_lattice_stable (K := K) (L := L) S,
    augmented_lattice_real
      (K := K) (L := L) S hSinf, ?_⟩
  intro q
  exact augmented_lattice_herbrand
    (K := K) (L := L) S hSinf q

end

end Towers.CField.HQuotie
