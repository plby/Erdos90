import Towers.ClassField.HerbrandQuotients.PlaceHerbrand
import Towers.ClassField.HerbrandQuotients.SUnits
import Towers.NumberTheory.Locals.LogarithmicValuation
import Towers.ClassField.NormIndex.IdeleExtensionMap

/-!
# The logarithmic `T`-unit map in Proposition VII.3.1

This is Milne's map

`lambda : U(T) → Hom(T, ℝ),  a ↦ (log |a|_w)_w`.

The coordinates use the normalized upper places already constructed for the
place lattice.  The map is integral-linear after writing the multiplicative
`T`-unit group additively, and it commutes with Galois conjugation.
-/

namespace Towers.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Over a member of `S`, use the finite set of upper primes when the place
is finite and the empty type when it is infinite. -/
private abbrev primeFiber
    (S : Finset (NumberFieldPlace K)) (v : S) :=
  match v.1 with
  | .inl P => PrimesAboveBase (K := K) (L := L) P
  | .inr _ => PEmpty

private noncomputable instance finitePrimeFiber
    (S : Finset (NumberFieldPlace K)) (v : S) :
    Finite (primeFiber (K := K) (L := L) S v) := by
  rcases v with ⟨v, hv⟩
  cases v with
  | inl P =>
      exact Finite.of_equiv
        (UpperPrimeFactors (K := K) (L := L) P)
        (upperAboveBase
          (K := K) (L := L) P)
  | inr v => infer_instance

private noncomputable def abovePlacesSigma
    (S : Finset (NumberFieldPlace K)) :
    (primesAbovePlaces (K := K) (L := L) S) →
      Σ v : S, primeFiber (K := K) (L := L) S v :=
  fun Q =>
    ⟨⟨Sum.inl (Q.1.under (NumberField.RingOfIntegers K)), Q.2⟩,
      ⟨Q.1, rfl⟩⟩

private def fiberSigmaVal
    (S : Finset (NumberFieldPlace K)) :
    (Σ v : S, primeFiber (K := K) (L := L) S v) →
      FinitePrime L
  | ⟨⟨.inl _, _⟩, Q⟩ => Q.1
  | ⟨⟨.inr _, _⟩, Q⟩ => nomatch Q

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
private theorem places_sigma_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (abovePlacesSigma (K := K) (L := L) S) := by
  intro Q R h
  apply Subtype.ext
  exact congrArg (fiberSigmaVal (K := K) (L := L) S) h

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Only finitely many finite primes of `L` lie over the finite members of
a finite set `S`. -/
theorem primes_above_places
    (S : Finset (NumberFieldPlace K)) :
    (primesAbovePlaces (K := K) (L := L) S).Finite := by
  letI : Finite (primesAbovePlaces (K := K) (L := L) S) :=
    Finite.of_injective
      (abovePlacesSigma (K := K) (L := L) S)
      (places_sigma_injective (K := K) (L := L) S)
  exact Set.finite_coe_iff.mp inferInstance

/-- The finite primes above the finite members of `S`, as a finite type. -/
noncomputable instance abovePlacesFintype
    (S : Finset (NumberFieldPlace K)) :
    Fintype (primesAbovePlaces (K := K) (L := L) S) :=
  (primes_above_places (K := K) (L := L) S).fintype

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The additive group of the actual `T`-units is a finite integral module. -/
theorem units_places_module
    (S : Finset (NumberFieldPlace K)) :
    Module.Finite ℤ
      (Additive (unitsAtPlaces (K := K) (L := L) S)) :=
  s_units_module L (primesAbovePlaces (K := K) (L := L) S)
    (primes_above_places (K := K) (L := L) S)

/-- Milne's logarithmic embedding as a homomorphism of additive groups. -/
noncomputable def upperLogHom
    (S : Finset (NumberFieldPlace K)) :
    Additive (unitsAtPlaces (K := K) (L := L) S) →+
      (upperPlacesAt (K := K) (L := L) S → ℝ) where
  toFun x t := Real.log (t.2.1
    (((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L))
  map_zero' := by
    funext t
    change Real.log (t.2.1 (1 : L)) = 0
    simp
  map_add' x y := by
    funext t
    change Real.log (t.2.1
        (((Additive.toMul (x + y) :
          unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) =
      Real.log (t.2.1
        (((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) +
      Real.log (t.2.1
        (((Additive.toMul y : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L))
    rw [show (((Additive.toMul (x + y) :
        unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L) =
        ((((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L) *
          (((Additive.toMul y : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) by rfl,
      map_mul]
    exact Real.log_mul
      (t.2.1.ne_zero
        ((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ).ne_zero)
      (t.2.1.ne_zero
        ((Additive.toMul y : unitsAtPlaces (K := K) (L := L) S) : Lˣ).ne_zero)

/-- Milne's logarithmic embedding of the `T`-units into real functions on
the places above `S`, as an integral linear map. -/
noncomputable def upperUnitLog
    (S : Finset (NumberFieldPlace K)) :
    Additive (unitsAtPlaces (K := K) (L := L) S) →ₗ[ℤ]
      (upperPlacesAt (K := K) (L := L) S → ℝ) :=
  (upperLogHom (K := K) (L := L) S).toIntLinearMap

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem upper_unit_log
    (S : Finset (NumberFieldPlace K))
    (x : Additive (unitsAtPlaces (K := K) (L := L) S))
    (t : upperPlacesAt (K := K) (L := L) S) :
    upperUnitLog (K := K) (L := L) S x t =
      Real.log (t.2.1
        (((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) :=
  rfl

omit [FiniteDimensional K L] in
/-- The logarithmic embedding commutes with Galois conjugation. -/
theorem upper_log_equivariant
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : Additive (unitsAtPlaces (K := K) (L := L) S)) :
    placeFunctionRepresentation (K := K) (L := L) S sigma
        (upperUnitLog (K := K) (L := L) S x) =
      upperUnitLog (K := K) (L := L) S
        ((unitsPlacesRepresentation (K := K) (L := L) S).ρ sigma x) := by
  funext t
  rcases t with ⟨v, t⟩
  change Real.log ((sigma⁻¹ • t).1
      (((Additive.toMul x : unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) =
    Real.log (t.1
      (sigma (((Additive.toMul x :
        unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)))
  rfl

/-- Milne's `M⁰`, the logarithmic image of the `T`-unit group. -/
noncomputable def upperLogLattice
    (S : Finset (NumberFieldPlace K)) :
    Submodule ℤ (upperPlacesAt (K := K) (L := L) S → ℝ) :=
  LinearMap.range (upperUnitLog (K := K) (L := L) S)

omit [FiniteDimensional K L] in
/-- `M⁰` is Galois-stable. -/
theorem log_lattice_stable
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : upperPlacesAt (K := K) (L := L) S → ℝ)
    (hx : x ∈ upperLogLattice (K := K) (L := L) S) :
    placeFunctionRepresentation (K := K) (L := L) S sigma x ∈
      upperLogLattice (K := K) (L := L) S := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨(unitsPlacesRepresentation (K := K) (L := L) S).ρ sigma a,
    upper_log_equivariant (K := K) (L := L) S sigma a⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The logarithmic image `M⁰` is finitely generated over `ℤ`. -/
theorem log_lattice_module
    (S : Finset (NumberFieldPlace K)) :
    Module.Finite ℤ (upperLogLattice (K := K) (L := L) S) := by
  letI : Module.Finite ℤ
      (Additive (unitsAtPlaces (K := K) (L := L) S)) :=
    units_places_module (K := K) (L := L) S
  exact Module.Finite.range (upperUnitLog (K := K) (L := L) S)

/-- Milne's constant vector `e = (1, ..., 1)`. -/
def upperConstantVector
    (S : Finset (NumberFieldPlace K)) :
    upperPlacesAt (K := K) (L := L) S → ℝ :=
  fun _ => 1

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem function_representation_vector
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K)) :
    placeFunctionRepresentation (K := K) (L := L) S sigma
      (upperConstantVector (K := K) (L := L) S) =
        upperConstantVector (K := K) (L := L) S := by
  rfl

/-- Milne's second full-lattice candidate `M = M⁰ + ℤ e`. -/
noncomputable def upperAugmentedLattice
    (S : Finset (NumberFieldPlace K)) :
    Submodule ℤ (upperPlacesAt (K := K) (L := L) S → ℝ) :=
  upperLogLattice (K := K) (L := L) S ⊔
    ℤ ∙ upperConstantVector (K := K) (L := L) S

omit [FiniteDimensional K L] in
/-- The augmented logarithmic lattice is Galois-stable. -/
theorem augmented_lattice_stable
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : upperPlacesAt (K := K) (L := L) S → ℝ)
    (hx : x ∈ upperAugmentedLattice (K := K) (L := L) S) :
    placeFunctionRepresentation (K := K) (L := L) S sigma x ∈
      upperAugmentedLattice (K := K) (L := L) S := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left
      (log_lattice_stable (K := K) (L := L) S sigma a ha)
  · apply Submodule.mem_sup_right
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hb
    apply Submodule.mem_span_singleton.mpr
    refine ⟨n, ?_⟩
    funext t
    rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The augmented logarithmic lattice is finitely generated over `ℤ`. -/
theorem upper_augmented_lattice
    (S : Finset (NumberFieldPlace K)) :
    Module.Finite ℤ
      (upperAugmentedLattice (K := K) (L := L) S) := by
  change Module.Finite ℤ
    (↥((upperLogLattice (K := K) (L := L) S) ⊔
      (ℤ ∙ upperConstantVector (K := K) (L := L) S)))
  letI : Module.Finite ℤ
      (upperLogLattice (K := K) (L := L) S) :=
    log_lattice_module (K := K) (L := L) S
  letI : Module.Finite ℤ
      (ℤ ∙ upperConstantVector (K := K) (L := L) S) :=
    inferInstance
  infer_instance

end

end Towers.CField.HQuotie
