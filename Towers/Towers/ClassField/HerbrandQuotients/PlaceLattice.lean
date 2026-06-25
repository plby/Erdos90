import Towers.ClassField.HerbrandQuotients.FiniteAbovePlaces
import Towers.NumberTheory.Locals.ArbitraryPlaceClassification
import Mathlib.LinearAlgebra.TensorProduct.Free

/-!
# The place lattice in Proposition VII.3.1

This file constructs the first of the two lattices in Milne's proof of
Proposition VII.3.1.  For a finite set `S` of base places, `upperPlacesAt S`
is the disjoint union of the places of `L` above the members of `S`.  The
Galois group acts inside each fibre.  The real permutation representation on
functions on this finite set contains the literal integral lattice
`Hom(T, Z)`.
-/

namespace Towers.CField.HQuotie

open AbsoluteValue IsDedekindDomain Module NumberField Representation
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped TensorProduct

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The disjoint union, over `v in S`, of the normalized absolute values of
`L` extending `v`.  This is the set denoted `T` in Proposition VII.3.1. -/
abbrev upperPlacesAt (S : Finset (NumberFieldPlace K)) :=
  Σ v : S, CompletionPlacesAbove (L := L)
    (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))

/-- Galois conjugation preserves the base place of an upper place. -/
instance upperPlacesAction (S : Finset (NumberFieldPlace K)) :
    MulAction Gal(L/K) (upperPlacesAt (K := K) (L := L) S) where
  smul sigma w := ⟨w.1, sigma • w.2⟩
  one_smul w := by
    rcases w with ⟨v, w⟩
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul Gal(L/K) w)
  mul_smul sigma tau w := by
    rcases w with ⟨v, w⟩
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul sigma tau w)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem infinite_place_upper
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    ∃ w : InfinitePlace L,
      w.comap (algebraMap K L) = v ∧ w.1 = z.1 := by
  have hzNontrivial : z.1.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
    have hxMap : algebraMap K L x ≠ 0 := by
      simpa using (algebraMap K L).injective.ne hx0
    refine ⟨algebraMap K L x, hxMap, ?_⟩
    have heq := DFunLike.congr_fun z.2.comp_eq x
    change z.1 (algebraMap K L x) = v.1 x at heq
    exact fun h => hx1 (heq.symm.trans h)
  have hzArch : ¬ IsNonarchimedean z.1 := by
    intro hz
    apply infinite_place_nonarchimedean v
    intro x y
    calc
      v.1 (x + y) = z.1 (algebraMap K L (x + y)) :=
        (DFunLike.congr_fun z.2.comp_eq (x + y)).symm
      _ = z.1 (algebraMap K L x + algebraMap K L y) := by rw [map_add]
      _ ≤ max (z.1 (algebraMap K L x)) (z.1 (algebraMap K L y)) := hz _ _
      _ = max (v.1 x) (v.1 y) := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨w, hzw⟩ :=
    infinite_not_nonarchimedean
      z.1 hzNontrivial hzArch
  have hwComap : w.comap (algebraMap K L) = v := by
    apply (InfinitePlace.eq_iff_isEquiv (K := K)).2
    intro x y
    change w.1 (algebraMap K L x) ≤ w.1 (algebraMap K L y) ↔
      v.1 x ≤ v.1 y
    calc
      w.1 (algebraMap K L x) ≤ w.1 (algebraMap K L y) ↔
          z.1 (algebraMap K L x) ≤ z.1 (algebraMap K L y) :=
        (hzw _ _).symm
      _ ↔ v.1 x ≤ v.1 y := by
        have hx := DFunLike.congr_fun z.2.comp_eq x
        have hy := DFunLike.congr_fun z.2.comp_eq y
        change z.1 (algebraMap K L x) = v.1 x at hx
        change z.1 (algebraMap K L y) = v.1 y at hy
        rw [hx, hy]
  obtain ⟨c, _hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hzw
  obtain ⟨x, hx0, hx1⟩ := infinite_place_nontrivial v
  have hvx : 0 < v.1 x := v.1.pos hx0
  have hzBase := DFunLike.congr_fun z.2.comp_eq x
  have hwLies := infinite_lies_comap v w hwComap
  have hwBase := DFunLike.congr_fun hwLies.comp_eq x
  change z.1 (algebraMap K L x) = v.1 x at hzBase
  change w.1 (algebraMap K L x) = v.1 x at hwBase
  have hbase : v.1 x ^ c = v.1 x ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    calc
      v.1 x ^ c = z.1 (algebraMap K L x) ^ c := by
        exact congrArg (fun r : ℝ => r ^ c) hzBase.symm
      _ = w.1 (algebraMap K L x) := congrFun hpow _
      _ = v.1 x := hwBase
  have hc1 : c = 1 := (Real.rpow_right_inj hvx hx1).mp hbase
  refine ⟨w, hwComap, ?_⟩
  apply AbsoluteValue.ext
  intro y
  have hy := congrFun hpow y
  simpa [hc1] using hy.symm

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem upperInfinitePlaces (v : InfinitePlace K) :
    Finite (CompletionPlacesAbove (L := L) v.1) := by
  let toInfinitePlace : CompletionPlacesAbove (L := L) v.1 → InfinitePlace L :=
    fun z => ⟨z.1, by
      obtain ⟨w, _hwv, hw⟩ := infinite_place_upper
        (K := K) (L := L) v z
      exact hw ▸ w.isInfinitePlace⟩
  exact Finite.of_injective toInfinitePlace fun z z' h => by
    apply Subtype.ext
    exact congrArg (fun w : InfinitePlace L => w.1) h

/-- Galois conjugation is transitive on the normalized places above any
finite or infinite number-field place. -/
theorem upper_fiber_pretransitive (v : NumberFieldPlace K) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L)
        (coinvariantsInvariantsAbsolute v)) := by
  cases v with
  | inl P =>
      exact completion_above_pretransitive P
  | inr v =>
      constructor
      intro z w
      obtain ⟨zInf, hzComap, hz⟩ := infinite_place_upper
        (K := K) (L := L) v z
      obtain ⟨wInf, hwComap, hw⟩ := infinite_place_upper
        (K := K) (L := L) v w
      obtain ⟨sigma, hsigma⟩ :=
        InfinitePlace.exists_smul_eq_of_comap_eq
          (hzComap.trans hwComap.symm)
      have hsigmaAbs : (sigma • zInf).1 = sigma • zInf.1 := by
        apply AbsoluteValue.ext
        intro x
        rfl
      refine ⟨sigma, Subtype.ext ?_⟩
      change sigma • z.1 = w.1
      calc
        sigma • z.1 = sigma • zInf.1 :=
          congrArg (fun q : AbsoluteValue L ℝ => sigma • q) hz.symm
        _ = (sigma • zInf).1 := hsigmaAbs.symm
        _ = wInf.1 := congrArg (fun q : InfinitePlace L => q.1) hsigma
        _ = w.1 := hw

/-- Each fibre of normalized places above a number-field place is finite. -/
noncomputable instance upperPlaceFiber (v : NumberFieldPlace K) :
    Finite (CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) := by
  cases v with
  | inl P =>
      letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
        placeUltrametricDist P
      exact absolute_extensions_separable
        (FinitePlace.mk P).val
  | inr v =>
      exact upperInfinitePlaces (K := K) (L := L) v

/-- There are finitely many upper places above a finite set of base places. -/
instance upperPlacesFinite (S : Finset (NumberFieldPlace K)) :
    Finite (upperPlacesAt (K := K) (L := L) S) := by
  infer_instance

/-- Milne's real permutation representation `V = Hom(T, R)`. -/
noncomputable def placeFunctionRepresentation
    (S : Finset (NumberFieldPlace K)) :
    Representation ℝ Gal(L/K)
      (upperPlacesAt (K := K) (L := L) S → ℝ) where
  toFun sigma :=
    { toFun := fun f w => f (sigma⁻¹ • w)
      map_add' := fun f g => by ext w; rfl
      map_smul' := fun r f => by ext w; simp }
  map_one' := by
    ext f w
    exact congrArg f (one_smul Gal(L/K) w)
  map_mul' sigma tau := by
    ext f w
    exact congrArg f (mul_smul tau⁻¹ sigma⁻¹ w)

/-- Coordinatewise inclusion of integral functions into real functions. -/
def upperFunctionEmbedding
    (S : Finset (NumberFieldPlace K)) :
    (upperPlacesAt (K := K) (L := L) S → ℤ) →ₗ[ℤ]
      (upperPlacesAt (K := K) (L := L) S → ℝ) where
  toFun f w := (f w : ℝ)
  map_add' f g := by ext w; simp
  map_smul' n f := by ext w; simp

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem upper_function_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (upperFunctionEmbedding (K := K) (L := L) S) := by
  intro f g h
  ext w
  have hw := congrFun h w
  change (f w : ℝ) = (g w : ℝ) at hw
  exact Int.cast_injective hw

/-- The literal lattice `N = Hom(T, Z)` inside `V = Hom(T, R)`. -/
def upperPlaceLattice
    (S : Finset (NumberFieldPlace K)) :
    Submodule ℤ (upperPlacesAt (K := K) (L := L) S → ℝ) :=
  LinearMap.range (upperFunctionEmbedding (K := K) (L := L) S)

private noncomputable def upperIntegerLattice
    (S : Finset (NumberFieldPlace K)) :
    (upperPlacesAt (K := K) (L := L) S → ℤ) ≃ₗ[ℤ]
      upperPlaceLattice (K := K) (L := L) S :=
  LinearEquiv.ofInjective
    (upperFunctionEmbedding (K := K) (L := L) S)
    (upper_function_injective (K := K) (L := L) S)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
private theorem integer_lattice_coe
    (S : Finset (NumberFieldPlace K))
    (f : upperPlacesAt (K := K) (L := L) S → ℤ)
    (j : upperPlacesAt (K := K) (L := L) S) :
    ((upperIntegerLattice (K := K) (L := L) S f :
        upperPlaceLattice (K := K) (L := L) S) :
      upperPlacesAt (K := K) (L := L) S → ℝ) j = (f j : ℝ) := by
  have h :
      ((upperIntegerLattice (K := K) (L := L) S f :
          upperPlaceLattice (K := K) (L := L) S) :
        upperPlacesAt (K := K) (L := L) S → ℝ) =
        upperFunctionEmbedding (K := K) (L := L) S f := by
    exact LinearEquiv.ofInjective_apply
      (h := upper_function_injective
        (K := K) (L := L) S)
      (upperFunctionEmbedding (K := K) (L := L) S) f
  exact congrFun h j

private noncomputable def upperLatticeBasis
    (S : Finset (NumberFieldPlace K)) :
    Basis (upperPlacesAt (K := K) (L := L) S) ℤ
      (upperPlaceLattice (K := K) (L := L) S) :=
  (Pi.basisFun ℤ
      (upperPlacesAt (K := K) (L := L) S)).map
    (upperIntegerLattice (K := K) (L := L) S)

@[simp]
private theorem upper_lattice_repr
    (S : Finset (NumberFieldPlace K))
    (f : upperPlacesAt (K := K) (L := L) S → ℤ) :
    (upperLatticeBasis (K := K) (L := L) S).repr
        (upperIntegerLattice (K := K) (L := L) S f) = f := by
  classical
  ext i
  simp [upperLatticeBasis]

open scoped Classical in
private theorem upper_lattice_coe
    (S : Finset (NumberFieldPlace K))
    (i j : upperPlacesAt (K := K) (L := L) S) :
    ((upperLatticeBasis (K := K) (L := L) S i :
        upperPlaceLattice (K := K) (L := L) S) :
      upperPlacesAt (K := K) (L := L) S → ℝ) j =
      if i = j then 1 else 0 := by
  classical
  rw [upperLatticeBasis, Basis.map_apply, Pi.basisFun_apply]
  rw [integer_lattice_coe]
  by_cases h : i = j <;> simp [Pi.single_apply, h]

/-- In the standard integral basis, scalar extension of `Hom(T, Z)` to
`R` is the usual real function space. -/
private noncomputable def upperLatticeChange
    (S : Finset (NumberFieldPlace K)) :
    ℝ ⊗[ℤ] upperPlaceLattice (K := K) (L := L) S ≃ₗ[ℝ]
      (upperPlacesAt (K := K) (L := L) S → ℝ) :=
  Algebra.TensorProduct.equivPiOfFiniteBasis ℝ
    (upperLatticeBasis (K := K) (L := L) S)

private theorem upper_lattice_realization
    (S : Finset (NumberFieldPlace K)) :
    (upperLatticeChange (K := K) (L := L) S).toLinearMap =
      fullLatticeRealization
        (upperPlaceLattice (K := K) (L := L) S) := by
  letI : Fintype (upperPlacesAt (K := K) (L := L) S) :=
    Fintype.ofFinite _
  apply TensorProduct.AlgebraTensorModule.ext
  intro r m
  apply funext
  intro j
  rw [lattice_realization_tmul]
  change
    (upperLatticeChange (K := K) (L := L) S)
        (r ⊗ₜ[ℤ] m) j = r * (m :
          upperPlacesAt (K := K) (L := L) S → ℝ) j
  rw [show (upperLatticeChange
      (K := K) (L := L) S) (r ⊗ₜ[ℤ] m) j =
        ((upperLatticeBasis
          (K := K) (L := L) S).repr m j : ℝ) * r by
      simp [upperLatticeChange]]
  classical
  let e := upperIntegerLattice (K := K) (L := L) S
  let f := e.symm m
  have hm : m = e f := (e.apply_symm_apply m).symm
  have hcoord :
      ((upperLatticeBasis (K := K) (L := L) S).repr m j : ℝ) =
        (m : upperPlacesAt (K := K) (L := L) S → ℝ) j := by
    rw [hm]
    rw [upper_lattice_repr,
      integer_lattice_coe]
  rw [hcoord, mul_comm]

/-- The first lattice in Milne's proof is a full real lattice, in the exact
algebraic sense used by Lemma VII.3.5. -/
theorem upper_lattice_real
    (S : Finset (NumberFieldPlace K)) :
    FullRealLattice
      (upperPlaceLattice (K := K) (L := L) S) := by
  constructor
  · let e := upperIntegerLattice (K := K) (L := L) S
    exact Module.Finite.equiv e
  · rw [← upper_lattice_realization
      (K := K) (L := L) S]
    exact (upperLatticeChange
      (K := K) (L := L) S).bijective

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Permuting the upper places preserves integer-valued functions. -/
theorem upper_lattice_stable
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : upperPlacesAt (K := K) (L := L) S → ℝ)
    (hx : x ∈ upperPlaceLattice (K := K) (L := L) S) :
    placeFunctionRepresentation (K := K) (L := L) S sigma x ∈
      upperPlaceLattice (K := K) (L := L) S := by
  obtain ⟨f, rfl⟩ := hx
  refine ⟨fun w => f (sigma⁻¹ • w), ?_⟩
  rfl

/-- The integral permutation representation on `Hom(T, Z)`. -/
noncomputable def upperFunctionRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep ℤ Gal(L/K) :=
  Rep.of
    { toFun := fun sigma =>
        { toFun := fun
            (f : upperPlacesAt (K := K) (L := L) S → ℤ) =>
              fun w => f (sigma⁻¹ • w)
          map_add' := fun f g => by ext w; rfl
          map_smul' := fun r f => by ext w; simp }
      map_one' := by
        ext f w
        exact congrArg f (one_smul Gal(L/K) w)
      map_mul' := by
        intro sigma tau
        ext f w
        exact congrArg f (mul_smul tau⁻¹ sigma⁻¹ w) }

/-- The stable-lattice representation on `N` is literally the integral
place-permutation representation. -/
noncomputable def functionStableLattice
    (S : Finset (NumberFieldPlace K)) :
    upperFunctionRepresentation (K := K) (L := L) S ≅
      stableLatticeRepresentation
        (placeFunctionRepresentation (K := K) (L := L) S)
        (upperPlaceLattice (K := K) (L := L) S)
        (upper_lattice_stable (K := K) (L := L) S) := by
  apply Rep.mkIso
  refine
    { toLinearEquiv := upperIntegerLattice
        (K := K) (L := L) S
      isIntertwining' := ?_ }
  intro sigma
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext w
  rfl

end

end Towers.CField.HQuotie
