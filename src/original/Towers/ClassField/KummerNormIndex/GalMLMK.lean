import Mathlib.LinearAlgebra.Basis.VectorSpace
import Towers.NumberTheory.Locals.PlaceExtension
import Towers.ClassField.KummerTheory.KummerCorrespondence
import Towers.ClassField.NormIndex.NumberFieldElement
import Towers.Group.FiniteFrattiniSelection

/-!
# Chapter VII, Section 6, Lemma 6.2

In the Kummer tower `K ⊆ L ⊆ M`, with `M/K` abelian of exponent `p`,
there is a finite set of base primes outside `S` whose Frobenius elements
form an `ᵓ_p`-basis of `Gal(M/L)`.

The conclusion retains chosen primes of `M` above the base primes.  Its basis
vectors are the actual arithmetic Frobenius elements for `M/L`, and the
displayed compatibility identifies their images in `Gal(M/K)` with the
actual arithmetic Frobenius elements for `M/K`.  Thus the formal statement
records the equality `(p_w,M/L) = (p_w,M/K)` used in the source proof rather
than replacing either side by an abstract vector.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open scoped Pointwise IsMulCommutative
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.KTheory
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

variable {K L M : Type u}
  [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M]
  [IsGalois L M] [IsAbelianGalois K M]

local instance ringOfIntegersGaloisAction :
    MulSemiringAction Gal(M/K) (OK M) :=
  IsIntegralClosure.MulSemiringAction (OK K) K M (OK M)

local instance ringOfIntegersGaloisAction_smulCommClass :
    SMulCommClass Gal(M/K) (OK K) (OK M) where
  smul_comm sigma a b := by
    apply Subtype.ext
    have hG (x : OK M) : ((sigma • x : OK M) : M) = sigma (x : M) :=
      algebraMap.coe_smul' (B := OK M) (C := M) sigma x
    have hA (x : OK M) : ((a • x : OK M) : M) = (a : K) • (x : M) :=
      algebraMap.coe_smul (A := OK K) (B := OK M) (C := M) a x
    calc
      ((sigma • (a • b) : OK M) : M) = sigma (((a • b : OK M) : M)) := hG (a • b)
      _ = sigma ((a : K) • (b : M)) := congrArg sigma (hA b)
      _ = (a : K) • sigma (b : M) := smul_comm sigma (a : K) (b : M)
      _ = (a : K) • ((sigma • b : OK M) : M) :=
        congrArg (fun y : M ↦ (a : K) • y) (hG b).symm
      _ = ((a • (sigma • b) : OK M) : M) := (hA (sigma • b)).symm

local instance ringOfIntegersGaloisAction_isInvariant :
    Algebra.IsInvariant (OK K) (OK M) Gal(M/K) := by
  exact Algebra.isInvariant_of_isGalois (A := OK K) (K := K)
    (L := M) (B := OK M)

local instance ringOfIntegersIsGaloisGroup :
    IsGaloisGroup Gal(M/K) (OK K) (OK M) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(M/K))
    (A := OK K) (B := OK M) (K := K) (L := M)

/-- Inclusion of `Gal(M/L)` into `Gal(M/K)` by restriction of scalars. -/
def galMLMK : Gal(M/L) →* Gal(M/K) where
  toFun sigma := sigma.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField L] [NumberField M]
  [FiniteDimensional K L] [FiniteDimensional L M] [IsGalois L M]
  [IsAbelianGalois K M] in
theorem gal_ml_injective :
    Function.Injective (galMLMK (K := K) (L := L) (M := M)) := by
  intro sigma tau h
  ext x
  exact DFunLike.congr_fun h x

omit [NumberField L] [NumberField M] [FiniteDimensional L M] [IsGalois L M] in
/-- Abelianity descends from `Gal(M/K)` to `Gal(M/L)`. -/
theorem gal_ml_commutative
    (K : Type u) [Field K] [Algebra K L] [Algebra K M]
    [IsScalarTower K L M] [IsAbelianGalois K M] :
    IsMulCommutative Gal(M/L) := by
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  ext x
  simpa using DFunLike.congr_fun
    (mul_comm (sigma.restrictScalars K) (tau.restrictScalars K)) x

set_option synthInstance.maxHeartbeats 200000 in
-- Extending an automorphism across the scalar tower requires deeper instance synthesis.
omit [NumberField K] [NumberField L] [NumberField M]
  [FiniteDimensional K L] [FiniteDimensional L M] [IsGalois L M] in
/-- The exponent-`p` condition descends from `Gal(M/K)` to `Gal(M/L)`. -/
theorem gal_ml_pow
    (p : ℕ) (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (sigma : Gal(M/L)) : sigma ^ p = 1 := by
  apply gal_ml_injective (K := K) (L := L) (M := M)
  rw [map_pow, hexponent, map_one]

set_option synthInstance.maxHeartbeats 200000 in
-- Constructing the `ZMod p` module searches through the induced additive group structure.
/-- The canonical `ᵓ_p`-vector-space structure on an abelian group killed
by `p`. -/
@[implicit_reducible]
noncomputable def exponentPModule
    (p : ℕ) {G : Type u} [Group G] [IsMulCommutative G]
    (hexponent : ∀ g : G, g ^ p = 1) : Module (ZMod p) (Additive G) := by
  apply AddCommGroup.zmodModule
  intro x
  induction x using Additive.rec with
  | ofMul g =>
      apply Additive.toMul.injective
      simpa using hexponent g

/-- Finite primes of `M` lying over a member of `S`. -/
def primesAboveSet
    (S : Finset (NumberFieldPlace K)) : Set (FinitePrime M) :=
  {Q | (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∈ S}

omit [IsAbelianGalois K M] in
/-- Only finitely many primes of a finite number-field extension lie above a
fixed finite set of base primes. -/
theorem primes_above_set
    (S : Finset (NumberFieldPlace K)) :
    (primesAboveSet (K := K) (M := M) S).Finite := by
  have hfiber : ∀ p : FinitePrime K,
      Set.Finite {Q : FinitePrime M | Q.under (OK K) = p} := by
    intro p
    apply Set.Finite.of_finite_image
        (f := fun Q : FinitePrime M ↦ Q.asIdeal)
    · apply (finite_places (K := K) (L := M) p.asIdeal).subset
      rintro P ⟨Q, hQ, rfl⟩
      change Q.asIdeal ∈ p.asIdeal.primesOver (OK M)
      exact ⟨Q.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hQ).symm⟩⟩
    · intro Q _ R _ hQR
      exact HeightOneSpectrum.ext hQR
  let Sfinite : Set (FinitePrime K) :=
    {p | (Sum.inl p : NumberFieldPlace K) ∈ S}
  have hSfinite : Sfinite.Finite := by
    apply Set.Finite.of_finite_image
        (f := fun p : FinitePrime K ↦
          (Sum.inl p : NumberFieldPlace K))
    · apply S.finite_toSet.subset
      rintro v ⟨p, hp, rfl⟩
      exact hp
    · exact Set.injOn_of_injective Sum.inl_injective
  let U : Set (FinitePrime M) :=
    ⋃ p ∈ Sfinite,
      {Q : FinitePrime M | Q.under (OK K) = p}
  have hUfinite : U.Finite := by
    exact hSfinite.biUnion fun p _ ↦ hfiber p
  apply hUfinite.subset
  intro Q hQ
  apply Set.mem_iUnion.mpr
  refine ⟨Q.under (OK K), ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨hQ, rfl⟩

/-- The literal finite exceptional set upstairs consisting of all primes
above `S`. -/
noncomputable def finiteAboveBase
    (S : Finset (NumberFieldPlace K)) : Finset (FinitePrime M) :=
  (primes_above_set (K := K) (M := M) S).toFinset

omit [IsAbelianGalois K M] in
@[simp]
theorem primes_above_base
    (S : Finset (NumberFieldPlace K)) (Q : FinitePrime M) :
    Q ∈ finiteAboveBase (K := K) (M := M) S ↔
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∈ S := by
  exact Set.Finite.mem_toFinset (primes_above_set
    (K := K) (M := M) S)

/-- The exact local step in Milne's proof.  Away from `S`, an unramified
local extension of exponent `p` has degree zero or one as an `ᵓ_p`-line.
If its `M/L` Frobenius is nontrivial, the completion of `L` is already the
completion of `K`; Frobenius restriction therefore gives the displayed
equality.

This bridge contains no generation or basis assertion. -/
def CompletionRestrictionBridge : Prop :=
  ∀ (p : ℕ) (_hp : Nat.Prime p)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M]
    (_hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K))
    (_hunramified : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
        Algebra.IsUnramifiedAt (OK K) Q.asIdeal)
    (Q : FinitePrime M),
    (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
      numberFrobeniusElement (K := L) Q ≠ 1 →
      galMLMK (K := K) (L := L) (M := M)
          (numberFrobeniusElement (K := L) Q) =
        numberFrobeniusElement (K := K) Q

/-- A finite set `T` of base primes, together with the literal Frobenius
basis asserted in Lemma 6.2.  `indexPrime` is a bijection from the basis
indices to `T`, so no prime is repeated. -/
def HasFrobeniusBasis
    (p : ℕ) (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K)) : Prop :=
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  ∃ (T : Finset (FinitePrime K))
    (i : Type u) (fi : Fintype i),
    letI : Fintype i := fi
    ∃ (indexPrime : i → T) (w : i → FinitePrime M)
      (b : Module.Basis i (ZMod p) (Additive Gal(M/L))),
      Function.Bijective indexPrime ∧
        (∀ q : FinitePrime K, q ∈ T →
          (Sum.inl q : NumberFieldPlace K) ∉ S) ∧
        (∀ j, (w j).under (OK K) = (indexPrime j : FinitePrime K)) ∧
        (∀ j, b j = Additive.ofMul
          (numberFrobeniusElement (K := L) (w j))) ∧
        (∀ j,
          galMLMK (K := K) (L := L) (M := M)
              (numberFrobeniusElement (K := L) (w j)) =
            numberFrobeniusElement (K := K) (w j))

/-- In an abelian number-field extension, arithmetic Frobenius depends only
on the prime downstairs. -/
theorem number_frobenius_element
    (Q R : FinitePrime M)
    (hunder : Q.under (OK K) = R.under (OK K))
    (hQunramified : Algebra.IsUnramifiedAt (OK K) Q.asIdeal) :
    numberFrobeniusElement (K := K) Q =
      numberFrobeniusElement (K := K) R := by
  let q : Ideal (OK K) := Q.asIdeal.under (OK K)
  letI : Q.asIdeal.LiesOver q := ⟨rfl⟩
  letI : R.asIdeal.LiesOver q := ⟨by
    change Q.asIdeal.under (OK K) = R.asIdeal.under (OK K)
    exact congrArg HeightOneSpectrum.asIdeal hunder⟩
  letI : Algebra.IsUnramifiedAt (OK K) Q.asIdeal := hQunramified
  obtain ⟨tau, htau⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup q Q.asIdeal R.asIdeal Gal(M/K)
  letI : Finite ((OK M) ⧸ (tau • Q.asIdeal : Ideal (OK M))) := by
    rw [htau]
    infer_instance
  have hconj := arith_frob_conjugate
    (R := OK K) (S := OK M) (G := Gal(M/K)) Q.asIdeal tau
  have hconjR : numberFrobeniusElement (K := K) R =
      tau * numberFrobeniusElement (K := K) Q * tau⁻¹ := by
    simpa only [numberFrobeniusElement, htau] using hconj
  rw [mul_comm tau, mul_assoc, mul_inv_cancel, mul_one] at hconjR
  exact hconjR.symm

/-- Lemma 6.2 from Proposition 4.7, finite-dimensional basis extraction,
and the one local completion/restriction bridge above. -/
theorem galMLStatement
    (h47 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ T : Finset (FinitePrime L),
            ContainsRamifiedPrimes (K := K) (L := L) T →
              frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤))
    (hlocal : CompletionRestrictionBridge.{u}) :
    (∀ (p : ℕ) (_hp : Nat.Prime p)
          (K L M : Type u)
          [Field K] [Field L] [Field M]
          [NumberField K] [NumberField L] [NumberField M]
          [Algebra K L] [Algebra L M] [Algebra K M]
          [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional L M]
          [IsGalois L M] [IsAbelianGalois K M],
          (primitiveRoots p K).Nonempty →
            ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
              (S : Finset (NumberFieldPlace K)),
              (∀ Q : FinitePrime M,
                (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
                  Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
              HasFrobeniusBasis (K := K) (L := L) (M := M)
                p hexponent S) := by
  classical
  intro p hp K L M
    _ _ _
    _ _ _
    _ _ _
    _
    _ _
    _ _
    _hroot hexponent S hunramified
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  have hexponentML : ∀ sigma : Gal(M/L), sigma ^ p = 1 :=
    gal_ml_pow (K := K) (L := L) (M := M) p hexponent
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p hexponentML
  let SM := finiteAboveBase (K := K) (M := M) S
  have hramifiedML : ContainsRamifiedPrimes (K := L) (L := M) SM := by
    intro Q hQSM
    have hQnotS :
        (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S := by
      simpa only [SM, primes_above_base] using hQSM
    letI : Algebra.IsUnramifiedAt (OK K) Q.asIdeal :=
      hunramified Q hQnotS
    exact Algebra.IsUnramifiedAt.of_restrictScalars (OK K) Q.asIdeal
  have hgenerate :
      frobeniusGeneratedSubgroup (K := L) (L := M) SM = ⊤ :=
    h47 L M SM hramifiedML
  let V := Additive Gal(M/L)
  let frobeniusVectors : Set V :=
    Additive.ofMul '' frobeniusElementsOutside (K := L) SM
  have hspan : Submodule.span (ZMod p) frobeniusVectors = ⊤ := by
    exact Towers.FFSelect.span_top_closure
      (p := p) hgenerate
  have htopSpan : ⊤ ≤ Submodule.span (ZMod p) frobeniusVectors := by
    rw [hspan]
  let i : Set V :=
    (linearIndepOn_empty (ZMod p) id).extend
      (Set.empty_subset frobeniusVectors)
  let b : Module.Basis i (ZMod p) V := Module.Basis.ofSpan htopSpan
  let fi : Fintype i := Fintype.ofFinite i
  letI : Fintype i := fi
  have hwexists : ∀ j : i, ∃ Q : FinitePrime M,
      Q ∉ SM ∧
        b j = Additive.ofMul
          (numberFrobeniusElement (K := L) Q) := by
    intro j
    have hbmem : b j ∈ frobeniusVectors :=
      Module.Basis.ofSpan_subset htopSpan (Set.mem_range_self j)
    rcases hbmem with ⟨sigma, ⟨Q, hQSM, hQsigma⟩, hsigma⟩
    refine ⟨Q, hQSM, ?_⟩
    rw [hQsigma]
    exact hsigma.symm
  choose w hwSM hwbasis using hwexists
  have hwNotS (j : i) :
      (Sum.inl ((w j).under (OK K)) : NumberFieldPlace K) ∉ S := by
    simpa only [SM, primes_above_base] using hwSM j
  have hwFrobNe (j : i) :
      numberFrobeniusElement (K := L) (w j) ≠ 1 := by
    intro hFrob
    have hbzero : b j = 0 := by
      rw [hwbasis j, hFrob]
      rfl
    exact b.ne_zero j hbzero
  have hwcompat (j : i) :
      galMLMK (K := K) (L := L) (M := M)
          (numberFrobeniusElement (K := L) (w j)) =
        numberFrobeniusElement (K := K) (w j) :=
    hlocal p hp K L M hexponent S hunramified (w j)
      (hwNotS j) (hwFrobNe j)
  let v : i → FinitePrime K := fun j ↦ (w j).under (OK K)
  have hvInjective : Function.Injective v := by
    intro j k hjk
    have hMK : numberFrobeniusElement (K := K) (w j) =
        numberFrobeniusElement (K := K) (w k) := by
      apply number_frobenius_element
        (K := K) (M := M) (w j) (w k) hjk
      exact hunramified (w j) (hwNotS j)
    have hML : numberFrobeniusElement (K := L) (w j) =
        numberFrobeniusElement (K := L) (w k) := by
      apply gal_ml_injective (K := K) (L := L) (M := M)
      rw [hwcompat j, hwcompat k, hMK]
    apply b.injective
    rw [hwbasis j, hwbasis k, hML]
  let T : Finset (FinitePrime K) := Finset.univ.image v
  let indexPrime : i → T := fun j ↦
    ⟨v j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hindexBijective : Function.Bijective indexPrime := by
    constructor
    · intro j k hjk
      apply hvInjective
      exact congrArg Subtype.val hjk
    · intro q
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp q.property
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact hj
  have hdisjoint : ∀ q : FinitePrime K, q ∈ T →
      (Sum.inl q : NumberFieldPlace K) ∉ S := by
    intro q hqT hqS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hqT
    exact hwNotS j hqS
  refine ⟨T, i, fi, indexPrime, w, b,
    hindexBijective, hdisjoint, ?_, hwbasis, hwcompat⟩
  intro j
  rfl

end

end Towers.CField.KNIndex
