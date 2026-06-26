import Towers.NumberTheory.Density.SplittingPrimeDensity
import Towers.NumberTheory.Locals.WeakApproximationCompletion
import Towers.ClassField.Ideles.FiniteCoordinate
import Towers.ClassField.Ideles.LocalPlaceEmbeddings
import Towers.ClassField.NormIndex.CyclicSubextensionData

/-!
# Chapter VII, Section 4, Proposition 4.6

If a finite solvable Galois extension `L/K` is nontrivial, infinitely many
finite primes of `K` fail to split completely in `L`.

The proof follows Milne literally.  If there were only finitely many such
primes, put all of them in a finite set `S` and take `D = I^S`, the subgroup
of idèles which is `1` on `S` (with all infinite places implicit in `S`).
Complete splitting outside `S` puts `D` in the idèle norm range, while weak
approximation makes `Kˣ D` dense.  Lemma 4.5 then forces `[L : K] = 1`.

The current completion/idèle API does not yet export the assembly of local
preimages at completely split primes, and the restricted-product density
consequence of weak approximation is only present as a named proposition.
Those two exact inputs are isolated below; no density theorem for primes is
assumed.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open AbsoluteValue Filter Set Topology
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open scoped RestrictedProduct

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (OK K) K

/-- The finite family of coordinates retained when quotienting by
`IdelesAwayFrom K S`: the primes in `S` and every archimedean place. -/
private abbrev PlaceIndex
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :=
  {P : HeightOneSpectrum (OK K) // P ∈ S} ⊕ InfinitePlace K

private def absoluteValue
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    PlaceIndex K S → AbsoluteValue K ℝ
  | .inl P => (FinitePlace.mk P.1).1
  | .inr w => w.1

private def place
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    PlaceIndex K S → NumberFieldPlace K
  | .inl P => .inl P.1
  | .inr w => .inr w

private theorem absolute_nontrivial
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    ∀ i, (absoluteValue K S i).IsNontrivial := by
  intro i
  cases i with
  | inl P => exact finite_place_nontrivial (FinitePlace.mk P.1)
  | inr w => exact infinite_place_nontrivial w

private theorem absoluteValue_pairwise
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    Pairwise fun i j ↦
      ¬(absoluteValue K S i).IsEquiv
        (absoluteValue K S j) := by
  intro i j hij hequiv
  apply hij
  cases i with
  | inl P =>
      cases j with
      | inl Q =>
          congr 1
          apply Subtype.ext
          exact FinitePlace.mk_eq_iff.mp
            ((finite_place_equiv (FinitePlace.mk P.1)
              (FinitePlace.mk Q.1)).2 hequiv)
      | inr w =>
          exfalso
          apply infinite_place_nonarchimedean w
          exact (nonarchimedean_equiv hequiv).1
            (place_nonarchimedean (FinitePlace.mk P.1))
  | inr w =>
      cases j with
      | inl P =>
          exfalso
          apply infinite_place_nonarchimedean w
          exact (nonarchimedean_equiv hequiv).2
            (place_nonarchimedean (FinitePlace.mk P.1))
      | inr z =>
          congr 1
          exact (InfinitePlace.eq_iff_isEquiv (K := K)).2 hequiv

private def localCoordinateMap
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (i : PlaceIndex K S) :
    WithAbs (absoluteValue K S i) →
      placeCompletion K (place K S i) :=
  match i with
  | .inl P => fun x ↦ FinitePlace.embedding P.1 x.ofAbs
  | .inr w => fun x ↦ completionEmbedding w.1 x.ofAbs

private theorem local_coordinate_continuous
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (i : PlaceIndex K S) :
    Continuous (localCoordinateMap K S i) := by
  cases i with
  | inl P =>
      change Continuous (fun x : WithAbs (FinitePlace.mk P.1).1 ↦
        FinitePlace.embedding P.1 x.ofAbs)
      exact (show Isometry (fun x : WithAbs (FinitePlace.mk P.1).1 ↦
          FinitePlace.embedding P.1 x.ofAbs) by
        apply Isometry.of_dist_eq
        intro x y
        rw [dist_eq_norm, ← map_sub, FinitePlace.norm_embedding,
          dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
        change (HeightOneSpectrum.adicAbv K P.1)
          (x.ofAbs - y.ofAbs) =
            ‖FinitePlace.embedding P.1 (x - y).ofAbs‖
        rw [FinitePlace.norm_embedding, WithAbs.ofAbs_sub]).continuous
  | inr w =>
      simpa only [localCoordinateMap, completionEmbedding_apply,
        WithAbs.toAbs_ofAbs] using
        (UniformSpace.Completion.continuous_coe ( α := WithAbs w.1))

private theorem local_dense_range
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (i : PlaceIndex K S) :
    DenseRange (localCoordinateMap K S i) := by
  cases i with
  | inl P =>
      apply (P.1.denseRange_algebraMap (K := K)).mono
      rintro y ⟨x, rfl⟩
      refine ⟨(WithAbs.equiv (FinitePlace.mk P.1).1).symm x, ?_⟩
      rfl
  | inr w =>
      simpa only [localCoordinateMap, completionEmbedding_apply,
        WithAbs.toAbs_ofAbs] using
        (UniformSpace.Completion.denseRange_coe (α := WithAbs w.1))

/-- Weak approximation in the product of the actual completions at `S` and
at all archimedean places. -/
private theorem place_diagonal_range
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    DenseRange (fun x : K ↦ fun i : PlaceIndex K S ↦
      localCoordinateMap K S i
        ((WithAbs.equiv (absoluteValue K S i)).symm x)) := by
  let complete : ((i : PlaceIndex K S) →
      WithAbs (absoluteValue K S i)) →
      ((i : PlaceIndex K S) →
        placeCompletion K (place K S i)) :=
    fun z i ↦ localCoordinateMap K S i (z i)
  have hdenseComplete : DenseRange complete :=
    DenseRange.piMap fun i ↦ local_dense_range K S i
  have hcontinuousComplete : Continuous complete := by
    exact continuous_pi fun i ↦
      (local_coordinate_continuous K S i).comp
        (continuous_apply i)
  exact hdenseComplete.comp
    (weak_approximation_dense (absoluteValue K S)
      (absolute_nontrivial K S)
      (absoluteValue_pairwise K S))
    hcontinuousComplete

private def fieldDiagonal
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (x : K) :
    ∀ i : PlaceIndex K S,
      placeCompletion K (place K S i) :=
  fun i ↦ localCoordinateMap K S i
    ((WithAbs.equiv (absoluteValue K S i)).symm x)

private theorem field_diagonal_range
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    DenseRange (fieldDiagonal K S) :=
  place_diagonal_range K S

private def localUnitDiagonal
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (x : Kˣ) :
    ∀ i : PlaceIndex K S,
      (placeCompletion K (place K S i))ˣ
  | .inl P => Units.map (FinitePlace.embedding (K := K) P.1).toMonoidHom x
  | .inr w => Units.map (completionEmbedding (K := K) w.1).toMonoidHom x

private def localUnitVal
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    (∀ i : PlaceIndex K S,
      (placeCompletion K (place K S i))ˣ) →
      (∀ i : PlaceIndex K S,
        placeCompletion K (place K S i)) :=
  fun x i ↦ x i

private theorem local_val_open
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    IsOpenMap (localUnitVal K S) := by
  apply IsOpenMap.piMap
  · intro i
    cases i with
    | inl P =>
        change IsOpenMap (fun x : (P.1.adicCompletion K)ˣ ↦
          (x : P.1.adicCompletion K))
        exact Units.isOpenEmbedding_val.isOpenMap
    | inr w =>
        change IsOpenMap (fun x : w.1.Completionˣ ↦ (x : w.1.Completion))
        exact Units.isOpenEmbedding_val.isOpenMap
  · rw [cofinite_eq_bot]
    simp

private theorem field_diagonal_val
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) (x : Kˣ) :
    fieldDiagonal K S x =
      localUnitVal K S
        (localUnitDiagonal K S x) := by
  funext i
  cases i with
  | inl P =>
      change FinitePlace.embedding (K := K) P.1
          (((WithAbs.equiv (FinitePlace.mk P.1).1).symm (x : K)).ofAbs) =
        FinitePlace.embedding (K := K) P.1 (x : K)
      rfl
  | inr w =>
      change completionEmbedding (K := K) w.1
          (((WithAbs.equiv w.1).symm (x : K)).ofAbs) =
        completionEmbedding (K := K) w.1 (x : K)
      rfl

private theorem diagonal_dense_range
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    DenseRange (localUnitDiagonal K S) := by
  have hpre : Dense
      (localUnitVal K S ⁻¹'
        Set.range (fieldDiagonal K S)) :=
    (field_diagonal_range K S).preimage
      (local_val_open K S)
  have heq : localUnitVal K S ⁻¹'
      Set.range (fieldDiagonal K S) =
        Set.range (localUnitDiagonal K S) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      let w : InfinitePlace K := Classical.choice inferInstance
      let i : PlaceIndex K S := .inr w
      have hx0 : x ≠ 0 := by
        intro hzero
        have hi := congrFun hx i
        apply (z i).ne_zero
        change localUnitVal K S z i = 0
        rw [← hi, hzero]
        cases i <;> rfl
      let xu : Kˣ := Units.mk0 x hx0
      refine ⟨xu, ?_⟩
      funext i
      apply Units.ext
      have hi := congrFun hx i
      calc
        ((localUnitDiagonal K S xu i :
            (placeCompletion K (place K S i))ˣ) :
              placeCompletion K (place K S i)) =
            fieldDiagonal K S (x : K) i :=
          (congrFun (field_diagonal_val K S xu) i).symm
        _ = localUnitVal K S z i := hi
    · rintro ⟨x, rfl⟩
      refine ⟨(x : K), ?_⟩
      exact field_diagonal_val K S x
  rwa [heq] at hpre

private abbrev LocalUnits
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :=
  (∀ P : {P : HeightOneSpectrum (OK K) // P ∈ S},
      (P.1.adicCompletion K)ˣ) ×
    (∀ w : InfinitePlace K, w.Completionˣ)

/-- Projection to the coordinates killed by `IdelesAwayFrom K S`. -/
private noncomputable def coordinateMap
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    IK K →* LocalUnits K S where
  toFun a := (
    (fun P ↦ a.2.1 P.1),
    MulEquiv.piUnits a.1)
  map_one' := by
    apply Prod.ext
    · rfl
    · exact map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))
  map_mul' a b := by
    apply Prod.ext
    · rfl
    · exact map_mul (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))
          a.1 b.1

private noncomputable def localUnitsHomeomorph
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    (∀ i : PlaceIndex K S,
      (placeCompletion K (place K S i))ˣ) ≃ₜ
        LocalUnits K S :=
  Homeomorph.sumPiEquivProdPi
    {P : HeightOneSpectrum (OK K) // P ∈ S} (InfinitePlace K)
    (fun i ↦ (placeCompletion K (place K S i))ˣ)

private theorem principal_coordinate_diagonal
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) (x : Kˣ) :
    coordinateMap K S (principalIdele (OK K) K x) =
      localUnitsHomeomorph K S
        (localUnitDiagonal K S x) := by
  apply Prod.ext
  · funext P
    change (principalIdele (OK K) K x).2.1 P.1 =
      localUnitDiagonal K S x (.inl P)
    rw [principal_idele_finite]
    apply Units.ext
    change algebraMap K (P.1.adicCompletion K) (x : K) =
      FinitePlace.embedding P.1 (x : K)
    exact (show FinitePlace.embedding P.1 (x : K) =
      algebraMap K (P.1.adicCompletion K) (x : K) by rfl).symm
  · funext w
    change MulEquiv.piUnits (principalIdele (OK K) K x).1 w =
      localUnitDiagonal K S x (.inr w)
    rw [principal_idele_infinite]
    apply Units.ext
    rfl

private theorem principal_dense_range
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    DenseRange (fun x : Kˣ ↦
      coordinateMap K S (principalIdele (OK K) K x)) := by
  have hlocal : DenseRange (fun x : Kˣ ↦
      localUnitsHomeomorph K S
        (localUnitDiagonal K S x)) :=
    (localUnitsHomeomorph K S).surjective.denseRange.comp
      (diagonal_dense_range K S)
      (localUnitsHomeomorph K S).continuous
  convert hlocal using 1

private theorem cofinite_principal_compl
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    cofinite ≤ 𝓟 {P : HeightOneSpectrum (OK K) | P ∉ S} := by
  rw [le_principal_iff, mem_cofinite]
  simpa only [compl_setOf, not_not] using S.finite_toSet

private def finitePrincipalSection
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (x : ∀ P : {P : HeightOneSpectrum (OK K) // P ∈ S},
      (P.1.adicCompletion K)ˣ) :
    Πʳ P : HeightOneSpectrum (OK K),
      [(P.adicCompletion K)ˣ, IdeleUnitSubgroup (OK K) K P]_[𝓟
        {P : HeightOneSpectrum (OK K) | P ∉ S}] := by
  classical
  refine ⟨fun P ↦ if h : P ∈ S then x ⟨P, h⟩ else 1, ?_⟩
  rw [eventually_principal]
  intro P hP
  simp only [dif_neg hP]
  exact (IdeleUnitSubgroup (OK K) K P).one_mem

private theorem continuous_principal_section
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    Continuous (finitePrincipalSection K S) := by
  classical
  apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
  intro P
  by_cases hP : P ∈ S
  · change Continuous (fun x :
        (∀ Q : {Q : HeightOneSpectrum (OK K) // Q ∈ S},
          (Q.1.adicCompletion K)ˣ) ↦
        if h : P ∈ S then x ⟨P, h⟩ else
          (1 : (P.adicCompletion K)ˣ))
    simp only [hP]
    exact continuous_apply
      (⟨P, hP⟩ : {Q : HeightOneSpectrum (OK K) // Q ∈ S})
  · change Continuous (fun x :
        (∀ Q : {Q : HeightOneSpectrum (OK K) // Q ∈ S},
          (Q.1.adicCompletion K)ˣ) ↦
        if h : P ∈ S then x ⟨P, h⟩ else
          (1 : (P.adicCompletion K)ˣ))
    simp only [hP]
    exact continuous_const

/-- Simultaneously insert values in the finite set `S` and at every infinite
place. -/
private noncomputable def coordinateSection
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (x : LocalUnits K S) : IK K :=
  ((MulEquiv.piUnits : (InfiniteAdeleRing K)ˣ ≃*
      ((w : InfinitePlace K) → w.Completionˣ)).symm x.2,
    RestrictedProduct.inclusion
      (fun P : HeightOneSpectrum (OK K) ↦ (P.adicCompletion K)ˣ)
      (fun P ↦ (IdeleUnitSubgroup (OK K) K P :
        Set (P.adicCompletion K)ˣ))
      (cofinite_principal_compl K S)
      (finitePrincipalSection K S x.1))

private theorem continuous_CoordinateSection
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    Continuous (coordinateSection K S) := by
  apply (ContinuousMulEquiv.piUnits.symm.continuous.comp continuous_snd).prodMk
  exact (RestrictedProduct.continuous_inclusion
      (cofinite_principal_compl K S)).comp
    ((continuous_principal_section K S).comp continuous_fst)

set_option maxHeartbeats 1000000 in
-- Reducing the dependent restricted-product inclusion is elaboration-heavy.
private theorem coordinate_section_inverse
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    Function.RightInverse (coordinateSection K S)
      (coordinateMap K S) := by
  classical
  intro x
  apply Prod.ext
  · funext P
    change (coordinateSection K S x).2.1 P.1 = x.1 P
    change (if h : P.1 ∈ S then x.1 ⟨P.1, h⟩ else 1) = x.1 P
    simp only [dif_pos P.2]
  · exact MulEquiv.apply_symm_apply MulEquiv.piUnits x.2

private theorem coordinateSection_one
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    coordinateSection K S 1 = 1 := by
  classical
  apply Prod.ext
  · change (MulEquiv.piUnits : (InfiniteAdeleRing K)ˣ ≃*
        ((w : InfinitePlace K) → w.Completionˣ)).symm 1 = 1
    exact map_one (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ)).symm
  · apply RestrictedProduct.ext
    intro P
    by_cases hP : P ∈ S
    · change (if h : P ∈ S then (1 : (P.adicCompletion K)ˣ)
          else 1) = 1
      simp only [dif_pos hP]
    · change (if h : P ∈ S then (1 : (P.adicCompletion K)ˣ)
          else 1) = 1
      simp only [dif_neg hP]

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product group structure needs a larger synthesis budget.
/-- The coordinate projection is open because it has continuous translated
sections through every idèle. -/
theorem coordinate_open
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    IsOpenMap (coordinateMap K S) := by
  apply IsOpenMap.of_sections
  intro x
  let sectionAt : LocalUnits K S → IK K := fun y ↦
    x * coordinateSection K S
      ((coordinateMap K S x)⁻¹ * y)
  refine ⟨sectionAt, ?_, ?_, ?_⟩
  · apply Continuous.continuousAt
    exact continuous_const.mul
      ((continuous_CoordinateSection K S).comp
        (continuous_const.mul continuous_id))
  · dsimp only [sectionAt]
    simp [coordinateSection_one]
  · intro y
    dsimp only [sectionAt]
    rw [map_mul, coordinate_section_inverse]
    exact mul_inv_cancel_left _ _

/-- Weak approximation in the retained local coordinates gives the exact
restricted-product density statement used in Proposition 4.6. -/
theorem weakApproximationDensity
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))) :
    WeakApproximationDensity K S := by
  let principalCoordinates : Kˣ → LocalUnits K S := fun b ↦
    coordinateMap K S (principalIdele (OK K) K b)
  have hpre : Dense (coordinateMap K S ⁻¹'
      Set.range principalCoordinates) :=
    (principal_dense_range K S).preimage
      (coordinate_open K S)
  apply hpre.mono
  intro x hx
  obtain ⟨b, hb⟩ := hx
  let p : IK K := principalIdele (OK K) K b
  let a₀ : IK K := x * p⁻¹
  have ha₀ : a₀ ∈ IdelesAwayFrom K S := by
    rw [ideles_away]
    constructor
    · intro P hP
      have hcoord := congrArg
        (fun z : LocalUnits K S ↦ z.1 ⟨P, hP⟩) hb
      dsimp only [principalCoordinates, coordinateMap, p] at hcoord
      change p.2.1 P = x.2.1 P at hcoord
      change (x.2.1 P) * (p.2.1 P)⁻¹ = 1
      rw [← hcoord]
      exact mul_inv_cancel _
    · intro w
      have hcoord := congrArg
        (fun z : LocalUnits K S ↦ z.2 w) hb
      dsimp only [principalCoordinates, coordinateMap, p] at hcoord
      change MulEquiv.piUnits p.1 w = MulEquiv.piUnits x.1 w at hcoord
      change MulEquiv.piUnits (x.1 * p.1⁻¹) w = 1
      calc
        MulEquiv.piUnits (x.1 * p.1⁻¹) w =
            (MulEquiv.piUnits x.1 * MulEquiv.piUnits p.1⁻¹) w :=
          congrFun ((MulEquiv.piUnits : (InfiniteAdeleRing K)ˣ ≃*
            ((w : InfinitePlace K) → w.Completionˣ)).map_mul x.1 p.1⁻¹) w
        _ = MulEquiv.piUnits x.1 w * MulEquiv.piUnits p.1⁻¹ w := rfl
        _ = MulEquiv.piUnits x.1 w * (MulEquiv.piUnits p.1 w)⁻¹ := by
          congr 1
        _ = 1 := by rw [← hcoord]; exact mul_inv_cancel _
  refine ⟨⟨a₀, ha₀⟩, b, ?_⟩
  dsimp only [a₀, p]
  simp

/-- The exact local-norm consequence used in Proposition 4.6.  If every
finite prime outside `S` splits completely in `L`, then an idèle which is
`1` at `S` and at all infinite places is a norm from `L`.

This packages only the choice and restricted-product assembly of the local
norm preimages; its hypothesis uses the concrete `SplitsCompletelyAt`
predicate. -/
def SplitAwayBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K))),
    (∀ p : HeightOneSpectrum (OK K), p ∉ S →
      SplitsCompletelyAt K L p) →
    IdelesAwayFrom K S ≤ ideleNormSubgroup (K := K) (L := L)

/-- The restricted-product form of weak approximation used in Milne's
proof: `I^S Kˣ` is dense in the full idèle group. -/
def WeakApproximationBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K))),
    WeakApproximationDensity K S

/-- The weak-approximation bridge is discharged by the completion-product
weak approximation theorem and the open retained-coordinate projection. -/
theorem weakApproximationBridge :
    WeakApproximationBridge.{u} := by
  intro K _ _ S
  exact weakApproximationDensity K S

/-- **Proposition VII.4.6, source statement.**  A nontrivial finite solvable
Galois extension has infinitely many finite primes which do not split
completely.

The complement is taken inside the concrete type of finite primes of `K`.
The conclusion `[L : K] ≠ 1` is the type-theoretic formulation of
`L ≠ K`, as in Lemma 4.5. -/
def NontrivialNonsplitPrimes : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsSolvable Gal(L/K)],
    Module.finrank K L ≠ 1 →
      (splittingPrimes K L)ᶜ.Infinite

/-- Weak approximation for `I^S Kˣ` implies density of the literal
subgroup join `Kˣ · I^S`. -/
private theorem sup_ideles_away
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (OK K)))
    (hweak : WeakApproximationDensity K S) :
    Dense ((principalIdeles (OK K) K ⊔ IdelesAwayFrom K S :
      Subgroup (IK K)) : Set (IK K)) := by
  apply hweak.mono
  intro x hx
  obtain ⟨a, b, rfl⟩ := hx
  apply (principalIdeles (OK K) K ⊔ IdelesAwayFrom K S).mul_mem
  · exact (show IdelesAwayFrom K S ≤
        principalIdeles (OK K) K ⊔ IdelesAwayFrom K S from le_sup_right)
      a.property
  · exact (show principalIdeles (OK K) K ≤
        principalIdeles (OK K) K ⊔ IdelesAwayFrom K S from le_sup_left)
      ⟨b, rfl⟩

/-- Proposition 4.6 follows directly from Lemma 4.5 after choosing `S` to
be the finite set of nonsplitting primes. -/
theorem placeIndexStatement
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1))
    (hnorm : SplitAwayBridge.{u})
    (hweak : WeakApproximationBridge.{u}) :
    NontrivialNonsplitPrimes.{u} := by
  intro K L _ _ _ _ _ _ _ _ hnontrivial
  by_contra hinfinite
  have hfinite : (splittingPrimes K L)ᶜ.Finite :=
    Set.not_infinite.mp hinfinite
  let S : Finset (HeightOneSpectrum (OK K)) := hfinite.toFinset
  have hsplitOutside : ∀ p : HeightOneSpectrum (OK K), p ∉ S →
      SplitsCompletelyAt K L p := by
    intro p hpS
    by_contra hsplit
    apply hpS
    exact hfinite.mem_toFinset.mpr hsplit
  let D : Subgroup (IK K) := IdelesAwayFrom K S
  have hDnorm : D ≤ ideleNormSubgroup (K := K) (L := L) :=
    hnorm K L S hsplitOutside
  have hDdense : Dense
      ((principalIdeles (OK K) K ⊔ D : Subgroup (IK K)) : Set (IK K)) := by
    exact sup_ideles_away K S (hweak K S)
  exact hnontrivial (h45 K L D hDnorm hDdense)

/-- After discharging weak approximation, Proposition 4.6 depends only on
Lemma 4.5 and the assembly of split local norm preimages into an idèle. -/
theorem place_statement_away
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1))
    (hnorm : SplitAwayBridge.{u}) :
    NontrivialNonsplitPrimes.{u} :=
  placeIndexStatement h45 hnorm
    weakApproximationBridge

end

end Towers.CField.NIndex
