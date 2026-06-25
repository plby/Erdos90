import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.Ideles.Ideles
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic


/-!
# Galois actions on restricted products

This file isolates the algebraic step in the construction following
Proposition VII.2.3.  A multiplicative action on the full dependent product
which preserves the restricted-product condition induces a multiplicative
action, and hence an integral representation, on the restricted product.

For number-field ideles we also package the precise arithmetic data still
needed: an action on places, compatible equivalences between conjugate local
completions, and an action on the idele group satisfying Milne's coordinate
formula.  This keeps the statement tied to the actual `IdeleGroup` type rather
than to an unspecified abstract group.
-/

namespace Submission.CField.ICohomo

open Filter IsDedekindDomain NumberField Representation
open scoped RestrictedProduct
open Submission.CField.Ideles

noncomputable section

universe u v

variable {G W : Type u} [Group G]
variable (M : W → Type v) [∀ w, CommGroup (M w)]
variable (U : ∀ w, Subgroup (M w))

/-- A coordinatewise action on a full product preserves the restricted
product if it sends families which are locally integral almost everywhere
to families with the same property. -/
def PreservesRestrictedProduct
    [MulDistribMulAction G (∀ w, M w)] : Prop :=
  ∀ (sigma : G) (x : ∀ w, M w),
    (∀ᶠ w in cofinite, x w ∈ U w) →
      ∀ᶠ w in cofinite, (sigma • x) w ∈ U w

/-- Milne's coordinate formula plus preservation of every local unit subgroup
implies preservation of the cofinite restricted-product condition. -/
theorem preserves_restricted_coordinate
    [MulAction G W] [MulDistribMulAction G (∀ w, M w)]
    (transport : ∀ (sigma : G) (w : W), M (sigma⁻¹ • w) →* M w)
    (hcoordinate : ∀ (sigma : G) (x : ∀ w, M w) (w : W),
      (sigma • x) w = transport sigma w (x (sigma⁻¹ • w)))
    (hunits : ∀ (sigma : G) (w : W) (x : M (sigma⁻¹ • w)),
      x ∈ U (sigma⁻¹ • w) → transport sigma w x ∈ U w) :
    PreservesRestrictedProduct (G := G) M U := by
  intro sigma x hx
  rw [Filter.eventually_cofinite] at hx ⊢
  refine (hx.preimage (MulAction.injective sigma⁻¹).injOn).subset ?_
  intro w hw
  change ¬x (sigma⁻¹ • w) ∈ U (sigma⁻¹ • w)
  intro hunit
  apply hw
  rw [hcoordinate]
  exact hunits sigma w _ hunit

/-- The restricted-product action obtained by restricting an action on the
full product. -/
@[reducible]
def restrictedDistribAction
    [MulDistribMulAction G (∀ w, M w)]
    (hstable : PreservesRestrictedProduct (G := G) M U) :
    MulDistribMulAction G (Πʳ w, [M w, U w]) where
  smul sigma x := ⟨sigma • (x : ∀ w, M w), hstable sigma x x.2⟩
  one_smul x := by
    apply RestrictedProduct.ext
    intro w
    exact congrFun (one_smul G (x : ∀ w, M w)) w
  mul_smul sigma tau x := by
    apply RestrictedProduct.ext
    intro w
    exact congrFun (mul_smul sigma tau (x : ∀ w, M w)) w
  smul_one sigma := by
    apply RestrictedProduct.ext
    intro w
    exact congrFun (smul_one sigma : sigma • (1 : ∀ w, M w) = 1) w
  smul_mul sigma x y := by
    apply RestrictedProduct.ext
    intro w
    exact congrFun (smul_mul' sigma (x : ∀ w, M w) (y : ∀ w, M w)) w

@[simp]
theorem restricted_product_smul
    [MulDistribMulAction G (∀ w, M w)]
    (hstable : PreservesRestrictedProduct (G := G) M U)
    (sigma : G) (x : Πʳ w, [M w, U w]) (w : W) :
    letI := restrictedDistribAction M U hstable
    (sigma • x) w = (sigma • (x : ∀ w, M w)) w :=
  rfl

/-- The integral representation carried by a multiplicative restricted
product. -/
def restrictedProductRepresentation
    [MulDistribMulAction G (∀ w, M w)]
    (hstable : PreservesRestrictedProduct (G := G) M U) : Rep ℤ G := by
  letI := restrictedDistribAction M U hstable
  exact Rep.ofMulDistribMulAction G (Πʳ w, [M w, U w])

section NumberFieldIdeles

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

abbrev RingOfIntegers (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

/-- The local multiplicative group at a finite or infinite place. -/
abbrev PlaceUnits (F : Type u) [Field F] [NumberField F]
    (w : NumberFieldPlace F) :=
  (placeCompletion F w)ˣ

/-- Extract the coordinate of an idele at a finite or infinite place. -/
def ideleCoordinate
    (x : IdeleGroup (RingOfIntegers L) L) (w : NumberFieldPlace L) :
    PlaceUnits L w := by
  cases w with
  | inl w =>
      exact (show Πʳ v : HeightOneSpectrum (RingOfIntegers L),
          [(v.adicCompletion L)ˣ, IdeleUnitSubgroup (RingOfIntegers L) L v]
        from x.2).1 w
  | inr w => exact MulEquiv.piUnits x.1 w

@[simp]
theorem ideleCoordinate_finite
    (x : IdeleGroup (RingOfIntegers L) L)
    (w : HeightOneSpectrum (RingOfIntegers L)) :
    ideleCoordinate x (.inl w) =
      (show Πʳ v : HeightOneSpectrum (RingOfIntegers L),
          [(v.adicCompletion L)ˣ, IdeleUnitSubgroup (RingOfIntegers L) L v]
        from x.2).1 w :=
  rfl

@[simp]
theorem ideleCoordinate_infinite
    (x : IdeleGroup (RingOfIntegers L) L) (w : InfinitePlace L) :
    ideleCoordinate x (.inr w) = MulEquiv.piUnits x.1 w :=
  rfl

/-- The diagonal embedding of `L×` into one local multiplicative group. -/
def placePrincipalUnit (w : NumberFieldPlace L) :
    Lˣ →* PlaceUnits L w :=
  Units.map (placeEmbedding L w)

/-- IdeleGroup are determined by all of their finite and infinite local
coordinates. -/
theorem ideles_ext
    {x y : IdeleGroup (RingOfIntegers L) L}
    (h : ∀ w : NumberFieldPlace L,
      ideleCoordinate x w = ideleCoordinate y w) : x = y := by
  apply Prod.ext
  · apply MulEquiv.piUnits.injective
    funext w
    exact h (.inr w)
  · apply RestrictedProduct.ext
    intro w
    exact h (.inl w)

/-- Every coordinate of a principal idele is the corresponding completed
image of the global unit. -/
@[simp]
theorem idele_coordinate_principal
    (x : Lˣ) (w : NumberFieldPlace L) :
    ideleCoordinate
        (principalIdele (RingOfIntegers L) L x) w =
      placePrincipalUnit w x := by
  cases w with
  | inl w =>
      apply Units.ext
      rfl
  | inr w =>
      apply Units.ext
      rfl

/-- **The Galois action on ideles following Proposition VII.2.3.**

This structure states the missing arithmetic construction against the actual
idele group.  `placeAction` is the permutation of finite and infinite places,
`transport` is the extension of `sigma` between the corresponding local
completions, and `action` is the resulting multiplicative action on ideles.
The last field is precisely Milne's formula

`(sigma * alpha)(w) = sigma (alpha (sigma^-1 * w))`.

Constructing this data now amounts to connecting integral-closure prime
transport and infinite-place transport to the completion equivalences already
available for absolute values. -/
structure IAData where
  placeAction : MulAction Gal(L/K) (NumberFieldPlace L)
  preserves_finite : ∀ (sigma : Gal(L/K))
      (w : HeightOneSpectrum (RingOfIntegers L)),
    ∃ w' : HeightOneSpectrum (RingOfIntegers L),
      placeAction.smul sigma (.inl w) = .inl w'
  preserves_infinite : ∀ (sigma : Gal(L/K)) (w : InfinitePlace L),
    ∃ w' : InfinitePlace L, placeAction.smul sigma (.inr w) = .inr w'
  transport : ∀ (sigma : Gal(L/K)) (w : NumberFieldPlace L),
    PlaceUnits L (placeAction.smul sigma⁻¹ w) ≃* PlaceUnits L w
  continuous_transport : ∀ (sigma : Gal(L/K)) (w : NumberFieldPlace L),
    Continuous (transport sigma w)
  action : MulDistribMulAction Gal(L/K) (IdeleGroup (RingOfIntegers L) L)
  transport_principal : ∀ (sigma : Gal(L/K)) (w : NumberFieldPlace L)
      (x : Lˣ),
    transport sigma w
        (placePrincipalUnit (placeAction.smul sigma⁻¹ w) x) =
      placePrincipalUnit w (Units.map sigma.toRingEquiv.toRingHom x)
  coordinate_formula : ∀ (sigma : Gal(L/K))
      (x : IdeleGroup (RingOfIntegers L) L) (w : NumberFieldPlace L),
    ideleCoordinate (action.smul sigma x) w =
      transport sigma w (ideleCoordinate x (placeAction.smul sigma⁻¹ w))
  continuous_action : ∀ sigma : Gal(L/K), Continuous (action.smul sigma)

/-- The integral Galois representation on the idele group supplied by
`IAData`. -/
def IAData.representation
    (D : IAData (K := K) (L := L)) : Rep ℤ Gal(L/K) := by
  letI := D.action
  exact Rep.ofMulDistribMulAction Gal(L/K)
    (IdeleGroup (RingOfIntegers L) L)

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- The action supplied by `D` sends the principal idele of `x` to the
principal idele of `sigma x`. -/
theorem IAData.smul_principalIdele
    (D : IAData (K := K) (L := L))
    (sigma : Gal(L/K)) (x : Lˣ) :
    D.action.smul sigma (principalIdele (RingOfIntegers L) L x) =
      principalIdele (RingOfIntegers L) L
        (Units.map sigma.toRingEquiv.toRingHom x) := by
  apply ideles_ext
  intro w
  rw [D.coordinate_formula, idele_coordinate_principal,
    D.transport_principal, idele_coordinate_principal]

/-- The canonical equivariant diagonal embedding `Lˣ → I_L`. -/
def IAData.principalIdeleHom
    (D : IAData (K := K) (L := L)) :
    Rep.ofAlgebraAutOnUnits K L ⟶ D.representation :=
  Rep.ofHom
    { toLinearMap :=
        (MonoidHom.toAdditive
          (principalIdele (RingOfIntegers L) L)).toIntLinearMap
      isIntertwining' := fun sigma => by
        ext x
        change principalIdele (RingOfIntegers L) L
            (Units.map sigma.toRingEquiv.toRingHom x.toMul) =
          D.action.smul sigma
            (principalIdele (RingOfIntegers L) L x.toMul)
        exact (D.smul_principalIdele sigma x.toMul).symm }

/-- A proposition-valued form of the missing construction, convenient for
the statement inventory. -/
def NumberGaloisRepresentation : Prop :=
  Nonempty (IAData (K := K) (L := L))

end NumberFieldIdeles

end

end Submission.CField.ICohomo
