import Submission.ClassField.LocalReciprocity.LocalUnitsRep
import Submission.ClassField.LocalReciprocity.TowerMaps

/-!
# Milne, Class Field Theory, Lemma III.3.2

For a subgroup `H ≤ Gal(L/K)` we write its fixed field for Milne's
intermediate local field `E`.  This file states the two Artin tower squares
using the unconditional Artin equivalences of Theorem III.3.1 and packages
the exact forward Tate-naturality assertions from which they follow.

The degree-minus-two integral restriction and corestriction maps are already
available, but `TateTwoShift` stores only the chosen equivalences and no
naturality fields connecting them to those maps.  Consequently the two
forward assertions below are the remaining cup-product inputs, not
additional field-theoretic hypotheses.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteLocalNormResidueMulEquivValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteLocalNormResidueMulEquivValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The multiplicative form of the forward degree-minus-two isomorphism in
Theorem III.3.1. -/
noncomputable def localNormResidue :
    Abelianization Gal(L/K) ≃* (Kˣ ⧸ normSubgroup K L) :=
  let e : Additive (Abelianization Gal(L/K)) ≃+
      Additive (Kˣ ⧸ normSubgroup K L) :=
    localResidueEquiv K L
  { toFun := fun x => Additive.toMul (e (Additive.ofMul x))
    invFun := fun x => Additive.toMul (e.symm (Additive.ofMul x))
    left_inv := fun x => by
      change Additive.toMul (e.symm (e (Additive.ofMul x))) = x
      rw [e.symm_apply_apply]
      rfl
    right_inv := fun x => by
      change Additive.toMul (e (e.symm (Additive.ofMul x))) = x
      rw [e.apply_symm_apply]
      rfl
    map_mul' := fun x y => by
      rw [ofMul_mul, map_add, toMul_add] }

/-- The unconditional finite local Artin homomorphism, with no commutativity
assumption on the Galois group. -/
noncomputable def localArtinHom : Kˣ →* Abelianization Gal(L/K) :=
  (localNormResidue K L).symm.toMonoidHom.comp
    (QuotientGroup.mk' (normSubgroup K L))

@[simp]
theorem local_artin_hom (x : Kˣ) :
    localArtinHom K L x =
      (localNormResidue K L).symm
        (QuotientGroup.mk' (normSubgroup K L) x) :=
  rfl

/-- At every finite Galois level, the canonical Artin homomorphism has
exactly the norm subgroup as its kernel.  This is the finite-level content
of Theorem III.3.4(b), independent of tower naturality. -/
theorem artin_hom_ker :
    (localArtinHom K L).ker = normSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker, local_artin_hom]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply (localNormResidue K L).symm.injective
    simpa using hx
  · intro hx
    have hq : QuotientGroup.mk' (normSubgroup K L) x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    rw [hq, map_one]

/-- The finite local Artin homomorphism is surjective. -/
theorem artin_hom_surjective :
    Function.Surjective (localArtinHom K L) := by
  intro sigma
  let q := localNormResidue K L sigma
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (normSubgroup K L) q
  refine ⟨x, ?_⟩
  rw [local_artin_hom, hx]
  exact (localNormResidue K L).symm_apply_apply sigma

section FixedField

variable (H : Subgroup Gal(L/K))

private abbrev F := IntermediateField.fixedField H

/-- The forward fundamental-class equivalence over `E = Lᴴ`, transported
along the canonical identification `H ≃ Gal(L/E)`. -/
noncomputable def fixedResidueEquiv :
    Abelianization H ≃* ((F K L H)ˣ ⧸ normSubgroup (F K L H) L) := by
  let E := F K L H
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  exact (IntermediateField.subgroupEquivAlgEquiv H).abelianizationCongr.trans
    (localNormResidue E L)

/-- The Artin homomorphism for `L/E`, with its target written as `Hᵃᵇ`. -/
noncomputable def fixedArtinHom :
    (F K L H)ˣ →* Abelianization H :=
  (fixedResidueEquiv K L H).symm.toMonoidHom.comp
    (QuotientGroup.mk' (normSubgroup (F K L H) L))

@[simp]
theorem fixed_artin_hom (x : (F K L H)ˣ) :
    fixedArtinHom K L H x =
      (fixedResidueEquiv K L H).symm
        (QuotientGroup.mk' (normSubgroup (F K L H) L) x) :=
  rfl

/-- The left-hand diagram in Lemma III.3.2: field norm corresponds to the
map on abelianizations induced by `H → Gal(L/K)`. -/
def NormSquare : Prop :=
  (abelianizedSubgroupInclusion H).comp (fixedArtinHom K L H) =
    (localArtinHom K L).comp (normOnUnits K (F K L H))

/-- The right-hand diagram in Lemma III.3.2: inclusion of field units
corresponds to Verlag. -/
def InclusionSquare : Prop :=
  (subgroupVerlagerung H).comp (localArtinHom K L) =
    (fixedArtinHom K L H).comp (unitInclusion K (F K L H))

/-- The exact corestriction/cup-product naturality assertion for the forward
fundamental-class maps.  This is the forward form of the left-hand square. -/
def ForwardNormSquare : Prop :=
  (towerNormHom K (F K L H) L).comp
      (fixedResidueEquiv K L H).toMonoidHom =
    (localNormResidue K L).toMonoidHom.comp
      (abelianizedSubgroupInclusion H)

/-- The exact restriction/cup-product naturality assertion needed for the
right-hand square, stated on representatives so no unimplemented negative
Tate restriction map is hidden in the formulation. -/
def ForwardInclusionSquare : Prop :=
  ∀ g : Abelianization Gal(L/K), ∀ a : Kˣ,
    localNormResidue K L g =
        QuotientGroup.mk' (normSubgroup K L) a →
      fixedResidueEquiv K L H (subgroupVerlagerung H g) =
        QuotientGroup.mk' (normSubgroup (F K L H) L)
          (unitInclusion K (F K L H) a)

set_option maxRecDepth 10000 in
/-- Forward corestriction naturality implies the first Artin square. -/
theorem norm_square_forward
    (hforward : ForwardNormSquare K L H) :
    NormSquare K L H := by
  unfold NormSquare
  apply MonoidHom.ext
  intro x
  let q : (F K L H)ˣ ⧸ normSubgroup (F K L H) L :=
    QuotientGroup.mk' (normSubgroup (F K L H) L) x
  have hx := DFunLike.congr_fun hforward
    ((fixedResidueEquiv K L H).symm q)
  apply (localNormResidue K L).injective
  simpa [fixedArtinHom, localArtinHom, q] using hx.symm

set_option maxRecDepth 10000 in
/-- Forward restriction naturality implies the second Artin square. -/
theorem inclusion_square_forward
    (hforward : ForwardInclusionSquare K L H) :
    InclusionSquare K L H := by
  unfold InclusionSquare
  apply MonoidHom.ext
  intro a
  let g := (localNormResidue K L).symm
    (QuotientGroup.mk' (normSubgroup K L) a)
  have hg : localNormResidue K L g =
      QuotientGroup.mk' (normSubgroup K L) a :=
    (localNormResidue K L).apply_symm_apply _
  have h := hforward g a hg
  apply (fixedResidueEquiv K L H).injective
  simp only [MonoidHom.comp_apply, local_artin_hom,
    fixed_artin_hom, MulEquiv.apply_symm_apply]
  dsimp only [g] at h
  exact h

end FixedField

end

end Submission.CField.LRecip
