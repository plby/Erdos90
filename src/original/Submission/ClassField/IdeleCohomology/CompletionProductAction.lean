import Submission.ClassField.IdeleCohomology.CompletionConjugation
import Submission.ClassField.IdeleCohomology.DecompositionStatements
import Submission.NumberTheory.Completions.PlaceFactorCorrespondence
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.Pi.Units

/-!
# Galois action on products of completions

This file carries out the construction preceding Milne, Chapter VII, Lemma
2.1.  For a fixed absolute value `v` of `K`, the Galois group of `L / K`
acts on the absolute values of `L` above `v`, on their completions, and hence
on the dependent product of those completions by

`(sigma * alpha)(w) = sigma(alpha(sigma^-1 * w))`.
-/

namespace Submission.CField.ICohomo

open AbsoluteValue
open Submission.NumberTheory.Milne

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The absolute values of `L` extending a fixed absolute value of `K`. -/
abbrev CompletionPlacesAbove (v : AbsoluteValue K ℝ) :=
  {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}

/-- Galois conjugation preserves the property of lying above `v`. -/
instance completionPlacesAction (v : AbsoluteValue K ℝ) :
    MulAction Gal(L/K) (CompletionPlacesAbove (L := L) v) where
  smul sigma w := ⟨sigma • w.1, by
    constructor
    ext x
    change w.1 (sigma.symm (algebraMap K L x)) = v x
    rw [sigma.symm.commutes]
    exact DFunLike.congr_fun w.2.comp_eq x⟩
  one_smul w := Subtype.ext (one_smul Gal(L/K) w.1)
  mul_smul sigma tau w := Subtype.ext (mul_smul sigma tau w.1)

@[simp]
theorem places_above_val
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) v) :
    (sigma • w).1 = sigma • w.1 :=
  rfl

/-- The family of completions above `v`. -/
abbrev CompletionFamilyAbove (v : AbsoluteValue K ℝ)
    (w : CompletionPlacesAbove (L := L) v) :=
  w.1.Completion

/-- The coordinate transport from the completion at `sigma^-1 * w` to the
completion at `w`. -/
def completionFamilyTransport
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) v) :
    CompletionFamilyAbove v (sigma⁻¹ • w) ≃+* CompletionFamilyAbove v w :=
  completionTransport sigma w.1

/-- Milne's action formula on the product of all completions above `v`. -/
def completionProductAction
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w) :
    ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w :=
  fun w => completionFamilyTransport v sigma w (alpha (sigma⁻¹ • w))

@[simp]
theorem completion_product_action
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w)
    (w : CompletionPlacesAbove (L := L) v) :
    completionProductAction v sigma alpha w =
      completionFamilyTransport v sigma w (alpha (sigma⁻¹ • w)) :=
  rfl

/-- The diagonal family obtained by embedding one global element in every
completion above `v`. -/
def completionGlobalEmbedding
    (v : AbsoluteValue K ℝ) (x : L) :
    ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w :=
  fun w => completionEmbedding w.1 x

/-- Condition (c) in the construction preceding Lemma VII.2.1: the product
action sends the diagonal family attached to `x` to that attached to
`sigma x`. -/
theorem action_global_embedding
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K)) (x : L) :
    completionProductAction v sigma (completionGlobalEmbedding v x) =
      completionGlobalEmbedding v (sigma x) := by
  funext w
  exact completion_transport_embedding sigma w.1 x

/-- The diagonal embedding of the completed base field into all completions
above `v`. -/
def completionBaseDiagonal
    (v : AbsoluteValue K ℝ) (b : v.Completion) :
    ∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w :=
  fun w => completionLies v w.1 w.2 b

/-- Condition (b) in the construction preceding Lemma VII.2.1: every
element of the diagonal copy of `K_v` is fixed by the Galois action. -/
theorem action_base_diagonal
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K)) (b : v.Completion) :
    completionProductAction v sigma (completionBaseDiagonal v b) =
      completionBaseDiagonal v b := by
  funext w
  have hfun :
      (fun c : v.Completion => completionFamilyTransport v sigma w
        (completionLies v (sigma⁻¹ • w).1 (sigma⁻¹ • w).2 c)) =
      fun c : v.Completion => completionLies v w.1 w.2 c :=
    (dense_range_embedding v).equalizer
      ((completionTransport_isometry sigma w.1).continuous.comp
        (completion_lies_isometry v
          (sigma⁻¹ • w).1 (sigma⁻¹ • w).2).continuous)
      (completion_lies_isometry v w.1 w.2).continuous
      (funext fun x => by
        change completionFamilyTransport v sigma w
            (completionLies v (sigma⁻¹ • w).1
              (sigma⁻¹ • w).2 (completionEmbedding v x)) =
          completionLies v w.1 w.2 (completionEmbedding v x)
        rw [show completionLies v (sigma⁻¹ • w).1
              (sigma⁻¹ • w).2 (completionEmbedding v x) =
            completionEmbedding (sigma⁻¹ • w).1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v
              (sigma⁻¹ • w).1 (sigma⁻¹ • w).2) x]
        rw [show completionLies v w.1 w.2 (completionEmbedding v x) =
            completionEmbedding w.1 (algebraMap K L x) by
          exact RingHom.congr_fun (completion_lies_comp v w.1 w.2) x]
        change completionTransport sigma w.1
            (completionEmbedding (sigma⁻¹ • w.1) (algebraMap K L x)) =
          completionEmbedding w.1 (algebraMap K L x)
        rw [completion_transport_embedding]
        simp)
  exact congrFun hfun b

/-- Galois transport between two conjugate completion coordinates is an
algebra equivalence over the fixed base completion. -/
def completionTransportAlg
    (v : AbsoluteValue K ℝ) (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Algebra v.Completion (sigma⁻¹ • w).1.Completion :=
      (completionLies v (sigma⁻¹ • w).1 (sigma⁻¹ • w).2).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    (sigma⁻¹ • w).1.Completion ≃ₐ[v.Completion] w.1.Completion := by
  letI : Algebra v.Completion (sigma⁻¹ • w).1.Completion :=
    (completionLies v (sigma⁻¹ • w).1 (sigma⁻¹ • w).2).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  exact AlgEquiv.ofRingEquiv
    (f := completionFamilyTransport v sigma w) (fun b => by
      exact congrFun (action_base_diagonal v sigma b) w)

/-- The identity element acts trivially on the product of completions. -/
theorem completion_action_one
    (v : AbsoluteValue K ℝ)
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w) :
    completionProductAction v 1 alpha = alpha := by
  funext w
  have hw : (1 : Gal(L/K))⁻¹ • w = w := by simp
  cases hw
  change (completionGaloisRing (1 : Gal(L/K))⁻¹ w.1).symm
      (alpha w) = alpha w
  rw [galois_ring_inv]
  rfl

/-- The coordinate formula respects multiplication in the Galois group. -/
theorem completion_action_mul
    (v : AbsoluteValue K ℝ) (sigma tau : Gal(L/K))
    (alpha : ∀ w : CompletionPlacesAbove (L := L) v,
      CompletionFamilyAbove v w) :
    completionProductAction v (sigma * tau) alpha =
      completionProductAction v sigma (completionProductAction v tau alpha) := by
  funext w
  have hw : (sigma * tau)⁻¹ • w = tau⁻¹ • sigma⁻¹ • w := by
    rw [mul_inv_rev, mul_smul]
  cases hw
  change (completionGaloisRing (sigma * tau)⁻¹ w.1).symm
      (alpha (tau⁻¹ • sigma⁻¹ • w)) =
    (completionGaloisRing sigma⁻¹ w.1).symm
      ((completionGaloisRing tau⁻¹ (sigma⁻¹ • w.1)).symm
        (alpha (tau⁻¹ • sigma⁻¹ • w)))
  rw [completion_galois_inv]
  rfl

/-- **Construction preceding Lemma VII.2.1.** The coordinate formula defines
a genuine Galois action on the product of completions above `v`. -/
theorem completionGaloisAction
    (v : AbsoluteValue K ℝ) :
    ProductGaloisAction
      (CompletionFamilyAbove (L := L) v)
      (fun sigma w => completionFamilyTransport v sigma w)
      (completionProductAction v) := by
  refine ⟨completion_action_one v, completion_action_mul v, ?_⟩
  intro sigma alpha w
  rfl

/-- **Lemma VII.2.1.** Each Galois automorphism acts continuously on the
product of completions endowed with its product topology. -/
theorem galois_action_continuous
    (v : AbsoluteValue K ℝ) :
    ContinuousGaloisAction
      (CompletionFamilyAbove (L := L) v)
      (fun sigma w => completionFamilyTransport v sigma w)
      (completionProductAction v) := by
  refine ⟨completionGaloisAction v, ?_⟩
  intro sigma
  exact continuous_pi fun w =>
    (completionTransport_isometry sigma w.1).continuous.comp
      (continuous_apply (sigma⁻¹ • w))

/-- The completion-product action preserves its coordinatewise ring
structure.  This is the algebraic action used in Proposition VII.2.2. -/
@[reducible]
def completionSemiringAction
    (v : AbsoluteValue K ℝ) :
    MulSemiringAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) where
  smul := completionProductAction v
  one_smul := completion_action_one v
  mul_smul := completion_action_mul v
  smul_zero sigma := by
    funext w
    exact (completionFamilyTransport v sigma w).map_zero
  smul_add sigma alpha beta := by
    funext w
    exact (completionFamilyTransport v sigma w).map_add _ _
  smul_one sigma := by
    funext w
    exact (completionFamilyTransport v sigma w).map_one
  smul_mul sigma alpha beta := by
    funext w
    exact (completionFamilyTransport v sigma w).map_mul _ _

/-- The induced action on the units of the completion product. -/
@[reducible]
def unitsDistribAction
    (v : AbsoluteValue K ℝ) :
    MulDistribMulAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)ˣ := by
  letI : MulSemiringAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w) :=
    completionSemiringAction v
  exact Units.mulDistribMulActionRight

/-- The canonical identification of the units of the completion product with
the product of the local multiplicative groups. -/
def completionUnitsPi
    (v : AbsoluteValue K ℝ) :
    (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)ˣ ≃*
      (∀ w : CompletionPlacesAbove (L := L) v,
        (CompletionFamilyAbove v w)ˣ) :=
  MulEquiv.piUnits

/-- The integral Galois representation on the multiplicative group
`prod_{w | v} L_w^x` used in Propositions VII.2.2 and VII.2.3. -/
def completionUnitsRepresentation
    (v : AbsoluteValue K ℝ) : Rep ℤ Gal(L/K) := by
  letI : MulDistribMulAction Gal(L/K)
      (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)ˣ :=
    unitsDistribAction v
  exact Rep.ofMulDistribMulAction Gal(L/K)
    (∀ w : CompletionPlacesAbove (L := L) v, CompletionFamilyAbove v w)ˣ

end

end Submission.CField.ICohomo
