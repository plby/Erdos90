import Towers.ClassField.HasseNorm.QuadraticFormPlace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Chapter VIII, Section 3, Corollary 3.6 -/

namespace Towers.CField.HNorm

open scoped TensorProduct
open NumberField
open Towers.CField.Ideles

noncomputable section
universe u

/-- Scalar extension preserves a represented scalar. -/
def RepresentationChangeBridge : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (c : K),
    Represents Q c →
      ∀ v, Represents (quadraticFormPlace K V Q v)
        (algebraMap K (placeCompletion K v) c)

/-- A nonzero representing vector remains nonzero after faithfully flat
scalar extension, and its quadratic value is carried by the algebra map. -/
theorem represented_scalar_change :
    RepresentationChangeBridge.{u} := by
  intro K V _ _ _ _ _ Q c
  rintro ⟨x, hx, hQx⟩ v
  refine ⟨(1 : placeCompletion K v) ⊗ₜ[K] x, ?_, ?_⟩
  · intro hzero
    exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K V x).mp hzero)
  · simp [quadraticFormPlace, QuadraticForm.baseChange_tmul, hQx,
      Algebra.smul_def]

/-- Base change distributes over the product defining `Q - cY²`.  The
scalar tensor factor is identified with the extension field itself. -/
noncomputable def adjoinChangeIsometry
    (K F V : Type u) [Field K] [Field F] [Algebra K F]
    [Invertible (2 : K)] [Invertible (2 : F)]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (c : K) :
    QuadraticMap.IsometryEquiv
      ((adjoinNegativeSquare Q c).baseChange F)
      (adjoinNegativeSquare (Q.baseChange F) (algebraMap K F c)) := by
  let e : F ⊗[K] (V × K) ≃ₗ[F] (F ⊗[K] V) × F :=
    (TensorProduct.prodRight K F F V K).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl F (F ⊗[K] V))
        (TensorProduct.AlgebraTensorModule.rid K F F))
  refine { toLinearEquiv := e, map_app' := ?_ }
  have hforms :
      (adjoinNegativeSquare (Q.baseChange F) (algebraMap K F c)).comp
          e.toLinearMap =
        (adjoinNegativeSquare Q c).baseChange F := by
    apply baseChange_ext
    rintro ⟨v, r⟩
    simp [e, adjoin_negative_square, QuadraticForm.baseChange_tmul,
      Algebra.smul_def]
  intro x
  exact DFunLike.congr_fun hforms x

/-- Base change commutes with the augmented form `Q-cY²`, and that form is
nondegenerate when `Q` is and `c ≠ 0`.  The implication displayed is exactly
the direction used in the local-to-global proof. -/
def AdjoinSquareBridge : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (c : K),
    Q.Nondegenerate → c ≠ 0 →
      (adjoinNegativeSquare Q c).Nondegenerate ∧
      ∀ v,
        Represents (quadraticFormPlace K V Q v)
          (algebraMap K (placeCompletion K v) c) →
        Represents
          (quadraticFormPlace K (V × K) (adjoinNegativeSquare Q c) v) 0

/-- The augmented form is nondegenerate, and a local vector representing
`c` gives the isotropic vector `(x,1)` after distributing base change over
the product. -/
theorem adjoinSquare : AdjoinSquareBridge.{u} := by
  intro K V _ _ _ _ _ Q c hQ hc
  have htwoK : (2 : K) ≠ 0 := by norm_num
  letI : NeZero (2 : K) := ⟨htwoK⟩
  letI : Invertible (2 : K) := invertibleOfNonzero htwoK
  refine ⟨adjoin_square_nondegenerate hQ hc, ?_⟩
  intro v hlocal
  let F := placeCompletion K v
  have htwoF : (2 : F) ≠ 0 := by
    intro h
    apply htwoK
    apply (algebraMap K F).injective
    simpa only [map_ofNat, map_zero] using h
  letI : Invertible (2 : F) := invertibleOfNonzero htwoF
  change Represents (Q.baseChange F) (algebraMap K F c) at hlocal
  change Represents ((adjoinNegativeSquare Q c).baseChange F) 0
  obtain ⟨x, hx, hQx⟩ := hlocal
  let e := adjoinChangeIsometry K F V Q c
  let y : F ⊗[K] (V × K) := e.symm (x, 1)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    have hpair : (x, (1 : F)) = 0 := by
      have h := congrArg e hy
      simp [y] at h
    exact one_ne_zero (congrArg Prod.snd hpair)
  · calc
      (adjoinNegativeSquare Q c).baseChange F y =
          adjoinNegativeSquare (Q.baseChange F) (algebraMap K F c) (e y) :=
        (e.map_app y).symm
      _ = 0 := by simp [y, adjoin_negative_square, hQx]

/-- **Corollary VIII.3.6 (source statement).** -/
def QuadraticFormRepresentation : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (c : K),
    Q.Nondegenerate →
      (Represents Q c ↔
        ∀ v, Represents (quadraticFormPlace K V Q v)
          (algebraMap K (placeCompletion K v) c))

theorem representationChangeBridge
    (h35 : (MinkowskiAlmostEverywhere.{u} ∧ HasseMinkowskiGlobal.{u}))
    (hbase : RepresentationChangeBridge.{u})
    (hadjoin : AdjoinSquareBridge.{u}) :
    QuadraticFormRepresentation.{u} := by
  intro K V _ _ _ _ _ Q c hQ
  constructor
  · exact hbase K V Q c
  · intro hlocal
    by_cases hc : c = 0
    · subst c
      exact h35.2 K V Q hQ (fun v => by simpa using hlocal v)
    · obtain ⟨hrNondegenerate, hlocalZero⟩ := hadjoin K V Q c hQ hc
      have hrZero : Represents (adjoinNegativeSquare Q c) 0 :=
        h35.2 K (V × K) (adjoinNegativeSquare Q c)
          hrNondegenerate (fun v => hlocalZero v (hlocal v))
      apply (represents_adjoin_anisotropic hQ hc).2
      intro hanisotropic
      obtain ⟨x, hx, hvalue⟩ := hrZero
      exact hx (hanisotropic x hvalue)

/-- Corollary VIII.3.6 now needs only the Hasse--Minkowski theorem itself;
the scalar-extension and augmented-form steps are proved above. -/
theorem representation_hasse_comparison
    (h35 : (MinkowskiAlmostEverywhere.{u} ∧ HasseMinkowskiGlobal.{u})) :
    QuadraticFormRepresentation.{u} :=
  representationChangeBridge h35 represented_scalar_change
    adjoinSquare

end
end Towers.CField.HNorm
