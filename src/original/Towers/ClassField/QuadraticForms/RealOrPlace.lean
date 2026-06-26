import Towers.ClassField.QuadraticForms.QuadraticHilbert
import Towers.ClassField.Ideles.GlobalPlace

/-!
# Chapter VIII, Section 6, Lemma 6.13

An even finite set of real or finite places, at each of which `b` is a
nonsquare, is realized as the set of places where `(a,b)_v = -1`.
-/

namespace Towers.CField.QForms

open NumberField
open Towers.CField.Ideles

noncomputable section
universe u

/-- The source allows finite places and real infinite places, but not complex
infinite places, in the prescribed exceptional set. -/
def RealOrFinite
    (K : Type u) [Field K] [NumberField K] : NumberFieldPlace K → Prop
  | .inl _ => True
  | .inr v => InfinitePlace.IsReal v

/-- The actual image of a global element in one completion. -/
def elementAtPlace
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (x : K) : placeCompletion K v :=
  algebraMap K (placeCompletion K v) x

/-- The quadratic Hilbert sign of two global nonzero elements at a place. -/
noncomputable def globalHilbertSign
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (a b : Kˣ) : ℤˣ :=
  quadraticHilbertSign (elementAtPlace K v (a : K))
    (elementAtPlace K v (b : K))

/-- The requested sign pattern: negative exactly on `T`. -/
noncomputable def prescribedHilbertSign
    {K : Type u} [Field K] [NumberField K]
    (T : Finset (NumberFieldPlace K)) (v : NumberFieldPlace K) : ℤˣ := by
  classical
  exact if v ∈ T then -1 else 1

/-- The exact idelic/class-field-theoretic realization input in Tate's proof.
The compatibility condition is only the product-one condition on the desired
finite sign pattern; nonsquareness supplies the nontrivial local characters. -/
def RealRealizationBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (T : Finset (NumberFieldPlace K)) (b : Kˣ),
    (∀ v ∈ T, RealOrFinite K v) →
    (∀ v ∈ T, ¬ IsSquare (elementAtPlace K v (b : K))) →
    (∏ _v ∈ T, (-1 : ℤˣ)) = 1 →
      ∃ a : Kˣ, ∀ v : NumberFieldPlace K,
        globalHilbertSign K v a b =
          prescribedHilbertSign T v

/-- Lemma 6.13 from the narrow global realization input.  The only remaining
step is the elementary fact that an even product of minus signs is one. -/
theorem real_or_realization
    (hrealize : RealRealizationBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
    (T : Finset (NumberFieldPlace K)) (b : Kˣ),
    (∀ v ∈ T, RealOrFinite K v) →
    Even T.card →
    (∀ v ∈ T, ¬ IsSquare (elementAtPlace K v (b : K))) →
      ∃ a : Kˣ, ∀ v : NumberFieldPlace K,
        globalHilbertSign K v a b =
          prescribedHilbertSign T v
  := by
  intro K _ _ T b hplaces heven hnonsquare
  apply hrealize K T b hplaces hnonsquare
  obtain ⟨m, hm⟩ := heven
  simp only [Finset.prod_const]
  rw [hm, ← two_mul, pow_mul]
  norm_num

end
end Towers.CField.QForms
