import Submission.Group.Zassenhaus.CorrectionFormulas
import Submission.Group.Zassenhaus.PolynomialConstructorSupport

/-!
# Specializing Hall collection monomials along power-coordinate families

The generic product collector of TeX Claim 8 emits weighted products of
generalized binomial coefficients in Hall coordinates.  During repeated-power
collection those input Hall coordinates are themselves integer-valued
polynomials in the repetition count `q`.

This file proves that substituting such power-coordinate families into any
Claim 8 monomial yields an explicit bounded repeated-block expansion.  It then
lifts the construction over finite coordinate recipe lists.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace IVMost

/-- The constant function `1` is an integer-valued polynomial of every degree bound. -/
lemma one
    (degreeBound : ℕ) :
    IVMost
      (1 : ℕ → ℤ) degreeBound := by
  exact ⟨1, by simp, by simp⟩

/-- A finite product of integer-valued polynomials has the sum of their degree bounds. -/
lemma finsetProd
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℕ → ℤ)
    (degreeBound : ι → ℕ)
    (hf :
      ∀ i ∈ S,
        IVMost (f i) (degreeBound i)) :
    IVMost
      (fun q : ℕ => ∏ i ∈ S, f i q)
      (∑ i ∈ S, degreeBound i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using one 0
  | @insert a S ha ih =>
      have haPolynomial := hf a (by simp)
      have hSPolynomial := ih fun i hi => hf i (by simp [hi])
      simpa [ha] using haPolynomial.mul hSPolynomial

end IVMost

namespace Finset

/-- The sum of natural quotients is bounded by the quotient of the sum. -/
lemma le_div_sum
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℕ)
    (denominator : ℕ) :
    (∑ i ∈ S, f i / denominator) ≤
      (∑ i ∈ S, f i) / denominator := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact (Nat.add_le_add_left ih _).trans
        (Nat.add_div_le_add_div (f a) (∑ i ∈ S, f i) denominator)

end Finset

/--
A family of Hall exponent coordinates parametrized by `q`, with the Claim 5
polynomial degree bound at every ordinary Hall weight.
-/
def HallCoordinateFamily
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (inputWeight : ℕ)
    (E : ℕ → ι → HEFam H) :
    Prop :=
  ∀ (j : ι) (s : ℕ) (i : (H s).index),
    IVMost
      (fun q : ℕ => E q j s i) (s / inputWeight)

/--
A constructive power-coordinate family: every coordinate is supplied by an
explicit repeated-block expansion at its ordinary Hall weight.
-/
def CEFam
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (inputWeight : ℕ)
    (E : ℕ → ι → HEFam H) :
    Prop :=
  ∀ (j : ι) (s : ℕ) (i : (H s).index),
    ∃ expansion : BCExp inputWeight s,
      expansion.eval = fun q : ℕ => E q j s i

/-- Explicit power-coordinate expansions imply the Claim 5 polynomial bounds. -/
lemma CEFam.toPolynomialFamily
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {E : ℕ → ι → HEFam H}
    (hinputWeight : 0 < inputWeight)
    (hE : CEFam H ι inputWeight E) :
    HallCoordinateFamily H ι inputWeight E := by
  intro j s i
  obtain ⟨expansion, hexpansion⟩ := hE j s i
  rw [← hexpansion]
  exact expansion.integerValuedMost hinputWeight

namespace WHMono

/-- Substitute a power-coordinate family into one generic Claim 8 monomial. -/
def powerSpecialization
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (E : ℕ → ι → HEFam H)
    (m : WHMono H ι s) :
    ℕ → ℤ :=
  fun q : ℕ => m.eval (E q)

/--
Specializing a Claim 8 monomial along power-coordinate polynomials preserves
the Claim 5 degree bound.
-/
lemma specialization_valued_most
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (m : WHMono H ι s) :
    IVMost
      (m.powerSpecialization E) (s / inputWeight) := by
  let factor : Fin m.length → ℕ → ℤ := fun ν q =>
    Ring.choose
      (E q (m.input ν) (m.address ν).1 (m.address ν).2)
      (m.binomialIndex ν)
  have hfactor :
      ∀ ν : Fin m.length,
        IVMost
          (factor ν)
          ((m.binomialIndex ν * (m.address ν).1) / inputWeight) := by
    intro ν
    exact
      ((hE (m.input ν) (m.address ν).1 (m.address ν).2).ringChoose
        (m.binomialIndex ν)).mono
          (le_div_left
            (m.binomialIndex ν) (m.address ν).1 inputWeight)
  have hproduct :
      IVMost
        (fun q : ℕ => ∏ ν : Fin m.length, factor ν q)
        (∑ ν : Fin m.length,
          (m.binomialIndex ν * (m.address ν).1) / inputWeight) := by
    simpa using
      IVMost.finsetProd
        Finset.univ factor
          (fun ν =>
            (m.binomialIndex ν * (m.address ν).1) / inputWeight)
          (by
            intro ν _hν
            exact hfactor ν)
  apply hproduct.mono
  calc
    (∑ ν : Fin m.length,
        (m.binomialIndex ν * (m.address ν).1) / inputWeight) ≤
        (∑ ν : Fin m.length,
          m.binomialIndex ν * (m.address ν).1) / inputWeight :=
      Finset.le_div_sum Finset.univ
        (fun ν : Fin m.length =>
          m.binomialIndex ν * (m.address ν).1)
        inputWeight
    _ ≤ s / inputWeight :=
      Nat.div_le_div_right m.weightedWeight_le

/--
Normalize the specialization of one generic Hall monomial into explicit
repeated-block recipes.
-/
noncomputable def powerSpecializationExpansion
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (m : WHMono H ι s) :
    BCExp inputWeight s :=
  BCExp.binomialBasis inputWeight s hinputWeight
    (m.powerSpecialization E)

/-- The normalized specialization expansion evaluates to the original Claim 8 monomial. -/
lemma eval_specialization_expansion
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (m : WHMono H ι s) :
    (m.powerSpecializationExpansion hinputWeight E).eval =
      m.powerSpecialization E :=
  BCExp.eval_binomialBasis hinputWeight
    (m.specialization_valued_most E hE)

end WHMono

/-- Evaluate a finite sum of functions pointwise. -/
lemma list_sum_specialization
    {α M : Type*}
    [AddMonoid M]
    (L : List (α → M))
    (x : α) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil =>
      simp
  | cons f L ih =>
      simp [ih]

/--
Normalize a finite list of specialized Claim 8 monomials into one explicit
repeated-block expansion.
-/
noncomputable def monomialSpecializationExpansion
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (L : List (WHMono H ι s)) :
    BCExp inputWeight s :=
  BCExp.listSum inputWeight s
    (L.map fun m => m.powerSpecializationExpansion hinputWeight E)

/-- The normalized finite-list specialization evaluates to the sum of its monomials. -/
lemma monomial_specialization_expansion
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (L : List (WHMono H ι s)) :
    (monomialSpecializationExpansion
      hinputWeight E L).eval =
        fun q : ℕ => (L.map fun m => m.eval (E q)).sum := by
  ext q
  rw [monomialSpecializationExpansion,
    BCExp.eval_listSum,
    list_sum_specialization]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m hm
  simpa [WHMono.powerSpecialization] using
    congrFun
      (m.eval_specialization_expansion hinputWeight E hE) q

namespace CHRecipe

/--
Specialize one coordinate recipe list from the generic Hall collector into an
explicit repeated-power expansion.
-/
noncomputable def powerSpecializationExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (s : ℕ)
    (i : (H s).index) :
    BCExp inputWeight s :=
  monomialSpecializationExpansion
    hinputWeight E (R.recipes s i)

/-- Specialized generic coordinate recipes evaluate to the generic recipe coordinate. -/
lemma eval_specialization_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E)
    (s : ℕ)
    (i : (H s).index) :
    (R.powerSpecializationExpansion hinputWeight E s i).eval =
      fun q : ℕ => R.eval (E q) s i := by
  exact monomial_specialization_expansion
    hinputWeight E hE (R.recipes s i)

end CHRecipe

/--
A family of generic Hall coordinate recipe systems sends power-coordinate
polynomials to explicit repeated-block expansion families.
-/
lemma recipes_expansion_family
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (R : κ → CHRecipe H ι)
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E) :
    CEFam H κ inputWeight
      (fun q k => (R k).eval (E q)) := by
  intro k s i
  exact ⟨(R k).powerSpecializationExpansion hinputWeight E s i,
    (R k).eval_specialization_expansion hinputWeight E hE s i⟩

/--
Consequently, generic Hall coordinate recipes preserve the Claim 5 polynomial
degree bounds under substitution.
-/
lemma collected_recipes_family
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (R : κ → CHRecipe H ι)
    (hinputWeight : 0 < inputWeight)
    (E : ℕ → ι → HEFam H)
    (hE : HallCoordinateFamily H ι inputWeight E) :
    HallCoordinateFamily H κ inputWeight
      (fun q k => (R k).eval (E q)) :=
  (recipes_expansion_family
    R hinputWeight E hE).toPolynomialFamily hinputWeight

end TCTex
end Submission
