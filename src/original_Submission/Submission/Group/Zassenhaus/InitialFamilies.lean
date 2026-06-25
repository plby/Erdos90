import Submission.Group.Zassenhaus.HallSpecialization
import Submission.Group.Zassenhaus.Factors

/-!
# Initial scaled coordinate families for Hall power collection

Before higher corrections appear, one raw Hall coordinate from each repeated
block contributes the function `q ↦ e_s,i * q`.  If the original Hall exponent
family vanishes below an input weight `r`, these scaled coordinates have
explicit bounded repeated-block expansions at every Hall weight.

This supplies the base family consumed by the generic Hall-recipe
specialization bridge.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- Scale every coordinate of one Hall exponent family by the repetition count. -/
def scaledExponentFamily
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (e : HEFam H)
    (q : ℕ) :
    HEFam H :=
  fun s i => e s i * (q : ℤ)

/--
The explicit repeated-block expansion of one scaled raw Hall coordinate.
Below the initial nonzero weight it is zero; above that weight it is the
singleton selection `choose q 1`.
-/
noncomputable def scaledCoordinateExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (e : HEFam H)
    (s : ℕ)
    (i : (H s).index) :
    BCExp inputWeight s :=
  if hs : inputWeight ≤ s then
    (SPFactora.source (e s i)
      (⟨s, i⟩ : HEAddres H) hs).coordinateExpansion
  else
    BCExp.zero inputWeight s

/-- The raw scaled-coordinate expansion evaluates to `e_s,i * q`. -/
lemma scaled_coordinate_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (s : ℕ)
    (i : (H s).index) :
    (scaledCoordinateExpansion (inputWeight := inputWeight) e s i).eval =
      fun q : ℕ => scaledExponentFamily e q s i := by
  by_cases hs : inputWeight ≤ s
  · rw [scaledCoordinateExpansion, dif_pos hs]
    calc
      (SPFactora.source (e s i)
          (⟨s, i⟩ : HEAddres H) hs).coordinateExpansion.eval =
          (SPFactora.source (e s i)
            (⟨s, i⟩ : HEAddres H) hs).exponent :=
        SPFactora.coordinateExpansion_eval _
      _ = fun q : ℕ => scaledExponentFamily e q s i := by
        ext q
        simp [scaledExponentFamily]
  · have hsi : e s i = 0 := by
      rw [heBelow s (Nat.lt_of_not_ge hs)]
      rfl
    ext q
    simp [scaledCoordinateExpansion, hs,
      BCExp.eval_zero,
      scaledExponentFamily, hsi]

/--
A family of input Hall exponents vanishing below `inputWeight` yields an
explicit family of scaled repeated-power coordinate expansions.
-/
lemma scaled_exponent_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (heBelow :
      ∀ (j : ι) (s : ℕ), s < inputWeight → e j s = 0) :
    CEFam H ι inputWeight
      (fun q j => scaledExponentFamily (e j) q) := by
  intro j s i
  exact ⟨scaledCoordinateExpansion (inputWeight := inputWeight) (e j) s i,
    scaled_coordinate_expansion (e j) (heBelow j) s i⟩

/--
The scaled raw Hall coordinates therefore satisfy the Claim 5 polynomial
degree bounds.
-/
lemma scaled_exponent_family
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (e : ι → HEFam H)
    (heBelow :
      ∀ (j : ι) (s : ℕ), s < inputWeight → e j s = 0) :
    HallCoordinateFamily H ι inputWeight
      (fun q j => scaledExponentFamily (e j) q) :=
  CEFam.toPolynomialFamily hinputWeight
    (scaled_exponent_expansion e heBelow)

/--
Applying generic Hall coordinate recipes to scaled raw coordinates produces a
new explicit repeated-power coordinate expansion family.
-/
lemma recipes_scaled_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (R : κ → CHRecipe H ι)
    (hinputWeight : 0 < inputWeight)
    (e : ι → HEFam H)
    (heBelow :
      ∀ (j : ι) (s : ℕ), s < inputWeight → e j s = 0) :
    CEFam H κ inputWeight
      (fun q k => (R k).eval
        (fun j => scaledExponentFamily (e j) q)) :=
  recipes_expansion_family
    R hinputWeight
      (fun q j => scaledExponentFamily (e j) q)
      (scaled_exponent_family
        hinputWeight e heBelow)

end TCTex
end Submission
