import Towers.Group.Zassenhaus.InitialFamilies

/-!
# Feeding explicit power-coordinate families into Claim 5

The remaining group-theoretic obligation of a repeated-power collector is a
recollected-product identity.  Once that identity and explicit coordinate
expansions are available, this file constructs the coordinate expansion data
and polynomial data consumed by TeX Claim 5.

It also specializes the adapter to generic Hall coordinate recipe systems
applied to scaled raw input coordinates.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
An explicit coordinate expansion family and its recollected-product identity
construct the expansion-data interface consumed by Claim 5.
-/
theorem collected_data_family
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (E : ℕ → HEFam H)
    (hEproduct :
      ∀ q : ℕ,
        collectedHallProduct (n := n) H (E q) =
          collectedHallProduct (n := n) H e ^ q)
    (hE :
      CEFam H Unit inputWeight
        (fun q _ => E q)) :
    CEData (n := n) H e inputWeight := by
  intro _heBelow
  refine ⟨E, hEproduct, ?_⟩
  intro s _hs _hsn i
  exact hE () s i

/--
The same explicit-family input therefore constructs the polynomial-data
interface consumed directly by Claim 5.
-/
theorem collected_expansion_family
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (E : ℕ → HEFam H)
    (hEproduct :
      ∀ q : ℕ,
        collectedHallProduct (n := n) H (E q) =
          collectedHallProduct (n := n) H e ^ q)
    (hE :
      CEFam H Unit inputWeight
        (fun q _ => E q)) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  CEData.toPolynomialData hinputWeight
    (collected_data_family E hEproduct hE)

/--
If generic Hall coordinate recipes recollect a power and their raw input
coordinates vanish below `inputWeight`, specialization constructs the explicit
power-coordinate expansion data for Claim 5.
-/
theorem expansion_scaled_recipes
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    {ι : Type}
    (hinputWeight : 0 < inputWeight)
    (inputs : ι → HEFam H)
    (hinputsBelow :
      ∀ (j : ι) (s : ℕ), s < inputWeight → inputs j s = 0)
    (R : CHRecipe H ι)
    (hRproduct :
      ∀ q : ℕ,
        collectedHallProduct (n := n) H
            (R.eval (fun j => scaledExponentFamily (inputs j) q)) =
          collectedHallProduct (n := n) H e ^ q) :
    CEData (n := n) H e inputWeight := by
  let E : ℕ → HEFam H :=
    fun q => R.eval (fun j => scaledExponentFamily (inputs j) q)
  apply collected_data_family E
  · simpa [E] using hRproduct
  · exact
      recipes_scaled_expansion
        (fun _ : Unit => R) hinputWeight inputs hinputsBelow

/--
Scaled generic Hall recipes satisfying the recollected-product identity
therefore construct the polynomial input required by Claim 5.
-/
theorem collected_scaled_recipes
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    {ι : Type}
    (hinputWeight : 1 ≤ inputWeight)
    (inputs : ι → HEFam H)
    (hinputsBelow :
      ∀ (j : ι) (s : ℕ), s < inputWeight → inputs j s = 0)
    (R : CHRecipe H ι)
    (hRproduct :
      ∀ q : ℕ,
        collectedHallProduct (n := n) H
            (R.eval (fun j => scaledExponentFamily (inputs j) q)) =
          collectedHallProduct (n := n) H e ^ q) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  CEData.toPolynomialData hinputWeight
    (expansion_scaled_recipes
      (Nat.zero_lt_of_lt hinputWeight) inputs hinputsBelow R hRproduct)

end TCTex
end Towers
