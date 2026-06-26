import Towers.ClassField.LocalBrauer.LocalInvariantTorsion
import Towers.ClassField.Ideles.GlobalPlace
import Towers.ClassField.IdeleCohomology.InducedModule
import Towers.ClassField.IdeleCohomology.ShapiroHilbert90
import Towers.ClassField.IdeleCohomology.RestrictedProductAction
import Towers.ClassField.Shifting.LowTateCohomology
import Mathlib.Algebra.DirectSum.Module

/-!
# Statements for Chapter VII, Section 2

The arithmetic completion-conjugation maps and the continuous Galois action
on each product above one place are constructed in `CompletionConjugation`
and `CompletionProductAction`.  `RestrictedProductAction` constructs the
representation on a restricted product from a coordinatewise action that
preserves local units, and `IAData` states its arithmetic
instantiation against the actual number-field idele type.  The remaining gap
is to build that data by connecting the finite-prime and infinite-place
interfaces to the existing completion-conjugation maps.
-/

namespace Towers.CField.ICohomo

open CategoryTheory Representation
open Towers.CField.LBrauer
open Towers.CField.Shifting

noncomputable section

universe u v

/-- **Construction preceding Lemma VII.2.1.** A proposed action on a dependent
product of completions is Milne's action when it is a group action and its
coordinates satisfy
`(sigma * alpha)(w) = sigma (alpha (sigma⁻¹ w))`.

The maps `transport sigma w` are the extensions of `sigma` from the global
field to the two indicated completions. -/
def ProductGaloisAction
    {G W : Type u} [Group G] [MulAction G W]
    (M : W → Type v)
    (transport : ∀ (sigma : G) (w : W), M (sigma⁻¹ • w) → M w)
    (act : G → (∀ w, M w) → (∀ w, M w)) : Prop :=
  (∀ alpha, act 1 alpha = alpha) ∧
    (∀ sigma tau alpha, act (sigma * tau) alpha = act sigma (act tau alpha)) ∧
    ∀ sigma alpha w, act sigma alpha w =
      transport sigma w (alpha (sigma⁻¹ • w))

/-- The continuity clause in the construction preceding Lemma VII.2.1. -/
def ContinuousGaloisAction
    {G W : Type u} [Group G] [MulAction G W]
    (M : W → Type v) [∀ w, TopologicalSpace (M w)]
    (transport : ∀ (sigma : G) (w : W), M (sigma⁻¹ • w) → M w)
    (act : G → (∀ w, M w) → (∀ w, M w)) : Prop :=
  ProductGaloisAction M transport act ∧
    ∀ sigma, Continuous (act sigma)

/-- **The idele action following Proposition VII.2.3.** This is the same
coordinate formula on a Galois-stable restricted product. -/
def IdeleGaloisAction
    {G W I : Type u} [Group G] [MulAction G W]
    (M : W → Type v) (coordinate : ∀ w, I → M w)
    (transport : ∀ (sigma : G) (w : W), M (sigma⁻¹ • w) → M w)
    (act : G → I → I) : Prop :=
  (∀ x, act 1 x = x) ∧
    (∀ sigma tau x, act (sigma * tau) x = act sigma (act tau x)) ∧
    ∀ sigma x w, coordinate w (act sigma x) =
      transport sigma w (coordinate (sigma⁻¹ • w) x)

/-- **Proposition VII.2.2.** The product of the completions above one place,
as a `G`-representation, is the module coinduced from the decomposition group.
Milne calls this function-valued representation `Ind`. -/
def ProductsCompletionsInduced
    {k : Type u} {G : Type v} [CommRing k] [Group G] (P : Rep k G)
    (H : Subgroup G) (A : Rep k H) : Prop :=
  Nonempty (P ≅ milneInducedModule (k := k) (G := G) H A)

/-- **Proposition VII.2.3.** The local Shapiro decomposition, stated after the
arithmetic product representation has been supplied. -/
def LocalShapiroDecomposition
    {k G : Type u} [CommRing k] [Group G] (P : Rep k G)
    (H : Subgroup G) (A : Rep k H) : Prop :=
  ∀ r : ℕ, Nonempty (groupCohomology P r ≅ groupCohomology A r)

/-- The coinduced model itself satisfies the Shapiro statement. -/
theorem shapiro_decomposition_coinduced
    {k G : Type u} [CommRing k] [Group G]
    (H : Subgroup G) (A : Rep k H) :
    LocalShapiroDecomposition
      (milneInducedModule (k := k) (G := G) H A) H A := by
  intro r
  exact ⟨shapiro (k := k) (G := G) H A r⟩

/-- **Proposition VII.2.5(b), positive-degree part.** For ordinary group
cohomology the direct-sum formula starts in degree one.  Degree zero in the
book is Tate cohomology and must be stated separately. -/
def CohomologyDirectSum
    {k G ι : Type u} [CommRing k] [Group G]
    (ideleRep : Rep k G) (decompositionGroup : ι → Subgroup G)
    (localUnitsRep : ∀ v, Rep k (decompositionGroup v)) : Prop :=
  ∀ r : ℕ, Nonempty
    (groupCohomology ideleRep (r + 1) ≃+
      DirectSum ι (fun v ↦ groupCohomology (localUnitsRep v) (r + 1)))

/-- **Proposition VII.2.5(b), full `r ≥ 0` statement.** At `r = 0` this uses
Tate cohomology; positive Tate cohomology is ordinary group cohomology. -/
def IdeleCohomologyDirect
    {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (ideleRep : Rep k G) (decompositionGroup : ι → Subgroup G)
    [∀ v, Fintype (decompositionGroup v)]
    (localUnitsRep : ∀ v, Rep k (decompositionGroup v)) : Prop :=
  Nonempty (tateCohomologyZero ideleRep ≃+
      DirectSum ι (fun v ↦ tateCohomologyZero (localUnitsRep v))) ∧
    CohomologyDirectSum ideleRep decompositionGroup localUnitsRep

/-- **Corollary VII.2.6.** The first idele cohomology vanishes, and the second
is the direct sum of the local invariant groups `(1 / n_v) Z / Z`. -/
def IdeleVanishingDecomposition
    {k G ι : Type u} [CommRing k] [Group G] (ideleRep : Rep k G)
    (localDegree : ι → ℕ) : Prop :=
  (∀ x : groupCohomology ideleRep 1, x = 0) ∧
    Nonempty (groupCohomology ideleRep 2 ≃+
      DirectSum ι (fun v ↦ localInvariantTorsion (localDegree v)))

end

end Towers.CField.ICohomo
