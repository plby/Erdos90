import Towers.ClassField.GlobalClass.FundamentalClass
import Towers.ClassField.CyclicIdeles.FiniteGalois
import Towers.ClassField.LocalBrauer.DivisionAlgebraInvariant

/-! # Chapter VIII, Section 4, Lemma 4.6 and Theorem 4.7 -/

namespace Towers.CField.GClass

open CategoryTheory groupCohomology
open IsDedekindDomain NumberField
open Towers.CField.LBrauer
open Towers.CField.CIdeles

noncomputable section
universe u

/-- **Lemma VIII.4.6.** Abstract form of the restriction formula for the
canonical absolute idèle-class invariants.  The groups stand for
`H²(Ω/K)` and `H²(Ω/L)`, while `restrict` is the actual cohomological
restriction once that infinite-tower map is constructed. -/
def AbsoluteRestrictionFormula
    {HK HL : Type*} [AddCommGroup HK] [AddCommGroup HL]
    (restrict : HK →+ HL)
    (invK : HK →+ LocalInvariant) (invL : HL →+ LocalInvariant)
    (degree : ℕ) : Prop :=
  ∀ γ : HK, invL (restrict γ) = degree • invK γ

/-- The actual relative idèle-class cohomology group `H²(L/K)`. -/
abbrev RelativeIdele2
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :=
  H2 (ideleCohomologyRepresentation K L)

/-- **Theorem VIII.4.7 (source statement).** For every finite Galois
extension, the actual group `H²(L/K)` admits the invariant isomorphism with
the cyclic group of order `[L:K]`; its invariant-one class is a generator of
that exact order. -/
def RelativeInvariantGenerator : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ∃ inv : RelativeIdele2 K L ≃+ ZMod (Module.finrank K L),
      addOrderOf (fundamentalClassInvariant inv) = Module.finrank K L ∧
      AddSubgroup.zmultiples (fundamentalClassInvariant inv) = ⊤

/-- Construction of the canonical global invariant on the actual relative
idèle-class `H²`.  This is the only unavailable cohomological input to
Theorem 4.7. -/
def InvariantBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Nonempty
      (RelativeIdele2 K L ≃+ ZMod (Module.finrank K L))

/-- Once the invariant is constructed, the order and generator assertions
of Theorem 4.7 are the algebra already proved in `FundamentalClass`. -/
theorem of_invariant
    (hInvariant : InvariantBridge.{u}) :
    RelativeInvariantGenerator.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨inv⟩ := hInvariant K L
  exact ⟨inv, add_fundamental_invariant inv,
    zmultiples_fundamental_top inv⟩

end
end Towers.CField.GClass
