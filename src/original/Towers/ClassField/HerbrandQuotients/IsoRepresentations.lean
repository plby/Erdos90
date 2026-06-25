import Towers.ClassField.Shifting.KernelImageComplex
import Towers.ClassField.IdeleCohomology.NormInvariants
import Towers.ClassField.HerbrandQuotients.Representation

/-!
# Chapter VII, Section 3, Lemma 3.4

Finite-generation over `ℤ` and rational isomorphism of two modules for a
finite cyclic group imply equality of their Herbrand quotients whenever one
of the two quotients is defined.

The source proof clears denominators in a rational equivariant isomorphism,
producing an integral equivariant map with finite kernel and cokernel, and
then applies Corollary II.3.9.  Both steps are recorded below as exact,
non-circular interfaces.  Corollary II.3.9 is already proved in the project,
but its ordinary-group-cohomology formulation places the coefficient ring
and the group in one universe.  Chapter VII uses the universe-polymorphic
low-Tate formulation `HerbrandQuotientValue`, hence the small transport
interface below.
-/

namespace Towers.CField.HQuotie

open CategoryTheory CategoryTheory.Limits Representation
open Towers.CField.ICohomo

noncomputable section

universe u v

/-- The literal hypothesis that the rational scalar extensions of two
integral `G`-modules are isomorphic as `ℚ[G]`-modules. -/
def RationallyIsomorphicRepresentations
    {G : Type u} [Group G] [Finite G]
    (M N : Rep.{v, 0, u} ℤ G) : Prop :=
  let _ : Module ℤ M := M.hV2
  let _ : Module ℤ N := N.hV2
  Nonempty
    ((Representation.baseChange ℤ ℚ G M M.ρ).Equiv
      (Representation.baseChange ℤ ℚ G N N.ρ))

/-- Having a defined Herbrand quotient, expressed using the exact
universe-polymorphic low-Tate cardinal ratio used throughout Chapter VII. -/
def DefinedHerbrandQuotient
    {G : Type u} [CommGroup G] [Fintype G]
    (M : Rep.{v, 0, u} ℤ G) : Prop :=
  ∃ q : ℚ, HerbrandQuotientValue M q

/-- The clearing-denominators step of Milne's proof.  For finitely generated
integral representations, an isomorphism after tensoring with `ℚ` produces
an equivariant integral map with finite kernel and cokernel.

This includes the harmless preliminary removal of torsion via Corollary
II.3.9, exactly as in the source. -/
def IntegralIsogenyBridge : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
    letI : Fintype G := Fintype.ofFinite G
    letI : CommGroup G := IsCyclic.commGroup
    ∀ (M N : Rep.{v, 0, u} ℤ G) [Module.Finite ℤ M] [Module.Finite ℤ N],
      RationallyIsomorphicRepresentations M N →
      ∃ f : M ⟶ N,
        Finite ↑(kernel f : Rep.{v, 0, u} ℤ G) ∧
          Finite ↑(cokernel f : Rep.{v, 0, u} ℤ G)

/-- Universe-polymorphic low-Tate form of Corollary II.3.9: an equivariant
map with finite kernel and cokernel preserves existence and the value of the
Herbrand quotient.

The older same-universe version is
`Shifting.herbrand_quotient_cokernel`; this is
the exact comparison needed for Chapter VII's `HerbrandQuotientValue`. -/
def HerbrandIsogenyBridge : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
    letI : Fintype G := Fintype.ofFinite G
    letI : CommGroup G := IsCyclic.commGroup
    ∀ (M N : Rep.{v, 0, u} ℤ G) (f : M ⟶ N),
      Finite ↑(kernel f : Rep.{v, 0, u} ℤ G) →
      Finite ↑(cokernel f : Rep.{v, 0, u} ℤ G) →
      ∀ q : ℚ,
        HerbrandQuotientValue M q ↔
          HerbrandQuotientValue N q

/-- Lemma 3.4 follows from its literal clearing-denominators construction
and the already-established finite-kernel/cokernel invariance of Herbrand
quotients. -/
theorem rationally_representations_isogeny
    (hintegral : IntegralIsogenyBridge.{u, v})
    (hherbrand : HerbrandIsogenyBridge.{u, v}) :
    (∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
          letI : Fintype G := Fintype.ofFinite G
          letI : CommGroup G := IsCyclic.commGroup
          ∀ (M N : Rep.{v, 0, u} ℤ G) [Module.Finite ℤ M] [Module.Finite ℤ N],
            RationallyIsomorphicRepresentations M N →
            ((DefinedHerbrandQuotient M →
                ∃ q : ℚ,
                  HerbrandQuotientValue M q ∧
                    HerbrandQuotientValue N q) ∧
              (DefinedHerbrandQuotient N →
                ∃ q : ℚ,
                  HerbrandQuotientValue M q ∧
                    HerbrandQuotientValue N q))) := by
  intro G _ _ _ M N _ _ hMN
  obtain ⟨f, hker, hcoker⟩ := hintegral G M N hMN
  constructor
  · rintro ⟨q, hMq⟩
    exact ⟨q, hMq, (hherbrand G M N f hker hcoker q).mp hMq⟩
  · rintro ⟨q, hNq⟩
    exact ⟨q, (hherbrand G M N f hker hcoker q).mpr hNq, hNq⟩

end

end Towers.CField.HQuotie
