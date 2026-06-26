import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Class Field Theory, Chapter II, statement 1.7

Positive-degree group cohomology vanishes on injective coefficient modules.
We use Milne's concrete dimension-shifting construction: the canonical map
from a representation to the module coinduced from the trivial subgroup is a
monomorphism.  It splits when the source is injective, while Shapiro's lemma
annihilates the positive cohomology of the coinduced module.
-/

namespace Towers.CField.COps

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The canonical embedding into the module coinduced from the trivial
subgroup. -/
private noncomputable def injectiveEmbedding (I : Rep k G) :
    I ⟶ Rep.coind (⊥ : Subgroup G).subtype
      (Rep.res (⊥ : Subgroup G).subtype I) :=
  (Rep.resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app I

private instance (I : Rep k G) : Mono (injectiveEmbedding I) := by
  rw [Rep.mono_iff_injective]
  intro x y hxy
  have hvalue := congrArg
    (fun f : Representation.coindV (⊥ : Subgroup G).subtype
      (I.ρ.comp (⊥ : Subgroup G).subtype) => f.1 1) hxy
  change I.ρ 1 x = I.ρ 1 y at hvalue
  simpa using hvalue

/-- An injective representation is a retract of its canonical coinduced
module. -/
private noncomputable def injectiveRetractCoinduced
    (I : Rep k G) [Injective I] :
    Retract I (Rep.coind (⊥ : Subgroup G).subtype
      (Rep.res (⊥ : Subgroup G).subtype I)) where
  i := injectiveEmbedding I
  r := Injective.factorThru (𝟙 I) (injectiveEmbedding I)
  retract := Injective.comp_factorThru (𝟙 I) (injectiveEmbedding I)

/-- A retract of a zero object is zero. -/
private theorem zero_retract {C : Type u} [Category C]
    {X Y : C} (h : Retract X Y) (hY : Limits.IsZero Y) :
    Limits.IsZero X := by
  refine ⟨fun Z ↦ ⟨⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩⟩,
    fun Z ↦ ⟨⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩⟩⟩
  · intro f
    calc
      f = 𝟙 X ≫ f := by simp
      _ = (h.i ≫ h.r) ≫ f := by rw [h.retract]
      _ = h.i ≫ (h.r ≫ f) := Category.assoc _ _ _
      _ = h.i ≫ hY.to_ Z := by rw [hY.eq_of_src (h.r ≫ f) (hY.to_ Z)]
  · intro f
    calc
      f = f ≫ 𝟙 X := by simp
      _ = f ≫ (h.i ≫ h.r) := by rw [h.retract]
      _ = (f ≫ h.i) ≫ h.r := (Category.assoc _ _ _).symm
      _ = hY.from_ Z ≫ h.r := by rw [hY.eq_of_tgt (f ≫ h.i) (hY.from_ Z)]

/-- **Statement II.1.7.** If `I` is an injective `G`-module, then
`H^{n+1}(G, I) = 0`. -/
theorem cohomology_succ_injective
    (I : Rep k G) [Injective I] (n : ℕ) :
    Limits.IsZero (groupCohomology I (n + 1)) := by
  let A := Rep.res (⊥ : Subgroup G).subtype I
  have hA : Limits.IsZero (groupCohomology A (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton A n
  have hcoind : Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) :=
    Limits.IsZero.of_iso hA (groupCohomology.coindIso A (n + 1))
  let h := (injectiveRetractCoinduced I).map
    (groupCohomology.functor k G (n + 1))
  exact zero_retract h hcoind

/-- Positive-degree formulation of statement II.1.7. -/
theorem zero_cohomology_injective
    (I : Rep k G) [Injective I] (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupCohomology I n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact cohomology_succ_injective I m

end Towers.CField.COps
