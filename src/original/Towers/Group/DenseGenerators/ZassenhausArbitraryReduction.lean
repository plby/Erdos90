import Towers.Algebra.AugmentationFiniteSupport
import Towers.Group.DimensionSubgroup
import Towers.Group.DenseGenerators.RestrictedBurnside

/-!
# Arbitrary-group reduction for Zassenhaus separation

An individual augmentation-power witness has finite support.  If an explicit positive
Zassenhaus layer is trivial, Restricted Burnside therefore reduces separation at that
layer to the finite-group case.
-/

namespace Towers

noncomputable section

universe u

/-- A finitely generated group with a trivial positive explicit Zassenhaus layer is
finite.  This packages the tuple-oriented Restricted Burnside theorem behind the
standard `Group.FG` typeclass. -/
lemma fg_restricted_burnside
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Group.FG G]
    {n : ℕ}
    (hn : 1 < n)
    (htrivial : zassenhausFiltration p G n = ⊥) :
    Finite G := by
  classical
  rcases Group.fg_iff.mp (inferInstance : Group.FG G) with ⟨S, hgen, hS⟩
  letI : Fintype S := hS.fintype
  let t : Fin (Fintype.card S) → G :=
    fun i => ((Fintype.equivFin S).symm i : S)
  have hrange : Set.range t = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin S).symm i).property
    · intro hx
      refine ⟨Fintype.equivFin S ⟨x, hx⟩, ?_⟩
      simp [t]
  have hgent : Subgroup.closure (Set.range t) = ⊤ := by
    rw [hrange]
    exact hgen
  exact
    fg_trivial_burnside
      (p := p)
      t
      hn
      hgent
      htrivial

/-- If finite groups separate the dimension subgroup at a killed explicit layer, then
all groups do.  The proof uses finite support and Restricted Burnside only; it does not
assume the desired reverse Zassenhaus inclusion. -/
lemma zmod_filtration_bot
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (hfinite :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {x : Q},
            x ∈ GroupAlgebra.dSubgro (ZMod p) Q n →
              x = 1)
    (htrivial : zassenhausFiltration p G n = ⊥)
    {g : G}
    (hg : g ∈ GroupAlgebra.dSubgro (ZMod p) G n) :
    g = 1 := by
  rw [GroupAlgebra.mem_dimensionSubgroup] at hg
  rcases
      GroupAlgebra.fg_sub_power
        (R := ZMod p)
        g
        hg with
    ⟨H, hH, gH, hgH, hgHpow⟩
  have htrivialH : zassenhausFiltration p H n = ⊥ :=
    filtration_bot_ambient
      H
      htrivial
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  letI : Finite H :=
    fg_restricted_burnside
      (p := p)
      hn
      htrivialH
  have hgHmem : gH ∈ GroupAlgebra.dSubgro (ZMod p) H n := by
    rw [GroupAlgebra.mem_dimensionSubgroup]
    exact hgHpow
  have hgHone : gH = 1 :=
    hfinite htrivialH hgHmem
  calc
    g = (gH : G) := hgH.symm
    _ = ((1 : H) : G) := congrArg Subtype.val hgHone
    _ = 1 := rfl

end

end Towers
