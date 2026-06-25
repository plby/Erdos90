import Towers.Algebra.DenseGenerators.JenningsSeparationCore
import Towers.Algebra.TruncatedJennings.CyclicFiltrationBasis
import Towers.Group.DenseGenerators.ZassenhausArbitraryReduction

open scoped commutatorElement

/-!
# Jennings reduction for explicit Zassenhaus laws

The finite cyclic-basis construction separates a killed explicit Zassenhaus layer once
the explicit filtration satisfies its weighted power and commutator laws.  Finite
support and Restricted Burnside then remove the finiteness hypothesis from the group.
-/

namespace Towers

noncomputable section

universe u

/-- The dense finite-group-algebra augmentation ideal is the ordinary augmentation
ideal. -/
lemma dense_algebra_ideal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] :
    denseGeneratorsIdeal p Q =
      GroupAlgebra.augmentationIdeal (ZMod p) Q := by
  rw [dense_generators_ker]
  rfl

/-- Ordinary dimension-subgroup membership gives the dense finite-group-algebra
congruence used by the Jennings separator. -/
lemma dense_congruence_zmod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ} {x : Q}
    (hx : x ∈ GroupAlgebra.dSubgro (ZMod p) Q n) :
    dDCongru p Q n x := by
  rw [GroupAlgebra.mem_dimensionSubgroup] at hx
  simpa [
    GroupAlgebra.augmentationPower,
    dDCongru,
    denseGeneratorsElement,
    dense_algebra_ideal,
    _root_.MonoidAlgebra.of,
  ] using hx

/-- The dense finite-group-algebra congruence is exactly mod-`p` dimension-subgroup
membership. -/
lemma dimension_zmod_congruence
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {n : ℕ} {x : Q}
    (hx : dDCongru p Q n x) :
    x ∈ GroupAlgebra.dSubgro (ZMod p) Q n := by
  rw [GroupAlgebra.mem_dimensionSubgroup]
  simpa [
    GroupAlgebra.augmentationPower,
    dDCongru,
    denseGeneratorsElement,
    dense_algebra_ideal,
    _root_.MonoidAlgebra.of,
  ] using hx

/-- The explicit filtration is contained in the ordinary mod-`p` dimension subgroup.
This is the easy inclusion, transported through the dense group-algebra model. -/
lemma filtration_dimension_zmod
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (n : ℕ) :
    zassenhausFiltration p Q n ≤
      GroupAlgebra.dSubgro (ZMod p) Q n := by
  intro x hx
  exact
    dimension_zmod_congruence
      (by
        change groupAlgebraSub p Q x ∈ augmentationIdealPower p Q n
        exact filtration_dimension_subgroup (p := p) (G := Q) n hx)

/-- Weighted power and commutator laws for finite killed layers give the corresponding
finite ordinary dimension-subgroup separator. -/
lemma zmod_bot_laws
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (hn : 1 ≤ n)
    (hpow :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r : ℕ} {x : Q},
            x ∈ zassenhausFiltration p Q r →
              x ^ p ∈ zassenhausFiltration p Q (p * r))
    (hcomm :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            x ∈ zassenhausFiltration p Q r →
            y ∈ zassenhausFiltration p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ∀ {Q : Type u} [Group Q] [Finite Q],
      zassenhausFiltration p Q n = ⊥ →
        ∀ {x : Q},
          x ∈ GroupAlgebra.dSubgro (ZMod p) Q n →
            x = 1 := by
  let H :
      TUBound.{u}
        (p := p) n :=
    trivial_separation_data
      (p := p) (n := n) fun {Q} _ _ hbot =>
        TJennin.nonempty_separation_laws
          hn
          hbot
          (hpow hbot)
          (hcomm hbot)
  intro Q _ _ hbot x hx
  exact
    H.one_trivial_zassenhaus
      hbot
      x
      (dense_congruence_zmod hx)

/-- Weighted power and commutator laws for finite killed layers separate an arbitrary
killed layer.  This is the exact interface needed after quotienting by an explicit
Zassenhaus term. -/
lemma zmod_filtration_laws
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (hpow :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r : ℕ} {x : Q},
            x ∈ zassenhausFiltration p Q r →
              x ^ p ∈ zassenhausFiltration p Q (p * r))
    (hcomm :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            x ∈ zassenhausFiltration p Q r →
            y ∈ zassenhausFiltration p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (htrivial : zassenhausFiltration p G n = ⊥)
    {g : G}
    (hg : g ∈ GroupAlgebra.dSubgro (ZMod p) G n) :
    g = 1 := by
  exact
    zmod_filtration_bot
      hn
      (zmod_bot_laws
        (p := p)
        (n := n)
        (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (lt_trans Nat.zero_lt_one hn)))
        hpow
        hcomm)
      htrivial
      hg

/-- Exact-generator successor centrality and additive exact-generator commutator bounds on
finite killed layers give the corresponding finite ordinary dimension-subgroup separator. -/
lemma
    zmod_exact_law
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (hn : 1 ≤ n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ exactGeneratorSet p Q r →
            y ∈ exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ∀ {Q : Type u} [Group Q] [Finite Q],
      zassenhausFiltration p Q n = ⊥ →
        ∀ {x : Q},
          x ∈ GroupAlgebra.dSubgro (ZMod p) Q n →
            x = 1 := by
  let H :
      TUBound.{u}
        (p := p) n :=
    trivial_separation_data
      (p := p) (n := n) fun {Q} _ _ hbot =>
        TJennin.nonempty_separation_law
          hn
          hbot
          (hsucc hbot)
          (hexact hbot)
  intro Q _ _ hbot x hx
  exact
    H.one_trivial_zassenhaus
      hbot
      x
      (dense_congruence_zmod hx)

/-- Exact-generator successor centrality and additive exact-generator commutator bounds on
finite killed layers separate an arbitrary killed layer. -/
lemma
    dimension_zmod_law
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ exactGeneratorSet p Q r →
            y ∈ exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (htrivial : zassenhausFiltration p G n = ⊥)
    {g : G}
    (hg : g ∈ GroupAlgebra.dSubgro (ZMod p) G n) :
    g = 1 := by
  exact
    zmod_filtration_bot
      hn
      (zmod_exact_law
        (p := p)
        (n := n)
        (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (lt_trans Nat.zero_lt_one hn)))
        hsucc
        hexact)
      htrivial
      hg

/-- Exact-generator successor centrality and additive exact-generator commutator bounds on
finite killed layers give the reverse dimension-subgroup inclusion for every group. -/
lemma
    zmod_filtration_law
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (hsucc :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          TJennin.WPForm.ExactSuccBound
            p Q n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ exactGeneratorSet p Q r →
            y ∈ exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    GroupAlgebra.dSubgro (ZMod p) G n ≤
      zassenhausFiltration p G n := by
  intro g hg
  let Ω : Type u := zassenhausSelfQuotient p G n
  letI : Group Ω := instSelfQuotient p G n
  let q : G →* Ω := zassenhausSelf p G n
  have hg_dense :
      dDCongru p G n g :=
    dense_congruence_zmod hg
  have hq_dense :
      dDCongru p Ω n (q g) := by
    dsimp [q, Ω]
    exact
      dDCongru.map_zass_selfquot
        (p := p) hg_dense
  have hq_mem :
      q g ∈ GroupAlgebra.dSubgro (ZMod p) Ω n :=
    dimension_zmod_congruence
      hq_dense
  have hΩ :
      zassenhausFiltration p Ω n = ⊥ := by
    dsimp [Ω]
    exact filtration_self_bot p G n
  have hq_one : q g = 1 :=
    dimension_zmod_law
      hn
      hsucc
      hexact
      hΩ
      hq_mem
  dsimp [q, Ω] at hq_one
  exact
    (zassenhaus_self_quotient p G n g).mp hq_one

/-- Exact-generator commutator laws on finite killed layers give the corresponding finite
ordinary dimension-subgroup separator.  No full explicit-filtration power law is needed. -/
lemma zmod_generator_law
    {p : ℕ} [Fact p.Prime]
    {n : ℕ}
    (hn : 1 ≤ n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ exactGeneratorSet p Q r →
            y ∈ exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    ∀ {Q : Type u} [Group Q] [Finite Q],
      zassenhausFiltration p Q n = ⊥ →
        ∀ {x : Q},
          x ∈ GroupAlgebra.dSubgro (ZMod p) Q n →
            x = 1 := by
  let H :
      TUBound.{u}
        (p := p) n :=
    trivial_separation_data
      (p := p) (n := n) fun {Q} _ _ hbot =>
        TJennin.jennings_separation_law
          hn
          hbot
          (hexact hbot)
  intro Q _ _ hbot x hx
  exact
    H.one_trivial_zassenhaus
      hbot
      x
      (dense_congruence_zmod hx)

/-- Exact-generator commutator laws on finite killed layers separate an arbitrary killed
layer. -/
lemma zmod_commutator_law
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (hexact :
      ∀ {Q : Type u} [Group Q] [Finite Q],
        zassenhausFiltration p Q n = ⊥ →
          ∀ {r s : ℕ} {x y : Q},
            r < n →
            s < n →
            x ∈ exactGeneratorSet p Q r →
            y ∈ exactGeneratorSet p Q s →
              ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (htrivial : zassenhausFiltration p G n = ⊥)
    {g : G}
    (hg : g ∈ GroupAlgebra.dSubgro (ZMod p) G n) :
    g = 1 := by
  exact
    zmod_filtration_bot
      hn
      (zmod_generator_law
        (p := p)
        (n := n)
        (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (lt_trans Nat.zero_lt_one hn)))
        hexact)
      htrivial
      hg

end

end Towers
