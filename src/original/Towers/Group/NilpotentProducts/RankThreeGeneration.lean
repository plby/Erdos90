import Towers.Group.NilpotentProducts.RankThreeBasis


/-!
# Surjectivity of the equation-(18) model map
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

/-- The ordered fourteen-factor word from Theorem 1, evaluated at any three
group elements. -/
noncomputable def rankGenerationNormal
    {G : Type*} [Group G]
    (a₁ a₂ a₃ : G) (c : RLCoordi) : G :=
  a₁ ^ c.c1 *
  a₂ ^ c.c2 *
  a₃ ^ c.c3 *
  hallCommutator a₁ a₂ ^ c.c12 *
  hallCommutator a₁ a₃ ^ c.c13 *
  hallCommutator a₂ a₃ ^ c.c23 *
  hallTripleCommutator a₁ a₂ a₁ ^ c.c121 *
  hallTripleCommutator a₁ a₃ a₁ ^ c.c131 *
  hallTripleCommutator a₂ a₃ a₂ ^ c.c232 *
  hallTripleCommutator a₁ a₂ a₂ ^ c.c122 *
  hallTripleCommutator a₁ a₃ a₃ ^ c.c133 *
  hallTripleCommutator a₂ a₃ a₃ ^ c.c233 *
  hallTripleCommutator a₁ a₂ a₃ ^ c.c123 *
  hallTripleCommutator a₂ a₃ a₁ ^ c.c231

theorem general_normal_word
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a₁ a₂ a₃ : G) (c : RLCoordi) :
    f (rankGenerationNormal a₁ a₂ a₃ c) =
      rankGenerationNormal (f a₁) (f a₂) (f a₃) c := by
  simp [rankGenerationNormal, hallCommutator, hallTripleCommutator]

/-- In the integral coordinate group, the ordered standard-commutator word
evaluates to the tuple of its exponents. -/
theorem normalWord_generators
    (c : RLCoordi) :
    rankGenerationNormal generator1 generator2
      generator3 c = c := by
  rw [rankGenerationNormal,
    hallCommutator_12, hallCommutator_13,
    hallCommutator_23,
    hallTriple_121, hallTriple_131,
    hallTriple_232, hallTriple_122,
    hallTriple_133, hallTriple_233,
    hallTriple_123, hallTriple_231,
    ← axis_generators.1,
    ← axis_generators.2.1,
    ← axis_generators.2.2]
  simp only [axis_one_zpow]
  exact axisProduct_eq c

theorem normal_residue_generators
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃)
    (c : RLCoordi) :
    rankGenerationNormal
      (generator1 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
      (generator2 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
      (generator3 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) c =
      (c : RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) := by
  let q := (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).mk'
  calc
    rankGenerationNormal
        (generator1 :
          RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
        (generator2 :
          RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
        (generator3 :
          RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) c =
      q (rankGenerationNormal generator1 generator2
        generator3 c) := by
          symm
          exact general_normal_word q _ _ _ c
    _ = q c := congrArg q (normalWord_generators c)
    _ = (c : RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) := rfl

/-- The canonical map from the cyclic free product onto the coordinate model
is surjective. -/
theorem odd_residues_surjective
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Function.Surjective
      (cyclicOddResidues
        α₁ α₂ α₃ hα₁ hα₂ hα₃) := by
  intro y
  induction y using Con.induction_on with
  | _ c =>
      let order := orders α₁ α₂ α₃
      let a₁ : CyclicFreeProduct order := cyclicGenerator order 0
      let a₂ : CyclicFreeProduct order := cyclicGenerator order 1
      let a₃ : CyclicFreeProduct order := cyclicGenerator order 2
      refine ⟨rankGenerationNormal a₁ a₂ a₃ c, ?_⟩
      calc
        (cyclicOddResidues
            α₁ α₂ α₃ hα₁ hα₂ hα₃)
            (rankGenerationNormal a₁ a₂ a₃ c) =
          rankGenerationNormal
            ((cyclicOddResidues
              α₁ α₂ α₃ hα₁ hα₂ hα₃) a₁)
            ((cyclicOddResidues
              α₁ α₂ α₃ hα₁ hα₂ hα₃) a₂)
            ((cyclicOddResidues
              α₁ α₂ α₃ hα₁ hα₂ hα₃) a₃) c :=
          general_normal_word
            (cyclicOddResidues
              α₁ α₂ α₃ hα₁ hα₂ hα₃) a₁ a₂ a₃ c
        _ = rankGenerationNormal
            (generator1 :
              RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
            (generator2 :
              RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
            (generator3 :
              RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) c := by
          congr 1
        _ = (c : RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) :=
          normal_residue_generators
            α₁ α₂ α₃ hα₁ hα₂ hα₃ c

/-- The factored map from Struik's `F/F₄` is also surjective. -/
theorem nilpotent_odd_residues
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Function.Surjective
      (nilpotentOddResidues
        α₁ α₂ α₃ hα₁ hα₂ hα₃) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    odd_residues_surjective
      α₁ α₂ α₃ hα₁ hα₂ hα₃ y
  refine ⟨QuotientGroup.mk'
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (orders α₁ α₂ α₃)) 3) x, ?_⟩
  rfl

end P1960
end Struik
