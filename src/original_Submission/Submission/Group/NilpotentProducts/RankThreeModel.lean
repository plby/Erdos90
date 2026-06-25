import Submission.Group.NilpotentProducts.CyclicProducts
import Submission.Group.NilpotentProducts.RankThreeNilpotency


/-!
# The equation-(18) model of Struik's Theorem 1

For three odd-or-zero cyclic orders, the coordinate residue group receives
the canonical homomorphism from the corresponding nilpotent cyclic product
`F/F₄`.
-/

namespace Struik
namespace P1960

open Submission

/-- The three cyclic orders used in Theorem 1, indexed by `Fin 3`. -/
def orders (α₁ α₂ α₃ : ℕ) : Fin 3 → ℕ :=
  Fin.cases α₁ (Fin.cases α₂ fun _ => α₃)

@[simp] theorem general_residue_orders (α₁ α₂ α₃ : ℕ) :
    orders α₁ α₂ α₃ 0 = α₁ :=
  rfl

@[simp] theorem general_orders_one (α₁ α₂ α₃ : ℕ) :
    orders α₁ α₂ α₃ 1 = α₂ :=
  rfl

@[simp] theorem general_orders_two (α₁ α₂ α₃ : ℕ) :
    orders α₁ α₂ α₃ 2 = α₃ :=
  rfl

/-- The first integral coordinate generator. -/
def generator1 : RLCoordi :=
  { RLCoordi.zero with c1 := 1 }

/-- The second integral coordinate generator. -/
def generator2 : RLCoordi :=
  { RLCoordi.zero with c2 := 1 }

/-- The third integral coordinate generator. -/
def generator3 : RLCoordi :=
  { RLCoordi.zero with c3 := 1 }

private def c1Multiple (n : ℤ) : RLCoordi :=
  { RLCoordi.zero with c1 := n }

private def c2Multiple (n : ℤ) : RLCoordi :=
  { RLCoordi.zero with c2 := n }

private def c3Multiple (n : ℤ) : RLCoordi :=
  { RLCoordi.zero with c3 := n }

private theorem generator1_pow (n : ℕ) :
    generator1 ^ n = c1Multiple n := by
  induction n with
  | zero =>
      change RLCoordi.zero = c1Multiple 0
      rfl
  | succ n ih =>
      rw [pow_succ, ih]
      change
        RLCoordi.mul (c1Multiple n)
          generator1 =
          c1Multiple (n + 1)
      ext <;>
        simp [RLCoordi.mul, c1Multiple,
          generator1, RLCoordi.zero]

private theorem generator2_pow (n : ℕ) :
    generator2 ^ n = c2Multiple n := by
  induction n with
  | zero =>
      change RLCoordi.zero = c2Multiple 0
      rfl
  | succ n ih =>
      rw [pow_succ, ih]
      change
        RLCoordi.mul (c2Multiple n)
          generator2 =
          c2Multiple (n + 1)
      ext <;>
        simp [RLCoordi.mul, c2Multiple,
          generator2, RLCoordi.zero]

private theorem generator3_pow (n : ℕ) :
    generator3 ^ n = c3Multiple n := by
  induction n with
  | zero =>
      change RLCoordi.zero = c3Multiple 0
      rfl
  | succ n ih =>
      rw [pow_succ, ih]
      change
        RLCoordi.mul (c3Multiple n)
          generator3 =
          c3Multiple (n + 1)
      ext <;>
        simp [RLCoordi.mul, c3Multiple,
          generator3, RLCoordi.zero]

/-- The three canonical generators in the equation-(18) residue group. -/
noncomputable def rankModelGenerator
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Fin 3 → RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃ :=
  Fin.cases
    (generator1 :
      RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
    (Fin.cases
      (generator2 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)
      (fun _ =>
        (generator3 :
          RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃)))

private theorem generator_1_rel
    (α₁ α₂ α₃ : ℕ) :
    RRMod α₁ α₂ α₃
      (generator1 ^ α₁) RLCoordi.zero := by
  rw [generator1_pow]
  refine ⟨?_, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _,
    .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩
  simp [c1Multiple, RLCoordi.zero, Int.ModEq]

private theorem generator_2_rel
    (α₁ α₂ α₃ : ℕ) :
    RRMod α₁ α₂ α₃
      (generator2 ^ α₂) RLCoordi.zero := by
  rw [generator2_pow]
  refine ⟨.refl _, ?_, .refl _, .refl _, .refl _, .refl _, .refl _,
    .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩
  simp [c2Multiple, RLCoordi.zero, Int.ModEq]

private theorem generator_3_rel
    (α₁ α₂ α₃ : ℕ) :
    RRMod α₁ α₂ α₃
      (generator3 ^ α₃) RLCoordi.zero := by
  rw [generator3_pow]
  refine ⟨.refl _, .refl _, ?_, .refl _, .refl _, .refl _, .refl _,
    .refl _, .refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩
  simp [c3Multiple, RLCoordi.zero, Int.ModEq]

/-- Each coordinate generator satisfies the defining order relation of its
cyclic factor. -/
theorem rank_model_residue
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃)
    (i : Fin 3) :
    rankModelGenerator α₁ α₂ α₃ hα₁ hα₂ hα₃ i ^
        orders α₁ α₂ α₃ i =
      1 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i
  · change
      (generator1 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) ^ α₁ =
        1
    apply (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).eq.mpr
    exact generator_1_rel α₁ α₂ α₃
  · change
      (generator2 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) ^ α₂ =
        1
    apply (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).eq.mpr
    exact generator_2_rel α₁ α₂ α₃
  · change
      (generator3 :
        RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) ^ α₃ =
        1
    apply (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).eq.mpr
    exact generator_3_rel α₁ α₂ α₃

/-- The free product of the three cyclic factors maps canonically to the
equation-(18) residue group. -/
noncomputable def cyclicOddResidues
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    CyclicFreeProduct (orders α₁ α₂ α₃) →*
      RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃ := by
  refine PresentedGroup.toGroup
    (f := rankModelGenerator α₁ α₂ α₃ hα₁ hα₂ hα₃) ?_
  intro r hr
  obtain ⟨i, rfl⟩ := hr
  simpa using
    rank_model_residue
      α₁ α₂ α₃ hα₁ hα₂ hα₃ i

/-- The canonical map factors through `F/F₄`, since the coordinate model has
trivial fourth lower-central term. -/
noncomputable def nilpotentOddResidues
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    NilpotentCyclicProduct (orders α₁ α₂ α₃) 4 →*
      RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃ := by
  let f :=
    cyclicOddResidues
      α₁ α₂ α₃ hα₁ hα₂ hα₃
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (orders α₁ α₂ α₃)) 3) f
  intro x hx
  apply MonoidHom.mem_ker.mp
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) 3 :=
    Subgroup.lowerCentralSeries.map f 3 (Subgroup.mem_map_of_mem f hx)
  simpa [lower_residue_bot
    α₁ α₂ α₃ hα₁ hα₂ hα₃] using hxmap

end P1960
end Struik
