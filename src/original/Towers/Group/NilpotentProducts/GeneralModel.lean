import Towers.Group.NilpotentProducts.CyclicProducts
import Towers.Group.NilpotentProducts.GeneralNilpotency


/-!
# The equation-(18) model of Struik's Theorem 2
-/

namespace Struik
namespace P1960

open Towers

/-- The integral coordinate generator in position `i`. -/
def generalGenerator {t : ℕ} (i : Fin t) :
    GCoordi t where
  single j := if j = i then 1 else 0
  pair _ := 0
  pairLeft _ := 0
  pairRight _ := 0
  tripleFirst _ := 0
  tripleSecond _ := 0

/-- An arbitrary integral multiple of one generator coordinate. -/
def generalGeneratorMultiple {t : ℕ}
    (i : Fin t) (n : ℤ) : GCoordi t where
  single j := if j = i then n else 0
  pair _ := 0
  pairLeft _ := 0
  pairRight _ := 0
  tripleFirst _ := 0
  tripleSecond _ := 0

/-- Powers of a coordinate generator only change its single coordinate. -/
theorem generalGenerator_pow {t : ℕ}
    (i : Fin t) (n : ℕ) :
    generalGenerator i ^ n =
      generalGeneratorMultiple i n := by
  induction n with
  | zero =>
      change GCoordi.zero t =
        generalGeneratorMultiple i 0
      ext <;> simp [GCoordi.zero,
        generalGeneratorMultiple]
  | succ n ih =>
      rw [pow_succ, ih]
      change
        GCoordi.mul
          (generalGeneratorMultiple i n)
          (generalGenerator i) =
        generalGeneratorMultiple i (n + 1)
      ext j
      · by_cases hji : j = i <;>
          simp [GCoordi.mul,
            generalGeneratorMultiple, generalGenerator,
            hji]
      · have hjlt := j.lt
        by_cases hji : j.i = i <;> by_cases hjj : j.j = i
        <;> simp [GCoordi.mul,
          generalGeneratorMultiple, generalGenerator,
          hji, hjj] at *
      · have hjlt := j.lt
        by_cases hji : j.i = i <;> by_cases hjj : j.j = i
        <;> simp [GCoordi.mul,
          generalGeneratorMultiple, generalGenerator,
          hji, hjj] at *
      · have hjlt := j.lt
        by_cases hji : j.i = i <;> by_cases hjj : j.j = i
        <;> simp [GCoordi.mul,
          generalGeneratorMultiple, generalGenerator,
          hji, hjj] at *
      · have hij := j.lt_ij
        have hjklt := j.lt_jk
        by_cases hji : j.i = i <;> by_cases hjj : j.j = i
        <;> by_cases hjk : j.k = i
        <;> simp [GCoordi.mul,
          generalGeneratorMultiple, generalGenerator,
          hji, hjj, hjk, Triple.ij, Triple.ik,
          Triple.jk] at *
      · have hij := j.lt_ij
        have hjklt := j.lt_jk
        by_cases hji : j.i = i <;> by_cases hjj : j.j = i
        <;> by_cases hjk : j.k = i
        <;> simp [GCoordi.mul,
          generalGeneratorMultiple, generalGenerator,
          hji, hjj, hjk, Triple.ij, Triple.ik,
          Triple.jk] at *

/-- The canonical generators of the arbitrary-rank residue coordinate
group. -/
noncomputable def generalResidueGenerator
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : Fin t) :
    GeneralResidueGroup order horder :=
  (generalGenerator i :
    GeneralResidueGroup order horder)

private theorem general_generator_rel
    {t : ℕ} (order : Fin t → ℕ) (i : Fin t) :
    GMEq order
      (generalGenerator i ^ order i)
      (GCoordi.zero t) := by
  rw [generalGenerator_pow]
  refine ⟨?_, fun _ => .refl _, fun _ => .refl _, fun _ => .refl _,
    fun _ => .refl _, fun _ => .refl _⟩
  intro j
  by_cases hji : j = i
  · subst j
    simp [generalGeneratorMultiple,
      GCoordi.zero, Int.ModEq]
  · simp [generalGeneratorMultiple,
      GCoordi.zero, hji]

theorem general_residue_generator
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : Fin t) :
    generalResidueGenerator order horder i ^ order i = 1 := by
  apply (generalCon order horder).eq.mpr
  exact general_generator_rel order i

/-- The free product of all cyclic factors maps canonically to the
arbitrary-rank equation-(18) residue group. -/
noncomputable def cyclicGeneralResidues
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    CyclicFreeProduct order →*
      GeneralResidueGroup order horder := by
  apply PresentedGroup.toGroup
  · intro r hr
    obtain ⟨i, rfl⟩ := hr
    simpa using
      general_residue_generator order horder i

/-- The canonical map factors through the nilpotent product `F/F₄`. -/
noncomputable def nilpotentGeneralResidues
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    NilpotentCyclicProduct order 4 →*
      GeneralResidueGroup order horder := by
  let f := cyclicGeneralResidues order horder
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries (CyclicFreeProduct order) 3) f
  intro x hx
  apply MonoidHom.mem_ker.mp
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (GeneralResidueGroup order horder) 3 :=
    Subgroup.lowerCentralSeries.map f 3 (Subgroup.mem_map_of_mem f hx)
  simpa [lower_general_bot
    order horder] using hxmap

end P1960
end Struik
