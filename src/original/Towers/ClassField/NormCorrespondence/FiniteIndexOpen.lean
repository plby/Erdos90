import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Class Field Theory, Chapter I, paragraph 1.7

Milne proves that a finite-index subgroup of the multiplicative group of a
characteristic-zero local field is open.  The group-theoretic and topological
part of the proof says that a finite-index subgroup contains all powers whose
exponent is its index, so it is open as soon as such powers contain a
neighborhood of one.
-/

namespace Towers.CField.LFTheory

open Filter Set
open scoped Topology

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- A finite-index subgroup of a commutative topological group is open if,
eventually near one, every element is an `index`-th power. -/
theorem open_eventually_pow
    (H : Subgroup G) [H.FiniteIndex]
    (hpow : ∀ᶠ x in nhds (1 : G), ∃ y : G, y ^ H.index = x) :
    IsOpen (H : Set G) := by
  apply H.isOpen_of_mem_nhds
  filter_upwards [hpow] with x hx
  obtain ⟨y, rfl⟩ := hx
  exact H.pow_index_mem y

/-- Neighborhood form of the argument in paragraph 1.7. -/
theorem index_open_nhds
    (H : Subgroup G) [H.FiniteIndex] (V : Set G)
    (hVopen : IsOpen V) (hone : (1 : G) ∈ V)
    (hpow : ∀ x ∈ V, ∃ y : G, y ^ H.index = x) :
    IsOpen (H : Set G) := by
  apply open_eventually_pow H
  filter_upwards [hVopen.mem_nhds hone] with x hx
  exact hpow x hx

section CharacteristicZero

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K]

/-- In a complete characteristic-zero normed field, the `n`th-power map is
locally surjective at `1` for every nonzero `n`.

This is the inverse-function-theorem form of the Newton lemma used in
paragraph 1.7. -/
theorem eventually_char_zero
    (n : ℕ) (hn : n ≠ 0) :
    ∀ᶠ x in 𝓝 (1 : K), ∃ y : K, y ^ n = x := by
  let f : K → K := fun y => y ^ n
  have hf : HasStrictDerivAt f (n : K) 1 := by
    simpa only [f, Nat.cast_ofNat, one_pow, mul_one] using
      hasStrictDerivAt_pow n (1 : K)
  have hmap : Filter.map f (𝓝 (1 : K)) = 𝓝 (1 : K) := by
    simpa only [f, one_pow] using
      hf.map_nhds_eq (Nat.cast_ne_zero.mpr hn)
  rw [← hmap]
  change ∀ᶠ y in 𝓝 (1 : K), ∃ z : K, z ^ n = f y
  filter_upwards [] with y
  exact ⟨y, rfl⟩

/-- The same local power-surjectivity statement on the multiplicative group
of the field. -/
theorem eventually_units_char
    (n : ℕ) (hn : n ≠ 0) :
    ∀ᶠ x in 𝓝 (1 : Kˣ), ∃ y : Kˣ, y ^ n = x := by
  have hroots := eventually_char_zero (K := K) n hn
  have hval : Tendsto (fun x : Kˣ => (x : K)) (𝓝 1) (𝓝 1) := by
    simpa using Units.continuous_val.continuousAt
  filter_upwards [hval.eventually hroots] with x hx
  obtain ⟨y, hy⟩ := hx
  have hy0 : y ≠ 0 := by
    intro hyzero
    subst y
    simp only [zero_pow hn] at hy
    exact x.ne_zero hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

/-- Milne, paragraph 1.7: every finite-index subgroup of the multiplicative
group of a complete characteristic-zero normed field is open. -/
theorem open_char_zero
    (H : Subgroup Kˣ) (hH : H.FiniteIndex) :
    IsOpen (H : Set Kˣ) := by
  letI : H.FiniteIndex := hH
  apply open_eventually_pow H
  exact eventually_units_char
    (K := K) H.index Subgroup.FiniteIndex.index_ne_zero

end CharacteristicZero

end Towers.CField.LFTheory
