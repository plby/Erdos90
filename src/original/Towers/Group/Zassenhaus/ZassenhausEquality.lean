import Towers.Group.Zassenhaus.RecursiveMagnus
import Towers.Algebra.Magnus.WeightedConverse


/-!
# The q-Zassenhaus product formula

This file applies Theorem 6.1 to the recursive q-Zassenhaus filtration
and proves the reverse inclusion in Theorem 8.3 for free groups.
-/

namespace EChapma

section FreeGroup

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- The q-Zassenhaus recursion, with all positive commutator pairs
presented in the format required by Theorem 6.1. -/
theorem q_recursive_univ
    (p r n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) :
    qZassenhausFiltration (FreeGroup X) p (p ^ r) hp n ≤
      subgroupPower
          (qZassenhausFiltration (FreeGroup X) p (p ^ r) hp
            (n ⌈/⌉ p))
          (p ^ r) ⊔
        ⨆ st : {st : ℕ × ℕ //
            st ∈ (Set.univ : Set (ℕ × ℕ)) ∧
              1 ≤ st.1 ∧ 1 ≤ st.2 ∧ st.1 + st.2 = n},
          ⁅qZassenhausFiltration (FreeGroup X) p (p ^ r) hp st.1.1,
            qZassenhausFiltration (FreeGroup X) p (p ^ r) hp st.1.2⁆ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [q_filtration_succ]
  apply sup_le
  · exact le_sup_left
  · apply iSup_le
    intro st
    let st' : {uv : ℕ × ℕ //
        uv ∈ (Set.univ : Set (ℕ × ℕ)) ∧
          1 ≤ uv.1 ∧ 1 ≤ uv.2 ∧ uv.1 + uv.2 = k + 2} :=
      ⟨st.1, by simpa using st.property⟩
    exact (le_iSup
      (fun uv : {uv : ℕ × ℕ //
          uv ∈ (Set.univ : Set (ℕ × ℕ)) ∧
            1 ≤ uv.1 ∧ 1 ≤ uv.2 ∧ uv.1 + uv.2 = k + 2} =>
        ⁅qZassenhausFiltration (FreeGroup X) p (p ^ r) hp uv.1.1,
          qZassenhausFiltration (FreeGroup X) p (p ^ r) hp uv.1.2⁆)
      st').trans le_sup_right

omit [Fintype X] [DecidableEq X] in
/-- The reverse inclusion in Theorem 8.3, obtained from Theorem 6.1 and
the integral equality of Theorem 4.3. -/
theorem q_logarithmic_lower
    [Finite X]
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    qZassenhausFiltration (FreeGroup X) p (p ^ r) hp n ≤
      logarithmicLowerProduct (G := FreeGroup X) p r hp n := by
  classical
  have hMagnus :
      qZassenhausFiltration (FreeGroup X) p (p ^ r) hp n ≤
        MSeries.magnusWeightedSubgroup
          (R := ℤ) (X := X)
          (MDescen.logarithmicPrimePower p r hp) n := by
    apply MSeries.recursive_sequence_magnus
      (Q := qZassenhausFiltration (FreeGroup X) p (p ^ r) hp)
      (T := Set.univ)
      (f := fun _ => p ^ r)
      (g := fun m => m ⌈/⌉ p)
      (hg := by
        intro m hm
        exact ⟨one_ceil_div p m hp (by omega),
          ceil_div_self p m hp hm⟩)
      (e := MDescen.logarithmicPrimePower p r hp)
      (n := n)
    · exact
        (MDescen.logarithmic_commutator_condition
          p r hp).on Set.univ
    · exact
        MDescen.logarithmic_prime_condition
          p r hp hr
    · simp [MSeries.magnus_weighted_top]
    · intro m hm
      exact q_recursive_univ p r m hp hm
    · exact hn
  rw [← MSeries.weighted_magnus_int
    (MDescen.logarithmicPrimePower p r hp)
    (MDescen.logarithmic_prime_binomial p r hp hr)
    hn] at hMagnus
  simpa [logarithmicLowerProduct,
    MSeries.weightedLowerProduct] using hMagnus

omit [Fintype X] [DecidableEq X] in
/-- Efrat--Chapman, Theorem 8.3 for free groups. -/
theorem q_logarithmic_product
    [Finite X]
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    qZassenhausFiltration (FreeGroup X) p (p ^ r) hp n =
      logarithmicLowerProduct (G := FreeGroup X) p r hp n :=
  le_antisymm
    (q_logarithmic_lower
      p r n hp hr hn)
    (logarithmic_q_filtration p r n hp)

end FreeGroup

end EChapma
