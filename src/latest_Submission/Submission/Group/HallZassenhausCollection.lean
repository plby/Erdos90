import Submission.Group.Edmonton.HallEmbeddings

/-!
# Hall--Zassenhaus coordinate collection

This file isolates the final finite induction in the Hall--Zassenhaus
collection argument.  Once the Zassenhaus condition gives coordinate
divisibility and the normalized Hall word for the current coordinate has the
expected leading coordinate, one word-value kills that coordinate without
disturbing the earlier ones.  Repeating through the finite Hall basis gives a
uniform product bound.
-/

namespace Submission
namespace Edmonton

universe u

variable {G : Type u} [Group G] {M : ℕ}

namespace HCBasis

/-- The predicate that the first `k` Hall coordinates of `g` vanish. -/
def PrefixZero (b : HCBasis G M) (k : ℕ) (g : G) : Prop :=
  ∀ i : Fin M, (i : ℕ) < k → b.coord g i = 0

lemma prefix_zero_tail (b : HCBasis G M) {k : ℕ}
    (hk : k ≤ M) {g : G} :
    PrefixZero b k g ↔ g ∈ b.tail k := by
  rw [b.mem_tail_iff hk]
  rfl

lemma prefix_zero_length (b : HCBasis G M) {g : G}
    (hg : PrefixZero b M g) : g = 1 := by
  have htail : g ∈ b.tail M := (prefix_zero_tail b le_rfl).mp hg
  have hbot : g ∈ (⊥ : Subgroup G) := by
    simpa [b.tail_length] using htail
  exact Subgroup.mem_bot.mp hbot

/--
Data needed for the coordinate-killing part of the Hall--Zassenhaus
collection proof.

Here `D` is the target Zassenhaus/dimension subgroup, `alpha i` is the
integer divisor forced on the `i`-th Hall coordinate, and
`normalizedWord i m` is the normalized Hall word-value whose leading
coordinate is `(alpha i) * m`.  The field `step` packages the triangular
normal-form calculation: after removing this word-value, the residual is still
in `D` and has one more initial zero coordinate.
-/
structure NCData
    (b : HCBasis G M) (D : Subgroup G) where
  alpha : Fin M → ℕ
  coord_divisible :
    ∀ {y : G}, y ∈ D → ∀ i : Fin M, ((alpha i : ℤ) ∣ b.coord y i)
  normalizedWord : Fin M → ℤ → G
  normalizedWord_mem : ∀ i m, normalizedWord i m ∈ D
  step :
    ∀ {y : G}, y ∈ D →
      ∀ {k : ℕ} (hk : k < M),
        PrefixZero b k y →
          ∀ m : ℤ,
            b.coord y ⟨k, hk⟩ = (alpha ⟨k, hk⟩ : ℤ) * m →
              let z := normalizedWord ⟨k, hk⟩ m
              z⁻¹ * y ∈ D ∧ PrefixZero b (k + 1) (z⁻¹ * y)

/--
The same input in the more geometric form used in the Hall--Zassenhaus
argument: the normalized word has prescribed leading coordinates, and the
Hall normal form is triangular enough that two elements with the same first
`k` coordinates have quotient in the `k`-th tail.
-/
structure NCDataa
    (b : HCBasis G M) (D : Subgroup G) where
  alpha : Fin M → ℕ
  coord_divisible :
    ∀ {y : G}, y ∈ D → ∀ i : Fin M, ((alpha i : ℤ) ∣ b.coord y i)
  normalizedWord : Fin M → ℤ → G
  normalizedWord_mem : ∀ i m, normalizedWord i m ∈ D
  normalized_coord_before :
    ∀ (i : Fin M) (m : ℤ) (j : Fin M),
      (j : ℕ) < (i : ℕ) → b.coord (normalizedWord i m) j = 0
  normalized_coord_self :
    ∀ (i : Fin M) (m : ℤ),
      b.coord (normalizedWord i m) i = (alpha i : ℤ) * m
  prefix_zero_same :
    ∀ {k : ℕ}, k ≤ M →
      ∀ {x y : G},
        (∀ i : Fin M, (i : ℕ) < k → b.coord x i = b.coord y i) →
          PrefixZero b k (x⁻¹ * y)

namespace NCDataa

variable {b : HCBasis G M} {D : Subgroup G}
variable (K : NCDataa b D)

/-- A factor is one of the normalized word-values supplied by the coordinate data. -/
def IsNormalizedFactor (g : G) : Prop :=
  ∃ i : Fin M, ∃ m : ℤ, K.normalizedWord i m = g

/-- Coordinate-level Hall--Zassenhaus data supplies the residual-killing step. -/
def toCollectionData : NCData b D where
  alpha := K.alpha
  coord_divisible := K.coord_divisible
  normalizedWord := K.normalizedWord
  normalizedWord_mem := K.normalizedWord_mem
  step := by
    intro y hy k hk hprefix m hm
    let i : Fin M := ⟨k, hk⟩
    let z : G := K.normalizedWord i m
    have hzD : z ∈ D := K.normalizedWord_mem i m
    constructor
    · exact D.mul_mem (D.inv_mem hzD) hy
    · apply K.prefix_zero_same (Nat.succ_le_of_lt hk)
      intro j hj
      by_cases hjk : (j : ℕ) < k
      · rw [K.normalized_coord_before i m j (by simpa [i] using hjk),
          hprefix j hjk]
      · have hji : j = i := by
          apply Fin.ext
          change (j : ℕ) = k
          omega
        subst j
        rw [K.normalized_coord_self i m, hm]

end NCDataa

namespace NCData

variable {b : HCBasis G M} {D : Subgroup G}
variable (K : NCData b D)

/-- A factor is one of the normalized word-values supplied by the data. -/
def IsNormalizedFactor (g : G) : Prop :=
  ∃ i : Fin M, ∃ m : ℤ, K.normalizedWord i m = g

/--
The formal coordinate-killing induction: every element of `D` is a product of
at most `M` normalized word-values.
-/
theorem normalized_word_prod {y : G} (hy : y ∈ D) :
    ∃ factors : List G,
      factors.length ≤ M ∧
        (∀ g ∈ factors, K.IsNormalizedFactor g) ∧
          factors.prod = y := by
  classical
  have hmain :
      ∀ r k : ℕ, k + r = M →
        ∀ y : G, y ∈ D → PrefixZero b k y →
          ∃ factors : List G,
            factors.length ≤ r ∧
              (∀ g ∈ factors, K.IsNormalizedFactor g) ∧
                factors.prod = y := by
    intro r
    induction r with
    | zero =>
        intro k hk y hy hprefix
        have hkM : k = M := by omega
        subst k
        refine ⟨[], by simp, by simp, ?_⟩
        exact (prefix_zero_length b hprefix).symm
    | succ r ih =>
        intro k hk y hy hprefix
        have hklt : k < M := by omega
        let i : Fin M := ⟨k, hklt⟩
        obtain ⟨m, hm⟩ := K.coord_divisible hy i
        have hstep :=
          K.step hy hklt hprefix m (by
            simpa [i, mul_comm] using hm)
        let z : G := K.normalizedWord i m
        have hstep' : z⁻¹ * y ∈ D ∧ PrefixZero b (k + 1) (z⁻¹ * y) := by
          simpa [z, i] using hstep
        obtain ⟨hy', hprefix'⟩ := hstep'
        obtain ⟨factors, hlen, hnorm, hprod⟩ :=
          ih (k + 1) (by omega) (z⁻¹ * y) hy' hprefix'
        refine ⟨z :: factors, by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
        · intro g hg
          simp only [List.mem_cons] at hg
          rcases hg with hgz | hg
          · subst g
            exact ⟨i, m, rfl⟩
          · exact hnorm g hg
        · simp [z, hprod]
  have hprefix0 : PrefixZero b 0 y := by
    intro i hi
    omega
  obtain ⟨factors, hlen, hnorm, hprod⟩ := hmain M 0 (by simp) y hy hprefix0
  exact ⟨factors, hlen, hnorm, hprod⟩

end NCData

namespace NCDataa

variable {b : HCBasis G M} {D : Subgroup G}
variable (K : NCDataa b D)

/--
The bounded collection theorem in terms of the coordinate-level hypotheses:
every element of `D` is a product of at most `M` normalized word-values.
-/
theorem normalized_word_prod {y : G} (hy : y ∈ D) :
    ∃ factors : List G,
      factors.length ≤ M ∧
        (∀ g ∈ factors, K.IsNormalizedFactor g) ∧
          factors.prod = y := by
  obtain ⟨factors, hlen, hnorm, hprod⟩ :=
    (K.toCollectionData).normalized_word_prod hy
  refine ⟨factors, hlen, ?_, hprod⟩
  intro g hg
  rcases hnorm g hg with ⟨i, m, hgm⟩
  exact ⟨i, m, hgm⟩

end NCDataa

end HCBasis
end Edmonton
end Submission
