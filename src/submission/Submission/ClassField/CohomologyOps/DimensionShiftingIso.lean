import Submission.ClassField.CohomologyOps.ZeroCoinducedSucc
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Class Field Theory, Chapter II, Remark 1.13

An exact sequence `0 -> M -> J -> N -> 0` with acyclic middle term gives the
dimension-shifting isomorphisms

`H^r(G, N) ≃ H^(r+1)(G, M)` for `r > 0`.

We also construct Milne's canonical sequence by embedding a representation
in the module coinduced from the trivial subgroup and taking its cokernel.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits

universe u

variable {k G : Type u} [CommRing k] [Group G]

noncomputable section

/-- **Remark II.1.13.** The connecting map is an isomorphism in positive
degrees when the middle term of a short exact sequence is cohomologically
acyclic in positive degrees. -/
noncomputable def dimensionShiftingIso
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hacyclic : ∀ n : ℕ, 0 < n → IsZero (groupCohomology X.X₂ n))
    (n : ℕ) (hn : 0 < n) :
    groupCohomology X.X₃ n ≅ groupCohomology X.X₁ (n + 1) := by
  letI : IsIso (groupCohomology.δ hX n (n + 1) rfl) :=
    groupCohomology.isIso_δ_of_isZero hX n
      (hacyclic n hn) (hacyclic (n + 1) (Nat.succ_pos n))
  exact asIso (groupCohomology.δ hX n (n + 1) rfl)

/-- In degree zero the connecting map is surjective when `H^1(G,J)=0`,
which is the terminal zero in Milne's displayed five-term sequence. -/
theorem shifting_delta_epi
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₂ 1)) :
    Epi (groupCohomology.δ hX 0 1 rfl) :=
  groupCohomology.epi_δ_of_isZero hX 0 h1

/-- Exactness at `H^0(G,N)` in the low-degree part of Remark II.1.13. -/
theorem shifting_low_exact
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    (groupCohomology.mapShortComplex₃ (i := 0) (j := 1) hX rfl).Exact :=
  groupCohomology.mapShortComplex₃_exact hX rfl

/-- Milne's canonical equivariant embedding `M -> M_*`, where `M_*` is
coinduced from the underlying module over the trivial subgroup. -/
noncomputable def canonicalShiftEmbedding (A : Rep k G) :
    A ⟶ Rep.coind (⊥ : Subgroup G).subtype
      (Rep.res (⊥ : Subgroup G).subtype A) :=
  (Rep.resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A

@[simp]
theorem dimension_shift_embedding
    (A : Rep k G) (a : A) (g : G) :
    ((canonicalShiftEmbedding A).hom a :
      Representation.coindV (⊥ : Subgroup G).subtype
        (A.ρ.comp (⊥ : Subgroup G).subtype)).1 g = A.ρ g a :=
  rfl

instance shift_embedding_mono (A : Rep k G) :
    Mono (canonicalShiftEmbedding A) := by
  rw [Rep.mono_iff_injective]
  intro x y hxy
  have hvalue := congrArg
    (fun f : Representation.coindV (⊥ : Subgroup G).subtype
      (A.ρ.comp (⊥ : Subgroup G).subtype) => f.1 1) hxy
  change A.ρ 1 x = A.ρ 1 y at hvalue
  simpa using hvalue

/-- The canonical short complex `M -> M_* -> M_dagger`, with
`M_dagger = M_*/M`. -/
noncomputable abbrev dimensionShiftSequence (A : Rep k G) :
    ShortComplex (Rep k G) :=
  ShortComplex.cokernelSequence (canonicalShiftEmbedding A)

/-- Milne's canonical dimension-shifting sequence is short exact. -/
theorem shift_sequence_short (A : Rep k G) :
    (dimensionShiftSequence A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := shift_embedding_mono A
  epi_g := inferInstance

/-- The middle term `M_*` of the canonical dimension-shifting sequence has
zero positive-degree cohomology by Shapiro's lemma. -/
theorem shift_middle_acyclic
    (A : Rep k G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology (dimensionShiftSequence A).X₂ n) := by
  change IsZero (groupCohomology
    (Rep.coind (⊥ : Subgroup G).subtype
      (Rep.res (⊥ : Subgroup G).subtype A)) n)
  exact zero_cohomology_coinduced
    (Rep.res (⊥ : Subgroup G).subtype A) n hn

/-- The canonical dimension-shifting isomorphism
`H^r(G,M_dagger) ≃ H^(r+1)(G,M)` for every positive `r`. -/
noncomputable def canonicalShiftingIso
    (A : Rep k G) (n : ℕ) (hn : 0 < n) :
    groupCohomology (dimensionShiftSequence A).X₃ n ≅
      groupCohomology A (n + 1) :=
  dimensionShiftingIso (shift_sequence_short A)
    (shift_middle_acyclic A) n hn

/-- In the canonical sequence the boundary `H^0(G,M_dagger) -> H^1(G,M)`
is surjective. -/
theorem shift_delta_epi (A : Rep k G) :
    Epi (groupCohomology.δ
      (shift_sequence_short A) 0 1 rfl) :=
  shifting_delta_epi
    (shift_sequence_short A)
    (shift_middle_acyclic A 1 Nat.zero_lt_one)

end

end Submission.CField.COps
