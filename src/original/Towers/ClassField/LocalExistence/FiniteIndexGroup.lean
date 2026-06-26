import Towers.ClassField.NormCorrespondence.FiniteIndexOpen
import Towers.ClassField.LocalExistence.ImageKernelCompact
import Towers.ClassField.LocalExistence.CandidateNonemptiness
import Towers.ClassField.LocalExistence.NormCoreTriviality

/-!
# Milne, Theorem III.5.1: the local existence theorem

For a characteristic-zero nonarchimedean local field, every open subgroup
of finite index in `Kˣ` is the norm group of a finite abelian extension.
The source statement below has no proof-assumption parameters.  The
subsequent theorems expose exactly the remaining Step 3 input while reusing
the completed compactness and lattice assembly.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LRecip

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CharZero K]

local instance sourceStatementIffEveryFiniteIndexIsNormGroupValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance sourceStatementIffEveryFiniteIndexIsNormGroupValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

/-- **Theorem III.5.1 (Existence Theorem), literal reverse direction.**
Every open finite-index subgroup of `Kˣ` is the norm group of a finite
abelian subextension. -/
def IndexNormExistence : Prop :=
  ∀ H : Subgroup Kˣ,
    OFSubgro H → LGroup K H

/-- In characteristic zero, finite index already implies openness.  Thus
the literal statement is equivalent to Milne's formulation using only
finite-index subgroups. -/
theorem index_existence_every :
    IndexNormExistence K ↔
      ∀ H : Subgroup Kˣ, H.FiniteIndex → LGroup K H := by
  constructor
  · intro h H hfinite
    exact h H ⟨open_char_zero H hfinite, hfinite⟩
  · intro h H hH
    exact h H hH.2

omit [CharZero K] in
/-- With local reciprocity supplying the already-proved forward direction,
the literal source statement is exactly the full local existence theorem. -/
theorem local_existence_theorem
    (hrec : LocalReciprocityLaw K) :
    LocalExistenceTheorem K ↔ IndexNormExistence K := by
  constructor
  · intro h H hH
    exact (h H).2 hH
  · intro h H
    constructor
    · exact local_existence_reciprocity K hrec H
    · exact h H

omit [CharZero K] in
/-- Every finite-abelian norm-family member has finite index, using the
finite local norm-residue equivalence already proved in Chapter III.3. -/
theorem local_family_index
    (L : FASubext K) :
    (localNormFamily K L).FiniteIndex := by
  letI : Finite (Kˣ ⧸ normSubgroup K L.1) :=
    Finite.of_injective (localArtinEquiv K L.1)
      (localArtinEquiv K L.1).injective
  change (normSubgroup K L.1).FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Consequently every member of the concrete norm family is closed.  This
is the unconditional Step 1 input needed by the final compactness argument. -/
theorem local_family_closed
    (L : FASubext K) :
    IsClosed (localNormFamily K L : Set Kˣ) := by
  apply (localNormFamily K L).isClosed_of_isOpen
  exact open_char_zero
    (localNormFamily K L) (local_family_index K L)

/-- Strongest arithmetic-independent final assembly.  The completed Steps
1, 4, and 5 plus the abstract norm correspondence reduce the existence
theorem solely to Step 3 divisibility. -/
theorem existence_correspondence_candidate
    (hNorm : LocalNormCorrespondence K)
    (hCandidateNonemptiness : (IDSubgro (localNormCore K))) :
    IndexNormExistence K := by
  intro I hI
  letI : I.FiniteIndex := hI.2
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  have hcore : localNormCore K ≤ I := hCandidateNonemptiness.le_finiteIndex
  obtain ⟨L, hLI⟩ := inf_directed_core
    (localUnitSubgroup K) I (localNormFamily K)
    (local_unit_compact K) hI.1
    (local_family_closed K)
    (local_family_directed K hNorm) hcore
  refine family_inf
    (LGroup K) (localUnitSubgroup K) I
    ?_ ?_ ?_ ?_ (localNormFamily K L) ⟨L, rfl⟩ hLI
  · intro N hN
    obtain ⟨E, rfl⟩ := hN
    exact local_family_index K E
  · intro N J hN hNJ hJfinite
    obtain ⟨E, hE⟩ := hN
    apply hNorm.supergroup_norm_group E J
    exact hE.trans_le hNJ
  · intro N₁ N₂ hN₁ hN₂
    obtain ⟨E₁, rfl⟩ := hN₁
    obtain ⟨E₂, rfl⟩ := hN₂
    obtain ⟨M, _, hM⟩ := hNorm.norm_compositum E₁ E₂
    exact ⟨M.normGroup, ⟨M, rfl⟩, le_of_eq hM⟩
  · intro J hJfinite hUJ
    letI : J.FiniteIndex := hJfinite
    exact local_unit_subgroup K J hUJ

/-- Exact candidate-nonemptiness form of the unconditional final assembly. -/
theorem existence_candidate_nonemptiness
    (hNorm : LocalNormCorrespondence K)
    (hcandidates : CandidateNonemptiness K) :
    IndexNormExistence K := by
  apply existence_correspondence_candidate K hNorm
  exact candidate_nonemptiness K hcandidates

/-- The completed compactness/lattice assembly reduces Theorem III.5.1 to
the literal Step 3 assertion that the common norm core is divisible. -/
theorem reciprocity_candidate_statement
    (hrec : LocalReciprocityLaw K)
    (hCandidateNonemptiness : (IDSubgro (localNormCore K))) :
    IndexNormExistence K := by
  exact existence_correspondence_candidate K
    (norm_correspondence_reciprocity hrec) hCandidateNonemptiness

/-- Equivalently, it is enough to prove nonemptiness of all finite candidate
sets `E(L)` from Step 3. Finiteness and directedness are already proved by
`candidate_nonemptiness`. -/
theorem existence_reciprocity_nonemptiness
    (hrec : LocalReciprocityLaw K)
    (hcandidates : CandidateNonemptiness K) :
    IndexNormExistence K := by
  apply reciprocity_candidate_statement K hrec
  exact candidate_nonemptiness K hcandidates

omit [CharZero K] in
/-- Finite-level reciprocity is sufficient for the final assembly; neither
Frobenius normalization nor uniqueness of the infinite Artin map is used. -/
theorem existence_candidate_statement
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (hCandidateNonemptiness : (IDSubgro (localNormCore K))) :
    IndexNormExistence K := by
  intro H hH
  exact existence_divisible_core
    K phi hphi hCandidateNonemptiness H hH

omit [CharZero K] in
/-- Exact candidate-set form of the preceding finite-reciprocity reduction. -/
theorem reciprocity_candidate_nonemptiness
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (hcandidates : CandidateNonemptiness K) :
    IndexNormExistence K := by
  apply existence_candidate_statement K phi hphi
  exact candidate_nonemptiness K hcandidates

end

end Towers.CField.LExist
