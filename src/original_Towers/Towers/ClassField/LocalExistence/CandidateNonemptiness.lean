import Towers.ClassField.HilbertSymbols.FiniteCyclicExtension
import Towers.ClassField.LocalExistence.HilbertRootCandidates
import Towers.ClassField.LocalExistence.RelativeNormCore

/-!
# Milne, Class Field Theory, Section III.5, Step 3

This file states Step 3 literally: the common norm subgroup `D_K` is
divisible.  It proves unconditionally the finite-set, compositum-directedness,
and norm-of-an-`n`th-power parts of Milne's argument.  Consequently the source
statement is equivalent to nonemptiness of all candidate sets `E(L)`.

The remaining source bridge is arithmetic.  Step 2 produces an element of a
relative norm core upstairs.  To invoke Proposition III.4.1 one must know that
this element is a norm from every cyclic extension of the upstairs field whose
degree divides `n`; equivalently, every corresponding finite Artin symbol must
vanish.  The current relative core only ranges over overfields abelian over
the original base, and Proposition III.4.1 itself is not yet proved.  These
two missing facts are isolated below as propositions, not added to the source
statement.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.HSymbol
open Towers.CField.LBrauer

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance candidateNonemptinessValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance candidateNonemptinessValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

set_option maxHeartbeats 3000000 in
-- Norm transitivity through the two compositum towers is instance-heavy.
set_option synthInstance.maxHeartbeats 500000 in
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- Pure norm transitivity: the norm group of a compositum is contained in
the norm group of each factor.  This is the directedness input in Step 3 and
does not require a norm-correspondence hypothesis. -/
theorem norm_group_sup
    (L₁ L₂ : FASubext K) :
    (L₁.sup L₂).normGroup ≤ L₁.normGroup ⊓ L₂.normGroup := by
  intro x hx
  let S : FASubext K := L₁.sup L₂
  have h₁ : L₁.intermediateField ≤ S.intermediateField := by
    dsimp [S]
    exact le_sup_left
  have h₂ : L₂.intermediateField ≤ S.intermediateField := by
    dsimp [S]
    exact le_sup_right
  change x ∈ S.normGroup at hx
  constructor
  · obtain ⟨z, rfl⟩ := hx
    letI : Algebra L₁.1 S.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion h₁)
    letI : IsScalarTower K L₁.1 S.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : Module.Finite L₁.1 S.1 :=
      Module.Finite.of_restrictScalars_finite K L₁.1 S.1
    exact ⟨normOnUnits L₁.1 S.1 z, by
      apply Units.ext
      exact Algebra.norm_norm (R := K) (S := L₁.1)
        (A := S.1) (a := (z : S.1))⟩
  · obtain ⟨z, rfl⟩ := hx
    letI : Algebra L₂.1 S.1 :=
      RingHom.toAlgebra (IntermediateField.inclusion h₂)
    letI : IsScalarTower K L₂.1 S.1 :=
      IsScalarTower.of_algebraMap_eq fun x => by rfl
    letI : Module.Finite L₂.1 S.1 :=
      Module.Finite.of_restrictScalars_finite K L₂.1 S.1
    exact ⟨normOnUnits L₂.1 S.1 z, by
      apply Units.ext
      exact Algebra.norm_norm (R := K) (S := L₂.1)
        (A := S.1) (a := (z : S.1))⟩

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The sets `E(L)` are downward directed under compositum, unconditionally. -/
theorem candidates_directed_compositum
    (n : ℕ) (a : Kˣ) (L₁ L₂ : FASubext K) :
    ∃ M : FASubext K,
      localRootCandidates K n a M ⊆
        localRootCandidates K n a L₁ ∩
          localRootCandidates K n a L₂ := by
  refine ⟨L₁.sup L₂, ?_⟩
  rintro b ⟨hpow, hnorm⟩
  have h := norm_group_sup K L₁ L₂ hnorm
  exact ⟨⟨hpow, h.1⟩, ⟨hpow, h.2⟩⟩

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The norm-of-a-power calculation in Milne's proof: if `a` has an
upstairs norm preimage which is an `n`th power, then `E(L)` is nonempty. -/
theorem candidates_nonempty_preimage
    (n : ℕ) (a : Kˣ) (L : FASubext K)
    (h : NthNormPreimage K n a L) :
    (localRootCandidates K n a L).Nonempty :=
  candidates_nth_preimage K n a L h

/-- Exact candidate-set formulation of the only remaining assertion in the
finite-intersection proof. -/
def CandidateNonemptiness : Prop :=
  ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ localNormCore K,
    ∀ L : FASubext K,
      (localRootCandidates K n a L).Nonempty

/-- Nonempty finite directed candidate sets give the divisibility asserted
in Step 3. -/
theorem candidate_nonemptiness
    (h : CandidateNonemptiness K) :
    (IDSubgro (localNormCore K)) := by
  intro n hn a ha
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  obtain ⟨b, hb, hpow⟩ := common_directed_nonempty
    (localRootCandidates K n a) n a
    (candidates_directed_compositum K n a)
    (h n hn a ha)
    (local_root_candidates K n hn a)
    (fun _ _ hb => hb.1)
  refine ⟨b, ?_, hpow⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf]
  intro L
  exact (Set.mem_iInter.mp hb L).2

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- Conversely, divisibility supplies a common root in the norm core and
hence a point of every candidate set.  Thus this reduction loses nothing. -/
theorem nonemptiness_statement
    (h : (IDSubgro (localNormCore K))) :
    CandidateNonemptiness K := by
  intro n hn a ha L
  obtain ⟨b, hb, hpow⟩ := h n hn a ha
  refine ⟨b, hpow, ?_⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf] at hb
  exact hb L

/-- The literal Step 3 statement is exactly candidate nonemptiness; all
finiteness and directedness work has been discharged above. -/
theorem candidate_nonemptiness_statement :
    (
      IDSubgro (localNormCore K)
    ) ↔ CandidateNonemptiness K := by
  exact ⟨nonemptiness_statement K,
    candidate_nonemptiness K⟩

end

end Towers.CField.LExist
