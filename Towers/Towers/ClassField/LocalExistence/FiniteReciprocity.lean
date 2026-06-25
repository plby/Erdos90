import Towers.ClassField.LocalExistence.ConcreteLocalExistence
import Towers.ClassField.LocalExistence.FiniteNormRoots

/-!
# Local existence from finite-level reciprocity

The existence proof only uses the finite norm-residue isomorphisms, rather
than Frobenius normalization or uniqueness of the infinite local Artin map.
This file records that sharper dependency and reduces divisibility of the
common norm subgroup to the concrete nonemptiness assertion in Step III.5.3.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The possible `n`th roots of `a` which belong to one finite-abelian norm
group.  These are Milne's finite sets `E(L)` in Step III.5.3. -/
def localRootCandidates (n : ℕ) (a : Kˣ)
    (L : FASubext K) : Set Kˣ :=
  {b | b ^ n = a ∧ b ∈ localNormFamily K L}

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- For a positive exponent, every set of local norm-root candidates is
finite.  This is the purely polynomial part of Step III.5.3. -/
theorem local_root_candidates
    (n : ℕ) (hn : n ≠ 0) (a : Kˣ) (L : FASubext K) :
    (localRootCandidates K n a L).Finite := by
  let p : Polynomial K := Polynomial.X ^ n - Polynomial.C (a : K)
  have hp : p ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) (a : K)
  apply Set.Finite.of_finite_image (f := fun b : Kˣ ↦ (b : K))
  · apply (Polynomial.finite_setOf_isRoot hp).subset
    rintro x ⟨b, hb, rfl⟩
    change Polynomial.IsRoot p (b : K)
    rw [Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    exact sub_eq_zero.mpr (congrArg Units.val hb.1)
  · intro x _ y _ hxy
    exact Units.ext hxy

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The norm correspondence makes the candidate-root sets downward directed.
No root-existence input is used here. -/
theorem local_candidates_directed
    (hNorm : LocalNormCorrespondence K) (n : ℕ) (a : Kˣ)
    (L₁ L₂ : FASubext K) :
    ∃ M : FASubext K,
      localRootCandidates K n a M ⊆
        localRootCandidates K n a L₁ ∩
          localRootCandidates K n a L₂ := by
  obtain ⟨M, hM⟩ := local_family_directed K hNorm L₁ L₂
  refine ⟨M, ?_⟩
  rintro b hb
  exact ⟨⟨hb.1, (hM hb.2).1⟩, ⟨hb.1, (hM hb.2).2⟩⟩

/-- The strongest direct reduction of the missing divisibility step supplied
by the current Section 5 API.  It remains only to prove that each finite set
`E(L)` is nonempty; directedness, finiteness, common norm membership, and the
power identity are then automatic. -/
theorem divisible_candidates_nonempty
    (hNorm : LocalNormCorrespondence K)
    (hnonempty : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ localNormCore K,
      ∀ L : FASubext K,
        (localRootCandidates K n a L).Nonempty) :
    IDSubgro (localNormCore K) := by
  intro n hn a ha
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  obtain ⟨b, hb, hpow⟩ := common_directed_nonempty
    (localRootCandidates K n a) n a
    (local_candidates_directed K hNorm n a)
    (hnonempty n hn a ha)
    (local_root_candidates K n hn a)
    (fun _ _ hb ↦ hb.1)
  refine ⟨b, ?_, hpow⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf]
  intro L
  exact (Set.mem_iInter.mp hb L).2

set_option synthInstance.maxHeartbeats 200000 in
-- The finite quotient and Galois-group instances require deeper synthesis than the default budget.
omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Finite-level reciprocity makes every finite-abelian norm group have
finite index. -/
theorem norm_index_reciprocity
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L : FASubext K) :
    L.normGroup.FiniteIndex := by
  obtain ⟨e, _⟩ := hphi L
  letI : Finite Gal(L.finiteIntermediateField/K) := inferInstance
  letI : Finite (Kˣ ⧸ L.normGroup) :=
    Finite.of_equiv Gal(L.finiteIntermediateField/K) e.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Finite-level reciprocity and Lemma I.1.3 make every norm-family member
closed, which is the topological input to the final compactness argument. -/
theorem local_closed_reciprocity
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (L : FASubext K) :
    IsClosed (localNormFamily K L : Set Kˣ) := by
  apply (localNormFamily K L).isClosed_of_isOpen
  letI : L.normGroup.FiniteIndex :=
    norm_index_reciprocity K phi hphi L
  letI : (normSubgroup K L.1).FiniteIndex := by
    change L.normGroup.FiniteIndex
    infer_instance
  change IsOpen (L.normGroup : Set Kˣ)
  exact norm_subgroup K L.1

/-- The forward implication of local existence needs only finite-level
reciprocity. -/
theorem existence_forward_reciprocity
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L) :
    ∀ H : Subgroup Kˣ,
      LGroup K H → OFSubgro H := by
  apply existence_forward_index K
  intro H hH
  obtain ⟨L, hL⟩ := hH
  rw [← hL]
  exact norm_index_reciprocity K phi hphi L

/-- The reverse implication of local existence from finite-level reciprocity
and divisibility of the common norm subgroup. -/
theorem existence_divisible_core
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (hdiv : IDSubgro (localNormCore K)) :
    ∀ I : Subgroup Kˣ,
      OFSubgro I → LGroup K I := by
  let hNorm : LocalNormCorrespondence K :=
    local_correspondence_reciprocity phi hphi
  intro I hI
  letI : I.FiniteIndex := hI.2
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  have hcore : localNormCore K ≤ I := hdiv.le_finiteIndex
  obtain ⟨L, hLI⟩ := inf_directed_core
    (localUnitSubgroup K) I (localNormFamily K)
    (local_unit_compact K) hI.1
    (local_closed_reciprocity K phi hphi)
    (local_family_directed K hNorm) hcore
  refine family_inf
    (LGroup K) (localUnitSubgroup K) I
    ?_ ?_ ?_ ?_ (localNormFamily K L) ⟨L, rfl⟩ hLI
  · intro N hN
    obtain ⟨E, rfl⟩ := hN
    exact norm_index_reciprocity K phi hphi E
  · intro N J hN hNJ hJfinite
    rcases hN with ⟨E, hE⟩
    apply hNorm.supergroup_norm_group E J
    exact hE.trans_le hNJ
  · intro N₁ N₂ hN₁ hN₂
    rcases hN₁ with ⟨E₁, rfl⟩
    rcases hN₂ with ⟨E₂, rfl⟩
    obtain ⟨M, _, hM⟩ := hNorm.norm_compositum E₁ E₂
    exact ⟨M.normGroup, ⟨M, rfl⟩, le_of_eq hM⟩
  · intro J hJfinite hUJ
    letI : J.FiniteIndex := hJfinite
    exact local_unit_subgroup K J hUJ

/-- Local existence depends on finite-level reciprocity and divisible core,
not on Frobenius normalization or uniqueness of the infinite reciprocity map. -/
theorem reciprocity_divisible_core
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (hdiv : IDSubgro (localNormCore K)) :
    LocalExistenceTheorem K := by
  intro I
  constructor
  · exact existence_forward_reciprocity K phi hphi I
  · exact existence_divisible_core
      K phi hphi hdiv I

/-- A finite-level-reciprocity form whose sole additional arithmetic input
is the nonemptiness of Milne's candidate root sets. -/
theorem existence_candidates_nonempty
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (hnonempty : ∀ (n : ℕ), n ≠ 0 → ∀ a ∈ localNormCore K,
      ∀ L : FASubext K,
        (localRootCandidates K n a L).Nonempty) :
    LocalExistenceTheorem K := by
  apply reciprocity_divisible_core K phi hphi
  exact divisible_candidates_nonempty K
    (local_correspondence_reciprocity phi hphi) hnonempty

end

end Towers.CField.LExist
