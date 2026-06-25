import Towers.ClassField.SimpleAlgebras.SSupGenerators

/-!
# Milne, Class Field Theory, Proposition IV.1.4

The existing range-set formulation selects a set of distinct simple
submodules from the range of the given family.  The source statement instead
selects a subset of the original index set.  The theorem below makes that
last step explicit: choose one original index for each selected submodule.
The resulting indexed family is supremum-independent, so its supremum is the
internal direct sum appearing in Milne's statement.
-/

namespace Towers.CField.SAlgebr

open Set

noncomputable section

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **Proposition IV.1.4.**  If `M` is the sum of a family of simple
submodules `S i`, then every submodule `W` has a complement which is the
internal direct sum of the `S j` for a subset `J` of the original index set.
-/
theorem indexed_complement_simple
    (S : ι → Submodule R M)
    (hS : ∀ i, IsSimpleModule R (S i))
    (hTop : ⨆ i, S i = ⊤)
    (W : Submodule R M) :
    ∃ J : Set ι,
      iSupIndep (fun j : J ↦ S j.1) ∧
        IsCompl W (⨆ j : J, S j.1) := by
  obtain ⟨T, hTrange, hTindep, hTcompl⟩ :=
    complement_simple_generators S hS hTop W
  let chooseIndex : T → ι := fun A ↦
    Classical.choose (hTrange A.property)
  have hchoose (A : T) : S (chooseIndex A) = A.1 :=
    Classical.choose_spec (hTrange A.property)
  let J : Set ι := Set.range chooseIndex
  have hmem (j : J) : S j.1 ∈ T := by
    obtain ⟨A, hA⟩ := j.property
    have hj : S j.1 = A.1 := by
      rw [← hA]
      exact hchoose A
    rw [hj]
    exact A.property
  have hSinjective : Function.Injective (fun j : J ↦ S j.1) := by
    intro j k hjk
    obtain ⟨A, hA⟩ := j.property
    obtain ⟨B, hB⟩ := k.property
    have hAB : A = B := by
      apply Subtype.ext
      calc
        A.1 = S (chooseIndex A) := (hchoose A).symm
        _ = S j.1 := congrArg S hA
        _ = S k.1 := hjk
        _ = S (chooseIndex B) := congrArg S hB.symm
        _ = B.1 := hchoose B
    apply Subtype.ext
    exact hA.symm.trans ((congrArg chooseIndex hAB).trans hB)
  let toT : J → T := fun j ↦ ⟨S j.1, hmem j⟩
  have htoTInjective : Function.Injective toT := by
    intro j k hjk
    apply hSinjective
    exact congrArg Subtype.val hjk
  have hTindexed : iSupIndep ((↑) : T → Submodule R M) :=
    (sSupIndep_iff T).mp hTindep
  have hJindep : iSupIndep (fun j : J ↦ S j.1) := by
    have hcomp := hTindexed.comp htoTInjective
    simpa only [toT, Function.comp_apply] using hcomp
  have hsup : (⨆ j : J, S j.1) = sSup T := by
    apply le_antisymm
    · refine iSup_le fun j ↦ ?_
      exact le_sSup (hmem j)
    · rw [sSup_le_iff]
      intro A hA
      let j : J :=
        ⟨chooseIndex ⟨A, hA⟩, ⟨⟨A, hA⟩, rfl⟩⟩
      have hj : S j.1 = A := hchoose ⟨A, hA⟩
      rw [← hj]
      exact le_iSup (fun j : J ↦ S j.1) j
  refine ⟨J, hJindep, ?_⟩
  rw [hsup]
  exact hTcompl

end

end Towers.CField.SAlgebr
