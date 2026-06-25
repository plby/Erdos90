import Submission.ClassField.GrunwaldWang.IndexSubgroupExtension
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Extending prescribed subgroups on a finite family

This file packages the finite-product bookkeeping in the paragraph before
Theorem VIII.2.3.  A family of homomorphisms `j i : G i →* C` induces the
product homomorphism `Π i, G i →* C`.  Once a sufficiently small open
finite-index subgroup of `C` is known, the abstract extension lemma produces
one ambient subgroup whose pullback along every `j i` is the prescribed
subgroup `N i`.
-/

namespace Submission.CField.GWang

open scoped BigOperators

noncomputable section

/-- The homomorphism from a finite product obtained by multiplying the
images of all coordinates. -/
def finiteFamilyHom
    {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    (C : Type*) [CommGroup C] (j : ∀ i, G i →* C) :
    ((i : ι) → G i) →* C := by
  classical
  exact (Pi.monoidHomMulEquiv G C).symm j

@[simp]
theorem finite_family_hom
    {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    (C : Type*) [CommGroup C] (j : ∀ i, G i →* C)
    (x : (i : ι) → G i) :
    finiteFamilyHom G C j x = ∏ i, j i (x i) := by
  classical
  simp [finiteFamilyHom, Pi.monoidHomMulEquiv]

@[simp]
theorem family_hom_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    (C : Type*) [CommGroup C] (j : ∀ i, G i →* C)
    (i : ι) (x : G i) :
    finiteFamilyHom G C j (Pi.mulSingle i x) = j i x := by
  change (((Pi.monoidHomMulEquiv G C).symm j).comp
    (MonoidHom.mulSingle G i)) x = j i x
  have h := congrFun ((Pi.monoidHomMulEquiv G C).apply_symm_apply j) i
  exact congrArg (fun f : G i →* C ↦ f x) h

/-- The combined finite-family homomorphism is continuous when every
coordinate homomorphism is continuous. -/
theorem continuous_family_hom
    {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (C : Type*) [CommGroup C] [TopologicalSpace C] [ContinuousMul C]
    (j : ∀ i, G i →* C) (hj : ∀ i, Continuous (j i)) :
    Continuous (finiteFamilyHom G C j) := by
  classical
  have h : Continuous (fun x : (i : ι) → G i ↦ ∏ i, j i (x i)) :=
    continuous_finsetProd Finset.univ fun i _ ↦
      (hj i).comp (continuous_apply i)
  convert h using 1
  ext x
  simp [finiteFamilyHom, Pi.monoidHomMulEquiv]

/-- The product of a family of subgroups. -/
abbrev finiteFamilySubgroup
    {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
    (N : ∀ i, Subgroup (G i)) : Subgroup ((i : ι) → G i) :=
  Subgroup.pi Set.univ N

/-- A finite product of open subgroups is open in the product topology. -/
theorem family_subgroup_open
    {ι : Type*} [Finite ι]
    (G : ι → Type*) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (N : ∀ i, Subgroup (G i))
    (hN : ∀ i, IsOpen (N i : Set (G i))) :
    IsOpen (finiteFamilySubgroup G N : Set ((i : ι) → G i)) := by
  rw [Subgroup.coe_pi]
  exact isOpen_set_pi Set.finite_univ fun i _ ↦ hN i

/-- A finite product of finite-index subgroups has finite index. -/
theorem family_subgroup_index
    {ι : Type*} [Finite ι]
    (G : ι → Type*) [∀ i, Group (G i)]
    (N : ∀ i, Subgroup (G i)) (hN : ∀ i, (N i).FiniteIndex) :
    (finiteFamilySubgroup G N).FiniteIndex := by
  classical
  have hpi : finiteFamilySubgroup G N =
      ⨅ i, (N i).comap (Pi.evalMonoidHom G i) := by
    ext x
    simp [finiteFamilySubgroup, Subgroup.mem_pi]
  rw [hpi]
  apply Subgroup.finiteIndex_iInf
  intro i
  refine ⟨?_⟩
  rw [Subgroup.index_comap_of_surjective]
  · exact (hN i).index_ne_zero
  · intro x
    exact ⟨fun j ↦ if h : j = i then h ▸ x else 1, by simp⟩

/-- It is enough to find one open finite-index ambient subgroup whose
pullback along the combined product homomorphism is contained in the product
of the prescribed subgroups. -/
theorem open_comap_family
    {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    (C : Type*) [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (j : ∀ i, G i →* C) (N : ∀ i, Subgroup (G i))
    (V : Subgroup C) (hVopen : IsOpen (V : Set C))
    (hVfinite : V.FiniteIndex)
    (hVsmall : V.comap (finiteFamilyHom G C j) ≤
      finiteFamilySubgroup G N) :
    ∃ U : Subgroup C,
      IsOpen (U : Set C) ∧ U.FiniteIndex ∧
        ∀ i, U.comap (j i) = N i := by
  classical
  obtain ⟨U, hUopen, hUfinite, hUproduct⟩ :=
    open_index_comap
      (finiteFamilyHom G C j) (finiteFamilySubgroup G N)
      V hVopen hVfinite hVsmall
  refine ⟨U, hUopen, hUfinite, fun i ↦ ?_⟩
  apply le_antisymm
  · intro x hx
    have hsingle : Pi.mulSingle i x ∈
        U.comap (finiteFamilyHom G C j) := by
      change finiteFamilyHom G C j (Pi.mulSingle i x) ∈ U
      simpa only [family_hom_single] using hx
    rw [hUproduct] at hsingle
    exact (Subgroup.mulSingle_mem_pi i x).mp hsingle (Set.mem_univ i)
  · intro x hx
    have hsingle : Pi.mulSingle i x ∈ finiteFamilySubgroup G N :=
      (Subgroup.mulSingle_mem_pi i x).mpr fun _ ↦ hx
    rw [← hUproduct] at hsingle
    change finiteFamilyHom G C j (Pi.mulSingle i x) ∈ U at hsingle
    simpa only [family_hom_single] using hsingle

end

end Submission.CField.GWang
