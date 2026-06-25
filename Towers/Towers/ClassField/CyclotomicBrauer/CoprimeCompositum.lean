import Towers.ClassField.CyclotomicBrauer.CompositumArithmetic
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Lemma VII.7.3: coprime cyclic composita

Two finite Galois subfields of a common overfield whose degrees are
coprime have a cyclic compositum when both factors are cyclic.  Their
degrees multiply.  This is the binary field-theoretic step behind the
finite compositum of the prime-power blocks in Lemma VII.7.3.
-/

namespace Towers.CField.CBrauer

open IntermediateField

noncomputable section

universe u v

variable {K : Type v} {Omega : Type u}
  [Field K] [Field Omega] [Algebra K Omega]

/-- The compositum of cyclic Galois fields of coprime degrees is cyclic. -/
theorem compositum_coprime_finrank
    (A B : IntermediateField K Omega)
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsGalois K A] [IsGalois K B]
    [IsCyclic Gal(↑A/K)] [IsCyclic Gal(↑B/K)]
    (hcoprime : (Module.finrank K A).Coprime (Module.finrank K B)) :
    IsCyclic Gal(↑(A ⊔ B)/K) := by
  let A0 := A.restrict (show A ≤ A ⊔ B from le_sup_left)
  let B0 := B.restrict (show B ≤ A ⊔ B from le_sup_right)
  let eA : A ≃ₐ[K] A0 := IntermediateField.restrict_algEquiv le_sup_left
  let eB : B ≃ₐ[K] B0 := IntermediateField.restrict_algEquiv le_sup_right
  letI : FiniteDimensional K ↑(A ⊔ B) :=
    IntermediateField.finiteDimensional_sup A B
  letI : IsGalois K ↑(A ⊔ B) := inferInstance
  letI : IsGalois K A0 := IsGalois.of_algEquiv eA
  letI : IsGalois K B0 := IsGalois.of_algEquiv eB
  letI : IsCyclic Gal(↑A0/K) :=
    isCyclic_of_surjective (AlgEquiv.autCongr eA)
      (AlgEquiv.autCongr eA).surjective
  letI : IsCyclic Gal(↑B0/K) :=
    isCyclic_of_surjective (AlgEquiv.autCongr eB)
      (AlgEquiv.autCongr eB).surjective
  have hcoprimeCard : (Nat.card Gal(↑A0/K)).Coprime
      (Nat.card Gal(↑B0/K)) := by
    rw [IsGalois.card_aut_eq_finrank K A0,
      IsGalois.card_aut_eq_finrank K B0,
      ← eA.toLinearEquiv.finrank_eq, ← eB.toLinearEquiv.finrank_eq]
    exact hcoprime
  letI : IsCyclic (Gal(↑A0/K) × Gal(↑B0/K)) :=
    cyclic_coprime_card Gal(↑A0/K) Gal(↑B0/K) hcoprimeCard
  let restriction : Gal(↑(A ⊔ B)/K) →* Gal(↑A0/K) × Gal(↑B0/K) :=
    (AlgEquiv.restrictNormalHom A0).prod (AlgEquiv.restrictNormalHom B0)
  apply isCyclic_of_injective restriction
  apply (injective_iff_map_eq_one restriction).2
  intro sigma hsigma
  have hA : AlgEquiv.restrictNormalHom A0 sigma = 1 := by
    have h := congrArg Prod.fst hsigma
    exact h
  have hB : AlgEquiv.restrictNormalHom B0 sigma = 1 := by
    have h := congrArg Prod.snd hsigma
    exact h
  have hfixA : sigma ∈ A0.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' := congrArg (fun tau : Gal(A0/K) ↦ tau ⟨x, hx⟩) hA
    calc
      sigma x = ↑((AlgEquiv.restrictNormalHom A0 sigma) ⟨x, hx⟩) := by
        symm
        exact AlgEquiv.restrictNormal_commutes
          (χ := sigma) (E := A0) ⟨x, hx⟩
      _ = x := by simpa using congrArg Subtype.val hx'
  have hfixB : sigma ∈ B0.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' := congrArg (fun tau : Gal(B0/K) ↦ tau ⟨x, hx⟩) hB
    calc
      sigma x = ↑((AlgEquiv.restrictNormalHom B0 sigma) ⟨x, hx⟩) := by
        symm
        exact AlgEquiv.restrictNormal_commutes
          (χ := sigma) (E := B0) ⟨x, hx⟩
      _ = x := by simpa using congrArg Subtype.val hx'
  have hsup : A0 ⊔ B0 = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup,
      IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  have hfix : sigma ∈ (A0 ⊔ B0).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfixA, hfixB⟩
  rw [hsup, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hfix
  exact hfix

/-- Coprime finite extensions are linearly disjoint, so their compositum
has product degree. -/
theorem finrank_compositum_coprime
    (A B : IntermediateField K Omega)
    [FiniteDimensional K A] [FiniteDimensional K B]
    (hcoprime : (Module.finrank K A).Coprime (Module.finrank K B)) :
    Module.finrank K ↑(A ⊔ B) =
      Module.finrank K A * Module.finrank K B := by
  exact (IntermediateField.LinearDisjoint.of_finrank_coprime hcoprime).finrank_sup

/-- A finite supremum and the corresponding bounded supremum describe the
same intermediate field. -/
theorem finset_sup_bi
    {I : Type*} (fields : I → IntermediateField K Omega) (s : Finset I) :
    s.sup fields = ⨆ i ∈ s, fields i := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    exact Finset.le_sup (f := fields) hi

/-- A finite supremum of finite-dimensional intermediate fields is
finite-dimensional. -/
theorem finset_sup_dimensional
    {I : Type*} (fields : I → IntermediateField K Omega) (s : Finset I)
    (hfinite : ∀ i, FiniteDimensional K (fields i)) :
    let compositum : IntermediateField K Omega := s.sup fields
    FiniteDimensional K compositum := by
  let boundedSup : IntermediateField K Omega := ⨆ i ∈ s, fields i
  letI : FiniteDimensional K boundedSup := by
    dsimp only [boundedSup]
    exact IntermediateField.finiteDimensional_iSup_of_finset'
      (t := fields) (s := s) (fun i _ ↦ hfinite i)
  let compositum : IntermediateField K Omega := s.sup fields
  let equivalence : boundedSup ≃ₐ[K] compositum :=
    (IntermediateField.equivOfEq (finset_sup_bi fields s)).symm
  exact Module.Finite.equiv equivalence.toLinearEquiv

/-- A finite supremum of finite Galois intermediate fields is Galois. -/
theorem finset_sup_galois
    {I : Type*} (fields : I → IntermediateField K Omega) (s : Finset I)
    (hGalois : ∀ i, IsGalois K (fields i)) :
    let compositum : IntermediateField K Omega := s.sup fields
    IsGalois K compositum := by
  classical
  let index := {i // i ∈ s}
  let family : index → IntermediateField K Omega := fun i ↦ fields i.1
  let boundedSup : IntermediateField K Omega := ⨆ i ∈ s, fields i
  let indexedSup : IntermediateField K Omega := ⨆ i : index, family i
  have hsup : boundedSup = indexedSup := by
    apply le_antisymm
    · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
      exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    · refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le i.1 (le_iSup_of_le i.2 le_rfl)
  have hnormal : Normal K indexedSup := by
    simpa only [indexedSup, family] using
      (IntermediateField.normal_iSup
        (F := K) (K := Omega) (t := family)
        (h := fun i ↦ (hGalois i.1).to_normal))
  have hseparable : Algebra.IsSeparable K indexedSup := by
    simpa only [indexedSup, family] using
      (IntermediateField.isSeparable_iSup
        (F := K) (E := Omega) (t := family)
        (h := fun i ↦ (hGalois i.1).to_isSeparable))
  letI : IsGalois K indexedSup :=
    { to_normal := hnormal, to_isSeparable := hseparable }
  let compositum : IntermediateField K Omega := s.sup fields
  let equivalence : indexedSup ≃ₐ[K] compositum :=
    (IntermediateField.equivOfEq
      ((finset_sup_bi fields s).trans hsup)).symm
  exact IsGalois.of_algEquiv equivalence

/-- A finite compositum of cyclic Galois fields with pairwise coprime
degrees is cyclic, and its degree is the product of the factor degrees. -/
theorem finset_compositum_finrank
    {I : Type*}
    (fields : I → IntermediateField K Omega)
    [∀ i, FiniteDimensional K (fields i)]
    [∀ i, IsGalois K (fields i)]
    [∀ i, IsCyclic Gal(↑(fields i)/K)]
    (s : Finset I)
    (hcoprime : Set.Pairwise (s : Set I)
      (Function.onFun Nat.Coprime fun i ↦ Module.finrank K (fields i))) :
    let compositum : IntermediateField K Omega := s.sup fields
    IsCyclic Gal(↑compositum/K) ∧
      Module.finrank K compositum =
        ∏ i ∈ s, Module.finrank K (fields i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      dsimp only
      rw [Finset.sup_empty, Finset.prod_empty]
      letI : IsGalois K (⊥ : IntermediateField K Omega) := inferInstance
      have hcard : Nat.card Gal(↑(⊥ : IntermediateField K Omega)/K) = 1 := by
        rw [IsGalois.card_aut_eq_finrank K (⊥ : IntermediateField K Omega)]
        exact (IntermediateField.botEquiv K Omega).symm.toLinearEquiv.finrank_eq.symm.trans
          (Module.finrank_self K)
      letI : Subsingleton Gal(↑(⊥ : IntermediateField K Omega)/K) :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      constructor
      · infer_instance
      · exact (IntermediateField.botEquiv K Omega).symm.toLinearEquiv.finrank_eq.symm.trans
          (Module.finrank_self K)
  | @insert a s ha ih =>
      have hcoprimeS : Set.Pairwise (s : Set I)
          (Function.onFun Nat.Coprime fun i ↦ Module.finrank K (fields i)) :=
        hcoprime.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
      obtain ⟨hcyclicS, hdegreeS⟩ := ih hcoprimeS
      let compositumS : IntermediateField K Omega := s.sup fields
      letI : FiniteDimensional K compositumS :=
        finset_sup_dimensional fields s (fun i ↦ inferInstance)
      letI : IsGalois K compositumS :=
        finset_sup_galois fields s (fun i ↦ inferInstance)
      letI : IsCyclic Gal(↑compositumS/K) := hcyclicS
      have hfactorCoprime : (Module.finrank K (fields a)).Coprime
          (Module.finrank K compositumS) := by
        rw [hdegreeS, Nat.coprime_prod_right_iff]
        intro i hi
        exact hcoprime (Finset.mem_insert_self a s)
          (Finset.mem_insert_of_mem hi) (by
            intro hai
            apply ha
            rwa [hai])
      have hcyclic : IsCyclic Gal(↑(fields a ⊔ compositumS)/K) :=
        compositum_coprime_finrank
          (fields a) compositumS hfactorCoprime
      have hdegree : Module.finrank K ↑(fields a ⊔ compositumS) =
          Module.finrank K (fields a) * Module.finrank K compositumS :=
        finrank_compositum_coprime
          (fields a) compositumS hfactorCoprime
      dsimp only
      rw [Finset.sup_insert, Finset.prod_insert ha]
      exact ⟨hcyclic, hdegree.trans (congrArg (Module.finrank K (fields a) * ·)
        hdegreeS)⟩

end

end Towers.CField.CBrauer
