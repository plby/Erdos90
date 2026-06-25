import Towers.ClassField.CyclotomicBrauer.CoprimeCompositum

/-!
# Lemma VII.7.3: finite cyclotomic composita

This file packages the second half of the common-ambient construction.  A
finite family of cyclotomic intermediate fields in one overfield has a
cyclotomic compositum, with conductor obtained by iterated least common
multiple.  Subfields embedded in the corresponding cyclotomic factors lie
in that common cyclotomic overfield.
-/

namespace Towers.CField.CBrauer

open IntermediateField

noncomputable section

universe u v

variable {K : Type v} {Omega : Type u}
  [Field K] [Field Omega] [Algebra K Omega]

/-- A singleton cyclotomic presentation can always be replaced by one with
a nonzero conductor.  Conductor zero forces the extension to be trivial,
which is cyclotomic of conductor one. -/
theorem nonzero_cyclotomic_conductor
    (n : ℕ) (L : Type*) [Field L] [Algebra K L]
    (hcyclotomic : IsCyclotomicExtension {n} K L) :
    ∃ m : ℕ, m ≠ 0 ∧ IsCyclotomicExtension {m} K L := by
  by_cases hn : n = 0
  · subst n
    have hsurjective : Function.Surjective (algebraMap K L) :=
      (IsCyclotomicExtension.isCyclotomicExtension_zero_iff
        (A := K) (B := L)).mp
        hcyclotomic
    exact ⟨1, one_ne_zero,
      IsCyclotomicExtension.singleton_one_of_algebraMap_bijective hsurjective⟩
  · exact ⟨n, hn, hcyclotomic⟩

/-- A finite supremum of rational cyclotomic intermediate fields is again
cyclotomic.  The resulting conductor is intentionally existential: only
the common cyclotomic overfield, not a minimal conductor, is used later. -/
theorem finset_sup_cyclotomic
    {I : Type*} (fields : I → IntermediateField K Omega)
    (conductors : I → ℕ)
    (hcyclotomic : ∀ i,
      IsCyclotomicExtension {conductors i} K ↑(fields i))
    (s : Finset I) :
    ∃ conductor : ℕ,
      conductor ≠ 0 ∧ IsCyclotomicExtension {conductor} K
        ↑(⨆ i ∈ s, fields i : IntermediateField K Omega) := by
  classical
  choose normalizedConductors hnormalizedNe hnormalizedCyclotomic using
    fun i ↦ nonzero_cyclotomic_conductor
      (K := K) (conductors i) ↑(fields i) (hcyclotomic i)
  induction s using Finset.induction_on with
  | empty =>
      haveI : IsCyclotomicExtension {1} K K :=
        IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
          (A := K) (B := K) (fun x ↦ ⟨x, rfl⟩)
      have hbot : (⨆ i ∈ (∅ : Finset I), fields i) =
          (⊥ : IntermediateField K Omega) := by simp
      let equivalence : K ≃ₐ[K]
          ↑(⨆ i ∈ (∅ : Finset I), fields i) :=
        (IntermediateField.botEquiv K Omega).symm.trans
          (IntermediateField.equivOfEq hbot.symm)
      exact ⟨1, one_ne_zero, IsCyclotomicExtension.equiv
        (S := {1}) (A := K) (B := K) equivalence⟩
  | @insert i s hi ih =>
      obtain ⟨conductor, hconductorNe, hcompositum⟩ := ih
      let A : IntermediateField K Omega := fields i
      let B : IntermediateField K Omega := ⨆ j ∈ s, fields j
      letI : IsCyclotomicExtension {normalizedConductors i} K A :=
        hnormalizedCyclotomic i
      letI : IsCyclotomicExtension {conductor} K B := hcompositum
      letI : NeZero (normalizedConductors i) := ⟨hnormalizedNe i⟩
      letI : NeZero conductor := ⟨hconductorNe⟩
      have hsup : IsCyclotomicExtension
          {Nat.lcm (normalizedConductors i) conductor} K ↑(A ⊔ B) := by
        exact IntermediateField.isCyclotomicExtension_lcm_sup
          K Omega (normalizedConductors i) conductor A B
      have hEq :
          (⨆ j ∈ insert i s, fields j : IntermediateField K Omega) =
            A ⊔ B := by
        calc
          (⨆ j ∈ insert i s, fields j : IntermediateField K Omega) =
              (insert i s).sup fields :=
            (Finset.sup_eq_iSup (insert i s) fields).symm
          _ = fields i ⊔ s.sup fields := Finset.sup_insert
          _ = A ⊔ B := by
            dsimp only [A, B]
            rw [Finset.sup_eq_iSup]
      refine ⟨Nat.lcm (normalizedConductors i) conductor,
        Nat.lcm_ne_zero (hnormalizedNe i) hconductorNe, ?_⟩
      exact hEq.symm ▸ hsup

/-- Pointwise inclusions of a finite family induce inclusion of the two
finite composita. -/
theorem finset_sup_mono
    {I : Type*} (small large : I → IntermediateField K Omega)
    (s : Finset I) (hle : ∀ i ∈ s, small i ≤ large i) :
    s.sup small ≤ s.sup large := by
  classical
  apply Finset.sup_le
  intro i hi
  exact (hle i hi).trans (Finset.le_sup (f := large) hi)

/-- Embed one cyclic cyclotomic block together with a witnessing cyclotomic
overfield into a chosen algebraically closed common ambient field.  The
block embedding is obtained by restricting the overfield embedding, so the
resulting intermediate fields come with the required inclusion. -/
theorem embedded_cyclic_data
    (data : FEData ℚ)
    (hcyclicCyclotomic : data.IsCyclicCyclotomic)
    (Omega : Type u) [Field Omega] [Algebra ℚ Omega] [IsAlgClosed Omega] :
    letI : Field data.L := data.fieldL
    letI : NumberField data.L := data.numberFieldL
    letI : Algebra ℚ data.L := data.algebraKL
    letI : FiniteDimensional ℚ data.L := data.finiteDimensionalKL
    letI : IsGalois ℚ data.L := data.isGaloisKL
    ∃ (blockField cyclotomicField : IntermediateField ℚ Omega),
      letI : Algebra ℚ blockField := blockField.algebra'
      letI : Algebra ℚ cyclotomicField := cyclotomicField.algebra'
      Nonempty (data.L ≃ₐ[ℚ] blockField) ∧
        blockField ≤ cyclotomicField ∧
          FiniteDimensional ℚ blockField ∧
          IsGalois ℚ blockField ∧
          IsCyclic Gal(↑blockField/ℚ) ∧
          ∃ conductor : ℕ,
            IsCyclotomicExtension {conductor} ℚ ↑cyclotomicField := by
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra ℚ data.L := data.algebraKL
  letI : FiniteDimensional ℚ data.L := data.finiteDimensionalKL
  letI : IsGalois ℚ data.L := data.isGaloisKL
  change IsCyclic Gal(data.L/ℚ) ∧ _ at hcyclicCyclotomic
  rcases hcyclicCyclotomic with
    ⟨cyclicL, conductor, C, fieldC, numberFieldC, algebraQC,
      algebraLC, scalarTower, cyclotomicC, _⟩
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : Algebra ℚ C := algebraQC
  letI : Algebra data.L C := algebraLC
  letI : IsScalarTower ℚ data.L C := scalarTower
  letI : IsCyclotomicExtension {conductor} ℚ C := cyclotomicC
  let embeddingC : C →ₐ[ℚ] Omega := IsAlgClosed.lift
  let cyclotomicField : IntermediateField ℚ Omega := embeddingC.fieldRange
  letI : Algebra ℚ cyclotomicField := cyclotomicField.algebra'
  let cyclotomicEquiv : C ≃ₐ[ℚ] cyclotomicField := by
    simpa [cyclotomicField, AlgHom.fieldRange_toSubalgebra embeddingC] using
      (AlgEquiv.ofInjectiveField embeddingC)
  let embeddingL : data.L →ₐ[ℚ] Omega :=
    embeddingC.comp (IsScalarTower.toAlgHom ℚ data.L C)
  let blockField : IntermediateField ℚ Omega := embeddingL.fieldRange
  letI : Algebra ℚ blockField := blockField.algebra'
  let blockEquiv : data.L ≃ₐ[ℚ] blockField := by
    simpa [blockField, AlgHom.fieldRange_toSubalgebra embeddingL] using
      (AlgEquiv.ofInjectiveField embeddingL)
  have hle : blockField ≤ cyclotomicField := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨algebraMap data.L C x, rfl⟩
  have hfinite : FiniteDimensional ℚ blockField :=
    FiniteDimensional.of_surjective
      blockEquiv.toLinearEquiv.toLinearMap blockEquiv.surjective
  letI : FiniteDimensional ℚ blockField := hfinite
  have hGalois : IsGalois ℚ blockField := IsGalois.of_algEquiv blockEquiv
  letI : IsGalois ℚ blockField := hGalois
  letI : IsCyclic Gal(data.L/ℚ) := cyclicL
  have hcyclic : IsCyclic Gal(↑blockField/ℚ) :=
    isCyclic_of_surjective (AlgEquiv.autCongr blockEquiv)
      (AlgEquiv.autCongr blockEquiv).surjective
  have hcyclotomic :
      IsCyclotomicExtension {conductor} ℚ ↑cyclotomicField :=
    IsCyclotomicExtension.equiv
      (S := {conductor}) (A := ℚ) (B := C) cyclotomicEquiv
  exact ⟨blockField, cyclotomicField, ⟨blockEquiv⟩, hle, hfinite,
    hGalois, hcyclic, conductor, hcyclotomic⟩

/-- Common-ambient finite assembly.  Pairwise coprime cyclic Galois block
fields have a cyclic compositum of product degree, and pointwise containment
in cyclotomic factors puts that compositum inside one finite cyclotomic
overfield. -/
theorem cyclic_cyclotomic_compositum
    {I : Type*}
    (blockFields cyclotomicFields : I → IntermediateField K Omega)
    (conductors : I → ℕ)
    [∀ i, FiniteDimensional K (blockFields i)]
    [∀ i, IsGalois K (blockFields i)]
    [∀ i, IsCyclic Gal(↑(blockFields i)/K)]
    (hcyclotomic : ∀ i,
      IsCyclotomicExtension {conductors i} K ↑(cyclotomicFields i))
    (s : Finset I)
    (hle : ∀ i ∈ s, blockFields i ≤ cyclotomicFields i)
    (hcoprime : Set.Pairwise (s : Set I)
      (Function.onFun Nat.Coprime fun i ↦
        Module.finrank K ↑(blockFields i))) :
    ∃ (compositum cyclotomicOverfield : IntermediateField K Omega),
      (∀ i ∈ s, blockFields i ≤ compositum) ∧
        compositum ≤ cyclotomicOverfield ∧
        FiniteDimensional K compositum ∧
        IsGalois K compositum ∧
        IsCyclic Gal(↑compositum/K) ∧
        Module.finrank K compositum =
          ∏ i ∈ s, Module.finrank K ↑(blockFields i) ∧
        ∃ conductor : ℕ,
          IsCyclotomicExtension {conductor} K ↑cyclotomicOverfield := by
  classical
  let compositum : IntermediateField K Omega := s.sup blockFields
  let cyclotomicOverfield : IntermediateField K Omega :=
    ⨆ i ∈ s, cyclotomicFields i
  have hcompositumLe : compositum ≤ cyclotomicOverfield := by
    have hleSup : s.sup blockFields ≤ s.sup cyclotomicFields :=
      finset_sup_mono blockFields cyclotomicFields s hle
    exact hleSup.trans_eq (Finset.sup_eq_iSup s cyclotomicFields)
  have hblocksLe : ∀ i ∈ s, blockFields i ≤ compositum := by
    intro i hi
    exact Finset.le_sup (f := blockFields) hi
  have hfinite : FiniteDimensional K compositum :=
    finset_sup_dimensional blockFields s (fun _ ↦ inferInstance)
  letI : FiniteDimensional K compositum := hfinite
  have hGalois : IsGalois K compositum :=
    finset_sup_galois blockFields s (fun _ ↦ inferInstance)
  letI : IsGalois K compositum := hGalois
  obtain ⟨hcyclic, hdegree⟩ :=
    finset_compositum_finrank
      blockFields s hcoprime
  obtain ⟨conductor, _hconductor, hcyclotomicOverfield⟩ :=
    finset_sup_cyclotomic
      cyclotomicFields conductors hcyclotomic s
  exact ⟨compositum, cyclotomicOverfield, hblocksLe, hcompositumLe, hfinite,
    hGalois, hcyclic, hdegree, conductor, hcyclotomicOverfield⟩

end

end Towers.CField.CBrauer
