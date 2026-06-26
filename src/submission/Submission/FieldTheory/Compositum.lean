import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

section CompositumDegreeFormula

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

/-- The compositum of a finite family of intermediate fields inside a common ambient field. -/
def compositum {m : ℕ} (L : Fin m → IntermediateField ℚ Ω) (s : Finset (Fin m)) :
    IntermediateField ℚ Ω :=
  ⨆ i ∈ s, L i

/-- The compositum of the fields `L j` with index strictly smaller than `i`. -/
def compositumBefore {m : ℕ} (L : Fin m → IntermediateField ℚ Ω) (i : Fin m) :
    IntermediateField ℚ Ω :=
  compositum L (Finset.univ.filter fun j => j < i)


/--
Lemma 2 from `CompositumDegreeFormula.tex`.

This isolates the field-theoretic core of the disjoint-ramification argument in a form that is
easy to reuse in the tower construction: each `L i` has prime degree, is Galois over `ℚ`, and has
a rational prime that ramifies in `L i` but not in the earlier compositum.
-/
theorem disjoint_before_ramification
    {m : ℕ}
    (L : Fin m → IntermediateField ℚ Ω)
    [∀ i, FiniteDimensional ℚ ↥(L i)]
    (RamifiedAt : ℕ → IntermediateField ℚ Ω → Prop)
    (hprimeDegree : ∀ i, Nat.Prime (Module.finrank ℚ ↥(L i)))
    (hgal : ∀ i, @IsGalois ℚ _ ↥(L i) _ (L i).algebra')
    (_hscalar : ∀ i, IsScalarTower ℚ ↥(L i) Ω)
    (hram : ∀ i, ∃ p : ℕ, RamifiedAt p (L i) ∧ ¬ RamifiedAt p (compositumBefore L i))
    (hramified_mono : ∀ {p : ℕ} {K M : IntermediateField ℚ Ω},
      K ≤ M → RamifiedAt p K → RamifiedAt p M) :
    ∀ i, (compositumBefore L i).LinearDisjoint (L i) := by
  intro i
  let M : IntermediateField ℚ Ω := compositumBefore L i
  letI : FiniteDimensional ℚ ↥M := by
    classical
    dsimp [M, compositumBefore, compositum]
    exact IntermediateField.finiteDimensional_iSup_of_finset'
      (t := L) (s := Finset.univ.filter fun j => j < i) (fun j _ => inferInstance)
  letI : Algebra ℚ ↥(L i) := (L i).algebra'
  letI : IsGalois ℚ ↥(L i) := hgal i
  letI : IsScalarTower ℚ ↥(L i) Ω := _hscalar i
  have h_inf_bot : (L i) ⊓ M = ⊥ := by
    by_contra h_inf_bot
    obtain ⟨p, hp_ramified, hp_not_ramified⟩ := hram i
    have h_inf_le_left : (L i) ⊓ M ≤ L i := inf_le_left
    let E := ((L i) ⊓ M).restrict h_inf_le_left
    have hE_top : E = ⊤ := by
      letI : Algebra ℚ ↥(L i) := (L i).algebra'
      have hprimeDegree_i : Nat.Prime (Module.finrank ℚ ↥(L i)) := by
        simpa using hprimeDegree i
      have hSimple :
          IsSimpleOrder (IntermediateField ℚ ↥(L i)) :=
        IntermediateField.isSimpleOrder_of_finrank_prime ℚ ↥(L i) hprimeDegree_i
      have hE_bot_or_top :
          E = ⊥ ∨ E = ⊤ :=
        hSimple.eq_bot_or_eq_top E
      refine hE_bot_or_top.resolve_left ?_
      intro hE_bot
      apply h_inf_bot
      calc
        (L i) ⊓ M = IntermediateField.lift E := by
          symm
          simp [E]
        _ = ⊥ := by
          rw [hE_bot]
          simp
    have h_inf_eq_left : (L i) ⊓ M = L i := by
      calc
        (L i) ⊓ M = IntermediateField.lift E := by
          symm
          simp [E]
        _ = L i := by
          rw [hE_top]
          simp
    have hLi_le_M : L i ≤ M := by
      rw [← h_inf_eq_left]
      exact inf_le_right
    have hM_ramified : RamifiedAt p M := hramified_mono hLi_le_M hp_ramified
    exact hp_not_ramified (by simpa [M] using hM_ramified)
  have hld :
      @IntermediateField.LinearDisjoint ℚ Ω _ _ _ (L i) ↥M _ M.algebra' inferInstance
        (IntermediateField.isScalarTower_mid' (K := ℚ) (S := M) (L := Ω)) := by
    exact @IntermediateField.LinearDisjoint.of_inf_eq_bot
      ℚ Ω _ _ _ (L i) M inferInstance (by infer_instance) (by infer_instance) h_inf_bot
  simpa [M] using hld.symm

end CompositumDegreeFormula

end Submission
