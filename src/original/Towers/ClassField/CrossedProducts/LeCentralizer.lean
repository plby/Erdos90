import Towers.ClassField.CrossedProducts.TensorEquivLeft
import Towers.ClassField.CrossedProducts.SeparableNotField


/-!
# Chapter IV, Proposition 3.8

Every finite-dimensional central division algebra contains a maximal subfield
which is separable over its centre.
-/

namespace Towers.CField.CProduca

universe u

variable (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
  [Algebra.IsCentral k D] [Module.Finite k D]

private abbrev Centralizer (L : Subalgebra k D) :=
  Subalgebra.centralizer k (L : Set D)

omit [Algebra.IsCentral k D] [Module.Finite k D] in
private theorem le_centralizer (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) : L ≤ Centralizer k D L := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)

private def centralizerInclusion (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) :
    L →+* Centralizer k D L :=
  (Subalgebra.inclusion (le_centralizer k D L hcomm)).toRingHom

@[reducible] private noncomputable def algebraCentralizer
    (L : Subalgebra k D) [IsSimpleRing L]
    (hcomm : ∀ x y : L, x * y = y * x) :
    letI : Field L := fieldCommutativeSubalgebra k D L hcomm
    Algebra L (Centralizer k D L) := by
  letI : Field L := fieldCommutativeSubalgebra k D L hcomm
  exact (centralizerInclusion k D L hcomm).toAlgebra' fun l c => by
    apply Subtype.ext
    exact (Iff.mp (Subalgebra.mem_centralizer_iff k) c.2 l l.2)

/-- The enlargement step in Milne's proof of Proposition IV.3.8.  If a
commutative simple subalgebra is smaller than its centralizer, that centralizer
contains an element outside the subalgebra which is separable over it. -/
theorem centralizer_separable_not
    (L : Subalgebra k D) [IsSimpleRing L]
    (hcomm : ∀ x y : L, x * y = y * x)
    (hneq : L ≠ Centralizer k D L) :
    letI : Field L := fieldCommutativeSubalgebra k D L hcomm
    letI : Algebra L (Centralizer k D L) := algebraCentralizer k D L hcomm
    ∃ x : Centralizer k D L,
      x ∉ (⊥ : Subalgebra L (Centralizer k D L)) ∧ IsSeparable L x := by
  let C := Centralizer k D L
  letI : Field L := fieldCommutativeSubalgebra k D L hcomm
  letI : Algebra L C := algebraCentralizer k D L hcomm
  letI : IsScalarTower k L C := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change algebraMap k D x = algebraMap k D x
    rfl
  letI : Module.Finite k C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  letI : Module.Finite L C :=
    Module.Finite.of_restrictScalars_finite k L C
  letI : IsDomain C :=
    Function.Injective.isDomain C.val.toRingHom Subtype.val_injective
  letI : DivisionRing C := divisionRingOfFiniteDimensional L C
  letI : Algebra.IsCentral L C := by
    constructor
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    have hzdouble : (z : D) ∈ Subalgebra.centralizer k (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro c hc
      exact congrArg Subtype.val (hz ⟨c, hc⟩)
    have hzL : (z : D) ∈ L := by
      rw [centralizer_centralizer_eq k D L] at hzdouble
      exact hzdouble
    rw [Algebra.mem_bot]
    refine ⟨⟨z, hzL⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hbot : (⊥ : Subalgebra L C) ≠ ⊤ := by
    intro heq
    apply hneq
    apply le_antisymm (le_centralizer k D L hcomm)
    intro c hc
    let cC : C := ⟨c, hc⟩
    have hcBot : cC ∈ (⊥ : Subalgebra L C) := by
      rw [heq]
      exact trivial
    rw [Algebra.mem_bot] at hcBot
    obtain ⟨l, hl⟩ := hcBot
    change c ∈ L
    have hcl : c = (l : D) := by
      have h := congrArg (fun z : C => (z : D)) hl.symm
      simpa [cC] using h
    rw [hcl]
    exact l.2
  letI : Algebra.IsAlgebraic L C := Algebra.IsAlgebraic.of_finite L C
  exact JacobsonNoether.exists_separable_and_not_isCentral' hbot

/-- A separable commutative subalgebra which is smaller than its centralizer
can be enlarged to a strictly larger separable commutative subalgebra. -/
theorem larger_separable_subalgebra
    (L : Subalgebra k D) [IsSimpleRing L]
    (hcomm : ∀ x y : L, x * y = y * x)
    (hsep :
      letI : Field L := fieldCommutativeSubalgebra k D L hcomm
      Algebra.IsSeparable k L)
    (hneq : L ≠ Centralizer k D L) :
    ∃ L' : Subalgebra k D, L < L' ∧
      ∃ hL'comm : ∀ x y : L', x * y = y * x,
        letI : IsSimpleRing L' :=
          commutative_subalgebra_simple k D L' hL'comm
        letI : Field L' :=
          fieldCommutativeSubalgebra k D L' hL'comm
        Algebra.IsSeparable k L' := by
  let C := Centralizer k D L
  letI : Field L := fieldCommutativeSubalgebra k D L hcomm
  letI : Algebra L C := algebraCentralizer k D L hcomm
  letI : IsScalarTower k L C := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change algebraMap k D x = algebraMap k D x
    rfl
  letI : Module.Finite k C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  letI : Module.Finite L C :=
    Module.Finite.of_restrictScalars_finite k L C
  letI : IsDomain C :=
    Function.Injective.isDomain C.val.toRingHom Subtype.val_injective
  letI : DivisionRing C := divisionRingOfFiniteDimensional L C
  letI : Algebra.IsCentral L C := by
    constructor
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    have hzdouble : (z : D) ∈ Subalgebra.centralizer k (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro c hc
      exact congrArg Subtype.val (hz ⟨c, hc⟩)
    have hzL : (z : D) ∈ L := by
      rw [centralizer_centralizer_eq k D L] at hzdouble
      exact hzdouble
    rw [Algebra.mem_bot]
    refine ⟨⟨z, hzL⟩, ?_⟩
    apply Subtype.ext
    rfl
  obtain ⟨x, hxbot, hxsep⟩ :=
    centralizer_separable_not k D L hcomm hneq
  let S : Set D := (L : Set D) ∪ {(x : D)}
  let L' := Algebra.adjoin k S
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
    · exact Iff.mp (Subalgebra.mem_centralizer_iff k) x.2 a ha
    · exact (Iff.mp (Subalgebra.mem_centralizer_iff k) x.2 b hb).symm
    · rfl
  have hL'comm : ∀ a b : L', a * b = b * a :=
    by
      letI : IsMulCommutative L' := Algebra.isMulCommutative_adjoin k hScomm
      exact mul_comm'
  letI : IsSimpleRing L' :=
    commutative_subalgebra_simple k D L' hL'comm
  let fieldL' : Field L' :=
    fieldCommutativeSubalgebra k D L' hL'comm
  letI : Field L' := fieldL'
  letI : Semiring L' := fieldL'.toSemiring
  have hLL' : L ≤ L' := fun l hl => Algebra.subset_adjoin (Or.inl hl)
  letI : Algebra L L' :=
    (Subalgebra.inclusion hLL').toRingHom.toAlgebra
  letI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    change algebraMap k D r = algebraMap k D r
    rfl
  have hL'C : L' ≤ C := by
    apply Algebra.adjoin_le
    intro z hz
    rcases hz with hz | rfl
    · exact le_centralizer k D L hcomm hz
    · exact x.2
  let f : L' →ₐ[L] C :=
    { toFun := fun y => ⟨y, hL'C y.2⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun _ _ => by apply Subtype.ext; rfl
      map_zero' := by apply Subtype.ext; rfl
      map_add' := fun _ _ => by apply Subtype.ext; rfl
      commutes' := fun l => by
        apply Subtype.ext
        rfl }
  let xL' : L' := ⟨x, Algebra.subset_adjoin (Or.inr rfl)⟩
  have hxL'sep : IsSeparable L xL' := by
    apply (isSeparable_map_iff f f.injective).mp
    simpa [f, xL'] using hxsep
  have hgen : Algebra.adjoin L ({xL'} : Set L') = ⊤ := by
    apply top_unique
    intro y hy
    have hsubset (z : D) (hz : z ∈ L') :
        (⟨z, hz⟩ : L') ∈ Algebra.adjoin L ({xL'} : Set L') := by
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
          rcases hz with hz | rfl
          · have heq : (⟨z, Algebra.subset_adjoin (Or.inl hz)⟩ : L') =
                algebraMap L L' ⟨z, hz⟩ := by
              apply Subtype.ext
              rfl
            rw [heq]
            exact (Algebra.adjoin L {xL'}).algebraMap_mem ⟨z, hz⟩
          · exact Algebra.subset_adjoin (Set.mem_singleton xL')
      | algebraMap r =>
          have heq : (⟨algebraMap k D r, L'.algebraMap_mem r⟩ : L') =
                algebraMap L L' (algebraMap k L r) := by
            apply Subtype.ext
            rfl
          rw [heq]
          exact (Algebra.adjoin L {xL'}).algebraMap_mem (algebraMap k L r)
      | add a b ha hb ia ib =>
          exact (Algebra.adjoin L {xL'}).add_mem ia ib
      | mul a b ha hb ia ib =>
          exact (Algebra.adjoin L {xL'}).mul_mem ia ib
    exact hsubset y y.2
  letI : Algebra.IsSeparable L L' := ⟨fun y => by
    have hy : y ∈ Algebra.adjoin L ({xL'} : Set L') := by
      rw [hgen]
      exact trivial
    induction hy using Algebra.adjoin_induction with
    | mem z hz => simpa only [Set.mem_singleton_iff] using hz ▸ hxL'sep
    | algebraMap l => exact isSeparable_algebraMap l
    | add a b ha hb ia ib => exact Field.isSeparable_add ia ib
    | mul a b ha hb ia ib => exact Field.isSeparable_mul ia ib⟩
  letI : Algebra.IsSeparable k L := hsep
  letI : Algebra.IsSeparable k L' := Algebra.IsSeparable.trans k L L'
  have hxnotL : (x : D) ∉ L := by
    intro hxL
    apply hxbot
    rw [Algebra.mem_bot]
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hxmemL' : (x : D) ∈ L' := Algebra.subset_adjoin (Or.inr rfl)
  have hne : L ≠ L' := by
    intro heq
    apply hxnotL
    exact (show L' ≤ L from le_of_eq heq.symm) hxmemL'
  refine ⟨L', lt_of_le_of_ne hLL' hne, hL'comm, ?_⟩
  exact inferInstance

/-- Milne, Proposition IV.3.8: every finite-dimensional central division
algebra contains a maximal subfield which is separable over its centre. -/
theorem maximal_separable_subfield :
    ∃ (L : Subalgebra k D)
      (hcomm : ∀ x y : L, x * y = y * x),
      letI : IsSimpleRing L :=
        commutative_subalgebra_simple k D L hcomm
      letI : Field L :=
        fieldCommutativeSubalgebra k D L hcomm
      IsMaximalCommutative L ∧ Algebra.IsSeparable k L := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (L : Subalgebra k D)
      (hcomm : ∀ x y : L, x * y = y * x),
      letI : IsSimpleRing L :=
        commutative_subalgebra_simple k D L hcomm
      letI : Field L :=
        fieldCommutativeSubalgebra k D L hcomm
      Algebra.IsSeparable k L ∧ Module.finrank k L = n
  have finrank_le (L : Subalgebra k D) :
      Module.finrank k L ≤ Module.finrank k D := by
    letI : Module.Finite k L :=
      Module.Finite.of_injective L.val.toLinearMap Subtype.val_injective
    simpa using Submodule.finrank_mono
      (show L.toSubmodule ≤ (⊤ : Submodule k D) from le_top)
  let L₀ : Subalgebra k D := ⊥
  have hcomm₀ : ∀ x y : L₀, x * y = y * x := by
    intro x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    change (x : D) * (y : D) = (y : D) * (x : D)
    rw [← ha, ← hb]
    exact Algebra.commutes a (algebraMap k D b)
  letI : IsSimpleRing L₀ :=
    commutative_subalgebra_simple k D L₀ hcomm₀
  letI : Field L₀ :=
    fieldCommutativeSubalgebra k D L₀ hcomm₀
  have hsep₀ : Algebra.IsSeparable k L₀ := ⟨fun x ↦ by
    obtain ⟨a, ha⟩ := x.2
    have hx : x = algebraMap k L₀ a := by
      apply Subtype.ext
      exact ha.symm
    rw [hx]
    exact isSeparable_algebraMap a⟩
  have hP₀ : P (Module.finrank k L₀) := by
    exact ⟨L₀, hcomm₀, hsep₀, rfl⟩
  have hPmax : P (Nat.findGreatest P (Module.finrank k D)) :=
    Nat.findGreatest_spec (finrank_le L₀) hP₀
  obtain ⟨L, hcomm, hsep, hfinrank⟩ := hPmax
  letI : IsSimpleRing L :=
    commutative_subalgebra_simple k D L hcomm
  letI : Field L :=
    fieldCommutativeSubalgebra k D L hcomm
  let C := Centralizer k D L
  have hCL : C = L := by
    by_contra hCL
    have hLC : L ≠ C := fun h ↦ hCL h.symm
    obtain ⟨L', hLL', hcomm', hsep'⟩ :=
      larger_separable_subalgebra k D L hcomm hsep hLC
    letI : IsSimpleRing L' :=
      commutative_subalgebra_simple k D L' hcomm'
    letI : Field L' :=
      fieldCommutativeSubalgebra k D L' hcomm'
    have hP' : P (Module.finrank k L') :=
      ⟨L', hcomm', hsep', rfl⟩
    have hmaxbound : Module.finrank k L' ≤ Nat.findGreatest P (Module.finrank k D) :=
      Nat.le_findGreatest (finrank_le L') hP'
    have hsubmodule : L.toSubmodule < L'.toSubmodule := by
      exact hLL'
    have hdimlt : Module.finrank k L < Module.finrank k L' :=
      Submodule.finrank_lt_finrank_of_lt hsubmodule
    rw [hfinrank] at hdimlt
    exact (not_lt_of_ge hmaxbound) hdimlt
  refine ⟨L, hcomm, ?_, hsep⟩
  intro M hLM hMcomm
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ C := by
      rw [Subalgebra.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hMcomm ⟨y, hLM hy⟩ ⟨x, hx⟩)
    rw [hCL] at hxC
    exact hxC
  · exact hLM

end Towers.CField.CProduca
