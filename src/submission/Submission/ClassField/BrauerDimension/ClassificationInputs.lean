import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Submission.ClassField.BrauerDimension.EveryModuleSemisimple

/-!
# Chapter IV, Section 5, Theorem 5.5: source-facing results

This file records the fixed-product simple modules occurring in Milne's
statement and the existence and uniqueness of the multiplicity of a fixed
simple isomorphism type in a finite isotypic module.
-/

namespace Submission.CField.BDim

universe u v


/-- A module for the `i`-th factor, regarded as a module for the whole
product through the projection onto that factor. -/
def PFModule {ι : Type u} (_R : ι → Type v)
    (S : ι → Type v) (i : ι) := S i

namespace PFModule

variable {ι : Type u} (R : ι → Type v) (S : ι → Type v)
  [∀ i, Ring (R i)] [∀ i, AddCommGroup (S i)] [∀ i, Module (R i) (S i)]

instance (i : ι) : AddCommGroup (PFModule R S i) :=
  inferInstanceAs (AddCommGroup (S i))

instance (i : ι) : Module (R i) (PFModule R S i) :=
  inferInstanceAs (Module (R i) (S i))

/-- The product acts through its `i`-th projection. -/
instance (i : ι) : Module (∀ j, R j) (PFModule R S i) :=
  Module.compHom _ (Pi.evalRingHom R i)

@[simp]
theorem smul_def (i : ι) (a : ∀ j, R j)
    (x : PFModule R S i) : a • x = a i • x :=
  rfl

/-- A chosen simple module for one factor remains simple when inflated to
the whole product.  This is the first assertion of Theorem IV.5.5(a). -/
theorem isSimpleModule (i : ι) [IsSimpleModule (R i) (S i)] :
    IsSimpleModule (∀ j, R j) (PFModule R S i) := by
  letI : IsSimpleModule (R i) (PFModule R S i) :=
    inferInstanceAs (IsSimpleModule (R i) (S i))
  let e : PFModule R S i →ₛₗ[Pi.evalRingHom R i]
      PFModule R S i :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  exact (e.isSimpleModule_iff_of_bijective Function.bijective_id).2 inferInstance

/-- Chosen simple modules inflated from distinct factors are not isomorphic.
Thus the list in Theorem IV.5.5(a) has no repetitions. -/
theorem not_nonempty_ne (i j : ι) (hij : i ≠ j)
    [IsSimpleModule (R i) (S i)] [IsSimpleModule (R j) (S j)] :
    ¬ Nonempty
      (PFModule R S i ≃ₗ[∀ q, R q]
        PFModule R S j) := by
  classical
  rintro ⟨e⟩
  letI : IsSimpleModule (∀ q, R q) (PFModule R S i) :=
    isSimpleModule R S i
  letI : Nontrivial (PFModule R S i) :=
    IsSimpleModule.nontrivial (∀ q, R q) _
  obtain ⟨x, hx⟩ : ∃ x : PFModule R S i, x ≠ 0 :=
    exists_ne 0
  let a : ∀ q, R q := Pi.single i 1
  have hai : a i = 1 := by simp [a]
  have haj : a j = 0 := by simp [a, hij]
  have hmap := e.map_smul a x
  rw [smul_def, smul_def, hai, haj, one_smul, zero_smul] at hmap
  exact hx (e.injective (hmap.trans e.map_zero.symm))

end PFModule

namespace PSClass

variable {ι : Type u} [Fintype ι]
  (R : ι → Type v) [∀ i, Ring (R i)]

/-- The product element supported at the `i`-th factor. -/
noncomputable def coordinateElement (i : ι) (a : R i) : ∀ j, R j := by
  classical
  exact Pi.single i a

omit [Fintype ι] in
@[simp]
theorem coordinateElement_same (i : ι) (a : R i) :
    coordinateElement R i a i = a := by
  classical
  simp [coordinateElement]

omit [Fintype ι] in
@[simp]
theorem coordinateElement_ne {i j : ι} (h : j ≠ i) (a : R i) :
    coordinateElement R i a j = 0 := by
  classical
  simp [coordinateElement, h]

/-- The central idempotent supported at the `i`-th factor. -/
noncomputable def coordinateIdempotent (i : ι) : ∀ j, R j :=
  coordinateElement R i 1

variable (M : Type v) [AddCommGroup M] [Module (∀ i, R i) M]

/-- The endomorphism of a product-ring module induced by its `i`-th central
idempotent. -/
noncomputable def coordinateEnd (i : ι) : Module.End (∀ i, R i) M where
  toFun x := coordinateIdempotent R i • x
  map_add' x y := smul_add _ _ _
  map_smul' a x := by
    rw [smul_smul, smul_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst j
      simp [coordinateIdempotent]
    · simp [coordinateIdempotent, h]

omit [Fintype ι] in
@[simp]
theorem coordinateEnd_apply (i : ι) (x : M) :
    coordinateEnd R M i x = coordinateIdempotent R i • x :=
  rfl

omit [Fintype ι] in
theorem coordinateEnd_idempotent (i : ι) :
    coordinateEnd R M i ∘ₗ coordinateEnd R M i = coordinateEnd R M i := by
  ext x
  classical
  simp only [LinearMap.comp_apply, coordinateEnd_apply, smul_smul]
  congr 1
  ext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

omit [Fintype ι] in
theorem end_or_id [IsSimpleModule (∀ i, R i) M]
    (i : ι) : coordinateEnd R M i = 0 ∨ coordinateEnd R M i = LinearMap.id := by
  rcases (coordinateEnd R M i).bijective_or_eq_zero with hbij | hzero
  · right
    ext x
    obtain ⟨y, rfl⟩ := hbij.2 x
    exact DFunLike.congr_fun (coordinateEnd_idempotent R M i) y
  · exact Or.inl hzero

omit [Fintype ι] in
/-- On a simple module over a finite product, exactly one coordinate central
idempotent acts as the identity. -/
theorem existsUnique_coordinate [Finite ι] [IsSimpleModule (∀ i, R i) M] :
    ∃! i : ι, coordinateEnd R M i = LinearMap.id := by
  classical
  letI := Fintype.ofFinite ι
  letI : Nontrivial M := IsSimpleModule.nontrivial (∀ i, R i) M
  have hsumIdem : ∑ i, coordinateIdempotent R i = (1 : ∀ i, R i) := by
    simpa [coordinateIdempotent, coordinateElement] using
      (Finset.univ_sum_single (1 : ∀ i, R i))
  have hsumEnd : ∑ i, coordinateEnd R M i = LinearMap.id := by
    ext x
    rw [LinearMap.sum_apply]
    simp only [coordinateEnd_apply, LinearMap.id_apply]
    rw [← Finset.sum_smul, hsumIdem, one_smul]
  have hex : ∃ i, coordinateEnd R M i = LinearMap.id := by
    by_contra h
    push Not at h
    have hz (i : ι) : coordinateEnd R M i = 0 :=
      (end_or_id R M i).resolve_right (h i)
    have : (0 : Module.End (∀ i, R i) M) = LinearMap.id := by
      simpa [hz] using hsumEnd
    exact zero_ne_one this
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hzero : coordinateEnd R M i (coordinateEnd R M j x) = 0 := by
    change coordinateIdempotent R i • (coordinateIdempotent R j • x) = 0
    rw [← mul_smul]
    have hmul : coordinateIdempotent R i * coordinateIdempotent R j = 0 := by
      ext q
      by_cases hqi : q = i
      · subst q
        change coordinateElement R i 1 i * coordinateElement R j 1 i = 0
        rw [coordinateElement_same,
          coordinateElement_ne R (Ne.symm hij), mul_zero]
      · change coordinateElement R i 1 q * coordinateElement R j 1 q = 0
        rw [coordinateElement_ne R hqi, zero_mul]
    rw [hmul, zero_smul]
  have hfixi (y : M) : coordinateEnd R M i y = y := by
    simpa only [LinearMap.id_apply] using DFunLike.congr_fun hi y
  have hfixj : coordinateEnd R M j x = x := by
    simpa only [LinearMap.id_apply] using DFunLike.congr_fun hj x
  exact hx (by simpa [hfixi, hfixj] using hzero)

omit [Fintype ι] in
theorem smul_single_id
    {i : ι} (hi : coordinateEnd R M i = LinearMap.id)
    (a : ∀ i, R i) (x : M) :
    a • x = coordinateElement R i (a i) • x := by
  classical
  have hfix : coordinateIdempotent R i • x = x := by
    simpa only [coordinateEnd_apply, LinearMap.id_apply] using
      DFunLike.congr_fun hi x
  have hscalar : a * coordinateIdempotent R i = coordinateElement R i (a i) := by
    ext j
    by_cases h : j = i
    · subst j
      simp [coordinateIdempotent, coordinateElement]
    · simp [coordinateIdempotent, coordinateElement, h]
  calc
    a • x = a • (coordinateIdempotent R i • x) := congrArg (a • ·) hfix.symm
    _ = (a * coordinateIdempotent R i) • x := (mul_smul _ _ _).symm
    _ = coordinateElement R i (a i) • x := by rw [hscalar]

end PSClass

/-- An Artinian simple ring has only one simple-module isomorphism type.
This is the factorwise classification used in Theorem IV.5.5(a). -/
theorem nonempty_simple_ring
    (R : Type u) [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (S T : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup T] [Module R T] [IsSimpleModule R T] :
    Nonempty (S ≃ₗ[R] T) := by
  obtain ⟨I, ⟨eS⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R S
  obtain ⟨J, ⟨eT⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R T
  letI : IsSimpleModule R I := IsSimpleModule.congr eS.symm
  letI : IsSimpleModule R J := IsSimpleModule.congr eT.symm
  exact ⟨eS.trans
    (((IsSimpleRing.isIsotypic R R) I J).some.symm.trans eT.symm)⟩

/-- For a finite product of simple semisimple factors, the inflated chosen
factor modules give every simple module exactly once.  This is the full
classification assertion in Theorem IV.5.5(a). -/
theorem unique_simple_module
    {ι : Type u} [Finite ι]
    (R : ι → Type v) [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]
    [IsSemisimpleRing (∀ i, R i)]
    (S : ι → Type v) [∀ i, AddCommGroup (S i)]
    [∀ i, Module (R i) (S i)] [∀ i, IsSimpleModule (R i) (S i)]
    (M : Type v) [AddCommGroup M] [Module (∀ i, R i) M]
    [IsSimpleModule (∀ i, R i) M] :
    ∃! i : ι, Nonempty
      (M ≃ₗ[∀ q, R q] PFModule R S i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, hi, hique⟩ :=
    PSClass.existsUnique_coordinate R M
  letI : SMul (R i) M :=
    ⟨fun a x ↦ PSClass.coordinateElement R i a • x⟩
  letI : Module (R i) M :=
    { one_smul := fun x ↦ by
        change PSClass.coordinateElement R i 1 • x = x
        simpa only [PSClass.coordinateIdempotent,
          PSClass.coordinateEnd_apply,
          LinearMap.id_apply] using DFunLike.congr_fun hi x
      mul_smul := fun a b x ↦ by
        change PSClass.coordinateElement R i (a * b) • x =
          PSClass.coordinateElement R i a •
            (PSClass.coordinateElement R i b • x)
        rw [← mul_smul]
        congr 1
        ext j
        by_cases h : j = i
        · subst j
          simp
        · simp [h]
      smul_zero := fun a ↦ by
        change PSClass.coordinateElement R i a • (0 : M) = 0
        exact smul_zero _
      smul_add := fun a x y ↦ by
        change PSClass.coordinateElement R i a • (x + y) = _
        exact smul_add _ _ _
      add_smul := fun a b x ↦ by
        change PSClass.coordinateElement R i (a + b) • x =
          PSClass.coordinateElement R i a • x +
            PSClass.coordinateElement R i b • x
        rw [show PSClass.coordinateElement R i (a + b) =
            PSClass.coordinateElement R i a +
              PSClass.coordinateElement R i b by
          ext j
          by_cases h : j = i
          · subst j
            simp
          · simp [h], add_smul]
      zero_smul := fun x ↦ by
        change PSClass.coordinateElement R i 0 • x = 0
        rw [show PSClass.coordinateElement R i 0 = 0 by
          ext j
          by_cases h : j = i
          · subst j
            simp
          · simp [h], zero_smul] }
  letI : Nontrivial M := IsSimpleModule.nontrivial (∀ q, R q) M
  letI : IsSimpleModule (R i) M :=
    isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨inferInstance, by
      intro x hx y
      obtain ⟨a, ha⟩ :=
        (IsSimpleModule.toSpanSingleton_surjective (∀ q, R q) hx) y
      refine ⟨a i, ?_⟩
      change PSClass.coordinateElement R i (a i) • x = y
      rw [← PSClass.smul_single_id
        R M hi]
      exact ha⟩
  letI : IsSemisimpleRing (R i) :=
    RingHom.isSemisimpleRing_of_surjective (Pi.evalRingHom R i)
      RingHomSurjective.is_surjective
  letI : IsArtinianRing (R i) :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mp inferInstance
  obtain ⟨e⟩ := nonempty_simple_ring (R i) M (S i)
  let eA : M ≃ₗ[∀ q, R q] PFModule R S i :=
    { e with
      map_smul' := by
        intro a x
        change e (a • x) = a i • e x
        rw [PSClass.smul_single_id
          R M hi]
        exact e.map_smul (a i) x }
  refine ⟨i, ⟨eA⟩, ?_⟩
  intro j hj
  by_contra hji
  obtain ⟨ej⟩ := hj
  exact PFModule.not_nonempty_ne R S i j (Ne.symm hji)
    ⟨eA.symm.trans ej⟩

/-- Every module over the fixed finite product is a direct sum of copies of
the chosen factor modules.  The indexing type may be infinite. -/
theorem every_module_decomposition
    {ι : Type u} [Finite ι]
    (R : ι → Type v) [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]
    [IsSemisimpleRing (∀ i, R i)]
    (S : ι → Type v) [∀ i, AddCommGroup (S i)]
    [∀ i, Module (R i) (S i)] [∀ i, IsSimpleModule (R i) (S i)]
    (M : Type v) [AddCommGroup M] [Module (∀ i, R i) M] :
    ∃ (J : Type v) (factor : J → ι), Nonempty
      (M ≃ₗ[∀ i, R i] Π₀ j : J, PFModule R S (factor j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨T, e, _, hT⟩ :=
    IsSemisimpleModule.exists_linearEquiv_dfinsupp (∀ i, R i) M
  letI (j : T) : IsSimpleModule (∀ i, R i) j.1 := hT j
  choose factor hfactor using fun j : T ↦
    (unique_simple_module R S j.1).exists
  let eT (j : T) : j.1 ≃ₗ[∀ i, R i]
      PFModule R S (factor j) := (hfactor j).some
  exact ⟨T, factor, ⟨e.trans (DFinsupp.mapRange.linearEquiv eT)⟩⟩

/-- For a finite module the preceding decomposition has finitely many
summands, so its fibers over `i` are precisely Milne's natural-number
multiplicities `r_i`. -/
theorem module_factor_decomposition
    {ι : Type u} [Finite ι]
    (R : ι → Type v) [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]
    [IsSemisimpleRing (∀ i, R i)]
    (S : ι → Type v) [∀ i, AddCommGroup (S i)]
    [∀ i, Module (R i) (S i)] [∀ i, IsSimpleModule (R i) (S i)]
    (M : Type v) [AddCommGroup M] [Module (∀ i, R i) M]
    [Module.Finite (∀ i, R i) M] :
    ∃ (n : ℕ) (factor : Fin n → ι), Nonempty
      (M ≃ₗ[∀ i, R i]
        Π₀ j : Fin n, PFModule R S (factor j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, T, e, hT⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (∀ i, R i) M
  letI (j : Fin n) : IsSimpleModule (∀ i, R i) (T j) := hT j
  choose factor hfactor using fun j : Fin n ↦
    (unique_simple_module R S (T j)).exists
  let eT (j : Fin n) : T j ≃ₗ[∀ i, R i]
      PFModule R S (factor j) := (hfactor j).some
  exact ⟨n, factor, ⟨e.trans (DFinsupp.mapRange.linearEquiv eT)⟩⟩

/-- Milne's grouped direct sum `⊕ᵢ r_i S_i`, represented as a finite
product of finite powers. -/
def GFModule {ι : Type u} (R : ι → Type v)
    (S : ι → Type v) (r : ι → ℕ) :=
  ∀ i, Fin (r i) → PFModule R S i

namespace GFModule

variable {ι : Type u} [Fintype ι]
  (R : ι → Type v) [∀ i, Ring (R i)]
  (S : ι → Type v) [∀ i, AddCommGroup (S i)]
  [∀ i, Module (R i) (S i)]

instance (r : ι → ℕ) : AddCommGroup (GFModule R S r) :=
  inferInstanceAs (AddCommGroup
    (∀ i, Fin (r i) → PFModule R S i))

instance (r : ι → ℕ) : Module (∀ i, R i) (GFModule R S r) :=
  inferInstanceAs (Module (∀ i, R i)
    (∀ i, Fin (r i) → PFModule R S i))

omit [Fintype ι] in
private theorem coordinate_smul_single [DecidableEq ι] (r : ι → ℕ) (i : ι)
    (x : Fin (r i) → PFModule R S i) :
    PSClass.coordinateIdempotent R i •
        (LinearMap.single (∀ q, R q)
          (fun j ↦ Fin (r j) → PFModule R S j) i x) =
      LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (r j) → PFModule R S j) i x := by
  funext j y
  by_cases h : j = i
  · subst j
    simp [PSClass.coordinateIdempotent]
  · simp [LinearMap.single_apply, h,
      PSClass.coordinateIdempotent]

omit [Fintype ι] in
private theorem single_coordinate_fixed [DecidableEq ι]
    (r : ι → ℕ) (i : ι)
    (x : GFModule R S r)
    (hfix : PSClass.coordinateIdempotent R i • x = x) :
    LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (r j) → PFModule R S j) i (x i) = x := by
  funext j y
  by_cases h : j = i
  · subst j
    simp
  · have hj := congrArg (fun z : GFModule R S r ↦ z j y) hfix
    change
      (PSClass.coordinateIdempotent R i j) • x j y = x j y at hj
    rw [PSClass.coordinateIdempotent,
      PSClass.coordinateElement_ne R h, zero_smul] at hj
    simp [LinearMap.single_apply, h, hj.symm]

omit [Fintype ι] in
/-- Two grouped sums of the fixed pairwise nonisomorphic simple factor
modules are isomorphic iff every multiplicity agrees.  This is the final
uniqueness clause of Theorem IV.5.5(b). -/
theorem nonempty_linear_equiv
    [Finite ι] [∀ i, IsSimpleModule (R i) (S i)] (r s : ι → ℕ) :
    Nonempty
        (GFModule R S r ≃ₗ[∀ i, R i]
          GFModule R S s) ↔
      r = s := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · rintro ⟨e⟩
    funext i
    let incR : (Fin (r i) → PFModule R S i) →ₗ[∀ q, R q]
        GFModule R S r :=
      LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (r j) → PFModule R S j) i
    let incS : (Fin (s i) → PFModule R S i) →ₗ[∀ q, R q]
        GFModule R S s :=
      LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (s j) → PFModule R S j) i
    let projR : GFModule R S r →ₗ[∀ q, R q]
        (Fin (r i) → PFModule R S i) :=
      LinearMap.proj i
    let projS : GFModule R S s →ₗ[∀ q, R q]
        (Fin (s i) → PFModule R S i) :=
      LinearMap.proj i
    let f : (Fin (r i) → PFModule R S i) →ₗ[∀ q, R q]
        (Fin (s i) → PFModule R S i) :=
      projS.comp (e.toLinearMap.comp incR)
    let g : (Fin (s i) → PFModule R S i) →ₗ[∀ q, R q]
        (Fin (r i) → PFModule R S i) :=
      projR.comp (e.symm.toLinearMap.comp incS)
    have he_fixed (x : Fin (r i) → PFModule R S i) :
        PSClass.coordinateIdempotent R i • e (incR x) =
          e (incR x) := by
      rw [← e.map_smul]
      exact congrArg e (coordinate_smul_single R S r i x)
    have hesymm_fixed (y : Fin (s i) → PFModule R S i) :
        PSClass.coordinateIdempotent R i • e.symm (incS y) =
          e.symm (incS y) := by
      rw [← e.symm.map_smul]
      exact congrArg e.symm (coordinate_smul_single R S s i y)
    have hfg (x : Fin (r i) → PFModule R S i) : g (f x) = x := by
      change projR (e.symm (incS (projS (e (incR x))))) = x
      rw [show incS (projS (e (incR x))) = e (incR x) from
        single_coordinate_fixed R S s i _ (he_fixed x)]
      rw [e.symm_apply_apply]
      change (LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (r j) → PFModule R S j) i x) i = x
      simp
    have hgf (y : Fin (s i) → PFModule R S i) : f (g y) = y := by
      change projS (e (incR (projR (e.symm (incS y))))) = y
      rw [show incR (projR (e.symm (incS y))) = e.symm (incS y) from
        single_coordinate_fixed R S r i _ (hesymm_fixed y)]
      rw [e.apply_symm_apply]
      change (LinearMap.single (∀ q, R q)
        (fun j ↦ Fin (s j) → PFModule R S j) i y) i = y
      simp
    let ei : (Fin (r i) → PFModule R S i) ≃ₗ[∀ q, R q]
        (Fin (s i) → PFModule R S i) :=
      LinearEquiv.ofLinear f g
        (by apply LinearMap.ext; intro y; exact hgf y)
        (by apply LinearMap.ext; intro x; exact hfg x)
    letI : IsSimpleModule (∀ q, R q) (PFModule R S i) :=
      PFModule.isSimpleModule R S i
    have hlength := ei.length_eq
    simpa using hlength
  · rintro rfl
    exact ⟨LinearEquiv.refl (∀ i, R i) (GFModule R S r)⟩

end GFModule

section Multiplicity

variable (R : Type u) [Ring R]
variable (S : Type v) [AddCommGroup S] [Module R S] [IsSimpleModule R S]

/-- Two finite powers of a nonzero simple module are isomorphic exactly when
their multiplicities agree.  This is the uniqueness mechanism in
Theorem IV.5.5(b). -/
theorem nonempty_linear_fin {m n : ℕ} :
    Nonempty ((Fin m → S) ≃ₗ[R] (Fin n → S)) ↔ m = n := by
  constructor
  · rintro ⟨e⟩
    have hlength := e.length_eq
    simpa using hlength
  · rintro rfl
    exact ⟨LinearEquiv.refl R (Fin m → S)⟩

variable (M : Type v) [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

/-- A finite isotypic module has a unique finite multiplicity of its fixed
simple type. -/
theorem unique_isotypic_type
    (h : IsIsotypicOfType R M S) :
    ∃! n : ℕ, Nonempty (M ≃ₗ[R] Fin n → S) := by
  obtain ⟨n, en⟩ := h.linearEquiv_fun
  refine ⟨n, en, ?_⟩
  intro m em
  obtain ⟨en'⟩ := en
  obtain ⟨em'⟩ := em
  exact (nonempty_linear_fin R S).1
    ⟨en'.symm.trans em'⟩ |>.symm

end Multiplicity

/-- Every module over a semisimple ring is a (possibly infinite) direct sum
of simple submodules.  This is the unrestricted-module existence statement
in Theorem IV.5.5(b). -/
theorem every_simple_decomposition
    (A : Type u) [Ring A] [IsSemisimpleRing A]
    (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (T : Set (Submodule A M))
      (_ : M ≃ₗ[A] Π₀ t : T, t.1),
      ∀ t : T, IsSimpleModule A t.1 := by
  obtain ⟨T, e, _, hT⟩ :=
    IsSemisimpleModule.exists_linearEquiv_dfinsupp A M
  exact ⟨T, e, hT⟩

/-- The unconditional decomposition available for every finite module over
a semisimple ring.  Each summand is simple; the preceding theorem supplies a
unique multiplicity after summands are grouped by simple isomorphism type. -/
theorem module_simple_decomposition
    (A : Type u) [Ring A] [IsSemisimpleRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (T : Fin n → Submodule A M)
      (_ : M ≃ₗ[A] Π₀ i : Fin n, T i),
      ∀ i, IsSimpleModule A (T i) :=
  IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M

end Submission.CField.BDim
