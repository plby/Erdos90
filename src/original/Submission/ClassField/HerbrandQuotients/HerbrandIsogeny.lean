import Submission.ClassField.HerbrandQuotients.IsoRepresentations
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Universe-polymorphic Herbrand isogeny invariance for VII.3.4

This file proves the low-Tate finite-kernel/cokernel comparison required by
Lemma VII.3.4.  It uses the two-periodic cyclic Tate complex directly, so the
carrier of the integral representation and the finite cyclic group may live
in independent universes.
-/

namespace Submission.CField.HQuotie

open CategoryTheory CategoryTheory.Limits Representation
open Submission.CField.Shifting
open Submission.CField.ICohomo
open scoped TensorProduct

noncomputable section

universe u v

/-- A map between finitely generated abelian groups whose rational base
change is an isomorphism has finite kernel and cokernel. -/
private theorem base_change_bijective
    {M N : Type*} [AddCommGroup M] [instM : Module ℤ M]
    [finM : Module.Finite ℤ M]
    [AddCommGroup N] [instN : Module ℤ N] [finN : Module.Finite ℤ N]
    (f : M →ₗ[ℤ] N)
    (hf : Function.Bijective (f.baseChange ℚ)) :
    Finite (LinearMap.ker f) ∧ Finite (N ⧸ LinearMap.range f) := by
  have hinstM : instM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  have hinstN : instN = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  cases hinstM
  cases hinstN
  let iM : M →ₗ[ℤ] ℚ ⊗[ℤ] M := TensorProduct.mk ℤ ℚ M 1
  let iN : N →ₗ[ℤ] ℚ ⊗[ℤ] N := TensorProduct.mk ℤ ℚ N 1
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) iM := by
    change IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1)
    infer_instance
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) iN := by
    change IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ N 1)
    infer_instance
  constructor
  · letI : AddGroup.FG (LinearMap.ker f) :=
      (AddGroup.fg_iff_addSubgroup_fg (LinearMap.ker f).toAddSubgroup).2
        (Submodule.fg_toAddSubgroup
          (IsNoetherian.noetherian (LinearMap.ker f)))
    apply AddCommGroup.finite_of_fg_torsion
    intro x
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    have hzero : iM (x : M) = 0 := by
      apply hf.injective
      rw [map_zero]
      change (1 : ℚ) ⊗ₜ[ℤ] f (x : M) = 0
      rw [x.property]
      simp
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := nonZeroDivisors ℤ) (f := iM)
      (x₁ := (x : M)) (x₂ := 0) (by simpa using hzero)
    have hs' : (s.1 : ℤ) • (x : M) = 0 := by
      simpa only [Submonoid.smul_def, smul_zero] using hs
    refine ⟨s.1.natAbs,
      Int.natAbs_pos.2 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    apply Subtype.ext
    simpa using (natAbs_nsmul_eq_zero.2 hs')
  · letI : AddGroup.FG N := Module.Finite.iff_addGroup_fg.mp finN
    letI : AddGroup.FG (N ⧸ LinearMap.range f) :=
      AddGroup.fg_of_surjective
        (f := (LinearMap.range f).mkQ.toAddMonoidHom)
        (Submodule.mkQ_surjective _)
    apply AddCommGroup.finite_of_fg_torsion
    intro y
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine Submodule.Quotient.induction_on (p := LinearMap.range f) y ?_
    intro n
    obtain ⟨z, hz⟩ := hf.surjective (iN n)
    obtain ⟨m, hm⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) iM z
    change m.2.1 • z = iM m.1 at hm
    have hclear : iN (m.2.1 • n) = iN (f m.1) := by
      calc
        iN (m.2.1 • n) = m.2.1 • iN n := by rw [map_zsmul]
        _ = m.2.1 • f.baseChange ℚ z := by rw [hz]
        _ = f.baseChange ℚ (m.2.1 • z) := by rw [map_zsmul]
        _ = f.baseChange ℚ (iM m.1) := by rw [hm]
        _ = iN (f m.1) := by
          change f.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] m.1) =
            (1 : ℚ) ⊗ₜ[ℤ] f m.1
          rw [LinearMap.baseChange_tmul]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq
      (S := nonZeroDivisors ℤ) (f := iN) hclear
    have ht' : (t.1 : ℤ) • (m.2.1 • n) = t.1 • f m.1 := by
      simpa only [Submonoid.smul_def] using ht
    refine ⟨(t * m.2).1.natAbs,
      Int.natAbs_pos.2 (nonZeroDivisors.coe_ne_zero (t * m.2)), ?_⟩
    apply natAbs_nsmul_eq_zero.2
    change (t * m.2).1 • (LinearMap.range f).mkQ n = 0
    calc
      _ = (LinearMap.range f).mkQ ((t * m.2).1 • n) := by
        have hmap :=
          (LinearMap.range f).mkQ.toAddMonoidHom.map_zsmul (t * m.2).1 n
        exact hmap.symm
      _ = 0 := by
        apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).2
        refine ⟨t.1 • m.1, ?_⟩
        simpa [mul_smul] using ht'.symm

/-- `Module.Finite` for an abelian group does not depend on the chosen
integer-module instance. -/
private theorem moduleIntTransport
    {A : Type*} [AddCommGroup A] {m₁ m₂ : Module ℤ A}
    (h : @Module.Finite ℤ A _ _ m₁) :
    @Module.Finite ℤ A _ _ m₂ := by
  cases Subsingleton.elim m₁ m₂
  exact h

/-- Use the module structure stored by a representation throughout this
file; for `ℤ` it is propositionally, but not definitionally, the canonical
integer-module structure inferred from the additive group. -/
local instance repModule
    {G : Type u} [Group G] (A : Rep.{v, 0, u} ℤ G) : Module ℤ A := A.hV2

local instance (priority := 2000) herbrandIsogenySubmoduleModule
    {M : Type v} [AddCommGroup M] [Module ℤ M]
    (p : Submodule ℤ M) : Module ℤ p := p.module

local instance (priority := 2000) herbrandIsogenyQuotientModule
    {M : Type v} [AddCommGroup M] [Module ℤ M]
    (p : Submodule ℤ M) : Module ℤ (M ⧸ p) :=
  Submodule.Quotient.module p

local instance (priority := 2000) herbrandIsogenyCoinvariantsModule
    {G : Type u} [Monoid G] {M : Type v} [AddCommGroup M] [Module ℤ M]
    (ρ : Representation ℤ G M) : Module ℤ ρ.Coinvariants :=
  Representation.Coinvariants.instModule ρ

private def cyclicTateShape : ComplexShape Bool where
  Rel i j := j = !i
  next_eq h h' := h.trans h'.symm
  prev_eq := by
    intro i i' j h h'
    cases i <;> cases i' <;> simp_all

/-- The two-periodic complex alternating `g - 1` and the norm, with carrier
and group universes independent. -/
private noncomputable def cyclicTateComplex
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :
    HomologicalComplex (ModuleCat.{v} ℤ) cyclicTateShape := by
  letI : Module ℤ A := A.hV2
  exact {
    X _ := ModuleCat.of ℤ A
    d i j :=
      match i, j with
      | false, true =>
          ModuleCat.ofHom (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
      | true, false => ModuleCat.ofHom A.norm.hom.toLinearMap
      | _, _ => 0
    shape i j hij := by
      cases i <;> cases j <;>
        simp [cyclicTateShape] at hij ⊢
    d_comp_d' i j l hij hjl := by
      cases i <;> cases j <;> cases l <;>
        simp only [cyclicTateShape, Bool.not_false,
          Bool.not_true, Bool.false_eq_true, Bool.true_eq_false] at hij hjl ⊢
      all_goals
        ext x
        simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]
  }

/-- A representation morphism acts degreewise on the arbitrary-universe
cyclic Tate complex. -/
private noncomputable def cyclicTateMap
    {G : Type u} [CommGroup G] [Fintype G]
    {A B : Rep.{v, 0, u} ℤ G} (φ : A ⟶ B) (g : G) :
    cyclicTateComplex A g ⟶
      cyclicTateComplex B g := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  exact {
    f _ := φ.toModuleCatHom
    comm' i j hij := by
      cases i <;> cases j <;>
        simp [cyclicTateShape] at hij
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        dsimp [cyclicTateComplex, Rep.sub_hom,
          Rep.applyAsHom]
        change A at x
        change B.ρ g (φ.hom x) - φ.hom x = φ.hom (A.ρ g x - x)
        rw [map_sub, Rep.hom_comm_apply φ g x]
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        dsimp [cyclicTateComplex, Rep.norm,
          Representation.norm]
        change A at x
        change (∑ h : G, B.ρ h) (φ.hom x) =
          φ.hom ((∑ h : G, A.ρ h) x)
        rw [LinearMap.sum_apply Finset.univ (fun h : G => B.ρ h) (φ.hom x),
          LinearMap.sum_apply Finset.univ (fun h : G => A.ρ h) x]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro h _
        exact (Rep.hom_comm_apply φ h x).symm
  }

@[simp]
private theorem cyclic_tate_id
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :
    cyclicTateMap (𝟙 A) g =
      𝟙 (cyclicTateComplex A g) := by
  ext i
  rfl

@[simp]
private theorem cyclic_tate_comp
    {G : Type u} [CommGroup G] [Fintype G]
    {A B C : Rep.{v, 0, u} ℤ G}
    (φ : A ⟶ B) (ψ : B ⟶ C) (g : G) :
    cyclicTateMap (φ ≫ ψ) g =
      cyclicTateMap φ g ≫
        cyclicTateMap ψ g := by
  ext i
  rfl

@[simp]
private theorem cyclic_tate_zero
    {G : Type u} [CommGroup G] [Fintype G]
    (A B : Rep.{v, 0, u} ℤ G) (g : G) :
    cyclicTateMap (0 : A ⟶ B) g = 0 := by
  ext i
  rfl

private noncomputable def cyclicShortComplex
    {G : Type u} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep.{v, 0, u} ℤ G)) (g : G) :
    ShortComplex
      (HomologicalComplex (ModuleCat.{v} ℤ)
        cyclicTateShape) :=
  ShortComplex.mk
    (cyclicTateMap X.f g)
    (cyclicTateMap X.g g) <| by
      rw [← cyclic_tate_comp, X.zero,
        cyclic_tate_zero]

private theorem cyclic_short_exact
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G) :
    (cyclicShortComplex X g).ShortExact := by
  letI : Mono X.f := hX.mono_f
  letI : Epi X.g := hX.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  simpa [cyclicShortComplex,
    cyclicTateComplex, cyclicTateMap] using
      hX.map (forget₂ (Rep.{v, 0, u} ℤ G) (ModuleCat.{v} ℤ))

private abbrev cyclicTateEven
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :=
  (cyclicTateComplex A g).homology false

private abbrev cyclicTateOdd
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :=
  (cyclicTateComplex A g).homology true

private noncomputable abbrev cyclicOddF
    {G : Type u} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep.{v, 0, u} ℤ G)) (g : G) :
    cyclicTateOdd X.X₁ g ⟶
      cyclicTateOdd X.X₂ g :=
  HomologicalComplex.homologyMap
    (cyclicTateMap X.f g) true

private noncomputable abbrev cyclicOddG
    {G : Type u} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep.{v, 0, u} ℤ G)) (g : G) :
    cyclicTateOdd X.X₂ g ⟶
      cyclicTateOdd X.X₃ g :=
  HomologicalComplex.homologyMap
    (cyclicTateMap X.g g) true

private noncomputable abbrev cyclicEvenF
    {G : Type u} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep.{v, 0, u} ℤ G)) (g : G) :
    cyclicTateEven X.X₁ g ⟶
      cyclicTateEven X.X₂ g :=
  HomologicalComplex.homologyMap
    (cyclicTateMap X.f g) false

private noncomputable abbrev cyclicEvenG
    {G : Type u} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep.{v, 0, u} ℤ G)) (g : G) :
    cyclicTateEven X.X₂ g ⟶
      cyclicTateEven X.X₃ g :=
  HomologicalComplex.homologyMap
    (cyclicTateMap X.g g) false

private noncomputable abbrev oddEvenBoundary
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G) :
    cyclicTateOdd X.X₃ g ⟶
      cyclicTateEven X.X₁ g :=
  (cyclic_short_exact hX g).δ true false rfl

private noncomputable abbrev evenOddBoundary
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G) :
    cyclicTateEven X.X₃ g ⟶
      cyclicTateOdd X.X₁ g :=
  (cyclic_short_exact hX g).δ false true rfl

private theorem cyclic_exact_hexagon
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G) :
    Function.Exact
        (cyclicOddF X g)
        (cyclicOddG X g) ∧
      Function.Exact
        (cyclicOddG X g)
        (oddEvenBoundary hX g) ∧
      Function.Exact
        (oddEvenBoundary hX g)
        (cyclicEvenF X g) ∧
      Function.Exact
        (cyclicEvenF X g)
        (cyclicEvenG X g) ∧
      Function.Exact
        (cyclicEvenG X g)
        (evenOddBoundary hX g) ∧
      Function.Exact
        (evenOddBoundary hX g)
        (cyclicOddF X g) := by
  let hS := cyclic_short_exact hX g
  have hOddMiddle := hS.homology_exact₂ true
  have hOddRight := hS.homology_exact₃ true false rfl
  have hEvenLeft := hS.homology_exact₁ true false rfl
  have hEvenMiddle := hS.homology_exact₂ false
  have hEvenRight := hS.homology_exact₃ false true rfl
  have hOddLeft := hS.homology_exact₁ false true rfl
  exact ⟨
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hOddMiddle,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hOddRight,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hEvenLeft,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hEvenMiddle,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hEvenRight,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      hOddLeft⟩

private noncomputable def generatorSub
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) : A →ₗ[ℤ] A := by
  letI : Module ℤ A := A.hV2
  exact (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap

private noncomputable def invariantsGeneratorKer
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants ≃ₗ[ℤ] LinearMap.ker
      (generatorSub A g) := by
  let e : A.ρ.invariants ≃+
      LinearMap.ker (generatorSub A g) :=
    { toFun := fun x => ⟨x.1, by
        change A.ρ g x.1 - x.1 = 0
        rw [x.2 g, sub_self]⟩
      invFun := fun x => ⟨x.1, by
        rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg]
        exact sub_eq_zero.mp x.2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl
      map_add' := fun x y => by apply Subtype.ext; rfl }
  exact e.toIntLinearEquiv

private noncomputable abbrev evenShortComplex
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :
    ShortComplex (ModuleCat.{v} ℤ) :=
  (cyclicTateComplex A g).sc' true false true

private noncomputable abbrev oddShortComplex
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G) :
    ShortComplex (ModuleCat.{v} ℤ) :=
  (cyclicTateComplex A g).sc' false true false

private noncomputable def invariantsEvenQuotient
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    A.ρ.invariants →ₗ[ℤ]
      (LinearMap.ker
          (evenShortComplex A g).g.hom ⧸
        LinearMap.range
          (evenShortComplex A g).moduleCatToCycles) :=
  (LinearMap.range
      (evenShortComplex A g).moduleCatToCycles).mkQ.comp
    (invariantsGeneratorKer A g hg).toLinearMap

private theorem invariants_even_surjective
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Surjective (invariantsEvenQuotient A g hg) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  refine ⟨(invariantsGeneratorKer A g hg).symm y, ?_⟩
  change Submodule.mkQ _
      (invariantsGeneratorKer A g hg
        ((invariantsGeneratorKer A g hg).symm y)) =
    Submodule.mkQ _ y
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem invariants_even_ker
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (invariantsEvenQuotient A g hg) =
      LinearMap.range (normCoinvariantsInvariants A) := by
  letI : Module ℤ A := A.hV2
  ext x
  rw [LinearMap.mem_ker]
  change (Submodule.Quotient.mk
      (invariantsGeneratorKer A g hg x) = 0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Representation.Coinvariants.mk A.ρ a, ?_⟩
    apply Subtype.ext
    have ha' := congrArg Subtype.val ha
    change A.ρ.norm a = x.1
    change A.ρ.norm a = x.1 at ha'
    exact ha'
  · rintro ⟨q, hq⟩
    induction q using Representation.Coinvariants.induction_on with
    | _ a =>
      refine ⟨a, ?_⟩
      apply Subtype.ext
      have hq' := congrArg Subtype.val hq
      change A.ρ.norm a = x.1
      change A.ρ.norm a = x.1 at hq'
      exact hq'

/-- The concrete degree-zero Tate group is the even homology of the
arbitrary-universe cyclic Tate complex. -/
noncomputable def tateCyclicEven
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateZero A ≃+
      cyclicTateEven A g := by
  letI : Module ℤ A := A.hV2
  let S := evenShortComplex A g
  let e₁ : tateZero A ≃ₗ[ℤ]
      (A.ρ.invariants ⧸
        LinearMap.ker
          (invariantsEvenQuotient A g hg)) :=
    Submodule.quotEquivOfEq _ _
      (invariants_even_ker A g hg).symm
  let e₂ := LinearMap.quotKerEquivOfSurjective
    (invariantsEvenQuotient A g hg)
    (invariants_even_surjective A g hg)
  let e₃ : cyclicTateEven A g ≅
      ModuleCat.of ℤ
        (LinearMap.ker S.g.hom ⧸
          LinearMap.range S.moduleCatToCycles) :=
    (cyclicTateComplex A g).homologyIsoSc'
        true false true
        (cyclicTateShape.prev_eq'
          (show cyclicTateShape.Rel true false from rfl))
        (cyclicTateShape.next_eq'
          (show cyclicTateShape.Rel false true from rfl)) ≪≫
      S.moduleCatHomologyIso
  exact e₁.toAddEquiv.trans <|
    e₂.toAddEquiv.trans e₃.symm.toLinearEquiv.toAddEquiv

/-- Send an element killed by the raw norm to its coinvariant class in the
concrete degree-minus-one Tate group. -/
private noncomputable def normTateNeg
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) :
    LinearMap.ker A.norm.hom.toLinearMap →ₗ[ℤ]
      tateNegOne A := by
  letI : Module ℤ A := A.hV2
  exact ((Representation.Coinvariants.mk A.ρ).comp
      (LinearMap.ker A.norm.hom.toLinearMap).subtype).codRestrict
    (LinearMap.ker (normCoinvariantsInvariants A))
      fun x => by
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        exact LinearMap.mem_ker.mp x.2

private theorem tate_neg_surjective
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) :
    Function.Surjective (normTateNeg A) := by
  letI : Module ℤ A := A.hV2
  rintro ⟨q, hq⟩
  obtain ⟨x, hx⟩ := Representation.Coinvariants.mk_surjective A.ρ q
  have hnorm : A.norm.hom.toLinearMap x = 0 := by
    have h := congrArg (normCoinvariantsInvariants A) hx
    rw [LinearMap.mem_ker.mp hq] at h
    exact Subtype.ext_iff.mp h
  refine ⟨⟨x, hnorm⟩, ?_⟩
  apply Subtype.ext
  exact hx

private theorem tate_neg_ker
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    LinearMap.ker (normTateNeg A) =
      LinearMap.range
        (oddShortComplex A g).moduleCatToCycles := by
  letI : Module ℤ A := A.hV2
  ext x
  rw [LinearMap.mem_ker]
  have hleft : normTateNeg A x = 0 ↔
      Representation.Coinvariants.mk A.ρ x.1 = 0 := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  rw [hleft, Representation.Coinvariants.mk_eq_zero,
    Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
  constructor
  · rintro ⟨a, ha⟩
    change A at a
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change A.ρ g a - a = x.1
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have ha' := congrArg Subtype.val ha
    change A at a
    change A.ρ g a - a = x.1
    change A.ρ g a - a = x.1 at ha'
    exact ha'

/-- The concrete degree-minus-one Tate group is the odd homology of the
arbitrary-universe cyclic Tate complex. -/
noncomputable def tateNegOdd
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateNegOne A ≃+
      cyclicTateOdd A g := by
  letI : Module ℤ A := A.hV2
  let S := oddShortComplex A g
  let e₁ := (LinearMap.quotKerEquivOfSurjective
    (normTateNeg A)
    (tate_neg_surjective A)).symm
  let e₂ := Submodule.quotEquivOfEq
    (LinearMap.ker (normTateNeg A))
    (LinearMap.range S.moduleCatToCycles)
    (tate_neg_ker A g hg)
  let e₃ : cyclicTateOdd A g ≅
      ModuleCat.of ℤ
        (LinearMap.ker S.g.hom ⧸
          LinearMap.range S.moduleCatToCycles) :=
    (cyclicTateComplex A g).homologyIsoSc'
        false true false
        (cyclicTateShape.prev_eq'
          (show cyclicTateShape.Rel false true from rfl))
        (cyclicTateShape.next_eq'
          (show cyclicTateShape.Rel true false from rfl)) ≪≫
      S.moduleCatHomologyIso
  exact e₁.toAddEquiv.trans <|
    e₂.toAddEquiv.trans e₃.symm.toLinearEquiv.toAddEquiv

private theorem finite_exact_ends
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C] (f : A →+ B) (g : B →+ C)
    (h : Function.Exact f g) : Finite B := by
  rw [AddMonoidHom.finite_iff_finite_ker_range g]
  constructor
  · rw [h.addMonoidHom_ker_eq]
    exact Finite.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective
  · exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem cyclic_tate_middle
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)]
    [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₃ g)]
    [Finite (cyclicTateEven X.X₃ g)] :
    Finite (cyclicTateOdd X.X₂ g) ∧
      Finite (cyclicTateEven X.X₂ g) := by
  obtain ⟨h₁, _, _, h₄, _, _⟩ :=
    cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (cyclicOddF X g).hom.toAddMonoidHom
      (cyclicOddG X g).hom.toAddMonoidHom h₁,
    finite_exact_ends
      (cyclicEvenF X g).hom.toAddMonoidHom
      (cyclicEvenG X g).hom.toAddMonoidHom h₄⟩

private theorem cyclic_tate_left
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₂ g)]
    [Finite (cyclicTateEven X.X₂ g)]
    [Finite (cyclicTateOdd X.X₃ g)]
    [Finite (cyclicTateEven X.X₃ g)] :
    Finite (cyclicTateOdd X.X₁ g) ∧
      Finite (cyclicTateEven X.X₁ g) := by
  obtain ⟨_, _, h₃, _, _, h₆⟩ :=
    cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (evenOddBoundary hX g).hom.toAddMonoidHom
      (cyclicOddF X g).hom.toAddMonoidHom h₆,
    finite_exact_ends
      (oddEvenBoundary hX g).hom.toAddMonoidHom
      (cyclicEvenF X g).hom.toAddMonoidHom h₃⟩

private theorem cyclic_tate_right
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)]
    [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₂ g)]
    [Finite (cyclicTateEven X.X₂ g)] :
    Finite (cyclicTateOdd X.X₃ g) ∧
      Finite (cyclicTateEven X.X₃ g) := by
  obtain ⟨_, h₂, _, _, h₅, _⟩ :=
    cyclic_exact_hexagon hX g
  exact ⟨
    finite_exact_ends
      (cyclicOddG X g).hom.toAddMonoidHom
      (oddEvenBoundary hX g).hom.toAddMonoidHom h₂,
    finite_exact_ends
      (cyclicEvenG X g).hom.toAddMonoidHom
      (evenOddBoundary hX g).hom.toAddMonoidHom h₅⟩

private theorem cyclic_herbrand_mul
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    [Finite (cyclicTateOdd X.X₁ g)]
    [Finite (cyclicTateEven X.X₁ g)]
    [Finite (cyclicTateOdd X.X₂ g)]
    [Finite (cyclicTateEven X.X₂ g)]
    [Finite (cyclicTateOdd X.X₃ g)]
    [Finite (cyclicTateEven X.X₃ g)] :
    addCardUnit (cyclicTateEven X.X₂ g) /
        addCardUnit (cyclicTateOdd X.X₂ g) =
      (addCardUnit (cyclicTateEven X.X₁ g) /
          addCardUnit (cyclicTateOdd X.X₁ g)) *
        (addCardUnit (cyclicTateEven X.X₃ g) /
          addCardUnit (cyclicTateOdd X.X₃ g)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    cyclic_exact_hexagon hX g
  have hcard := card_exact_hexagon
    (cyclicOddF X g).hom.toAddMonoidHom
    (cyclicOddG X g).hom.toAddMonoidHom
    (oddEvenBoundary hX g).hom.toAddMonoidHom
    (cyclicEvenF X g).hom.toAddMonoidHom
    (cyclicEvenG X g).hom.toAddMonoidHom
    (evenOddBoundary hX g).hom.toAddMonoidHom
    h₁ h₂ h₃ h₄ h₅ h₆
  simp only [div_eq_mul_inv]
  calc
    addCardUnit (cyclicTateEven X.X₂ g) *
          (addCardUnit
            (cyclicTateOdd X.X₂ g))⁻¹ =
        ((addCardUnit
              (cyclicTateOdd X.X₁ g) *
            addCardUnit
              (cyclicTateOdd X.X₃ g))⁻¹ *
          (addCardUnit
                (cyclicTateOdd X.X₁ g) *
              addCardUnit
                (cyclicTateOdd X.X₃ g) *
            addCardUnit
              (cyclicTateEven X.X₂ g))) *
          (addCardUnit
            (cyclicTateOdd X.X₂ g))⁻¹ := by group
    _ = ((addCardUnit
              (cyclicTateOdd X.X₁ g) *
            addCardUnit
              (cyclicTateOdd X.X₃ g))⁻¹ *
          (addCardUnit
                (cyclicTateOdd X.X₂ g) *
              addCardUnit
                (cyclicTateEven X.X₁ g) *
            addCardUnit
              (cyclicTateEven X.X₃ g))) *
          (addCardUnit
            (cyclicTateOdd X.X₂ g))⁻¹ := by rw [hcard]
    _ = (addCardUnit
            (cyclicTateEven X.X₁ g) *
          (addCardUnit
            (cyclicTateOdd X.X₁ g))⁻¹) *
        (addCardUnit
            (cyclicTateEven X.X₃ g) *
          (addCardUnit
            (cyclicTateOdd X.X₃ g))⁻¹) := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Finiteness of low Tate groups propagates to the middle term of an
arbitrary-universe short exact sequence. -/
theorem tate_finite_middle
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (tateZero X.X₁)]
    [Finite (tateNegOne X.X₁)]
    [Finite (tateZero X.X₃)]
    [Finite (tateNegOne X.X₃)] :
    Finite (tateZero X.X₂) ∧
      Finite (tateNegOne X.X₂) := by
  let e₁₀ := tateCyclicEven X.X₁ g hg
  let e₁₁ := tateNegOdd X.X₁ g hg
  let e₂₀ := tateCyclicEven X.X₂ g hg
  let e₂₁ := tateNegOdd X.X₂ g hg
  let e₃₀ := tateCyclicEven X.X₃ g hg
  let e₃₁ := tateNegOdd X.X₃ g hg
  letI : Finite (cyclicTateEven X.X₁ g) :=
    Finite.of_equiv _ e₁₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₁ g) :=
    Finite.of_equiv _ e₁₁.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) :=
    Finite.of_equiv _ e₃₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) :=
    Finite.of_equiv _ e₃₁.toEquiv
  obtain ⟨hodd, heven⟩ := cyclic_tate_middle hX g
  letI : Finite (cyclicTateEven X.X₂ g) := heven
  letI : Finite (cyclicTateOdd X.X₂ g) := hodd
  exact ⟨Finite.of_equiv _ e₂₀.symm.toEquiv,
    Finite.of_equiv _ e₂₁.symm.toEquiv⟩

/-- Finiteness of low Tate groups propagates to the left term. -/
theorem tate_finite_left
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (tateZero X.X₂)]
    [Finite (tateNegOne X.X₂)]
    [Finite (tateZero X.X₃)]
    [Finite (tateNegOne X.X₃)] :
    Finite (tateZero X.X₁) ∧
      Finite (tateNegOne X.X₁) := by
  let e₁₀ := tateCyclicEven X.X₁ g hg
  let e₁₁ := tateNegOdd X.X₁ g hg
  let e₂₀ := tateCyclicEven X.X₂ g hg
  let e₂₁ := tateNegOdd X.X₂ g hg
  let e₃₀ := tateCyclicEven X.X₃ g hg
  let e₃₁ := tateNegOdd X.X₃ g hg
  letI : Finite (cyclicTateEven X.X₂ g) :=
    Finite.of_equiv _ e₂₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₂ g) :=
    Finite.of_equiv _ e₂₁.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) :=
    Finite.of_equiv _ e₃₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) :=
    Finite.of_equiv _ e₃₁.toEquiv
  obtain ⟨hodd, heven⟩ := cyclic_tate_left hX g
  letI : Finite (cyclicTateEven X.X₁ g) := heven
  letI : Finite (cyclicTateOdd X.X₁ g) := hodd
  exact ⟨Finite.of_equiv _ e₁₀.symm.toEquiv,
    Finite.of_equiv _ e₁₁.symm.toEquiv⟩

/-- Finiteness of low Tate groups propagates to the right term. -/
theorem tate_finite_right
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (tateZero X.X₁)]
    [Finite (tateNegOne X.X₁)]
    [Finite (tateZero X.X₂)]
    [Finite (tateNegOne X.X₂)] :
    Finite (tateZero X.X₃) ∧
      Finite (tateNegOne X.X₃) := by
  let e₁₀ := tateCyclicEven X.X₁ g hg
  let e₁₁ := tateNegOdd X.X₁ g hg
  let e₂₀ := tateCyclicEven X.X₂ g hg
  let e₂₁ := tateNegOdd X.X₂ g hg
  let e₃₀ := tateCyclicEven X.X₃ g hg
  let e₃₁ := tateNegOdd X.X₃ g hg
  letI : Finite (cyclicTateEven X.X₁ g) :=
    Finite.of_equiv _ e₁₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₁ g) :=
    Finite.of_equiv _ e₁₁.toEquiv
  letI : Finite (cyclicTateEven X.X₂ g) :=
    Finite.of_equiv _ e₂₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₂ g) :=
    Finite.of_equiv _ e₂₁.toEquiv
  obtain ⟨hodd, heven⟩ := cyclic_tate_right hX g
  letI : Finite (cyclicTateEven X.X₃ g) := heven
  letI : Finite (cyclicTateOdd X.X₃ g) := hodd
  exact ⟨Finite.of_equiv _ e₃₀.symm.toEquiv,
    Finite.of_equiv _ e₃₁.symm.toEquiv⟩

/-- Multiplicativity of the literal low-Tate cardinal ratio in an
arbitrary-universe short exact sequence. -/
theorem tate_card_ratio
    {G : Type u} [CommGroup G] [Fintype G]
    {X : ShortComplex (Rep.{v, 0, u} ℤ G)}
    (hX : X.ShortExact) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (tateZero X.X₁)]
    [Finite (tateNegOne X.X₁)]
    [Finite (tateZero X.X₂)]
    [Finite (tateNegOne X.X₂)]
    [Finite (tateZero X.X₃)]
    [Finite (tateNegOne X.X₃)] :
    (Nat.card (tateZero X.X₂) : ℚ) /
        Nat.card (tateNegOne X.X₂) =
      ((Nat.card (tateZero X.X₁) : ℚ) /
          Nat.card (tateNegOne X.X₁)) *
        ((Nat.card (tateZero X.X₃) : ℚ) /
          Nat.card (tateNegOne X.X₃)) := by
  let e₁₀ := tateCyclicEven X.X₁ g hg
  let e₁₁ := tateNegOdd X.X₁ g hg
  let e₂₀ := tateCyclicEven X.X₂ g hg
  let e₂₁ := tateNegOdd X.X₂ g hg
  let e₃₀ := tateCyclicEven X.X₃ g hg
  let e₃₁ := tateNegOdd X.X₃ g hg
  letI : Finite (cyclicTateEven X.X₁ g) :=
    Finite.of_equiv _ e₁₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₁ g) :=
    Finite.of_equiv _ e₁₁.toEquiv
  letI : Finite (cyclicTateEven X.X₂ g) :=
    Finite.of_equiv _ e₂₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₂ g) :=
    Finite.of_equiv _ e₂₁.toEquiv
  letI : Finite (cyclicTateEven X.X₃ g) :=
    Finite.of_equiv _ e₃₀.toEquiv
  letI : Finite (cyclicTateOdd X.X₃ g) :=
    Finite.of_equiv _ e₃₁.toEquiv
  have hmul := cyclic_herbrand_mul hX g
  have hmulQ := congrArg (fun z : ℚˣ => (z : ℚ)) hmul
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    card_unit_val] at hmulQ
  rw [← Nat.card_congr e₂₀.toEquiv, ← Nat.card_congr e₂₁.toEquiv,
    ← Nat.card_congr e₁₀.toEquiv, ← Nat.card_congr e₁₁.toEquiv,
    ← Nat.card_congr e₃₀.toEquiv, ← Nat.card_congr e₃₁.toEquiv] at hmulQ
  exact hmulQ

private theorem exact_coinvariants_mk
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Exact (generatorSub A g)
      (Representation.Coinvariants.mk A.ρ) := by
  intro x
  rw [Representation.Coinvariants.mk_eq_zero,
    Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg]
  rfl

private theorem invariants_card_coinvariants
    {G : Type u} [CommGroup G] [Finite G]
    (A : Rep.{v, 0, u} ℤ G) [Finite A]
    [Finite A.ρ.Coinvariants] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    addCardUnit A.ρ.invariants =
      addCardUnit A.ρ.Coinvariants := by
  letI := Fintype.ofFinite G
  letI : Module ℤ A := A.hV2
  let d := generatorSub A g
  have hKerExact : Function.Exact
      (LinearMap.ker d).subtype.toAddMonoidHom
      d.rangeRestrict.toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hdx : d x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hdx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact x.property
  have hCokerExact : Function.Exact
      d.range.subtype.toAddMonoidHom
      (Representation.Coinvariants.mk A.ρ).toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ LinearMap.range d :=
        (exact_coinvariants_mk A g hg x).mp hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (exact_coinvariants_mk A g hg x).mpr
        x.property
  have hKer := card_short_exact
    (LinearMap.ker d).subtype.toAddMonoidHom
    d.rangeRestrict.toAddMonoidHom
    (Submodule.injective_subtype _)
    hKerExact d.toAddMonoidHom.rangeRestrict_surjective
  have hCoker := card_short_exact
    d.range.subtype.toAddMonoidHom
    (Representation.Coinvariants.mk A.ρ).toAddMonoidHom
    (Submodule.injective_subtype _)
    hCokerExact (Representation.Coinvariants.mk_surjective A.ρ)
  have hInvKer : addCardUnit A.ρ.invariants =
      addCardUnit (LinearMap.ker d) := by
    apply Units.ext
    simp only [card_unit_val]
    exact_mod_cast Nat.card_congr
      (invariantsGeneratorKer A g hg).toEquiv
  rw [hInvKer]
  rw [hKer] at hCoker
  calc
    addCardUnit (LinearMap.ker d) =
        (addCardUnit (LinearMap.range d))⁻¹ *
          (addCardUnit (LinearMap.ker d) *
            addCardUnit (LinearMap.range d)) := by
      simp [mul_assoc, mul_comm]
    _ = (addCardUnit (LinearMap.range d))⁻¹ *
          (addCardUnit (LinearMap.range d) *
            addCardUnit A.ρ.Coinvariants) := by rw [hCoker]
    _ = addCardUnit A.ρ.Coinvariants := by
      simp [mul_assoc, mul_comm]

/-- Both literal low-Tate groups of a finite integral module are finite. -/
theorem tate_finite_module
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) [Finite A] :
    Finite (tateZero A) ∧
      Finite (tateNegOne A) := by
  letI : Module ℤ A := A.hV2
  letI : Finite A.ρ.Coinvariants :=
    Finite.of_surjective (Representation.Coinvariants.mk A.ρ)
      (Representation.Coinvariants.mk_surjective A.ρ)
  letI : Finite A.ρ.invariants :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact ⟨
    Finite.of_surjective
      (LinearMap.range
        (normCoinvariantsInvariants A)).mkQ
      (Submodule.mkQ_surjective _),
    Finite.of_injective Subtype.val Subtype.val_injective⟩

private theorem tate_neg_zero
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) [Finite A]
    [Finite (tateNegOne A)]
    [Finite (tateZero A)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    addCardUnit (tateNegOne A) =
      addCardUnit (tateZero A) := by
  letI : Module ℤ A := A.hV2
  letI : Finite A.ρ.Coinvariants :=
    Finite.of_surjective (Representation.Coinvariants.mk A.ρ)
      (Representation.Coinvariants.mk_surjective A.ρ)
  let n := normCoinvariantsInvariants A
  have hKerExact : Function.Exact
      (LinearMap.ker n).subtype.toAddMonoidHom
      n.rangeRestrict.toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hnorm : n x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hnorm⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact x.property
  have hCokerExact : Function.Exact
      n.range.subtype.toAddMonoidHom
      n.range.mkQ.toAddMonoidHom := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ LinearMap.range n :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr x.property
  have hKer := card_short_exact
    (LinearMap.ker n).subtype.toAddMonoidHom
    n.rangeRestrict.toAddMonoidHom
    (Submodule.injective_subtype _)
    hKerExact n.toAddMonoidHom.rangeRestrict_surjective
  have hCoker := card_short_exact
    n.range.subtype.toAddMonoidHom n.range.mkQ.toAddMonoidHom
    (Submodule.injective_subtype _)
    hCokerExact (Submodule.mkQ_surjective _)
  have hInvCoinv := invariants_card_coinvariants A g hg
  rw [hKer, hCoker] at hInvCoinv
  simpa [mul_comm] using hInvCoinv.symm

/-- A finite integral module has literal low-Tate cardinal ratio one. -/
theorem tate_ratio_module
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep.{v, 0, u} ℤ G) [Finite A]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI : Finite (tateZero A) :=
      (tate_finite_module A).1
    letI : Finite (tateNegOne A) :=
      (tate_finite_module A).2
    (Nat.card (tateZero A) : ℚ) /
      Nat.card (tateNegOne A) = 1 := by
  letI : Finite (tateZero A) :=
    (tate_finite_module A).1
  letI : Finite (tateNegOne A) :=
    (tate_finite_module A).2
  have hunit := tate_neg_zero A g hg
  have hcard : Nat.card (tateNegOne A) =
      Nat.card (tateZero A) := by
    have hval : (Nat.card (tateNegOne A) : ℚ) =
        Nat.card (tateZero A) := by
      simpa only [card_unit_val] using
        congrArg (fun z : ℚˣ => (z : ℚ)) hunit
    exact_mod_cast hval
  rw [← hcard]
  exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private noncomputable abbrev imageShortComplex
    {G : Type u} [Group G]
    {M N : Rep.{v, 0, u} ℤ G} (f : M ⟶ N) :
    ShortComplex (Rep.{v, 0, u} ℤ G) :=
  ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) <| by
    rw [← cancel_mono (Abelian.image.ι f)]
    simp

private theorem image_short_exact
    {G : Type u} [Group G]
    {M N : Rep.{v, 0, u} ℤ G} (f : M ⟶ N) :
    (imageShortComplex f).ShortExact := by
  let S : ShortComplex (Rep.{v, 0, u} ℤ G) :=
    ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f)
      (cokernel.condition _)
  have hS : S.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (kernel.ι f))
    · infer_instance
    · infer_instance
  let e : S ≅ imageShortComplex f :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (Abelian.coimageIsoImage f)
      (by simp [S, imageShortComplex])
      (by
        dsimp [S, imageShortComplex]
        rw [← cancel_mono (Abelian.image.ι f)]
        simp [Category.assoc])
  exact ShortComplex.shortExact_of_iso e hS

private noncomputable abbrev imageCokernelComplex
    {G : Type u} [Group G]
    {M N : Rep.{v, 0, u} ℤ G} (f : M ⟶ N) :
    ShortComplex (Rep.{v, 0, u} ℤ G) :=
  ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (kernel.condition _)

private theorem cokernel_short_exact
    {G : Type u} [Group G]
    {M N : Rep.{v, 0, u} ℤ G} (f : M ⟶ N) :
    (imageCokernelComplex f).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _
      (kernelIsKernel (cokernel.π f))
  · dsimp [imageCokernelComplex]
    infer_instance
  · dsimp [imageCokernelComplex]
    infer_instance

/-- The universe-polymorphic low-Tate form of Corollary II.3.9 required by
Lemma VII.3.4. -/
theorem herbrandIsogenyBridge :
    HerbrandIsogenyBridge.{u, v} := by
  intro G _ _ _ M N f hker hcoker q
  letI : Fintype G := Fintype.ofFinite G
  letI : CommGroup G := IsCyclic.commGroup
  letI : Finite ↑(kernel f : Rep.{v, 0, u} ℤ G) := hker
  letI : Finite ↑(cokernel f : Rep.{v, 0, u} ℤ G) := hcoker
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let X₁ := imageShortComplex f
  let X₂ := imageCokernelComplex f
  have hX₁ := image_short_exact f
  have hX₂ := cokernel_short_exact f
  constructor
  · intro hM
    letI : Finite (tateZero M) := hM.1
    letI : Finite (tateNegOne M) := hM.2.1
    letI : Finite (tateZero (kernel f)) :=
      (tate_finite_module (kernel f)).1
    letI : Finite (tateNegOne (kernel f)) :=
      (tate_finite_module (kernel f)).2
    obtain ⟨hI₀, hI₁⟩ := tate_finite_right hX₁ g hg
    letI : Finite (tateZero (Abelian.image f)) := hI₀
    letI : Finite (tateNegOne (Abelian.image f)) := hI₁
    letI : Finite (tateZero (cokernel f)) :=
      (tate_finite_module (cokernel f)).1
    letI : Finite (tateNegOne (cokernel f)) :=
      (tate_finite_module (cokernel f)).2
    obtain ⟨hN₀, hN₁⟩ := tate_finite_middle hX₂ g hg
    letI : Finite (tateZero N) := hN₀
    letI : Finite (tateNegOne N) := hN₁
    have hmul₁ := tate_card_ratio hX₁ g hg
    have hmul₂ := tate_card_ratio hX₂ g hg
    have hK := tate_ratio_module
      (kernel f) g hg
    have hC := tate_ratio_module
      (cokernel f) g hg
    refine ⟨inferInstance, inferInstance, ?_⟩
    calc
      (Nat.card (tateZero N) : ℚ) /
          Nat.card (tateNegOne N) =
        ((Nat.card (tateZero (Abelian.image f)) : ℚ) /
            Nat.card (tateNegOne (Abelian.image f))) *
          ((Nat.card (tateZero (cokernel f)) : ℚ) /
            Nat.card (tateNegOne (cokernel f))) := hmul₂
      _ = (Nat.card (tateZero (Abelian.image f)) : ℚ) /
          Nat.card (tateNegOne (Abelian.image f)) := by rw [hC, mul_one]
      _ = ((Nat.card (tateZero (kernel f)) : ℚ) /
            Nat.card (tateNegOne (kernel f))) *
          ((Nat.card (tateZero (Abelian.image f)) : ℚ) /
            Nat.card (tateNegOne (Abelian.image f))) := by rw [hK, one_mul]
      _ = (Nat.card (tateZero M) : ℚ) /
          Nat.card (tateNegOne M) := hmul₁.symm
      _ = q := hM.2.2
  · intro hN
    letI : Finite (tateZero N) := hN.1
    letI : Finite (tateNegOne N) := hN.2.1
    letI : Finite (tateZero (cokernel f)) :=
      (tate_finite_module (cokernel f)).1
    letI : Finite (tateNegOne (cokernel f)) :=
      (tate_finite_module (cokernel f)).2
    obtain ⟨hI₀, hI₁⟩ := tate_finite_left hX₂ g hg
    letI : Finite (tateZero (Abelian.image f)) := hI₀
    letI : Finite (tateNegOne (Abelian.image f)) := hI₁
    letI : Finite (tateZero (kernel f)) :=
      (tate_finite_module (kernel f)).1
    letI : Finite (tateNegOne (kernel f)) :=
      (tate_finite_module (kernel f)).2
    obtain ⟨hM₀, hM₁⟩ := tate_finite_middle hX₁ g hg
    letI : Finite (tateZero M) := hM₀
    letI : Finite (tateNegOne M) := hM₁
    have hmul₁ := tate_card_ratio hX₁ g hg
    have hmul₂ := tate_card_ratio hX₂ g hg
    have hK := tate_ratio_module
      (kernel f) g hg
    have hC := tate_ratio_module
      (cokernel f) g hg
    refine ⟨inferInstance, inferInstance, ?_⟩
    calc
      (Nat.card (tateZero M) : ℚ) /
          Nat.card (tateNegOne M) =
        ((Nat.card (tateZero (kernel f)) : ℚ) /
            Nat.card (tateNegOne (kernel f))) *
          ((Nat.card (tateZero (Abelian.image f)) : ℚ) /
            Nat.card (tateNegOne (Abelian.image f))) := hmul₁
      _ = (Nat.card (tateZero (Abelian.image f)) : ℚ) /
          Nat.card (tateNegOne (Abelian.image f)) := by rw [hK, one_mul]
      _ = ((Nat.card (tateZero (Abelian.image f)) : ℚ) /
            Nat.card (tateNegOne (Abelian.image f))) *
          ((Nat.card (tateZero (cokernel f)) : ℚ) /
            Nat.card (tateNegOne (cokernel f))) := by rw [hC, mul_one]
      _ = (Nat.card (tateZero N) : ℚ) /
          Nat.card (tateNegOne N) := hmul₂.symm
      _ = q := hN.2.2

/-- Conjugate an integral linear map by a group element. -/
private def conjugate
    {G : Type u} [Group G]
    (M N : Rep.{v, 0, u} ℤ G) (h : M →ₗ[ℤ] N) (g : G) : M →ₗ[ℤ] N :=
  N.ρ g⁻¹ ∘ₗ h ∘ₗ M.ρ g

/-- The sum of all conjugates of an integral linear map. This is the
denominator-free Reynolds operator used to restore equivariance. -/
private def average
    {G : Type u} [Group G] [Fintype G]
    (M N : Rep.{v, 0, u} ℤ G) (h : M →ₗ[ℤ] N) : M →ₗ[ℤ] N :=
  ∑ g : G, conjugate M N h g

/-- Averaging an integral linear map over the finite group produces a
representation morphism. -/
private theorem exists_averageHom
    {G : Type u} [Group G] [Fintype G]
    (M N : Rep.{v, 0, u} ℤ G) (h : M →ₗ[ℤ] N) :
    ∃ f : M ⟶ N, f.hom.toLinearMap = average M N h := by
  let fLin : M →ₗ[ℤ] N := average M N h
  have hcomm (g : G) (x : M) :
      fLin (M.ρ g x) = N.ρ g (fLin x) := by
    simp only [fLin, average, LinearMap.sum_apply,
      conjugate, LinearMap.comp_apply, map_sum]
    refine Fintype.sum_bijective (· * g) (Group.mulRight_bijective g)
      _ _ fun i ↦ ?_
    simp
  exact ⟨Rep.ofHom {
    toLinearMap := fLin
    isIntertwining' := fun g ↦ by
      ext x
      exact hcomm g x }, rfl⟩

/-- If an integral map becomes a nonzero scalar multiple of a rational
representation equivalence, then its averaged map is still a rational
isomorphism. -/
private theorem average_change_bijective
    {G : Type u} [Group G] [Fintype G]
    (M N : Rep.{v, 0, u} ℤ G) (h : M →ₗ[ℤ] N)
    (φ : (Representation.baseChange ℤ ℚ G M M.ρ).Equiv
      (Representation.baseChange ℤ ℚ G N N.ρ))
    (c : ℚ) (hc : c ≠ 0)
    (hbase : h.baseChange ℚ = c • φ.toLinearEquiv.toLinearMap) :
    Function.Bijective ((average M N h).baseChange ℚ) := by
  have hterm (g : G) :
      (conjugate M N h g).baseChange ℚ =
        c • φ.toLinearEquiv.toLinearMap := by
    rw [conjugate, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp, hbase]
    ext z
    change
      (N.ρ g⁻¹).baseChange ℚ
          (c • φ ((M.ρ g).baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z))) =
        c • φ ((1 : ℚ) ⊗ₜ[ℤ] z)
    rw [map_smul]
    change c • (Representation.baseChange ℤ ℚ G N N.ρ) g⁻¹
        (φ ((Representation.baseChange ℤ ℚ G M M.ρ) g
          ((1 : ℚ) ⊗ₜ[ℤ] z))) = _
    have hφ : φ ((Representation.baseChange ℤ ℚ G M M.ρ) g
          ((1 : ℚ) ⊗ₜ[ℤ] z)) =
        (Representation.baseChange ℤ ℚ G N N.ρ) g
          (φ ((1 : ℚ) ⊗ₜ[ℤ] z)) :=
      congr($(φ.toIntertwiningMap.isIntertwining' g) ((1 : ℚ) ⊗ₜ[ℤ] z))
    rw [hφ]
    change c • (Representation.baseChange ℤ ℚ G N N.ρ) g⁻¹
        ((Representation.baseChange ℤ ℚ G N N.ρ) g
          (φ ((1 : ℚ) ⊗ₜ[ℤ] z))) = _
    rw [← LinearMap.comp_apply]
    change c • (((Representation.baseChange ℤ ℚ G N N.ρ) g⁻¹ *
        (Representation.baseChange ℤ ℚ G N N.ρ) g)
          (φ ((1 : ℚ) ⊗ₜ[ℤ] z))) = _
    rw [← map_mul]
    simp
  have havg :
      (average M N h).baseChange ℚ =
        (Fintype.card G : ℚ) • (c • φ.toLinearEquiv.toLinearMap) := by
    rw [average]
    change (LinearMap.baseChangeHom ℤ ℚ M N)
        (∑ g : G, conjugate M N h g) = _
    rw [map_sum]
    change (∑ g : G, (conjugate M N h g).baseChange ℚ) = _
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [havg]
  have hcard : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hd : (Fintype.card G : ℚ) * c ≠ 0 := mul_ne_zero hcard hc
  constructor
  · intro x y hxy
    apply φ.toLinearEquiv.injective
    apply smul_right_injective _ hd
    simpa [smul_smul] using hxy
  · intro y
    refine ⟨φ.toLinearEquiv.symm
      (((Fintype.card G : ℚ) * c)⁻¹ • y), ?_⟩
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [inv_mul_cancel₀ hd, one_smul]
    change φ.toLinearEquiv (φ.toLinearEquiv.symm y) = y
    exact φ.toLinearEquiv.apply_symm_apply y

/-- The clearing-denominators step in Lemma VII.3.4. A rational equivariant
isomorphism is first lifted, after multiplying by a common denominator, to
an integral linear map. Summing its conjugates makes it equivariant; its
rational base change remains an isomorphism, so its kernel and cokernel are
finite. -/
theorem integralIsogenyBridge :
    IntegralIsogenyBridge.{u, v} := by
  intro G _ _ _ M N finM finN hMN
  letI : Fintype G := Fintype.ofFinite G
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module.Finite ℤ M := moduleIntTransport finM
  letI : Module.Finite ℤ N := moduleIntTransport finN
  obtain ⟨φ⟩ := hMN
  let iM : M →ₗ[ℤ] ℚ ⊗[ℤ] M := TensorProduct.mk ℤ ℚ M 1
  let iN : N →ₗ[ℤ] ℚ ⊗[ℤ] N := TensorProduct.mk ℤ ℚ N 1
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) iM := by
    change IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1)
    infer_instance
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) iN := by
    change IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ N 1)
    infer_instance
  let φZ : (ℚ ⊗[ℤ] M) →ₗ[ℤ] (ℚ ⊗[ℤ] N) :=
    φ.toLinearEquiv.toLinearMap.restrictScalars ℤ
  let g : M →ₗ[ℤ] ℚ ⊗[ℤ] N := φZ ∘ₗ iM
  letI : Module.FinitePresentation ℤ M :=
    Module.finitePresentation_of_finite ℤ M
  obtain ⟨h, s, hs⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (nonZeroDivisors ℤ) iN g
  have hs_ne : (s.1 : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero s
  have hbase : h.baseChange ℚ =
      (s.1 : ℚ) • φ.toLinearEquiv.toLinearMap := by
    ext x
    have hsx := LinearMap.congr_fun hs x
    change iN (h x) = s.1 • φZ (iM x) at hsx
    change (1 : ℚ) ⊗ₜ[ℤ] h x =
      (s.1 : ℚ) • φ ((1 : ℚ) ⊗ₜ[ℤ] x)
    simpa [iM, iN, φZ, g, LinearMap.comp_apply] using hsx
  obtain ⟨f, hf⟩ := exists_averageHom M N h
  have hfQ : Function.Bijective (f.hom.toLinearMap.baseChange ℚ) := by
    rw [hf]
    exact average_change_bijective
      M N h φ (s.1 : ℚ) hs_ne hbase
  obtain ⟨hker, hcoker⟩ :=
    base_change_bijective
      f.hom.toLinearMap hfQ
  let F := forget₂ (Rep.{v, 0, u} ℤ G) (ModuleCat.{v} ℤ)
  let eK :=
    PreservesKernel.iso F f ≪≫ ModuleCat.kernelIsoKer (F.map f)
  let eC :=
    PreservesCokernel.iso F f ≪≫
      ModuleCat.cokernelIsoRangeQuotient (F.map f)
  refine ⟨f, ?_, ?_⟩
  · letI : Finite (LinearMap.ker f.hom.toLinearMap) := hker
    exact Finite.of_equiv _ eK.toLinearEquiv.symm.toEquiv
  · letI : Finite (N ⧸ LinearMap.range f.hom.toLinearMap) := hcoker
    exact Finite.of_equiv _ eC.toLinearEquiv.symm.toEquiv

/-- Lemma VII.3.4 follows from the now-unconditional integral isogeny and
Herbrand-isogeny comparisons. -/
theorem herbrandIsogenyStatement : (∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
      letI : Fintype G := Fintype.ofFinite G
      letI : CommGroup G := IsCyclic.commGroup
      ∀ (M N : Rep.{v, 0, u} ℤ G)
        [@Module.Finite ℤ (↑M) Int.instSemiring M.hV1.toAddCommMonoid
          (AddCommGroup.toIntModule ↑M)]
        [@Module.Finite ℤ (↑N) Int.instSemiring N.hV1.toAddCommMonoid
          (AddCommGroup.toIntModule ↑N)],
        RationallyIsomorphicRepresentations M N →
        ((DefinedHerbrandQuotient M →
            ∃ q : ℚ,
              HerbrandQuotientValue M q ∧
                HerbrandQuotientValue N q) ∧
          (DefinedHerbrandQuotient N →
            ∃ q : ℚ,
              HerbrandQuotientValue M q ∧
                HerbrandQuotientValue N q))) := by
  simpa only using
    (rationally_representations_isogeny integralIsogenyBridge
      herbrandIsogenyBridge)

/-- Compatibility endpoint retained for consumers that supply their own
integral isogeny construction. -/
theorem herbrand_isogeny_integral
    (hintegral : IntegralIsogenyBridge.{u, v}) :
    (∀ (G : Type u) [Group G] [Finite G] [IsCyclic G],
          letI : Fintype G := Fintype.ofFinite G
          letI : CommGroup G := IsCyclic.commGroup
          ∀ (M N : Rep.{v, 0, u} ℤ G)
            [@Module.Finite ℤ (↑M) Int.instSemiring M.hV1.toAddCommMonoid
              (AddCommGroup.toIntModule ↑M)]
            [@Module.Finite ℤ (↑N) Int.instSemiring N.hV1.toAddCommMonoid
              (AddCommGroup.toIntModule ↑N)],
            RationallyIsomorphicRepresentations M N →
            ((DefinedHerbrandQuotient M →
                ∃ q : ℚ,
                  HerbrandQuotientValue M q ∧
                    HerbrandQuotientValue N q) ∧
              (DefinedHerbrandQuotient N →
                ∃ q : ℚ,
                  HerbrandQuotientValue M q ∧
                    HerbrandQuotientValue N q))) := by
  simpa only using
    (rationally_representations_isogeny hintegral
      herbrandIsogenyBridge)

end

end Submission.CField.HQuotie
