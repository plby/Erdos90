import Towers.ClassField.CohomologyOps.Associativity
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace Towers.CField.COps.CPFuncto

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Towers.CField.COps.CPBuild
open scoped MonoidalCategory IsMulCommutative

variable {G : Type} [Group G]

/-- Regard an additive map between integer module objects as a linear map,
using the module structures stored in the objects. -/
noncomputable def moduleCatLinear
    (A B : ModuleCat ℤ) (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' z a := by
    change f (A.isModule.smul z a) = B.isModule.smul z (f a)
    rw [int_smul_eq_zsmul A.isModule, int_smul_eq_zsmul B.isModule]
    exact f.map_zsmul z a

noncomputable def braidingShortComplex
    (N : Rep ℤ G) (X : ShortComplex (Rep ℤ G)) :
    leftShortComplex N X ⟶ tensorShortComplex X N where
  τ₁ := (β_ N X.X₁).hom
  τ₂ := (β_ N X.X₂).hom
  τ₃ := (β_ N X.X₃).hom
  comm₁₂ := by simp
  comm₂₃ := by simp

theorem braiding_delta_naturality
    (N : Rep ℤ G) (X : ShortComplex (Rep ℤ G))
    (hNX : (leftShortComplex N X).ShortExact)
    (hXN : (tensorShortComplex X N).ShortExact) (n : ℕ) :
    groupCohomology.δ hNX n (n + 1) rfl ≫
        groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom (n + 1) =
      groupCohomology.map (MonoidHom.id G) (β_ N X.X₃).hom n ≫
        groupCohomology.δ hXN n (n + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map
      (braidingShortComplex N X))
    (groupCohomology.map_cochainsFunctor_shortExact hNX)
    (groupCohomology.map_cochainsFunctor_shortExact hXN) n (n + 1) rfl

noncomputable def braidingReverseShort
    (N : Rep ℤ G) (X : ShortComplex (Rep ℤ G)) :
    tensorShortComplex X N ⟶ leftShortComplex N X where
  τ₁ := (β_ X.X₁ N).hom
  τ₂ := (β_ X.X₂ N).hom
  τ₃ := (β_ X.X₃ N).hom
  comm₁₂ := by simp
  comm₂₃ := by simp

theorem braiding_reverse_naturality
    (N : Rep ℤ G) (X : ShortComplex (Rep ℤ G))
    (hXN : (tensorShortComplex X N).ShortExact)
    (hNX : (leftShortComplex N X).ShortExact) (n : ℕ) :
    groupCohomology.δ hXN n (n + 1) rfl ≫
        groupCohomology.map (MonoidHom.id G) (β_ X.X₁ N).hom (n + 1) =
      groupCohomology.map (MonoidHom.id G) (β_ X.X₃ N).hom n ≫
        groupCohomology.δ hNX n (n + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map
      (braidingReverseShort N X))
    (groupCohomology.map_cochainsFunctor_shortExact hXN)
    (groupCohomology.map_cochainsFunctor_shortExact hNX) n (n + 1) rfl

noncomputable def braidingShortIso
    (N : Rep ℤ G) (X : ShortComplex (Rep ℤ G)) :
    leftShortComplex N X ≅ tensorShortComplex X N :=
  X.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight N)

theorem delta_cohomologyCast
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (m n : ℕ) (h : m = n) (x : groupCohomology X.X₃ m) :
    groupCohomology.δ hX n (n + 1) rfl
        (cohomologyCast X.X₃ h x) =
      cohomologyCast X.X₁ (congrArg (· + 1) h)
        (groupCohomology.δ hX m (m + 1) rfl x) := by
  subst h
  rfl

theorem map_cohomologyCast
    {A B : Rep ℤ G} (f : A ⟶ B)
    (m n : ℕ) (h : m = n) (x : groupCohomology A m) :
    groupCohomology.map (MonoidHom.id G) f n
        (cohomologyCast A h x) =
      cohomologyCast B h
        (groupCohomology.map (MonoidHom.id G) f m x) := by
  subst h
  rfl

theorem cohomologyCast_trans (A : Rep ℤ G) {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) (x : groupCohomology A a) :
    cohomologyCast A h₂ (cohomologyCast A h₁ x) =
      cohomologyCast A (h₁.trans h₂) x := by
  subst h₁
  subst h₂
  rfl

theorem cohomologyCast_eq (A : Rep ℤ G) {a b : ℕ}
    (h₁ h₂ : a = b) (x : groupCohomology A a) :
    cohomologyCast A h₁ x = cohomologyCast A h₂ x := by
  subst h₁
  rfl

theorem module_cat_zsmul {A B : ModuleCat ℤ} (f : A ⟶ B)
    (z : ℤ) (x : A) : f (z • x) = z • f x := by
  exact map_zsmul f.hom z x

theorem cat_stored_smul {A B : ModuleCat ℤ} (f : A ⟶ B)
    (z : ℤ) (x : A) :
    f (A.isModule.smul z x) = B.isModule.smul z (f x) := by
  exact f.hom.map_smul z x

/-- Apply the tensor braiding, reassociate the cohomological degree, and
multiply by the Koszul sign. -/
noncomputable def swappedCupOutput (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology (N ⊗ M : Rep ℤ G) (s + r) →ₗ[ℤ]
      groupCohomology (M ⊗ N : Rep ℤ G) (r + s) :=
  (-1 : ℤ) ^ (r * s) •
    ((cohomologyCast (M ⊗ N : Rep ℤ G) (Nat.add_comm s r)).hom.comp
      (groupCohomology.map (MonoidHom.id G) (β_ N M).hom (s + r)).hom)

@[simp]
theorem swapped_cup_output (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology (N ⊗ M : Rep ℤ G) (s + r)) :
    swappedCupOutput M N r s x =
      (-1 : ℤ) ^ (r * s) •
        cohomologyCast (M ⊗ N : Rep ℤ G) (Nat.add_comm s r)
          (groupCohomology.map (MonoidHom.id G) (β_ N M).hom (s + r) x) :=
  rfl

noncomputable def swappedRightAdd (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) :
    groupCohomology N s →+ groupCohomology (M ⊗ N : Rep ℤ G) (r + s) where
  toFun b := swappedCupOutput M N r s (cupCohomology N M s r b a)
  map_zero' := by
    rw [(cupCohomology N M s r).map_zero, LinearMap.zero_apply]
    exact (swappedCupOutput M N r s).map_zero
  map_add' b₁ b₂ := by
    rw [(cupCohomology N M s r).map_add]
    simp only [LinearMap.add_apply]
    exact (swappedCupOutput M N r s).map_add _ _

noncomputable def swappedCupRight (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) :
    groupCohomology N s →ₗ[ℤ] groupCohomology (M ⊗ N : Rep ℤ G) (r + s) :=
  moduleCatLinear (groupCohomology N s)
    (groupCohomology (M ⊗ N : Rep ℤ G) (r + s))
    (swappedRightAdd M N r s a)

noncomputable def swappedCupAdd (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology M r →+
      (groupCohomology N s →ₗ[ℤ] groupCohomology (M ⊗ N : Rep ℤ G) (r + s)) where
  toFun := swappedCupRight M N r s
  map_zero' := by
    apply LinearMap.ext
    intro b
    change swappedCupOutput M N r s (cupCohomology N M s r b 0) = 0
    rw [(cupCohomology N M s r b).map_zero]
    exact (swappedCupOutput M N r s).map_zero
  map_add' a₁ a₂ := by
    apply LinearMap.ext
    intro b
    change swappedCupOutput M N r s (cupCohomology N M s r b (a₁ + a₂)) = _
    rw [(cupCohomology N M s r b).map_add]
    exact (swappedCupOutput M N r s).map_add _ _

noncomputable def swappedCupFamily : CPFam (G := G) :=
  fun M N r s ↦
    { toFun := swappedCupAdd M N r s
      map_add' := (swappedCupAdd M N r s).map_add
      map_smul' := by
        intro z a
        change (swappedCupAdd M N r s)
            ((groupCohomology M r).isModule.smul z a) =
          z • (swappedCupAdd M N r s) a
        rw [int_smul_eq_zsmul (groupCohomology M r).isModule]
        exact (swappedCupAdd M N r s).map_zsmul z a }

@[simp]
theorem swapped_cup_family
    (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) (b : groupCohomology N s) :
    swappedCupFamily M N r s a b =
      swappedCupOutput M N r s (cupCohomology N M s r b a) :=
  rfl

theorem braiding_tensorElement (M N : Rep ℤ G) (m : M) (n : N) :
    (β_ M N).hom (tensorElement M N m n) = tensorElement N M n m := by
  letI := M.hV2
  letI := N.hV2
  change (TensorProduct.comm ℤ M N) (m ⊗ₜ[ℤ] n) = n ⊗ₜ[ℤ] m
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem cup_cocycle_braiding (M N : Rep ℤ G)
    (a : groupCohomology.cocycles M 0)
    (b : groupCohomology.cocycles N 0) :
    groupCohomology.cocyclesMap (MonoidHom.id G) (β_ N M).hom 0
        (cupCocycle N M 0 0 b a) =
      cupCocycle M N 0 0 a b := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) 0)).1 inferInstance
  rw [i_cocycles_id]
  change (fun g => (β_ N M).hom
      (groupCohomology.iCocycles (N ⊗ M : Rep ℤ G) 0
        (cupCocycle N M 0 0 b a) g)) =
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) 0
      (cupCocycle M N 0 0 a b)
  have hleft := i_cup_cocycle N M 0 0 b a
  have hleft' :
      groupCohomology.iCocycles
          (Rep.instMonoidalCategory.toMonoidalCategoryStruct.1 N M) 0
          (cupCocycle N M 0 0 b a) =
        cochainCup N M 0 0
          (groupCohomology.iCocycles N 0 b)
          (groupCohomology.iCocycles M 0 a) := by
    convert hleft using 1
  have hright := i_cup_cocycle M N 0 0 a b
  rw [hleft', hright]
  funext q
  rw [cochain_cup_zero, cochain_cup_zero,
    braiding_tensorElement]

theorem swapped_cup_zero :
    DegreeZeroNormalized (swappedCupFamily (G := G)) := by
  intro M N a b
  rw [swapped_cup_family, swapped_cup_output]
  simp only [Nat.zero_mul, pow_zero, one_smul]
  rw [cupCohomology_π]
  have hmap := congrArg (fun q => q (cupCocycle N M 0 0 b a))
    (groupCohomology.π_map
      (f := MonoidHom.id G) (φ := (β_ N M).hom) 0)
  simp only [ConcreteCategory.comp_apply] at hmap
  have hc := congrArg (groupCohomology.π (M ⊗ N : Rep ℤ G) 0)
    (cup_cocycle_braiding M N a b)
  calc
    cohomologyCast (M ⊗ N : Rep ℤ G) (Nat.add_comm 0 0)
        (groupCohomology.map (MonoidHom.id G) (β_ N M).hom 0
          (groupCohomology.π (N ⊗ M : Rep ℤ G) 0
            (cupCocycle N M 0 0 b a))) =
      groupCohomology.map (MonoidHom.id G) (β_ N M).hom 0
          (groupCohomology.π (N ⊗ M : Rep ℤ G) 0
            (cupCocycle N M 0 0 b a)) := by rfl
    _ = groupCohomology.π (M ⊗ N : Rep ℤ G) 0
        (groupCohomology.cocyclesMap (MonoidHom.id G) (β_ N M).hom 0
          (cupCocycle N M 0 0 b a)) := by
            convert hmap using 1
    _ = groupCohomology.π (M ⊗ N : Rep ℤ G) 0
        (cupCocycle M N 0 0 a b) := hc

theorem swapped_family_connecting :
    CompatibleLeftConnecting (swappedCupFamily (G := G)) := by
  intro X hX N hXN i s a b
  rw [swapped_cup_family, swapped_cup_output,
    swapped_cup_family, swapped_cup_output]
  let hNX : (leftShortComplex N X).ShortExact :=
    ShortComplex.shortExact_of_iso (braidingShortIso N X).symm hXN
  let u := cupCohomology N X.X₃ s i b a
  let d := groupCohomology.δ hNX (s + i) ((s + i) + 1) rfl u
  let v := cupCohomology N X.X₁ s (i + 1) b
    (groupCohomology.δ hX i (i + 1) rfl a)
  let hcomm : s + i = i + s := Nat.add_comm s i
  let hinner : s + (i + 1) = (i + 1) + s := Nat.add_comm s (i + 1)
  let houter : (i + 1) + s = (i + s) + 1 := by omega
  let hcommon : (s + i) + 1 = (i + s) + 1 := congrArg (· + 1) hcomm
  have hcup : v = (-1 : ℤ) ^ s • d := by
    exact cup_cohomology_delta N hX hNX s i b a
  have hβm := braiding_delta_naturality N X hNX hXN (s + i)
  have hβ := congrArg (fun q => q u) hβm
  simp only [ConcreteCategory.comp_apply] at hβ
  have hβ' :
      groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom ((s + i) + 1) d =
        groupCohomology.δ hXN (s + i) ((s + i) + 1) rfl
          (groupCohomology.map (MonoidHom.id G) (β_ N X.X₃).hom (s + i) u) := by
    exact hβ
  have hdc (x : groupCohomology (X.X₃ ⊗ N : Rep ℤ G) (s + i)) :
      groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
          (cohomologyCast (X.X₃ ⊗ N : Rep ℤ G) hcomm x) =
        cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hcommon
          (groupCohomology.δ hXN (s + i) ((s + i) + 1) rfl x) := by
    convert delta_cohomologyCast hXN (s + i) (i + s) hcomm x using 1
  have hleft :
      groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
          ((-1 : ℤ) ^ (i * s) •
            cohomologyCast (X.X₃ ⊗ N : Rep ℤ G) hcomm
              (groupCohomology.map (MonoidHom.id G) (β_ N X.X₃).hom
                (s + i) u)) =
        (-1 : ℤ) ^ (i * s) •
          cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hcommon
            (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
              ((s + i) + 1) d) := by
    let x₀ := cohomologyCast (X.X₃ ⊗ N : Rep ℤ G) hcomm
      (groupCohomology.map (MonoidHom.id G) (β_ N X.X₃).hom (s + i) u)
    have hz :
        groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
            ((-1 : ℤ) ^ (i * s) • x₀) =
          (-1 : ℤ) ^ (i * s) •
            groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl x₀ := by
      exact module_cat_zsmul
        (groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl)
        ((-1 : ℤ) ^ (i * s)) x₀
    change groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
        ((-1 : ℤ) ^ (i * s) • x₀) = _
    rw [hz]
    rw [hdc, ← hβ']
    rfl
  have hsign :
      (-1 : ℤ) ^ ((i + 1) * s) * (-1 : ℤ) ^ s =
        (-1 : ℤ) ^ (i * s) := by
    rw [Nat.add_mul, one_mul, pow_add, mul_assoc]
    rw [← mul_pow]
    simp
  have hright :
      cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter
          ((-1 : ℤ) ^ ((i + 1) * s) •
            cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner
              (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
                (s + (i + 1)) v)) =
        (-1 : ℤ) ^ (i * s) •
          cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hcommon
            (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
              ((s + i) + 1) d) := by
    let md := groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
      (s + (i + 1)) d
    let ci := cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner md
    have houtT :
        cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter
            ((-1 : ℤ) ^ ((i + 1) * s) •
              cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner
                (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
                  (s + (i + 1)) v)) =
          (-1 : ℤ) ^ ((i + 1) * s) •
            cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter
              (cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner
                (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
                  (s + (i + 1)) v)) := by
      exact module_cat_zsmul
        (cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter) _ _
    have hv :
        groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
            (s + (i + 1)) v =
          (-1 : ℤ) ^ s • md := by
      rw [hcup]
      exact module_cat_zsmul
        (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
          (s + (i + 1))) _ _
    have hi :
        cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner
            ((-1 : ℤ) ^ s • md) =
          (-1 : ℤ) ^ s • ci := by
      exact module_cat_zsmul
        (cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hinner) _ _
    have ho :
        cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter
            ((-1 : ℤ) ^ s • ci) =
          (-1 : ℤ) ^ s •
            cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter ci := by
      exact module_cat_zsmul
        (cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) houter) _ _
    rw [houtT, hv, hi, ho]
    rw [cohomologyCast_trans]
    have hc := cohomologyCast_eq (X.X₁ ⊗ N : Rep ℤ G)
      (hinner.trans houter) hcommon
      (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
        ((s + i) + 1) d)
    rw [smul_smul, hsign]
    change (-1 : ℤ) ^ (i * s) •
        cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) (hinner.trans houter)
          (groupCohomology.map (MonoidHom.id G) (β_ N X.X₁).hom
            ((s + i) + 1) d) = _
    exact congrArg (fun z => (-1 : ℤ) ^ (i * s) • z) hc
  exact hleft.trans hright.symm

theorem swapped_cup_connecting :
    CompatibleRightConnecting (swappedCupFamily (G := G)) := by
  intro M X hX hMX r s a b
  rw [swapped_cup_family, swapped_cup_output,
    swapped_cup_family, swapped_cup_output]
  let hXM : (tensorShortComplex X M).ShortExact :=
    ShortComplex.shortExact_of_iso (braidingShortIso M X) hMX
  let u := cupCohomology X.X₃ M s r b a
  let d := groupCohomology.δ hXM (s + r) ((s + r) + 1) rfl u
  let v := cupCohomology X.X₁ M (s + 1) r
    (groupCohomology.δ hX s (s + 1) rfl b) a
  let hsource : s + r = r + s := Nat.add_comm s r
  let hcommon : (s + r) + 1 = (r + s) + 1 := congrArg (· + 1) hsource
  let hconn : (s + 1) + r = (s + r) + 1 := by omega
  let htarget : (s + 1) + r = r + (s + 1) := Nat.add_comm (s + 1) r
  have hcup : d = cohomologyCast (X.X₁ ⊗ M : Rep ℤ G) hconn v := by
    exact connecting_cup X hX M hXM s r b a
  have hβm := braiding_reverse_naturality M X hXM hMX (s + r)
  have hβ := congrArg (fun q => q u) hβm
  simp only [ConcreteCategory.comp_apply] at hβ
  have hβ' :
      groupCohomology.map (MonoidHom.id G) (β_ X.X₁ M).hom ((s + r) + 1) d =
        groupCohomology.δ hMX (s + r) ((s + r) + 1) rfl
          (groupCohomology.map (MonoidHom.id G) (β_ X.X₃ M).hom (s + r) u) := by
    exact hβ
  let mv := groupCohomology.map (MonoidHom.id G) (β_ X.X₁ M).hom
    ((s + 1) + r) v
  let md := groupCohomology.map (MonoidHom.id G) (β_ X.X₁ M).hom
    ((s + r) + 1) d
  have hmd : md = cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) hconn mv := by
    dsimp only [md, mv]
    rw [hcup]
    exact map_cohomologyCast (β_ X.X₁ M).hom
      ((s + 1) + r) ((s + r) + 1) hconn v
  have hcpath :
      cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) htarget mv =
        cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) hcommon md := by
    rw [hmd, cohomologyCast_trans]
  have hleft :
      (-1 : ℤ) ^ (r * (s + 1)) •
          cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) htarget mv =
        (-1 : ℤ) ^ (r * (s + 1)) •
          cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) hcommon md := by
    exact congrArg (fun z => (-1 : ℤ) ^ (r * (s + 1)) • z) hcpath
  have hdc (x : groupCohomology (M ⊗ X.X₃ : Rep ℤ G) (s + r)) :
      groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
          (cohomologyCast (M ⊗ X.X₃ : Rep ℤ G) hsource x) =
        cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) hcommon
          (groupCohomology.δ hMX (s + r) ((s + r) + 1) rfl x) := by
    convert delta_cohomologyCast hMX (s + r) (r + s) hsource x using 1
  let x₀ := cohomologyCast (M ⊗ X.X₃ : Rep ℤ G) hsource
    (groupCohomology.map (MonoidHom.id G) (β_ X.X₃ M).hom (s + r) u)
  have hz :
      groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
          ((-1 : ℤ) ^ (r * s) • x₀) =
        (-1 : ℤ) ^ (r * s) •
          groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl x₀ := by
    exact module_cat_zsmul
      (groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl) _ _
  have hsign :
      (-1 : ℤ) ^ r * (-1 : ℤ) ^ (r * s) =
        (-1 : ℤ) ^ (r * (s + 1)) := by
    rw [Nat.mul_add, mul_one, pow_add]
    ac_rfl
  have hright :
      (-1 : ℤ) ^ r •
          groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
            ((-1 : ℤ) ^ (r * s) • x₀) =
        (-1 : ℤ) ^ (r * (s + 1)) •
          cohomologyCast (M ⊗ X.X₁ : Rep ℤ G) hcommon md := by
    rw [hz, hdc, ← hβ']
    rw [smul_smul, hsign]
    dsimp only [md]
    rfl
  exact hleft.trans hright.symm

/-- The swapped, signed cup-product family is the canonical cup-product
family, by Proposition II.1.38. -/
theorem swapped_cup_canonical :
    swappedCupFamily (G := G) =
      canonicalCupFamily (G := G) := by
  exact CPFam.eq_canonical swappedCupFamily
    swapped_cup_zero
    swapped_family_connecting
    swapped_cup_connecting

/-- Proposition II.1.39(b), graded commutativity, with the two coefficient
modules identified by the symmetry isomorphism and the two equal total
degrees identified by `Nat.add_comm`. -/
theorem cup_graded_commutative
    (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) (b : groupCohomology N s) :
    cupCohomology M N r s a b =
      (-1 : ℤ) ^ (r * s) •
        cohomologyCast (M ⊗ N : Rep ℤ G) (Nat.add_comm s r)
          (groupCohomology.map (MonoidHom.id G) (β_ N M).hom (s + r)
            (cupCohomology N M s r b a)) := by
  have h := congrArg
    (fun P : CPFam (G := G) => P M N r s a b)
    (swapped_cup_canonical (G := G))
  exact h.symm

/-- Equivalent form of graded commutativity obtained by applying
`(β_ M N).hom` to the original cup product. -/
theorem graded_commutative_braiding
    (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) (b : groupCohomology N s) :
    groupCohomology.map (MonoidHom.id G) (β_ M N).hom (r + s)
        (cupCohomology M N r s a b) =
      (-1 : ℤ) ^ (r * s) •
        cohomologyCast (N ⊗ M : Rep ℤ G) (Nat.add_comm s r)
          (cupCohomology N M s r b a) := by
  let e : ℤ := (-1 : ℤ) ^ (r * s)
  let x := groupCohomology.map (MonoidHom.id G) (β_ M N).hom (r + s)
    (cupCohomology M N r s a b)
  have hswap := cup_graded_commutative N M s r b a
  have hsign : (-1 : ℤ) ^ (s * r) = e := by
    dsimp only [e]
    rw [Nat.mul_comm]
  rw [hsign] at hswap
  have hcast :
      cohomologyCast (N ⊗ M : Rep ℤ G) (Nat.add_comm s r)
          (cupCohomology N M s r b a) = e • x := by
    rw [hswap, module_cat_zsmul, cohomologyCast_trans]
    dsimp only [x]
    congr 1
  have hesquare : e * e = 1 := by
    dsimp only [e]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    x = 1 • x := by simp
    _ = (e * e) • x := by simp [hesquare]
    _ = e • (e • x) := by rw [smul_smul]
    _ = e • cohomologyCast (N ⊗ M : Rep ℤ G) (Nat.add_comm s r)
        (cupCohomology N M s r b a) := by rw [hcast]

end Towers.CField.COps.CPFuncto
