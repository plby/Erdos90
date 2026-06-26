import Towers.ClassField.CohomologyOps.Naturality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open Rep
open scoped MonoidalCategory

variable {G : Type} [Group G]

noncomputable abbrev tensorShortComplex
    (X : ShortComplex (Rep ℤ G)) (N : Rep ℤ G) :
    ShortComplex (Rep ℤ G) :=
  X.map ((tensoringRight (Rep ℤ G)).obj N)

example (X : ShortComplex (Rep ℤ G)) (N : Rep ℤ G) :
    (tensorShortComplex X N).f = X.f ⊗ₘ 𝟙 N := by
  rfl

example (X : ShortComplex (Rep ℤ G)) (N : Rep ℤ G) :
    (tensorShortComplex X N).g = X.g ⊗ₘ 𝟙 N := by
  rfl

/-- Cochain representatives used in compatibility of the cup product with
the connecting morphism in the left coefficient variable. -/
theorem connecting_cup_representative
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (N : Rep ℤ G) (hXN : (tensorShortComplex X N).ShortExact)
    (i s : ℕ)
    (z : (Fin i → G) → X.X₃)
    (hz : (inhomogeneousCochains.d X.X₃ i).hom z = 0)
    (y : (Fin i → G) → X.X₂)
    (hy : (groupCohomology.cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin (i + 1) → G) → X.X₁)
    (hx : X.f.hom ∘ x = (inhomogeneousCochains.d X.X₂ i).hom y)
    (ψ : (Fin s → G) → N)
    (hψ : (inhomogeneousCochains.d N s).hom ψ = 0) :
    groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
        (cupCohomology X.X₃ N i s
          (groupCohomology.π X.X₃ i (groupCohomology.cocyclesMk z hz))
          (groupCohomology.π N s (groupCohomology.cocyclesMk ψ hψ))) =
      cohomologyCast (X.X₁ ⊗ N : Rep ℤ G)
        (by omega : (i + 1) + s = (i + s) + 1)
        (cupCohomology X.X₁ N (i + 1) s
          (groupCohomology.δ hX i (i + 1) rfl
            (groupCohomology.π X.X₃ i (groupCohomology.cocyclesMk z hz)))
          (groupCohomology.π N s (groupCohomology.cocyclesMk ψ hψ))) := by
  let XT := tensorShortComplex X N
  let zT : (Fin (i + s) → G) → XT.X₃ :=
    cochainCup X.X₃ N i s z ψ
  let yT : (Fin (i + s) → G) → XT.X₂ :=
    cochainCup X.X₂ N i s y ψ
  let hdeg : (i + s) + 1 = (i + 1) + s := by omega
  let xT : (Fin ((i + s) + 1) → G) → XT.X₁ :=
    cochainCast hdeg (cochainCup X.X₁ N (i + 1) s x ψ)
  have hzT : (inhomogeneousCochains.d XT.X₃ (i + s)).hom zT = 0 := by
    change cochainDifferential (X.X₃ ⊗ N : Rep ℤ G) (i + s)
      (cochainCup X.X₃ N i s z ψ) = 0
    exact cochain_cocycle X.X₃ N i s z ψ hz hψ
  have hy' : X.g.hom ∘ y = z := by
    simpa only [groupCohomology.cochainsMap_id_f_hom_eq_compLeft,
      LinearMap.compLeft_apply] using hy
  have hyT : (groupCohomology.cochainsMap (MonoidHom.id G) XT.g).f (i + s) yT = zT := by
    change (fun q => (X.g ⊗ₘ 𝟙 N) (cochainCup X.X₂ N i s y ψ q)) =
      cochainCup X.X₃ N i s z ψ
    rw [cochainCup_natural X.g (𝟙 N)]
    have hy'' : (fun a => X.g (y a)) = z := hy'
    rw [hy'']
    rfl
  have hxT : XT.f.hom ∘ xT =
      (inhomogeneousCochains.d XT.X₂ (i + s)).hom yT := by
    change (fun q => (X.f ⊗ₘ 𝟙 N)
        (cochainCast hdeg (cochainCup X.X₁ N (i + 1) s x ψ) q)) =
      cochainDifferential (X.X₂ ⊗ N : Rep ℤ G) (i + s)
        (cochainCup X.X₂ N i s y ψ)
    rw [cochain_cup_d X.X₂ N i s y ψ hψ]
    funext q
    have hn := congrFun (cochainCup_natural X.f (𝟙 N) (i + 1) s x ψ)
      (tupleCast hdeg q)
    have hx' : (fun a => X.f (x a)) = cochainDifferential X.X₂ i y := hx
    rw [hx'] at hn
    simpa [cochainCast] using hn
  have hxC : X.f.hom ∘ x =
      ((groupCohomology.inhomogeneousCochains X.X₂).d i (i + 1)).hom y := by
    calc
      X.f.hom ∘ x = (inhomogeneousCochains.d X.X₂ i).hom y := hx
      _ = ((groupCohomology.inhomogeneousCochains X.X₂).d i (i + 1)).hom y :=
        (congrArg (fun f => f.hom y)
          (groupCohomology.inhomogeneousCochains.d_def X.X₂ i)).symm
  have hxTC : XT.f.hom ∘ xT =
      ((groupCohomology.inhomogeneousCochains XT.X₂).d (i + s) ((i + s) + 1)).hom yT := by
    calc
      XT.f.hom ∘ xT = (inhomogeneousCochains.d XT.X₂ (i + s)).hom yT := hxT
      _ = ((groupCohomology.inhomogeneousCochains XT.X₂).d
          (i + s) ((i + s) + 1)).hom yT :=
        (congrArg (fun f => f.hom yT)
          (groupCohomology.inhomogeneousCochains.d_def XT.X₂ (i + s))).symm
  have hzC :
      ((groupCohomology.inhomogeneousCochains X.X₃).d i (i + 1)).hom z = 0 := by
    calc
      ((groupCohomology.inhomogeneousCochains X.X₃).d i (i + 1)).hom z =
          (inhomogeneousCochains.d X.X₃ i).hom z :=
        congrArg (fun f => f.hom z)
          (groupCohomology.inhomogeneousCochains.d_def X.X₃ i)
      _ = 0 := hz
  have hzTC :
      ((groupCohomology.inhomogeneousCochains XT.X₃).d (i + s) ((i + s) + 1)).hom zT = 0 := by
    calc
      ((groupCohomology.inhomogeneousCochains XT.X₃).d
          (i + s) ((i + s) + 1)).hom zT =
          (inhomogeneousCochains.d XT.X₃ (i + s)).hom zT :=
        congrArg (fun f => f.hom zT)
          (groupCohomology.inhomogeneousCochains.d_def XT.X₃ (i + s))
      _ = 0 := hzT
  let cz : groupCohomology.cocycles X.X₃ i := groupCohomology.cocyclesMk z hz
  let cψ : groupCohomology.cocycles N s := groupCohomology.cocyclesMk ψ hψ
  let cx : groupCohomology.cocycles X.X₁ (i + 1) :=
    groupCohomology.cocyclesMkOfCompEqD hX hxC
  let cxT : groupCohomology.cocycles XT.X₁ ((i + s) + 1) :=
    groupCohomology.cocyclesMkOfCompEqD hXN hxTC
  let czT : groupCohomology.cocycles XT.X₃ (i + s) :=
    groupCohomology.cocyclesMk zT hzT
  have icx : groupCohomology.iCocycles X.X₁ (i + 1) cx = x := by
    unfold cx groupCohomology.cocyclesMkOfCompEqD
    apply groupCohomology.iCocycles_mk
  have icxT : groupCohomology.iCocycles XT.X₁ ((i + s) + 1) cxT = xT := by
    unfold cxT groupCohomology.cocyclesMkOfCompEqD
    apply groupCohomology.iCocycles_mk
  have icxT' :
      groupCohomology.iCocycles (X.X₁ ⊗ N : Rep ℤ G) ((i + s) + 1) cxT = xT := icxT
  have hczT : cupCocycle X.X₃ N i s cz cψ = czT := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (X.X₃ ⊗ N : Rep ℤ G) (i + s))).1 inferInstance
    rw [i_cup_cocycle]
    have iczT :
        groupCohomology.iCocycles (X.X₃ ⊗ N : Rep ℤ G) (i + s) czT = zT := by
      unfold czT
      apply groupCohomology.iCocycles_mk
    rw [iczT]
    unfold cz cψ zT
    rw [groupCohomology.iCocycles_mk, groupCohomology.iCocycles_mk]
  have hc :
      cocyclesCast (X.X₁ ⊗ N : Rep ℤ G) hdeg.symm
          (cupCocycle X.X₁ N (i + 1) s cx cψ) = cxT := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (X.X₁ ⊗ N : Rep ℤ G) ((i + s) + 1))).1 inferInstance
    have hi := congrArg
      (fun q => q (cupCocycle X.X₁ N (i + 1) s cx cψ))
      (cocycles_cast_i (X.X₁ ⊗ N : Rep ℤ G) hdeg.symm)
    have hi' := hi
    simp only [ConcreteCategory.comp_apply] at hi'
    rw [cochain_hom, i_cup_cocycle, icx,
      groupCohomology.iCocycles_mk] at hi'
    · rw [hi', icxT']
      rfl
    · exact hdeg.symm
  have hdXT :
      groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
          (groupCohomology.π XT.X₃ (i + s) czT) =
        groupCohomology.π XT.X₁ ((i + s) + 1) cxT := by
    exact groupCohomology.δ_apply hXN rfl zT hzTC yT hyT xT hxTC
  have hdXT' :
      groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
          (groupCohomology.π (X.X₃ ⊗ N : Rep ℤ G) (i + s) czT) =
        groupCohomology.π (X.X₁ ⊗ N : Rep ℤ G) ((i + s) + 1) cxT := hdXT
  have hdX :
      groupCohomology.δ hX i (i + 1) rfl
          (groupCohomology.π X.X₃ i cz) =
        groupCohomology.π X.X₁ (i + 1) cx := by
    exact groupCohomology.δ_apply hX rfl z hzC y hy x hxC
  change groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
      (cupCohomology X.X₃ N i s
        (groupCohomology.π X.X₃ i cz) (groupCohomology.π N s cψ)) =
    cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hdeg.symm
      (cupCohomology X.X₁ N (i + 1) s
        (groupCohomology.δ hX i (i + 1) rfl (groupCohomology.π X.X₃ i cz))
        (groupCohomology.π N s cψ))
  rw [cupCohomology_π, hczT, hdXT', hdX, cupCohomology_π]
  change groupCohomology.π (X.X₁ ⊗ N : Rep ℤ G) ((i + s) + 1) cxT =
    cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hdeg.symm
      (groupCohomology.π (X.X₁ ⊗ N : Rep ℤ G) ((i + 1) + s)
        (cupCocycle X.X₁ N (i + 1) s cx cψ))
  have hp := congrArg
    (fun q => q (cupCocycle X.X₁ N (i + 1) s cx cψ))
    (π_comp_cohomologyCast (X.X₁ ⊗ N : Rep ℤ G) hdeg.symm)
  have hp' := hp
  simp only [ConcreteCategory.comp_apply] at hp'
  rw [hp', hc]

theorem exists_conne_repre
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact) (i : ℕ)
    (z : (Fin i → G) → X.X₃)
    (hz : (inhomogeneousCochains.d X.X₃ i).hom z = 0) :
    ∃ (y : (Fin i → G) → X.X₂)
      (x : (Fin (i + 1) → G) → X.X₁),
      (groupCohomology.cochainsMap (MonoidHom.id G) X.g).f i y = z ∧
        X.f.hom ∘ x = (inhomogeneousCochains.d X.X₂ i).hom y := by
  letI : Epi X.g := hX.epi_g
  letI : Epi ((groupCohomology.cochainsMap (MonoidHom.id G) X.g).f i) := inferInstance
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((groupCohomology.cochainsMap (MonoidHom.id G) X.g).f i)).1 inferInstance z
  letI repModule (A : Rep ℤ G) : Module ℤ A := A.hV2
  let F : Functor (Rep ℤ G) (ModuleCat ℤ) := forget₂ (Rep ℤ G) (ModuleCat ℤ)
  let UX := X.map F
  have hUX : UX.ShortExact := hX.map_of_exact F
  have he : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := by
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact UX).mp hUX.exact
  have hcomm := congrArg (fun q => q y)
    ((groupCohomology.cochainsMap (MonoidHom.id G) X.g).comm i (i + 1))
  have hcomm' := hcomm
  simp only [ConcreteCategory.comp_apply] at hcomm'
  rw [hy] at hcomm'
  have hcomm'' :
      (inhomogeneousCochains.d X.X₃ i).hom z =
        (groupCohomology.cochainsMap (MonoidHom.id G) X.g).f (i + 1)
          ((inhomogeneousCochains.d X.X₂ i).hom y) := by
    calc
      (inhomogeneousCochains.d X.X₃ i).hom z =
          ((groupCohomology.inhomogeneousCochains X.X₃).d i (i + 1)).hom z :=
        (congrArg (fun f => f.hom z)
          (groupCohomology.inhomogeneousCochains.d_def X.X₃ i)).symm
      _ = (groupCohomology.cochainsMap (MonoidHom.id G) X.g).f (i + 1)
          (((groupCohomology.inhomogeneousCochains X.X₂).d i (i + 1)).hom y) := hcomm'
      _ = (groupCohomology.cochainsMap (MonoidHom.id G) X.g).f (i + 1)
          ((inhomogeneousCochains.d X.X₂ i).hom y) := by
        rw [groupCohomology.inhomogeneousCochains.d_def]
  rw [hz] at hcomm''
  have hgdy : X.g.hom ∘ ((inhomogeneousCochains.d X.X₂ i).hom y) = 0 := by
    simpa only [groupCohomology.cochainsMap_id_f_hom_eq_compLeft,
      LinearMap.compLeft_apply] using hcomm''.symm
  choose x hx using fun q =>
    (he ((inhomogeneousCochains.d X.X₂ i).hom y q)).1 (congrFun hgdy q)
  refine ⟨y, x, hy, ?_⟩
  funext q
  exact hx q

/-- Proposition II.1.38(c), left coefficient variable: the cup product
commutes with the connecting homomorphism.  Exactness of the tensor row is
stated separately, so no flatness hypothesis is hidden in the theorem. -/
theorem connecting_cup
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (N : Rep ℤ G) (hXN : (tensorShortComplex X N).ShortExact)
    (i s : ℕ) (a : groupCohomology X.X₃ i)
    (b : groupCohomology N s) :
    groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
        (cupCohomology X.X₃ N i s a b) =
      cohomologyCast (X.X₁ ⊗ N : Rep ℤ G)
        (by omega : (i + 1) + s = (i + s) + 1)
        (cupCohomology X.X₁ N (i + 1) s
          (groupCohomology.δ hX i (i + 1) rfl a) b) := by
  induction a using groupCohomology_induction_on with
  | h za =>
      induction b using groupCohomology_induction_on with
      | h zb =>
          let z := groupCohomology.iCocycles X.X₃ i za
          let ψ := groupCohomology.iCocycles N s zb
          have hz : (inhomogeneousCochains.d X.X₃ i).hom z = 0 :=
            cocycles_cocycle X.X₃ i za
          have hψ : (inhomogeneousCochains.d N s).hom ψ = 0 :=
            cocycles_cocycle N s zb
          obtain ⟨y, x, hy, hx⟩ := exists_conne_repre X hX i z hz
          have hza : groupCohomology.cocyclesMk z hz = za := by
            apply (ModuleCat.mono_iff_injective
              (groupCohomology.iCocycles X.X₃ i)).1 inferInstance
            rw [groupCohomology.iCocycles_mk]
          have hzb : groupCohomology.cocyclesMk ψ hψ = zb := by
            apply (ModuleCat.mono_iff_injective
              (groupCohomology.iCocycles N s)).1 inferInstance
            rw [groupCohomology.iCocycles_mk]
          have h := connecting_cup_representative X hX N hXN i s
            z hz y hy x hx ψ hψ
          rw [hza, hzb] at h
          exact h

end Towers.CField.COps.CPBuild
