import Submission.ClassField.CohomologyOps.Naturality
import Submission.ClassField.CohomologyOps.ConnectingCocycle
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace Submission.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidalCategory

variable {G : Type} [Group G]

/-- Tensor a short complex of coefficient modules on the left by `M`. -/
noncomputable abbrev leftShortComplex (M : Rep ℤ G) (X : ShortComplex (Rep ℤ G)) :
    ShortComplex (Rep ℤ G) :=
  X.map ((MonoidalCategory.tensoringLeft (Rep ℤ G)).obj M)

theorem cup_delta_lifts
    (M : Rep ℤ G) {X : ShortComplex (Rep ℤ G)}
    (hX : X.ShortExact) (hMX : (leftShortComplex M X).ShortExact)
    (r s : ℕ)
    (φ : (Fin r → G) → M) (hφ : cochainDifferential M r φ = 0)
    (ψ : (Fin s → G) → X.X₃) (hψ : cochainDifferential X.X₃ s ψ = 0)
    (y : (Fin s → G) → X.X₂) (hy : (fun q => X.g (y q)) = ψ)
    (x : (Fin (s + 1) → G) → X.X₁)
    (hx : (fun q => X.f (x q)) = cochainDifferential X.X₂ s y) :
    cupCohomology M X.X₁ r (s + 1)
        (groupCohomology.π M r (groupCohomology.cocyclesMk φ hφ))
        (groupCohomology.δ hX s (s + 1) rfl
          (groupCohomology.π X.X₃ s (groupCohomology.cocyclesMk ψ hψ))) =
      (-1 : ℤ) ^ r •
        groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
          (cupCohomology M X.X₃ r s
            (groupCohomology.π M r (groupCohomology.cocyclesMk φ hφ))
            (groupCohomology.π X.X₃ s (groupCohomology.cocyclesMk ψ hψ))) := by
  have hxRaw : X.f.hom ∘ x =
      (groupCohomology.inhomogeneousCochains X.X₂).d s (s + 1) y := by
    simpa [Function.comp_def, cochainDifferential] using hx
  have hδX := groupCohomology.δ_apply hX rfl ψ (by
    simpa [cochainDifferential] using hψ) y (by
    simpa [groupCohomology.cochainsMap_id_f_hom_eq_compLeft] using hy) x hxRaw
  rw [hδX]
  rw [cupCohomology_π]
  have hcupψ : cochainDifferential (M ⊗ X.X₃ : Rep ℤ G) (r + s)
      (cochainCup M X.X₃ r s φ ψ) = 0 :=
    cochain_cocycle M X.X₃ r s φ ψ hφ hψ
  have hyCup :
      (fun q => (leftShortComplex M X).g
        (cochainCup M X.X₂ r s φ y q)) =
        cochainCup M X.X₃ r s φ ψ := by
    rw [← hy]
    exact cochainCup_natural (𝟙 M) X.g r s φ y
  let sign : ℤ := (-1 : ℤ) ^ r
  let cupx : (Fin ((r + s) + 1) → G) → (M ⊗ X.X₁ : Rep ℤ G) :=
    fun q => (M ⊗ X.X₁ : Rep ℤ G).hV2.smul sign
      (cochainCup M X.X₁ r (s + 1) φ x q)
  have hxCup :
      (fun q => (leftShortComplex M X).f (cupx q)) =
        cochainDifferential (M ⊗ X.X₂ : Rep ℤ G) (r + s)
          (cochainCup M X.X₂ r s φ y) := by
    rw [cochain_d_cocycle M X.X₂ r s φ y hφ]
    ext q
    simp only [cupx, sign, Pi.smul_apply, cochainCast]
    have hq : tupleCast (by omega : (r + s) + 1 = r + (s + 1)) q = q := by
      ext i
      simp only [tupleCast_apply]
      congr 1
    rw [hq, ← hx]
    let c := cochainCup M X.X₁ r (s + 1) φ x
    have hm := map_zsmul
      ((groupCohomology.cochainsMap (MonoidHom.id G)
        (leftShortComplex M X).f).f ((r + s) + 1)).hom sign c
    have hn := cochainCup_natural (𝟙 M) X.f r (s + 1) φ x
    have hn' : (fun q => (leftShortComplex M X).f (c q)) =
        cochainCup M X.X₂ r (s + 1) φ (fun q => X.f (x q)) := by
      simpa only [Rep.id_apply] using hn
    calc
      (leftShortComplex M X).f
          ((M ⊗ X.X₁ : Rep ℤ G).hV2.smul sign (c q)) =
          (leftShortComplex M X).f ((sign • c) q) := by
            rw [Pi.smul_apply,
              int_smul_eq_zsmul (M ⊗ X.X₁ : Rep ℤ G).hV2]
      _ = (sign • (fun q => (leftShortComplex M X).f (c q))) q := by
            exact congrFun hm q
      _ = sign • cochainCup M X.X₂ r (s + 1) φ
          (fun q => X.f (x q)) q := by
            rw [Pi.smul_apply, congrFun hn' q]
            rfl
  have hxCupRaw : (leftShortComplex M X).f.hom ∘ cupx =
      (groupCohomology.inhomogeneousCochains
        (leftShortComplex M X).X₂).d
        (r + s) ((r + s) + 1) (cochainCup M X.X₂ r s φ y) := by
    simpa [Function.comp_def, cochainDifferential] using hxCup
  have hδMX := groupCohomology.δ_apply hMX rfl
    (cochainCup M X.X₃ r s φ ψ) (by
      simpa [cochainDifferential] using hcupψ)
    (cochainCup M X.X₂ r s φ y) (by
      simpa [groupCohomology.cochainsMap_id_f_hom_eq_compLeft] using hyCup)
    cupx hxCupRaw
  have hδMX' :
      groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
          (groupCohomology.π (M ⊗ X.X₃ : Rep ℤ G) (r + s)
            (groupCohomology.cocyclesMk
              (cochainCup M X.X₃ r s φ ψ) hcupψ)) =
        groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) ((r + s) + 1)
          (groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) := by
    simpa only using hδMX
  have hinput :
      cupCocycle M X.X₃ r s
          (groupCohomology.cocyclesMk φ hφ)
          (groupCohomology.cocyclesMk ψ hψ) =
        groupCohomology.cocyclesMk (cochainCup M X.X₃ r s φ ψ) hcupψ := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ X.X₃ : Rep ℤ G) (r + s))).1 inferInstance
    rw [i_cup_cocycle]
    rw [groupCohomology.iCocycles_mk, groupCohomology.iCocycles_mk,
      groupCohomology.iCocycles_mk]
  have houtput :
      cupCocycle M X.X₁ r (s + 1)
          (groupCohomology.cocyclesMk φ hφ)
          (groupCohomology.cocyclesMkOfCompEqD hX hxRaw) =
        sign • groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1)))).1 inferInstance
    rw [i_cup_cocycle]
    rw [groupCohomology.iCocycles_mk, groupCohomology.iCocycles_mk]
    have hi :
        groupCohomology.iCocycles (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
            (sign • groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) =
          sign • groupCohomology.iCocycles (M ⊗ X.X₁ : Rep ℤ G)
            (r + (s + 1))
            (groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) := by
      exact map_zsmul (groupCohomology.iCocycles
        (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))).hom sign _
    rw [hi]
    have hitarget :
        groupCohomology.iCocycles (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
            (groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) = cupx := by
      exact groupCohomology.iCocycles_mk cupx _
    rw [hitarget]
    simp only [cupx, sign]
    ext q
    change cochainCup M X.X₁ r (s + 1) φ x q =
      (-1 : ℤ) ^ r • (M ⊗ X.X₁ : Rep ℤ G).hV2.smul ((-1 : ℤ) ^ r)
        (cochainCup M X.X₁ r (s + 1) φ x q)
    rw [int_smul_eq_zsmul (M ⊗ X.X₁ : Rep ℤ G).hV2]
    rw [← smul_assoc]
    simp [← pow_add]
  rw [cupCohomology_π]
  rw [hinput]
  rw [hδMX']
  have hp :
      groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
          (sign • groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) =
        sign • groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
          (groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) := by
    exact map_zsmul (groupCohomology.π
      (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))).hom sign _
  calc
    groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
        (cupCocycle M X.X₁ r (s + 1)
          (groupCohomology.cocyclesMk φ hφ)
          (groupCohomology.cocyclesMkOfCompEqD hX hxRaw)) =
      groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
        (sign • groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) :=
          congrArg (groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G)
            (r + (s + 1))) houtput
    _ = sign • groupCohomology.π (M ⊗ X.X₁ : Rep ℤ G) (r + (s + 1))
        (groupCohomology.cocyclesMkOfCompEqD hMX hxCupRaw) := hp

/-- Proposition II.1.38(d): the cup product is compatible with the
connecting homomorphism in its right coefficient variable, with the Koszul
sign determined by the degree of the left class. -/
theorem cup_cohomology_delta
    (M : Rep ℤ G) {X : ShortComplex (Rep ℤ G)}
    (hX : X.ShortExact) (hMX : (leftShortComplex M X).ShortExact)
    (r s : ℕ) (a : groupCohomology M r) (b : groupCohomology X.X₃ s) :
    cupCohomology M X.X₁ r (s + 1) a
        (groupCohomology.δ hX s (s + 1) rfl b) =
      (-1 : ℤ) ^ r •
        groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
          (cupCohomology M X.X₃ r s a b) := by
  induction a using groupCohomology_induction_on with
  | h ac =>
      induction b using groupCohomology_induction_on with
      | h bc =>
          let φ := groupCohomology.iCocycles M r ac
          have hφ : cochainDifferential M r φ = 0 :=
            cocycles_cocycle M r ac
          let ψ := groupCohomology.iCocycles X.X₃ s bc
          have hψ : cochainDifferential X.X₃ s ψ = 0 :=
            cocycles_cocycle X.X₃ s bc
          have hψRaw :
              (groupCohomology.inhomogeneousCochains X.X₃).d
                s (s + 1) ψ = 0 := by
            simpa [cochainDifferential] using hψ
          obtain ⟨y, x, hy, hx, _⟩ :=
            lift_representing_connecting hX rfl ψ hψRaw
          have hy' : (fun q => X.g (y q)) = ψ := by
            simpa [groupCohomology.cochainsMap_id_f_hom_eq_compLeft] using hy
          have hx' : (fun q => X.f (x q)) =
              cochainDifferential X.X₂ s y := by
            simpa [Function.comp_def, cochainDifferential] using hx
          have hφc : groupCohomology.cocyclesMk φ hφ = ac := by
            apply (ModuleCat.mono_iff_injective
              (groupCohomology.iCocycles M r)).1 inferInstance
            rw [groupCohomology.iCocycles_mk]
          have hψc : groupCohomology.cocyclesMk ψ hψ = bc := by
            apply (ModuleCat.mono_iff_injective
              (groupCohomology.iCocycles X.X₃ s)).1 inferInstance
            rw [groupCohomology.iCocycles_mk]
          have hrep := cup_delta_lifts M hX hMX r s
            φ hφ ψ hψ y hy' x hx'
          rw [hφc, hψc] at hrep
          exact hrep

end Submission.CField.COps.CPBuild
