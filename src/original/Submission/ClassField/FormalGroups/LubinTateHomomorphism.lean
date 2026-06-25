import Submission.ClassField.FormalGroups.LubinGroupLaw

/-!
# Class Field Theory, Chapter I, Proposition 2.14

The canonical unary intertwiner `[a]_{g,f}` is a homomorphism from the
Lubin--Tate formal group law attached to `f` to the one attached to `g`.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- Milne's canonical series `[a]_{g,f}`. -/
noncomputable def tateScalarIntertwiner
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) : UnarySeries R :=
  lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
    (fun _ : Fin 1 ↦ a)

theorem lubin_intertwiner_spec
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    LIntert g f (fun _ : Fin 1 ↦ a)
      (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a) :=
  tate_intertwiner_spec pi hpi0 hpi hfield g f hg hf _

/-- The binary homomorphism identity in Proposition 2.14. -/
theorem intertwiner_law_binary
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    FGLaw.compose
        (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
        (lubinTateLaw pi hpi0 hpi hfield f hf) =
      FGLaw.substitute
        (lubinTateLaw pi hpi0 hpi hfield g hg)
        (FGLaw.compose
          (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
          FGLaw.binaryX)
        (FGLaw.compose
          (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
          FGLaw.binaryY) := by
  let h := tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1
  have hh : LIntert g f (fun _ : Fin 1 ↦ a) h :=
    lubin_intertwiner_spec pi hpi0 hpi hfield f g hf hg a
  let lawF := lubinTateLaw pi hpi0 hpi hfield f hf
  let lawG := lubinTateLaw pi hpi0 hpi hfield g hg
  have hlawF : LIntert f f (fun _ : Fin 2 ↦ 1) lawF :=
    lubin_tate_spec pi hpi0 hpi hfield f hf
  have hlawG : LIntert g g (fun _ : Fin 2 ↦ 1) lawG :=
    lubin_tate_spec pi hpi0 hpi hfield g hg
  let leftFamily : Fin 1 → BinarySeries R := fun _ ↦ lawF
  let leftCoeffs : Fin 1 → Fin 2 → R := fun _ _ ↦ 1
  have hleftFamily : ∀ i, LIntert f f
      (leftCoeffs i) (leftFamily i) := fun _ ↦ hlawF
  have hleft := hh.subst hf0 hf0 hleftFamily
  have hleftCoeffs :
      (fun j : Fin 2 ↦ ∑ i, a * leftCoeffs i j) = fun _ ↦ a := by
    funext j
    rw [Fin.sum_univ_one]
    simp [leftCoeffs]
  rw [hleftCoeffs] at hleft
  let coordinate : Fin 2 → BinarySeries R := fun i => X i
  let basis : Fin 2 → Fin 2 → R := fun i j ↦ if j = i then 1 else 0
  have hcoordinate : ∀ i,
      LIntert f f (basis i) (coordinate i) := by
    intro i
    exact lubin_intertwiner_x hf0 i
  let rightFamily : Fin 2 → BinarySeries R :=
    Fin.cases (FGLaw.compose h FGLaw.binaryX)
      (fun _ => FGLaw.compose h FGLaw.binaryY)
  let rightCoeffs : Fin 2 → Fin 2 → R := fun i j ↦ a * basis i j
  have hrightFamily : ∀ i,
      LIntert g f (rightCoeffs i) (rightFamily i) := by
    intro i
    fin_cases i
    · have hi := hh.subst hf0 hf0
        (fun _ : Fin 1 => hcoordinate (0 : Fin 2))
      have hcoeff :
          (fun j : Fin 2 => ∑ k : Fin 1, a * basis 0 j) =
            rightCoeffs 0 := by
        funext j
        rw [Fin.sum_univ_one]
      rw [hcoeff] at hi
      simpa [rightFamily, coordinate, FGLaw.compose,
        FGLaw.binaryX] using hi
    · have hi := hh.subst hf0 hf0
        (fun _ : Fin 1 => hcoordinate (1 : Fin 2))
      have hcoeff :
          (fun j : Fin 2 => ∑ k : Fin 1, a * basis 1 j) =
            rightCoeffs 1 := by
        funext j
        rw [Fin.sum_univ_one]
      rw [hcoeff] at hi
      simpa [rightFamily, coordinate, FGLaw.compose,
        FGLaw.binaryY] using hi
  have hright := hlawG.subst hg0 hf0 hrightFamily
  have hrightCoeffs :
      (fun j : Fin 2 ↦ ∑ i, (1 : R) * rightCoeffs i j) = fun _ ↦ a := by
    funext j
    fin_cases j <;> simp [rightCoeffs, basis]
  rw [hrightCoeffs] at hright
  have hleftEq :
      FGLaw.compose
          (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
          (lubinTateLaw pi hpi0 hpi hfield f hf) =
        lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
          (fun _ : Fin 2 => a) :=
    tate_intertwiner pi hpi0 hpi hfield g f hg hf _
      (by simpa [FGLaw.compose, h, leftFamily, lawF] using hleft)
  have hrightEq :
      FGLaw.substitute
          (lubinTateLaw pi hpi0 hpi hfield g hg)
          (FGLaw.compose
            (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
            FGLaw.binaryX)
          (FGLaw.compose
            (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)
            FGLaw.binaryY) =
        lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
          (fun _ : Fin 2 => a) :=
    tate_intertwiner pi hpi0 hpi hfield g f hg hf _
      (by simpa [FGLaw.compose, FGLaw.substitute, h, lawG,
          rightFamily, coordinate] using hright)
  exact hleftEq.trans hrightEq.symm

/-- Proposition 2.14: `[a]_{g,f}` is a homomorphism `F_f → F_g`. -/
noncomputable def lubinTateScalar
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    FGLaw.Hom
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield g hg) where
  toSeries := tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a
  constant_coeff_zero := LIntert.constant_coeff_zero
    (lubin_intertwiner_spec pi hpi0 hpi hfield f g hf hg a)
  map_law {σ} x y hx hy := by
    let z : Fin 2 → MvPowerSeries σ R := Fin.cases x (fun _ ↦ y)
    have hz : HasSubst z := hasSubst_of_constantCoeff_zero (by
      intro i
      exact Fin.cases hx (fun _ ↦ hy) i)
    let h := tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a
    let lawF := lubinTateLaw pi hpi0 hpi hfield f hf
    let lawG := lubinTateLaw pi hpi0 hpi hfield g hg
    have hh0 : constantCoeff h = 0 :=
      LIntert.constant_coeff_zero
        (lubin_intertwiner_spec pi hpi0 hpi hfield f g hf hg a)
    have hlawF0 : constantCoeff lawF = 0 :=
      lubin_law_coeff pi hpi0 hpi hfield f hf
    have hconstLawF : HasSubst (fun _ : Fin 1 ↦ lawF) :=
      hasSubst_of_constantCoeff_zero (fun _ ↦ hlawF0)
    let w : Fin 2 → BinarySeries R :=
      Fin.cases (FGLaw.compose h FGLaw.binaryX)
        (fun _ ↦ FGLaw.compose h FGLaw.binaryY)
    have hw0 : ∀ i, constantCoeff (w i) = 0 := by
      intro i
      refine Fin.cases ?_ (fun _ ↦ ?_) i
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero
            (fun _ : Fin 1 ↦ by simp [FGLaw.binaryX]))
          (fun _ : Fin 1 ↦ by simp [FGLaw.binaryX]) hh0
      · exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero
            (fun _ : Fin 1 ↦ by simp [FGLaw.binaryY]))
          (fun _ : Fin 1 ↦ by simp [FGLaw.binaryY]) hh0
    have hw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have hbinary := intertwiner_law_binary
      pi hpi0 hpi hfield f g hf hg a
    change subst (fun _ : Fin 1 ↦ subst z lawF) h =
      subst (Fin.cases (subst (fun _ : Fin 1 ↦ x) h)
        (fun _ ↦ subst (fun _ : Fin 1 ↦ y) h)) lawG
    calc
      subst (fun _ : Fin 1 ↦ subst z lawF) h =
          subst z (subst (fun _ : Fin 1 ↦ lawF) h) :=
        (MvPowerSeries.subst_comp_subst_apply hconstLawF hz h).symm
      _ = subst z (subst w lawG) := by
        apply congrArg (subst z)
        simpa [FGLaw.compose, FGLaw.substitute, h, lawF,
          lawG, w] using hbinary
      _ = subst (fun i ↦ subst z (w i)) lawG :=
        MvPowerSeries.subst_comp_subst_apply hw hz lawG
      _ = subst (Fin.cases (subst (fun _ : Fin 1 ↦ x) h)
          (fun _ ↦ subst (fun _ : Fin 1 ↦ y) h)) lawG := by
        congr 1
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change subst z (subst (fun _ : Fin 1 ↦ FGLaw.binaryX) h) = _
          rw [MvPowerSeries.subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero
              (fun _ : Fin 1 ↦ by simp [FGLaw.binaryX])) hz h]
          congr 1
          funext k
          rw [FGLaw.binaryX, subst_X hz]
          rfl
        · change subst z (subst (fun _ : Fin 1 ↦ FGLaw.binaryY) h) = _
          rw [MvPowerSeries.subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero
              (fun _ : Fin 1 ↦ by simp [FGLaw.binaryY])) hz h]
          congr 1
          funext k
          rw [FGLaw.binaryY, subst_X hz]
          rfl

@[simp]
theorem lubin_scalar_series
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    (lubinTateScalar pi hpi0 hpi hfield f g hf hg a).toSeries =
      tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a := rfl

end

end Submission.CField.FGroups
