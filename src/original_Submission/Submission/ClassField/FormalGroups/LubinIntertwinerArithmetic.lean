import Submission.ClassField.FormalGroups.LubinGroupLaw

/-!
# Class Field Theory, Chapter I, Proposition 2.15

Milne's canonical unary intertwiners respect addition, where addition in the
target is computed using its Lubin--Tate formal group law, and multiplication,
where multiplication is composition.  Both identities follow directly from
the uniqueness clause in Lemma 2.11.
-/

namespace Submission.CField.FGroups

open MvPowerSeries
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- Proposition 2.15, additive identity:
`[a+b]_{g,f} = [a]_{g,f} +_{F_g} [b]_{g,f}`. -/
theorem lubin_intertwiner_add
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a b : R) :
    FGLaw.substitute
        (lubinTateLaw pi hpi0 hpi hfield g hg)
        (lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
          (fun _ : Fin 1 => a))
        (lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
          (fun _ : Fin 1 => b)) =
      lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
        (fun _ : Fin 1 => a + b) := by
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  let x : Fin 2 -> UnarySeries R :=
    Fin.cases
      (lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
        (fun _ : Fin 1 => a))
      (fun _ => lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
        (fun _ : Fin 1 => b))
  let c : Fin 2 -> Fin 1 -> R :=
    Fin.cases (fun _ => a) (fun _ _ => b)
  have hx : forall i, LIntert g f (c i) (x i) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact tate_intertwiner_spec pi hpi0 hpi hfield g f hg hf _
    · exact tate_intertwiner_spec pi hpi0 hpi hfield g f hg hf _
  have hsubst :=
    (lubin_tate_spec pi hpi0 hpi hfield g hg).subst hg0 hf0 hx
  have hcoeff :
      (fun j : Fin 1 => ∑ i, (1 : R) * c i j) =
        (fun _ : Fin 1 => a + b) := by
    funext j
    fin_cases j
    rw [Fin.sum_univ_two]
    simp only [one_mul]
    change c 0 0 + c 1 0 = a + b
    change a + b = a + b
    rfl
  rw [hcoeff] at hsubst
  apply tate_intertwiner pi hpi0 hpi hfield g f hg hf _
  simpa [FGLaw.substitute, x] using hsubst

/-- Proposition 2.15, multiplicative identity:
`[ab]_{h,f} = [a]_{h,g} o [b]_{g,f}`. -/
theorem lubin_intertwiner_mul
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g h : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (hh : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) h)
    (a b : R) :
    FGLaw.compose
        (lubinTateIntertwiner pi hpi0 hpi hfield h g hh hg
          (fun _ : Fin 1 => a))
        (lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
          (fun _ : Fin 1 => b)) =
      lubinTateIntertwiner pi hpi0 hpi hfield h f hh hf
        (fun _ : Fin 1 => a * b) := by
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  have ha := tate_intertwiner_spec pi hpi0 hpi hfield h g hh hg
    (fun _ : Fin 1 => a)
  let x : Fin 1 -> UnarySeries R := fun _ =>
    lubinTateIntertwiner pi hpi0 hpi hfield g f hg hf
      (fun _ : Fin 1 => b)
  let c : Fin 1 -> Fin 1 -> R := fun _ _ => b
  have hx : forall i, LIntert g f (c i) (x i) := by
    intro i
    exact tate_intertwiner_spec pi hpi0 hpi hfield g f hg hf _
  have hsubst := ha.subst hg0 hf0 hx
  have hcoeff :
      (fun j : Fin 1 => ∑ i, a * c i j) =
        (fun _ : Fin 1 => a * b) := by
    funext j
    fin_cases j
    rw [Fin.sum_univ_one]
  rw [hcoeff] at hsubst
  apply tate_intertwiner pi hpi0 hpi hfield h f hh hf _
  simpa [FGLaw.compose, x] using hsubst

end

end Submission.CField.FGroups
