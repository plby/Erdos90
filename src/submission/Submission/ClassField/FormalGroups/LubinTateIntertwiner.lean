import Submission.ClassField.FormalGroups.LubinTateSeries

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the Frobenius congruence

Milne constructs the intertwining power series in Lemma 2.11 by successively
correcting its homogeneous components.  The key integrality input is that the
intertwining error is divisible by the chosen uniformizer.  This file proves
that input: after reduction to the finite residue field, both composites are
the same Frobenius power.

The subsequent files implement the coefficient recursion and its stable
coefficientwise limit, culminating in the full proof of Lemma 2.11.
-/

namespace Submission.CField.FGroups

noncomputable section

/-- Apply a unary power series independently to each variable. -/
def coordinatewiseSubst {R σ : Type*} [CommRing R]
    (g : PowerSeries R) (i : σ) : MvPowerSeries σ R :=
  PowerSeries.subst (MvPowerSeries.X i) g

@[simp]
theorem coordinatewise_subst_coeff
    {R σ : Type*} [CommRing R] {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (i : σ) :
    MvPowerSeries.constantCoeff (coordinatewiseSubst g i) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg

theorem coordinatewise_subst
    {R σ : Type*} [CommRing R] [Finite σ] {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst
      (coordinatewiseSubst (σ := σ) g : σ → MvPowerSeries σ R) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (coordinatewise_subst_coeff hg)

/-- Over a finite field, the `#k`-th power of a multivariable power series is
obtained by replacing every variable by its `#k`-th power. -/
theorem mv_card_expand
    {k σ : Type*} [Field k] [Fintype k]
    (phi : MvPowerSeries σ k) :
    phi ^ Fintype.card k =
      MvPowerSeries.expand (Fintype.card k) Fintype.card_ne_zero phi := by
  obtain ⟨p, hpChar, n, hp, hcard⟩ := FiniteField.card' k
  letI : CharP k p := hpChar
  letI : ExpChar k p := ExpChar.prime hp
  have hiterate : iterateFrobenius k p (n : ℕ) = RingHom.id k := by
    ext a
    rw [iterateFrobenius_def, ← hcard, FiniteField.pow_card]
    rfl
  have h := MvPowerSeries.map_iterateFrobenius_expand
    (R := k) (σ := σ) p hp.ne_zero phi (n : ℕ)
  rw [hiterate, MvPowerSeries.map_id, RingHom.id_apply] at h
  simpa only [hcard] using h.symm

/-- Mapping a coordinatewise substitution commutes with specializing the
underlying unary series. -/
theorem coordinatewise_subst_x
    {R k σ : Type*} [CommRing R] [CommRing k] (rho : R →+* k)
    {g : PowerSeries R}
    {q : ℕ} (hgmap : PowerSeries.map rho g = PowerSeries.X ^ q) (i : σ) :
    MvPowerSeries.map rho (coordinatewiseSubst g i) =
      (MvPowerSeries.X i : MvPowerSeries σ k) ^ q := by
  calc
    MvPowerSeries.map rho (coordinatewiseSubst g i) =
        PowerSeries.subst (MvPowerSeries.map rho (MvPowerSeries.X i))
          (PowerSeries.map rho g) := by
            simpa [coordinatewiseSubst] using
              PowerSeries.map_subst (h := rho) (PowerSeries.HasSubst.X i) g
    _ = PowerSeries.subst (MvPowerSeries.X i) (PowerSeries.X ^ q) := by
      rw [hgmap, MvPowerSeries.map_X]
    _ = (MvPowerSeries.X i : MvPowerSeries σ k) ^ q := by
      rw [PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

/-- Generic finite-field form of the Frobenius congruence used in Lemma
2.11. -/
theorem intertwining_maps_x
    {R k σ : Type*} [CommRing R] [Field k] [Fintype k] [Finite σ]
    (rho : R →+* k) {f g : PowerSeries R}
    (hfmap : PowerSeries.map rho f = PowerSeries.X ^ Fintype.card k)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hgmap : PowerSeries.map rho g = PowerSeries.X ^ Fintype.card k)
    {phi : MvPowerSeries σ R} (hphi : MvPowerSeries.constantCoeff phi = 0) :
    MvPowerSeries.map rho (PowerSeries.subst phi f) =
      MvPowerSeries.map rho
        (MvPowerSeries.subst (coordinatewiseSubst g) phi) := by
  have hphiSubst : PowerSeries.HasSubst phi :=
    PowerSeries.HasSubst.of_constantCoeff_zero hphi
  have hcoord : MvPowerSeries.HasSubst
      (coordinatewiseSubst (σ := σ) g : σ → MvPowerSeries σ R) :=
    coordinatewise_subst (σ := σ) hg0
  calc
    MvPowerSeries.map rho (PowerSeries.subst phi f) =
        PowerSeries.subst (MvPowerSeries.map rho phi) (PowerSeries.map rho f) := by
      simpa using PowerSeries.map_subst (h := rho) hphiSubst f
    _ = PowerSeries.subst (MvPowerSeries.map rho phi)
        (PowerSeries.X ^ Fintype.card k) := by rw [hfmap]
    _ = (MvPowerSeries.map rho phi) ^ Fintype.card k := by
      rw [PowerSeries.subst_pow (hphiSubst.map rho),
        PowerSeries.subst_X (hphiSubst.map rho)]
    _ = MvPowerSeries.expand (Fintype.card k) Fintype.card_ne_zero
        (MvPowerSeries.map rho phi) := mv_card_expand _
    _ = MvPowerSeries.subst
        (fun i ↦ (MvPowerSeries.X i : MvPowerSeries σ k) ^ Fintype.card k)
        (MvPowerSeries.map rho phi) := by
      rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
    _ = MvPowerSeries.subst
        (fun i ↦ MvPowerSeries.map rho (coordinatewiseSubst g i))
        (MvPowerSeries.map rho phi) := by
      congr 1
      funext i
      exact (coordinatewise_subst_x rho hgmap i).symm
    _ = MvPowerSeries.map rho
        (MvPowerSeries.subst (coordinatewiseSubst g) phi) := by
      exact (MvPowerSeries.map_subst (h := rho) hcoord phi).symm

/-- The divisibility input in Milne's proof of Lemma 2.11.  If `f` and `g`
belong to `\mathcal F_\pi`, then the error in the desired intertwining
identity vanishes after reduction modulo `pi`.

The hypothesis that the quotient is a finite field is the abstract form of
`A / (pi)` being the residue field of the local field. -/
theorem lubin_intertwining_pi
    {R σ : Type*} [CommRing R] [Finite σ] (pi : R)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    {phi : MvPowerSeries σ R} (hphi : MvPowerSeries.constantCoeff phi = 0) :
    MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {pi}))
        (PowerSeries.subst phi f) =
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {pi}))
        (MvPowerSeries.subst (coordinatewiseSubst g) phi) := by
  letI : Field (R ⧸ Ideal.span {pi}) := hfield.toField
  let rho : R →+* (R ⧸ Ideal.span {pi}) :=
    Ideal.Quotient.mk (Ideal.span {pi})
  have hfmap : PowerSeries.map rho f =
      PowerSeries.X ^ Fintype.card (R ⧸ Ideal.span {pi}) := by
    simpa [rho] using hf.2.2
  have hgmap : PowerSeries.map rho g =
      PowerSeries.X ^ Fintype.card (R ⧸ Ideal.span {pi}) := by
    simpa [rho] using hg.2.2
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact hg.1
  change MvPowerSeries.map rho (PowerSeries.subst phi f) =
    MvPowerSeries.map rho (MvPowerSeries.subst (coordinatewiseSubst g) phi)
  exact intertwining_maps_x
    (R := R) (k := R ⧸ Ideal.span {pi}) (σ := σ)
    (f := f) (g := g) rho hfmap hg0 hgmap hphi

/-- Coefficientwise form of `lubin_intertwining_pi`: the
intertwining error is divisible by `pi`.  This is the numerator-divisibility
step in the homogeneous correction used in Lemma 2.11. -/
theorem intertwining_error_span
    {R σ : Type*} [CommRing R] [Finite σ] (pi : R)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    {phi : MvPowerSeries σ R} (hphi : MvPowerSeries.constantCoeff phi = 0)
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
        (PowerSeries.subst phi f -
          MvPowerSeries.subst (coordinatewiseSubst g) phi) ∈
      Ideal.span {pi} := by
  have hcoeff := congrArg (MvPowerSeries.coeff d)
    (lubin_intertwining_pi pi hfield hf hg hphi)
  simp only [MvPowerSeries.coeff_map] at hcoeff
  simpa using
    (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {pi})).mp
      (show Ideal.Quotient.mk (Ideal.span {pi})
          (MvPowerSeries.coeff d
            (PowerSeries.subst phi f -
              MvPowerSeries.subst (coordinatewiseSubst g) phi)) = 0 by
        simpa using sub_eq_zero.mpr hcoeff)

end

end Submission.CField.FGroups
