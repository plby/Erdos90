import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Basic
import Submission.NumberTheory.Locals.LocalPolynomialCoprime
import Submission.NumberTheory.Locals.NewtonRootLifting


/-!
# Uniqueness in Hensel factorization

The algebraic uniqueness argument in Milne's Lemma 7.35 only uses strict
coprimality, monicity, and equality of degrees.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

section

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Milne, Lemma 7.35, algebraic core: two factorizations with coprime
cross-factors and equal-degree monic first factors coincide. -/
theorem monic_unique_coprime
    {g h g' h' : A[X]}
    (hg : g.Monic) (hg' : g'.Monic)
    (hdegree : g.natDegree = g'.natDegree)
    (hcoprime : IsCoprime g h')
    (hfactor : g * h = g' * h') :
    g = g' ∧ h = h' := by
  have hgdvd : g ∣ g' * h' := ⟨h, hfactor.symm⟩
  have hgg' : g ∣ g' := hcoprime.dvd_of_dvd_mul_right hgdvd
  have hgeq : g = g' :=
    eq_of_dvd_of_natDegree_le_of_leadingCoeff hgg'
      (by rw [hdegree]) (by rw [hg.leadingCoeff, hg'.leadingCoeff])
  refine ⟨hgeq, ?_⟩
  subst g'
  exact hg.isRegular.left hfactor

end

section LocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

/-- Milne, Lemma 7.35: monic factorizations with the same relatively-prime
reduction modulo the maximal ideal are unique. -/
theorem monic_unique_residue
    {g h g' h' : A[X]}
    (hg : g.Monic) (_hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hfactor : g * h = g' * h')
    (hmapg : g.map (IsLocalRing.residue A) =
      g'.map (IsLocalRing.residue A))
    (hmaph : h.map (IsLocalRing.residue A) =
      h'.map (IsLocalRing.residue A))
    (hcoprime : IsCoprime
      (g.map (IsLocalRing.residue A)) (h.map (IsLocalRing.residue A))) :
    g = g' ∧ h = h' := by
  have hdegree : g.natDegree = g'.natDegree := by
    rw [← hg.natDegree_map (IsLocalRing.residue A), hmapg,
      hg'.natDegree_map (IsLocalRing.residue A)]
  have hcoprime' : IsCoprime g h' := by
    apply coprime_monic_residue hg hh'
    simpa only [← hmaph] using hcoprime
  exact monic_unique_coprime hg hg' hdegree hcoprime' hfactor

/-- Milne, Proposition 7.31, including uniqueness: a simple root modulo the
maximal ideal of a Henselian local domain has exactly one root lift in its
residue class. -/
theorem simple_lifts_unique
    [HenselianLocalRing A]
    (f : A[X]) (hf : f.Monic) (a0 : A)
    (hroot : f.eval a0 ∈ IsLocalRing.maximalIdeal A)
    (hsimple : IsUnit (f.derivative.eval a0)) :
    ∃! a : A, f.IsRoot a ∧ a - a0 ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨a, ha, ha0⟩ :=
    simple_maximal_lifts f hf a0 hroot hsimple
  refine ⟨a, ⟨ha, ha0⟩, ?_⟩
  rintro b ⟨hb, hb0⟩
  let rho : A →+* IsLocalRing.ResidueField A := IsLocalRing.residue A
  let g : A[X] := X - C a
  let h : A[X] := f /ₘ g
  let g' : A[X] := X - C b
  let h' : A[X] := f /ₘ g'
  have hg : g.Monic := by simpa [g] using monic_X_sub_C a
  have hg' : g'.Monic := by simpa [g'] using monic_X_sub_C b
  have hfactor : g * h = f := by
    simpa [g, h] using
      (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha
  have hfactor' : g' * h' = f := by
    simpa [g', h'] using
      (mul_divByMonic_eq_iff_isRoot (p := f) (a := b)).2 hb
  have hh : h.Monic := hg.of_mul_monic_left (by rw [hfactor]; exact hf)
  have hh' : h'.Monic := hg'.of_mul_monic_left (by rw [hfactor']; exact hf)
  have hresa : rho a = rho a0 := by
    rw [← sub_eq_zero, ← map_sub]
    change IsLocalRing.residue A (a - a0) = 0
    exact (IsLocalRing.residue_eq_zero_iff _).2 ha0
  have hresb : rho b = rho a0 := by
    rw [← sub_eq_zero, ← map_sub]
    change IsLocalRing.residue A (b - a0) = 0
    exact (IsLocalRing.residue_eq_zero_iff _).2 hb0
  have hgmap : g.map rho = X - C (rho a0) := by
    simp [g, hresa]
  have hgmap' : g'.map rho = X - C (rho a0) := by
    simp [g', hresb]
  have hhmap : h.map rho = h'.map rho := by
    have hmaps := congrArg (Polynomial.map rho)
      (hfactor.trans hfactor'.symm)
    rw [Polynomial.map_mul, Polynomial.map_mul] at hmaps
    rw [hgmap, hgmap'] at hmaps
    exact (monic_X_sub_C (rho a0)).isRegular.left hmaps
  have hderiv : (f.map rho).derivative.eval (rho a0) ≠ 0 := by
    simpa [derivative_map] using (hsimple.map rho).ne_zero
  have hcoprime : IsCoprime (g.map rho) (h.map rho) := by
    have hc := isCoprime_of_is_root_of_eval_derivative_ne_zero
      (f.map rho) (rho a0) hderiv
    have hhdiv : h.map rho =
        f.map rho /ₘ (X - C (rho a0)) := by
      change (f /ₘ g).map rho = _
      rw [map_divByMonic rho hg, hgmap]
    simpa [hgmap, hhdiv] using hc
  have heq := monic_unique_residue
    hg hh hg' hh' (hfactor.trans hfactor'.symm)
    (hgmap.trans hgmap'.symm) hhmap hcoprime
  have hcoeff := congrArg (fun q : A[X] => q.coeff 0) heq.1
  exact (by simpa [g, g'] using hcoeff : a = b).symm

end LocalRing

end Submission.NumberTheory.Milne
