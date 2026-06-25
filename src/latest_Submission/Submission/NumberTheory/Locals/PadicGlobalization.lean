import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicNumbers
import Submission.NumberTheory.Locals.PolynomialStability

/-!
# Rational approximation of p-adic polynomials

This file formalizes the coefficient-approximation step in Milne, Corollary
7.62.  A monic polynomial over `ℚ_[p]` can be approximated coefficientwise
by a monic polynomial over `ℚ`, without changing its degree.  Combined with
the stability theorem of Proposition 7.61, this is the algebraic engine that
produces the global polynomial in Milne's proof.
-/

namespace Submission.NumberTheory.Milne

open Polynomial IntermediateField

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient-approximation core of Milne, Corollary 7.62.

Every monic p-adic polynomial admits a rational polynomial of the same degree
whose p-adic scalar extension is uniformly coefficientwise close.  The leading
coefficient is kept equal to `1`; only the finitely many lower coefficients are
approximated using density of `ℚ` in `ℚ_[p]`. -/
theorem rational_monic_close
    (f : Polynomial ℚ_[p]) (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Polynomial ℚ,
      g.Monic ∧
      g.natDegree = f.natDegree ∧
      ∀ i : ℕ, ‖(g.map (Rat.castHom ℚ_[p])).coeff i - f.coeff i‖ < ε := by
  let n := f.natDegree
  have happrox : ∀ i : Fin n, ∃ q : ℚ, ‖f.coeff i - (q : ℚ_[p])‖ < ε := by
    intro i
    exact Padic.rat_dense p (f.coeff i) hε
  choose q hq using happrox
  let lower : Polynomial ℚ := Polynomial.ofFn n q
  let g : Polynomial ℚ := X ^ n + lower
  have hlowerDegree : lower.degree < n := by
    exact Polynomial.ofFn_degree_lt q
  have hgMonic : g.Monic := by
    exact Polynomial.monic_X_pow_add hlowerDegree
  have hgDegree : g.natDegree = n := by
    have hlowerDegree' : lower.degree < (X ^ n : Polynomial ℚ).degree := by
      simpa using hlowerDegree
    change (X ^ n + lower).natDegree = n
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt hlowerDegree',
      Polynomial.natDegree_X_pow]
  refine ⟨g, hgMonic, hgDegree.trans rfl, ?_⟩
  intro i
  by_cases hi : i < n
  · have hqi := hq ⟨i, hi⟩
    simpa [g, lower, Polynomial.coeff_map, Polynomial.coeff_X_pow,
      Polynomial.ofFn_coeff_eq_val_of_lt, hi, ne_of_lt hi, norm_sub_rev] using hqi
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    rcases hni.eq_or_lt with rfl | hlt
    · have hfLeading : f.coeff n = 1 := by
        simpa [n] using hf.coeff_natDegree
      simp [g, lower, Polynomial.coeff_map, Polynomial.coeff_X_pow,
        Polynomial.ofFn_coeff_eq_zero_of_ge, hfLeading, hε]
    · have hfZero : f.coeff i = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [n] using hlt)
      simp [g, lower, Polynomial.coeff_map, Polynomial.coeff_X_pow,
        Polynomial.ofFn_coeff_eq_zero_of_ge, hlt.le, hlt.ne', hfZero, hε]

section Stability

variable {Ω : Type*} [NormedField Ω] [NormedAlgebra ℚ_[p] Ω]
  [Algebra.IsAlgebraic ℚ_[p] Ω] [IsGalois ℚ_[p] Ω]

/-- Rational form of the quantitative stability theorem used in Milne,
Corollary 7.62.

Under the explicit hypotheses of Proposition 7.61, a rational approximation
is irreducible already over `ℚ`; its root field has the expected global degree,
and after mapping coefficients to `ℚ_[p]` its roots generate exactly the same
p-adic intermediate fields as the roots of the original polynomial. -/
theorem rational_stability_close
    (hna : IsNonarchimedean (norm : Ω → ℝ))
    {f : Polynomial ℚ_[p]} (hfi : Irreducible f) (hfm : f.Monic)
    (g : Polynomial ℚ) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hfs : (f.map (algebraMap ℚ_[p] Ω)).Splits)
    (hgs : ((g.map (Rat.castHom ℚ_[p])).map (algebraMap ℚ_[p] Ω)).Splits)
    {ε : ℝ} (hε : 0 < ε)
    (hcoeff : ∀ i : ℕ, ‖(g.map (Rat.castHom ℚ_[p])).coeff i - f.coeff i‖ < ε)
    (hsep : ∀ α ∈ f.aroots Ω, ∀ α' ∈ f.aroots Ω, α' ≠ α →
      rootApproximationScale f.natDegree ε
        (commonCauchyBound Ω f (g.map (Rat.castHom ℚ_[p]))) < ‖α' - α‖) :
    Irreducible g ∧
      Module.finrank ℚ (AdjoinRoot g) = f.natDegree ∧
      (∀ β ∈ (g.map (Rat.castHom ℚ_[p])).aroots Ω, ∃! α : Ω,
        α ∈ f.aroots Ω ∧
          ‖α - β‖ < rootApproximationScale f.natDegree ε
            (commonCauchyBound Ω f (g.map (Rat.castHom ℚ_[p]))) ∧
          IntermediateField.adjoin ℚ_[p] {α} = IntermediateField.adjoin ℚ_[p] {β}) ∧
      {E : IntermediateField ℚ_[p] Ω |
        ∃ α ∈ f.aroots Ω, E = IntermediateField.adjoin ℚ_[p] {α}} =
        {E : IntermediateField ℚ_[p] Ω |
          ∃ β ∈ (g.map (Rat.castHom ℚ_[p])).aroots Ω,
            E = IntermediateField.adjoin ℚ_[p] {β}} := by
  have hgpMonic : (g.map (Rat.castHom ℚ_[p])).Monic := hgm.map _
  have hgpDegree : (g.map (Rat.castHom ℚ_[p])).natDegree = f.natDegree :=
    (hgm.natDegree_map _).trans hdeg
  have hstable := stability_close_cauchy
    (K := ℚ_[p]) (Ω := Ω) hna hfi hfm hgpMonic hgpDegree hfs hgs hε hcoeff hsep
  have hgIrreducible : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Rat.castHom ℚ_[p]) g hgm hstable.1
  have hfinrank : Module.finrank ℚ (AdjoinRoot g) = f.natDegree :=
    (AdjoinRoot.powerBasis hgIrreducible.ne_zero).finrank.trans hdeg
  exact ⟨hgIrreducible, hfinrank, hstable.2⟩

/-- Milne, Corollary 7.62, the number-field conclusion obtained from a stable
rational approximation.

For a chosen root `α` of the original p-adic polynomial, the stability
theorem supplies a root `β` of the rational approximation whose p-adic root
field is the same.  The global field `ℚ⟨β⟩` has the expected degree and,
after restricting scalars, is contained in `ℚ_[p]⟨α⟩`.  Thus the last
equality is the precise intermediate-field form of Milne's assertion
`L · ℚ_p = K`. -/
theorem rational_coeff_close
    [Algebra ℚ Ω] [IsScalarTower ℚ ℚ_[p] Ω]
    (hna : IsNonarchimedean (norm : Ω → ℝ))
    {f : Polynomial ℚ_[p]} (hfi : Irreducible f) (hfm : f.Monic)
    (g : Polynomial ℚ) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hfs : (f.map (algebraMap ℚ_[p] Ω)).Splits)
    (hgs : ((g.map (Rat.castHom ℚ_[p])).map (algebraMap ℚ_[p] Ω)).Splits)
    {ε : ℝ} (hε : 0 < ε)
    (hcoeff : ∀ i : ℕ, ‖(g.map (Rat.castHom ℚ_[p])).coeff i - f.coeff i‖ < ε)
    (hsep : ∀ α ∈ f.aroots Ω, ∀ α' ∈ f.aroots Ω, α' ≠ α →
      rootApproximationScale f.natDegree ε
        (commonCauchyBound Ω f (g.map (Rat.castHom ℚ_[p]))) < ‖α' - α‖)
    {α : Ω} (hα : α ∈ f.aroots Ω) :
    ∃ β : Ω,
      β ∈ (g.map (Rat.castHom ℚ_[p])).aroots Ω ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ {β}) = f.natDegree ∧
      IntermediateField.adjoin ℚ {β} ≤
        (IntermediateField.adjoin ℚ_[p] {α}).restrictScalars ℚ ∧
      IntermediateField.adjoin ℚ_[p] {β} = IntermediateField.adjoin ℚ_[p] {α} := by
  have hstable := rational_stability_close p hna hfi hfm
    g hgm hdeg hfs hgs hε hcoeff hsep
  have hleft : IntermediateField.adjoin ℚ_[p] {α} ∈
      {E : IntermediateField ℚ_[p] Ω |
        ∃ a ∈ f.aroots Ω, E = IntermediateField.adjoin ℚ_[p] {a}} := by
    exact ⟨α, hα, rfl⟩
  have hright : IntermediateField.adjoin ℚ_[p] {α} ∈
      {E : IntermediateField ℚ_[p] Ω |
        ∃ b ∈ (g.map (Rat.castHom ℚ_[p])).aroots Ω,
          E = IntermediateField.adjoin ℚ_[p] {b}} := by
    rw [← hstable.2.2.2]
    exact hleft
  rcases hright with ⟨β, hβ, hfield⟩
  have hβevalp : Polynomial.aeval β (g.map (Rat.castHom ℚ_[p])) = 0 :=
    (Polynomial.mem_aroots.mp hβ).2
  have hβeval : Polynomial.aeval β g = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ_[p] β g]
    exact hβevalp
  have hβint : IsIntegral ℚ β := ⟨g, hgm, hβeval⟩
  have hgmin : g = minpoly ℚ β :=
    minpoly.eq_of_irreducible_of_monic hstable.1 hβeval hgm
  refine ⟨β, hβ, ?_, ?_, hfield.symm⟩
  · rw [IntermediateField.adjoin.finrank hβint, ← hgmin, hdeg]
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change β ∈ IntermediateField.adjoin ℚ_[p] {α}
    rw [hfield]
    exact IntermediateField.mem_adjoin_simple_self ℚ_[p] β

/-- Milne, Corollary 7.62, in the canonical p-adic algebraic closure.

Once a rational monic approximation satisfies the explicit separation bound
from Proposition 7.61, it has a root `β` in `PadicAlgCl p` whose global field
has the expected degree and whose p-adic root field equals that of the chosen
root `α` of `f`.  Algebraic closedness supplies both splitting hypotheses. -/
theorem rational_cl_close
    {f : Polynomial ℚ_[p]} (hfi : Irreducible f) (hfm : f.Monic)
    (g : Polynomial ℚ) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    {ε : ℝ} (hε : 0 < ε)
    (hcoeff : ∀ i : ℕ, ‖(g.map (Rat.castHom ℚ_[p])).coeff i - f.coeff i‖ < ε)
    (hsep : ∀ α ∈ f.aroots (PadicAlgCl p),
      ∀ α' ∈ f.aroots (PadicAlgCl p), α' ≠ α →
        rootApproximationScale f.natDegree ε
          (commonCauchyBound (PadicAlgCl p) f
            (g.map (Rat.castHom ℚ_[p]))) < ‖α' - α‖)
    {α : PadicAlgCl p} (hα : α ∈ f.aroots (PadicAlgCl p)) :
    ∃ β : PadicAlgCl p,
      β ∈ (g.map (Rat.castHom ℚ_[p])).aroots (PadicAlgCl p) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ {β}) = f.natDegree ∧
      IntermediateField.adjoin ℚ {β} ≤
        (IntermediateField.adjoin ℚ_[p] {α}).restrictScalars ℚ ∧
      IntermediateField.adjoin ℚ_[p] {β} =
        IntermediateField.adjoin ℚ_[p] {α} := by
  apply rational_coeff_close
    (p := p) (Ω := PadicAlgCl p) (PadicAlgCl.isNonarchimedean p)
    hfi hfm g hgm hdeg
  · exact IsAlgClosed.splits _
  · exact IsAlgClosed.splits _
  · exact hε
  · exact hcoeff
  · exact hsep
  · exact hα

/-- Milne, Corollary 7.62, the rational globalization theorem for a chosen
root of a monic irreducible p-adic polynomial.

The proof chooses the minimum distance `δ` from `α` to its other conjugates,
approximates the coefficients of `f` by rational coefficients inside the
corresponding root-continuity radius, and applies Krasner's lemma.  The
resulting rational polynomial is irreducible, its global root field has the
same degree as `f`, and scalar extension to `ℚ_[p]` gives the original p-adic
root field. -/
theorem rational_root_field
    {f : Polynomial ℚ_[p]} (hfi : Irreducible f) (hfm : f.Monic)
    {α : PadicAlgCl p} (hα : α ∈ f.aroots (PadicAlgCl p)) :
    ∃ g : Polynomial ℚ,
      g.Monic ∧ Irreducible g ∧ g.natDegree = f.natDegree ∧
      ∃ β : PadicAlgCl p,
        β ∈ (g.map (Rat.castHom ℚ_[p])).aroots (PadicAlgCl p) ∧
        Module.finrank ℚ (IntermediateField.adjoin ℚ {β}) = f.natDegree ∧
        IntermediateField.adjoin ℚ {β} ≤
          (IntermediateField.adjoin ℚ_[p] {α}).restrictScalars ℚ ∧
        IntermediateField.adjoin ℚ_[p] {β} =
          IntermediateField.adjoin ℚ_[p] {α} := by
  have hαeval : Polynomial.aeval α f = 0 := (Polynomial.mem_aroots.mp hα).2
  have hfmin : f = minpoly ℚ_[p] α :=
    minpoly.eq_of_irreducible_of_monic hfi hαeval hfm
  have fnatdeg0 : f.natDegree ≠ 0 := hfi.natDegree_pos.ne'
  classical
  let S : Finset (PadicAlgCl p) :=
    {x ∈ (f.rootSet (PadicAlgCl p)).toFinset | x ≠ α}
  let δ : ℝ := if hS : S.Nonempty then
      Finset.min' (S.image fun x => ‖α - x‖) (Finset.image_nonempty.mpr hS)
    else 1
  have norm_sub_le : ∀ α' : PadicAlgCl p,
      IsConjRoot ℚ_[p] α α' → α ≠ α' → δ ≤ ‖α - α'‖ := by
    intro α' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x => ‖α - x‖) (‖α - α'‖)
      apply Finset.mem_image_of_mem
      simp only [minpoly.eq_of_irreducible_of_monic hfi hαeval hfm,
        Finset.mem_filter, Set.mem_toFinset, S]
      rw [← isConjRoot_iff_mem_minpoly_rootSet ⟨f, hfm, hαeval⟩]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty,
        Finset.filter_eq_empty_iff, Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet ⟨f, hfm, hαeval⟩,
        ← minpoly.eq_of_irreducible_of_monic hfi hαeval hfm] at conj
      exact (ne (hS conj).symm).elim
  have δpos : 0 < δ := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [Finset.lt_min'_iff, Finset.mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂]
      rintro α' hα'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at hα'
      rw [norm_pos_iff, sub_ne_zero]
      exact hα'.2.symm
    · linarith
  let ε : ℝ := (δ / max ‖α‖ 1) ^ f.natDegree / (f.natDegree + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    rational_monic_close p f hfm hε
  let gp : Polynomial ℚ_[p] := g.map (Rat.castHom ℚ_[p])
  have hgpm : gp.Monic := hgm.map _
  have hgpdeg : gp.natDegree = f.natDegree :=
    (hgm.natDegree_map _).trans hdeg
  obtain ⟨β, hβ, hαβ⟩ :=
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := gp) hε hαeval hfm hgpm hgpdeg
      (by simpa [gp] using hcoeff) (IsAlgClosed.splits _)
  have hαβδ : ‖α - β‖ < δ := by
    dsimp [ε] at hαβ
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
      ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hαβ
    · simpa [mul_assoc, div_mul_cancel₀ _
        (by positivity : (max ‖α‖ 1) > 0).ne'] using hαβ
    · simp [fnatdeg0]
    · positivity
  have hclose : ∀ α' : PadicAlgCl p,
      IsConjRoot ℚ_[p] α α' → α ≠ α' → ‖α - β‖ < ‖α - α'‖ := by
    intro α' hconj hne
    exact hαβδ.trans_le (norm_sub_le α' hconj hne)
  have hcore := krasner_close_complete
    hfi hfi.separable hfm hgpm hgpdeg (IsAlgClosed.splits _) hα hβ hclose
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Rat.castHom ℚ_[p]) g hgm hcore.1
  have hβevalp : Polynomial.aeval β gp = 0 :=
    (Polynomial.mem_aroots.mp hβ).2
  have hβeval : Polynomial.aeval β g = 0 := by
    have hcast : algebraMap ℚ ℚ_[p] = Rat.castHom ℚ_[p] := by
      ext q
      simp
    rw [← Polynomial.aeval_map_algebraMap ℚ_[p] β g]
    rw [hcast]
    simpa [gp] using hβevalp
  have hβint : IsIntegral ℚ β := ⟨g, hgm, hβeval⟩
  have hgmin : g = minpoly ℚ β :=
    minpoly.eq_of_irreducible_of_monic hgirr hβeval hgm
  refine ⟨g, hgm, hgirr, hdeg, β, ?_, ?_, ?_, hcore.2.symm⟩
  · simpa [gp] using hβ
  · rw [IntermediateField.adjoin.finrank hβint, ← hgmin, hdeg]
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change β ∈ IntermediateField.adjoin ℚ_[p] {α}
    rw [hcore.2]
    exact IntermediateField.mem_adjoin_simple_self ℚ_[p] β

/-- Milne, Corollary 7.62, for an arbitrary finite extension of `ℚ_[p]`
realized inside its algebraic closure.

The element `β` generates a number field contained in `K`; its global degree
equals the local degree of `K`, and adjoining `β` to `ℚ_[p]` recovers `K`.
This is the intermediate-field formulation of `L · ℚ_p = K`. -/
theorem number_globalizing_extension
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ β : PadicAlgCl p,
      Module.finrank ℚ (IntermediateField.adjoin ℚ {β}) = Module.finrank ℚ_[p] K ∧
      IntermediateField.adjoin ℚ {β} ≤ K.restrictScalars ℚ ∧
      IntermediateField.adjoin ℚ_[p] {β} = K := by
  obtain ⟨α, hαprim⟩ := Field.exists_primitive_element ℚ_[p] K
  let a : PadicAlgCl p := α
  have hαintK : IsIntegral ℚ_[p] α := IsIntegral.of_finite ℚ_[p] α
  have hαint : IsIntegral ℚ_[p] a := hαintK.map K.val
  let f : Polynomial ℚ_[p] := minpoly ℚ_[p] a
  have hfmonic : f.Monic := minpoly.monic hαint
  have hfirr : Irreducible f := minpoly.irreducible hαint
  have hαroot : a ∈ f.aroots (PadicAlgCl p) := by
    exact Polynomial.mem_aroots.mpr
      ⟨minpoly.ne_zero hαint, minpoly.aeval ℚ_[p] a⟩
  have hK : IntermediateField.adjoin ℚ_[p] {a} = K := by
    rw [← IntermediateField.lift_adjoin_simple ℚ_[p] K α, hαprim,
      IntermediateField.lift_top]
  have hfdegree : f.natDegree = Module.finrank ℚ_[p] K := by
    rw [← IntermediateField.adjoin.finrank hαint, hK]
  obtain ⟨g, -, -, -, β, -, hdegree, hle, hfield⟩ :=
    rational_root_field p hfirr hfmonic hαroot
  exact ⟨β, hdegree.trans hfdegree, hK ▸ hle, hfield.trans hK⟩

end Stability

end Submission.NumberTheory.Milne
