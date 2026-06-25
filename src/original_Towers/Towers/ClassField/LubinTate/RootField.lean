import Towers.ClassField.LubinTate.RingUnitsCard

/-!
# The distinguished root field of a Lubin--Tate level

Milne constructs `K_{pi,n}` by first choosing a compatible nonzero torsion
point `pi_n`.  Its minimal polynomial is the reduced Lubin--Tate iterate
`f^[n]`, an Eisenstein polynomial of degree `(q - 1) * q ^ (n - 1)`.

This file constructs the corresponding field unconditionally as an
`AdjoinRoot` and identifies its roots with its field embeddings.  The
companion adic file proves that the reduced polynomial splits here and that
the extension is Galois.  The companion Galois-action file proves that the
explicit quotient-unit correspondence is multiplicative, hence that the
Galois group is abelian, as asserted in Theorem I.3.6(b).
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups

universe u v

/-- The polynomial data used in Milne's construction of a finite
Lubin--Tate level. -/
structure LTDatum
    (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] where
  pi : A
  q : ℕ
  residueCard : Nat.card (A ⧸ Ideal.span {pi}) = q
  f : A[X]
  pi_irreducible : Irreducible pi
  f_monic : f.Monic
  f_natDegree : f.natDegree = q
  one_lt_q : 1 < q
  lubinTateSeries : LubinSeries pi q (f : PowerSeries A)

namespace LTDatum

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-- The residue-cardinality condition in the datum implies that the residue
ring really is finite. -/
@[reducible]
noncomputable def finiteResidue (D : LTDatum A) :
    Finite (A ⧸ Ideal.span {D.pi}) := by
  apply Nat.finite_of_card_ne_zero
  rw [D.residueCard]
  exact Nat.ne_of_gt (lt_trans Nat.zero_lt_one D.one_lt_q)

/-- The cardinality stored in the polynomial datum agrees with the concrete
`Fintype.card` used by the formal Lubin--Tate module construction. -/
theorem lubin_tate_card
    (D : LTDatum A)
    [Fintype (A ⧸ Ideal.span {D.pi})] :
    LubinSeries D.pi
      (Fintype.card (A ⧸ Ideal.span {D.pi}))
      (D.f : PowerSeries A) := by
  rw [← Nat.card_eq_fintype_card, D.residueCard]
  exact D.lubinTateSeries

/-- The quotient-unit count in exactly the indexing of the concrete root
field: both sides have cardinality `(q - 1) * q ^ n`. -/
theorem card_quotientUnits (D : LTDatum A) (n : ℕ) :
    Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
      (D.q - 1) * D.q ^ n := by
  letI := D.finiteResidue
  simpa only [D.residueCard] using
    card_units_succ D.pi_irreducible n

/-- Milne's reduced level-`n + 1` polynomial, with coefficients extended
from the valuation ring `A` to its fraction field `K`. -/
def reducedPolynomial (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] (n : ℕ) : K[X] :=
  (reducedLubinIterate D.f n).map (algebraMap A K)

/-- The full level-`n + 1` Lubin--Tate torsion polynomial. -/
def torsionPolynomial (D : LTDatum A)
    (K : Type v) [Field K] [Algebra A K] (n : ℕ) : K[X] :=
  (D.f.comp^[n + 1] X).map (algebraMap A K)

variable (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsFractionRing A K] in
/-- The reduced level polynomial is monic. -/
theorem reducedPolynomial_monic (n : ℕ) :
    (D.reducedPolynomial K n).Monic := by
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  have hfdeg : D.f.natDegree ≠ 0 := by
    have hq := D.one_lt_q
    rw [D.f_natDegree]
    omega
  exact (reduced_iterate_monic D.f_monic hf0
    hfdeg n).map _

omit [IsFractionRing A K] in
/-- The full torsion polynomial factors as the preceding iterate times the
reduced level polynomial.  Thus the nonzero roots at level `n + 1` are among
the roots of the reduced polynomial. -/
theorem torsionPolynomial_factor (n : ℕ) :
    D.torsionPolynomial K n =
      (D.f.comp^[n] X).map (algebraMap A K) *
        D.reducedPolynomial K n := by
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  have hmul : X * D.f.divX = D.f := by
    simpa only [hf0, C_0, add_zero] using Polynomial.X_mul_divX_add D.f
  have hfactor :
      D.f.comp (D.f.comp^[n] X) =
        (D.f.comp^[n] X) * D.f.divX.comp (D.f.comp^[n] X) := by
    calc
      D.f.comp (D.f.comp^[n] X) =
          (X * D.f.divX).comp (D.f.comp^[n] X) :=
        congrArg (fun p : A[X] ↦ p.comp (D.f.comp^[n] X)) hmul.symm
      _ = (D.f.comp^[n] X) *
          D.f.divX.comp (D.f.comp^[n] X) := by
        rw [Polynomial.mul_comp, Polynomial.X_comp]
  rw [torsionPolynomial, Function.iterate_succ_apply', hfactor,
    Polynomial.map_mul]
  rfl

/-- The reduced level polynomial is Eisenstein, hence irreducible over the
fraction field. -/
theorem reducedPolynomial_irreducible (n : ℕ) :
    Irreducible (D.reducedPolynomial K n) := by
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  have hf1 : D.f.coeff 1 = D.pi := by
    simpa using D.lubinTateSeries.2.1
  have hmod : D.f.map (Ideal.Quotient.mk (Ideal.span {D.pi})) =
      X ^ D.q := by
    apply Polynomial.coe_injective
    simpa only [Polynomial.polynomial_map_coe, Polynomial.coe_X,
      Polynomial.coe_pow] using D.lubinTateSeries.2.2
  exact reduced_iterate_irreducible
    D.pi_irreducible D.f_monic hf0 hf1 D.f_natDegree
      D.one_lt_q hmod n

instance reduced_polynomial_fact (n : ℕ) :
    Fact (Irreducible (D.reducedPolynomial K n)) :=
  ⟨D.reducedPolynomial_irreducible K n⟩

/-- The field generated by a distinguished nonzero level-`n + 1`
Lubin--Tate torsion point. -/
def RootField (n : ℕ) : Type v :=
  AdjoinRoot (D.reducedPolynomial K n)

noncomputable instance rootFieldField (n : ℕ) : Field (D.RootField K n) := by
  change Field (AdjoinRoot (D.reducedPolynomial K n))
  infer_instance

instance rootFieldAlgebra (n : ℕ) : Algebra K (D.RootField K n) := by
  change Algebra K (AdjoinRoot (D.reducedPolynomial K n))
  infer_instance

instance rootFieldDimensional (n : ℕ) :
    FiniteDimensional K (D.RootField K n) := by
  change Module.Finite K (AdjoinRoot (D.reducedPolynomial K n))
  exact (D.reducedPolynomial_monic K n).finite_adjoinRoot

/-- The distinguished root `pi_(n+1)`. -/
def root (n : ℕ) : D.RootField K n :=
  AdjoinRoot.root (D.reducedPolynomial K n)

/-- The distinguished element is a root of the reduced level polynomial. -/
theorem aeval_root (n : ℕ) :
    Polynomial.aeval (D.root K n) (D.reducedPolynomial K n) = 0 := by
  exact AdjoinRoot.eval₂_root (D.reducedPolynomial K n)

/-- The constant coefficient of the reduced level polynomial is the chosen
uniformizer. -/
theorem reduced_coeff_zero (n : ℕ) :
    (D.reducedPolynomial K n).coeff 0 = algebraMap A K D.pi := by
  have hf0 : D.f.coeff 0 = 0 := by
    simpa using D.lubinTateSeries.1
  rw [reducedPolynomial, Polynomial.coeff_map,
    reduced_iterate_coeff D.f hf0]
  simpa using D.lubinTateSeries.2.1

/-- The distinguished root is nonzero, so it is genuinely a level-`n + 1`
torsion point rather than the common zero root of all iterates. -/
theorem root_ne_zero (n : ℕ) : D.root K n ≠ 0 := by
  intro hroot
  have heval := D.aeval_root K n
  rw [hroot] at heval
  have hconstant : (D.reducedPolynomial K n).coeff 0 = 0 := by
    simpa [Polynomial.aeval_def] using heval
  rw [D.reduced_coeff_zero K n] at hconstant
  exact D.pi_irreducible.ne_zero
    (IsFractionRing.injective A K (hconstant.trans (map_zero _).symm))

/-- The distinguished root is a root of the full level-`n + 1` iterate, so
it defines an actual Lubin--Tate torsion point at that level. -/
theorem aeval_torsion_root (n : ℕ) :
    Polynomial.aeval (D.root K n) (D.torsionPolynomial K n) = 0 := by
  rw [D.torsionPolynomial_factor K n, map_mul, D.aeval_root K n, mul_zero]

/-- The distinguished root has exact level `n + 1`: it is not killed by the
preceding `n`-fold iterate.  Together with `aeval_torsion_root`,
this is the primitive-torsion input needed for the future quotient-unit
action on the root. -/
theorem aeval_previous_iterate (n : ℕ) :
    Polynomial.aeval (D.root K n)
      ((D.f.comp^[n] X).map (algebraMap A K)) ≠ 0 := by
  let fK : K[X] := D.f.map (algebraMap A K)
  have hiter :
      (D.f.comp^[n] X).map (algebraMap A K) = fK.comp^[n] X := by
    exact iterate_x (algebraMap A K) D.f n
  have hreduced :
      D.reducedPolynomial K n = reducedLubinIterate fK n := by
    exact lubin_tate_iterate (algebraMap A K) D.f n
  intro hprevious
  rw [hiter] at hprevious
  have hroot := D.aeval_root K n
  rw [hreduced, reducedLubinIterate, Polynomial.aeval_comp,
    hprevious] at hroot
  have hcoeffE :
      algebraMap K (D.RootField K n) (fK.coeff 1) = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  have hcoeffK : fK.coeff 1 = 0 := by
    apply (algebraMap K (D.RootField K n)).injective
    exact hcoeffE.trans (map_zero _).symm
  have hpiK : algebraMap A K D.pi = 0 := by
    rw [show fK.coeff 1 = algebraMap A K (D.f.coeff 1) by
      simp [fK]] at hcoeffK
    have hf1 : D.f.coeff 1 = D.pi := by
      simpa using D.lubinTateSeries.2.1
    rw [hf1] at hcoeffK
    exact hcoeffK
  exact D.pi_irreducible.ne_zero
    (IsFractionRing.injective A K (hpiK.trans (map_zero _).symm))

/-- The distinguished root generates its `AdjoinRoot` field. -/
theorem adjoin_root_top (n : ℕ) :
    IntermediateField.adjoin K {D.root K n} = ⊤ := by
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.adjoin_toSubalgebra,
    IntermediateField.top_toSubalgebra]
  exact AdjoinRoot.adjoinRoot_eq_top

/-- For the concrete `AdjoinRoot`, choosing the image of the distinguished
root is equivalent to choosing a root of the defining polynomial. -/
noncomputable def rootSetAlg (n : ℕ) :
    (D.reducedPolynomial K n).rootSet (D.RootField K n) ≃
      (D.RootField K n →ₐ[K] D.RootField K n) where
  toFun z := AdjoinRoot.liftAlgHom (D.reducedPolynomial K n)
    (Algebra.ofId K (D.RootField K n)) z (by
      simpa [Polynomial.aeval_def] using
        (D.reducedPolynomial_monic K n).mem_rootSet.mp z.property)
  invFun φ := ⟨φ (D.root K n),
    (D.reducedPolynomial_monic K n).mem_rootSet.mpr (by
      change Polynomial.aeval
        (φ (AdjoinRoot.root (D.reducedPolynomial K n)))
          (D.reducedPolynomial K n) = 0
      exact AdjoinRoot.aeval_algHom_eq_zero
        (D.reducedPolynomial K n) φ)⟩
  left_inv z := by
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv φ := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem root_set_alg
    (n : ℕ) (z : (D.reducedPolynomial K n).rootSet (D.RootField K n)) :
    D.rootSetAlg K n z (D.root K n) = z := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Since the distinguished root field is finite over `K`, its algebra
endomorphisms are automorphisms.  Thus its reduced-polynomial roots are in
canonical bijection with its `K`-automorphisms. -/
noncomputable def rootSetAut (n : ℕ) :
    (D.reducedPolynomial K n).rootSet (D.RootField K n) ≃
      (D.RootField K n ≃ₐ[K] D.RootField K n) :=
  (D.rootSetAlg K n).trans (algEquivEquivAlgHom K
    (D.RootField K n)).symm

@[simp]
theorem root_set_aut
    (n : ℕ) (z : (D.reducedPolynomial K n).rootSet (D.RootField K n)) :
    D.rootSetAut K n z (D.root K n) = z := by
  have hhom :
      ((algEquivEquivAlgHom K (D.RootField K n)).symm
        (D.rootSetAlg K n z)).toAlgHom =
          D.rootSetAlg K n z :=
    (algEquivEquivAlgHom K (D.RootField K n)).apply_symm_apply _
  calc
    D.rootSetAut K n z (D.root K n) =
        ((algEquivEquivAlgHom K (D.RootField K n)).symm
          (D.rootSetAlg K n z)).toAlgHom (D.root K n) := rfl
    _ = D.rootSetAlg K n z (D.root K n) := by rw [hhom]
    _ = z := D.root_set_alg K n z

omit [IsFractionRing A K] in
/-- The reduced level polynomial has Milne's asserted degree
`(q - 1) * q ^ n`; this is level `n + 1` in the book's indexing. -/
theorem reduced_nat_degree (n : ℕ) :
    (D.reducedPolynomial K n).natDegree = (D.q - 1) * D.q ^ n := by
  have hfdeg : D.f.natDegree ≠ 0 := by
    have hq := D.one_lt_q
    rw [D.f_natDegree]
    omega
  calc
    (D.reducedPolynomial K n).natDegree =
        (reducedLubinIterate D.f n).natDegree :=
      (reduced_iterate_monic D.f_monic
        (by simpa using D.lubinTateSeries.1) hfdeg n).natDegree_map _
    _ = (D.q - 1) * D.q ^ n := by
      rw [reduced_iterate_degree, D.f_natDegree]

/-- The distinguished root field has Milne's asserted degree
`(q - 1) * q ^ n`; this is level `n + 1` in the book's indexing. -/
theorem finrank_rootField (n : ℕ) :
    Module.finrank K (D.RootField K n) = (D.q - 1) * D.q ^ n := by
  change Module.finrank K
      (K[X] ⧸ Ideal.span {D.reducedPolynomial K n}) = _
  rw [finrank_quotient_span_eq_natDegree,
    D.reduced_nat_degree K n]

/-- The quotient-unit group expected to act on the distinguished level has
cardinality equal to the degree of the concrete root field. -/
theorem card_units_finrank (n : ℕ) :
    Nat.card (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ =
      Module.finrank K (D.RootField K n) := by
  rw [D.card_quotientUnits n, D.finrank_rootField K n]

/-- Theorem I.3.6(c) for the concrete distinguished root field: the chosen
uniformizer is a field norm. -/
theorem norm_uniformizer (n : ℕ) :
    ∃ y : D.RootField K n,
      Algebra.norm K y = algebraMap A K D.pi := by
  exact algebra_uniformizer_generates
    D.pi_irreducible D.f_monic D.f_natDegree D.one_lt_q
      D.lubinTateSeries n (D.root K n) (D.aeval_root K n)
      (D.adjoin_root_top K n)

/-- In the concrete adjoining-root presentation, the negative distinguished
root itself has norm equal to the chosen uniformizer.  The negation cancels
the sign in the constant-coefficient norm formula. -/
theorem norm_neg_uniformizer (n : ℕ) :
    Algebra.norm K (-D.root K n) = algebraMap A K D.pi := by
  let f := D.reducedPolynomial K n
  let pb : PowerBasis K (D.RootField K n) :=
    AdjoinRoot.powerBasis (D.reducedPolynomial_monic K n).ne_zero
  have hmin : minpoly K pb.gen = f := by
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (D.reducedPolynomial_monic K n)
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hmin, D.reduced_coeff_zero K n] at hnorm
  have hroot : pb.gen = D.root K n := rfl
  rw [show -D.root K n = algebraMap K (D.RootField K n) (-1) * pb.gen by
      rw [hroot]
      simp,
    (Algebra.norm K).map_mul, Algebra.norm_algebraMap, hnorm, pb.finrank,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end LTDatum

end

end Towers.CField.LTate
