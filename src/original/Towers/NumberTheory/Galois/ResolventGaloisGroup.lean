import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.FieldTheory.PolynomialGaloisGroup


/-!
# Milne, Chapter 8, Theorem 8.20

Milne's resolvent construction recovers a permutation Galois group as the
stabilizer of one irreducible factor of the full resolvent polynomial.  The
factor containing the original linear form is its orbit polynomial under the
Galois subgroup.  The theorem below records the group-theoretic algebraic core:
provided that the stabilizer of that linear form is already contained in the
subgroup, the stabilizer of its orbit polynomial is exactly the subgroup.

For the usual linear form `theta = sum alpha_i * t_i`, distinct labelled roots
make its stabilizer trivial.  A different irreducible factor is a translate of
this one and therefore has a conjugate stabilizer, as expected when the roots
are relabelled.
-/

namespace Towers.NumberTheory.Milne

open MulAction Polynomial
open scoped BigOperators

noncomputable section

variable {G E : Type*} [Group G] [Finite G] [CommRing E] [IsDomain E]
  [MulSemiringAction G E]

/-- Milne's full resolvent polynomial: its roots, with multiplicity, are all
the translates of `theta` by the ambient permutation group. -/
def fullResolventPolynomial (theta : E) : E[X] :=
  letI := Fintype.ofFinite G
  (Finset.univ : Finset G).prod fun g => X - C (g • theta)

/-- The factor of the full resolvent belonging to a subgroup `H`.  In the
Galois application, `H` is the image of the Galois group in the permutation
group of the labelled roots. -/
def galoisResolventFactor (H : Subgroup G) (theta : E) : E[X] :=
  by
    classical
    letI := Fintype.ofFinite G
    exact (Finset.univ : Finset H).prod fun h => X - C (h.1 • theta)

omit [IsDomain E] in
/-- The Galois-orbit factor is an actual factor of the full resolvent. -/
theorem galois_resolvent_full
    (H : Subgroup G) (theta : E) :
    galoisResolventFactor H theta ∣ fullResolventPolynomial (G := G) theta := by
  classical
  letI := Fintype.ofFinite G
  refine ⟨(Finset.univ : Finset {g : G // g ∉ H}).prod
    (fun g => X - C (g.1 • theta)), ?_⟩
  simpa only [fullResolventPolynomial, galoisResolventFactor] using
    (Fintype.prod_subtype_mul_prod_subtype (fun g : G => g ∈ H)
      (fun g => X - C (g • theta))).symm

omit [IsDomain E] in
/-- The orbit factor is fixed by every element of the subgroup that defines
it. -/
private theorem smul_resolvent_factor
    (H : Subgroup G) (theta : E) (h : H) :
    h.1 • galoisResolventFactor H theta = galoisResolventFactor H theta := by
  classical
  letI := Fintype.ofFinite G
  change h.1 • (Finset.univ.prod fun g : H => X - C (g.1 • theta)) =
    Finset.univ.prod fun g : H => X - C (g.1 • theta)
  rw [Finset.smul_prod']
  exact Fintype.prod_bijective (Equiv.mulLeft h) (Equiv.mulLeft h).bijective
    (fun g : H => h.1 • (X - C (g.1 • theta)))
    (fun g : H => X - C (g.1 • theta)) (fun g => by
      simp only [Equiv.coe_mulLeft, smul_sub, Polynomial.smul_X,
        Polynomial.smul_C, mul_smul, Subgroup.coe_mul])

/-- Milne, Theorem 8.20 in full-resolvent form: if every ambient symmetry
fixing `theta` already lies in `H`, then the factor of the full resolvent
formed from the `H`-translates of `theta` has stabilizer exactly `H`. -/
theorem stabilizer_resolvent_factor
    (H : Subgroup G) (theta : E) (htheta : stabilizer G theta ≤ H) :
    stabilizer G (galoisResolventFactor H theta) = H := by
  classical
  letI := Fintype.ofFinite G
  apply le_antisymm
  · intro g hg
    have hthetaRoot : (galoisResolventFactor H theta).eval theta = 0 := by
      simp only [galoisResolventFactor, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Finset.prod_eq_zero_iff]
      exact ⟨1, Finset.mem_univ _, by simp⟩
    have hroot : (galoisResolventFactor H theta).eval (g • theta) = 0 := by
      calc
        (galoisResolventFactor H theta).eval (g • theta) =
            (g • galoisResolventFactor H theta).eval (g • theta) := by rw [hg]
        _ = g • (galoisResolventFactor H theta).eval theta :=
          Polynomial.smul_eval_smul E g (galoisResolventFactor H theta) theta
        _ = 0 := by rw [hthetaRoot, smul_zero]
    simp only [galoisResolventFactor, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff] at hroot
    obtain ⟨h, -, hroot⟩ := hroot
    have hfix : h.1⁻¹ * g ∈ stabilizer G theta := by
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
      simpa only [sub_eq_zero] using hroot
    have hmem : h.1 * (h.1⁻¹ * g) ∈ H := H.mul_mem h.2 (htheta hfix)
    simpa only [mul_assoc, mul_inv_cancel_left] using hmem
  · intro h hh
    rw [mem_stabilizer_iff]
    exact smul_resolvent_factor H theta ⟨h, hh⟩

/-- The orbit factor used in the classical Galois resolvent: its roots are the
distinct elements in the `H`-orbit of `theta`. -/
def resolventFactor (H : Subgroup G) (theta : E) : E[X] :=
  letI := Fintype.ofFinite H
  prodXSubSMul H E theta

/-- Milne, Theorem 8.20, in its intrinsic resolvent form: the permutations
fixing the orbit factor are precisely the chosen Galois subgroup.

The hypothesis says that any ambient permutation fixing the chosen linear
form already belongs to `H`.  In the classical construction this follows from
the distinctness of the labelled roots. -/
theorem stabilizer_resolvent (H : Subgroup G) (theta : E)
    (htheta : stabilizer G theta <= H) :
    stabilizer G (resolventFactor H theta) = H := by
  letI := Fintype.ofFinite H
  apply le_antisymm
  · intro g hg
    have hthetaRoot : (resolventFactor H theta).eval theta = 0 := by
      simpa only [resolventFactor] using prodXSubSMul.eval H E theta
    have hroot : (resolventFactor H theta).eval (g • theta) = 0 := by
      calc
        (resolventFactor H theta).eval (g • theta) =
            (g • resolventFactor H theta).eval (g • theta) := by rw [hg]
        _ = g • (resolventFactor H theta).eval theta :=
          Polynomial.smul_eval_smul E g (resolventFactor H theta) theta
        _ = 0 := by rw [hthetaRoot, smul_zero]
    simp only [resolventFactor, prodXSubSMul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff] at hroot
    obtain ⟨q, -, hq⟩ := hroot
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hfix : h.1⁻¹ * g ∈ stabilizer G theta := by
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
      simpa only [Subgroup.smul_def, sub_eq_zero] using hq
    have hmem : h.1 * (h.1⁻¹ * g) ∈ H := H.mul_mem h.2 (htheta hfix)
    simpa only [mul_assoc, mul_inv_cancel_left] using hmem
  · intro g hg
    rw [mem_stabilizer_iff]
    change g • prodXSubSMul H E theta = _
    simpa only [Subgroup.smul_def] using prodXSubSMul.smul H E theta ⟨g, hg⟩

section VariablePermutation

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The action denoted `sigma_t` by Milne: a permutation acts on a
multivariable polynomial by permuting its variables. -/
noncomputable instance mvVariablePermutation :
    MulSemiringAction (Equiv.Perm ι) (MvPolynomial ι R) where
  smul sigma f := MvPolynomial.rename sigma f
  one_smul f := by
    change MvPolynomial.rename (1 : Equiv.Perm ι) f = f
    simpa only [Equiv.Perm.coe_one] using MvPolynomial.rename_id_apply f
  mul_smul sigma tau f := by
    change MvPolynomial.rename (sigma * tau) f =
      MvPolynomial.rename sigma (MvPolynomial.rename tau f)
    simpa only [Equiv.Perm.coe_mul] using
      (MvPolynomial.rename_rename tau sigma f).symm
  smul_zero sigma := map_zero (MvPolynomial.rename sigma)
  smul_add sigma f g := map_add (MvPolynomial.rename sigma) f g
  smul_one sigma := map_one (MvPolynomial.rename sigma)
  smul_mul sigma f g := map_mul (MvPolynomial.rename sigma) f g

/-- Milne's labelled linear form `theta = sum alpha_i t_i`. -/
def resolventLinearForm (alpha : ι → R) : MvPolynomial ι R :=
  ∑ i, MvPolynomial.C (alpha i) * MvPolynomial.X i

@[simp]
theorem coeff_resolvent_form (alpha : ι → R) (i : ι) :
    MvPolynomial.coeff (Finsupp.single i 1) (resolventLinearForm alpha) = alpha i := by
  classical
  change (MvPolynomial.coeffAddMonoidHom (Finsupp.single i 1))
    (∑ j, MvPolynomial.C (alpha j) * MvPolynomial.X j) = alpha i
  rw [map_sum]
  simp [MvPolynomial.coeff_X', Finsupp.single_eq_single_iff]

@[simp]
theorem resolvent_linear_form (sigma : Equiv.Perm ι) (alpha : ι → R) :
    sigma • resolventLinearForm alpha =
      ∑ i, MvPolynomial.C (alpha i) * MvPolynomial.X (sigma i) := by
  change MvPolynomial.rename sigma (resolventLinearForm alpha) = _
  simp [resolventLinearForm]

/-- Permuting the variables relabels the coefficients by the inverse
permutation. -/
theorem smul_resolvent_form (sigma : Equiv.Perm ι) (alpha : ι → R) :
    sigma • resolventLinearForm alpha =
      resolventLinearForm (alpha ∘ sigma.symm) := by
  rw [resolvent_linear_form]
  simpa [resolventLinearForm] using
    (Equiv.sum_comp sigma
      (fun i => MvPolynomial.C (alpha (sigma.symm i)) * MvPolynomial.X i))

/-- Distinct labels make Milne's linear form a free point for the variable
permutation action. -/
theorem stabilizer_resolvent_bot (alpha : ι → R)
    (halpha : Function.Injective alpha) :
    stabilizer (Equiv.Perm ι) (resolventLinearForm alpha) = ⊥ := by
  apply le_antisymm
  · intro sigma hsigma
    rw [Subgroup.mem_bot]
    apply Equiv.ext
    intro i
    have hpoly : resolventLinearForm (alpha ∘ sigma.symm) =
        resolventLinearForm alpha := by
      rw [← smul_resolvent_form]
      exact mem_stabilizer_iff.mp hsigma
    have hcoeff := congrArg
      (MvPolynomial.coeff (Finsupp.single i 1)) hpoly
    simp only [coeff_resolvent_form, Function.comp_apply] at hcoeff
    have hinv : sigma.symm i = i := halpha hcoeff
    have happly := congrArg sigma hinv
    simpa using happly.symm
  · exact bot_le

/-- Milne's Theorem 8.20 for the factor containing the original labelled
linear form: its stabilizer in the full symmetric group is exactly `H`.

In the application, `alpha` lists the distinct roots of the separable
polynomial and `H` is its permutation Galois group. -/
theorem stabilizer_resolvent_form [IsDomain R]
    (H : Subgroup (Equiv.Perm ι)) (alpha : ι → R)
    (halpha : Function.Injective alpha) :
    stabilizer (Equiv.Perm ι)
      (resolventFactor H (resolventLinearForm alpha)) = H := by
  apply stabilizer_resolvent
  rw [stabilizer_resolvent_bot alpha halpha]
  exact bot_le

/-- Milne, Theorem 8.20 in the explicit full-resolvent formulation.  For a
list of distinct labelled roots and a permutation Galois subgroup `H`, the
full symmetric resolvent has a factor whose stabilizer is exactly `H`. -/
theorem resolvent_factor_stabilizer [IsDomain R]
    (H : Subgroup (Equiv.Perm ι)) (alpha : ι → R)
    (halpha : Function.Injective alpha) :
    ∃ F₁ : (MvPolynomial ι R)[X],
      F₁ ∣ fullResolventPolynomial
        (G := Equiv.Perm ι) (resolventLinearForm alpha) ∧
      stabilizer (Equiv.Perm ι) F₁ = H := by
  refine ⟨galoisResolventFactor H (resolventLinearForm alpha),
    galois_resolvent_full H _, ?_⟩
  apply stabilizer_resolvent_factor
  rw [stabilizer_resolvent_bot alpha halpha]
  exact bot_le

/-- Theorem 8.20 phrased for a permutation representation: a factor of the
full resolvent recovers exactly the image of the represented group.  Taking
`A` to be the Galois group and `rho` its action on the roots gives Milne's
permutation Galois group. -/
theorem full_resolvent_stabilizer [IsDomain R]
    {A : Type*} [Group A] (rho : A →* Equiv.Perm ι)
    (alpha : ι → R) (halpha : Function.Injective alpha) :
    ∃ F₁ : (MvPolynomial ι R)[X],
      F₁ ∣ fullResolventPolynomial
        (G := Equiv.Perm ι) (resolventLinearForm alpha) ∧
      stabilizer (Equiv.Perm ι) F₁ = rho.range :=
  resolvent_factor_stabilizer rho.range alpha halpha

end VariablePermutation

section PolynomialGaloisGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The resolvent stabilizer construction specialized to the actual Galois
group of a polynomial.  The resulting stabilizer is the faithful permutation
image of `Polynomial.Gal p` on the roots in `L`, and hence is isomorphic to
that Galois group.

The base-field descent is proved in `ResolventFactorDescent`; irreducibility
of the descended orbit factor is the remaining external van der Waerden
result cited by Milne. -/
theorem full_resolvent_gal
    (p : K[X]) [Fact ((p.map (algebraMap K L)).Splits)] :
    ∃ F₁ : (MvPolynomial (p.rootSet L) L)[X],
      F₁ ∣ fullResolventPolynomial
          (G := Equiv.Perm (p.rootSet L))
          (resolventLinearForm fun x : p.rootSet L ↦ (x : L)) ∧
      stabilizer (Equiv.Perm (p.rootSet L)) F₁ =
          (Polynomial.Gal.galActionHom p L).range ∧
      Nonempty
        (p.Gal ≃*
          stabilizer (Equiv.Perm (p.rootSet L)) F₁) := by
  let rho := Polynomial.Gal.galActionHom p L
  obtain ⟨F₁, hdiv, hstab⟩ :=
    full_resolvent_stabilizer rho
      (fun x : p.rootSet L ↦ (x : L)) Subtype.val_injective
  refine ⟨F₁, hdiv, hstab, ?_⟩
  let eRange : p.Gal ≃* rho.range :=
    MonoidHom.ofInjective (Polynomial.Gal.galActionHom_injective p L)
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hstab.symm)⟩

end PolynomialGaloisGroup

end

end Towers.NumberTheory.Milne
