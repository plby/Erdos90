import Towers.NumberTheory.Galois.FrobeniusElement


/-!
# Reduction of roots and arithmetic Frobenius

This file isolates the formal compatibility used in the proof of Milne's
Theorem 8.23.  A root of a monic polynomial with coefficients in the base
ring reduces to a root of the reduced polynomial.  Moreover, reduction
intertwines an arithmetic Frobenius with the finite-field Frobenius.

When the polynomial splits in the source ring and its reduction is separable,
the root-reduction map is an equivalence.  The proof obtains injectivity by
mapping the complete multiset of roots and using the absence of repeated
roots after reduction.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDomain S]

variable {p : Ideal R} {Q : Ideal S} [p.IsPrime] [Q.IsPrime]
  [Q.LiesOver p]

attribute [local instance] Ideal.Quotient.field

/-- Reduction modulo `Q` sends roots of a monic polynomial to roots of its
reduction modulo the prime below `Q`. -/
def rootReduction (f : R[X]) (hf : f.Monic) :
    f.rootSet S → (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q) :=
  fun x => ⟨Ideal.Quotient.mk Q x, by
    rw [(hf.map (Ideal.Quotient.mk p)).mem_rootSet]
    have h := congrArg (Ideal.Quotient.mk Q) (hf.mem_rootSet.mp x.2)
    rw [map_zero] at h
    have hcomp :
        (algebraMap (R ⧸ p) (S ⧸ Q)).comp (Ideal.Quotient.mk p) =
          (Ideal.Quotient.mk Q).comp (algebraMap R S) := by
      ext r
      exact Ideal.Quotient.algebraMap_mk_of_liesOver Q p r
    exact ((f.map_aeval_eq_aeval_map hcomp x).symm.trans h)⟩

omit [IsDomain R] [p.IsPrime] in
@[simp]
theorem rootReduction_coe (f : R[X]) (hf : f.Monic) (x : f.rootSet S) :
    (rootReduction (p := p) (Q := Q) f hf x : S ⧸ Q) =
      Ideal.Quotient.mk Q x :=
  rfl

omit [IsDomain R] [p.IsPrime] in
/-- The root-reduction map is injective exactly when no two roots of `f`
coalesce modulo `Q`. -/
theorem root_reduction_injective (f : R[X]) (hf : f.Monic) :
    Function.Injective (rootReduction (p := p) (Q := Q) f hf) ↔
      ∀ x y : f.rootSet S,
        x.1 - y.1 ∈ Q → x = y := by
  constructor
  · intro hinj x y hxy
    apply hinj
    apply Subtype.ext
    exact Ideal.Quotient.eq.mpr hxy
  · intro hseparated x y hxy
    apply hseparated x y
    apply Ideal.Quotient.eq.mp
    exact congrArg Subtype.val hxy

omit [IsDomain R] [p.IsPrime] in
/-- A convenient direct form of injectivity: if distinct roots have
noncongruent reductions, root reduction is injective. -/
theorem rootReduction_injective (f : R[X]) (hf : f.Monic)
    (hseparated : ∀ x y : f.rootSet S, x ≠ y → x.1 - y.1 ∉ Q) :
    Function.Injective (rootReduction (p := p) (Q := Q) f hf) := by
  rw [root_reduction_injective]
  intro x y hxy
  by_contra hne
  exact hseparated x y hne hxy

omit [IsDomain R] [p.IsPrime] in
/-- If `f` splits over `S` and its reduction modulo the prime below `Q` is
separable, then distinct roots remain distinct modulo `Q`.

The proof maps the complete multiset of roots in `S` to the residue field.
Since the reduced polynomial is separable, that mapped multiset has no
duplicates. -/
theorem root_splits_separable
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable) :
    Function.Injective (rootReduction (p := p) (Q := Q) f hf) := by
  rw [root_reduction_injective]
  intro x y hxy
  apply Subtype.ext
  let fS : S[X] := f.map (algebraMap R S)
  have hfS : fS.Monic := hf.map (algebraMap R S)
  have hcard : fS.roots.card = fS.natDegree :=
    hsplits.natDegree_eq_card_roots.symm
  have hmaproots :
      fS.roots.map (Ideal.Quotient.mk Q) =
        (fS.map (Ideal.Quotient.mk Q)).roots :=
    hfS.roots_map_of_card_eq_natDegree (Ideal.Quotient.mk Q) hcard
  have hpoly :
      fS.map (Ideal.Quotient.mk Q) =
        (f.map (Ideal.Quotient.mk p)).map
          (algebraMap (R ⧸ p) (S ⧸ Q)) := by
    ext n
    simp only [fS, coeff_map, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hnodup : (fS.roots.map (Ideal.Quotient.mk Q)).Nodup := by
    rw [hmaproots, hpoly]
    exact nodup_roots hseparable.map
  apply Multiset.inj_on_of_nodup_map hnodup
  · rw [mem_roots hfS.ne_zero]
    simpa only [fS, IsRoot, eval_map, aeval_def] using hf.mem_rootSet.mp x.2
  · rw [mem_roots hfS.ne_zero]
    simpa only [fS, IsRoot, eval_map, aeval_def] using hf.mem_rootSet.mp y.2
  · exact Ideal.Quotient.eq.mpr hxy

omit [IsDomain R] [p.IsPrime] in
/-- If `f` splits over `S`, every root of the reduced polynomial in `S ⧸ Q`
is the reduction of a root in `S`. -/
theorem root_surjective_splits
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits) :
    Function.Surjective (rootReduction (p := p) (Q := Q) f hf) := by
  intro z
  let fS : S[X] := f.map (algebraMap R S)
  have hfS : fS.Monic := hf.map (algebraMap R S)
  have hmaproots :
      fS.roots.map (Ideal.Quotient.mk Q) =
        (fS.map (Ideal.Quotient.mk Q)).roots :=
    hfS.roots_map_of_card_eq_natDegree (Ideal.Quotient.mk Q)
      hsplits.natDegree_eq_card_roots.symm
  have hpoly :
      fS.map (Ideal.Quotient.mk Q) =
        (f.map (Ideal.Quotient.mk p)).map
          (algebraMap (R ⧸ p) (S ⧸ Q)) := by
    ext n
    simp only [fS, coeff_map, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hzroots :
      z.1 ∈ ((f.map (Ideal.Quotient.mk p)).map
        (algebraMap (R ⧸ p) (S ⧸ Q))).roots := by
    rw [mem_roots ((hf.map (Ideal.Quotient.mk p)).map
      (algebraMap (R ⧸ p) (S ⧸ Q))).ne_zero]
    simpa only [IsRoot, eval_map, aeval_def] using
      (hf.map (Ideal.Quotient.mk p)).mem_rootSet.mp z.2
  rw [← hpoly, ← hmaproots] at hzroots
  obtain ⟨x, hxroots, hxz⟩ := Multiset.mem_map.mp hzroots
  let xroot : f.rootSet S := ⟨x, by
    rw [hf.mem_rootSet]
    rw [mem_roots hfS.ne_zero] at hxroots
    simpa only [fS, IsRoot, eval_map, aeval_def] using hxroots⟩
  refine ⟨xroot, Subtype.ext ?_⟩
  exact hxz

/-- When the reduced polynomial is separable, reduction gives a bijection
between the roots in a splitting ring and the roots in the residue field. -/
def rootReductionEquiv
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable) :
    f.rootSet S ≃ (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q) :=
  Equiv.ofBijective (rootReduction (p := p) (Q := Q) f hf)
    ⟨root_splits_separable
        (p := p) (Q := Q) f hf hsplits hseparable,
      root_surjective_splits
        (p := p) (Q := Q) f hf hsplits⟩

omit [IsDomain R] [p.IsPrime] in
@[simp]
theorem root_reduction_equiv
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    (x : f.rootSet S) :
    rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable x =
      rootReduction (p := p) (Q := Q) f hf x :=
  rfl

section Frobenius

variable {G : Type*} [Group G] [MulSemiringAction G S]
  [SMulCommClass G R S]

omit [IsDomain R] [p.IsPrime] in
/-- Root reduction intertwines an arithmetic Frobenius with the defining
power map on the residue field. -/
theorem coe_arith_frob
    (f : R[X]) (hf : f.Monic) {sigma : G}
    (hsigma : IsArithFrobAt R sigma Q) (x : f.rootSet S) :
    (rootReduction (p := p) (Q := Q) f hf (sigma • x) : S ⧸ Q) =
      (rootReduction (p := p) (Q := Q) f hf x : S ⧸ Q) ^
        Nat.card (R ⧸ p) := by
  simpa only [rootReduction_coe, Q.over_def p] using
    hsigma.mk_apply x

variable [p.IsMaximal] [Q.IsMaximal] [Fintype (R ⧸ p)] [Finite (S ⧸ Q)]
  [Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q)]

omit [IsDomain R] [p.IsPrime] [Finite (S ⧸ Q)] in
/-- In finite residue fields, the preceding power map is the canonical
finite-field Frobenius. -/
theorem reduction_smul_frobenius
    (f : R[X]) (hf : f.Monic) {sigma : G}
    (hsigma : IsArithFrobAt R sigma Q) (x : f.rootSet S) :
    (rootReduction (p := p) (Q := Q) f hf (sigma • x) : S ⧸ Q) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ Q)
        (rootReduction (p := p) (Q := Q) f hf x) := by
  rw [field_frobenius_element]
  simpa only [Fintype.card_eq_nat_card] using
    coe_arith_frob
      (p := p) (Q := Q) f hf hsigma x

omit [IsDomain R] [p.IsPrime] [Finite (S ⧸ Q)] in
/-- Via the root-reduction equivalence, arithmetic Frobenius on the roots in
`S` is conjugate to finite-field Frobenius on the reduced roots. -/
theorem root_smul_frobenius
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    {sigma : G} (hsigma : IsArithFrobAt R sigma Q)
    (z : (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q)) :
    (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable
        (sigma • (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).symm z) :
      S ⧸ Q) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ Q) z := by
  have h := reduction_smul_frobenius
    (p := p) (Q := Q) f hf hsigma
      ((rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).symm z)
  have hz :
      rootReduction (p := p) (Q := Q) f hf
          ((rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).symm z) = z := by
    simpa only [root_reduction_equiv] using
      (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).apply_symm_apply z
  have hzval := congrArg Subtype.val hz
  rw [hzval] at h
  simpa only [root_reduction_equiv] using h

end Frobenius

end

end Towers.NumberTheory.Milne
