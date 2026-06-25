import Submission.NumberTheory.Galois.DedekindRootReduction
import Submission.NumberTheory.Galois.FrobeniusFactorPartition
import Submission.NumberTheory.Ramification.KummerFactorization

/-!
# Milne, Chapter 8, Theorem 8.23: Dedekind's cycle-type theorem

The main theorem below isolates the structural content of Dedekind's theorem.
For a monic polynomial that splits in a finite Galois ring extension, assume
that reduction modulo a prime is separable and is explicitly factored into
distinct monic irreducibles.  Arithmetic Frobenius on the global roots is
conjugate, through reduction of roots, to finite-field Frobenius.  The latter
root set is partitioned into cycles indexed by the irreducible factors, and
each cycle has length equal to the degree of its factor.

The file also retains the Chapter 3 Kummer-Dedekind ideal-factorization
theorem, which is a related arithmetic input but a logically separate result.
-/

namespace Submission.NumberTheory.Milne

open Algebra Ideal Polynomial UniqueFactorizationMonoid

noncomputable section

section CycleType

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDomain S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

variable {p : Ideal R} {Q : Ideal S} [p.IsPrime] [Q.IsPrime]
  [p.IsMaximal] [Q.IsMaximal] [Q.LiesOver p]
  [Fintype (R ⧸ p)] [Finite (S ⧸ Q)]
  [Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q)]

attribute [local instance] Ideal.Quotient.field

omit [IsDomain R] [p.IsPrime] in
/-- Milne, Theorem 8.23 (Dedekind), in a rootwise form independent of a
numbering of the roots.  The displayed arithmetic Frobenius is conjugate to
finite-field Frobenius under reduction.  Its disjoint cycles are therefore
the cycles indexed below by the distinct irreducible factors, and their
lengths are the corresponding factor degrees. -/
theorem dedekind_cycle_type
    {iota : Type*} [Fintype iota]
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    (g : iota → (R ⧸ p)[X])
    (hfactor : f.map (Ideal.Quotient.mk p) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hfactorSplits : ∀ i,
      ((g i).map (algebraMap (R ⧸ p) (S ⧸ Q))).Splits)
    (hinj : Function.Injective g) :
    ∃ sigma : G, ∃ x : iota → S ⧸ Q,
      IsArithFrobAt R sigma Q ∧
      (∀ z : (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q),
        (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable
            (sigma •
              (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).symm z) :
          S ⧸ Q) =
          FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ Q) z) ∧
      (∀ i, x i ∈ (g i).rootSet (S ⧸ Q) ∧
        minpoly (R ⧸ p) (x i) = g i ∧
        Set.ncard (frobeniusCycle (R ⧸ p) (S ⧸ Q) (x i)) =
          (g i).natDegree) ∧
      (Pairwise fun i j => Disjoint
        (frobeniusCycle (R ⧸ p) (S ⧸ Q) (x i))
        (frobeniusCycle (R ⧸ p) (S ⧸ Q) (x j))) ∧
      (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q) =
        ⋃ i, frobeniusCycle (R ⧸ p) (S ⧸ Q) (x i) := by
  let sigma : G := arithFrobAt R G Q
  have hsigma : IsArithFrobAt R sigma Q :=
    IsArithFrobAt.arithFrobAt R G Q
  obtain ⟨x, hx, hdisjoint, hcover⟩ :=
    cycles_partition_set (R ⧸ p) (S ⧸ Q)
      (f.map (Ideal.Quotient.mk p)) g hfactor hirr hmonic hfactorSplits hinj
  refine ⟨sigma, x, hsigma, ?_, hx, hdisjoint, hcover⟩
  intro z
  exact root_smul_frobenius
    (p := p) (Q := Q) f hf hsplits hseparable hsigma z

end CycleType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

attribute [local instance] Ideal.Quotient.field

open Classical in
/-- The Kummer-Dedekind ideal-factorization theorem used as an arithmetic
ingredient in the discussion surrounding Milne's Theorem 8.23: the prime
factors, with multiplicity, of `p B` correspond to the irreducible factors of
the reduced minimal polynomial. -/
theorem dedekind_factorization_theorem
    {alpha : B} {p : Ideal A} [p.IsMaximal] (hp0 : p ≠ ⊥)
    (halpha : Algebra.adjoin A {alpha} = ⊤)
    (halpha_int : IsIntegral A alpha) :
    normalizedFactors (p.map (algebraMap A B)) =
      Multiset.map
        (fun g =>
          ((KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
            inferInstance hp0 (by
              rw [conductor_eq_top_iff_adjoin_eq_top.mpr halpha,
                Ideal.comap_top, top_sup_eq]) halpha_int).symm g : Ideal B))
        (normalizedFactors
          ((minpoly A alpha).map (Ideal.Quotient.mk p))).attach :=
  by
    letI : Field (A ⧸ p) := Ideal.Quotient.field p
    exact GKDedeki.normalized_minpoly_top
      hp0 halpha halpha_int

end

end Submission.NumberTheory.Milne
