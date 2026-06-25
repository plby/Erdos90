import Towers.NumberTheory.Galois.DedekindTheorem
import Towers.NumberTheory.Galois.FrobeniusPermutationCycles


/-!
# Dedekind cycles as permutations of integral roots

Root reduction conjugates arithmetic Frobenius on global integral roots to
finite-field Frobenius.  The results here package that compatibility as
`Equiv.Perm.IsCycleOn` statements suitable for the permutation-group
criterion in Example 8.25.
-/

namespace Towers.NumberTheory.Milne

open Equiv Finset Polynomial Set

noncomputable section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDomain S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

variable {p : Ideal R} {Q : Ideal S} [p.IsPrime] [Q.IsPrime]
  [p.IsMaximal] [Q.IsMaximal] [Q.LiesOver p]
  [Fintype (R ⧸ p)] [Finite (S ⧸ Q)]
  [Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q)]

attribute [local instance] Ideal.Quotient.field

/-- The permutation of the global roots induced by a Galois element. -/
def arithmeticRootPerm (f : R[X]) (sigma : G) :
    Equiv.Perm (f.rootSet S) :=
  MulAction.toPermHom G (f.rootSet S) sigma

/-- Lift one finite-field Frobenius cycle to the global roots through the
root-reduction equivalence. -/
def liftedFrobeniusCycle
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    (x : (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q)) :
    Finset (f.rootSet S) :=
  (frobeniusRootCycle (R ⧸ p) (S ⧸ Q)
      (f.map (Ideal.Quotient.mk p)) x).map
    (rootReductionEquiv (p := p) (Q := Q) f hf hsplits hseparable).symm.toEmbedding

omit [Finite G] [IsDomain R] [p.IsPrime] in
/-- Arithmetic Frobenius is cyclic on the lift of each finite-field
Frobenius cycle. -/
theorem arithmetic_cycle_lifted
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    {sigma : G} (hsigma : IsArithFrobAt R sigma Q)
    (x : (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q)) :
    (arithmeticRootPerm f sigma).IsCycleOn
      (liftedFrobeniusCycle (p := p) (Q := Q)
        f hf hsplits hseparable x : Set (f.rootSet S)) := by
  classical
  let e := rootReductionEquiv (p := p) (Q := Q)
    f hf hsplits hseparable
  let tau := frobeniusRootPerm (R ⧸ p) (S ⧸ Q)
    (f.map (Ideal.Quotient.mk p))
  let s := frobeniusRootCycle (R ⧸ p) (S ⧸ Q)
    (f.map (Ideal.Quotient.mk p)) x
  have hcycle : tau.IsCycleOn (s : Set _) :=
    frobenius_perm_cycle
      (R ⧸ p) (S ⧸ Q) (f.map (Ideal.Quotient.mk p)) x
  apply Equiv.Perm.IsCycleOn.transp_finse e.symm s hcycle
  intro z
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ Q) z =
    (e (sigma • e.symm z) : S ⧸ Q)
  exact (root_smul_frobenius
    (p := p) (Q := Q) f hf hsplits hseparable hsigma z).symm

omit [IsDomain R] [p.IsPrime]
  [Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q)] in
/-- Lifting a Frobenius root cycle preserves its cardinality. -/
theorem card_lifted_cycle
    (f : R[X]) (hf : f.Monic)
    (hsplits : (f.map (algebraMap R S)).Splits)
    (hseparable : (f.map (Ideal.Quotient.mk p)).Separable)
    (x : (f.map (Ideal.Quotient.mk p)).rootSet (S ⧸ Q)) :
    (liftedFrobeniusCycle (p := p) (Q := Q)
      f hf hsplits hseparable x).card =
      Set.ncard (frobeniusCycle (R ⧸ p) (S ⧸ Q) x) := by
  rw [liftedFrobeniusCycle, Finset.card_map]
  exact card_frobenius_cycle
    (R ⧸ p) (S ⧸ Q) (f.map (Ideal.Quotient.mk p)) x

end

end Towers.NumberTheory.Milne
