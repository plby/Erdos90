import Submission.Group.PetrescoClaimTail
import Submission.Group.PresentedAlgebraKernel
import Submission.Group.FinitePRelator.FiniteSeparation

open scoped commutatorElement

namespace Submission
namespace HACoeff

open PPColl
open PPColl.RCColl.RPAggreg

/--
The inverse-oriented adjacent collection identity inside literal left and
right contexts.  This is the local rewrite primitive `BA = A [A⁻¹, B] B`: it
does not by itself construct a source ledger or a scheduler.

In particular, the older labelled-word rewrite emitting `[B, A], A, B` is a
different orientation and must not be used as a certificate for this packet.
-/
lemma DTerm.contexteval_mulinv_corrmul
    {M N K : ℕ}
    (leftContext rightContext : FreeGroup (LabelledAtom M N))
    (B A : DTerm M N K)
    (hA : A.erasedShape.PBPos) :
    leftContext * (B.eval * A.eval) * rightContext =
      leftContext * (A.eval * (DTerm.inverseCorrection B A).eval * B.eval) *
        rightContext := by
  rw [DTerm.eval_inverse_correction B A hA]

/--
One typed inverse-oriented adjacent interchange in a literal decorated-term
context.  This is the smallest local operational bridge for `BA = A [A⁻¹,B] B`.
It deliberately carries no packet-completion or source-ledger claim.
-/
structure DTerm.IOInterc
    {M N K : ℕ}
    (source target : List (DTerm M N K)) where
  pre :
    List (DTerm M N K)
  post :
    List (DTerm M N K)
  B :
    DTerm M N K
  A :
    DTerm M N K
  right_positive :
    A.erasedShape.PBPos
  source_eq :
    source = pre ++ B :: A :: post
  target_eq :
    target = pre ++ A :: DTerm.inverseCorrection B A :: B :: post

namespace DTerm.IOInterc

/-- A typed inverse-oriented interchange preserves the exact labelled-list
value, including its literal prefix and suffix. -/
lemma decorated_list_eval
    {M N K : ℕ}
    {source target : List (DTerm M N K)}
    (step : DTerm.IOInterc source target) :
    decoratedListEval target = decoratedListEval source := by
  calc
    decoratedListEval target =
        decoratedListEval
          (step.pre ++
            step.A :: DTerm.inverseCorrection step.B step.A ::
              step.B :: step.post) := by
      exact congrArg decoratedListEval step.target_eq
    _ = decoratedListEval (step.pre ++ step.B :: step.A :: step.post) := by
      rw [decorated_list_append, decorated_list_append]
      simp only [decorated_list_cons]
      simpa only [mul_assoc] using
        (DTerm.contexteval_mulinv_corrmul
          (decoratedListEval step.pre) (decoratedListEval step.post)
          step.B step.A step.right_positive).symm
    _ = decoratedListEval source := by
      exact congrArg decoratedListEval step.source_eq.symm

end DTerm.IOInterc

/--
The two-branch right-prime incidence alternative retained by a completed
independent-block recipe.

The second branch is essential: a recipe with one right block of size `p`
has coefficient `choose p p = 1`, but its right Hall degree is divisible by
`p`.
-/
def RIAltern
    (p : ℕ)
    (coefficient : ℤ)
    (rightDegree : ℕ) :
    Prop :=
  (p : ℤ) ∣ coefficient ∨ p ∣ rightDegree

namespace RIAltern

/-- Either branch supplies the right-prime divisibility needed by a collected
factor. -/
lemma dvd_degree_coefficient
    {p rightDegree : ℕ}
    {coefficient : ℤ}
    (h : RIAltern p coefficient rightDegree) :
    (p : ℤ) ∣ (rightDegree : ℤ) * coefficient := by
  rcases h with hcoefficient | hdegree
  · exact dvd_mul_of_dvd_right hcoefficient _
  · exact dvd_mul_of_dvd_left (by exact_mod_cast hdegree) _

end RIAltern

/-- At a prime, one binomial block either contributes a factor of the prime or
has prime-divisible size. -/
lemma dvd_choose_or
    (p k : ℕ) [Fact p.Prime] :
    (p : ℤ) ∣ (Nat.choose p k : ℤ) ∨ p ∣ k := by
  have hp : p ∣ k * Nat.choose p k := by
    simpa using
      (HPGood.dvd_choose_nat
        (p := p) (A := 1) (k := k))
  rcases (Fact.out : Nat.Prime p).dvd_mul.mp hp with hk | hchoose
  · exact Or.inr hk
  · exact Or.inl (by exact_mod_cast hchoose)

/-- For a complete right block list, either its compressed coefficient gains a
factor of `p` or its exact right-slot sum does.  Zero-size bookkeeping blocks
are harmless in this formulation. -/
lemma choose_or_sum
    (p : ℕ) [Fact p.Prime] :
    ∀ blocks : List ℕ,
      (p : ℤ) ∣
          (blocks.map fun degree => (Nat.choose p degree : ℤ)).prod ∨
        p ∣ blocks.sum
  | [] => by
      exact Or.inr (by simp)
  | degree :: blocks => by
      rcases dvd_choose_or p degree with hchoose | hdegree
      · exact Or.inl (by
          simpa using
            dvd_mul_of_dvd_left hchoose
              ((blocks.map fun d => (Nat.choose p d : ℤ)).prod))
      · rcases choose_or_sum p blocks with hprod | hsum
        · exact Or.inl (by
            simpa using
              dvd_mul_of_dvd_right hprod (Nat.choose p degree : ℤ))
        · exact Or.inr (by
            simpa using dvd_add hdegree hsum)

/-- Completed independent-block recipes satisfy the full two-branch
prime-incidence invariant.  This deliberately does not replace recipes by
diagonal-history factors. -/
lemma BRecipe.factor_rightprime_incidenalterna
    (p M : ℕ) [Fact p.Prime]
    (R : BRecipe) :
    RIAltern p
      (R.factor M p).coefficient R.rightDegree := by
  rcases choose_or_sum p R.rightBlocks with hprod | hsum
  · exact Or.inl (by
      rw [BRecipe.factor]
      exact dvd_mul_of_dvd_right hprod _)
  · exact Or.inr hsum

/-- The cutoff approximation `K(A,B) gamma_m` used by the finite-class
route. -/
def lowerCentralApproximation
    (A B : ℤ)
    (m : ℕ) :
    Subgroup UniversalGroup :=
  BNClos.subgroup A B ⊔
    Subgroup.lowerCentralSeries UniversalGroup m

/--
Explicit hypothesis for the lower-central lift.  No unconditional closedness
claim is made here: proving this predicate, or replacing it by a direct finite
identity, is a separate algebraic obligation.
-/
def LowerCentralClosed
    (A B : ℤ) :
    Prop :=
  ∀ {g : UniversalGroup},
    (∀ m : ℕ, g ∈ lowerCentralApproximation A B m) →
      g ∈ BNClos.subgroup A B

/-- Pointwise triviality of the nilpotent residual of a group. -/
def NilpotentResidualSeparated
    (G : Type*) [Group G] :
    Prop :=
  ∀ x : G,
    (∀ m : ℕ, x ∈ Subgroup.lowerCentralSeries G m) →
      x = 1

/-- Residual nilpotence of every quotient by a bidegree normal closure. -/
def BudgetedResidualNilpotence :
    Prop :=
  ∀ A B : ℤ,
    NilpotentResidualSeparated
      (UniversalGroup ⧸ BNClos.subgroup A B)

/-- A surjective homomorphism maps each lower-central term onto the
corresponding target term. -/
lemma central_series_surjective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H)
    (hf : Function.Surjective f)
    (i : ℕ) :
    Subgroup.map f (Subgroup.lowerCentralSeries G i) =
      Subgroup.lowerCentralSeries H i := by
  apply le_antisymm (Subgroup.lowerCentralSeries.map f i)
  induction i with
  | zero =>
      rw [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_zero]
      exact (Subgroup.map_top_of_surjective f hf).ge
  | succ i ih =>
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
      exact
        Subgroup.commutator_le_map_commutator ih
          ((Subgroup.map_top_of_surjective f hf).ge)

/-- Residual nilpotence of the budgeted quotient supplies lower-central
closedness of the corresponding bidegree normal closure. -/
lemma closed_nilpotent_separated
    {A B : ℤ}
    (hresidual :
      NilpotentResidualSeparated
        (UniversalGroup ⧸ BNClos.subgroup A B)) :
    LowerCentralClosed A B := by
  intro g happrox
  let K : Subgroup UniversalGroup :=
    BNClos.subgroup A B
  let q : UniversalGroup →* UniversalGroup ⧸ K :=
    QuotientGroup.mk' K
  have hqmem :
      ∀ m : ℕ, q g ∈ Subgroup.lowerCentralSeries (UniversalGroup ⧸ K) m := by
    intro m
    have hmapped :
        q g ∈ Subgroup.map q (lowerCentralApproximation A B m) :=
      Subgroup.mem_map_of_mem q (happrox m)
    have hKmap : Subgroup.map q K = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      simp [q]
    rw [lowerCentralApproximation,
      show BNClos.subgroup A B = K from rfl,
      Subgroup.map_sup, hKmap, bot_sup_eq,
      central_series_surjective q
        (QuotientGroup.mk'_surjective K) m] at hmapped
    exact hmapped
  have hqone : q g = 1 :=
    hresidual (q g) (by simpa [K] using hqmem)
  exact (QuotientGroup.eq_one_iff g).mp (by simpa [q] using hqone)

/-- Lower-central membership gives an optional integral augmentation-power
adapter.  The clean filtered route in notes Section 58 instead stays over
`ZMod p`; this integral specialization does not prove separatedness. -/
lemma difference_int_central
    {G : Type*} [Group G]
    {m : ℕ}
    {g : G}
    (hg : g ∈ Subgroup.lowerCentralSeries G m) :
    augmentationDifference ℤ G g ∈
      (GShafar.augmentationIdeal ℤ G) ^ (m + 1) := by
  simpa [GShafar.augmentationPowerSubgroup,
    augmentationDifference] using
      (GShafar.lower_series_succ
        (R := ℤ) (G := G) m hg)

/-- Over the integers, an augmentation difference vanishes only at the
identity basis element. -/
lemma augmentation_difference_int
    {G : Type*} [Group G]
    (g : G) :
    augmentationDifference ℤ G g = 0 ↔ g = 1 := by
  classical
  constructor
  · intro hzero
    by_contra hg
    have hcoefficient :=
      congrArg (fun x : MonoidAlgebra ℤ G => x g) hzero
    simp only [augmentationDifference, MonoidAlgebra.one_def] at hcoefficient
    change
      (MonoidAlgebra.single g (1 : ℤ)) g -
          (MonoidAlgebra.single (1 : G) (1 : ℤ)) g =
        0 at hcoefficient
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hg] at hcoefficient
    norm_num at hcoefficient
  · rintro rfl
    simp [augmentationDifference, MonoidAlgebra.one_def]

/-- Over any nontrivial coefficient ring, an augmentation difference vanishes
only at the identity basis element. -/
lemma augmentation_difference_nontrivial
    (R : Type*) [CommRing R] [Nontrivial R]
    {G : Type*} [Group G]
    (g : G) :
    augmentationDifference R G g = 0 ↔ g = 1 := by
  classical
  constructor
  · intro hzero
    by_contra hg
    have hcoefficient :=
      congrArg (fun x : MonoidAlgebra R G => x g) hzero
    simp only [augmentationDifference, MonoidAlgebra.one_def] at hcoefficient
    change
      (MonoidAlgebra.single g (1 : R)) g -
          (MonoidAlgebra.single (1 : G) (1 : R)) g =
        0 at hcoefficient
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hg] at hcoefficient
    rw [sub_zero] at hcoefficient
    exact (one_ne_zero : (1 : R) ≠ 0) hcoefficient
  · rintro rfl
    simp [augmentationDifference, MonoidAlgebra.one_def]

/-- Index the full bidegree generator set by its subtype. -/
def bidegreeClosureListing
    (A B : ℤ) :
    {g : UniversalGroup // g ∈ BNClos.generatorSet A B} →
      UniversalGroup :=
  Subtype.val

@[simp]
lemma range_bidegree_listing
    (A B : ℤ) :
    Set.range (bidegreeClosureListing A B) =
      BNClos.generatorSet A B := by
  ext g
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro hg
    exact ⟨⟨g, hg⟩, rfl⟩

/-- The ordinary relator-difference ideal for the full bidegree generator
listing over an arbitrary coefficient ring. -/
noncomputable def bidegreeDifferenceIdeal
    (R : Type*) [CommRing R]
    (A B : ℤ) :
    Ideal (MonoidAlgebra R UniversalGroup) :=
  GShafar.relatorDifferenceIdeal
    (R := R) (bidegreeClosureListing A B)

/-- The ordinary integral relator-difference ideal for the full bidegree
generator listing. -/
noncomputable def bidegreeClosureDifference
    (A B : ℤ) :
    Ideal (MonoidAlgebra ℤ UniversalGroup) :=
  GShafar.relatorDifferenceIdeal
    (R := ℤ) (bidegreeClosureListing A B)

/--
Ordinary integral relator-ideal membership is exactly membership in the
bidegree normal closure.

The reverse implication uses the ordinary presented-group algebra kernel,
basis separation in the integral group algebra, and
`PresentedGroup.mk_eq_one_iff`.  This is a valid optional integral
specialization.  It does not use a completed group algebra or prove
augmentation-adic separatedness.
-/
lemma bidegree_closure_difference
    {A B : ℤ}
    {g : UniversalGroup} :
    g ∈ BNClos.subgroup A B ↔
      augmentationDifference ℤ UniversalGroup g ∈
        bidegreeClosureDifference A B := by
  constructor
  · intro hg
    apply
      augmentation_difference_closure
        (R := ℤ) (bidegreeClosureListing A B)
    simpa [BNClos.subgroup] using hg
  · intro hideal
    have hker :
        augmentationDifference ℤ UniversalGroup g ∈
          RingHom.ker
            (GShafar.presentedAlgebra
              (R := ℤ)
              (Set.range (bidegreeClosureListing A B))) := by
      rw [← relator_difference_algebra
        (R := ℤ) (bidegreeClosureListing A B)]
      exact hideal
    have hmap :=
      RingHom.mem_ker.mp hker
    have hdifference :
        augmentationDifference ℤ
            (PresentedGroup
              (Set.range (bidegreeClosureListing A B)))
            (PresentedGroup.mk
              (Set.range (bidegreeClosureListing A B)) g) =
          0 := by
      simpa [GShafar.presentedAlgebra] using
        (domain_ring_difference
          ℤ UniversalGroup
          (PresentedGroup
            (Set.range (bidegreeClosureListing A B)))
          (PresentedGroup.mk
            (Set.range (bidegreeClosureListing A B))) g ▸ hmap)
    have hmk :
        PresentedGroup.mk
            (Set.range (bidegreeClosureListing A B)) g =
          1 :=
      (augmentation_difference_int _).mp hdifference
    have hnormal :
        g ∈ Subgroup.normalClosure
          (Set.range (bidegreeClosureListing A B)) :=
      (PresentedGroup.mk_eq_one_iff
        (rels := Set.range (bidegreeClosureListing A B))
        (x := g)).mp hmk
    simpa [BNClos.subgroup] using hnormal

/--
Ordinary relator-ideal membership over any nontrivial coefficient ring is
exactly membership in the bidegree normal closure.

This makes the clean mod-`p` filtered route available without asserting any
augmentation-adic separatedness theorem.
-/
lemma bidegree_difference_ideal
    (R : Type*) [CommRing R] [Nontrivial R]
    {A B : ℤ}
    {g : UniversalGroup} :
    g ∈ BNClos.subgroup A B ↔
      augmentationDifference R UniversalGroup g ∈
        bidegreeDifferenceIdeal R A B := by
  constructor
  · intro hg
    apply
      augmentation_difference_closure
        (R := R) (bidegreeClosureListing A B)
    simpa [BNClos.subgroup] using hg
  · intro hideal
    have hker :
        augmentationDifference R UniversalGroup g ∈
          RingHom.ker
            (GShafar.presentedAlgebra
              (R := R)
              (Set.range (bidegreeClosureListing A B))) := by
      rw [← relator_difference_algebra
        (R := R) (bidegreeClosureListing A B)]
      exact hideal
    have hmap :=
      RingHom.mem_ker.mp hker
    have hdifference :
        augmentationDifference R
            (PresentedGroup
              (Set.range (bidegreeClosureListing A B)))
            (PresentedGroup.mk
              (Set.range (bidegreeClosureListing A B)) g) =
          0 := by
      simpa [GShafar.presentedAlgebra] using
        (domain_ring_difference
          R UniversalGroup
          (PresentedGroup
            (Set.range (bidegreeClosureListing A B)))
          (PresentedGroup.mk
            (Set.range (bidegreeClosureListing A B))) g ▸ hmap)
    have hmk :
        PresentedGroup.mk
            (Set.range (bidegreeClosureListing A B)) g =
          1 :=
      (augmentation_difference_nontrivial R _).mp hdifference
    have hnormal :
        g ∈ Subgroup.normalClosure
          (Set.range (bidegreeClosureListing A B)) :=
      (PresentedGroup.mk_eq_one_iff
        (rels := Set.range (bidegreeClosureListing A B))
        (x := g)).mp hmk
    simpa [BNClos.subgroup] using hnormal

/-- Lower-central membership gives a coefficient-generic ordinary
augmentation-power approximation. -/
lemma augmentation_difference_central
    (R : Type*) [CommRing R]
    {G : Type*} [Group G]
    {m : ℕ}
    {g : G}
    (hg : g ∈ Subgroup.lowerCentralSeries G m) :
    augmentationDifference R G g ∈
      (GShafar.augmentationIdeal R G) ^ (m + 1) := by
  simpa [GShafar.augmentationPowerSubgroup,
    augmentationDifference] using
      (GShafar.lower_series_succ
        (R := R) (G := G) m hg)

/--
One lower-central approximation gives the corresponding optional ordinary
integral relator-ideal approximation.  This is a finite algebraic calculation;
it does not descend membership in all filtered approximations to ordinary
ideal membership or prove separatedness.  The clean route in notes Section 58
uses the analogous calculation over `ZMod p`.
-/
lemma difference_int_sup
    {A B : ℤ}
    {m : ℕ}
    {g : UniversalGroup}
    (hg : g ∈ lowerCentralApproximation A B m) :
    augmentationDifference ℤ UniversalGroup g ∈
      bidegreeClosureDifference A B ⊔
        (GShafar.augmentationIdeal ℤ UniversalGroup) ^ (m + 1) := by
  rw [lowerCentralApproximation] at hg
  rcases Subgroup.mem_sup_of_normal_right.mp hg with
    ⟨k, hk, residual, hresidual, rfl⟩
  rw [augmentation_difference_left]
  apply Ideal.add_mem
  · apply Submodule.mem_sup_left
    exact
      bidegree_closure_difference.mp
        hk
  · apply
      (bidegreeClosureDifference A B ⊔
        (GShafar.augmentationIdeal ℤ UniversalGroup) ^ (m + 1)).mul_mem_left
    exact Submodule.mem_sup_right
      (difference_int_central
        hresidual)

/-- One lower-central approximation gives the coefficient-generic ordinary
relator-ideal approximation.  Taking `R := ZMod p` exposes the clean finite
filtered route without descending the resulting infinite intersection. -/
lemma difference_sup_pow
    (R : Type*) [CommRing R] [Nontrivial R]
    {A B : ℤ}
    {m : ℕ}
    {g : UniversalGroup}
    (hg : g ∈ lowerCentralApproximation A B m) :
    augmentationDifference R UniversalGroup g ∈
      bidegreeDifferenceIdeal R A B ⊔
        (GShafar.augmentationIdeal R UniversalGroup) ^ (m + 1) := by
  rw [lowerCentralApproximation] at hg
  rcases Subgroup.mem_sup_of_normal_right.mp hg with
    ⟨k, hk, residual, hresidual, rfl⟩
  rw [augmentation_difference_left]
  apply Ideal.add_mem
  · apply Submodule.mem_sup_left
    exact
      bidegree_difference_ideal
        R |>.mp hk
  · apply
      (bidegreeDifferenceIdeal R A B ⊔
        (GShafar.augmentationIdeal R UniversalGroup) ^ (m + 1)).mul_mem_left
    exact Submodule.mem_sup_right
      (augmentation_difference_central
        R hresidual)

/-- Prime-specific specialization of the coefficient-generic filtered
approximation. -/
lemma difference_zmod_sup
    (p : ℕ) [Fact p.Prime]
    {A B : ℤ}
    {m : ℕ}
    {g : UniversalGroup}
    (hg : g ∈ lowerCentralApproximation A B m) :
    augmentationDifference (ZMod p) UniversalGroup g ∈
      bidegreeDifferenceIdeal (ZMod p) A B ⊔
        (GShafar.augmentationIdeal (ZMod p) UniversalGroup) ^
          (m + 1) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact
    difference_sup_pow
      (ZMod p) hg

/-- Reversing and inverting a bidegree-certified factor list preserves every
certificate. -/
lemma forall_bidegree_inv
    {A B : ℤ}
    {L : List (RFactor UniversalGroup)}
    (hL :
      ∀ F ∈ L,
        F.word.PBPos ∧
          A ∣ (F.word.pairLeftDegree : ℤ) * F.multiplicity ∧
            B ∣ (F.word.pairRightDegree : ℤ) * F.multiplicity) :
    ∀ F ∈ PPColl.listInv L,
      F.word.PBPos ∧
        A ∣ (F.word.pairLeftDegree : ℤ) * F.multiplicity ∧
          B ∣ (F.word.pairRightDegree : ℤ) * F.multiplicity := by
  revert hL
  induction L with
  | nil =>
      simp [PPColl.listInv]
  | cons D L ih =>
      intro hL F hF
      rw [PPColl.listInv, List.mem_append,
        List.mem_singleton] at hF
      rcases hF with hF | rfl
      · exact ih (fun E hE => hL E (List.mem_cons_of_mem D hE)) F hF
      · rcases hL D List.mem_cons_self with ⟨hpositive, hleft, hright⟩
        exact
          ⟨by simpa [RFactor.inv] using hpositive,
            by simpa [RFactor.inv] using hleft,
            by simpa [RFactor.inv] using hright⟩

/-- Membership in a bidegree normal closure expands into an exact ordered list
of bidegree-certified raw factors. -/
lemma bidegree_normal_closure
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ BNClos.subgroup A B) :
    ∃ L : List (RFactor UniversalGroup),
      PPColl.listEval universalLeft universalRight L = g ∧
        ∀ F ∈ L,
          F.word.PBPos ∧
            A ∣ (F.word.pairLeftDegree : ℤ) * F.multiplicity ∧
              B ∣ (F.word.pairRightDegree : ℤ) * F.multiplicity := by
  change
    g ∈ Subgroup.closure
      (Group.conjugatesOfSet (BNClos.generatorSet A B)) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨u, c, hpositive, hleft, hright, rfl⟩
      rcases isConj_iff.mp hconj with ⟨q, rfl⟩
      let F : RFactor UniversalGroup := {
        word := u
        multiplicity := c
        conjugator := q }
      refine ⟨[F], ?_, ?_⟩
      · simp [F, RFactor.eval]
      · intro E hE
        simp only [List.mem_singleton] at hE
        subst E
        exact ⟨hpositive, hleft, hright⟩
  | one =>
      exact ⟨[], rfl, by simp⟩
  | mul x y _hx _hy ihx ihy =>
      rcases ihx with ⟨L, hL, hLcert⟩
      rcases ihy with ⟨M, hM, hMcert⟩
      refine ⟨L ++ M, by simp [hL, hM], ?_⟩
      intro F hF
      rcases List.mem_append.mp hF with hF | hF
      · exact hLcert F hF
      · exact hMcert F hF
  | inv x _hx ih =>
      rcases ih with ⟨L, hL, hLcert⟩
      exact
        ⟨PPColl.listInv L, by simp [hL],
          forall_bidegree_inv hLcert⟩

/--
Ordered finite-class witness consequence from notes (15.1)-(15.3).

This is not a formalized scheduler.  It records the ordered witness extracted
from finite-class approximation membership: a raw-factor list, an explicit
residual modulo Mathlib's zero-based `lowerCentralSeries` cutoff `m`, exact
multiplied budgets, and the two-branch right-prime incidence alternative.
Round Three derives that alternative routinely from the full right-budget
witness after extraction.  A future scheduler proof must still keep its two
branches distinct during completed-recipe arithmetic rather than replacing
the multiplied budget with prime incidence.
-/
structure CRTrace
    (p m : ℕ)
    (A B : ℤ)
    (source : UniversalGroup) where
  factors :
    List (RFactor UniversalGroup)
  residual_mem :
    source *
        (PPColl.listEval
          universalLeft universalRight factors)⁻¹ ∈
      Subgroup.lowerCentralSeries UniversalGroup m
  factors_positive :
    ∀ F ∈ factors, F.word.PBPos
  factors_left_budget :
    ∀ F ∈ factors,
      A ∣ (F.word.pairLeftDegree : ℤ) * F.multiplicity
  factors_right_budget :
    ∀ F ∈ factors,
      (p : ℤ) * B ∣ (F.word.pairRightDegree : ℤ) * F.multiplicity
  factors_prime_incidence :
    ∀ F ∈ factors,
      RIAltern p
        F.multiplicity F.word.pairRightDegree

namespace CRTrace

/-- Each witnessed factor lies in the exact multiplied-budget normal closure. -/
lemma factor_eval_mem
    {p m : ℕ}
    {A B : ℤ}
    {source : UniversalGroup}
    (T : CRTrace p m A B source)
    {F : RFactor UniversalGroup}
    (hF : F ∈ T.factors) :
    F.eval universalLeft universalRight ∈
      BNClos.subgroup A ((p : ℤ) * B) := by
  exact
    (inferInstance :
      (BNClos.subgroup A ((p : ℤ) * B)).Normal).conj_mem
        (F.word.eval
          (HPAtom.eval universalLeft universalRight) ^ F.multiplicity)
        (BNClos.zpow_word_eval
          F.word F.multiplicity
          (T.factors_positive F hF)
          (T.factors_left_budget F hF)
          (T.factors_right_budget F hF))
        F.conjugator

/-- The ordered factor product lies in the exact multiplied-budget closure. -/
lemma listEval_mem
    {p m : ℕ}
    {A B : ℤ}
    {source : UniversalGroup}
    (T : CRTrace p m A B source) :
    PPColl.listEval
        universalLeft universalRight T.factors ∈
      BNClos.subgroup A ((p : ℤ) * B) := by
  rw [PPColl.listEval]
  apply Subgroup.list_prod_mem
  intro g hg
  rcases List.mem_map.mp hg with ⟨F, hF, rfl⟩
  exact T.factor_eval_mem hF

/-- Forget the witness data and retain the finite-class approximation boundary. -/
lemma source_lower_approximation
    {p m : ℕ}
    {A B : ℤ}
    {source : UniversalGroup}
    (T : CRTrace p m A B source) :
    source ∈ lowerCentralApproximation A ((p : ℤ) * B) m := by
  have hresidual :
      source *
          (PPColl.listEval
            universalLeft universalRight T.factors)⁻¹ ∈
        lowerCentralApproximation A ((p : ℤ) * B) m :=
    Subgroup.mem_sup_right T.residual_mem
  have hfactors :
      PPColl.listEval
          universalLeft universalRight T.factors ∈
        lowerCentralApproximation A ((p : ℤ) * B) m :=
    Subgroup.mem_sup_left T.listEval_mem
  simpa [mul_assoc] using
    (lowerCentralApproximation A ((p : ℤ) * B) m).mul_mem hresidual hfactors

/-- Approximation membership expands into an ordered finite-class trace. -/
lemma nonempty_lower_approximation
    {p m : ℕ} [Fact p.Prime]
    {A B : ℤ}
    {source : UniversalGroup}
    (hsource :
      source ∈ lowerCentralApproximation A ((p : ℤ) * B) m) :
    Nonempty (CRTrace p m A B source) := by
  rw [lowerCentralApproximation] at hsource
  rcases Subgroup.mem_sup_of_normal_right.mp hsource with
    ⟨factorsValue, hfactorsValue, residual, hresidual, heq⟩
  rcases bidegree_normal_closure hfactorsValue with
    ⟨factors, hfactorsEval, hfactors⟩
  refine ⟨{
    factors := factors
    residual_mem := ?_
    factors_positive := ?_
    factors_left_budget := ?_
    factors_right_budget := ?_
    factors_prime_incidence := ?_ }⟩
  · have hconj :=
      (inferInstance :
        (Subgroup.lowerCentralSeries UniversalGroup m).Normal).conj_mem
          residual hresidual factorsValue
    simpa [← heq, hfactorsEval, mul_assoc] using hconj
  · intro F hF
    exact (hfactors F hF).1
  · intro F hF
    exact (hfactors F hF).2.1
  · intro F hF
    exact (hfactors F hF).2.2
  · intro F hF
    have hp :
        (p : ℤ) ∣
          (F.word.pairRightDegree : ℤ) * F.multiplicity :=
      dvd_trans
        (dvd_mul_of_dvd_left (dvd_refl (p : ℤ)) B)
        (hfactors F hF).2.2
    rcases Int.Prime.dvd_mul' (Fact.out : Nat.Prime p) hp with
      hdegree | hcoefficient
    · exact Or.inr (by exact_mod_cast hdegree)
    · exact Or.inl hcoefficient

end CRTrace

namespace CSPrunin

/--
Deleting entries already contained in a normal subgroup changes an ordered
product only by an element of that subgroup.  Retained entries stay in their
original order; no commutative permutation argument is used.
-/
lemma filter_forall_pred
    {α G : Type*}
    [Group G]
    (H : Subgroup G)
    [H.Normal]
    (predicate : α → Prop)
    [DecidablePred predicate]
    (eval : α → G) :
    ∀ (terms : List α),
      (∀ term ∈ terms, ¬ predicate term → eval term ∈ H) →
        (terms.map eval).prod *
            (((terms.filter predicate).map eval).prod)⁻¹ ∈ H
  | [], _ => by
      simp
  | term :: terms, hterms => by
      have htail :
          (terms.map eval).prod *
              (((terms.filter predicate).map eval).prod)⁻¹ ∈ H :=
        filter_forall_pred
          H predicate eval terms
            (fun tail htail hnot =>
              hterms tail (by simp [htail]) hnot)
      by_cases hterm : predicate term
      · simpa [hterm, mul_assoc] using
          (inferInstance : H.Normal).conj_mem
            ((terms.map eval).prod *
              (((terms.filter predicate).map eval).prod)⁻¹)
            htail
            (eval term)
      · have hhead : eval term ∈ H :=
          hterms term (by simp) hterm
        simpa [hterm, mul_assoc] using H.mul_mem hhead htail

/--
A pending pairwise error whose ordinary Hall depth reaches `m + 1` belongs
to Mathlib's zero-based lower-central term `Subgroup.lowerCentralSeries _ m`.
-/
lemma pairwise_error_depth
    {p finalCutoff m : ℕ} [Fact p.Prime]
    (E :
      PError p universalLeft universalRight finalCutoff)
    (hdepth :
      m + 1 ≤ E.factor.word.weight (fun _ => 1)) :
    E.eval ∈ Subgroup.lowerCentralSeries UniversalGroup m := by
  have hword :
      E.factor.word.eval
          (HPAtom.eval universalLeft universalRight) ∈
        Subgroup.lowerCentralSeries UniversalGroup
          (E.factor.word.weight (fun _ => 1) - 1) := by
    apply CWord.eval_lower_series
    · intro atom
      simp
    · intro atom
      cases atom <;>
        simp [HPAtom.eval, Subgroup.lowerCentralSeries_zero]
  have hwordAtCutoff :
      E.factor.word.eval
          (HPAtom.eval universalLeft universalRight) ∈
        Subgroup.lowerCentralSeries UniversalGroup m :=
    Subgroup.lowerCentralSeries_antitone (by omega) hword
  have hpow :
      (E.factor.word.eval
            (HPAtom.eval universalLeft universalRight) ^
          (p ^ E.factor.primeExponent)) ^ E.factor.multiplicity ∈
        Subgroup.lowerCentralSeries UniversalGroup m :=
    (Subgroup.lowerCentralSeries UniversalGroup m).zpow_mem
      ((Subgroup.lowerCentralSeries UniversalGroup m).pow_mem
        hwordAtCutoff (p ^ E.factor.primeExponent))
      E.factor.multiplicity
  simpa [PError.eval, WCFactor.eval] using
    (inferInstance :
      (Subgroup.lowerCentralSeries UniversalGroup m).Normal).conj_mem
        ((E.factor.word.eval
              (HPAtom.eval universalLeft universalRight) ^
            (p ^ E.factor.primeExponent)) ^ E.factor.multiplicity)
        hpow E.factor.conjugator

/--
Every member of a correlated pending batch has strictly larger ordinary Hall
depth than the batch's common parent.  This is independent of the aggregate
`(1,p)` weight used by the right-prime collector.
-/
lemma batch_pairwise_error
    {p finalCutoff : ℕ} [Fact p.Prime]
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (error :
      PError p universalLeft universalRight finalCutoff)
    (herror : error ∈ batch.errors) :
    batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1) <
      error.factor.word.weight (fun _ => 1) := by
  have hsame := batch.same_parent error herror
  rcases error.origin with
    ⟨r, s, _hrs, multiplicity, conjugator, hfactor⟩
  have hincrease :=
    CWord.bind_pairwise_error
      (fun _ : HPAtom => 1)
      (by simp)
      error.left error.right r s
  rw [hfactor]
  simpa [WCFactor.raw, hsame.1, hsame.2] using
    hincrease

/-- Keep precisely the pending errors whose ordinary Hall depth is below the
finite-class cutoff `m + 1`. -/
noncomputable def ordinaryCutoffErrors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) :
    List (PError p universalLeft universalRight finalCutoff) := by
  classical
  exact batch.errors.filter fun error =>
    decide (error.factor.word.weight (fun _ => 1) < m + 1)

/-- The shallow filter preserves exactly the original members below the
ordinary-depth cutoff. -/
lemma ordinary_cutoff_errors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (error :
      PError p universalLeft universalRight finalCutoff) :
    error ∈ ordinaryCutoffErrors m batch ↔
      error ∈ batch.errors ∧
        error.factor.word.weight (fun _ => 1) < m + 1 := by
  simp [ordinaryCutoffErrors]

/--
Once the common parent reaches depth `m + 1`, all pairwise children are deep
residual terms and the shallow retained list is empty.
-/
lemma ordinary_errors_parent
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (hdepth :
      m + 1 ≤
        batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1)) :
    ordinaryCutoffErrors m batch = [] := by
  classical
  apply List.filter_eq_nil_iff.mpr
  intro error herror
  simp only [decide_eq_true_eq]
  intro hshallow
  have hincrease :=
    batch_pairwise_error batch error herror
  omega

/--
Deleting deep errors from one correlated pending batch preserves its exact
noncommutative order modulo `Subgroup.lowerCentralSeries _ m`.
-/
lemma correlated_errors_inv
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) :
    batch.eval *
          (errorListEval (ordinaryCutoffErrors m batch))⁻¹ ∈
      Subgroup.lowerCentralSeries UniversalGroup m := by
  classical
  apply
    filter_forall_pred
      (Subgroup.lowerCentralSeries UniversalGroup m)
      (fun error :
        PError p universalLeft universalRight finalCutoff =>
          error.factor.word.weight (fun _ => 1) < m + 1)
      PError.eval
      batch.errors
  intro error herror hnot
  exact pairwise_error_depth error
    (Nat.le_of_not_gt hnot)

/--
Every retained shallow child has strictly smaller ordinary
cutoff-minus-weight measure than its common parent.
-/
lemma ordinary_measure_parent
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (hparent :
      batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1) <
        m + 1)
    (error :
      PError p universalLeft universalRight finalCutoff)
    (herror : error ∈ ordinaryCutoffErrors m batch) :
    m + 1 - error.factor.word.weight (fun _ => 1) <
      m + 1 -
        (batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1)) := by
  have hincrease :=
    batch_pairwise_error batch error
      (ordinary_cutoff_errors m batch error |>.mp herror).1
  omega

/--
Pruning one correlated batch is stable inside arbitrary literal prefix and
suffix contexts.  No factor crosses either context.
-/
lemma context_ordinary_errors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (pre suffix : UniversalGroup)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) :
    ((pre * batch.eval) * suffix) *
        ((pre * errorListEval (ordinaryCutoffErrors m batch)) *
          suffix)⁻¹ ∈
      Subgroup.lowerCentralSeries UniversalGroup m := by
  apply
    inv_of_mem
      (Subgroup.lowerCentralSeries UniversalGroup m)
  · apply
      inv_of_mem
        (Subgroup.lowerCentralSeries UniversalGroup m)
    · simp
    · exact
        correlated_errors_inv
          m batch
  · simp

/-- Ordered evaluation of a finite list of correlated pending batches. -/
def correlatedPendingBatch
    {p finalCutoff : ℕ} [Fact p.Prime]
    (batches :
      List
        (CPBatch p universalLeft universalRight finalCutoff)) :
    UniversalGroup :=
  (batches.map CPBatch.eval).prod

/--
Flatten the retained shallow errors of a finite batch list without changing
batch order or the internal order of any batch.
-/
noncomputable def belowOrdinaryErrors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batches :
      List
        (CPBatch p universalLeft universalRight finalCutoff)) :
    List (PError p universalLeft universalRight finalCutoff) :=
  batches.flatMap (ordinaryCutoffErrors m)

/--
Pruning all deep errors from a finite ordered batch list changes its aggregate
evaluation only by `Subgroup.lowerCentralSeries _ m`.
-/
lemma correlated_ordinary_errors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batches :
      List
        (CPBatch p universalLeft universalRight finalCutoff)) :
    correlatedPendingBatch batches *
          (errorListEval (belowOrdinaryErrors m batches))⁻¹ ∈
      Subgroup.lowerCentralSeries UniversalGroup m := by
  induction batches with
  | nil =>
      simp [correlatedPendingBatch, belowOrdinaryErrors]
  | cons batch batches ih =>
      change
        (batch.eval * correlatedPendingBatch batches) *
            (errorListEval
              (ordinaryCutoffErrors m batch ++
                belowOrdinaryErrors m batches))⁻¹ ∈
          Subgroup.lowerCentralSeries UniversalGroup m
      rw [error_list_append]
      exact
        inv_of_mem
          (Subgroup.lowerCentralSeries UniversalGroup m)
          (correlated_errors_inv
            m batch)
          ih

/--
Retain the shallow errors as one correlated batch.  The filter does not split
them into independently certified raw histories.
-/
noncomputable def shallowCorrelatedBatch
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) :
    CPBatch p universalLeft universalRight finalCutoff where
  left := batch.left
  right := batch.right
  parent_below := batch.parent_below
  errors := ordinaryCutoffErrors m batch
  same_parent := by
    intro error herror
    exact batch.same_parent error
      (ordinary_cutoff_errors m batch error |>.mp herror).1

/--
Canonical pruning endpoint for one correlated batch: retained errors remain
correlated and ordered, deleted errors become a lower-central residual, and
every retained child exposes the strict recursive measure decrease.
-/
structure OrdinaryBatchEndpoint
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) where
  retained :
    CPBatch p universalLeft universalRight finalCutoff
  retained_errors_eq :
    retained.errors = ordinaryCutoffErrors m batch
  retained_left_eq :
    retained.left = batch.left
  retained_right_eq :
    retained.right = batch.right
  residual :
    batch.eval * retained.eval⁻¹ ∈ Subgroup.lowerCentralSeries UniversalGroup m
  retained_depth :
    ∀ error ∈ retained.errors,
      error.factor.word.weight (fun _ => 1) < m + 1
  retained_child_measure :
    batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1) <
        m + 1 →
      ∀ error ∈ retained.errors,
        m + 1 - error.factor.word.weight (fun _ => 1) <
          m + 1 -
            (batch.left.weight (fun _ => 1) +
              batch.right.weight (fun _ => 1))

/-- Every correlated pending batch has its canonical pruning endpoint. -/
noncomputable def ordinaryBatchEndpoint
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff) :
    OrdinaryBatchEndpoint m batch where
  retained := shallowCorrelatedBatch m batch
  retained_errors_eq := rfl
  retained_left_eq := rfl
  retained_right_eq := rfl
  residual := by
    simpa [CPBatch.eval, shallowCorrelatedBatch] using
      correlated_errors_inv
        m batch
  retained_depth := by
    intro error herror
    exact (ordinary_cutoff_errors m batch error |>.mp herror).2
  retained_child_measure := by
    intro hparent error herror
    exact
      ordinary_measure_parent
        m batch hparent error herror

/-- A terminal correlated batch is absorbed entirely by the residual. -/
lemma correlated_pending_parent
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (hdepth :
      m + 1 ≤
        batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1)) :
    batch.eval ∈ Subgroup.lowerCentralSeries UniversalGroup m := by
  have hresidual :=
    correlated_errors_inv
      m batch
  rw [ordinary_errors_parent m batch hdepth] at hresidual
  simpa [errorListEval] using hresidual

/-- A finite ordered list of terminal batches is entirely residual. -/
lemma correlated_pending_batch
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batches :
      List
        (CPBatch p universalLeft universalRight finalCutoff))
    (hdepth :
      ∀ batch ∈ batches,
        m + 1 ≤
          batch.left.weight (fun _ => 1) +
            batch.right.weight (fun _ => 1)) :
    correlatedPendingBatch batches ∈
      Subgroup.lowerCentralSeries UniversalGroup m := by
  induction batches with
  | nil =>
      simp [correlatedPendingBatch]
  | cons batch batches ih =>
      change
        batch.eval * correlatedPendingBatch batches ∈
          Subgroup.lowerCentralSeries UniversalGroup m
      apply (Subgroup.lowerCentralSeries UniversalGroup m).mul_mem
      · exact
          correlated_pending_parent
            m batch (hdepth batch (by simp))
      · exact ih fun tail htail => hdepth tail (by simp [htail])

/-- Terminal batch lists have no retained shallow errors. -/
lemma below_ordinary_errors
    {p finalCutoff : ℕ} [Fact p.Prime]
    (m : ℕ)
    (batches :
      List
        (CPBatch p universalLeft universalRight finalCutoff))
    (hdepth :
      ∀ batch ∈ batches,
        m + 1 ≤
          batch.left.weight (fun _ => 1) +
            batch.right.weight (fun _ => 1)) :
    belowOrdinaryErrors m batches = [] := by
  induction batches with
  | nil =>
      rfl
  | cons batch batches ih =>
      rw [belowOrdinaryErrors, List.flatMap_cons,
        ordinary_errors_parent
          m batch (hdepth batch (by simp))]
      simpa [belowOrdinaryErrors] using
        ih (fun tail htail => hdepth tail (by simp [htail]))

end CSPrunin

/-- Conjugate an ordered raw-factor list without changing its order. -/
def rawFactorConjugate
    (q : UniversalGroup)
    (factors : List (RFactor UniversalGroup)) :
    List (RFactor UniversalGroup) :=
  factors.map (RFactor.conjugate q)

@[simp]
lemma raw_factor_conjugate
    (q : UniversalGroup) :
    ∀ factors : List (RFactor UniversalGroup),
      PPColl.listEval universalLeft universalRight
          (rawFactorConjugate q factors) =
        q *
            PPColl.listEval
              universalLeft universalRight factors *
          q⁻¹
  | [] => by
      simp [rawFactorConjugate]
  | factor :: factors => by
      change
        (factor.conjugate q).eval universalLeft universalRight *
            PPColl.listEval universalLeft universalRight
              (rawFactorConjugate q factors) =
          q *
              (factor.eval universalLeft universalRight *
                PPColl.listEval
                  universalLeft universalRight factors) *
            q⁻¹
      rw [RFactor.eval_conjugate,
        raw_factor_conjugate q factors]
      group

/--
A diagnostic closure calculus for the proved pruning layer above.

This is not the correlated shallow-batch traversal required by notes Section
70.  In particular, `closedPacket` accepts an already-certified raw factor and
`rewrite` accepts an arbitrary equality: neither constructor records completed
source-slot provenance or a genuine inverse-oriented opened-batch transition.
The relation remains useful for checking that `prunePendingBatch` introduces
only a proved lower-central residual, but it must not be used as a sufficient
constructor for the finite-class approximation.
-/
inductive DCShallo
    (p m : ℕ) [Fact p.Prime]
    (A B : ℤ) :
    UniversalGroup → List (RFactor UniversalGroup) → Prop
  | one :
      DCShallo p m A B 1 []
  | closedPacket
      (factor : RFactor UniversalGroup)
      (hpositive : factor.word.PBPos)
      (hleft :
        A ∣ (factor.word.pairLeftDegree : ℤ) * factor.multiplicity)
      (hright :
        (p : ℤ) * B ∣
          (factor.word.pairRightDegree : ℤ) * factor.multiplicity)
      (hincidence :
        RIAltern p
          factor.multiplicity factor.word.pairRightDegree) :
      DCShallo p m A B
        (factor.eval universalLeft universalRight) [factor]
  | mul
      {left right : UniversalGroup}
      {leftFactors rightFactors : List (RFactor UniversalGroup)}
      (leftTraversal :
        DCShallo p m A B left leftFactors)
      (rightTraversal :
        DCShallo p m A B right rightFactors) :
      DCShallo p m A B
        (left * right) (leftFactors ++ rightFactors)
  | conjugate
      (q : UniversalGroup)
      {source : UniversalGroup}
      {factors : List (RFactor UniversalGroup)}
      (traversal :
        DCShallo p m A B source factors) :
      DCShallo p m A B
        (q * source * q⁻¹) (rawFactorConjugate q factors)
  | rewrite
      {source target : UniversalGroup}
      {factors : List (RFactor UniversalGroup)}
      (hsource : source = target)
      (traversal :
        DCShallo p m A B target factors) :
      DCShallo p m A B source factors
  | prunePendingBatch
      {finalCutoff : ℕ}
      (batch :
        CPBatch p universalLeft universalRight finalCutoff)
      {factors : List (RFactor UniversalGroup)}
      (retainedTraversal :
        DCShallo p m A B
          (errorListEval
            (CSPrunin.ordinaryCutoffErrors m batch))
          factors) :
      DCShallo p m A B batch.eval factors

namespace DCShallo

open CSPrunin

/-- A batch whose common parent is already deep has the empty diagnostic
closure. -/
lemma of_parent_depth
    {p m finalCutoff : ℕ} [Fact p.Prime]
    {A B : ℤ}
    (batch :
      CPBatch p universalLeft universalRight finalCutoff)
    (hdepth :
      m + 1 ≤
        batch.left.weight (fun _ => 1) +
          batch.right.weight (fun _ => 1)) :
    DCShallo p m A B batch.eval [] := by
  apply DCShallo.prunePendingBatch batch
  rw [ordinary_errors_parent m batch hdepth]
  exact DCShallo.one

/-- Every diagnostic closure records its exact ordered lower-central residual.
-/
lemma residual_mem
    {p m : ℕ} [Fact p.Prime]
    {A B : ℤ}
    {source : UniversalGroup}
    {factors : List (RFactor UniversalGroup)}
    (traversal :
      DCShallo p m A B source factors) :
    source *
          (PPColl.listEval
            universalLeft universalRight factors)⁻¹ ∈
      Subgroup.lowerCentralSeries UniversalGroup m := by
  induction traversal with
  | one =>
      simp
  | closedPacket factor hpositive hleft hright hincidence =>
      simp
  | mul leftTraversal rightTraversal hleft hright =>
      rw [PPColl.listEval_append]
      exact
        inv_of_mem
          (Subgroup.lowerCentralSeries UniversalGroup m) hleft hright
  | conjugate q traversal htraversal =>
      rw [raw_factor_conjugate]
      have hconjugated :=
        (inferInstance :
          (Subgroup.lowerCentralSeries UniversalGroup m).Normal).conj_mem
            _
            htraversal q
      convert hconjugated using 1
      all_goals group
  | rewrite hsource traversal htraversal =>
      simpa [hsource] using htraversal
  | prunePendingBatch batch retainedTraversal hretained =>
      rw [mul_inv_quotient
        (Subgroup.lowerCentralSeries UniversalGroup m)] at hretained ⊢
      have hprune :=
        correlated_errors_inv
          m batch
      rw [mul_inv_quotient
        (Subgroup.lowerCentralSeries UniversalGroup m)] at hprune
      exact hprune.trans hretained

/-- Every displayed diagnostic leaf carries direct aggregate budgets and the
separately retained prime-incidence alternative. -/
lemma factors_certificates
    {p m : ℕ} [Fact p.Prime]
    {A B : ℤ}
    {source : UniversalGroup}
    {factors : List (RFactor UniversalGroup)}
    (traversal :
      DCShallo p m A B source factors) :
    ∀ factor ∈ factors,
      factor.word.PBPos ∧
        A ∣ (factor.word.pairLeftDegree : ℤ) * factor.multiplicity ∧
          (p : ℤ) * B ∣
              (factor.word.pairRightDegree : ℤ) * factor.multiplicity ∧
            RIAltern p
              factor.multiplicity factor.word.pairRightDegree := by
  induction traversal with
  | one =>
      simp
  | closedPacket factor hpositive hleft hright hincidence =>
      intro output houtput
      simp only [List.mem_singleton] at houtput
      subst output
      exact ⟨hpositive, hleft, hright, hincidence⟩
  | mul leftTraversal rightTraversal hleft hright =>
      intro factor hfactor
      rcases List.mem_append.mp hfactor with hfactor | hfactor
      · exact hleft factor hfactor
      · exact hright factor hfactor
  | conjugate q traversal htraversal =>
      intro factor hfactor
      rcases List.mem_map.mp hfactor with ⟨input, hinput, rfl⟩
      simpa [RFactor.conjugate] using htraversal input hinput
  | rewrite hsource traversal htraversal =>
      exact htraversal
  | prunePendingBatch batch retainedTraversal hretained =>
      exact hretained

/-- Forget a diagnostic closure derivation and retain a finite-class trace.
This is a one-way sanity bridge, not a Section 70 scheduler interface. -/
def classRightTrace
    {p m : ℕ} [Fact p.Prime]
    {A B : ℤ}
    {source : UniversalGroup}
    {factors : List (RFactor UniversalGroup)}
    (traversal :
      DCShallo p m A B source factors) :
    CRTrace p m A B source where
  factors := factors
  residual_mem := traversal.residual_mem
  factors_positive := by
    intro factor hfactor
    exact (traversal.factors_certificates factor hfactor).1
  factors_left_budget := by
    intro factor hfactor
    exact (traversal.factors_certificates factor hfactor).2.1
  factors_right_budget := by
    intro factor hfactor
    exact (traversal.factors_certificates factor hfactor).2.2.1
  factors_prime_incidence := by
    intro factor hfactor
    exact (traversal.factors_certificates factor hfactor).2.2.2

/-- A diagnostic closure derivation gives the finite-class approximation
boundary.  This is not used to construct the production approximation. -/
lemma source_lower_approximation
    {p m : ℕ} [Fact p.Prime]
    {A B : ℤ}
    {source : UniversalGroup}
    {factors : List (RFactor UniversalGroup)}
    (traversal :
      DCShallo p m A B source factors) :
    source ∈ lowerCentralApproximation A ((p : ℤ) * B) m :=
  traversal.classRightTrace.source_lower_approximation

end DCShallo

/-- The finite-class multigraded witness boundary for right-prime transport. -/
def MultigradedRightTrace
    (p : ℕ) :
    Prop :=
  ∀ (m : ℕ) {A B : ℤ}
    (u : CWord HPAtom) (c : ℤ),
    u.PBPos →
      A ∣ (u.pairLeftDegree : ℤ) * c →
        B ∣ (u.pairRightDegree : ℤ) * c →
          Nonempty
            (CRTrace p m A B
              (BNClos.rightPrimeHom p
                (u.eval
                  (HPAtom.eval universalLeft universalRight) ^ c)))

/-- The signed finite-class approximation boundary from notes Section 64. -/
def ClassRightApproximation
    (p : ℕ) :
    Prop :=
  ∀ (m : ℕ) {A B : ℤ}
    (u : CWord HPAtom) (c : ℤ),
    u.PBPos →
      A ∣ (u.pairLeftDegree : ℤ) * c →
        B ∣ (u.pairRightDegree : ℤ) * c →
          BNClos.rightPrimeHom p
              (u.eval
                (HPAtom.eval universalLeft universalRight) ^ c) ∈
            lowerCentralApproximation A ((p : ℤ) * B) m

/-- The weaker approximation boundary routinely expands back into the ordered
finite-class witness boundary. -/
lemma multigraded_right_approximation
    (p : ℕ) [Fact p.Prime]
    (happrox : ClassRightApproximation p) :
    MultigradedRightTrace p := by
  intro m A B u c hpositive hleft hright
  exact
    CRTrace.nonempty_lower_approximation
      (happrox m u c hpositive hleft hright)

/-- Finite-class transport upgrades to exact generator transport under an
explicit lower-central closedness hypothesis. -/
lemma right_generator_closed
    (p : ℕ)
    {A B : ℤ}
    (hfinite : ClassRightApproximation p)
    (hclosed : LowerCentralClosed A ((p : ℤ) * B))
    (u : CWord HPAtom)
    (c : ℤ)
    (hpositive : u.PBPos)
    (hleft : A ∣ (u.pairLeftDegree : ℤ) * c)
    (hright : B ∣ (u.pairRightDegree : ℤ) * c) :
    BNClos.rightPrimeHom p
        (u.eval (HPAtom.eval universalLeft universalRight) ^ c) ∈
      BNClos.subgroup A ((p : ℤ) * B) := by
  apply hclosed
  intro m
  exact hfinite m u c hpositive hleft hright

/--
Special right-prime nilpotent-residual separation from notes Sections 99-101.

This is weaker than unconditional lower-central closedness: it asks for the
lift only for the right-prime image of one generator satisfying the stated
budgets.  The ordinary relator-ideal to finite normal-closure conversion is
proved above by
`bidegree_closure_difference`.
The finite-`p`-group separator target below is sufficient, and the subsequent
finite-relator reduction derives it from the smaller element-specific
relator-kernel closedness boundary of notes Section 100.  A special mod-`p`
augmentation-adic separatedness argument or a direct finite identity could
supply that remaining boundary.
The optional integral helpers above do not prove that separatedness.
Membership in every completed or filtered approximation must not be silently
descended to ordinary ideal membership.
-/
def SpecificNilpotentSeparation
    (p : ℕ) :
    Prop :=
  ∀ {A B : ℤ}
    (u : CWord HPAtom)
    (c : ℤ),
    u.PBPos →
      A ∣ (u.pairLeftDegree : ℤ) * c →
        B ∣ (u.pairRightDegree : ℤ) * c →
          (∀ m : ℕ,
            BNClos.rightPrimeHom p
                (u.eval
                  (HPAtom.eval universalLeft universalRight) ^ c) ∈
              lowerCentralApproximation A ((p : ℤ) * B) m) →
            BNClos.rightPrimeHom p
                (u.eval
                  (HPAtom.eval universalLeft universalRight) ^ c) ∈
              BNClos.subgroup A ((p : ℤ) * B)

/--
A concrete finite `p`-group shadow separating one element from a normal
subgroup.

The map is phrased on `UniversalGroup` and kills `K`; equivalently it factors
through `UniversalGroup ⧸ K`.  This is the convenient acyclic form of the
finite-`p`-group separator discussed in notes Section 101.
-/
structure PGSepara
    (p : ℕ)
    (K : Subgroup UniversalGroup)
    (g : UniversalGroup) where
  Target :
    Type
  [targetGroup :
    Group Target]
  [targetFinite :
    Finite Target]
  map :
    UniversalGroup →* Target
  target_p_group :
    IsPGroup p Target
  kills :
    K ≤ map.ker
  separates :
    map g ≠ 1

attribute [instance] PGSepara.targetGroup
attribute [instance] PGSepara.targetFinite

namespace PGSepara

/--
A finite `p`-group shadow of the budgeted quotient gives the ambient separator
interface used by the local exact-lift reduction.
-/
def ofQuotientMap
    (p : ℕ)
    (K : Subgroup UniversalGroup) [K.Normal]
    (g : UniversalGroup)
    (Target : Type) [Group Target] [Finite Target]
    (φ : UniversalGroup ⧸ K →* Target)
    (target_p_group : IsPGroup p Target)
    (separates : φ (QuotientGroup.mk' K g) ≠ 1) :
    PGSepara p K g where
  Target := Target
  map := φ.comp (QuotientGroup.mk' K)
  target_p_group := target_p_group
  kills := by
    intro k hk
    change φ (QuotientGroup.mk' K k) = 1
    simpa using congrArg φ ((QuotientGroup.eq_one_iff k).mpr hk)
  separates := by
    simpa using separates

end PGSepara

/--
Special finite-`p`-group separation target from notes Sections 100-101.

This is a sufficient target, not an established fact.  It is deliberately
restricted to the right-prime image of one positive Hall-word power with the
inherited budgets.
-/
def ElementSpecificSeparation
    (p : ℕ) :
    Prop :=
  ∀ {A B : ℤ}
    (u : CWord HPAtom)
    (c : ℤ),
    u.PBPos →
      A ∣ (u.pairLeftDegree : ℤ) * c →
        B ∣ (u.pairRightDegree : ℤ) * c →
          BNClos.rightPrimeHom p
              (u.eval
                (HPAtom.eval universalLeft universalRight) ^ c) ∉
            BNClos.subgroup A ((p : ℤ) * B) →
              Nonempty
                (PGSepara p
                  (BNClos.subgroup A ((p : ℤ) * B))
                  (BNClos.rightPrimeHom p
                    (u.eval
                      (HPAtom.eval universalLeft universalRight) ^ c)))

/--
The special finite-`p`-group separator target implies the local exact lift.

Indeed, a finite `p`-group is nilpotent.  Mapping a sufficiently deep
lower-central approximation into a separating shadow kills its residual and
its budgeted normal-closure factor, contradicting separation.
-/
lemma element_specific_separation
    {p : ℕ} [Fact p.Prime]
    (hseparator : ElementSpecificSeparation p) :
    SpecificNilpotentSeparation p := by
  intro A B u c hpositive hleft hright happrox
  by_contra hnotmem
  rcases hseparator u c hpositive hleft hright hnotmem with ⟨separator⟩
  let source : UniversalGroup :=
    BNClos.rightPrimeHom p
      (u.eval (HPAtom.eval universalLeft universalRight) ^ c)
  let K : Subgroup UniversalGroup :=
    BNClos.subgroup A ((p : ℤ) * B)
  letI : Group.IsNilpotent separator.Target :=
    separator.target_p_group.isNilpotent
  rcases
      Subgroup.nilpotent_iff_lowerCentralSeries.mp
        (inferInstance : Group.IsNilpotent separator.Target) with
    ⟨m, hm⟩
  have hsourceApprox :
      source ∈ lowerCentralApproximation A ((p : ℤ) * B) m := by
    exact happrox m
  rw [lowerCentralApproximation] at hsourceApprox
  rcases Subgroup.mem_sup_of_normal_right.mp hsourceApprox with
    ⟨k, hk, residual, hresidual, hsource⟩
  have hkilled :
      separator.map k = 1 := by
    exact separator.kills hk
  have hresidualImage :
      separator.map residual ∈
        Subgroup.lowerCentralSeries separator.Target m := by
    exact
      Subgroup.lowerCentralSeries.map separator.map m
        (Subgroup.mem_map_of_mem separator.map hresidual)
  have hresidualKilled :
      separator.map residual = 1 := by
    have :
        separator.map residual ∈ (⊥ : Subgroup separator.Target) := by
      simpa [hm] using hresidualImage
    simpa using this
  apply separator.separates
  change separator.map source = 1
  rw [← hsource, map_mul, hkilled, hresidualKilled, one_mul]

namespace BNKern

section

open PRFact
open PRQuotie

local instance universalGroupTopologicalSpace :
    TopologicalSpace UniversalGroup :=
  ⊥

local instance universalGroupDiscreteTopology :
    DiscreteTopology UniversalGroup :=
  discreteTopology_bot UniversalGroup

local instance universalGroupIsTopologicalGroup :
    IsTopologicalGroup UniversalGroup := by
  infer_instance

/--
The finite-`p` relator residual kernel for the discrete universal group and
the full bidegree normal-closure relator listing.

This is an intersection of kernels of finite relator-killing shadows.  No
reverse containment with the ordinary bidegree normal closure is asserted.
-/
noncomputable def subgroup
    (p : ℕ)
    (A B : ℤ) :
    Subgroup UniversalGroup :=
  relatorKernel p (bidegreeClosureListing A B)

/-- The ordinary relation subgroup of the full listing is exactly the
bidegree normal closure. -/
lemma relationSubgroup_eq
    (A B : ℤ) :
    relationSubgroup (bidegreeClosureListing A B) =
      BNClos.subgroup A B := by
  simp [relationSubgroup, BNClos.subgroup]

/--
The ordinary bidegree normal closure lies in its finite-`p` relator residual
kernel.  This is the easy containment; the reverse direction is deliberately
not claimed.
-/
lemma bidegree_closure_subgroup
    (p : ℕ)
    (A B : ℤ) :
    BNClos.subgroup A B ≤ subgroup p A B := by
  calc
    BNClos.subgroup A B =
        relationSubgroup (bidegreeClosureListing A B) :=
      (relationSubgroup_eq A B).symm
    _ ≤ completedRelationSubgroup (bidegreeClosureListing A B) :=
      relation_completed _
    _ ≤ relatorKernel p (bidegreeClosureListing A B) :=
      completed_relation_relator

/--
Nonmembership in the specialized relator residual kernel is detected by an
actual finite `p`-group quotient shadow.  Factoring that shadow through the
ordinary bidegree normal closure yields the ambient separator interface.
-/
lemma nonempty_separator_not
    {p : ℕ}
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∉ subgroup p A B) :
    Nonempty
      (PGSepara p
        (BNClos.subgroup A B) g) := by
  change
    g ∉ relatorKernel p (bidegreeClosureListing A B) at hg
  rcases
      (PRSep.not_relator_shadow
          (p := p)
          (relator := bidegreeClosureListing A B)
          (x := g)).mp hg with
    ⟨S, hS⟩
  have hnormal :
      (BNClos.subgroup A B).Normal :=
    inferInstance
  let φ :
      UniversalGroup ⧸ BNClos.subgroup A B →* S.Target :=
    QuotientGroup.lift
      (BNClos.subgroup A B)
      S.map
      (by
        rw [← relationSubgroup_eq A B]
        exact
          (kills_relators_relation
            (bidegreeClosureListing A B) S.map).mp
              S.relator_killed)
  refine
    ⟨PGSepara.ofQuotientMap p
      (BNClos.subgroup A B) g S.Target φ
      S.toRShadow.toShadow.target_p_group ?_⟩
  change S.map g ≠ 1
  exact hS

/--
Element-specific special right-prime closedness target from notes Section
100.  It asks only that the relevant right-prime generator image, when
outside the ordinary budgeted normal closure, is also outside the finite-`p`
relator residual kernel.  It is strictly weaker than asserting equality of
the residual kernel with the normal closure.
-/
def ElementSpecificClosedness
    (p : ℕ) :
    Prop :=
  ∀ {A B : ℤ}
    (u : CWord HPAtom)
    (c : ℤ),
    u.PBPos →
      A ∣ (u.pairLeftDegree : ℤ) * c →
        B ∣ (u.pairRightDegree : ℤ) * c →
          BNClos.rightPrimeHom p
              (u.eval
                (HPAtom.eval universalLeft universalRight) ^ c) ∉
            BNClos.subgroup A ((p : ℤ) * B) →
              BNClos.rightPrimeHom p
                  (u.eval
                    (HPAtom.eval universalLeft universalRight) ^ c) ∉
                subgroup p A ((p : ℤ) * B)

/-- The element-specific relator-kernel target supplies an actual finite
`p`-group separator. -/
lemma specific_p_separation
    {p : ℕ} [Fact p.Prime]
    (hclosed : ElementSpecificClosedness p) :
    ElementSpecificSeparation p := by
  intro A B u c hpositive hleft hright hnotmem
  exact
    nonempty_separator_not
      (hclosed u c hpositive hleft hright hnotmem)

end

end BNKern

/-- Budgeted quotient residual nilpotence supplies the local exact lift. -/
lemma specific_separation_budgeted
    (hresidual : BudgetedResidualNilpotence)
    (p : ℕ) :
    SpecificNilpotentSeparation p := by
  intro A B u c _hpositive _hleft _hright happrox
  exact
    closed_nilpotent_separated
      (hresidual A ((p : ℤ) * B)) happrox

/-- Universal free-group endomorphism implementing `left ↦ left ^ p`. -/
def leftPrimeHom
    (p : ℕ) :
    UniversalGroup →* UniversalGroup :=
  FreeGroup.lift (HPAtom.eval (universalLeft ^ p) universalRight)

@[simp]
lemma left_hom_universal
    (p : ℕ) :
    leftPrimeHom p universalLeft = universalLeft ^ p := by
  simp [leftPrimeHom, universalLeft, HPAtom.eval]

@[simp]
lemma left_universal_right
    (p : ℕ) :
    leftPrimeHom p universalRight = universalRight := by
  simp [leftPrimeHom, universalRight, HPAtom.eval]

namespace BTrans

/-- Universal free-group automorphism exchanging the two Hall-pair atoms. -/
def atomSwapHom :
    UniversalGroup →* UniversalGroup :=
  FreeGroup.lift (HPAtom.eval universalRight universalLeft)

/-- Atom swapping commutes with Hall-word evaluation by swapping the formal
Hall-pair alphabet. -/
lemma atom_swap_eval
    (u : CWord HPAtom) :
    atomSwapHom
        (u.eval (HPAtom.eval universalLeft universalRight)) =
      u.hallPairSwap.eval
        (HPAtom.eval universalLeft universalRight) := by
  induction u with
  | atom atom =>
      cases atom <;>
        simp [atomSwapHom, universalLeft, universalRight, CWord.eval,
          CWord.hallPairSwap, HPAtom.eval]
  | commutator u v ihu ihv =>
      simp [CWord.eval, CWord.hallPairSwap,
        map_commutatorElement, ihu, ihv]

/--
The atom-swap automorphism exchanges the two bidegree normal-closure
coordinates.
-/
lemma atom_swap_hom
    {A B : ℤ}
    {g : UniversalGroup}
    (hg : g ∈ BNClos.subgroup A B) :
    atomSwapHom g ∈ BNClos.subgroup B A := by
  change
    g ∈
      Subgroup.closure
        (Group.conjugatesOfSet (BNClos.generatorSet A B)) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨x, hx, hconj⟩
      rcases hx with ⟨u, c, hpositive, hleft, hright, rfl⟩
      rcases isConj_iff.mp hconj with ⟨q, rfl⟩
      simpa only [map_mul, map_inv, map_zpow, atom_swap_eval] using
        (inferInstance :
          (BNClos.subgroup B A).Normal).conj_mem
            (u.hallPairSwap.eval
                (HPAtom.eval universalLeft universalRight) ^ c)
            (BNClos.zpow_word_eval
              u.hallPairSwap c hpositive.swap
              (by simpa using hright)
              (by simpa using hleft))
            (atomSwapHom q)
  | one =>
      simp
  | mul x y _hx _hy ihx ihy =>
      simpa only [map_mul] using
        (BNClos.subgroup B A).mul_mem ihx ihy
  | inv x _hx ih =>
      simpa only [map_inv] using
        (BNClos.subgroup B A).inv_mem ih

/--
Conjugating right-prime substitution by atom swap is left-prime substitution.
-/
lemma atom_swap_prime
    (p : ℕ)
    (g : UniversalGroup) :
    atomSwapHom (BNClos.rightPrimeHom p (atomSwapHom g)) =
      leftPrimeHom p g := by
  let lhs : UniversalGroup →* UniversalGroup :=
    atomSwapHom.comp
      ((BNClos.rightPrimeHom p).comp atomSwapHom)
  change lhs g =
    FreeGroup.lift
      (HPAtom.eval (universalLeft ^ p) universalRight) g
  apply FreeGroup.lift_unique lhs
  intro atom
  cases atom <;>
    simp [lhs, atomSwapHom, BNClos.rightPrimeHom,
      universalLeft, universalRight, HPAtom.eval]

end BTrans

/-- The basic Hall commutator starts in `K(1,1)`. -/
lemma universal_commutator_one :
    ⁅universalLeft, universalRight⁆ ∈
      BNClos.subgroup 1 1 := by
  simpa using
    (BNClos.zpow_word_eval
      CWord.hallPairBase 1
      (by simp [CWord.PBPos])
      (by simp) (by simp))

/-- Specializing a prime-power bidegree normal closure lands directly in the
corresponding weighted Hall-pair subgroup. -/
lemma specialize_bidegree_weighted
    {p a b U V : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (x y : G)
    {g : UniversalGroup}
    (hg :
      g ∈
        BNClos.subgroup
          ((p : ℤ) ^ a) ((p : ℤ) ^ b)) :
    specialize x y g ∈
      weightedPairSubgroup p x y U V
        (U * p ^ a + V * p ^ b) := by
  change
    g ∈
      Subgroup.closure
        (Group.conjugatesOfSet
          (BNClos.generatorSet
            ((p : ℤ) ^ a) ((p : ℤ) ^ b))) at hg
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
      rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨q, hq, hconj⟩
      rcases hq with ⟨u, c, hpositive, hleft, hright, rfl⟩
      rcases isConj_iff.mp hconj with ⟨r, rfl⟩
      let F : RFactor UniversalGroup := {
        word := u
        multiplicity := c
        conjugator := r }
      have hFgood : F.Good p a b := by
        exact ⟨hpositive.left, hpositive.right, hleft, hright⟩
      have hmappedGood :
          (F.mapHom (specialize x y)).Good p a b :=
        (RFactor.good_mapHom (specialize x y) F).2 hFgood
      have hmem :=
        RFactor.eval_weighted_pair
          (x := x) (y := y) (A := U) (B := V) hmappedGood
      have hmapEval :
          (F.mapHom (specialize x y)).eval x y =
            specialize x y (F.eval universalLeft universalRight) := by
        simpa using
          (RFactor.eval_mapHom
            (specialize x y) universalLeft universalRight F)
      rw [hmapEval] at hmem
      simpa [F, RFactor.eval] using hmem
  | one =>
      simp
  | mul g h _hg _hh ihg ihh =>
      simpa only [map_mul] using
        (weightedPairSubgroup p x y U V
          (U * p ^ a + V * p ^ b)).mul_mem ihg ihh
  | inv g _hg ihg =>
      simpa only [map_inv] using
        (weightedPairSubgroup p x y U V
          (U * p ^ a + V * p ^ b)).inv_mem ihg

end HACoeff
end Submission
