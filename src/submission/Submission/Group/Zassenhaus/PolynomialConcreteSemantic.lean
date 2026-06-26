import Submission.Group.HallBasic.StandardSequence
import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.SignedCorrectionSemantics

/-!
# Concrete Hall recollection from packets and explicit residual sources

The canonical finite Hall families satisfy the associated-graded basis
hypothesis.  A cutoff-specific all-integral Hall-Petresco packet and explicit
intrinsic residual-source recollections therefore construct their global
product and inverse recollection polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
For the canonical Hall families, cutoff Hall-Petresco packets and explicit
intrinsic residual-source recollections construct product polynomials.
-/
theorem
    restr_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      SCBuilda
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_residual_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

/--
For the canonical Hall families, cutoff Hall-Petresco packets and explicit
intrinsic residual-source recollections construct inverse polynomials.
-/
theorem
    commutators_restr_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      SCBuilda
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  coord_collect_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

end TCTex
end Submission

/-!
# Concrete Hall recollection from class-three packets and residual sources

The explicit class-three all-integral Hall-Petresco packet discharges the
packet input to the signed symbolic recollector whenever the cutoff is at
most four.  The only remaining mathematical input is semantic recollection
of each intrinsic residual source.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace
  SCBuilda

/--
At cutoff at most four, the explicit class-three Hall-Petresco packet leaves
only intrinsic residual-source recollection to be supplied.
-/
def n_four
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (hn4 : n ≤ 4)
    (factorResidualSource :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          ∀ (factor : SPFactor H ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPSrc
                (lowerWeight := lowerWeight) hn H hH ι factor) :
    SCBuilda
      (n := n) hn H hH where
  packet :=
    PFSubsti.TAPkt.n_four
      hn4
  factorResidualSource := factorResidualSource

end
  SCBuilda

/--
For canonical Hall families at cutoff at most four, explicit intrinsic
residual-source recollections construct global product polynomials.
-/
theorem
    basic_commutators_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (factorResidualSource :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          ∀ (factor :
            SPFactor
              (concreteCommutatorsWeight.{u} d) ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPSrc
                (lowerWeight := lowerWeight) hn
                  (concreteCommutatorsWeight.{u} d)
                    (fun r hr hrn =>
                      concrete_forms_associated
                        d n r hr hrn)
                  ι factor) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restr_collect_builder
    hn e
      (SCBuilda.n_four
        hn4 factorResidualSource)

/--
For canonical Hall families at cutoff at most four, explicit intrinsic
residual-source recollections construct global inverse polynomials.
-/
theorem
    commutators_collected_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (factorResidualSource :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          ∀ (factor :
            SPFactor
              (concreteCommutatorsWeight.{u} d) ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPSrc
                (lowerWeight := lowerWeight) hn
                  (concreteCommutatorsWeight.{u} d)
                    (fun r hr hrn =>
                      concrete_forms_associated
                        d n r hr hrn)
                  ι factor) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_restr_builder
    hn e
      (SCBuilda.n_four
        hn4 factorResidualSource)

end TCTex
end Submission

/-!
# Unconditional concrete Hall recollection through class three

At cutoff at most four, every nonterminal intrinsic factor residual has
ordinary weight one.  The exact weight-one residual reduction therefore
discharges the final residual-source input to the explicit class-three packet.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace
  SCBuilda

/--
The explicit class-three packet and exact weight-one residual cancellation
construct a complete signed recollection builder at cutoff at most four.
-/
noncomputable def n_four_unconditional
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (hn4 : n ≤ 4) :
    SCBuilda
      (n := n) hn H hH :=
  n_four hn4 fun lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated => by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight HEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      TPSrc.of_weight_one
        hn H hH factor hfactorWeightOne

end
  SCBuilda

/--
Canonical Hall families have global collected-product coordinate polynomials
through class three.
-/
theorem
    concrete_commutators_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d))) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restr_collect_builder
    hn e
      (SCBuilda.n_four_unconditional
        hn4)

/--
Canonical Hall families have global collected-inverse coordinate polynomials
through class three.
-/
theorem
    commutators_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_restr_builder
    hn e
      (SCBuilda.n_four_unconditional
        hn4)

end TCTex
end Submission

/-!
# Concrete Hall families in the reachable signed recollection reduction

Right-to-left foliage contraction proves that the canonical finite Hall
families form bases in every free-group lower-central associated-graded layer.
The signed polynomial collector can therefore instantiate its high-weight
semantic normalizer with those concrete families.

This file joins the two standalone developments.  Global product and inverse
recollection for the canonical Hall families are reduced solely to the
reachable low-weight operational builder.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- The canonical Hall families satisfy every graded-basis premise below a cutoff. -/
theorem forms_graded_below
    (d n : ℕ) :
    ∀ s : ℕ,
      1 ≤ s →
        s < n →
          (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
            (n := n) := by
  intro s hs hsn
  exact concrete_forms_associated d n s hs hsn

/--
The commutative region has a canonical signed semantic normalizer for the
concrete Hall families.
-/
noncomputable def
  commutators_normalizer_high
    (d n lowerWeight : ℕ)
    (hn : 2 ≤ n)
    (hcutoff : n ≤ 2 * lowerWeight) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight)
      (concreteCommutatorsWeight.{u} d) :=
  TSNormal.of_highWeight
    hn (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
      hcutoff

/--
A reachable signed builder constructs product recollection polynomials for
the canonical finite Hall families.
-/
theorem
  concrete_reachable_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  reachable_semantic_derivation
    hn (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
      e builder

/--
A reachable signed builder constructs inverse recollection polynomials for
the canonical finite Hall families.
-/
theorem
  commutators_reachable_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  reachable_derivation_builder
    hn (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
      e builder

end TCTex
end Submission

/-!
# Reachable sharp higher-tail routing for concrete Hall families

The reachable signed recollection builder already supplies a semantic
normalizer at every support stratum and selects automatic class-two correction
packets whenever possible.  The sharp signed higher-tail router can consume
those two families directly.

This file packages the generic adapter and its concrete Hall-family
specialization.  The remaining operational work is the active-block route,
not movement across the previously normalized higher tail.  This file is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CDBuild

/-- A reachable builder supplies signed semantic normalizers at every bound. -/
noncomputable def supportedNormalizerFamily
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      CDBuild
        (n := n) H) :
    SNFam
      (n := n) H where
  normalizer lowerWeight :=
    builder.supportedCoordinateNormalizer
      hn H hH lowerWeight

/-- A reachable builder exposes its automatic-or-custom packet choice by stratum. -/
def supportedCorrectionFactory
    {d n : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (builder :
      CDBuild
        (n := n) H) :
    SFSched
      (n := n) H where
  factory lowerWeight := builder.packetFactoryAt H lowerWeight

/--
The reachable builder automa routes active factors across signed
higher tails by sharp parent-relative normalization.
-/
noncomputable def recursiveRouteSchedule
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      CDBuild
        (n := n) H) :
    RecursiveHigherSchedule
      (n := n) H :=
  (builder.supportedCorrectionFactory H)
    |>.recursiveRouteSchedule
      (builder.supportedNormalizerFamily hn H hH)

end CDBuild

/--
For the canonical finite Hall families, every reachable builder automa
supplies the terminating signed higher-tail route schedule.
-/
noncomputable def rec_reachable_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    RecursiveHigherSchedule
      (n := n) (concreteCommutatorsWeight.{u} d) :=
  builder.recursiveRouteSchedule
    hn (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)

end TCTex
end Submission

/-!
# Restricted sharp signed recollection for the canonical Hall families

The canonical finite Hall families have the associated-graded basis property
required by the direct restricted-sharp recursive collector.  This file
specializes its product and inverse recollection polynomial constructors to
those concrete families.

The remaining input is exactly the custom low-weight packet data:

* correction packets below the automatic class-two band;
* intrinsic factor-normalization residual expansions below the commutative
  terminal band.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
For the canonical Hall families, restricted sharp recursive data constructs
global product recollection polynomials.
-/
theorem commutators_sharp_rec
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      SRBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restricted_recursive_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

/--
For the canonical Hall families, restricted sharp recursive data constructs
global inverse recollection polynomials.
-/
theorem sharp_rec_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      SRBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restricted_sharp_recursive
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

end TCTex
end Submission

/-!
# Concrete Hall recollection from word expansions and singleton normalizations

The canonical finite Hall families satisfy the associated-graded basis
hypothesis required by the restricted-sharp signed collector.  The improved
mathematical interface therefore constructs their global product and inverse
recollection polynomials from all-integral higher-word expansions and
singleton semantic recollections.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
For the canonical Hall families, universal correction expansions and
singleton recollections construct global product recollection polynomials.
-/
theorem singleton_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      RSSingle
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_coord_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

/--
For the canonical Hall families, universal correction expansions and
singleton recollections construct global inverse recollection polynomials.
-/
theorem commutators_singleton_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      RSSingle
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_singleton_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

end TCTex
end Submission

/-!
# Concrete Hall recollection from cutoff packets and choose normalization

The canonical finite Hall families satisfy the associated-graded basis
hypothesis required by the packet-plus-arithmetic signed collector.  A
cutoff-specific all-integral Hall-Petresco packet, uniform positive-choose
normalization, and singleton semantic recollection therefore construct their
global product and inverse recollection polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
For the canonical Hall families, cutoff Hall-Petresco packets,
positive-choose arithmetic, and singleton recollections construct global
product recollection polynomials.
-/
theorem choose_singleton_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      SCBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  choose_collect_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

/--
For the canonical Hall families, cutoff Hall-Petresco packets,
positive-choose arithmetic, and singleton recollections construct global
inverse recollection polynomials.
-/
theorem commutators_choose_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      SCBuild
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_choose_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

end TCTex
end Submission

/-!
# Concrete Hall recollection from cutoff packets and singleton recollection

The canonical finite Hall families satisfy the associated-graded basis
hypothesis, and positive-choose formula normalization is now constructed
unconditionally.  A cutoff-specific all-integral Hall-Petresco packet and
singleton semantic recollection therefore suffice to construct their global
product and inverse recollection polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
For the canonical Hall families, cutoff Hall-Petresco packets and singleton
recollections construct global product recollection polynomials.
-/
theorem commutators_packet_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      RSBuilda
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_sharp_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

/--
For the canonical Hall families, cutoff Hall-Petresco packets and singleton
recollections construct global inverse recollection polynomials.
-/
theorem commutators_singleton_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      RSBuilda
        (n := n) hn
          (concreteCommutatorsWeight.{u} d)
            (fun r hr hrn =>
              concrete_forms_associated
                d n r hr hrn)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restricted_sharp_builder
    hn (concreteCommutatorsWeight.{u} d)
      (fun r hr hrn =>
        concrete_forms_associated d n r hr hrn)
        e builder

end TCTex
end Submission
