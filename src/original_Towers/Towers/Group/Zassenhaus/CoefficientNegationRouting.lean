import Towers.Group.Zassenhaus.SignedReductionFactors
import Towers.Group.Zassenhaus.SignedCorrectionSemantics
import Towers.Group.Zassenhaus.PolynomialBracketSupport
import Towers.Group.Zassenhaus.Polynomial


/-!
# Routing concrete signed-polynomial residuals through coefficient negation

Negating a concrete symbolic polynomial factor preserves its expanded Hall
tree, but it does not literally invert the ordered atomic reduction packet:
the canonical packet order is retained while every atomic coefficient changes
sign.  The resulting order correction is a semantically higher atomic source.

This file derives the concrete residual recollection of `factor.neg` from a
recollection of `factor`.  The same-ranked inverse factor in a value packet
therefore does not become an independent recursive child.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u


namespace SPFactor

/-- Negating a signed-polynomial factor twice restores the original factor. -/
@[simp]
theorem neg_neg
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (factor : SPFactor H ι) :
    factor.neg.neg = factor := by
  cases factor with
  | mk word coefficient =>
      cases coefficient with
      | mk terms =>
          simp [neg, WBForm.scale,
            WBTerm.scale, Function.comp_def]

end SPFactor

namespace CEWord

/--
The atomic correction between coefficientwise negation of the canonical
packet and list inversion of that packet.
-/
noncomputable def basicReductionNeg
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor.neg) ++
    SPFactor.inverseList (basicReductionFactors factor)

/-- Inverse atomic reduction packets retain their original symbolic weight. -/
theorem basic_reduction_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx :
      x ∈ SPFactor.inverseList
        (basicReductionFactors factor)) :
    x.word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  rw [SPFactor.inverseList] at hx
  rcases List.mem_map.mp hx with ⟨sourceFactor, hsourceFactor, rfl⟩
  simpa only [SPFactor.word_neg] using
    word_reduction_factors factor
      (by simpa using hsourceFactor)

/-- The atomic sign-order correction is physically truncated. -/
theorem truncated_raw_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (basicReductionNeg factor) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [basic_reduction_factors factor.neg hx]
    simpa only [SPFactor.word_neg] using hfactorTruncated
  · rw [basic_reduction_factors factor hx]
    exact hfactorTruncated

/-- Every factor in the atomic sign-order correction is an active-layer atom. -/
theorem atom_raw_source
    {d lowerWeight : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionNeg factor) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧ address.weight = lowerWeight := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases atom_reduction_factors factor.neg hx with
      ⟨address, hword, hweight⟩
    exact
      ⟨address, hword, by
        simpa only [SPFactor.word_neg] using
          hweight.trans hfactorWeight⟩
  · rcases atom_reduction_factors factor hx with
      ⟨address, hword, hweight⟩
    exact ⟨address, hword, hweight.trans hfactorWeight⟩

/--
The atomic sign-order correction starts one lower-central stratum higher.
It is the product of the residual for `factor.neg` and a conjugate of the
residual for `factor`.
-/
theorem
    reduction_neg_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionNeg factor) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
  have hneg :
      (SPFactor.listEval (n := n) e
          (basicReductionFactors factor.neg))⁻¹ *
          factor.neg.eval e ∈ K := by
    simpa only [K, SPFactor.word_neg,
      reduction_raw_source] using
      (list_reduction_series
        (n := n) factor.neg e)
  have hfactor :
      (SPFactor.listEval (n := n) e
          (basicReductionFactors factor))⁻¹ *
          factor.eval e ∈ K := by
    simpa only [K, reduction_raw_source] using
      (list_reduction_series
        (n := n) factor e)
  have hconjugated :
      factor.eval e *
            ((SPFactor.listEval (n := n) e
                (basicReductionFactors factor))⁻¹ *
              factor.eval e) *
          (factor.eval e)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem _ hfactor _
  rw [basicReductionNeg,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    SPFactor.list_eval_inverse]
  convert K.mul_mem hneg hconjugated using 1 ;
    simp only [SPFactor.eval_neg] ;
      group

end CEWord

namespace TSFtry

/--
Restricted-sharp atomic normalization recollects the finite sign-order
correction between a factor and its coefficientwise negation.
-/
noncomputable def basicNegRecollection
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (basicReductionNeg factor) := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let result :=
    factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
      (basicReductionNeg factor)
      hlowerWeightPos (by omega)
      (truncated_raw_source
        factor hfactorTruncated)
      (fun x hx =>
        atom_raw_source
          factor hfactorWeight hx)
      (fun e => by
        simpa only [hfactorWeight] using
          reduction_neg_series
            (n := n) factor e)
  exact
    {
      higherSource := result.choose
      higher_source_truncated := result.choose_spec.1
      higher_weight_least := result.choose_spec.2.1
      list_higher_raw := result.choose_spec.2.2
    }

end TSFtry

namespace
  TRRecoll

/--
Derive the true concrete reduction residual of `factor.neg` from the residual
of `factor`.
-/
noncomputable def neg_of_recollection
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (recollection :
      TRRecoll
        (n := n) factor) :
    TRRecoll
      (n := n) factor.neg := by
  let correction :=
    factory.basicNegRecollection hn hH sharp
      nextNormalizer factor hfactorWeight hfactorTruncated
  let inverseResidual :
      SSRecol
        (n := n) (lowerWeight := lowerWeight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactor.inverseList
          (basicRawSource factor)) :=
    {
      higherSource := SPFactor.inverseList recollection.higherSource
      higher_source_truncated :=
        SPFactor.truncated_inverse_list
          recollection.higher_source_truncated
      higher_weight_least :=
        SPFactor.least_inverse_list
          (by
            intro x hx
            simpa only [hfactorWeight] using
              recollection.higher_least_succ x hx)
      list_higher_raw := by
        intro e
        rw [SPFactor.list_eval_inverse,
          SPFactor.list_eval_inverse,
          recollection.list_higher_raw]
    }
  let conjugated :=
    factory.conjugated_sharp_normalizer sharp
      (SPFactor.inverseList (basicReductionFactors factor))
      (SPFactor.inverseList
        (basicRawSource factor))
      inverseResidual.higherSource
      (fun x hx =>
        (basic_reduction_factors factor hx).trans
          hfactorWeight)
      (SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactorTruncated))
      inverseResidual.higher_source_truncated
      inverseResidual.higher_weight_least
      inverseResidual.list_higher_raw
  exact
    {
      higherSource := correction.higherSource ++ conjugated.higherSource
      higher_source_truncated := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact correction.higher_source_truncated x hx
        · exact conjugated.higher_source_truncated x hx
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simpa only [SPFactor.word_neg, hfactorWeight] using
            correction.higher_weight_least x hx
        · simpa only [SPFactor.word_neg, hfactorWeight] using
            conjugated.higher_least_succ x hx
      list_higher_raw := by
        intro e
        dsimp [correction, conjugated, inverseResidual]
        rw [SPFactor.listEval_append,
          correction.list_higher_raw,
          conjugated.list_conjugated_raw,
          SPFactor.conjugated_raw_source,
          basicReductionNeg,
          SPFactor.listEval_append,
          SPFactor.list_eval_inverse,
          SPFactor.list_eval_inverse,
          SPFactor.list_eval_inverse,
          reduction_raw_source,
          reduction_raw_source,
          SPFactor.eval_neg]
        group
    }

end
  TRRecoll

end TCTex
end Towers

/-!
# Normalizing concrete polynomial basic-reduction residuals directly

The explicit atomic reduction packet for a concrete signed-polynomial Hall
factor leaves a raw residual source at the same physical Hall weight.  Its
evaluated product starts one lower-central layer higher.  A signed semantic
normalizer at the factor-weight stratum therefore recollects the whole raw
residual directly into its strictly higher coordinate tail.

This bypasses Jacobi-tree case analysis whenever a signed semantic normalizer
family is already available.  It also isolates the genuine circular boundary:
constructing that family without assuming current-stratum normalization.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

namespace
  TRRecoll

/--
Normalize the full concrete basic-reduction residual and discard its
vanishing active-weight block.
-/
noncomputable def ofNormalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (basicRawSource factor)
      hlowerWeightPos (by omega)
      (truncated_reduction_source factor
        hfactorTruncated)
      (by
        intro x hx
        simp only [basicRawSource, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact
            hfactorWeight.ge.trans
              (SPFactor.least_inverse_list
                (least_reduction_factors factor) x hx)
        · exact hfactorWeight.ge)
      (by
        intro e
        simpa only [hfactorWeight] using
          list_reduction_series
            factor e)
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

/-- Use a signed semantic normalizer family at the factor-weight stratum. -/
noncomputable def ofNormalizerFamily
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor hfactorWeight
    hfactorTruncated

end
  TRRecoll

/--
A Hall-Petresco packet and a signed semantic normalizer family.
Current-stratum normalization recollects every concrete basic-reduction
residual directly.
-/
structure
    ANBuild
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)

namespace
  ANBuild

open
  TRRecoll

/-- Compile direct residual normalization into the automatic collector. -/
noncomputable def automaticCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ANBuild.{u}
        hn hH) :
    TPBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  basicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated =>
      ofNormalizerFamily hn hH builder.normalizerFamily factor hfactorWeight
        hfactorTruncated

end
  ANBuild

/--
For canonical Hall families, a supplied signed semantic normalizer family
directly constructs the Claim 8 product coordinate polynomials.
-/
theorem
    hall_commutators_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      ANBuild.{u}
        hn
          (concrete_forms_associated d n)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_automatic_builder
    hn e builder.automaticCollectionBuilder

/--
For canonical Hall families, a supplied signed semantic normalizer family
directly constructs the Claim 8 inverse coordinate polynomials.
-/
theorem
    collected_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      ANBuild.{u}
        hn
          (concrete_forms_associated d n)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  automatic_collect_builder
    hn e builder.automaticCollectionBuilder

end TCTex
end Towers

/-!
# Concrete signed-polynomial Jacobi continuation recollection

The atomic Jacobi correction is only the first part of a true concrete factor
residual.  This file packages the remaining continuation as an explicit
boundary and composes any recollection of that continuation with the
supported atomic correction route.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/--
Semantic recollection data for the continuation left after peeling a Jacobi
atomic correction from a true concrete factor residual.
-/
structure ConcreteContinuationRecollection
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (jacobiContinuationRaw factor left middle right hword)

namespace
  TRRecoll

/--
Combine a strictly higher atomic Jacobi correction with a strictly higher
recollection of the remaining continuation.
-/
noncomputable def jacobi_raw_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (jacobiHigherSource :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι))
    (hjacobiTruncated :
      SPFactor.IsTruncated n jacobiHigherSource)
    (hjacobiSupported :
      SPFactor.WordWeightLeast
        (factor.word.weight HEAddres.weight + 1)
        jacobiHigherSource)
    (hjacobiEval :
      ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
        SPFactor.listEval (n := n) e jacobiHigherSource =
          SPFactor.listEval e
            (jacobiReductionSource factor left middle right hword))
    (continuation :
      ConcreteContinuationRecollection
        (n := n) factor left middle right hword) :
    TRRecoll
      (n := n) factor where
  higherSource := jacobiHigherSource ++ continuation.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiTruncated x hx
    · exact continuation.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiSupported x hx
    · exact continuation.higher_least_succ x hx
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append, hjacobiEval e,
      continuation.list_higher_raw e,
      jacobi_reduction_continuation]

/--
Use the supported correction factory for the atomic Jacobi packet, leaving
only its explicit continuation recollection as an input.
-/
noncomputable def of_jacobiReduction
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (continuation :
      ConcreteContinuationRecollection
        (n := n) factor left middle right hword) :
    TRRecoll
      (n := n) factor := by
  let jacobi :=
    factory.higher_jacobi_raw hn hH sharp
      nextNormalizer factor left middle right hword hfactorWeight
        hfactorTruncated
  let jacobiHigherSource := Classical.choose jacobi
  have hjacobiTruncated := (Classical.choose_spec jacobi).1
  have hjacobiSupported := (Classical.choose_spec jacobi).2.1
  have hjacobiEval := (Classical.choose_spec jacobi).2.2
  exact
    jacobi_raw_source factor left middle right hword
      jacobiHigherSource hjacobiTruncated
        (by simpa only [hfactorWeight] using hjacobiSupported)
          hjacobiEval continuation

/--
Compile the Hall-Petresco packet and a family of strictly deeper normalizers
into the data needed to lift one syntactic Jacobi residual.
-/
noncomputable def jacobi_normalizer_above
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    {ι : Type}
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (continuation :
      ConcreteContinuationRecollection
        (n := n) factor left middle right hword) :
    TRRecoll
      (n := n) factor :=
  of_jacobiReduction hn hH
    ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      lowerWeight).correctionPacketFactory)
    (TSNormala.ofNormalizerAbove
      normalizerAbove)
    (normalizerAbove (lowerWeight + 1) (by omega))
    factor left middle right hword hfactorWeight hfactorTruncated continuation

end
  TRRecoll

/--
A cutoff packet and continuation recollections for syntactically exposed
Jacobi brackets.  Compressed Hall addresses are deliberately left to a
separate expansion boundary.
-/
structure
    SJContin
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  jacobiContinuation :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left middle right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator (.commutator left middle) right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ConcreteContinuationRecollection
                (n := n) factor left middle right hword

namespace
  SJContin

open
  TRRecoll

/--
Lift one syntactically exposed Jacobi factor using only normalizers at
strictly larger support bounds.
-/
noncomputable def jacobiResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJContin.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  jacobi_normalizer_above hn
    (fun s hs hsn =>
      concrete_forms_associated d n s hs hsn)
    builder.packet normalizerAbove factor left middle right hword
      hfactorWeight hfactorTruncated
        (builder.jacobiContinuation lowerWeight hnonterminal factor left middle
          right hword hfactorWeight hfactorTruncated)

/--
Expanded Jacobi roots with a nonbasic inner bracket automa expose the
syntactic decomposition consumed by `jacobiResidual`.
-/
noncomputable def jacobiTreeNonbasic
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJContin.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      CEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hinnerNonbasic :
      ¬(HallTree.commutator left middle).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  let decomposition :=
    syntacticTreeNonbasic
      factor.word left middle right htree houterNonbasic hinnerNonbasic
  builder.jacobiResidual lowerWeight hnonterminal normalizerAbove factor
    decomposition.left decomposition.middle decomposition.right
      decomposition.word_eq hfactorWeight hfactorTruncated

end
  SJContin
end TCTex
end Towers
