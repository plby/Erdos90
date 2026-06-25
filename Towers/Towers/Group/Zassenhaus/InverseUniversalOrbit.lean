import Towers.Group.Zassenhaus.ClassEndpointFibers
import Towers.Group.Zassenhaus.CanonicalPacketAlignment
import Towers.Group.Zassenhaus.CompatiblePacketRouting
import Towers.Group.Zassenhaus.SignedProfilePackets
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary

/-!
# Reversible finite-index profiles for the selected cutoff-full endpoint

The selected cutoff-full endpoint trace is the appended raw-source and
scheduler-correction finite-index trace.  Accordingly, an aggregate
homogeneous profile can be split again once the raw-source profile is known:
subtract the raw profile word by word.

This file packages that reversible reduction and connects the existing
raw-history/correction split recollection law to the aggregate selected-trace
route.  Thus aggregate selected-endpoint polynomial counting and selected
correction polynomial counting are equivalent after the canonical raw side
has been supplied.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open scoped commutatorElement

namespace
  CFAlg

open
  CFSubsti

namespace FPkt

/-- Additive inverse of one homogeneous multiplicity-independent packet. -/
def negate
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree :=
  scale (-1) packet

/-- Difference of two homogeneous multiplicity-independent packets. -/
def subtract
    {leftDegree rightDegree : ℕ}
    (left right :
      HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree :=
  add left (negate right)

@[simp]
lemma value_negate
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (negate packet).value left right = -packet.value left right := by
  simp [negate]

@[simp]
lemma value_subtract
    {leftDegree rightDegree : ℕ}
    (leftPacket rightPacket :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (subtract leftPacket rightPacket).value left right =
      leftPacket.value left right - rightPacket.value left right := by
  simp [subtract, sub_eq_add_neg]

end FPkt
end
  CFAlg

namespace
  FIBridge

open CRLayer
open
  ISFiber
open
  CRSplit
open
  RHSplit
open
  FIProf
open
  CFAlg
open
  CFAlg.FPkt
open
  FIBridge
open
  SICollec

namespace EIFiber

/--
Subtract a known raw-source profile from an aggregate selected-endpoint
profile.  The result counts exactly the actual selected scheduler-correction
trace.
-/
def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight where
  profiles word hword :=
    FPkt.subtract
      (kernel.profiles word hword)
      (raw.profiles word hword)
  profiles_nat_trace M N word hword := by
    rw [FPkt.value_subtract,
      kernel.profiles_nat_trace M N word hword,
      raw.profiles_cast_trace M N word hword,
      selectedFullEndpoint, List.filter_append,
      List.length_append, Int.natCast_add]
    ring

/--
Once the raw-source profile is fixed, aggregate selected-endpoint polynomial
profiles exist exactly when selected scheduler-correction profiles exist.
-/
theorem
    nonempty_fiber_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    Nonempty
        (EIFiber
          layer hleftWeight hrightWeight) ↔
      Nonempty
        (SFProf
          layer hleftWeight hrightWeight) := by
  constructor
  · rintro ⟨kernel⟩
    exact ⟨kernel.shapeFiberProfile raw⟩
  · rintro ⟨corrections⟩
    exact
      ⟨idx_fiber_profile
        raw corrections⟩

/--
Adding raw-source and correction profiles in the selected endpoint compiler
gives the same assignment as the established raw-history split compiler.
-/
lemma
    signed_profile_fiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (corrections :
      SFProf
        layer hleftWeight hrightWeight) :
    (idx_fiber_profile
        raw corrections).signedProfileAssignment =
      (ISFiber.EFSplit.idx_fiber_profile
          raw corrections
        |>.endpointRecipeFiber
        |>.signedProfileAssignment) := by
  rfl

/--
The established ordered recollection law for split raw-source and correction
profiles transports to the aggregate selected-endpoint trace route.
-/
lemma
    satisfies_trunc_split
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (corrections :
      SFProf
        layer (by simp) (by simp))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (fiberProfileSplit
          raw corrections)) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (idx_fiber_profile
        raw corrections) := by
  simpa only [
    EIFiber.SatisfiesTruncEval,
    EFSplit.SatisfiesTruncEval,
    fiberProfileSplit,
    signed_profile_fiber
  ] using hlistEval

end EIFiber

end
  FIBridge

namespace TSInput

open CRLayer
open
  ISFiber
open
  RHSplit
open
  FIProf
open
  FIBridge
open
  SICollec

/--
The established split ordered law can be routed through the aggregate
selected-endpoint finite-index trace compiler before constructing the Claim 5
coordinate polynomials.
-/
theorem
    coordSplitTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (corrections :
      SFProf
        layer (by simp) (by simp))
    (hlistEval :
      EFSplit.SatisfiesTruncEval.{u}
        (d := d)
        (fiberProfileSplit
          raw corrections))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordTruncEval
    hn H hH
      (EIFiber.idx_fiber_profile
          raw corrections)
      (EIFiber.satisfies_trunc_split
          raw corrections hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Towers

/-!
# Per-index polynomial profiles for selected cutoff-full corrections

The selected scheduler-correction trace takes values in one fixed finite
polynomial-orbit index alphabet.  It is therefore enough to construct one
homogeneous multiplicity polynomial for the number of occurrences of each
index.  Summing those polynomials over indices with a prescribed erased Hall
shape gives the shape-fiber profiles consumed by the selected-endpoint
compiler.

This file packages that finite-alphabet reduction.  The remaining symbolic
collector may now track a finite vector of index multiplicities rather than
constructing shape-fiber packets directly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  IMProf

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  CFAlg
open
  CFAlg.FPkt
open
  CFSubsti
open
  RITrace
open
  FIBridge

/--
Over a finite alphabet, the number of entries satisfying a predicate is the
sum of the occurrence counts of the satisfying alphabet symbols.
-/
lemma ite_length_filter
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (entries : List α)
    (predicate : α → Prop)
    [DecidablePred predicate] :
    (∑ index : α, if predicate index then entries.count index else 0) =
      (entries.filter fun index => decide (predicate index)).length := by
  rw [← Finset.sum_filter]
  rw [←
    Finset.sum_subset
      (s₁ := entries.toFinset.filter predicate)
      (s₂ := Finset.univ.filter predicate)
      (by
        intro index hindex
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ index, (Finset.mem_filter.mp hindex).2⟩)
      (by
        intro index hindex hnotIndex
        apply List.count_eq_zero_of_not_mem
        intro hmem
        apply hnotIndex
        exact
          Finset.mem_filter.mpr
            ⟨List.mem_toFinset.mpr hmem, (Finset.mem_filter.mp hindex).2⟩)]
  simpa only [List.countP_eq_length_filter] using
    (Finset.sum_filter_count_eq_countP predicate entries)

/--
One homogeneous polynomial packet for the number of selected correction-trace
occurrences of each finite orbit index.
-/
structure MPKern
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
      HFPkt
        (retainedOrbitKey index).erasedShape.pairLeftDegree
        (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count :
    ∀ (M N : ℕ) index,
      (profiles index).value (M : ℤ) (N : ℤ) =
        ((selectedIndexTrace
          layer M N hleftWeight hrightWeight).count index : ℤ)

namespace MPKern

/--
Transport one per-index packet to the requested shape when the indexed key
has that shape, and use zero otherwise.
-/
noncomputable def profileForShape
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  if hshape : (retainedOrbitKey index).erasedShape = word then
    hshape ▸ kernel.profiles index
  else
    FPkt.zero word.pairLeftDegree word.pairRightDegree

@[simp]
lemma value_shape
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (M N : ℤ) :
    (kernel.profileForShape word index).value M N =
      if (retainedOrbitKey index).erasedShape = word then
        (kernel.profiles index).value M N
      else
        0 := by
  classical
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · subst word
    simp [profileForShape]
  · simp [profileForShape, hshape]

/--
Sum the per-index selected-correction multiplicity profiles over all indices
with one erased Hall shape.
-/
noncomputable def shapeProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  FPkt.finsetSum Finset.univ (kernel.profileForShape word)

/--
The finite sum for one erased shape counts exactly that filtered fiber of the
actual selected scheduler-correction index trace.
-/
lemma value_length_filter
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (kernel.shapeProfile word).value (M : ℤ) (N : ℤ) =
      (((selectedIndexTrace
        layer M N hleftWeight hrightWeight).filter fun index =>
          decide
            ((retainedOrbitKey index).erasedShape =
              word)).length : ℤ) := by
  classical
  rw [shapeProfile, FPkt.value_finsetSum]
  simp_rw [value_shape,
    kernel.profiles_nat_count M N]
  exact_mod_cast
    ite_length_filter
      (selectedIndexTrace
        layer M N hleftWeight hrightWeight)
      (fun index =>
        (retainedOrbitKey index).erasedShape = word)

/--
Per-index selected-correction multiplicity profiles compile to the shape-fiber
profile kernel expected by the selected correction trace.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight where
  profiles word _hword :=
    kernel.shapeProfile word
  profiles_nat_trace M N word _hword :=
    kernel.value_length_filter M N word

/--
Together with raw-source profiles, per-index selected-correction
multiplicity profiles compile directly to the aggregate selected endpoint
trace profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  EIFiber.idx_fiber_profile
      raw kernel.shapeFiberProfile

end MPKern

end
  IMProf
end TCTex
end Towers

/-!
# Algebra of finite-index trace multiplicity profiles

The cutoff-full collector emits retained correction traces by concatenating
the traces generated by recursive calls with newly generated correction
occurrences.  This file isolates the compositional part of the polynomial
accounting: homogeneous finite-index multiplicity profiles are closed under
empty traces, trace concatenation, and pointwise trace equality.

The selected scheduler-correction profile kernel is exactly the
specialization of this generic trace kernel to the selected retained
correction trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  MPAlg

open
  CRLayer
open
  ISFiber
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  PCBridge
open
  IMProf

/--
One homogeneous polynomial packet for the multiplicity of each finite orbit
index in an arbitrary two-parameter trace family.
-/
structure IMProfa
    {n leftWeight rightWeight : ℕ}
    (trace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight)) where
  profiles :
    ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
      HFPkt
        (retainedOrbitKey index).erasedShape.pairLeftDegree
        (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count :
    ∀ (M N : ℕ) index,
      (profiles index).value (M : ℤ) (N : ℤ) =
        ((trace M N).count index : ℤ)

namespace IMProfa

/-- The empty trace family has the all-zero finite-index profile vector. -/
noncomputable def zero
    {n leftWeight rightWeight : ℕ} :
    IMProfa
      (fun _M _N =>
        ([] : List
          (RetainedOrbitIndex n leftWeight rightWeight))) where
  profiles index :=
    FPkt.zero
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count M N index := by
    rw [FPkt.value_zero]
    rfl

/--
Adding the profile vectors of two trace families gives the profile vector of
their pointwise concatenation.
-/
noncomputable def append
    {n leftWeight rightWeight : ℕ}
    {leftTrace rightTrace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight)}
    (left :
      IMProfa leftTrace)
    (right :
      IMProfa rightTrace) :
    IMProfa
      (fun M N => leftTrace M N ++ rightTrace M N) where
  profiles index :=
    FPkt.add (left.profiles index) (right.profiles index)
  profiles_nat_count M N index := by
    rw [
      FPkt.value_add,
      left.profiles_nat_count,
      right.profiles_nat_count,
      List.count_append]
    exact_mod_cast rfl

/--
Repeat one finite orbit index according to a homogeneous multiplicity packet.
This is the family-level form of a scheduler branch emitting one correction
occurrence for each selected crossing.
-/
noncomputable def replicate
    {n leftWeight rightWeight : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    IMProfa
      (fun M N => List.replicate (multiplicity M N) selected) where
  profiles index :=
    if hindex : index = selected then
      hindex ▸ profile
    else
      FPkt.zero
        (retainedOrbitKey index).erasedShape.pairLeftDegree
        (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count M N index := by
    classical
    by_cases hindex : index = selected
    · subst index
      rw [dif_pos rfl, hprofile, List.count_replicate_self]
    · rw [dif_neg hindex, FPkt.value_zero,
        List.count_replicate]
      simp [Ne.symm hindex]

/--
Transport a finite-index profile vector across a pointwise equality of trace
families.  This is the adapter used after exposing a collector recurrence.
-/
noncomputable def of_trace_eq
    {n leftWeight rightWeight : ℕ}
    {trace nextTrace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight)}
    (kernel :
      IMProfa trace)
    (htrace : ∀ M N, trace M N = nextTrace M N) :
    IMProfa nextTrace where
  profiles :=
    kernel.profiles
  profiles_nat_count M N index := by
    rw [← htrace M N]
    exact kernel.profiles_nat_count M N index

end IMProfa

/--
A trace family bundled with its finite-index homogeneous multiplicity
profiles.  Bundling lets a recursive collector concatenate a finite list of
already-profiled branches.
-/
structure PIFam
    (n leftWeight rightWeight : ℕ) where
  trace :
    ℕ → ℕ →
      List (RetainedOrbitIndex n leftWeight rightWeight)
  kernel :
    IMProfa trace

namespace PIFam

/-- Bundle the empty finite-index trace family. -/
noncomputable def zero
    {n leftWeight rightWeight : ℕ} :
    PIFam n leftWeight rightWeight where
  trace := fun _M _N => []
  kernel :=
    IMProfa.zero

/-- Bundle pointwise concatenation of two profiled finite-index traces. -/
noncomputable def append
    {n leftWeight rightWeight : ℕ}
    (left right :
      PIFam n leftWeight rightWeight) :
    PIFam n leftWeight rightWeight where
  trace := fun M N => left.trace M N ++ right.trace M N
  kernel :=
    left.kernel.append right.kernel

/-- Bundle one polynomially repeated finite orbit index. -/
noncomputable def replicate
    {n leftWeight rightWeight : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    PIFam n leftWeight rightWeight where
  trace := fun M N => List.replicate (multiplicity M N) selected
  kernel :=
    IMProfa.replicate
      selected multiplicity profile hprofile

/-- Concatenate a finite list of profiled finite-index traces in order. -/
noncomputable def concat
    {n leftWeight rightWeight : ℕ} :
    List (PIFam n leftWeight rightWeight) →
      PIFam n leftWeight rightWeight
  | [] =>
      zero
  | family :: families =>
      family.append (concat families)

@[simp]
lemma trace_zero
    {n leftWeight rightWeight : ℕ}
    (M N : ℕ) :
    (zero :
      PIFam n leftWeight rightWeight).trace M N =
        [] := by
  rfl

@[simp]
lemma trace_append
    {n leftWeight rightWeight : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (M N : ℕ) :
    (left.append right).trace M N =
      left.trace M N ++ right.trace M N := by
  rfl

@[simp]
lemma trace_replicate
    {n leftWeight rightWeight : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ))
    (M N : ℕ) :
    (replicate selected multiplicity profile hprofile).trace M N =
      List.replicate (multiplicity M N) selected := by
  rfl

@[simp]
lemma trace_concat
    {n leftWeight rightWeight : ℕ}
    (families :
      List (PIFam
        n leftWeight rightWeight))
    (M N : ℕ) :
    (concat families).trace M N =
      (families.map fun family => family.trace M N).flatten := by
  induction families with
  | nil =>
      rfl
  | cons family families ih =>
      rw [concat, trace_append, List.map_cons, List.flatten_cons, ih]

end PIFam

namespace MPKern

/--
Forget that a finite-index multiplicity profile vector belongs to the
selected scheduler-correction trace and regard it as a generic trace kernel.
-/
noncomputable def indexMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight) :
    IMProfa
      (fun M N =>
        selectedIndexTrace
          layer M N hleftWeight hrightWeight) where
  profiles :=
    kernel.profiles
  profiles_nat_count :=
    kernel.profiles_nat_count

/--
Specialize a generic finite-index multiplicity profile vector to the selected
scheduler-correction trace.
-/
noncomputable def fin_idx_mult
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      IMProfa
        (fun M N =>
          selectedIndexTrace
            layer M N hleftWeight hrightWeight)) :
    MPKern
      layer hleftWeight hrightWeight where
  profiles :=
    kernel.profiles
  profiles_nat_count :=
    kernel.profiles_nat_count

@[simp]
lemma multiplicity_profile_kernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      MPKern
        layer hleftWeight hrightWeight) :
    fin_idx_mult
        (indexMultiplicityProfile kernel) =
      kernel := by
  rfl

@[simp]
lemma index_multiplicity_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      IMProfa
        (fun M N =>
          selectedIndexTrace
            layer M N hleftWeight hrightWeight)) :
    indexMultiplicityProfile
        (fin_idx_mult kernel) =
      kernel := by
  rfl

end MPKern

end
  MPAlg
end TCTex
end Towers

/-!
# Per-index selected-correction profiles through cutoff four

Through cutoff four at root weights, the actual scheduler retains no
generated correction occurrences.  Consequently every coordinate of its
finite polynomial-orbit index vector is represented by the zero homogeneous
packet.

This file instantiates the per-index arbitrary-cutoff reduction at the known
shallow boundary and compiles it back to the shape-fiber and aggregate
selected-endpoint interfaces.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  PCThree

open
  CRLayer
open
  CRInv
open
  ISFiber
open
  FIProf
open
  FUClass
open
  CFAlg
open
  RITrace
open
  FIBridge
open
  IMProf

/--
Through cutoff four, every finite orbit-index coordinate of the selected
scheduler-correction trace has the zero homogeneous profile.
-/
noncomputable def
    multiplicityNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    MPKern
      layer (by simp) (by simp) where
  profiles index :=
    FPkt.zero
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count M N index := by
    have hlength :
        (selectedIndexTrace
          layer M N (by simp) (by simp)).length = 0 := by
      calc
        _ =
            ((selectedIndexTrace
              layer M N (by simp) (by simp)).map
                retainedOrbitKey).length := by
              simp
        _ =
            ((selectedClosurePacket
              layer M N (by simp) (by simp)).map
                ROAggreg.polynomialOrbitKey).length := by
              rw [
                key_selected_trace]
        _ =
            (endpointCorrectionInventory layer M N).corrections.length := by
              simp [selectedClosurePacket]
        _ = 0 := by
              rw [
                inventory_corrections_nil
                  layer hhigh M N]
              rfl
    have hcount :
        (selectedIndexTrace
          layer M N (by simp) (by simp)).count index = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        _ ≤
            (selectedIndexTrace
              layer M N (by simp) (by simp)).length :=
          List.count_le_length
        _ = 0 := hlength
    rw [FPkt.value_zero, hcount]
    rfl

/--
The per-index zero profile kernel compiles to selected-correction shape-fiber
profiles through cutoff four.
-/
noncomputable def
    fiberNMultiplicities
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SFProf
      layer (by simp) (by simp) :=
  (multiplicityNFour
    layer hhigh).shapeFiberProfile

/--
Together with any raw-source profile kernel, the shallow per-index zero
profiles compile directly to the aggregate selected endpoint trace profile.
-/
noncomputable def
    endpointIdxMultiplicities
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    EIFiber
      layer (by simp) (by simp) :=
  (multiplicityNFour
    layer hhigh)
      |>.selectedFullFiber raw

end
  PCThree
end TCTex
end Towers

/-!
# Recursive composition of selected-correction finite-index profiles

One retained cutoff-insertion branch emits corrections in the literal order

`leftCorrections ++ [correction] ++ rightCorrections`.

Across the two natural input multiplicities, the middle correction may occur
a polynomial number of times.  This file packages the corresponding
family-level constructor

`leftTrace ++ replicate multiplicity correctionIndex ++ rightTrace`

and compiles any such recursive trace decomposition back to the selected
scheduler-correction profile kernel and aggregate endpoint profile kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  PRCompa

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  CFSubsti
open
  RITrace
open
  FIBridge
open
  IMProf
open
  MPAlg

namespace PIFam

/--
Family-level profile constructor matching one retained cutoff-insertion
branch: recursive left corrections, polynomially many copies of the new
correction index, then recursive right corrections.
-/
noncomputable def retained
    {n leftWeight rightWeight : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    PIFam n leftWeight rightWeight :=
  left.append
    ((MPAlg.PIFam.replicate
      selected multiplicity profile hprofile).append right)

@[simp]
lemma trace_retained
    {n leftWeight rightWeight : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ))
    (M N : ℕ) :
    (retained left right selected multiplicity profile hprofile).trace M N =
      left.trace M N ++
        List.replicate (multiplicity M N) selected ++
          right.trace M N := by
  simp [retained, List.append_assoc]

end PIFam

/--
A recursively profiled finite-index family whose trace is exactly the actual
selected retained-correction trace of the cutoff-full scheduler.
-/
structure SCProfil
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  family :
    PIFam n leftWeight rightWeight
  trace_eq :
    ∀ M N,
      family.trace M N =
        selectedIndexTrace
          layer M N hleftWeight hrightWeight

namespace SCProfil

/--
A finite ordered list of profiled recursive branches constructs a selected
trace decomposition once its flattened trace is identified with the actual
scheduler trace.
-/
noncomputable def ofConcat
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (families :
      List (PIFam
        n leftWeight rightWeight))
    (htrace :
      ∀ M N,
        (families.map fun family => family.trace M N).flatten =
          selectedIndexTrace
            layer M N hleftWeight hrightWeight) :
    SCProfil
      layer hleftWeight hrightWeight where
  family :=
    PIFam.concat families
  trace_eq M N := by
    rw [PIFam.trace_concat]
    exact htrace M N

/--
One recurrence-shaped left/middle/right decomposition constructs a selected
trace decomposition once its concrete trace equation is proved.
-/
noncomputable def ofRetained
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ))
    (htrace :
      ∀ M N,
        left.trace M N ++
              List.replicate (multiplicity M N) selected ++
                right.trace M N =
          selectedIndexTrace
            layer M N hleftWeight hrightWeight) :
    SCProfil
      layer hleftWeight hrightWeight where
  family :=
    PIFam.retained
      left right selected multiplicity profile hprofile
  trace_eq M N := by
    rw [PIFam.trace_retained]
    exact htrace M N

/--
Forget the recursive branch packaging and retain the generic finite-index
trace multiplicity profile kernel.
-/
noncomputable def indexMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCProfil
        layer hleftWeight hrightWeight) :
    IMProfa
      (fun M N =>
        selectedIndexTrace
          layer M N hleftWeight hrightWeight) :=
  decomposition.family.kernel.of_trace_eq decomposition.trace_eq

/-- Compile a recursive selected-trace decomposition to per-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCProfil
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  MPKern.fin_idx_mult
    decomposition.indexMultiplicityProfile

/--
Compile a recursive selected-trace decomposition to the correction
shape-fiber profiles consumed by the endpoint compiler.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCProfil
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.shapeFiberProfile

/--
Together with raw-source profiles, a recursive selected-trace decomposition
compiles to the aggregate selected endpoint trace profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCProfil
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.selectedFullFiber raw

end SCProfil

end
  PRCompa
end TCTex
end Towers

/-!
# Overlapping-grid middle branches for selected-correction profiles

The recursive selected-correction profile compiler consumes a homogeneous
packet for the multiplicity of each repeated middle correction index.  The
support-pattern compiler already constructs exactly such a packet for one
overlapping correction grid.  This file records the missing adapter.

The concrete represented terms may vary with the two source multiplicities,
while the compiled support-avoidance packets remain fixed.  Pointwise
specialization therefore yields one homogeneous packet controlling the whole
two-parameter family of repeated middle traces.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  OCGrid

open
  HACoeff
open
  CGCompa
open
  CFSubsti
open
  CSOverla
open
  SEComp
open
  SFComp
open
  SFSpec
open
  HSPacket
open
  RITrace
open
  MPAlg
open
  PRCompa

/-- Transport a homogeneous packet across equal bidegrees. -/
noncomputable def castHomogeneousDegrees
    {leftDegree rightDegree nextLeftDegree nextRightDegree : ℕ}
    (hleftDegree : leftDegree = nextLeftDegree)
    (hrightDegree : rightDegree = nextRightDegree)
    (packet :
      HFPkt leftDegree rightDegree) :
    HFPkt nextLeftDegree nextRightDegree := by
  cases hleftDegree
  cases hrightDegree
  exact packet

@[simp]
lemma cast_homogeneous_degrees
    {leftDegree rightDegree nextLeftDegree nextRightDegree : ℕ}
    (hleftDegree : leftDegree = nextLeftDegree)
    (hrightDegree : rightDegree = nextRightDegree)
    (packet :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (castHomogeneousDegrees
      hleftDegree hrightDegree packet).value left right =
        packet.value left right := by
  cases hleftDegree
  cases hrightDegree
  rfl

namespace SASpec

/--
The fixed homogeneous overlap packet evaluates to the concrete overlapping
correction-grid cardinality whenever both parent avoidance families
specialize their fixed packets.
-/
lemma overlap_avoidance_overlapping
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    {leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree}
    {rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree}
    {leftExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftLeftDegree leftRightDegree}
    {rightExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightLeftDegree rightRightDegree}
    (left :
      SASpec
        leftTerms leftPackets leftExpressions)
    (right :
      SASpec
        rightTerms rightPackets rightExpressions) :
    (SFPkt.overlapOfAvoidance
        leftPackets rightPackets).value (M : ℤ) (N : ℤ) =
      ((overlappingCorrectionGrid leftTerms rightTerms).length : ℤ) := by
  rw [← left.expression_overlap_avoidance right,
    HFPkt.value_expression_cast]
  exact
    (overlapExpressionAvoidance
      leftExpressions rightExpressions).length_eq.symm

end SASpec

namespace PIFam

/--
Compile a fixed homogeneous support-overlap packet into the repeated middle
trace emitted by one selected correction index.
-/
noncomputable def replicateOverlappingGrid
    {n leftWeight rightWeight K : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (leftTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (rightTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (leftTerms M N) slots
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (rightTerms M N) slots
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftSpecialization :
      ∀ M N : ℕ,
        SASpec
          (leftTerms M N) leftPackets (leftExpressions M N))
    (rightSpecialization :
      ∀ M N : ℕ,
        SASpec
          (rightTerms M N) rightPackets (rightExpressions M N)) :
    PIFam n leftWeight rightWeight := by
  have hleftDegree :
      leftShape.pairLeftDegree + rightShape.pairLeftDegree =
        (retainedOrbitKey selected).erasedShape.pairLeftDegree := by
    rw [hselectedShape,
      CWord.pair_left_commutator]
  have hrightDegree :
      leftShape.pairRightDegree + rightShape.pairRightDegree =
        (retainedOrbitKey selected).erasedShape.pairRightDegree := by
    rw [hselectedShape,
      CWord.pair_degree_commutator]
  refine
    MPAlg.PIFam.replicate
      selected
      (fun M N =>
        (overlappingCorrectionGrid
          (leftTerms M N) (rightTerms M N)).length)
      (castHomogeneousDegrees
        hleftDegree hrightDegree
        (SFPkt.overlapOfAvoidance leftPackets rightPackets)) ?_
  · intro M N
    rw [cast_homogeneous_degrees]
    exact
      SASpec.overlap_avoidance_overlapping
        (leftSpecialization M N) (rightSpecialization M N)

@[simp]
lemma replicate_overlapping_grid
    {n leftWeight rightWeight K : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (leftTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (rightTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (leftTerms M N) slots
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (rightTerms M N) slots
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftSpecialization :
      ∀ M N : ℕ,
        SASpec
          (leftTerms M N) leftPackets (leftExpressions M N))
    (rightSpecialization :
      ∀ M N : ℕ,
        SASpec
          (rightTerms M N) rightPackets (rightExpressions M N))
    (M N : ℕ) :
    (replicateOverlappingGrid selected leftShape rightShape
      hselectedShape leftTerms rightTerms leftPackets rightPackets
      leftExpressions rightExpressions leftSpecialization
      rightSpecialization).trace M N =
        List.replicate
          (overlappingCorrectionGrid
            (leftTerms M N) (rightTerms M N)).length
          selected := by
  simp [replicateOverlappingGrid]

/--
Insert a support-overlap middle branch between already-profiled recursive
left and right traces.
-/
noncomputable def retainedOverlappingGrid
    {n leftWeight rightWeight K : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (leftTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (rightTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (leftTerms M N) slots
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (rightTerms M N) slots
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftSpecialization :
      ∀ M N : ℕ,
        SASpec
          (leftTerms M N) leftPackets (leftExpressions M N))
    (rightSpecialization :
      ∀ M N : ℕ,
        SASpec
          (rightTerms M N) rightPackets (rightExpressions M N)) :
    PIFam n leftWeight rightWeight :=
  left.append
    ((replicateOverlappingGrid selected leftShape rightShape
      hselectedShape leftTerms rightTerms leftPackets rightPackets
      leftExpressions rightExpressions leftSpecialization
      rightSpecialization).append right)

@[simp]
lemma overlapping_correction_grid
    {n leftWeight rightWeight K : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (leftTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (rightTerms :
      ∀ M N : ℕ, List (DFTerm M N K))
    (leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (leftTerms M N) slots
          leftShape.pairLeftDegree leftShape.pairRightDegree)
    (rightExpressions :
      ∀ (M N : ℕ) (slots : Finset (Fin K)),
        SAExpr
          (rightTerms M N) slots
          rightShape.pairLeftDegree rightShape.pairRightDegree)
    (leftSpecialization :
      ∀ M N : ℕ,
        SASpec
          (leftTerms M N) leftPackets (leftExpressions M N))
    (rightSpecialization :
      ∀ M N : ℕ,
        SASpec
          (rightTerms M N) rightPackets (rightExpressions M N))
    (M N : ℕ) :
    (retainedOverlappingGrid left right selected leftShape
      rightShape hselectedShape leftTerms rightTerms leftPackets
      rightPackets leftExpressions rightExpressions leftSpecialization
      rightSpecialization).trace M N =
        left.trace M N ++
          List.replicate
            (overlappingCorrectionGrid
              (leftTerms M N) (rightTerms M N)).length
            selected ++
          right.trace M N := by
  simp [retainedOverlappingGrid, List.append_assoc]

end PIFam

end
  OCGrid
end TCTex
end Towers

/-!
# Permutation of_trace_eq for finite-index multiplicity profiles

Operational correction routing groups emitted terms by opened compatible
grids only up to permutation.  Finite-index multiplicity profiles count
occurrences and therefore do not depend on trace order.  This file records the
corresponding of_trace_eq operation without weakening the ordered trace APIs
used by the recursive scheduler compiler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  MPPerm

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  RITrace
open
  FIBridge
open
  MPAlg
open
  IMProf
open
  PRCompa

namespace IMProfa

/--
Transport a profile vector across a pointwise permutation of finite-index
traces.  Counts, unlike operational order, are permutation invariant.
-/
noncomputable def transportPerm
    {n leftWeight rightWeight : ℕ}
    {trace nextTrace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight)}
    (kernel :
      IMProfa trace)
    (htrace : ∀ M N, List.Perm (trace M N) (nextTrace M N)) :
    IMProfa nextTrace where
  profiles :=
    kernel.profiles
  profiles_nat_count M N index := by
    rw [← (htrace M N).count_eq index]
    exact kernel.profiles_nat_count M N index

end IMProfa

namespace PIFam

/-- Replace the concrete trace of a profiled family by any pointwise permutation. -/
noncomputable def transportPerm
    {n leftWeight rightWeight : ℕ}
    (family :
      PIFam n leftWeight rightWeight)
    (nextTrace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight))
    (htrace :
      ∀ M N, List.Perm (family.trace M N) (nextTrace M N)) :
    PIFam n leftWeight rightWeight where
  trace :=
    nextTrace
  kernel :=
    MPPerm.IMProfa.transportPerm
      family.kernel htrace

@[simp]
lemma trace_transportPerm
    {n leftWeight rightWeight : ℕ}
    (family :
      PIFam n leftWeight rightWeight)
    (nextTrace :
      ℕ → ℕ →
        List (RetainedOrbitIndex n leftWeight rightWeight))
    (htrace :
      ∀ M N, List.Perm (family.trace M N) (nextTrace M N))
    (M N : ℕ) :
    (MPPerm.PIFam.transportPerm
      family nextTrace htrace).trace M N =
      nextTrace M N := by
  rfl

end PIFam

/--
A profiled finite-index trace family identified with the actual selected
scheduler-correction trace only up to permutation.
-/
structure SPPerm
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  family :
    PIFam n leftWeight rightWeight
  trace_perm :
    ∀ M N,
      List.Perm (family.trace M N)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace SPPerm

/--
A finite list of profiled branches constructs a permuted selected-trace
decomposition once its flattened trace is identified with the scheduler trace
up to permutation.
-/
noncomputable def ofConcat
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (families :
      List (PIFam
        n leftWeight rightWeight))
    (htrace :
      ∀ M N,
        List.Perm
          ((families.map fun family => family.trace M N).flatten)
          (selectedIndexTrace
            layer M N hleftWeight hrightWeight)) :
    SPPerm
      layer hleftWeight hrightWeight where
  family :=
    PIFam.concat families
  trace_perm M N := by
    rw [PIFam.trace_concat]
    exact htrace M N

/-- Every exact selected-trace decomposition is also a permuted decomposition. -/
noncomputable def ofExact
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCProfil
        layer hleftWeight hrightWeight) :
    SPPerm
      layer hleftWeight hrightWeight where
  family :=
    decomposition.family
  trace_perm M N := by
    rw [decomposition.trace_eq M N]

/-- Forget a permuted decomposition to the selected scheduler profile kernel. -/
noncomputable def indexMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPPerm
        layer hleftWeight hrightWeight) :
    IMProfa
      (fun M N =>
        selectedIndexTrace
          layer M N hleftWeight hrightWeight) :=
  MPPerm.IMProfa.transportPerm
    decomposition.family.kernel decomposition.trace_perm

/-- Compile a permuted selected-trace decomposition to per-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPPerm
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  MPKern.fin_idx_mult
    decomposition.indexMultiplicityProfile

/-- Compile a permuted selected trace to correction shape-fiber profiles. -/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPPerm
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.shapeFiberProfile

/--
Together with raw-source profiles, compile a permuted selected trace to the
aggregate selected endpoint profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPPerm
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.selectedFullFiber raw

end SPPerm

end
  MPPerm
end TCTex
end Towers

/-!
# Recursive selected-correction profile composition through cutoff four

Through cutoff four at root weights, the selected scheduler-correction trace
is empty.  This file instantiates the recursive trace-profile compiler with
the empty profiled family and compiles the resulting decomposition back to
per-index, shape-fiber, and aggregate endpoint profile kernels.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  CCThreea

open
  CRLayer
open
  ISFiber
open
  CRInv
open
  FIProf
open
  FUClass
open
  RITrace
open
  FIBridge
open
  IMProf
open
  MPAlg
open
  PRCompa

/-- Through cutoff four, the selected finite-index correction trace is empty. -/
lemma selected_nil_n
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    selectedIndexTrace
      layer M N (by simp) (by simp) = [] := by
  apply List.length_eq_zero_iff.mp
  calc
    _ =
        ((selectedIndexTrace
          layer M N (by simp) (by simp)).map
            retainedOrbitKey).length := by
          simp
    _ =
        ((selectedClosurePacket
          layer M N (by simp) (by simp)).map
            ROAggreg.polynomialOrbitKey).length := by
          rw [
            key_selected_trace]
    _ =
        (endpointCorrectionInventory layer M N).corrections.length := by
          simp [selectedClosurePacket]
    _ = 0 := by
          rw [
            inventory_corrections_nil
              layer hhigh M N]
          rfl

/--
Through cutoff four, the actual selected scheduler-correction trace is the
empty recursively profiled family.
-/
noncomputable def selectedProfiledN
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SCProfil
      layer (by simp) (by simp) where
  family :=
    PIFam.zero
  trace_eq M N := by
    rw [PIFam.trace_zero]
    exact
      (selected_nil_n
        layer hhigh M N).symm

/--
The shallow empty recursive decomposition compiles to one homogeneous
selected-correction profile packet for every finite orbit index.
-/
noncomputable def
    nRecursiveComposition
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    MPKern
      layer (by simp) (by simp) :=
  (selectedProfiledN layer hhigh)
    |>.multiplicityProfileKernel

/--
The same recursive decomposition compiles to selected-correction shape-fiber
profiles through cutoff four.
-/
noncomputable def
    fiberRecursiveComposition
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SFProf
      layer (by simp) (by simp) :=
  (selectedProfiledN layer hhigh)
    |>.shapeFiberProfile

/--
Together with raw-source profiles, the empty recursive decomposition compiles
to the aggregate selected endpoint trace profile through cutoff four.
-/
noncomputable def
    idxRecComp
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    EIFiber
      layer (by simp) (by simp) :=
  (selectedProfiledN layer hhigh)
    |>.selectedFullFiber raw

end
  CCThreea
end TCTex
end Towers

/-!
# Compatible-grid middle branches for selected-correction profiles

The overlap packet controls the support-rejected part of a Cartesian
correction grid.  The operational collector emits the complementary
support-compatible grid.  This file subtracts the fixed overlap packet from
the fixed full Cartesian packet, proves that the result evaluates to the
compatible-grid cardinality, and packages that packet as a repeated selected
finite-index trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  CCGrid

open
  HACoeff
open
  CCGrida
open
  CSFilter
open
  CGComp
open
  CFAlg
open
  CFSubsti
open
  CSOverla
open
  COAvoida
open
  SEComp
open
  SFComp
open
  SFSpec
open
  HSPacket
open
  RITrace
open
  MPAlg
open
  OCGrid

/--
The homogeneous packet for the support-compatible part of one correction
grid: full Cartesian product minus the support-overlap packet.
-/
noncomputable def compatibleGridAvoidance
    {K : ℕ}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree)
    (right :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree) :
    HFPkt
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) :=
  CGComp.FPkt.subtract
    (FPkt.multiply (left ∅) (right ∅))
    (SFPkt.overlapOfAvoidance left right)

/--
Data needed to specialize one fixed homogeneous compatible-grid packet at
every pair of natural source multiplicities.
-/
structure CGFam
    (K : ℕ)
    (leftShape rightShape : CWord HPAtom) where
  leftTerms :
    ∀ M N : ℕ, List (DFTerm M N K)
  rightTerms :
    ∀ M N : ℕ, List (DFTerm M N K)
  leftPackets :
    ∀ _slots : Finset (Fin K),
      HFPkt
        leftShape.pairLeftDegree leftShape.pairRightDegree
  rightPackets :
    ∀ _slots : Finset (Fin K),
      HFPkt
        rightShape.pairLeftDegree rightShape.pairRightDegree
  leftExpressions :
    ∀ (M N : ℕ) (slots : Finset (Fin K)),
      SAExpr
        (leftTerms M N) slots
        leftShape.pairLeftDegree leftShape.pairRightDegree
  rightExpressions :
    ∀ (M N : ℕ) (slots : Finset (Fin K)),
      SAExpr
        (rightTerms M N) slots
        rightShape.pairLeftDegree rightShape.pairRightDegree
  leftSpecialization :
    ∀ M N : ℕ,
      SASpec
        (leftTerms M N) leftPackets (leftExpressions M N)
  rightSpecialization :
    ∀ M N : ℕ,
      SASpec
        (rightTerms M N) rightPackets (rightExpressions M N)
  leftShape_eq :
    ∀ (M N : ℕ) leftTerm,
      leftTerm ∈ leftTerms M N →
        leftTerm.erasedShape = leftShape
  rightShape_eq :
    ∀ (M N : ℕ) rightTerm,
      rightTerm ∈ rightTerms M N →
        rightTerm.erasedShape = rightShape
  leftWitness :
    ∀ M N : ℕ, DFTerm M N K
  rightWitness :
    ∀ M N : ℕ, DFTerm M N K
  leftWitness_mem :
    ∀ M N : ℕ, leftWitness M N ∈ leftTerms M N
  rightWitness_mem :
    ∀ M N : ℕ, rightWitness M N ∈ rightTerms M N
  witness_compatible :
    ∀ M N : ℕ,
      correctionPairCompatible (leftWitness M N) (rightWitness M N)

namespace CGFam

/-- Fixed homogeneous packet attached to a compatible-grid profile family. -/
noncomputable def packet
    {K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (family :
      CGFam K leftShape rightShape) :
    HFPkt
      (leftShape.pairLeftDegree + rightShape.pairLeftDegree)
      (leftShape.pairRightDegree + rightShape.pairRightDegree) :=
  compatibleGridAvoidance
    family.leftPackets family.rightPackets

/-- The fixed compatible-grid packet evaluates to the emitted grid length. -/
lemma length_compatible_grid
    {K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (family :
      CGFam K leftShape rightShape)
    (M N : ℕ) :
    family.packet.value (M : ℤ) (N : ℤ) =
      ((compatibleCorrectionGrid
        (family.leftTerms M N) (family.rightTerms M N)).length : ℤ) := by
  rw [packet, compatibleGridAvoidance,
    CGComp.FPkt.value_subtract,
    FPkt.value_multiply,
    (family.leftSpecialization M N).cast_avoiding_slots,
    (family.rightSpecialization M N).cast_avoiding_slots,
    SASpec.overlap_avoidance_overlapping
      (family.leftSpecialization M N) (family.rightSpecialization M N)]
  simp only [termsAvoidingSlots, Finset.disjoint_empty_left, decide_true,
    List.filter_true]
  have hpartition :=
    grid_perm_incompatible
      (family.leftTerms M N) (family.rightTerms M N)
  rw [incompatible_grid_overlapping
    (family.leftShape_eq M N) (family.rightShape_eq M N)
    (family.leftWitness_mem M N) (family.rightWitness_mem M N)
    (family.witness_compatible M N)] at hpartition
  have hlength :=
    congrArg (fun length : ℕ => (length : ℤ)) hpartition.length_eq
  simp only [List.length_append, Int.natCast_add] at hlength
  have hgrid :
      (DFTerm.correctionGrid
        (family.leftTerms M N) (family.rightTerms M N)).length =
          (family.leftTerms M N).length *
            (family.rightTerms M N).length := by
    simp [DFTerm.correctionGrid, List.length_flatMap]
  rw [hgrid, Int.natCast_mul] at hlength
  omega

end CGFam

namespace PIFam

/--
Compile a support-compatible correction grid into the repeated selected
finite-index middle trace emitted by one operational batch.
-/
noncomputable def replicateCompatibleGrid
    {n leftWeight rightWeight K : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (family :
      CGFam K leftShape rightShape) :
    PIFam n leftWeight rightWeight := by
  have hleftDegree :
      leftShape.pairLeftDegree + rightShape.pairLeftDegree =
        (retainedOrbitKey selected).erasedShape.pairLeftDegree := by
    rw [hselectedShape,
      CWord.pair_left_commutator]
  have hrightDegree :
      leftShape.pairRightDegree + rightShape.pairRightDegree =
        (retainedOrbitKey selected).erasedShape.pairRightDegree := by
    rw [hselectedShape,
      CWord.pair_degree_commutator]
  refine
    MPAlg.PIFam.replicate
      selected
      (fun M N =>
        (compatibleCorrectionGrid
          (family.leftTerms M N) (family.rightTerms M N)).length)
      (castHomogeneousDegrees
        hleftDegree hrightDegree family.packet) ?_
  intro M N
  rw [cast_homogeneous_degrees]
  exact family.length_compatible_grid M N

@[simp]
lemma replicate_compatible_grid
    {n leftWeight rightWeight K : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (family :
      CGFam K leftShape rightShape)
    (M N : ℕ) :
    (replicateCompatibleGrid selected leftShape rightShape
      hselectedShape family).trace M N =
        List.replicate
          (compatibleCorrectionGrid
            (family.leftTerms M N) (family.rightTerms M N)).length
          selected := by
  simp [replicateCompatibleGrid]

/--
Insert one profiled support-compatible correction grid between recursive left
and right traces.
-/
noncomputable def retainedCompatibleGrid
    {n leftWeight rightWeight K : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (family :
      CGFam K leftShape rightShape) :
    PIFam n leftWeight rightWeight :=
  left.append
    ((replicateCompatibleGrid selected leftShape rightShape
      hselectedShape family).append right)

@[simp]
lemma compatible_correction_grid
    {n leftWeight rightWeight K : ℕ}
    (left right :
      PIFam n leftWeight rightWeight)
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (leftShape rightShape : CWord HPAtom)
    (hselectedShape :
      (retainedOrbitKey selected).erasedShape =
        CWord.commutator leftShape rightShape)
    (family :
      CGFam K leftShape rightShape)
    (M N : ℕ) :
    (retainedCompatibleGrid left right selected leftShape
      rightShape hselectedShape family).trace M N =
        left.trace M N ++
          List.replicate
            (compatibleCorrectionGrid
              (family.leftTerms M N) (family.rightTerms M N)).length
            selected ++
          right.trace M N := by
  simp [retainedCompatibleGrid, List.append_assoc]

end PIFam

end
  CCGrid
end TCTex
end Towers

/-!
# Recursive polynomial-orbit expansions for selected-correction profiles

The recipe-free polynomial-orbit obstruction tree is finite and
multiplicity-independent.  If two parent orbit keys occur with homogeneous
multiplicity packets, every Cartesian parent crossing emits one correction
key.  Its multiplicity packet is the product of the parent packets.  The two
higher-weight obstruction children then recollect the left-versus-correction
and right-versus-correction crossings recursively.

This file compiles that conservative symbolic expansion into profiled
finite-index traces.  A finite root list can therefore be compiled once a
collector-specific theorem identifies its flattened expanded trace with the
actual selected scheduler trace up to permutation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  OEBounda

open
  RRPkt
open
  RRPkt.POObstru
open
  ROAggreg
open
  ROTransi
open
  CRLayer
open
  ISFiber
open
  FIProf
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  RIRecurs
open
  FIBridge
open
  MPAlg
open
  IMProf
open
  OCGrid
open
  MPPerm

/--
A two-parameter homogeneous multiplicity packet attached to one recipe-free
polynomial-orbit key.
-/
structure MPFam
    (key : POKey) where
  multiplicity :
    ℕ → ℕ → ℕ
  packet :
    HFPkt
      key.erasedShape.pairLeftDegree
      key.erasedShape.pairRightDegree
  value_packet_multiplicity :
    ∀ M N : ℕ,
      packet.value (M : ℤ) (N : ℤ) =
        (multiplicity M N : ℤ)

namespace MPFam

/--
Every Cartesian crossing of two profiled parent orbit families contributes
one occurrence of their correction orbit key.
-/
noncomputable def correction
    (O : POObstru)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right) :
    MPFam O.correction := by
  have hleftDegree :
      O.left.erasedShape.pairLeftDegree +
          O.right.erasedShape.pairLeftDegree =
        O.correction.erasedShape.pairLeftDegree := by
    simp [POObstru.correction, orbitCorrection,
      CWord.pair_left_commutator]
  have hrightDegree :
      O.left.erasedShape.pairRightDegree +
          O.right.erasedShape.pairRightDegree =
        O.correction.erasedShape.pairRightDegree := by
    simp [POObstru.correction, orbitCorrection,
      CWord.pair_degree_commutator]
  exact {
    multiplicity :=
      fun M N => left.multiplicity M N * right.multiplicity M N
    packet :=
      castHomogeneousDegrees
        hleftDegree hrightDegree
          (FPkt.multiply left.packet right.packet)
    value_packet_multiplicity := by
      intro M N
      rw [cast_homogeneous_degrees,
        FPkt.value_multiply,
        left.value_packet_multiplicity,
        right.value_packet_multiplicity,
        Int.natCast_mul] }

/-- Finite dictionary index selected by the correction key of one supported obstruction. -/
noncomputable def correctionIndex
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O) :
    RetainedOrbitIndex n leftWeight rightWeight :=
  indexOrbitKey
    ⟨O.correction,
      correction_supported
        hleftWeight hrightWeight O hsupport⟩

@[simp]
lemma retained_key_index
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O) :
    retainedOrbitKey
        (correctionIndex hleftWeight hrightWeight O hsupport) =
      O.correction := by
  apply orbit_key_index

/-- Compile one profiled correction key to its polynomially repeated index trace. -/
noncomputable def correctionReplicate
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (profile :
      MPFam O.correction) :
    PIFam n leftWeight rightWeight := by
  let selected :=
    correctionIndex hleftWeight hrightWeight O hsupport
  have hleftDegree :
      O.correction.erasedShape.pairLeftDegree =
        (retainedOrbitKey selected).erasedShape.pairLeftDegree := by
    rw [retained_key_index]
  have hrightDegree :
      O.correction.erasedShape.pairRightDegree =
        (retainedOrbitKey selected).erasedShape.pairRightDegree := by
    rw [retained_key_index]
  refine
    PIFam.replicate selected profile.multiplicity
      (castHomogeneousDegrees
        hleftDegree hrightDegree profile.packet) ?_
  intro M N
  rw [cast_homogeneous_degrees]
  exact profile.value_packet_multiplicity M N

@[simp]
lemma trace_correctionReplicate
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (profile :
      MPFam O.correction)
    (M N : ℕ) :
    (correctionReplicate
      hleftWeight hrightWeight O hsupport profile).trace M N =
        List.replicate (profile.multiplicity M N)
          (correctionIndex hleftWeight hrightWeight O hsupport) := by
  simp [correctionReplicate]

end MPFam

/--
Recursively compile the conservative correction expansion rooted at one
supported recipe-free polynomial-orbit obstruction.
-/
noncomputable def profiledOrbitExpansion
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right) :
    PIFam n leftWeight rightWeight :=
  let root :=
    left.correction O right
  let nestedLeft :=
    if hleft :
        O.operationalNestedLeft.weight leftWeight rightWeight < n then
      profiledOrbitExpansion
        hleftWeight hrightWeight O.operationalNestedLeft
        (operational_left_supported
          hleftWeight hrightWeight O hsupport hleft)
        left root
    else
      PIFam.zero
  let nestedRight :=
    if hright :
        O.operationalNestedRight.weight leftWeight rightWeight < n then
      profiledOrbitExpansion
        hleftWeight hrightWeight O.operationalNestedRight
        (operational_nested_supported
          hleftWeight hrightWeight O hsupport hright)
        right root
    else
      PIFam.zero
  root.correctionReplicate hleftWeight hrightWeight O hsupport
    |>.append (nestedLeft.append nestedRight)
termination_by O.defect n leftWeight rightWeight
decreasing_by
  · exact
      O.nestedLeftDescends
        hleftWeight hrightWeight hleft
  · exact
      O.nestedRightDescends
        hleftWeight hrightWeight hright

/--
The compiled expansion exposes the repeated correction root followed by its
two surviving higher-weight recursive branches.
-/
lemma trace_profiled_expansion
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    (profiledOrbitExpansion
      hleftWeight hrightWeight O hsupport left right).trace M N =
        List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            (MPFam.correctionIndex
              hleftWeight hrightWeight O hsupport) ++
          (if hleft :
              O.operationalNestedLeft.weight leftWeight rightWeight < n then
            (profiledOrbitExpansion
              hleftWeight hrightWeight O.operationalNestedLeft
              (operational_left_supported
                hleftWeight hrightWeight O hsupport hleft)
              left (left.correction O right)).trace M N
          else []) ++
          (if hright :
              O.operationalNestedRight.weight leftWeight rightWeight < n then
            (profiledOrbitExpansion
              hleftWeight hrightWeight O.operationalNestedRight
              (operational_nested_supported
                hleftWeight hrightWeight O hsupport hright)
              right (left.correction O right)).trace M N
          else []) := by
  rw [profiledOrbitExpansion]
  simp only [
    MPFam.trace_correctionReplicate,
    PIFam.trace_append]
  dsimp only [MPFam.correction]
  split <;> split <;> simp [List.append_assoc]

/--
One profiled conservative root branch: a supported orbit obstruction together
with homogeneous packets for the multiplicities of its two parent keys.
-/
structure POBranch
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  obstruction :
    POObstru
  support :
    IsSupported (n := n) hleftWeight hrightWeight obstruction
  left :
    MPFam obstruction.left
  right :
    MPFam obstruction.right

namespace POBranch

/-- Compile one symbolic root branch to its recursively expanded profiled trace. -/
noncomputable def profiledIndexFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PIFam n leftWeight rightWeight :=
  profiledOrbitExpansion
    hleftWeight hrightWeight branch.obstruction branch.support
      branch.left branch.right

/-- Concrete expanded finite-index trace of one symbolic root branch. -/
def indexTrace
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  branch.profiledIndexFamily.trace M N

/-- Concatenate a finite list of recursively expanded symbolic root branches. -/
noncomputable def concat
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branches :
      List (POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)) :
    PIFam n leftWeight rightWeight :=
  PIFam.concat
    (branches.map profiledIndexFamily)

@[simp]
lemma trace_concat
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branches :
      List (POBranch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (M N : ℕ) :
    (concat branches).trace M N =
      (branches.map fun branch => branch.indexTrace M N).flatten := by
  rw [concat, PIFam.trace_concat]
  rw [List.map_map]
  rfl

end POBranch

/--
A finite symbolic root list whose recursively expanded trace is the actual
selected retained-correction scheduler trace up to permutation.
-/
structure SPExp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  branches :
    List (POBranch
      n leftWeight rightWeight hleftWeight hrightWeight)
  trace_perm :
    ∀ M N,
      List.Perm
        ((branches.map fun branch => branch.indexTrace M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace SPExp

/-- Forget recursive orbit packaging and retain the generic permuted decomposition. -/
noncomputable def selectedProfiledPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPExp
        layer hleftWeight hrightWeight) :
    SPPerm
      layer hleftWeight hrightWeight where
  family :=
    POBranch.concat decomposition.branches
  trace_perm M N := by
    rw [POBranch.trace_concat]
    exact decomposition.trace_perm M N

/-- Compile a symbolic orbit-expansion decomposition to per-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPExp
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  decomposition.selectedProfiledPermutation
    |>.multiplicityProfileKernel

/-- Compile a symbolic orbit-expansion decomposition to correction shape fibers. -/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPExp
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.shapeFiberProfile

/--
Together with raw-source profiles, compile a symbolic orbit expansion to the
aggregate selected endpoint kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPExp
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.selectedFullFiber raw

end SPExp

end
  OEBounda
end TCTex
end Towers

/-!
# Finite compatible-grid branch lists for selected-correction profiles

One operational scheduler batch contributes a support-compatible correction
grid, encoded as repeated copies of one selected retained orbit index.  A
finite list of such batches contributes the flattened concatenation of those
repeated-index traces.  This file packages that reduction and compiles the
result to the selected scheduler profile kernel once the remaining
collector-specific flattened-trace permutation theorem is supplied.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  GBList

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  CCGrida
open
  RITrace
open
  FIBridge
open
  MPAlg
open
  IMProf
open
  CCGrid
open
  MPPerm

/--
One profiled scheduler batch: a selected retained orbit index together with a
two-parameter support-compatible correction-grid packet family of the same
erased Hall shape.
-/
structure PGBranch
    (n leftWeight rightWeight : ℕ) where
  K :
    ℕ
  selected :
    RetainedOrbitIndex n leftWeight rightWeight
  leftShape :
    CWord HPAtom
  rightShape :
    CWord HPAtom
  selectedShape_eq :
    (retainedOrbitKey selected).erasedShape =
      CWord.commutator leftShape rightShape
  family :
    CGFam K leftShape rightShape

namespace PGBranch

/-- Concrete repeated-index trace contributed by one compatible-grid branch. -/
def indexTrace
    {n leftWeight rightWeight : ℕ}
    (branch :
      PGBranch n leftWeight rightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  List.replicate
    (compatibleCorrectionGrid
      (branch.family.leftTerms M N)
      (branch.family.rightTerms M N)).length
    branch.selected

/-- Compile one compatible-grid branch to a profiled finite-index family. -/
noncomputable def profiledIndexFamily
    {n leftWeight rightWeight : ℕ}
    (branch :
      PGBranch n leftWeight rightWeight) :
    PIFam n leftWeight rightWeight :=
  PIFam.replicateCompatibleGrid
    branch.selected branch.leftShape branch.rightShape
    branch.selectedShape_eq branch.family

@[simp]
lemma profiled_index_family
    {n leftWeight rightWeight : ℕ}
    (branch :
      PGBranch n leftWeight rightWeight)
    (M N : ℕ) :
    branch.profiledIndexFamily.trace M N =
      branch.indexTrace M N := by
  simp [profiledIndexFamily, indexTrace]

/-- Concatenate a finite ordered branch list into one profiled trace family. -/
noncomputable def concat
    {n leftWeight rightWeight : ℕ}
    (branches :
      List (PGBranch
        n leftWeight rightWeight)) :
    PIFam n leftWeight rightWeight :=
  PIFam.concat
    (branches.map profiledIndexFamily)

@[simp]
lemma trace_concat
    {n leftWeight rightWeight : ℕ}
    (branches :
      List (PGBranch
        n leftWeight rightWeight))
    (M N : ℕ) :
    (concat branches).trace M N =
      (branches.map fun branch => branch.indexTrace M N).flatten := by
  rw [concat, PIFam.trace_concat]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro branch _hbranch
  exact profiled_index_family branch M N

end PGBranch

/--
A finite list of profiled compatible-grid batches whose flattened index trace
is the actual selected retained-correction scheduler trace up to permutation.
-/
structure SPDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  branches :
    List (PGBranch
      n leftWeight rightWeight)
  trace_perm :
    ∀ M N,
      List.Perm
        ((branches.map fun branch => branch.indexTrace M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace SPDecomp

/-- Forget branch packaging and retain the generic permuted decomposition. -/
noncomputable def selectedProfiledPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPDecomp
        layer hleftWeight hrightWeight) :
    SPPerm
      layer hleftWeight hrightWeight where
  family :=
    PGBranch.concat decomposition.branches
  trace_perm M N := by
    rw [PGBranch.trace_concat]
    exact decomposition.trace_perm M N

/-- Compile a finite compatible-grid branch decomposition to per-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPDecomp
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  decomposition.selectedProfiledPermutation
    |>.multiplicityProfileKernel

/-- Compile a finite compatible-grid branch decomposition to correction shape fibers. -/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPDecomp
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.shapeFiberProfile

/--
Together with raw-source profiles, compile a finite compatible-grid branch
decomposition to the aggregate selected endpoint kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPDecomp
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.multiplicityProfileKernel
    |>.selectedFullFiber raw

end SPDecomp

end
  GBList
end TCTex
end Towers

/-!
# Raw-source finite-index profiles for recursive polynomial-orbit expansions

The retained inverse-raw boundary previously stabilized erased-shape fibers.
Recursive polynomial-orbit collection needs a finer input: one homogeneous
multiplicity packet for each retained source-orbit index.  Summing those
packets over indices of one erased shape recovers the earlier raw shape-fiber
interface.

This file packages that refinement and uses it to seed the conservative
recursive orbit-expansion compiler from pairs of retained source indices.
A finite source-index branch list therefore compiles to the selected endpoint
profiles once a collector-specific theorem identifies its expanded trace
with the actual selected scheduler trace up to permutation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  ESIdx

open
  HACoeff
open
  ROAggreg
open
  RRPkt
open
  BRSpec
open
  CRLayer
open
  ISFiber
open
  FIProf
open
  RFTransv
open
  CFAlg
open
  CFAlg.FPkt
open
  CFSubsti
open
  RITrace
open
  IEDecomp
open
  RIRecurs
open
  FIBridge
open
  IMProf
open
  OEBounda
open
  ACAlign

/--
One homogeneous multiplicity packet for each retained raw-source orbit index.
This is the per-key refinement of retained raw erased-shape stabilization.
-/
structure RMProf
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
      HFPkt
        (retainedOrbitKey index).erasedShape.pairLeftDegree
        (retainedOrbitKey index).erasedShape.pairRightDegree
  profiles_nat_count :
    ∀ (M N : ℕ) index,
      (profiles index).value (M : ℤ) (N : ℤ) =
        ((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).count index :
            ℤ)

namespace RMProf

/--
Transport one per-index raw-source packet to a requested erased shape, using
zero for indices with another shape.
-/
noncomputable def profileForShape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  if hshape : (retainedOrbitKey index).erasedShape = word then
    hshape ▸ kernel.profiles index
  else
    FPkt.zero word.pairLeftDegree word.pairRightDegree

@[simp]
lemma value_shape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (M N : ℤ) :
    (kernel.profileForShape word index).value M N =
      if (retainedOrbitKey index).erasedShape = word then
        (kernel.profiles index).value M N
      else
        0 := by
  classical
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · subst word
    simp [profileForShape]
  · simp [profileForShape, hshape]

/-- Sum the raw-source per-index profiles over one erased Hall shape. -/
noncomputable def shapeProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  FPkt.finsetSum Finset.univ (kernel.profileForShape word)

/--
The finite sum of raw-source per-index profiles counts the corresponding
filtered source-trace shape fiber.
-/
lemma value_length_filter
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (kernel.shapeProfile word).value (M : ℤ) (N : ℤ) =
      (((universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight).filter
          fun index =>
            decide
              ((retainedOrbitKey index).erasedShape =
                word)).length : ℤ) := by
  classical
  rw [shapeProfile, FPkt.value_finsetSum]
  simp_rw [value_shape,
    kernel.profiles_nat_count M N]
  exact_mod_cast
    ite_length_filter
      (universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      (fun index =>
        (retainedOrbitKey index).erasedShape = word)

/--
Per-index raw-source multiplicity profiles recover the earlier shape-fiber
raw-source profile kernel by finite summation.
-/
noncomputable def idxFiberProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight where
  profiles word _hword :=
    kernel.shapeProfile word
  profiles_cast_trace M N word _hword :=
    kernel.value_length_filter M N word

/--
Regard the raw-source multiplicity packet at one finite index as a profiled
recipe-free polynomial-orbit family.
-/
noncomputable def multiplicityProfileFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    MPFam
      (retainedOrbitKey index) where
  multiplicity :=
    fun M N =>
      (universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight).count index
  packet :=
    kernel.profiles index
  value_packet_multiplicity :=
    fun M N =>
      kernel.profiles_nat_count M N index

end RMProf

/--
Canonical raw-source transversal representatives with one exact retained
polynomial-orbit key.
-/
noncomputable def rawTransversalIndex
    (n leftWeight rightWeight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    List BRecipe :=
  (retainedRawTransversal
    n leftWeight rightWeight).filter fun recipe =>
      decide (polynomialOrbitKey recipe = retainedOrbitKey index)

/-- Every recipe in an exact source-index transversal chunk has that index's shape. -/
lemma erased_transversal_index
    {n leftWeight rightWeight : ℕ}
    {index : RetainedOrbitIndex n leftWeight rightWeight}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈
        rawTransversalIndex
          n leftWeight rightWeight index) :
    recipe.erasedShape =
      (retainedOrbitKey index).erasedShape := by
  have hkey :
      polynomialOrbitKey recipe = retainedOrbitKey index :=
    of_decide_eq_true (List.mem_filter.mp hrecipe).2
  exact congrArg POKey.erasedShape hkey

/--
Concrete homogeneous raw-source candidate for one retained orbit index,
obtained from the canonical polynomial-orbit transversal.
-/
noncomputable def transversalProfileIndex
    (n leftWeight rightWeight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  HFPkt.ofRecipeChunk
    (retainedOrbitKey index).erasedShape
    (rawTransversalIndex
      n leftWeight rightWeight index)
    fun _recipe hrecipe =>
      erased_transversal_index
        hrecipe

/-- The exact-index raw-source candidate evaluates as its explicit recipe sum. -/
lemma value_transversal_index
    (n leftWeight rightWeight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftExponent rightExponent : ℤ) :
    (transversalProfileIndex
      n leftWeight rightWeight index).value leftExponent rightExponent =
        ((rawTransversalIndex
          n leftWeight rightWeight index).map fun recipe =>
            coefficientValue recipe leftExponent rightExponent).sum := by
  rw [transversalProfileIndex,
    HFPkt.value_recipe_chunk]

/--
Exact finite-index raw-source stabilization for the canonical transversal.
This is the scalar theorem needed to seed the recursive orbit collector.
-/
def RawTransversalCounts
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop :=
  ∀ (M N : ℕ) index,
    (transversalProfileIndex
      n leftWeight rightWeight index).value (M : ℤ) (N : ℤ) =
        ((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).count index :
            ℤ)

/--
Exact finite-index transversal stabilization constructs the raw-source
per-index multiplicity kernel consumed by the recursive collector.
-/
noncomputable def
    multiplicityTransversalCounts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hcounts :
      RawTransversalCounts
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RMProf
      n leftWeight rightWeight hleftWeight hrightWeight where
  profiles :=
    transversalProfileIndex
      n leftWeight rightWeight
  profiles_nat_count :=
    hcounts

/--
One conservative recursive correction root selected by two retained
raw-source orbit indices.
-/
structure IOBranch
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  leftIndex :
    RetainedOrbitIndex n leftWeight rightWeight
  rightIndex :
    RetainedOrbitIndex n leftWeight rightWeight
  support :
    IsSupported (n := n) hleftWeight hrightWeight {
      left := retainedOrbitKey leftIndex
      right := retainedOrbitKey rightIndex
    }

namespace IOBranch

/-- The recipe-free obstruction represented by one pair of source indices. -/
def obstruction
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    POObstru where
  left :=
    retainedOrbitKey branch.leftIndex
  right :=
    retainedOrbitKey branch.rightIndex

/--
Seed one conservative recursive orbit-expansion branch from the raw-source
per-index multiplicity packets at its two parent indices.
-/
noncomputable def profiledObstructionBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    POBranch
      n leftWeight rightWeight hleftWeight hrightWeight where
  obstruction :=
    branch.obstruction
  support :=
    branch.support
  left :=
    raw.multiplicityProfileFamily branch.leftIndex
  right :=
    raw.multiplicityProfileFamily branch.rightIndex

/-- Concrete recursively expanded correction trace of one raw-source branch. -/
def indexTrace
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  (branch.profiledObstructionBranch raw).indexTrace M N

end IOBranch

/--
A finite source-index branch list whose conservative recursive expansion is
the actual selected retained-correction scheduler trace up to permutation.

The remaining collector theorem is concentrated in `trace_perm`.
-/
structure
    SEDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RMProf
      n leftWeight rightWeight hleftWeight hrightWeight
  branches :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight)
  trace_perm :
    ∀ M N,
      List.Perm
        ((branches.map fun branch => branch.indexTrace raw M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  SEDecomp

/--
Forget the source-index packaging and retain the generic recursive
polynomial-orbit expansion decomposition.
-/
noncomputable def
    selectedProfiledExpansion
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SEDecomp
        layer hleftWeight hrightWeight) :
    SPExp
      layer hleftWeight hrightWeight where
  branches :=
    decomposition.branches.map fun branch =>
      branch.profiledObstructionBranch decomposition.raw
  trace_perm M N := by
    simpa only [List.map_map, Function.comp_apply] using
      decomposition.trace_perm M N

/-- Compile a raw-source-seeded expansion to per-index correction profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SEDecomp
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  decomposition.selectedProfiledExpansion
    |>.multiplicityProfileKernel

/--
Compile a raw-source-seeded expansion to the aggregate selected endpoint
shape-fiber profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SEDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.selectedProfiledExpansion
    |>.selectedFullFiber
      decomposition.raw.idxFiberProfile

end
  SEDecomp

end
  ESIdx

namespace RSTransv

/--
Stable public name for the scalar raw-source polynomial-orbit stabilization
kernel.  This is the remaining fixed-transversal count statement: the
canonical homogeneous source profile agrees with every natural raw-source
shape fiber.
-/
abbrev StabilizationKernel
    (n leftWeight rightWeight : ℕ) : Prop :=
  Towers.TCTex.RFTransv.PTStab
    n leftWeight rightWeight

/--
Stable public name for the equivalent finite-index trace count form of the
raw-source stabilization theorem.
-/
abbrev IndexFiberCounts
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) : Prop :=
  Towers.TCTex.TFIdx.SatisfiesTransversalCounts
      n leftWeight rightWeight hleftWeight hrightWeight

/--
The scalar stabilization kernel is equivalent to exact finite-index
source-trace fiber counts.
-/
theorem stabilization_index_counts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    StabilizationKernel n leftWeight rightWeight ↔
      IndexFiberCounts
        n leftWeight rightWeight hleftWeight hrightWeight :=
  Towers.TCTex.TFIdx.transversal_stabilization_counts
      hleftWeight hrightWeight

/--
Finite-index trace counts produce the raw shape-fiber profile kernel consumed
by the selected endpoint and retained-correction profile compilers.
-/
def raw_fiber_counts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hcounts :
      IndexFiberCounts
        n leftWeight rightWeight hleftWeight hrightWeight) :
    Towers.TCTex.FIProf.RFProf
      n leftWeight rightWeight hleftWeight hrightWeight :=
  Towers.TCTex.TFIdx.PTStab.idxFiberProfile
    ((stabilization_index_counts
        hleftWeight hrightWeight).mpr hcounts)
    hleftWeight hrightWeight

/--
The stabilization kernel itself produces the same raw shape-fiber profile
kernel.
-/
def rawFiberProfile
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (kernel : StabilizationKernel n leftWeight rightWeight) :
    Towers.TCTex.FIProf.RFProf
      n leftWeight rightWeight hleftWeight hrightWeight :=
  Towers.TCTex.TFIdx.PTStab.idxFiberProfile
    kernel hleftWeight hrightWeight

end RSTransv

end TCTex
end Towers
