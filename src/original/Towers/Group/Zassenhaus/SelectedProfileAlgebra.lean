import Towers.Group.Zassenhaus.InverseUniversalOrbit

/-!
# Erased-shape trace algebra for selected cutoff-full corrections

The selected retained-correction trace was encoded in a finite polynomial-orbit
alphabet in order to make its support finite.  Its chosen occurrence
representatives preserve erased Hall shape, but they need not preserve a
stronger orbit key selected by a recursive symbolic expansion.

The endpoint-coordinate compiler only needs erased-shape fiber counts.  This
file therefore erases orbit indices before recursive profile accounting.  It
proves that the erased selected trace is literally the ordered list of
scheduler-correction shapes, packages zero/append/replicate/of_trace_eq algebra
for homogeneous profiles of arbitrary erased-shape traces, and compiles a
recursive erased-shape decomposition back to the existing correction
shape-fiber kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  SEAlg

open
  CRLayer
open
  ISFiber
open
  CRInv
open
  FIProf
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  FIBridge
open
  MPAlg
open
  IMProf

/--
The ordered erased Hall shapes of the concrete scheduler corrections retained
below cutoff.
-/
def selectedErasedShape
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
  (M N : ℕ) :
    List (CWord HPAtom) :=
  (endpointCorrectionInventory layer M N).corrections.map
    (fun term => term.erasedShape)

/--
Erasing orbit indices from the selected correction trace recovers the literal
ordered scheduler-correction shape trace.
-/
lemma key_erased_selected
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (selectedIndexTrace
      layer M N hleftWeight hrightWeight).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      selectedErasedShape layer M N := by
  rw [show
    (fun index : RetainedOrbitIndex n leftWeight rightWeight =>
      (retainedOrbitKey index).erasedShape) =
        (fun key => key.erasedShape) ∘ retainedOrbitKey by
      rfl]
  rw [← List.map_map,
    key_selected_trace]
  unfold selectedErasedShape
  unfold selectedClosurePacket
  calc
    _ =
        (endpointCorrectionInventory layer M N).corrections.attach.map
          (fun term => term.1.erasedShape) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro term _hterm
      change
        (closureSelectedTerm
          layer hleftWeight hrightWeight term.1 term.2).erasedShape =
            term.1.erasedShape
      exact
        erased_selected_term
          layer hleftWeight hrightWeight term.1 term.2
    _ =
        (endpointCorrectionInventory layer M N).corrections.map
          (fun term => term.erasedShape) := by
      simpa only [List.map_map, Function.comp_apply] using
        congrArg
          (List.map fun term => term.erasedShape)
          (List.attach_map_subtype_val
            (endpointCorrectionInventory layer M N).corrections)

/-- Counting one value in a mapped list is filtering its source by the
pulled-back equality predicate. -/
lemma count_length_filter
    {α β : Type*}
    [DecidableEq β]
    (mapEntry : α → β)
    (value : β) :
    ∀ entries : List α,
      (entries.map mapEntry).count value =
        (entries.filter fun entry => decide (mapEntry entry = value)).length
  | [] =>
      rfl
  | entry :: entries => by
      by_cases hentry : mapEntry entry = value
      · simp [hentry, count_length_filter mapEntry value entries]
      · simp [hentry, count_length_filter mapEntry value entries]

/--
Shape counts in the literal correction-shape trace are exactly the filtered
fibers of the selected finite-index trace.
-/
lemma selected_filter_key
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    (selectedErasedShape layer M N).count word =
      ((selectedIndexTrace
        layer M N hleftWeight hrightWeight).filter fun index =>
          decide
            ((retainedOrbitKey index).erasedShape =
              word)).length := by
  rw [← key_erased_selected
    layer M N hleftWeight hrightWeight]
  exact
    count_length_filter
      (fun index => (retainedOrbitKey index).erasedShape)
      word
      (selectedIndexTrace
        layer M N hleftWeight hrightWeight)

/--
One homogeneous packet for the multiplicity of each erased Hall word in an
arbitrary two-parameter shape-trace family.
-/
structure EMProf
    (trace : ℕ → ℕ → List (CWord HPAtom)) where
  profiles :
    ∀ word : CWord HPAtom,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  profiles_nat_count :
    ∀ (M N : ℕ) word,
      (profiles word).value (M : ℤ) (N : ℤ) =
        ((trace M N).count word : ℤ)

namespace EMProf

/-- The empty shape trace has the all-zero profile vector. -/
noncomputable def zero :
    EMProf
      (fun _M _N => ([] : List (CWord HPAtom))) where
  profiles word :=
    FPkt.zero word.pairLeftDegree word.pairRightDegree
  profiles_nat_count M N word := by
    rw [FPkt.value_zero]
    rfl

/-- Add shape-profile vectors when shape traces concatenate pointwise. -/
noncomputable def append
    {leftTrace rightTrace :
      ℕ → ℕ → List (CWord HPAtom)}
    (left : EMProf leftTrace)
    (right : EMProf rightTrace) :
    EMProf
      (fun M N => leftTrace M N ++ rightTrace M N) where
  profiles word :=
    FPkt.add (left.profiles word) (right.profiles word)
  profiles_nat_count M N word := by
    rw [FPkt.value_add,
      left.profiles_nat_count,
      right.profiles_nat_count,
      List.count_append]
    exact_mod_cast rfl

/-- Repeat one erased Hall word according to a homogeneous multiplicity
packet. -/
noncomputable def replicate
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    EMProf
      (fun M N => List.replicate (multiplicity M N) selected) where
  profiles word :=
    if hword : word = selected then
      hword ▸ profile
    else
      FPkt.zero word.pairLeftDegree word.pairRightDegree
  profiles_nat_count M N word := by
    classical
    by_cases hword : word = selected
    · subst word
      rw [dif_pos rfl, hprofile, List.count_replicate_self]
    · rw [dif_neg hword, FPkt.value_zero, List.count_replicate]
      simp [Ne.symm hword]

/-- Transport shape profiles across pointwise equality of trace families. -/
noncomputable def of_trace_eq
    {trace nextTrace : ℕ → ℕ → List (CWord HPAtom)}
    (kernel : EMProf trace)
    (htrace : ∀ M N, trace M N = nextTrace M N) :
    EMProf nextTrace where
  profiles :=
    kernel.profiles
  profiles_nat_count M N word := by
    rw [← htrace M N]
    exact kernel.profiles_nat_count M N word

/--
Transport shape profiles across pointwise permutation of trace families.
Shape-fiber coordinates depend only on multiplicities, not trace order.
-/
noncomputable def permTransport
    {trace nextTrace : ℕ → ℕ → List (CWord HPAtom)}
    (kernel : EMProf trace)
    (htrace : ∀ M N, List.Perm (trace M N) (nextTrace M N)) :
    EMProf nextTrace where
  profiles :=
    kernel.profiles
  profiles_nat_count M N word := by
    rw [← (htrace M N).count_eq word]
    exact kernel.profiles_nat_count M N word

/--
Compile literal selected-correction shape profiles to the existing selected
correction shape-fiber interface.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      EMProf
        (selectedErasedShape layer))
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SFProf
      layer hleftWeight hrightWeight where
  profiles word _hword :=
    kernel.profiles word
  profiles_nat_trace M N word _hword := by
    rw [kernel.profiles_nat_count]
    exact congrArg (fun count : ℕ => (count : ℤ))
      (selected_filter_key
        layer M N hleftWeight hrightWeight word)

end EMProf

/-- A shape trace family bundled with homogeneous multiplicity profiles. -/
structure PEFam where
  trace : ℕ → ℕ → List (CWord HPAtom)
  kernel : EMProf trace

namespace PEFam

/-- Bundle the empty erased-shape trace. -/
noncomputable def zero :
    PEFam where
  trace := fun _M _N => []
  kernel :=
    EMProf.zero

/-- Bundle pointwise concatenation of profiled erased-shape traces. -/
noncomputable def append
    (left right : PEFam) :
    PEFam where
  trace := fun M N => left.trace M N ++ right.trace M N
  kernel :=
    left.kernel.append right.kernel

/-- Bundle one polynomially repeated erased Hall shape. -/
noncomputable def replicate
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    PEFam where
  trace := fun M N => List.replicate (multiplicity M N) selected
  kernel :=
    EMProf.replicate
      selected multiplicity profile hprofile

/-- Concatenate a finite list of profiled erased-shape traces in order. -/
noncomputable def concat :
    List PEFam →
      PEFam
  | [] =>
      zero
  | family :: families =>
      family.append (concat families)

/--
Bundle one scheduler-shaped branch: recursive left corrections, repeated new
correction shape, then recursive right corrections.
-/
noncomputable def retained
    (left right : PEFam)
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ)) :
    PEFam :=
  left.append ((replicate selected multiplicity profile hprofile).append right)

@[simp]
lemma trace_zero
    (M N : ℕ) :
    zero.trace M N = [] := by
  rfl

@[simp]
lemma trace_append
    (left right : PEFam)
    (M N : ℕ) :
    (left.append right).trace M N =
      left.trace M N ++ right.trace M N := by
  rfl

@[simp]
lemma trace_replicate
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
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
    (families : List PEFam)
    (M N : ℕ) :
    (concat families).trace M N =
      (families.map fun family => family.trace M N).flatten := by
  induction families with
  | nil =>
      rfl
  | cons family families ih =>
      rw [concat, trace_append, List.map_cons, List.flatten_cons, ih]

@[simp]
lemma trace_retained
    (left right : PEFam)
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
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

end PEFam

/--
Transport one finite-index trace packet to a requested erased Hall shape,
using zero for indices with another shape.
-/
noncomputable def profileShape
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  if hshape : (retainedOrbitKey index).erasedShape = word then
    hshape ▸ family.kernel.profiles index
  else
    FPkt.zero word.pairLeftDegree word.pairRightDegree

@[simp]
lemma value_profile_shape
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (M N : ℤ) :
    (profileShape family word index).value M N =
      if (retainedOrbitKey index).erasedShape = word then
        (family.kernel.profiles index).value M N
      else
        0 := by
  classical
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · subst word
    simp [profileShape]
  · simp [profileShape, hshape]

/-- Sum one profiled finite-index trace family over all indices with one
erased Hall shape. -/
noncomputable def erasedShapeProfile
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  FPkt.finsetSum Finset.univ (profileShape family word)

/-- The erased-shape profile sums exactly the filtered finite-index trace
fiber. -/
lemma
    cast_length_filter
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (erasedShapeProfile family word).value (M : ℤ) (N : ℤ) =
      (((family.trace M N).filter fun index =>
        decide
          ((retainedOrbitKey index).erasedShape =
            word)).length : ℤ) := by
  classical
  rw [erasedShapeProfile, FPkt.value_finsetSum]
  simp_rw [value_profile_shape,
    family.kernel.profiles_nat_count M N]
  exact_mod_cast
    ite_length_filter
      (family.trace M N)
      (fun index =>
        (retainedOrbitKey index).erasedShape = word)

/--
Erase finite orbit indices from a profiled trace family while summing packets
over equal erased Hall shapes.
-/
noncomputable def profiledErasedFamily
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight) :
    PEFam where
  trace :=
    fun M N =>
      (family.trace M N).map fun index =>
        (retainedOrbitKey index).erasedShape
  kernel := {
    profiles :=
      erasedShapeProfile family
    profiles_nat_count := by
      intro M N word
      rw [cast_length_filter]
      exact congrArg (fun count : ℕ => (count : ℤ))
        (count_length_filter
          (fun index => (retainedOrbitKey index).erasedShape)
          word (family.trace M N)).symm }

@[simp]
lemma profiled_erased_family
    {n leftWeight rightWeight : ℕ}
    (family : PIFam n leftWeight rightWeight)
    (M N : ℕ) :
    (profiledErasedFamily family).trace M N =
      (family.trace M N).map fun index =>
        (retainedOrbitKey index).erasedShape := by
  rfl

/--
A recursively profiled erased-shape family whose trace is exactly the literal
selected retained-correction shape trace.
-/
structure SEProfil
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight) where
  family : PEFam
  trace_eq :
    ∀ M N,
      family.trace M N =
        selectedErasedShape layer M N

namespace SEProfil

/-- Build a selected shape-trace decomposition from a finite list of profiled
branches. -/
noncomputable def ofConcat
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (families : List PEFam)
    (htrace :
      ∀ M N,
        (families.map fun family => family.trace M N).flatten =
          selectedErasedShape layer M N) :
    SEProfil layer where
  family :=
    PEFam.concat families
  trace_eq M N := by
    rw [PEFam.trace_concat]
    exact htrace M N

/--
Build a selected shape-trace decomposition from a finite list of profiled
branches whose flattened trace agrees with the operational trace up to
permutation.
-/
noncomputable def ofPermConcat
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (families : List PEFam)
    (htrace :
      ∀ M N,
        List.Perm
          ((families.map fun family => family.trace M N).flatten)
          (selectedErasedShape layer M N)) :
    EMProf
      (selectedErasedShape layer) :=
  (PEFam.concat families).kernel.permTransport
    (fun M N => by
      rw [PEFam.trace_concat]
      exact htrace M N)

/-- Build a selected shape-trace decomposition from one recurrence-shaped
left/middle/right presentation. -/
noncomputable def ofRetained
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (left right : PEFam)
    (selected : CWord HPAtom)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        selected.pairLeftDegree selected.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ))
    (htrace :
      ∀ M N,
        left.trace M N ++
              List.replicate (multiplicity M N) selected ++
                right.trace M N =
          selectedErasedShape layer M N) :
    SEProfil layer where
  family :=
    PEFam.retained
      left right selected multiplicity profile hprofile
  trace_eq M N := by
    rw [PEFam.trace_retained]
    exact htrace M N

/-- Forget recursive branch packaging and retain literal correction-shape
profiles. -/
noncomputable def erasedMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (decomposition :
      SEProfil layer) :
    EMProf
      (selectedErasedShape layer) :=
  decomposition.family.kernel.of_trace_eq decomposition.trace_eq

/--
Compile a recursively profiled literal shape trace to the existing selected
correction shape-fiber interface.  No equality or permutation of full orbit
indices is required.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (decomposition :
      SEProfil layer)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.erasedMultiplicityProfile
    |>.shapeFiberProfile
      hleftWeight hrightWeight

/--
Together with raw-source shape profiles, a recursively profiled literal
correction-shape trace compiles to the aggregate selected-endpoint profile
kernel consumed by fixed-slot interpolation.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (decomposition :
      SEProfil layer)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  EIFiber.idx_fiber_profile
    raw
    (decomposition.shapeFiberProfile
      hleftWeight hrightWeight)

end SEProfil

end SEAlg
end TCTex
end Towers
