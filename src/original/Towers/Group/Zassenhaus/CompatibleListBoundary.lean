import Towers.Group.Zassenhaus.InverseUniversalOrbit
import Towers.Group.Zassenhaus.ErasedShapePrograms

/-!
# Shape-erased compatible-grid branch lists for selected corrections

The operational collector emits support-compatible correction grids rather
than full Cartesian parent grids.  A finite list of compatible-grid scheduler
batches already carries homogeneous finite-index profiles.  Endpoint
coordinates need only erased Hall-shape multiplicities, so the collector
comparison can be weakened further: erase the batch indices before comparing
the flattened batch trace with the selected correction trace.

This file packages that shape-level boundary, compiles it directly to the
endpoint interpolation object consumed by the power-coordinate pipeline, and
shows that every exact compatible-grid index decomposition induces the weaker
shape-level decomposition.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  EBList

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
  GBList
open
  GGErased
open
  SEAlg

/--
A finite list of operational compatible-grid batches whose erased flattened
trace is the literal selected retained-correction shape trace up to
permutation.

Unlike the guarded full-Cartesian orbit expansion boundary, this criterion
keeps the support-compatible grids emitted after overlap subtraction.
-/
structure PCDecompb
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  branches :
    List (PGBranch
      n leftWeight rightWeight)
  shape_trace_perm :
    ∀ M N,
      List.Perm
        (((branches.map fun branch => branch.indexTrace M N).flatten).map
          fun index => (retainedOrbitKey index).erasedShape)
        (selectedErasedShape layer M N)

namespace
  PCDecompb

/--
Compile compatible-grid batch profiles to literal selected-correction shape
profiles using only the erased-shape scheduler permutation.
-/
noncomputable def erasedMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompb
        layer hleftWeight hrightWeight) :
    EMProf
      (selectedErasedShape layer) :=
  (profiledErasedFamily
    (PGBranch.concat
      decomposition.branches)).kernel
        |>.permTransport (fun M N => by
          rw [profiled_erased_family,
            PGBranch.trace_concat]
          exact decomposition.shape_trace_perm M N)

/--
Compile compatible-grid batch profiles to selected-correction shape fibers.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompb
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.erasedMultiplicityProfile
    |>.shapeFiberProfile
      hleftWeight hrightWeight

/--
Together with raw-source profiles, compile compatible-grid shape batches to
the aggregate selected endpoint profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompb
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  EIFiber.idx_fiber_profile
    raw
    decomposition.shapeFiberProfile

/--
Compile compatible-grid shape batches directly to the endpoint interpolation
object consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompb
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :=
  decomposition.selectedFullFiber
    raw
      |>.fiberProfileInterpolation

/--
Every exact compatible-grid index decomposition induces the weaker
erased-shape decomposition by mapping its trace permutation through key
erasure.
-/
noncomputable def exactIndexDecomposition
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SPDecomp
        layer hleftWeight hrightWeight) :
    PCDecompb
      layer hleftWeight hrightWeight where
  branches :=
    decomposition.branches
  shape_trace_perm M N := by
    rw [←
      key_erased_selected
        layer M N hleftWeight hrightWeight]
    exact
      (decomposition.trace_perm M N).map
        (fun index => (retainedOrbitKey index).erasedShape)

end
  PCDecompb

/--
Through cutoff four, the compatible-grid shape decomposition is empty.
-/
noncomputable def
    selectedProfiledFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    PCDecompb
      layer (by simp) (by simp) where
  branches :=
    []
  shape_trace_perm M N := by
    rw [
      selected_nil_four
        layer hhigh M N]
    simp

/--
Through cutoff four, compatible-grid shape batches recover selected endpoint
profiles.
-/
noncomputable def
    idxGridBranches
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    EIFiber
      layer (by simp) (by simp) :=
  (selectedProfiledFour
    layer hhigh)
      |>.selectedFullFiber
        raw

/--
Through cutoff four, compatible-grid shape batches reach the interpolation
object consumed by the power-coordinate compiler.
-/
noncomputable def
    fiberInterpolationBranches
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  (selectedProfiledFour
    layer hhigh)
      |>.fiberProfileInterpolation raw

end
  EBList
end TCTex
end Towers
