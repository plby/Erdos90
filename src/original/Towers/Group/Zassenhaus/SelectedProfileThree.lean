import
  Towers.Group.Zassenhaus.SelectedProfileAlgebra
import Towers.Group.Zassenhaus.CanonicalPacketAlignment

/-!
# Erased-shape selected-correction profiles through cutoff four

Through cutoff four at root weights, the cutoff-full scheduler retains no
generated correction occurrence.  This file instantiates the erased-shape
recursive profile algebra with its zero family and compiles the resulting
decomposition through the existing selected-endpoint interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  SEThree

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  FUClass
open
  SEAlg

/-- Through cutoff four, the literal selected correction-shape trace is empty. -/
lemma selected_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    selectedErasedShape layer M N = [] := by
  unfold selectedErasedShape
  rw [
    inventory_corrections_nil
      layer hhigh M N]
  rfl

/--
Through cutoff four, the zero profiled erased-shape family is the actual
selected scheduler-correction shape trace.
-/
noncomputable def
    selectedProfiledDecomposition
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SEProfil layer where
  family :=
    PEFam.zero
  trace_eq M N := by
    rw [PEFam.trace_zero]
    exact
      (selected_n_four
        layer hhigh M N).symm

/--
The shallow erased-shape decomposition compiles to selected-correction
shape-fiber profiles without an orbit-index trace permutation.
-/
noncomputable def
    fiberNErased
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SFProf
      layer (by simp) (by simp) :=
  (selectedProfiledDecomposition
    layer hhigh)
      |>.shapeFiberProfile
        (by simp) (by simp)

/--
Together with raw-source profiles, the shallow erased-shape decomposition
compiles to the aggregate selected-endpoint profile kernel.
-/
noncomputable def
    selectedFiberErased
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  (selectedProfiledDecomposition
    layer hhigh)
      |>.selectedFullFiber
        (by simp) (by simp) raw

end SEThree
end TCTex
end Towers
