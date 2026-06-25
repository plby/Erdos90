import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords
import Towers.Algebra.DenseGenerators.CanonicalAlgebra

open scoped Topology Pointwise BigOperators

noncomputable section

namespace Towers

universe u
universe v w z

/-- Forget the canonical-unit data on a carrier, retaining only the completed algebra object. -/
abbrev DCCarrie.toObject
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    DCObject (p := p) (Γ := Γ) s hs where
  completedGroupAlgebra := K.carrier
  instRing := K.instRing
  instAlgebra := K.instAlgebra
  instUniformSpace := K.instUniformSpace
  topologicalRing := K.topologicalRing.down
  instCompleteSpace := K.instCompleteSpace.down
  t2Space := K.t2Space.down
  instCompactSpace := K.instCompactSpace.down
  totallyDisconnected := K.totallyDisconnected.down

/-- Augmentation data compatible with the carrier-level canonical units. -/
def DCCarrie.CompatibleAugmentation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs) :
    Type (u + 1) :=
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  Σ Aug : DenseCompletedAugmentation K.toObject,
    PLift
      (∀ g : Γ,
        Aug.augmentationMap ((K.canonicalUnit g : K.carrier)) = 1)

/-- A trivial-character extension supplies the compatible augmentation package. -/
lemma DCCarrie.compat_augtrivial_characterext
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (H : K.TrivialCharacterExtension) :
    Nonempty K.CompatibleAugmentation := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  rcases H with ⟨Φ, hΦcont, hΦunit⟩
  let Aug : DenseCompletedAugmentation K.toObject := {
    augmentationMap := Φ
    augmentationMap_continuous := hΦcont
    augmentationIdeal := RingHom.ker Φ.toRingHom
    augmentation_ideal_ker := rfl
  }
  refine ⟨⟨Aug, ⟨?_⟩⟩⟩
  intro g
  simpa [Aug] using hΦunit g

/-- Package carrier-level data and a compatible augmentation as an ambient object. -/
abbrev DCCarrie.toAmbient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation) :
    GCAmbien (p := p) (Γ := Γ) s hs := by
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  let U : DenseCompletedUnits
      (p := p) (Γ := Γ) K.toObject AugC.1 := {
    canonicalUnit := K.canonicalUnit
    canonicalUnit_continuous := K.canonicalUnit_continuous.down
    canonicalUnit_augmentation := AugC.2.down
  }
  exact K.toObject.toAmbient AugC.1 U

/-- The carrier-level universal property becomes `CompletedAlgebra` after packaging. -/
lemma DCCarrie.ambient_complete_groupalg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation)
    (H : K.HasUniversalProperty) :
    (K.toAmbient AugC).CompletedAlgebra := by
  simpa [
    GCAmbien.CompletedAlgebra,
    DCCarrie.HasUniversalProperty,
    DCCarrie.toAmbient
  ] using H

/-- Carrier density transfers to the ambient object obtained by adding a compatible augmentation.

The `toAmbient` construction does not change the carrier or the canonical unit map; it only adds
augmentation data.  Thus the dense canonical-unit span predicate is definitionally the same on the
carrier and on the resulting ambient object. -/
lemma DCCarrie.ambient_denseunit_algspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation)
    (hdense : K.DenseAlgebraSpan) :
    (K.toAmbient AugC).DenseAlgebraSpan := by
  simpa [
    GCAmbien.DenseAlgebraSpan,
    DCCarrie.DenseAlgebraSpan,
    DCCarrie.toAmbient,
    GCAmbien.completedGroupAlgebra,
    GCAmbien.canonicalUnit,
    GCAmbien.canonicalUnits
  ] using hdense

/-- Ambient density transfers back to the carrier after adding a compatible augmentation.

This is the reverse of `ambient_denseunit_algspan`.  It lets the ambient density
theorem for a completed group algebra be used to recover carrier-level density after the
augmentation has been constructed from the carrier universal property. -/
lemma DCCarrie.dense_unitalg_spanambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation)
    (hdense : (K.toAmbient AugC).DenseAlgebraSpan) :
    K.DenseAlgebraSpan := by
  simpa [
    GCAmbien.DenseAlgebraSpan,
    DCCarrie.DenseAlgebraSpan,
    DCCarrie.toAmbient,
    GCAmbien.completedGroupAlgebra,
    GCAmbien.canonicalUnit,
    GCAmbien.canonicalUnits
  ] using hdense

/-- Adding a compatible augmentation does not change the explicit group-algebra lift.

The ambient package `K.toAmbient AugC` has the same underlying carrier and the same canonical
unit map as `K`; it only records an augmentation.  Therefore the algebra homomorphism obtained by
extending `g ↦ canonicalUnit g` from the abstract group algebra is definitionally the same map. -/
lemma DCCarrie.ambientcanon_groupalg_lifteq
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation) :
    letI := K.instRing
    letI := K.instAlgebra
    letI : DecidableEq Γ := Classical.decEq Γ
    (K.toAmbient AugC).canonicalAlgebraLift =
      K.canonicalAlgebraLift := by
  classical
  simp [
    GCAmbien.canonicalAlgebraLift,
    DCCarrie.canonicalAlgebraLift,
    DCCarrie.toAmbient,
  ]
  rfl

/-- Carrier dense explicit lift transfers to the ambient object after adding an augmentation.

This is a pure transport lemma.  Since `toAmbient` leaves the carrier topology and the explicit
lift unchanged, dense range of the carrier lift is exactly dense range of the ambient lift. -/
lemma DCCarrie.ambientdense_groupalg_liftrange
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation)
    (hdense : K.DenseLiftRange) :
    (K.toAmbient AugC).DenseLiftRange := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  have hmap :
      (K.toAmbient AugC).canonicalAlgebraLift =
        K.canonicalAlgebraLift :=
    K.ambientcanon_groupalg_lifteq AugC
  dsimp [
    GCAmbien.DenseLiftRange,
    DCCarrie.DenseLiftRange
  ] at hdense ⊢
  rw [hmap]
  exact hdense

/-- Ambient dense explicit lift transfers back to the carrier after adding an augmentation.

The completed ambient object obtained from a compatible augmentation is not a new topological
space; it is the same carrier with augmentation data attached.  Hence ambient completion-density
for the explicit group-algebra lift gives the carrier lift-density statement verbatim. -/
lemma DCCarrie.dense_groupalg_rangeambient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (K : DCCarrie
      (p := p) (Γ := Γ) s hs)
    (AugC : K.CompatibleAugmentation)
    (hdense : (K.toAmbient AugC).DenseLiftRange) :
    K.DenseLiftRange := by
  classical
  letI := K.instRing
  letI := K.instAlgebra
  letI := K.instUniformSpace
  have hmap :
      (K.toAmbient AugC).canonicalAlgebraLift =
        K.canonicalAlgebraLift :=
    K.ambientcanon_groupalg_lifteq AugC
  dsimp [
    GCAmbien.DenseLiftRange,
    DCCarrie.DenseLiftRange
  ] at hdense ⊢
  rw [← hmap]
  exact hdense
end Towers
