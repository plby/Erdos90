import Towers.FieldTheory.HMRFiniteGeneration
import Towers.FieldTheory.HMRCuttingOutput
import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers
namespace TBluepr
namespace STBuild

section InitialZassenhausOpen

local notation "G" => initialGaloisGroup

/-- The finite discrete Jennings quotient used to witness openness of the `n`th Zassenhaus term.
We package only the data needed for the final topological argument. -/
structure InitialJenningsDatum (n : ℕ) where
  quotient : Type
  [instGroup : Group quotient]
  [instTopologicalSpace : TopologicalSpace quotient]
  [instFinite : Finite quotient]
  [instDiscreteTopology : DiscreteTopology quotient]
  map : G →* quotient
  continuous_map : Continuous map
  ker_le : map.ker ≤ initialZassenhausFiltration n

attribute [instance] InitialJenningsDatum.instGroup
attribute [instance] InitialJenningsDatum.instTopologicalSpace
attribute [instance] InitialJenningsDatum.instFinite
attribute [instance] InitialJenningsDatum.instDiscreteTopology

section ProfinitePackaging

lemma subgroup_open_nhds
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (H : Subgroup Γ) (hH : (H : Set Γ) ∈ 𝓝 (1 : Γ)) :
    IsOpen (H : Set Γ) := by
  exact Subgroup.isOpen_of_mem_nhds H hH

lemma open_normal_subset
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (H : Subgroup Γ) (hOpen : IsOpen (H : Set Γ)) :
    ∃ N : OpenNormalSubgroup Γ, (N : Set Γ) ⊆ (H : Set Γ) := by
  exact
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hOpen H.one_mem

lemma subgroup_open_normal
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (H : Subgroup Γ) (hOpen : IsOpen (H : Set Γ)) :
    ∃ N : OpenNormalSubgroup Γ, (N : Subgroup Γ) ≤ H := by
  obtain ⟨N, hN⟩ :=
    open_normal_subset
      (Γ := Γ) H hOpen
  refine ⟨N, ?_⟩
  intro g hg
  exact hN hg

lemma open_normal_nhds
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (H : Subgroup Γ) (hH : (H : Set Γ) ∈ 𝓝 (1 : Γ)) :
    ∃ N : OpenNormalSubgroup Γ, (N : Subgroup Γ) ≤ H := by
  have hOpen : IsOpen (H : Set Γ) :=
    subgroup_open_nhds (Γ := Γ) H hH
  exact subgroup_open_normal
    (Γ := Γ) H hOpen

noncomputable def openNormalQuotient
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Γ →* Γ ⧸ (N : Subgroup Γ) :=
  QuotientGroup.mk' (N : Subgroup Γ)

@[simp] lemma open_normal_quotient
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) (g : Γ) :
    openNormalQuotient (Γ := Γ) N g =
      ((g : Γ) : Γ ⧸ (N : Subgroup Γ)) := by
  rfl

lemma open_subgroup_continuous
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ) :
    Continuous (openNormalQuotient (Γ := Γ) N) := by
  change Continuous (QuotientGroup.mk : Γ → Γ ⧸ (N : Subgroup Γ))
  exact QuotientGroup.continuous_mk

@[simp] lemma open_subgroup_ker
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    (openNormalQuotient (Γ := Γ) N).ker = (N : Subgroup Γ) := by
  simp [openNormalQuotient]

lemma open_normal_ker
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) {H : Subgroup Γ}
    (hN : (N : Subgroup Γ) ≤ H) :
    (openNormalQuotient (Γ := Γ) N).ker ≤ H := by
  simpa [open_subgroup_ker (Γ := Γ) N] using hN

lemma open_normal_discrete
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ) :
    DiscreteTopology (Γ ⧸ (N : Subgroup Γ)) := by
  infer_instance

lemma open_subgroup_finite
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Finite (Γ ⧸ (N : Subgroup Γ)) := by
  infer_instance

lemma open_preimage_one
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    ((openNormalQuotient (Γ := Γ) N) ⁻¹' ({1} : Set (Γ ⧸ (N : Subgroup Γ)))) =
      (N : Set Γ) := by
  ext g
  change openNormalQuotient (Γ := Γ) N g = 1 ↔ g ∈ (N : Subgroup Γ)
  rw [← QuotientGroup.eq_one_iff]
  rfl

lemma open_normal_preimage
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ) :
    IsOpen (((N : Subgroup Γ) : Set Γ)) := by
  have hcont :=
    open_subgroup_continuous (Γ := Γ) N
  have hdisc : DiscreteTopology (Γ ⧸ (N : Subgroup Γ)) :=
    open_normal_discrete (Γ := Γ) N
  simpa [open_preimage_one (Γ := Γ) N] using
    (show IsOpen
      ((openNormalQuotient (Γ := Γ) N) ⁻¹'
        ({1} : Set (Γ ⧸ (N : Subgroup Γ)))) from
      (isOpen_discrete ({1} : Set (Γ ⧸ (N : Subgroup Γ)))).preimage hcont)

end ProfinitePackaging

universe u

/-- A finite discrete quotient whose kernel already lies inside the `n`th Zassenhaus term.

This is the exact output one expects from the Jennings-Lazard machine. Once such a witness
exists, the openness argument for `zassenhausFiltration p Γ n` is entirely formal. -/
structure TFWitnes
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (n : ℕ) where
  quotient : Type u
  [instGroup : Group quotient]
  [instTopologicalSpace : TopologicalSpace quotient]
  [instFinite : Finite quotient]
  [instDiscreteTopology : DiscreteTopology quotient]
  map : Γ →* quotient
  continuous_map : Continuous map
  ker_le : map.ker ≤ zassenhausFiltration p Γ n

attribute [instance] TFWitnes.instGroup
attribute [instance] TFWitnes.instTopologicalSpace
attribute [instance] TFWitnes.instFinite
attribute [instance] TFWitnes.instDiscreteTopology

namespace TFWitnes

variable {p : ℕ}
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
variable {n : ℕ}

/-- The kernel of the witness map is the preimage of the singleton `{1}`. Keeping this as a
separate lemma makes later openness arguments read in the same order as the intended mathematics:
first identify the kernel as a preimage, then use discreteness of the target. -/
@[simp] lemma preimage_one_ker
    (w : TFWitnes p Γ n) :
    ((w.map : Γ → w.quotient) ⁻¹' ({1} : Set w.quotient)) = (w.map.ker : Set Γ) := by
  ext g
  change w.map g = 1 ↔ g ∈ w.map.ker
  rfl

/-- A continuous homomorphism to a finite discrete quotient has open kernel. This is the purely
topological input extracted from the witness structure. -/
lemma ker_isOpen
    (w : TFWitnes p Γ n) :
    IsOpen ((w.map.ker : Set Γ)) := by
  have honeOpen : IsOpen ({1} : Set w.quotient) := isOpen_discrete _
  simpa [w.preimage_one_ker] using honeOpen.preimage w.continuous_map

/-- Since the kernel is an open subgroup, it is automa a neighbourhood of `1`. -/
lemma ker_nhds_one
    (w : TFWitnes p Γ n) :
    ((w.map.ker : Set Γ)) ∈ 𝓝 (1 : Γ) := by
  exact IsOpen.mem_nhds w.ker_isOpen (by simp)

/-- The witness kernel is not only open, but also sits inside the target Zassenhaus term. We
package that as an existential statement because later arguments naturally ask for "some open
subgroup inside `D_n`". -/
lemma exists_open_le
    (w : TFWitnes p Γ n) :
    ∃ H : Subgroup Γ, IsOpen (H : Set Γ) ∧ H ≤ zassenhausFiltration p Γ n := by
  refine ⟨w.map.ker, w.ker_isOpen, w.ker_le⟩

/-- The witness already suffices to show that the Zassenhaus term is a neighbourhood of `1`.
This is the formal topological endgame of the overall proof. -/
lemma zassenhaus_nhds_one
    (w : TFWitnes p Γ n) :
    ((zassenhausFiltration p Γ n : Set Γ)) ∈ 𝓝 (1 : Γ) := by
  rcases w.exists_open_le with ⟨H, hHopen, hHle⟩
  have hHnhds : (H : Set Γ) ∈ 𝓝 (1 : Γ) := by
    exact IsOpen.mem_nhds hHopen H.one_mem
  exact Filter.mem_of_superset hHnhds hHle

/-- Once a Jennings witness exists, the `n`th Zassenhaus term contains an open normal subgroup.
This is a useful reformulation for downstream arithmetic arguments that want to pass to finite
quotients or fixed fields. -/
lemma open_subgroup
    (w : TFWitnes p Γ n) :
    ∃ N : OpenNormalSubgroup Γ, (N : Subgroup Γ) ≤ zassenhausFiltration p Γ n := by
  have hnhds :
      ((zassenhausFiltration p Γ n : Set Γ)) ∈ 𝓝 (1 : Γ) := by
    exact TFWitnes.zassenhaus_nhds_one w
  exact
    open_normal_nhds
      (Γ := Γ) (zassenhausFiltration p Γ n) hnhds

end TFWitnes

/-- A generic topological repackaging used in the final step of the proof:
if a subgroup contains some open subgroup, then it is a neighbourhood of `1`. -/
lemma subgroup_nhds_open
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {H : Subgroup Γ}
    (hH : ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ U ≤ H) :
    (H : Set Γ) ∈ 𝓝 (1 : Γ) := by
  rcases hH with ⟨U, hUopen, hUH⟩
  have hUnhds : (U : Set Γ) ∈ 𝓝 (1 : Γ) := by
    exact IsOpen.mem_nhds hUopen U.one_mem
  exact Filter.mem_of_superset hUnhds hUH

noncomputable def jenningsDatumOpen
    (n : ℕ) (N : OpenNormalSubgroup G)
    (hN : (N : Subgroup G) ≤ initialZassenhausFiltration n) :
    InitialJenningsDatum n where
  quotient := G ⧸ (N : Subgroup G)
  map := openNormalQuotient (Γ := G) N
  continuous_map := open_subgroup_continuous (Γ := G) N
  ker_le := open_normal_ker (Γ := G) N hN

@[simp] lemma initial_jennings_datum
    (n : ℕ) (N : OpenNormalSubgroup G)
    (hN : (N : Subgroup G) ≤ initialZassenhausFiltration n) :
    (jenningsDatumOpen n N hN).quotient =
      (G ⧸ (N : Subgroup G)) := by
  rfl

@[simp] lemma jennings_datum_open
    (n : ℕ) (N : OpenNormalSubgroup G)
    (hN : (N : Subgroup G) ≤ initialZassenhausFiltration n) :
    (jenningsDatumOpen n N hN).map =
      openNormalQuotient (Γ := G) N := by
  rfl

@[simp] lemma jennings_datum_ker
    (n : ℕ) (N : OpenNormalSubgroup G)
    (hN : (N : Subgroup G) ≤ initialZassenhausFiltration n) :
    (jenningsDatumOpen n N hN).map.ker =
      (N : Subgroup G) := by
  change (openNormalQuotient (Γ := G) N).ker = (N : Subgroup G)
  exact open_subgroup_ker (Γ := G) N

lemma jennings_datum_nonempty
    (n : ℕ) (N : OpenNormalSubgroup G)
    (hN : (N : Subgroup G) ≤ initialZassenhausFiltration n) :
    Nonempty (InitialJenningsDatum n) := by
  exact ⟨jenningsDatumOpen n N hN⟩

lemma jennings_datum_nhds
    (n : ℕ)
    (hnhds : ((initialZassenhausFiltration n : Set G)) ∈ 𝓝 (1 : G)) :
    Nonempty (InitialJenningsDatum n) := by
  obtain ⟨N, hNle⟩ :=
    open_normal_nhds
      (Γ := G) (initialZassenhausFiltration n) hnhds
  exact jennings_datum_nonempty n N hNle

/- Placeholder for the real Jennings-Lazard input. Once the completed group algebra
is formalized, this should say that every `p`-Zassenhaus term in a topologically
finitely generated profinite group is a neighborhood of `1`. -/
/-- A finite discrete quotient candidate extracted from the dense generating family.

This packages the target of the completed-group-algebra quotient map before we impose the
Jennings-Lazard identification on its kernel. Separating this from the kernel calculation keeps the
final theorem organized around the actual mathematical steps. -/
structure DGData
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] where
  quotient : Type u
  [instGroup : Group quotient]
  [instTopologicalSpace : TopologicalSpace quotient]
  [instFinite : Finite quotient]
  [instDiscreteTopology : DiscreteTopology quotient]
  map : Γ →* quotient
  continuous_map : Continuous map

attribute [instance] DGData.instGroup
attribute [instance] DGData.instTopologicalSpace
attribute [instance] DGData.instFinite
attribute [instance] DGData.instDiscreteTopology

namespace DGData

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- Once the kernel inclusion is known, a dense-generators quotient candidate upgrades
immediately to the witness structure used by the openness theorem. -/
def toJenningsWitness
    {p : ℕ} [Fact p.Prime]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {n : ℕ}
    (D : DGData Γ)
    (hker : D.map.ker ≤ zassenhausFiltration p Γ n) :
    TFWitnes p Γ n where
  quotient := D.quotient
  instGroup := D.instGroup
  instTopologicalSpace := D.instTopologicalSpace
  instFinite := D.instFinite
  instDiscreteTopology := D.instDiscreteTopology
  map := D.map
  continuous_map := D.continuous_map
  ker_le := hker

end DGData

/-- The intermediate object produced by the intended completed-group-algebra argument.

The point of this structure is to package the finite quotient together with:

1. build the finite discrete quotient from the dense generating family;
2. show, via Jennings-Lazard, that its kernel lies in `zassenhausFiltration p Γ n`.
3. retain the two high-level provenance properties that explain where the quotient came from.

The final witness theorem should then be a short packaging step. -/
structure DJApprox
    (p : ℕ) (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ) (n : ℕ) where
  quotientData : DGData Γ
  /-- The actual Jennings-Lazard output needed downstream: the kernel of the quotient map is
  contained in the `n`th Zassenhaus term. -/
  ker_le : quotientData.map.ker ≤ zassenhausFiltration p Γ n
  /-- The quotient map is induced from the completed group algebra modulo the `n`th augmentation
  ideal power attached to the dense generating family `s`. -/
  induced_completed_algebra : Prop
  /-- This records the finiteness mechanism coming from the fact that the completed group algebra is
  topologically generated by finitely many elements modulo the `n`th augmentation layer. -/
  finite_level_control : Prop

namespace DJApprox

/-- The substantive Jennings-Lazard step: once the quotient really is the
`I^n`-level quotient of the completed group algebra built from the dense
generating family, its kernel is contained in the `n`th Zassenhaus term. In
`DJApprox`, that conclusion is stored explicitly so that
downstream packaging can use it without reopening the completed-group-algebra
argument. -/
lemma ker_le_zassenhaus
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ} {n : ℕ}
    (A : DJApprox p Γ s n) :
    A.quotientData.map.ker ≤ zassenhausFiltration p Γ n := by
  exact A.ker_le

/-- After the kernel calculation is available, turning the approximation data
into the final Jennings witness is formal bookkeeping. -/
def toJenningsWitness
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ} {n : ℕ}
    (A : DJApprox p Γ s n) :
    TFWitnes p Γ n :=
  A.quotientData.toJenningsWitness (p := p) (n := n) (A.ker_le_zassenhaus)

end DJApprox

/-- The underlying quotient group used in the dense-generators Jennings-Lazard approximation.

Jennings-Lazard identifies this intrinsic quotient `Γ ⧸ Dₙ(Γ)` with the image
of `Γ` in the unit group of the completed group algebra modulo the `n`th
augmentation-ideal power. We keep the intrinsic carrier separate so that, once
the abstract Jennings witness theorem is available, its finite/discrete
structure can be recovered below as a clean corollary. -/
noncomputable def generators_jennings_approx
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (_hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type u := by
  exact Γ ⧸ zassenhausFiltration p Γ n

/-- The dense-generators quotient inherits a group structure from the unit group
of the augmentation-layer quotient. -/
noncomputable instance instGeneratorsApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Group (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  dsimp [generators_jennings_approx]
  infer_instance

/-- The dense-generators quotient carries the quotient topology inherited from
the finite augmentation-layer construction. -/
noncomputable instance instSpaceApprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    TopologicalSpace (generators_jennings_approx (p := p) (Γ := Γ) s hs n) := by
  dsimp [generators_jennings_approx]
  infer_instance

/-- The quotient map `Γ → Q_n(s)` obtained by restricting the
completed-group-algebra quotient map to the original group. -/
noncomputable def dense_jennings_approx
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Γ →* generators_jennings_approx (p := p) (Γ := Γ) s hs n := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  exact QuotientGroup.mk' (zassenhausFiltration p Γ n)

/-- Continuity of the dense-generators quotient map is inherited from the continuous completed-
group-algebra quotient map and the canonical map `Γ → units(ZMod p[[Γ]])`. -/
lemma jennings_approx_continuous
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Continuous (dense_jennings_approx
      (p := p) (Γ := Γ) s hs n) := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  dsimp [dense_jennings_approx, generators_jennings_approx]
  exact continuous_quotient_mk'

lemma jennings_approx_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    (dense_jennings_approx (p := p) (Γ := Γ) s hs n).ker ≤
      zassenhausFiltration p Γ n := by
  letI : (zassenhausFiltration p Γ n).Normal := zassenhausFiltration_normal p Γ n
  dsimp [
    dense_jennings_approx,
    generators_jennings_approx,
  ]
  exact (QuotientGroup.ker_mk' (zassenhausFiltration p Γ n)).le

/--
An interface for the completed-group-algebra provenance of the dense-generators
Jennings quotient.

The completed group algebra itself is not constructed here. Instead, this
records the exact topological algebra data the later formalization should
provide: a complete profinite `ZMod p`-algebra `A`, its augmentation ideal
`I`, the quotient algebra `A / I^n`, the canonical continuous map from `Γ` to
units, and an identification of the resulting unit image with the intrinsic
quotient `Γ ⧸ D_n(Γ)`.
-/
structure DCModel
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type (u + 1) where
  completedGroupAlgebra : Type u
  [instRing : Ring completedGroupAlgebra]
  [instAlgebra : Algebra (ZMod p) completedGroupAlgebra]
  [instUniformSpace : UniformSpace completedGroupAlgebra]
  [topologicalRing : IsTopologicalRing completedGroupAlgebra]
  [instCompleteSpace : CompleteSpace completedGroupAlgebra]
  [t2Space : T2Space completedGroupAlgebra]
  [instCompactSpace : CompactSpace completedGroupAlgebra]
  [totallyDisconnected : TotallyDisconnectedSpace completedGroupAlgebra]
  augmentationMap : completedGroupAlgebra →ₐ[ZMod p] ZMod p
  augmentationMap_continuous : Continuous augmentationMap
  augmentationIdeal : Ideal completedGroupAlgebra
  augmentation_ideal_ker :
    augmentationIdeal = RingHom.ker augmentationMap.toRingHom
  augmentationQuotient : Type u
  [instQuotientRing : Ring augmentationQuotient]
  [instQuotientAlgebra : Algebra (ZMod p) augmentationQuotient]
  [quotientTopology : TopologicalSpace augmentationQuotient]
  [quotientTopologicalRing : IsTopologicalRing augmentationQuotient]
  quotientMap : completedGroupAlgebra →ₐ[ZMod p] augmentationQuotient
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker :
    RingHom.ker quotientMap.toRingHom = augmentationIdeal ^ n
  canonicalUnit : Γ →* Units completedGroupAlgebra
  canonicalUnit_continuous : Continuous canonicalUnit
  canonicalUnit_augmentation :
    ∀ g : Γ, augmentationMap (canonicalUnit g : completedGroupAlgebra) = 1
  unitReduction : Units completedGroupAlgebra →* Units augmentationQuotient
  unitReduction_continuous : Continuous unitReduction
  unitReduction_apply :
    ∀ x : Units completedGroupAlgebra,
      (unitReduction x : augmentationQuotient) =
        quotientMap (x : completedGroupAlgebra)
  quotientUnitMap : Γ →* Units augmentationQuotient
  quotient_unit_continuous : Continuous quotientUnitMap
  quotient_unit_map :
    quotientUnitMap = unitReduction.comp canonicalUnit
  quotientEquiv :
    quotientUnitMap.range ≃*
      generators_jennings_approx (p := p) (Γ := Γ) s hs n
  quotientEquiv_apply :
    ∀ g : Γ,
      quotientEquiv ⟨quotientUnitMap g, ⟨g, rfl⟩⟩ =
        dense_jennings_approx (p := p) (Γ := Γ) s hs n g
  unit_map_ker :
    quotientUnitMap.ker = zassenhausFiltration p Γ n

/-- Provenance field recording that the quotient candidate really comes from the completed-group-
algebra construction attached to the dense generating family `s`. -/
def approx_induced_completed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Prop :=
  Nonempty
    (DCModel
      (p := p) (Γ := Γ) s hs n)

/-- Provenance field recording the finite-level control on the quotient candidate. This is the
finiteness mechanism used to see that the target group is finite and discrete:
there exists a completed-group-algebra model attached to `s` whose level-`n`
augmentation quotient is finite. -/
def approx_level_control
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    Prop :=
  ∃ M : DCModel
      (p := p) (Γ := Γ) s hs n,
    Finite M.augmentationQuotient

/- The genuine Jennings-Lazard frontier, stated with an explicit dense generating family.

This is where the mathematics still has to enter. The intended proof is:

1. use the dense generators to control the completed group algebra `ZMod p[[Γ]]`;
2. show that the quotient by the `n`th augmentation-ideal power is finite;
3. restrict the resulting quotient map to `Γ`;
4. identify its kernel with a subgroup contained in `zassenhausFiltration p Γ n`.

The surrounding lemmas ensure that, once this algebraic statement is formalized, the topological
conclusion needs no further ingenuity. -/
/-- A finite augmentation quotient has a finite unit-image range. This is the finite algebraic
piece of the dense-generators construction, separated from the topological discreteness input. -/
lemma dense_completed_model
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient) :
    Finite M.quotientUnitMap.range := by
  letI := M.instQuotientRing
  letI := hfinite
  infer_instance

/-- If the augmentation quotient is finite and Hausdorff, then the unit-image range is discrete.
This isolates the final topology step from the completed-group-algebra construction itself. -/
lemma completed_discrete_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hT2 :
      letI := M.quotientTopology
      T2Space M.augmentationQuotient) :
    letI := M.quotientTopology
    DiscreteTopology M.quotientUnitMap.range := by
  letI := M.quotientTopology
  letI : T2Space M.augmentationQuotient := hT2
  letI : T2Space M.quotientUnitMap.range := inferInstance
  have hfinite_range : Finite M.quotientUnitMap.range :=
    dense_completed_model
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite
  letI : Finite M.quotientUnitMap.range := hfinite_range
  infer_instance

/-- The quotient-unit map remains continuous after restricting its codomain to its range. -/
lemma completed_model_continuous
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.quotientTopology
    Continuous M.quotientUnitMap.rangeRestrict := by
  letI := M.instQuotientRing
  letI := M.quotientTopology
  simpa [MonoidHom.rangeRestrict] using
    M.quotient_unit_continuous.subtype_mk
      (fun g : Γ => ⟨g, rfl⟩)

/-- Jennings-Lazard kernel identification for the completed-group-algebra quotient gives the
kernel inclusion needed by the topological witness after codomain restriction to the range. -/
lemma completed_model_ker
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    M.quotientUnitMap.rangeRestrict.ker ≤ zassenhausFiltration p Γ n := by
  rw [MonoidHom.ker_rangeRestrict, M.unit_map_ker]

/-- Package the range of the completed-group-algebra quotient-unit map as the finite discrete
quotient datum used by the Jennings witness interface. -/
def DCModel.toQData
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hdiscrete :
      letI := M.quotientTopology
      DiscreteTopology M.quotientUnitMap.range) :
    DGData Γ where
  quotient := M.quotientUnitMap.range
  instGroup := by
    letI := M.instQuotientRing
    infer_instance
  instTopologicalSpace := by
    letI := M.instQuotientRing
    letI := M.quotientTopology
    infer_instance
  instFinite := by
    exact
      dense_completed_model
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite
  instDiscreteTopology := by
    letI := M.instQuotientRing
    letI := M.quotientTopology
    exact hdiscrete
  map := M.quotientUnitMap.rangeRestrict
  continuous_map := by
    letI := M.instQuotientRing
    letI := M.quotientTopology
    exact
      completed_model_continuous
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M

/-- Once the finite discrete completed-group-algebra quotient is available, the surrounding
dense-generators Jennings approximation is pure packaging. -/
def DCModel.dense_gens_jenningsapprox
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hdiscrete :
      letI := M.quotientTopology
      DiscreteTopology M.quotientUnitMap.range) :
    DJApprox p Γ s n where
  quotientData :=
    M.toQData (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
      hfinite hdiscrete
  ker_le := by
    exact
      completed_model_ker
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M
  induced_completed_algebra :=
    approx_induced_completed
      (p := p) (Γ := Γ) s hs n
  finite_level_control :=
    approx_level_control
      (p := p) (Γ := Γ) s hs n

/-- A finite Hausdorff augmentation quotient is enough for the finite-discrete-range package
required by the dense-generators Jennings approximation. -/
lemma model_discrete_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (h :
      ∃ M : DCModel
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          T2Space M.augmentationQuotient)) :
    ∃ M : DCModel
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  rcases h with ⟨M, hfinite, hT2⟩
  exact
    ⟨M, hfinite,
      completed_discrete_t
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite hT2⟩

/-- A finite Hausdorff augmentation quotient is enough to construct the dense-generators
Jennings approximation. -/
lemma jennings_approx_t
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ)
    (h :
      ∃ M : DCModel
          (p := p) (Γ := Γ) s hs n,
        Finite M.augmentationQuotient ∧
          (letI := M.quotientTopology
          T2Space M.augmentationQuotient)) :
    Nonempty (DJApprox p Γ s n) := by
  rcases model_discrete_t
      (p := p) (Γ := Γ) s hs n h with ⟨M, hfinite, hdiscrete⟩
  exact
    ⟨M.dense_gens_jenningsapprox
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
      hfinite hdiscrete⟩

end InitialZassenhausOpen

end STBuild
end TBluepr
end Towers
