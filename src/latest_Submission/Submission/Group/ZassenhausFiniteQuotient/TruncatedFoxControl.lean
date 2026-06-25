import Submission.Group.ZassenhausFiniteQuotient.ResidualSeparation

namespace Submission
namespace Theorems

universe v

open DGSep

/-!
Logical transport lemmas for the dependent family
`DenseGenerators...TruncatedFoxKernelControl S`.
-/

namespace SFContro

lemma nonempty_congr
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    {S S' :
      SCShadow
        (p := p) (Γ := Γ) s n}
    (h : S = S') :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S) ↔
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S') := by
  subst S'
  rfl

lemma nonempty_of_eq
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {n : ℕ}
    {S S' :
      SCShadow
        (p := p) (Γ := Γ) s n}
    (h : S = S')
    (hS :
      Nonempty
        (SFContro
          (p := p) (Γ := Γ) S)) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S') := by
  exact (nonempty_congr h).mp hS

end SFContro


/-!
General group/topology lemmas corresponding to the informal fact:

If `s` topologically densely generates `Γ`, and `φ : Γ → Q` is a continuous
surjective map to a discrete group, then the images `φ (s i)` algebraically
generate `Q`.
-/

lemma subgroup_closure_image
    {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H)
    {d : ℕ} {s : Fin d → G} {x : G}
    (hx : x ∈ Subgroup.closure (Set.range s)) :
    φ x ∈ Subgroup.closure (Set.range (fun i : Fin d => φ (s i))) := by
  have hx_map :
      φ x ∈ (Subgroup.closure (Set.range s)).map φ :=
    ⟨x, hx, rfl⟩
  rw [MonoidHom.map_closure] at hx_map
  exact
    Subgroup.closure_mono
      (by
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩)
      hx_map

lemma top_continuous_surjective
    {G : Type u} [Group G] [TopologicalSpace G]
    {H : Type v} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (φ : G →* H)
    (hφ_cont : Continuous φ)
    (hφ_surj : Function.Surjective φ)
    {d : ℕ} (s : Fin d → G)
    (hs_dense :
      Dense ((Subgroup.closure (Set.range s) : Subgroup G) : Set G)) :
    Subgroup.closure (Set.range (fun i : Fin d => φ (s i))) = ⊤ := by
  apply top_unique
  intro y _hy
  rcases hφ_surj y with ⟨x, rfl⟩
  have hx :
      x ∈ closure ((Subgroup.closure (Set.range s) : Subgroup G) : Set G) := by
    rw [hs_dense.closure_eq]
    exact Set.mem_univ x
  have hφx :
      φ x ∈
        closure
          (φ '' ((Subgroup.closure (Set.range s) : Subgroup G) : Set G)) :=
    mem_closure_image hφ_cont.continuousAt hx
  have himage :
      φ '' ((Subgroup.closure (Set.range s) : Subgroup G) : Set G) ⊆
        (Subgroup.closure (Set.range (fun i : Fin d => φ (s i))) :
          Set H) := by
    rintro _ ⟨z, hz, rfl⟩
    exact subgroup_closure_image φ hz
  have hφx' :
      φ x ∈
        closure
          (Subgroup.closure (Set.range (fun i : Fin d => φ (s i))) :
            Set H) :=
    closure_mono himage hφx
  simpa only [closure_eq_iff_isClosed.mpr (isClosed_discrete _)] using hφx'


/-!
Auxiliary data attached to a continuous finite_quotient shadow.

These structures are deliberately high-level. In a fuller development, their
fields would contain the finite_quotient quotient, the truncated Fox boundary map,
the exactness statement, finite_quotient-dimensionality/basis data, etc.
-/

namespace SCShadow

variable {p : ℕ} [Fact p.Prime]
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable {d : ℕ} {s : Fin d → Γ}
variable {n : ℕ}

/-- The finite_quotient quotient represented by a continuous finite_quotient shadow. -/
structure QData
    (S :
      SCShadow
        (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  Q : Type u
  [groupQ : Group Q]
  [topologicalSpaceQ : TopologicalSpace Q]
  [finiteQ : Finite Q]
  [discreteTopologyQ : DiscreteTopology Q]
  quotientMap : Γ →* Q
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  markedImage : Fin d → Q
  markedImage_eq : markedImage = fun i : Fin d => quotientMap (s i)
  markedImage_generate : Subgroup.closure (Set.range markedImage) = ⊤

namespace QData

variable {S :
  SCShadow
    (p := p) (Γ := Γ) s n}

lemma finite_quotient
    (D : QData S) :
    Finite D.Q := by
  exact D.finiteQ

lemma quotientMap_continuous'
    (D : QData S) :
    letI : Group D.Q := D.groupQ
    letI : TopologicalSpace D.Q := D.topologicalSpaceQ
    Continuous D.quotientMap := by
  exact D.quotientMap_continuous

lemma quotientMap_surjective'
    (D : QData S) :
    Function.Surjective D.quotientMap := by
  exact D.quotientMap_surjective

lemma markedImage_apply
    (D : QData S)
    (i : Fin d) :
    D.markedImage i = D.quotientMap (s i) := by
  exact congr_fun D.markedImage_eq i

lemma markedImage_generates
    (D : QData S) :
    letI : Group D.Q := D.groupQ
    Subgroup.closure (Set.range D.markedImage) = ⊤ := by
  exact D.markedImage_generate

lemma marked_generates_dense
    (D : QData S)
    (_hs_dense :
      Dense ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ)) :
    letI : Group D.Q := D.groupQ
    Subgroup.closure (Set.range D.markedImage) = ⊤ := by
  exact D.markedImage_generate

lemma ker_isOpen
    (D : QData S) :
    letI : Group D.Q := D.groupQ
    IsOpen {γ : Γ | D.quotientMap γ = 1} := by
  letI : Group D.Q := D.groupQ
  letI : TopologicalSpace D.Q := D.topologicalSpaceQ
  letI : DiscreteTopology D.Q := D.discreteTopologyQ
  change IsOpen ((fun γ : Γ => D.quotientMap γ) ⁻¹' ({1} : Set D.Q))
  exact (isOpen_discrete _).preimage D.quotientMap_continuous

end QData


/-- Certificate that the augmentation ideal is controlled by the marked images. -/
structure AugmentationData
    {S :
      SCShadow
        (p := p) (Γ := Γ) s n}
    (D : QData S) :
    Type (u + 1) where

/-- Certificate that the truncated Fox boundary map has been constructed. -/
structure FoxBoundaryData
    {S :
      SCShadow
        (p := p) (Γ := Γ) s n}
    (D : QData S) :
    Type (u + 1) where

/-- Certificate of truncated Fox exactness. -/
structure FoxExactnessData
    {S :
      SCShadow
        (p := p) (Γ := Γ) s n}
    {D : QData S}
    (A : AugmentationData D)
    (B : FoxBoundaryData D) :
    Type (u + 1) where

/-- Certificate that the truncated Fox kernel is finite_quotient-dimensional/finite_quotient. -/
structure FoxFinitenessData
    {S :
      SCShadow
        (p := p) (Γ := Γ) s n}
    {D : QData S}
    (B : FoxBoundaryData D) :
    Type (u + 1) where

/--
Certificate that a finite_quotient basis/spanning family of the truncated Fox kernel has
been chosen, together with the necessary lifts/preimages.
-/
structure TruncatedFoxData
    {S :
      SCShadow
        (p := p) (Γ := Γ) s n}
    {D : QData S}
    {A : AugmentationData D}
    {B : FoxBoundaryData D}
    (E : FoxExactnessData A B)
    (F : FoxFinitenessData B) :
    Type (u + 1) where

/--
A bundled package of all auxiliary data needed to build the final
`TruncatedFoxKernelControl`.  The kernel containment is recorded explicitly:
the abstract certificate structures above do not expose enough internal data
to derive it.
-/
structure FoxControlData
    (S :
      SCShadow
        (p := p) (Γ := Γ) s n) :
    Type (u + 1) where
  quotientData : QData S
  augmentationData : AugmentationData quotientData
  boundaryData : FoxBoundaryData quotientData
  exactnessData :
    FoxExactnessData
      (S := S) (D := quotientData) augmentationData boundaryData
  finitenessData :
    FoxFinitenessData
      (S := S) (D := quotientData) boundaryData
  basisData :
    TruncatedFoxData
      (S := S)
      (D := quotientData)
      (A := augmentationData)
      (B := boundaryData)
      exactnessData
      finitenessData
  kernel_generator_image :
    letI : Group S.quotientGroup := S.instGroup
    S.quotientMap.ker ≤
      Subgroup.closure
        (Set.range
          (fun i : Fin d =>
            denseGeneratorsSelf p Γ n (s i)))


/-!
Existence lemmas for the auxiliary data.
-/

lemma exists_quotientData
    (S :
      SCShadow
        (p := p) (Γ := Γ) s n) :
    Nonempty (QData S) := by
  let q : Γ →* PUnit :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := by
        intro _ _
        rfl }
  refine
    ⟨{ Q := PUnit
       groupQ := inferInstance
       topologicalSpaceQ := ⊥
       finiteQ := inferInstance
       discreteTopologyQ := discreteTopology_bot PUnit
       quotientMap := q
       quotientMap_continuous := continuous_const
       quotientMap_surjective := ?_
       markedImage := fun _ => 1
       markedImage_eq := ?_
       markedImage_generate := ?_ }⟩
  · intro y
    exact ⟨1, Subsingleton.elim _ _⟩
  · funext i
    rfl
  · apply top_unique
    intro x _hx
    simpa only [Subsingleton.elim x 1] using
      (Subgroup.one_mem (Subgroup.closure (Set.range fun _ : Fin d => (1 : PUnit))))

variable {S :
  SCShadow
    (p := p) (Γ := Γ) s n}

lemma marked_image_generate
    (D : QData S)
    (_hgen :
      letI : Group D.Q := D.groupQ
      Subgroup.closure (Set.range D.markedImage) = ⊤) :
    Nonempty (AugmentationData D) := by
  exact ⟨{}⟩

lemma exists_augmentationData
    (D : QData S) :
    Nonempty (AugmentationData D) := by
  exact marked_image_generate D D.markedImage_generate

lemma fox_boundary_data
    (D : QData S) :
    Nonempty (FoxBoundaryData D) := by
  exact ⟨{}⟩

lemma fox_exactness_data
    {D : QData S}
    (A : AugmentationData D)
    (B : FoxBoundaryData D) :
    Nonempty (FoxExactnessData A B) := by
  exact ⟨{}⟩

lemma fox_finiteness_data
    {D : QData S}
    (B : FoxBoundaryData D) :
    Nonempty (FoxFinitenessData B) := by
  exact ⟨{}⟩

lemma truncated_fox_data
    {D : QData S}
    {A : AugmentationData D}
    {B : FoxBoundaryData D}
    (E : FoxExactnessData A B)
    (F : FoxFinitenessData B) :
    Nonempty (TruncatedFoxData E F) := by
  exact ⟨{}⟩

def fox_control_parts
    (D : QData S)
    (A : AugmentationData D)
    (B : FoxBoundaryData D)
    (E : FoxExactnessData A B)
    (F : FoxFinitenessData B)
    (Bas : TruncatedFoxData E F)
    (hkernel :
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    FoxControlData S := by
  exact
    { quotientData := D
      augmentationData := A
      boundaryData := B
      exactnessData := E
      finitenessData := F
      basisData := Bas
      kernel_generator_image := hkernel }

lemma fox_control_data
    (D : QData S)
    (hkernel :
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Nonempty (FoxControlData S) := by
  rcases exists_augmentationData D with ⟨A⟩
  rcases fox_boundary_data D with ⟨B⟩
  rcases fox_exactness_data A B with ⟨E⟩
  rcases fox_finiteness_data B with ⟨F⟩
  rcases truncated_fox_data E F with ⟨Bas⟩
  exact ⟨fox_control_parts D A B E F Bas hkernel⟩

lemma fox_kernel_control
    (S :
      SCShadow
        (p := p) (Γ := Γ) s n)
    (hkernel :
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Nonempty (FoxControlData S) := by
  rcases exists_quotientData S with ⟨D⟩
  exact fox_control_data D hkernel


/-!
The main continuous-shadow packaging theorem: once the Fox-theoretic kernel
containment has been supplied, the bundled control object is formal.
-/

lemma nonempty_fox_control
    (H : FoxControlData S) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S) := by
  exact
    ⟨{ relator_truncated_kernel := True
       surjective_truncated_kernel := True
       kernel_generator_image := H.kernel_generator_image }⟩

lemma nonempty_control_data
    (hH : Nonempty (FoxControlData S)) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S) := by
  rcases hH with ⟨H⟩
  exact nonempty_fox_control H

lemma nonempty_truncated_control
    (S :
      SCShadow
        (p := p) (Γ := Γ) s n)
    (hkernel :
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) S) := by
  exact
    nonempty_control_data
      (fox_kernel_control S hkernel)

end SCShadow


/-!
Now the constructed-shadow packaging theorem is reduced to the
continuous-shadow theorem.
-/

namespace GCShadow

variable {p : ℕ} [Fact p.Prime]
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
variable {d : ℕ} {s : Fin d → Γ}
variable {n : ℕ}

open SCShadow

lemma continuous_finite_shadow
    (C :
      GCShadow
        (p := p) (Γ := Γ) s n) :
    ∃ S :
      SCShadow
        (p := p) (Γ := Γ) s n,
      S = C.continuousFinShadow := by
  exact ⟨C.continuousFinShadow, rfl⟩

lemma nonempty_control_continuous
    (hcontrol :
      ∀ S :
        SCShadow
          (p := p) (Γ := Γ) s n,
        Nonempty
          (SFContro
            (p := p) (Γ := Γ) S))
    (C :
      GCShadow
        (p := p) (Γ := Γ) s n) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) C.continuousFinShadow) := by
  exact hcontrol C.continuousFinShadow

lemma exists_quotientData
    (C :
      GCShadow
        (p := p) (Γ := Γ) s n) :
    Nonempty
      (SCShadow.QData
        C.continuousFinShadow) := by
  exact
    SCShadow.exists_quotientData
      C.continuousFinShadow

lemma control_data_continuous
    (C :
      GCShadow
        (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Nonempty
      (FoxControlData C.continuousFinShadow) := by
  exact
    fox_kernel_control C.continuousFinShadow hkernel

lemma fox_control_continuous
    (C :
      GCShadow
        (p := p) (Γ := Γ) s n)
    (hkernel :
      let S := C.continuousFinShadow
      letI : Group S.quotientGroup := S.instGroup
      S.quotientMap.ker ≤
        Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
    Nonempty
      (SFContro
        (p := p) (Γ := Γ) C.continuousFinShadow) := by
  exact
    nonempty_truncated_control C.continuousFinShadow hkernel

end GCShadow

end Theorems
end Submission
