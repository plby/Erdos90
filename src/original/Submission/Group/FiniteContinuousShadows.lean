import Mathlib


open scoped Topology

noncomputable section

namespace Submission
namespace PCShadow

universe u

/--
A continuous homomorphism from a topological group to a finite discrete
`p`-group.  These are the finite `p`-group shadows through which a pro-`p`
factorization statement is tested.
-/
structure Shadow
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F] where
  Target : Type u
  [targetGroup : Group Target]
  [targetTopologicalSpace : TopologicalSpace Target]
  [targetDiscreteTopology : DiscreteTopology Target]
  [targetFinite : Finite Target]
  map : F →* Target
  map_continuous : Continuous map
  target_p_group : IsPGroup p Target

attribute [instance] Shadow.targetGroup
attribute [instance] Shadow.targetTopologicalSpace
attribute [instance] Shadow.targetDiscreteTopology
attribute [instance] Shadow.targetFinite

namespace Shadow

variable
    {p : ℕ}
    {F H : Type u}
    [Group F]
    [TopologicalSpace F]
    [Group H]
    [TopologicalSpace H]

/-- The kernel of a continuous finite discrete shadow is closed. -/
lemma kernel_isClosed
    (S : Shadow p F) :
    IsClosed ((S.map.ker : Subgroup F) : Set F) := by
  change IsClosed ((fun x : F => S.map x) ⁻¹' ({1} : Set S.Target))
  exact isClosed_singleton.preimage S.map_continuous

/-- The kernel of a continuous finite discrete shadow is open. -/
lemma kernel_isOpen
    (S : Shadow p F) :
    IsOpen ((S.map.ker : Subgroup F) : Set F) := by
  have hone : IsOpen ({1} : Set S.Target) := isOpen_discrete _
  change IsOpen ((fun x : F => S.map x) ⁻¹' ({1} : Set S.Target))
  exact hone.preimage S.map_continuous

/--
Pull a finite `p`-shadow back along a continuous homomorphism.  This is the
operation used when a finite shadow of a quotient is viewed as a finite shadow
of the original group.
-/
def pullback
    (S : Shadow p H)
    (φ : F →* H)
    (hφ : Continuous φ) :
    Shadow p F where
  Target := S.Target
  map := S.map.comp φ
  map_continuous := S.map_continuous.comp hφ
  target_p_group := S.target_p_group

@[simp] lemma pullback_map
    (S : Shadow p H)
    (φ : F →* H)
    (hφ : Continuous φ) :
    (S.pullback φ hφ).map = S.map.comp φ := rfl

lemma pullback_kernel
    (S : Shadow p H)
    (φ : F →* H)
    (hφ : Continuous φ)
    (x : F) :
    x ∈ (S.pullback φ hφ).map.ker ↔ φ x ∈ S.map.ker := by
  change S.map (φ x) = 1 ↔ S.map (φ x) = 1
  rfl

lemma pullback_kernel_comap
    (S : Shadow p H)
    (φ : F →* H)
    (hφ : Continuous φ) :
    (S.pullback φ hφ).map.ker = S.map.ker.comap φ := by
  ext x
  exact S.pullback_kernel φ hφ x

/--
The product of two finite `p`-shadows is again a finite `p`-shadow.  Its kernel
is the simultaneous kernel of the two tests, so finite families of quotient
conditions can be combined without leaving finite `p`-groups.
-/
def prod
    [Fact p.Prime]
    (S T : Shadow p F) :
    Shadow p F where
  Target := S.Target × T.Target
  map := S.map.prod T.map
  map_continuous := S.map_continuous.prodMk T.map_continuous
  target_p_group := by
    classical
    rcases (IsPGroup.iff_card.mp S.target_p_group) with ⟨m, hm⟩
    rcases (IsPGroup.iff_card.mp T.target_p_group) with ⟨n, hn⟩
    apply IsPGroup.iff_card.mpr
    refine ⟨m + n, ?_⟩
    simp [Nat.card_prod, hm, hn, pow_add]

@[simp] lemma prod_map
    [Fact p.Prime]
    (S T : Shadow p F) :
    (S.prod T).map = S.map.prod T.map := rfl

@[simp] lemma prod_kernel
    [Fact p.Prime]
    (S T : Shadow p F) :
    (S.prod T).map.ker = S.map.ker ⊓ T.map.ker := by
  exact MonoidHom.ker_prod S.map T.map

lemma prod_kernel_iff
    [Fact p.Prime]
    (S T : Shadow p F)
    (x : F) :
    x ∈ (S.prod T).map.ker ↔ x ∈ S.map.ker ∧ x ∈ T.map.ker := by
  rw [prod_kernel, Subgroup.mem_inf]

lemma not_prod_kernel
    [Fact p.Prime]
    (S T : Shadow p F)
    (x : F) :
    x ∉ (S.prod T).map.ker ↔ x ∉ S.map.ker ∨ x ∉ T.map.ker := by
  rw [S.prod_kernel_iff T x]
  tauto

end Shadow

/--
The intersection of the kernels of all continuous finite `p`-group shadows.
It is the subgroup invisible to every finite discrete `p`-group quotient.
-/
def residualKernel
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F] :
    Subgroup F :=
  sInf (Set.range fun S : Shadow p F => S.map.ker)

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]

lemma residual_le_kernel
    (S : Shadow p F) :
    residualKernel p F ≤ S.map.ker := by
  exact sInf_le ⟨S, rfl⟩

lemma residual_kernel_iff
    (x : F) :
    x ∈ residualKernel p F ↔ ∀ S : Shadow p F, x ∈ S.map.ker := by
  constructor
  · intro hx S
    exact residual_le_kernel S hx
  · intro hx
    change x ∈ sInf (Set.range fun S : Shadow p F => S.map.ker)
    rw [Subgroup.mem_sInf]
    rintro K ⟨S, rfl⟩
    exact hx S

/--
A topological group is residually finite `p` with respect to continuous finite
discrete `p`-group shadows when those shadows separate every nonidentity
element.
-/
def RFP
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F] :
    Prop :=
  residualKernel p F = ⊥

lemma residually_separates_nontrivial
    (p : ℕ)
    (F : Type u)
    [Group F]
    [TopologicalSpace F] :
    RFP p F ↔
      ∀ x : F, x ≠ 1 → ∃ S : Shadow p F, S.map x ≠ 1 := by
  constructor
  · intro hres x hx
    by_contra hsep
    push Not at hsep
    have hxResidual : x ∈ residualKernel p F := by
      rw [residual_kernel_iff]
      intro S
      exact MonoidHom.mem_ker.mpr (hsep S)
    rw [hres] at hxResidual
    exact hx (by simpa using hxResidual)
  · intro hsep
    apply le_antisymm
    · intro x hxResidual
      by_contra hx
      rcases hsep x hx with ⟨S, hS⟩
      exact hS (MonoidHom.mem_ker.mp (residual_le_kernel S hxResidual))
    · exact bot_le

instance residualKernel_normal :
    (residualKernel p F).Normal where
  conj_mem x hx g := by
    change x ∈ sInf (Set.range fun S : Shadow p F => S.map.ker) at hx
    change g * x * g⁻¹ ∈ sInf (Set.range fun S : Shadow p F => S.map.ker)
    rw [Subgroup.mem_sInf] at hx ⊢
    rintro K ⟨S, rfl⟩
    exact (show S.map.ker.Normal from inferInstance).conj_mem x (hx S.map.ker ⟨S, rfl⟩) g

end PCShadow
end Submission
