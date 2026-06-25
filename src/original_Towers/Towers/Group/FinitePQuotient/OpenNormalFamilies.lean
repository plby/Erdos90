import Towers.Group.FinitePQuotient.KernelCofinalFamilies
import Towers.Group.FiniteProfiniteResidual
import Towers.Group.OpenRelators.Cofinality


open scoped Topology

noncomputable section

namespace Towers
namespace PRQuotie

open PCShadow
open ONCofina

universe u v

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [TotallyDisconnectedSpace F]

/--
The open-normal subgroup cut out by one actual surjective continuous finite
`p`-group quotient.
-/
def QShadow.kernelOpenSubgroup
    (S : QShadow p F) :
    OpenNormalSubgroup F where
  toOpenSubgroup := ⟨S.map.ker, S.toShadow.kernel_isOpen⟩
  isNormal' := inferInstance

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
@[simp]
lemma QShadow.kernel_open_subgroup
    (S : QShadow p F) :
    (S.kernelOpenSubgroup : Subgroup F) = S.map.ker := rfl

/--
The actual finite `p` quotient attached to one open-normal quotient of a
pro-`p` profinite group.
-/
def openNormalShadow
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F) :
    QShadow p F where
  toShadow := PCShadow.openNormalShadow hProP N
  map_surjective := QuotientGroup.mk'_surjective (N : Subgroup F)

omit [TotallyDisconnectedSpace F] in
@[simp]
lemma open_shadow_kernel
    (hProP : ProP.ProPGroup p F)
    (N : OpenNormalSubgroup F) :
    (openNormalShadow hProP N).map.ker =
      (N : Subgroup F) := by
  exact PCShadow.open_shadow_kernel hProP N

omit [TotallyDisconnectedSpace F] in
/--
Kernel cofinality among actual finite `p` quotients forces cofinality of their
kernel open-normal subgroups among all open-normal subgroups.
-/
lemma cofinal_open_shadow
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (Q : κ → QShadow p F)
    (hQ : CofinalShadowFamily Q) :
    CofinalOpenFamily
      (fun k : κ => (Q k).kernelOpenSubgroup) := by
  intro N
  rcases hQ (openNormalShadow hProP N) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [QShadow.kernel_open_subgroup,
    open_shadow_kernel] using hk

omit [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/--
Cofinality of the kernel open-normal subgroups forces kernel cofinality among
actual finite `p` quotients.
-/
lemma cofinal_shadow_open
    {κ : Type v}
    (Q : κ → QShadow p F)
    (hQ :
      CofinalOpenFamily
        (fun k : κ => (Q k).kernelOpenSubgroup)) :
    CofinalShadowFamily Q := by
  intro S
  rcases hQ S.kernelOpenSubgroup with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa using hk

omit [TotallyDisconnectedSpace F] in
/--
For actual finite `p` quotient families of a pro-`p` profinite group, kernel
cofinality and open-normal kernel cofinality are equivalent.
-/
lemma cofinal_shadow_normal
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (Q : κ → QShadow p F) :
    CofinalShadowFamily Q ↔
      CofinalOpenFamily
        (fun k : κ => (Q k).kernelOpenSubgroup) := by
  constructor
  · exact cofinal_open_shadow
      hProP
      Q
  · exact cofinal_shadow_open Q

/--
Every open neighborhood of `1` contains the kernel of one quotient in a
kernel-cofinal actual finite `p` quotient family.
-/
lemma subset_nhds_cofinal
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (Q : κ → QShadow p F)
    (hQ : CofinalShadowFamily Q)
    {U : Set F}
    (hU : U ∈ 𝓝 (1 : F)) :
    ∃ k : κ, ((Q k).kernelOpenSubgroup : Set F) ⊆ U := by
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, h1V⟩
  rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen h1V with
    ⟨N, hN⟩
  rcases (cofinal_open_shadow
      hProP
      Q
      hQ) N with
    ⟨k, hk⟩
  exact ⟨k, fun x hx => hVU (hN (hk hx))⟩

/--
A kernel-cofinal actual finite `p` quotient family gives a neighborhood basis
of open-normal kernels at `1`.
-/
lemma basis_nhds_cofinal
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (Q : κ → QShadow p F)
    (hQ : CofinalShadowFamily Q) :
    (𝓝 (1 : F)).HasBasis
      (fun _k : κ => True)
      (fun k : κ => ((Q k).kernelOpenSubgroup : Set F)) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    rcases subset_nhds_cofinal
        hProP
        Q
        hQ
        hU with
      ⟨k, hk⟩
    exact ⟨k, trivial, hk⟩
  · rintro ⟨k, _hk, hkU⟩
    exact Filter.mem_of_superset (Q k).kernelOpenSubgroup.toOpenSubgroup.mem_nhds_one hkU

end PRQuotie
end Towers
