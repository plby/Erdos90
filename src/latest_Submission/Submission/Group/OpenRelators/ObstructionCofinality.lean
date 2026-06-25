import Submission.Group.OpenRelators.Obstructions
import Submission.Group.OpenRelators.Cofinality


open scoped Topology

noncomputable section

namespace Submission
namespace OOCofina

open PRFact
open PRQuotie
open ONFact
open ONCofina
open ONCompar
open ONObstr

universe u v w

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    {ι : Type w}
    {q : F →* G}
    {relator : ι → F}

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
Membership in the finite-layer relator image descends from a finer
open-normal quotient to every coarser quotient.
-/
lemma relator_image
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    {x : F}
    (hxM : openNormalLayer M x ∈ relatorImage relator M) :
    openNormalLayer N x ∈ relatorImage relator N := by
  rcases hxM with ⟨y, hyrel, hyx⟩
  exact ⟨y, hyrel, of_eq_le hMN hyx⟩

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
If an ambient element survives the relator quotient of a coarser finite layer,
then the same ambient element survives the relator quotient of every finer
finite layer.
-/
lemma not_open_normal
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    {x : F}
    (hxN : x ∉ (openNormalRelator relator N).ker) :
    x ∉ (openNormalRelator relator M).ker := by
  intro hxM
  apply hxN
  apply (open_normal_kernel relator N x).mpr
  exact relator_image hMN
    ((open_normal_kernel relator M x).mp hxM)

/--
For a pro-`p` source, survival of one ambient element in the packaged canonical
relator quotient of a coarser finite layer persists in every finer packaged
canonical relator quotient.
-/
lemma not_algebraic_open
    (hProP : ProP.ProPGroup p F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    {x : F}
    (hxN :
      x ∉ (algebraicOpenNormal hProP N (relator := relator)).map.ker) :
    x ∉ (algebraicOpenNormal hProP M (relator := relator)).map.ker := by
  intro hxM
  apply hxN
  apply (ONFact.algebraic_open_relator
    hProP N x).mpr
  exact relator_image hMN
    ((ONFact.algebraic_open_relator
      hProP M x).mp hxM)

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
If an ambient candidate-kernel element survives the relator quotient of a
coarser finite layer, then it also survives the relator quotient of every finer
finite layer.
-/
lemma element_obstruction
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (hN : KernelElementObstruction q relator N) :
    KernelElementObstruction q relator M := by
  rcases hN with ⟨x, hxker, hxnotN⟩
  refine ⟨x, hxker, ?_⟩
  intro hxM
  exact hxnotN (relator_image hMN hxM)

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
A candidate-kernel-image obstruction in a coarser finite layer persists in
every finer finite layer.
-/
lemma kernel_element_obstruction
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (hN : ImageElementObstruction q relator N) :
    ImageElementObstruction q relator M := by
  apply (image_element_obstruction q relator M).mpr
  apply element_obstruction hMN
  exact (image_element_obstruction q relator N).mp hN

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
Failure of algebraic candidate-kernel generation in a coarser finite layer
persists in every finer finite layer.
-/
lemma not_generated_algebraically
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (hN : ¬ GeneratedAlgebraicallyOpen q relator N) :
    ¬ GeneratedAlgebraicallyOpen q relator M := by
  intro hM
  exact hN (generated_algebraically_open hMN hM)

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
Every obstruction in an arbitrary open-normal finite layer refines to an
obstruction along any cofinal open-normal family.
-/
lemma obstruction_along_cofinal
    {κ : Type v}
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B)
    {N : OpenNormalSubgroup F}
    (hN : KernelElementObstruction q relator N) :
    ∃ k : κ, KernelElementObstruction q relator (B k) := by
  rcases hB N with ⟨k, hk⟩
  exact ⟨k, element_obstruction hk hN⟩

/--
For a pro-`p` source, failure of finite relator quotient factorization is
equivalent to an ambient candidate-kernel obstruction along any cofinal
open-normal family.
-/
lemma property_along_pro
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B) :
    ¬ QuotientFactorizationProperty p relator q ↔
      ∃ k : κ, KernelElementObstruction q relator (B k) := by
  rw [factorization_along_pro
    hProP q B hB]
  change (¬ ∀ k : κ,
    GeneratedAlgebraicallyOpen q relator (B k)) ↔ _
  simp only [not_forall]
  exact exists_congr fun k =>
    ONObstr.not_algebraically_obstruction
      q relator (B k)

/--
For a pro-`p` source, failure of finite relator quotient factorization is
equivalent to a candidate-kernel-image obstruction along any cofinal
open-normal family.
-/
lemma factorization_property_along
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B) :
    ¬ QuotientFactorizationProperty p relator q ↔
      ∃ k : κ, ImageElementObstruction q relator (B k) := by
  exact
    (property_along_pro
      hProP q relator B hB).trans
      (exists_congr fun k =>
        (image_element_obstruction q relator (B k)).symm)

end OOCofina
end Submission
