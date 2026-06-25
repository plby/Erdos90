import Submission.Group.OpenRelators.CanonicalQuotients


noncomputable section

namespace Submission
namespace OCQuotie

open PRFact
open PRQuotie

universe u v w

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    {ι : Type w}
    {relator : ι → F}

/--
The subgroup invisible to every quotient in one family of actual surjective
finite relator-killing `p`-group quotients.
-/
def relatorFamilyKernel
    {κ : Type v}
    (Q : κ → RQShadow p F relator) :
    Subgroup F :=
  sInf (Set.range fun k : κ => (Q k).map.ker)

omit [IsTopologicalGroup F] in
/--
The full finite relator residual kernel lies in the kernel of every member of
any actual finite relator quotient family.
-/
lemma relator_kernel_family
    {κ : Type v}
    (Q : κ → RQShadow p F relator) :
    relatorKernel p relator ≤ relatorFamilyKernel Q := by
  apply le_sInf
  rintro K ⟨k, rfl⟩
  exact relator_kernel (Q k).toRShadow

omit [IsTopologicalGroup F] in
/--
If one actual finite relator quotient family is kernel-cofinal, then its family
kernel lies in the full finite relator residual kernel.
-/
lemma relator_family_cofinal
    {κ : Type v}
    (Q : κ → RQShadow p F relator)
    (hQ : CofinalRelatorFamily Q) :
    relatorFamilyKernel Q ≤ relatorKernel p relator := by
  apply le_sInf
  rintro K ⟨S, rfl⟩
  let T : RQShadow p F relator :=
    RQShadow.relatorShadowRange S
  rcases hQ T with ⟨k, hk⟩
  have hfamily : relatorFamilyKernel Q ≤ (Q k).map.ker :=
    sInf_le ⟨k, rfl⟩
  exact hfamily.trans (by simpa [T] using hk)

omit [IsTopologicalGroup F] in
/--
Kernel-cofinal actual finite relator quotient families detect exactly the full
finite relator residual kernel.
-/
lemma relator_kernel_cofinal
    {κ : Type v}
    (Q : κ → RQShadow p F relator)
    (hQ : CofinalRelatorFamily Q) :
    relatorFamilyKernel Q = relatorKernel p relator := by
  apply le_antisymm
  · exact relator_family_cofinal Q hQ
  · exact relator_kernel_family Q

end OCQuotie
end Submission
