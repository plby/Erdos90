import Submission.Group.FinitePRelator.FiniteQuotients


noncomputable section

namespace Submission
namespace PRQuotie

open PCShadow

universe u v

variable
    {p : ℕ}
    {F : Type u}
    [Group F]
    [TopologicalSpace F]

/--
A family of actual surjective continuous finite `p`-group quotients is
kernel-cofinal when every actual finite `p`-group quotient lies above the
kernel of one family member.
-/
def CofinalShadowFamily
    {κ : Type v}
    (Q : κ → QShadow p F) :
    Prop :=
  ∀ S : QShadow p F,
    ∃ k : κ, (Q k).map.ker ≤ S.map.ker

/--
The subgroup invisible to every quotient in one actual finite `p`-group
quotient family.
-/
def shadowFamilyKernel
    {κ : Type v}
    (Q : κ → QShadow p F) :
    Subgroup F :=
  sInf (Set.range fun k : κ => (Q k).map.ker)

/--
The full finite `p` residual kernel lies in the kernel of every member of any
actual finite `p` quotient family.
-/
lemma residual_shadow_family
    {κ : Type v}
    (Q : κ → QShadow p F) :
    residualKernel p F ≤ shadowFamilyKernel Q := by
  apply le_sInf
  rintro K ⟨k, rfl⟩
  exact residual_le_kernel (Q k).toShadow

/--
If one actual finite `p` quotient family is kernel-cofinal, then its family
kernel lies in the full finite `p` residual kernel.
-/
lemma shadow_residual_cofinal
    {κ : Type v}
    (Q : κ → QShadow p F)
    (hQ : CofinalShadowFamily Q) :
    shadowFamilyKernel Q ≤ residualKernel p F := by
  apply le_sInf
  rintro K ⟨S, rfl⟩
  let T : QShadow p F := QShadow.ofShadowRange S
  rcases hQ T with ⟨k, hk⟩
  have hfamily : shadowFamilyKernel Q ≤ (Q k).map.ker :=
    sInf_le ⟨k, rfl⟩
  exact hfamily.trans (by simpa [T] using hk)

/--
Kernel-cofinal actual finite `p` quotient families detect exactly the full
finite `p` residual kernel.
-/
lemma shadow_family_cofinal
    {κ : Type v}
    (Q : κ → QShadow p F)
    (hQ : CofinalShadowFamily Q) :
    shadowFamilyKernel Q = residualKernel p F := by
  apply le_antisymm
  · exact shadow_residual_cofinal Q hQ
  · exact residual_shadow_family Q

end PRQuotie
end Submission
