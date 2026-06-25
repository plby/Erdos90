import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chapter VII, Section 8: functoriality in the reciprocity argument

Lemma 8.4 uses two elementary group-theoretic facts.  Triviality on a
distinguished subgroup is preserved by postcomposition, and it can be pulled
back across a compatible square when the homomorphism on targets is
injective.  The first is the subextension step; the second is the algebraic
content of the base-change step after the local Artin/norm compatibility has
been supplied.

Lemma 8.5 also uses that complex characters separate points of a finite
abelian group.  `Statements` packages the missing cup-product comparison
explicitly and proves both implications of Lemma 8.5 from that diagram.
-/

namespace Towers.CField.RExist

noncomputable section

/-- A homomorphism is trivial on a subgroup when that subgroup lies in its
kernel. -/
def IsTrivialOn {A G : Type*} [Group A] [Group G]
    (phi : A →* G) (P : Subgroup A) : Prop :=
  P ≤ phi.ker

/-- **Lemma VII.8.4(a), abstract form.** Postcomposition preserves
triviality on a subgroup. -/
theorem trivial_comp
    {A G H : Type*} [Group A] [Group G] [Group H]
    (phi : A →* G) (r : G →* H) (P : Subgroup A)
    (hphi : IsTrivialOn phi P) :
    IsTrivialOn (r.comp phi) P := by
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
  rw [hphi hx, map_one]

/-- **Lemma VII.8.4(b), abstract compatible-square form.** Suppose the norm
map sends the distinguished subgroup upstairs into the one downstairs, and
the two reciprocity maps commute with an injective map on targets.  Then
triviality downstairs implies triviality upstairs. -/
theorem trivial_compatible_injective
    {A A' G G' : Type*} [Group A] [Group A'] [Group G] [Group G']
    (norm : A' →* A) (phi : A →* G) (phi' : A' →* G') (i : G' →* G)
    (P : Subgroup A) (P' : Subgroup A')
    (hcomm : i.comp phi' = phi.comp norm)
    (hprincipal : ∀ x ∈ P', norm x ∈ P)
    (hi : Function.Injective i)
    (hphi : IsTrivialOn phi P) :
    IsTrivialOn phi' P' := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply hi
  rw [map_one]
  have hcommx := DFunLike.congr_fun hcomm x
  change i (phi' x) = phi (norm x) at hcommx
  rw [hcommx, hphi (hprincipal x hx)]

/-- **Lemma VII.8.5, character-separation input.** If every complex
character of a finite abelian group takes the value one at `a`, then `a` is
the identity. -/
theorem one_all_char
    {A : Type*} [CommGroup A] [Finite A] {a : A}
    (ha : ∀ chi : MulChar A ℂ, chi a = 1) :
    a = 1 := by
  by_contra hne
  obtain ⟨chi, hchi⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℂ hne
  exact hchi (ha chi)

end

end Towers.CField.RExist
