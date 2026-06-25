import Towers.ClassField.NormLimitation.FixedField

/-!
# Chapter VII, Section 9, Lemma 9.1

This is the complete fixed-field proof from the source.  Global reciprocity
identifies a norm group with the kernel of the finite idèle-class Artin map.
For a larger subgroup `V`, its image in the finite Galois group fixes a
finite abelian subextension, and the restriction-kernel calculation shows
that the norm group of that fixed field is exactly `V`.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open scoped IsMulCommutative

noncomputable section

universe u

set_option maxHeartbeats 20000000 in
-- The fixed-field construction and both finite Artin kernels unfold together.
/-- **Lemma VII.9.1.**  Under the already established global Artin-map and
reciprocity theorems, every subgroup containing a norm group is a norm
group.  These are prior theorems in the source, rather than additional
hypotheses on `U` or `V`. -/
theorem of_globalReciprocity
    (K : Type u) [Field K] [NumberField K]
    (hArtin : GlobalArtinProposition (K := K))
    (hrec : IdeleReciprocityLaw (K := K))
    (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K))
    (hU : IdeleNormGroup K U) (hUV : U ≤ V) :
    IdeleNormGroup K V := by
  obtain ⟨L, hLU⟩ := hU
  obtain ⟨phi, hphi, _⟩ := hArtin
  let hL := (hrec phi hphi).2 L
  let f := ideleClassArtin L phi hL
  have hfker : f.ker = U := by
    rw [idele_artin_ker L phi hL, hLU]
  let H : Subgroup Gal(L.1/K) := V.map f
  let M : FASubext K := fixedSubextension L H
  let hM := (hrec phi hphi).2 M
  have hfixed :
      (ideleClassArtin M phi hM).ker = H.comap f := by
    exact fixed_subextension_ker
      phi hphi hrec L H
  have hfker_le : f.ker ≤ V := by
    rw [hfker]
    exact hUV
  have hquotient : (subgroupQuotientMap f V).ker = V :=
    subgroup_quotient_ker f V hfker_le
  refine ⟨M, ?_⟩
  calc
    ideleClassSubgroup M =
        (ideleClassArtin M phi hM).ker :=
      (idele_artin_ker M phi hM).symm
    _ = H.comap f := hfixed
    _ = (subgroupQuotientMap f V).ker := by
      ext c
      change f c ∈ V.map f ↔
        QuotientGroup.mk' (V.map f) (f c) = 1
      exact (QuotientGroup.eq_one_iff (f c)).symm
    _ = V := hquotient

/-- Universe-polymorphic source statement.  Lemma VII.9.1 therefore has no
arithmetic bridge left once Theorems V.5.2 and V.5.3 are in scope. -/
theorem global_reciprocity_statement
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (hrec : ∀ (K : Type u) [Field K] [NumberField K],
      IdeleReciprocityLaw (K := K)) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V) := by
  intro K _ _ U V hU hUV
  exact of_globalReciprocity K (hArtin K) (hrec K)
    U V hU hUV

end

end Towers.CField.NLimita
