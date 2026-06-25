import Towers.ClassField.Reciprocity.ArtinMapStatements

/-!
# Chapter V, Section 5, Theorem 5.3 (Idelic Recip Law)

This file spells out both quotient isomorphisms displayed in Milne's
statement.  The first is the quotient of the ideles by the product of the
principal ideles and the idele norms.  The second is the equivalent quotient
of the idele class group by the image of the norm subgroup.

The arithmetic assertion that remains to be proved in the project is exactly
`IdeleReciprocityLaw`.  No stronger input is used: the final theorem
shows that the source statement below is equivalent to that assertion.  The
passage between the two displayed quotients is entirely group-theoretic.
-/

namespace Towers.CField.Recip

open scoped IsMulCommutative

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable local instance finiteAbelianSubextensionNumberField_source
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

local notation "𝑜" => NumberField.RingOfIntegers K

/-- The canonical identification

`C_K / Nm(C_L) ≃ I_K / (Kˣ · Nm(I_L))`.

It is Noether's third isomorphism theorem.  Mapping the join of the principal
idele subgroup and `N` to the idele class group gives the same subgroup as
mapping `N`, since the principal ideles map to the identity. -/
noncomputable def ideleClassEquiv
    (N : Subgroup (IdeleGroup 𝑜 K)) :
    (IdeleClassGroup 𝑜 K ⧸
        N.map (QuotientGroup.mk' (principalIdeles 𝑜 K))) ≃*
      (IdeleGroup 𝑜 K ⧸ (principalIdeles 𝑜 K ⊔ N)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq])).trans
    (QuotientGroup.quotientQuotientEquivQuotient
      (principalIdeles 𝑜 K) (principalIdeles 𝑜 K ⊔ N) le_sup_left)

@[simp]
theorem idele_class_mk
    (N : Subgroup (IdeleGroup 𝑜 K)) (x : IdeleGroup 𝑜 K) :
    ideleClassEquiv (K := K) N
        (QuotientGroup.mk'
          (N.map (QuotientGroup.mk' (principalIdeles 𝑜 K)))
          (QuotientGroup.mk' (principalIdeles 𝑜 K) x)) =
      QuotientGroup.mk' (principalIdeles 𝑜 K ⊔ N) x := by
  rfl

/-- The first quotient isomorphism displayed in Theorem V.5.3(b). -/
noncomputable def ideleReciprocityEquiv
    (L : FASubext K)
    (phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw 𝑜 K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    (IdeleGroup 𝑜 K ⧸
        (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1))) ≃*
      Gal(L.1/K) :=
  finiteReciprocityEquiv 𝑜 K Gal(L.1/K)
    ((localAbelianRestriction L).comp phi)
    (ideleNormSubgroup (K := K) (L := L.1)) hL

@[simp]
theorem reciprocity_equiv_mk
    (L : FASubext K)
    (phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw 𝑜 K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1)))
    (x : IdeleGroup 𝑜 K) :
    ideleReciprocityEquiv L phi hL
        (QuotientGroup.mk'
          (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1)) x) =
      localAbelianRestriction L (phi x) :=
  finite_reciprocity_mk 𝑜 K Gal(L.1/K)
    ((localAbelianRestriction L).comp phi)
    (ideleNormSubgroup (K := K) (L := L.1)) hL x

/-- The equivalent idele-class quotient isomorphism displayed immediately
after Theorem V.5.3(b). -/
noncomputable def ideleClassReciprocity
    (L : FASubext K)
    (phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw 𝑜 K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    (IdeleClassGroup 𝑜 K ⧸ ideleClassSubgroup L) ≃* Gal(L.1/K) :=
  (ideleClassEquiv (K := K)
    (ideleNormSubgroup (K := K) (L := L.1))).trans
      (ideleReciprocityEquiv L phi hL)

@[simp]
theorem idele_reciprocity_mk
    (L : FASubext K)
    (phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw 𝑜 K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1)))
    (x : IdeleGroup 𝑜 K) :
    ideleClassReciprocity L phi hL
        (QuotientGroup.mk' (ideleClassSubgroup L)
          (QuotientGroup.mk' (principalIdeles 𝑜 K) x)) =
      localAbelianRestriction L (phi x) := by
  change ideleReciprocityEquiv L phi hL
      (ideleClassEquiv (K := K)
        (ideleNormSubgroup (K := K) (L := L.1))
        (QuotientGroup.mk'
          ((ideleNormSubgroup (K := K) (L := L.1)).map
            (QuotientGroup.mk' (principalIdeles 𝑜 K)))
          (QuotientGroup.mk' (principalIdeles 𝑜 K) x))) =
    localAbelianRestriction L (phi x)
  rw [idele_class_mk]
  exact reciprocity_equiv_mk L phi hL x

/-- Compatibility of the two quotient presentations: the class-group
isomorphism is the first displayed isomorphism after the canonical third
isomorphism theorem identification. -/
theorem idele_reciprocity_compatibility
    (L : FASubext K)
    (phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K)
    (hL : FiniteReciprocityLaw 𝑜 K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)
      (ideleNormSubgroup (K := K) (L := L.1))) :
    ideleClassReciprocity L phi hL =
      (ideleClassEquiv (K := K)
        (ideleNormSubgroup (K := K) (L := L.1))).trans
          (ideleReciprocityEquiv L phi hL) :=
  rfl

set_option maxHeartbeats 1600000 in
-- The nested global/local quotient types require an enlarged elaboration budget.
/-- The exact still-missing arithmetic reciprocity assertion implies the
literal source statement, with both displayed isomorphisms constructed. -/
theorem idelic_law_idele
    (hrec : IdeleReciprocityLaw (K := K)) :
    (∀ phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K,
          ContinuousGlobalArtin phi →
            TrivialPrincipalIdeles 𝑜 K
                (AbsoluteAbelianGalois K) phi ∧
            ∀ L : FASubext K,
              ∃ (eI : (IdeleGroup 𝑜 K ⧸
                    (principalIdeles 𝑜 K ⊔
                      ideleNormSubgroup (K := K) (L := L.1))) ≃* Gal(L.1/K))
                (eC : (IdeleClassGroup 𝑜 K ⧸ ideleClassSubgroup L) ≃*
                  Gal(L.1/K)),
                (∀ x : IdeleGroup 𝑜 K,
                  eI (QuotientGroup.mk'
                      (principalIdeles 𝑜 K ⊔
                        ideleNormSubgroup (K := K) (L := L.1)) x) =
                    localAbelianRestriction L (phi x)) ∧
                (∀ x : IdeleGroup 𝑜 K,
                  eC (QuotientGroup.mk' (ideleClassSubgroup L)
                      (QuotientGroup.mk' (principalIdeles 𝑜 K) x)) =
                    localAbelianRestriction L (phi x)) ∧
                eC =
                  (ideleClassEquiv (K := K)
                    (ideleNormSubgroup (K := K) (L := L.1))).trans eI) := by
  intro phi hphi
  obtain ⟨hprincipal, hfinite⟩ := hrec phi hphi
  refine ⟨hprincipal, ?_⟩
  intro L
  refine ⟨ideleReciprocityEquiv L phi (hfinite L),
    ideleClassReciprocity L phi (hfinite L), ?_, ?_, rfl⟩
  · intro x
    exact reciprocity_equiv_mk L phi (hfinite L) x
  · intro x
    exact idele_reciprocity_mk L phi (hfinite L) x

set_option maxHeartbeats 1600000 in
-- The nested global/local quotient types require an enlarged elaboration budget.
/-- Conversely, the first displayed quotient isomorphism, together with its
compatibility with the finite Artin map, recovers exactly surjectivity and
the kernel formula in `FiniteReciprocityLaw`. -/
theorem reciprocity_law_idelic
    (h53 : (∀ phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K,
          ContinuousGlobalArtin phi →
            TrivialPrincipalIdeles 𝑜 K
                (AbsoluteAbelianGalois K) phi ∧
            ∀ L : FASubext K,
              ∃ (eI : (IdeleGroup 𝑜 K ⧸
                    (principalIdeles 𝑜 K ⊔
                      ideleNormSubgroup (K := K) (L := L.1))) ≃* Gal(L.1/K))
                (eC : (IdeleClassGroup 𝑜 K ⧸ ideleClassSubgroup L) ≃*
                  Gal(L.1/K)),
                (∀ x : IdeleGroup 𝑜 K,
                  eI (QuotientGroup.mk'
                      (principalIdeles 𝑜 K ⊔
                        ideleNormSubgroup (K := K) (L := L.1)) x) =
                    localAbelianRestriction L (phi x)) ∧
                (∀ x : IdeleGroup 𝑜 K,
                  eC (QuotientGroup.mk' (ideleClassSubgroup L)
                      (QuotientGroup.mk' (principalIdeles 𝑜 K) x)) =
                    localAbelianRestriction L (phi x)) ∧
                eC =
                  (ideleClassEquiv (K := K)
                    (ideleNormSubgroup (K := K) (L := L.1))).trans eI)) :
    IdeleReciprocityLaw (K := K) := by
  intro phi hphi
  obtain ⟨hprincipal, hL⟩ := h53 phi hphi
  refine ⟨hprincipal, ?_⟩
  intro L
  obtain ⟨eI, eC, heI, heC, hcompat⟩ := hL L
  constructor
  · intro σ
    obtain ⟨q, rfl⟩ := eI.surjective σ
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1)) q
    refine ⟨x, ?_⟩
    change localAbelianRestriction L (phi x) =
      eI (QuotientGroup.mk'
        (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1)) x)
    exact (heI x).symm
  · apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hq : QuotientGroup.mk'
          (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1)) x = 1 :=
        (QuotientGroup.eq_one_iff x).2 hx
      change localAbelianRestriction L (phi x) = 1
      rw [← heI x, hq]
      exact map_one eI
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      apply (QuotientGroup.eq_one_iff x).1
      apply (MulEquiv.map_eq_one_iff eI).1
      change eI (QuotientGroup.mk'
        (principalIdeles 𝑜 K ⊔ ideleNormSubgroup (K := K) (L := L.1)) x) = 1
      rw [heI x]
      exact hx

/-- The literal statement introduces no extra arithmetic hypothesis: it is
logically equivalent to the existing exact reciprocity-law proposition. -/
theorem idelic_reciprocity_law :
    (
      ∀ phi : IdeleGroup 𝑜 K →* AbsoluteAbelianGalois K,
          ContinuousGlobalArtin phi →
            TrivialPrincipalIdeles 𝑜 K
                (AbsoluteAbelianGalois K) phi ∧
            ∀ L : FASubext K,
              ∃ (eI : (IdeleGroup 𝑜 K ⧸
                    (principalIdeles 𝑜 K ⊔
                      ideleNormSubgroup (K := K) (L := L.1))) ≃* Gal(L.1/K))
                (eC : (IdeleClassGroup 𝑜 K ⧸ ideleClassSubgroup L) ≃*
                  Gal(L.1/K)),
                (∀ x : IdeleGroup 𝑜 K,
                  eI (QuotientGroup.mk'
                      (principalIdeles 𝑜 K ⊔
                        ideleNormSubgroup (K := K) (L := L.1)) x) =
                    localAbelianRestriction L (phi x)) ∧
                (∀ x : IdeleGroup 𝑜 K,
                  eC (QuotientGroup.mk' (ideleClassSubgroup L)
                      (QuotientGroup.mk' (principalIdeles 𝑜 K) x)) =
                    localAbelianRestriction L (phi x)) ∧
                eC =
                  (ideleClassEquiv (K := K)
                    (ideleNormSubgroup (K := K) (L := L.1))).trans eI
    ) ↔
      IdeleReciprocityLaw (K := K) := by
  exact ⟨reciprocity_law_idelic,
    idelic_law_idele⟩

end

end Towers.CField.Recip
