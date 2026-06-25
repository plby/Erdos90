import Towers.ClassField.NormIndex.CanonicalTateFormula
import Towers.ClassField.KummerNormIndex.IdeleClassQuotient

/-!
# Chapter VII, Section 6, Lemma 6.1: exponent of the norm quotient

Extending an idèle class and then taking its norm raises it to the extension
degree.  Hence the literal idèle-class norm quotient is killed by that degree.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- The proof compares maps on two nested idèle quotient groups.
/-- Extending an idèle class and then applying the class norm raises the
class to the degree of the extension. -/
theorem canonical_comp_extension
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    let E := canonicalExtensionData (K := K) (L := L)
    (canonicalIdeleNorm (K := K) (L := L)).comp E.classMap =
      powMonoidHom (Module.finrank K L) := by
  dsimp only
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let E := canonicalExtensionData (K := K) (L := L)
  let hbij := canonical_fixed_bijective
    (K := K) (L := L)
  let hnorm := canonical_idele_compatible
    (K := K) (L := L)
  apply MonoidHom.ext
  intro c
  apply hbij.1
  apply Subtype.ext
  change E.classMap
      (canonicalIdeleNorm (K := K) (L := L) (E.classMap c)) =
    E.classMap (c ^ Module.finrank K L)
  rw [E.classmap_canonidele_classnorm hnorm]
  have hfixed (sigma : Gal(L/K)) :
      (ideleDistribAction (K := K) (L := L)).smul
        sigma (E.classMap c) = E.classMap c :=
    (E.class_map_fixed c).property sigma
  simp_rw [hfixed]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank, map_pow]

set_option maxHeartbeats 1000000 in
-- Quotient induction unfolds the idèle class group twice.
/-- The actual idèle-class norm quotient is killed by the extension degree. -/
theorem normExponentBridge :
    NormExponentBridge.{u} := by
  intro K L _ _ _ _ _ _ _ x
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let E := canonicalExtensionData (K := K) (L := L)
  refine Quotient.inductionOn' x fun c ↦ ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  refine ⟨E.classMap c, ?_⟩
  exact DFunLike.congr_fun
    (canonical_comp_extension K L) c

end

end Towers.CField.KNIndex
