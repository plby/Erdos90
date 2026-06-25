import Towers.ClassField.Shifting.RationalAllDegrees
import Towers.ClassField.Shifting.BottomToTrivial
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Milne, Class Field Theory, Lemma II.3.3(a): negative degrees

For a finite group, positive group homology with trivial rational
coefficients vanishes.  Via Milne's definition, this supplies the remaining
Tate-cohomological degrees `r ≤ -2` in the assertion
`H_T^r(G, ℚ) = 0` for every integer `r`.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep
open Towers.CField.COps

noncomputable section

variable (G : Type) [Group G] [Fintype G]

private abbrev rationalHomologyRepresentation : Rep ℤ G :=
  Rep.trivial ℤ G ℚ

private noncomputable def rationalHomologyScale (c : ℚ) :
    rationalHomologyRepresentation G ⟶ rationalHomologyRepresentation G :=
  Rep.ofHom ⟨LinearMap.mulLeft ℤ c, by simp⟩

private noncomputable def homologyAverageRetraction :
    Rep.coind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype (rationalHomologyRepresentation G)) ⟶
      rationalHomologyRepresentation G :=
  corestrictionTrace (rationalHomologyRepresentation G) (⊥ : Subgroup G) ≫
    rationalHomologyScale G ((Fintype.card G : ℚ)⁻¹)

private theorem homology_average_retraction :
    canonicalShiftEmbedding (rationalHomologyRepresentation G) ≫
      homologyAverageRetraction G =
        𝟙 (rationalHomologyRepresentation G) := by
  rw [homologyAverageRetraction, ← Category.assoc,
    canonicalShiftEmbedding]
  have htrace := res_coind_corestriction
    (rationalHomologyRepresentation G) (⊥ : Subgroup G)
  calc
    _ = ((⊥ : Subgroup G).index • 𝟙 (rationalHomologyRepresentation G)) ≫
        rationalHomologyScale G ((Fintype.card G : ℚ)⁻¹) :=
      congrArg (fun f => f ≫ rationalHomologyScale G
        ((Fintype.card G : ℚ)⁻¹)) htrace
    _ = 𝟙 (rationalHomologyRepresentation G) := by
      ext x
      change (Fintype.card G : ℚ)⁻¹ * ((⊥ : Subgroup G).index • x) = x
      rw [Subgroup.index_bot, Nat.card_eq_fintype_card]
      simp [nsmul_eq_mul, Fintype.card_ne_zero]

private noncomputable def homologyCoinducedRetract :
    Retract (rationalHomologyRepresentation G)
      (Rep.coind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype
          (rationalHomologyRepresentation G))) where
  i := canonicalShiftEmbedding (rationalHomologyRepresentation G)
  r := homologyAverageRetraction G
  retract := homology_average_retraction G

private theorem zero_retract_homology {C : Type*} [Category C]
    {X Y : C} (h : Retract X Y) (hY : IsZero Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩⟩⟩
  · intro f
    calc
      f = 𝟙 X ≫ f := by simp
      _ = (h.i ≫ h.r) ≫ f := by rw [h.retract]
      _ = h.i ≫ (h.r ≫ f) := Category.assoc _ _ _
      _ = h.i ≫ hY.to_ Z := by rw [hY.eq_of_src (h.r ≫ f) (hY.to_ Z)]
  · intro f
    calc
      f = f ≫ 𝟙 X := by simp
      _ = f ≫ (h.i ≫ h.r) := by rw [h.retract]
      _ = (f ≫ h.i) ≫ h.r := (Category.assoc _ _ _).symm
      _ = hY.from_ Z ≫ h.r := by rw [hY.eq_of_tgt (f ≫ h.i) (hY.from_ Z)]

omit [Fintype G] in
/-- **Lemma II.3.3(a), degrees at most `-2`.** Positive group homology with
trivial rational coefficients vanishes for every finite group. -/
theorem homology_trivial_rat
    [Finite G] (n : ℕ) (hn : 0 < n) :
    IsZero (groupHomology (Rep.trivial ℤ G ℚ) n) := by
  letI := Fintype.ofFinite G
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup G)) :=
    Classical.decRel _
  let A := Rep.res (⊥ : Subgroup G).subtype
    (rationalHomologyRepresentation G)
  let e : Rep.ind (⊥ : Subgroup G).subtype A ≅
      Rep.coind (⊥ : Subgroup G).subtype A := Rep.indCoindIso A
  have hi : IsZero
      (groupHomology (Rep.ind (⊥ : Subgroup G).subtype A) n) :=
    zero_homology_induced A n hn
  have hc : IsZero
      (groupHomology (Rep.coind (⊥ : Subgroup G).subtype A) n) :=
    IsZero.of_iso hi ((groupHomology.functor ℤ G n).mapIso e).symm
  let h := (homologyCoinducedRetract G).map
    (groupHomology.functor ℤ G n)
  exact zero_retract_homology h hc

end

end Towers.CField.Shifting
