import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Milne, Class Field Theory, Statement II.2.2

If `P` is a projective `G`-module, then its positive-degree group homology
vanishes.  We realize `P` as a retract of the module induced from the trivial
subgroup on the underlying coefficient module of `P`, apply Shapiro's lemma to the
induced module, and pass the vanishing to the retract.
-/

namespace Submission.CField.TCohomo

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The underlying module of `P`, with the trivial subgroup acting trivially. -/
private abbrev bottomTrivial (P : Rep.{u} k G) :
    Rep.{u} k (⊥ : Subgroup G) :=
  Rep.trivial k (⊥ : Subgroup G) P

/-- On the trivial subgroup, the trivial action and the restriction of the
given `G`-action agree. -/
private def bottomToRestriction (P : Rep.{u} k G) :
    bottomTrivial P ⟶ Rep.res (⊥ : Subgroup G).subtype P :=
  Rep.ofHom ⟨LinearMap.id, fun s ↦ LinearMap.ext fun x ↦ by
    obtain rfl : s = 1 := Subtype.ext (Subgroup.mem_bot.mp s.property)
    simp⟩

/-- The induced module which canonically surjects onto `P`. -/
private abbrev inducedCover (P : Rep.{u} k G) : Rep.{u} k G :=
  Rep.ind (⊥ : Subgroup G).subtype (bottomTrivial P)

/-- The counit from the module induced on the underlying coefficient module of `P`
to `P`. -/
private def inducedCoverMap (P : Rep.{u} k G) : inducedCover P ⟶ P :=
  (Rep.indResHomEquiv (⊥ : Subgroup G).subtype (bottomTrivial P) P).symm
    (bottomToRestriction P)

@[simp]
private theorem induced_ind_v (P : Rep.{u} k G) (x : P) :
    (inducedCoverMap P).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (bottomTrivial P).ρ 1 x) = x := by
  simp [inducedCoverMap, Rep.indResHomEquiv, bottomToRestriction]

private instance (P : Rep.{u} k G) : Epi (inducedCoverMap P) := by
  rw [Rep.epi_iff_surjective]
  intro x
  refine ⟨Representation.IndV.mk (⊥ : Subgroup G).subtype
    (bottomTrivial P).ρ 1 x, ?_⟩
  exact induced_ind_v P x

/-- A retract of a zero object is zero. -/
private theorem zero_retract {C : Type u} [Category C]
    {X Y : C} (h : Retract X Y) (hY : Limits.IsZero Y) : Limits.IsZero X := by
  refine ⟨fun Z ↦ ⟨⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩⟩,
    fun Z ↦ ⟨⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩⟩⟩
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

/-- A projective `G`-module is a retract of the module induced from the
trivial subgroup on its underlying abelian group. -/
private def projectiveRetractInduced (P : Rep.{u} k G) [Projective P] :
    Retract P (inducedCover P) where
  i := Projective.factorThru (𝟙 P) (inducedCoverMap P)
  r := inducedCoverMap P
  retract := Projective.factorThru_comp (𝟙 P) (inducedCoverMap P)

/-- Shapiro's lemma reduces positive homology of the induced cover to the
trivial subgroup, whose positive homology vanishes. -/
private theorem homology_induced_cover
    (P : Rep.{u} k G) (n : ℕ) :
    Limits.IsZero (groupHomology (inducedCover P) (n + 1)) := by
  letI := Classical.decEq G
  have hP : Limits.IsZero (groupHomology (bottomTrivial P) (n + 1)) :=
    isZero_groupHomology_succ_of_subsingleton (A := bottomTrivial P) n
  exact Limits.IsZero.of_iso hP
    (groupHomology.indIso (⊥ : Subgroup G) (bottomTrivial P) (n + 1))

/-- **Statement II.2.2.** If `P` is a projective `G`-module, then
`H_r(G,P) = 0` for every `r > 0`. -/
theorem homology_succ_projective
    (P : Rep.{u} k G) [Projective P] (n : ℕ) :
    Limits.IsZero (groupHomology P (n + 1)) := by
  let h : Retract (groupHomology P (n + 1))
      (groupHomology (inducedCover P) (n + 1)) :=
    (projectiveRetractInduced P).map (groupHomology.functor k G (n + 1))
  exact zero_retract h (homology_induced_cover P n)

/-- Positive-degree formulation of Statement II.2.2. -/
theorem zero_homology_projective
    (P : Rep.{u} k G) [Projective P] (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupHomology P n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact homology_succ_projective P m

end

end Submission.CField.TCohomo
