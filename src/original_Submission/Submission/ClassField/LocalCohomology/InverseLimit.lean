import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Milne, Class Field Theory, Proposition I.A.8

The inverse limit of an inverse system of exact sequences of finite abelian
groups is exact. We use the concrete description of an inverse limit as the
type of compatible sections. The only non-formal step is the existence of a
compatible family of lifts; it is the finite inverse-system compactness
theorem (`nonempty_sections_of_finite_inverse_system`).
-/

namespace Submission.CField.LocalCohomology

open CategoryTheory

universe u v

variable {I : Type u} [Preorder I] [IsDirectedOrder I]

/-- The concrete inverse limit of a diagram of additive commutative groups. -/
abbrev inverseLimit (F : Iᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  ((F ⋙ forget₂ AddCommGrpCat AddGrpCat) ⋙ forget AddGrpCat).sections

/-- A natural transformation of inverse systems induces a map on their
concrete inverse limits. -/
def inverseLimitMap {F G : Iᵒᵖ ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) :
    inverseLimit F → inverseLimit G := fun x =>
  ⟨fun i => η.app i (x.1 i), by
    intro i j φ
    calc
      G.map φ (η.app i (x.1 i)) = η.app j (F.map φ (x.1 i)) :=
        (CategoryTheory.congr_fun (η.naturality φ) (x.1 i)).symm
      _ = η.app j (x.1 j) := CategoryTheory.congr_arg (η.app j) (x.2 φ)⟩

omit [IsDirectedOrder I] in
@[simp]
theorem inverse_limit {F G : Iᵒᵖ ⥤ AddCommGrpCat.{v}}
    (η : F ⟶ G) (x : inverseLimit F) (i : Iᵒᵖ) :
    (inverseLimitMap η x).1 i = η.app i (x.1 i) :=
  rfl

/-- The fiber, over a compatible section `b`, of a pointwise map of inverse
systems. Naturality makes these fibers into an inverse system of finite
types. -/
def liftFiberFunctor {A B : Iᵒᵖ ⥤ AddCommGrpCat.{v}}
    (f : A ⟶ B) (b : inverseLimit B) : Iᵒᵖ ⥤ Type v where
  obj i := {a : A.obj i // f.app i a = b.1 i}
  map {i j} φ := TypeCat.ofHom fun a => ⟨A.map φ a.1, by
    calc
      f.app j (A.map φ a.1) = B.map φ (f.app i a.1) := by
        simp only [← CategoryTheory.comp_apply]
        exact CategoryTheory.congr_fun (f.naturality φ) a.1
      _ = B.map φ (b.1 i) := congrArg (B.map φ) a.2
      _ = b.1 j := b.2 φ⟩
  map_id _ := by
    ext
    simp
  map_comp _ _ := by
    ext
    simp

/-- **Proposition I.A.8.** The inverse limit of a directed inverse system of
pointwise exact sequences of finite abelian groups is exact.

No surjectivity assumption is made on the transition maps: finiteness is
exactly what supplies a compatible family of pointwise lifts. -/
theorem limit_exact_pointwise
    (A B C : Iᵒᵖ ⥤ AddCommGrpCat.{v})
    (f : A ⟶ B) (g : B ⟶ C)
    [∀ i, Finite (A.obj i)]
    (h : ∀ i, Function.Exact (f.app i) (g.app i)) :
    Function.Exact (inverseLimitMap f) (inverseLimitMap g) := by
  intro b
  constructor
  · intro hb
    have hb_pointwise : ∀ i, g.app i (b.1 i) = 0 := by
      intro i
      have hi := congrArg (fun s => s.1 i) hb
      simpa using hi
    let P : Iᵒᵖ ⥤ Type v := liftFiberFunctor f b
    letI : ∀ i, Finite (P.obj i) := fun i =>
      Finite.of_injective (fun a : P.obj i => a.1) (fun _ _ hxy => Subtype.ext hxy)
    letI : ∀ i, Nonempty (P.obj i) := fun i => by
      obtain ⟨a, ha⟩ := (h i (b.1 i)).mp (hb_pointwise i)
      exact ⟨⟨a, ha⟩⟩
    obtain ⟨a, ha⟩ := nonempty_sections_of_finite_inverse_system P
    let a' : inverseLimit A := ⟨fun i => (a i).1, by
      intro i j φ
      simpa [P, liftFiberFunctor] using congrArg Subtype.val (ha φ)⟩
    refine ⟨a', ?_⟩
    apply Subtype.ext
    funext i
    exact (a i).2
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext i
    simpa using (h i).apply_apply_eq_zero (a.1 i)

end Submission.CField.LocalCohomology
