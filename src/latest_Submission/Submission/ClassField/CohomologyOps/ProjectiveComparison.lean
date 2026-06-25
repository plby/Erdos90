import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Comparing computations from projective resolutions

This file isolates the resolution-comparison identity used in the proof of
Proposition II.1.30.  Mathlib's `Functor.leftDerived_map_eq` computes a
derived morphism from any augmentation-compatible lift.  Applying it to an
identity morphism shows that the comparison between the two chosen
resolution computations is precisely the homology map induced by that lift.
-/

namespace Submission.CField.COps

open CategoryTheory

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasProjectiveResolutions C]
variable {D : Type w} [Category D] [Abelian D]

/-- The comparison between the derived-functor computations attached to two
projective resolutions is induced by any augmentation-compatible comparison
chain map. -/
theorem iso_derived_obj
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C}
    (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ ≫ Q.π = P.π) :
    (P.isoLeftDerivedObj F n).inv ≫
        (Q.isoLeftDerivedObj F n).hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D
          (ComplexShape.down ℕ) n).map φ := by
  have hmap := F.leftDerived_map_eq n (𝟙 X) φ (by simpa using hφ)
  rw [(F.leftDerived n).map_id] at hmap
  rw [← cancel_epi (P.isoLeftDerivedObj F n).hom,
    Iso.hom_inv_id_assoc]
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).inv,
    Iso.hom_inv_id]
  simpa only [Category.assoc] using hmap

/-- A chain map in an opposite category induces a cochain map in the
original category, with the direction reversed. -/
def unopCochainMap {K L : ChainComplex Cᵒᵖ ℕ} (f : K ⟶ L) :
    L.unop ⟶ K.unop :=
  (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map f.op

/-- Transposing the components of a chain homotopy in an opposite category
gives a cochain homotopy after applying `unopCochainMap`. -/
def unopCochainHomotopy {K L : ChainComplex Cᵒᵖ ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy (unopCochainMap f) (unopCochainMap g) where
  hom i j := (h.hom j i).unop
  zero i j hij := by
    simpa using congrArg Quiver.Hom.unop (h.zero j i hij)
  comm i := by
    have hi := congrArg Quiver.Hom.unop (h.comm i)
    let hh := fun i j ↦ (h.hom j i).unop
    cases i with
    | zero =>
        change (unopCochainMap f).f 0 =
          dNext 0 hh + prevD 0 hh + (unopCochainMap g).f 0
        rw [dNext_eq (C := L.unop) (D := K.unop) hh
              (i := 0) (i' := 1) (by simp),
            prevD_eq_zero (C := L.unop) (D := K.unop) hh 0 (by simp)]
        rw [dNext_eq_zero (C := K) (D := L) h.hom 0 (by simp),
            prevD_eq (C := K) (D := L) h.hom
              (j := 0) (j' := 1) (by simp)] at hi
        change (f.f 0).unop = _
        rw [hi]
        simp [hh, unopCochainMap]
        abel
    | succ n =>
        change (unopCochainMap f).f (n + 1) =
          dNext (n + 1) hh + prevD (n + 1) hh +
            (unopCochainMap g).f (n + 1)
        rw [dNext_eq (C := L.unop) (D := K.unop) hh
              (i := n + 1) (i' := n + 2) (by simp),
            prevD_eq (C := L.unop) (D := K.unop) hh
              (j := n + 1) (j' := n) (by simp)]
        rw [dNext_eq (C := K) (D := L) h.hom
              (i := n + 1) (i' := n) (by simp),
            prevD_eq (C := K) (D := L) h.hom
              (j := n + 1) (j' := n + 2) (by simp)] at hi
        change (f.f (n + 1)).unop = _
        rw [hi]
        simp [hh, unopCochainMap]
        abel

omit [HasProjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the homology/unop comparison, oriented for the
contravariant cochain map induced by a chain map in the opposite category. -/
theorem homology_unop_cochain {K L : ChainComplex Cᵒᵖ ℕ}
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (unopCochainMap f) n =
      (HomologicalComplex.homologyUnop L n).hom ≫
        (HomologicalComplex.homologyMap f n).unop ≫
        (HomologicalComplex.homologyUnop K n).inv := by
  have h := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality
      (unopCochainMap f) n)
  simp only [unop_comp] at h
  simp only [Quiver.Hom.unop_op] at h
  rw [show (HomologicalComplex.opFunctor C
      (ComplexShape.down ℕ).symm).map (unopCochainMap f).op = f by
        ext i
        rfl] at h
  have h' :
      (HomologicalComplex.homologyUnop L n).hom ≫
          (HomologicalComplex.homologyMap f n).unop =
        HomologicalComplex.homologyMap (unopCochainMap f) n ≫
          (HomologicalComplex.homologyUnop K n).hom := by
    dsimp [HomologicalComplex.homologyUnop]
    exact h
  rw [← cancel_mono (HomologicalComplex.homologyUnop K n).hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'.symm

section Ext

variable (R : Type w) [Ring R] [Linear R C] [EnoughProjectives C]

/-- Precomposition with a chain map, viewed on the linear-Yoneda cochain
complexes which compute `Ext`. -/
def linearYonedaPrecomposition {P Q : ChainComplex C ℕ}
    (Y : C) (f : P ⟶ Q) :
    Q.linearYonedaObj R Y ⟶ P.linearYonedaObj R Y :=
  unopCochainMap
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map f)

/-- Chain-homotopic maps induce homotopic precomposition maps on the
linear-Yoneda cochain complexes. -/
def yonedaPrecompositionHomotopy {P Q : ChainComplex C ℕ}
    (Y : C) {f g : P ⟶ Q} (h : Homotopy f g) :
    Homotopy (linearYonedaPrecomposition R Y f)
      (linearYonedaPrecomposition R Y g) :=
  unopCochainHomotopy
    (((linearYoneda R C).obj Y).rightOp.mapHomotopy h)

set_option backward.isDefEq.respectTransparency false in
/-- At the `Ext` level, the inverse comparison from `Q` to `P` is
contravariant precomposition by `φ`.  The two `homologyUnop` isomorphisms
make the opposite-category transport explicit. -/
theorem iso_ext_inv
    (n : ℕ) {X Y : C} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (hφ : φ ≫ Q.π = P.π) :
    (Q.isoExt n Y).inv ≫ (P.isoExt n Y).hom =
      (HomologicalComplex.homologyUnop
          (((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) |>.obj Q.complex) n).hom ≫
        ((
          (((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ)) ⋙
            HomologicalComplex.homologyFunctor (ModuleCat R)ᵒᵖ
              (ComplexShape.down ℕ) n).map φ).unop ≫
        (HomologicalComplex.homologyUnop
          (((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ) |>.obj P.complex) n).inv := by
  let F := ((linearYoneda R C).obj Y).rightOp
  have h := iso_derived_obj F n P Q φ hφ
  have hu := congrArg Quiver.Hom.unop h
  simp only [unop_comp] at hu
  dsimp only [F] at hu
  rw [ProjectiveResolution.isoExt, ProjectiveResolution.isoExt]
  dsimp [Ext]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [hu]
  rfl

/-- The same comparison formula, with the opposite-category transport
packaged as precomposition on the linear-Yoneda cochain complex. -/
theorem iso_ext_homology
    (n : ℕ) {X Y : C} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (hφ : φ ≫ Q.π = P.π) :
    (Q.isoExt n Y).inv ≫ (P.isoExt n Y).hom =
      HomologicalComplex.homologyMap
        (linearYonedaPrecomposition R Y φ) n := by
  rw [iso_ext_inv R n P Q φ hφ]
  exact (homology_unop_cochain
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ) n).symm

end Ext

end

end Submission.CField.COps
