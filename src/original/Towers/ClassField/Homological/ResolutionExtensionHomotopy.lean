import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Milne, Class Field Theory, Lemmas II.A.9 and II.A.10

Morphisms into an injective resolution extend to arbitrary resolutions, and any two extensions
of the same morphism are homotopic.
-/

namespace Towers.CField.Homological

open CategoryTheory CategoryTheory.Limits Category
open CategoryTheory.Injective

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An arbitrary cochain resolution of `Z`.  Unlike `InjectiveResolution`, its terms are not
required to be injective. -/
structure Resolution (Z : C) where
  /-- The cochain complex underlying the resolution. -/
  cocomplex : CochainComplex C ℕ
  /-- The augmentation in degree zero. -/
  ι : Z ⟶ cocomplex.X 0
  /-- Exactness at `Z`, equivalently the initial zero in the augmented complex. -/
  [mono_ι : Mono ι]
  /-- The augmentation followed by the first differential is zero. -/
  ι_d : ι ≫ cocomplex.d 0 1 = 0
  /-- Exactness at degree zero. -/
  exact_zero : (ShortComplex.mk ι (cocomplex.d 0 1) ι_d).Exact
  /-- Exactness in every positive degree. -/
  exact_succ (n : ℕ) :
    (ShortComplex.mk (cocomplex.d n (n + 1)) (cocomplex.d (n + 1) (n + 2))
      (cocomplex.d_comp_d n (n + 1) (n + 2))).Exact

attribute [instance] Resolution.mono_ι

namespace Resolution

variable {M N : C} (I : Resolution M) (J : InjectiveResolution N)

/-- The degree-zero component of the extension in Lemma II.A.9. -/
private def extendFZero (f : M ⟶ N) : I.cocomplex.X 0 ⟶ J.cocomplex.X 0 :=
  factorThru (f ≫ J.ι.f 0) I.ι

@[reassoc (attr := simp)]
private lemma ι_comp_extendFZero (f : M ⟶ N) :
    I.ι ≫ extendFZero I J f = f ≫ J.ι.f 0 := by
  apply comp_factorThru

/-- The degree-one component of the extension in Lemma II.A.9. -/
private def extendFOne (f : M ⟶ N) : I.cocomplex.X 1 ⟶ J.cocomplex.X 1 :=
  I.exact_zero.descToInjective (extendFZero I J f ≫ J.cocomplex.d 0 1) (by
    dsimp
    rw [← assoc]
    simp only [extendFZero, comp_factorThru]
    simpa only [assoc] using
      (congrArg (fun k => f ≫ k) J.ι_f_zero_comp_complex_d).trans Limits.comp_zero)

@[simp]
private lemma extend_f_comm (f : M ⟶ N) :
    I.cocomplex.d 0 1 ≫ extendFOne I J f =
      extendFZero I J f ≫ J.cocomplex.d 0 1 := by
  apply I.exact_zero.comp_descToInjective

/-- The inductive step constructing the next component of the extension. -/
private def extendFSucc (n : ℕ)
    (g : I.cocomplex.X n ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : I.cocomplex.d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    Σ' g'' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 2),
      I.cocomplex.d (n + 1) (n + 2) ≫ g'' =
        g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  ⟨(I.exact_succ n).descToInjective
      (g' ≫ J.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
    (I.exact_succ n).comp_descToInjective _ _⟩

/-- The extension of a morphism from an arbitrary resolution to an injective resolution. -/
def extend (f : M ⟶ N) : I.cocomplex ⟶ J.cocomplex :=
  CochainComplex.mkHom _ _ (extendFZero I J f) (extendFOne I J f)
    (extend_f_comm I J f).symm fun n ⟨g, g', w⟩ =>
      ⟨(extendFSucc I J n g g' w.symm).1, (extendFSucc I J n g g' w.symm).2.symm⟩

/-- The extension agrees with the original morphism on the augmentations. -/
@[reassoc (attr := simp)]
theorem ι_comp_extend_f_zero (f : M ⟶ N) :
    I.ι ≫ (I.extend J f).f 0 = f ≫ J.ι.f 0 := by
  simp [extend]

/-- **Lemma II.A.9.** Every morphism extends from an arbitrary resolution to an injective
resolution. -/
theorem exists_extension (f : M ⟶ N) :
    ∃ g : I.cocomplex ⟶ J.cocomplex, I.ι ≫ g.f 0 = f ≫ J.ι.f 0 :=
  ⟨I.extend J f, I.ι_comp_extend_f_zero J f⟩

/-- The first component of a null-homotopy for a map vanishing on the augmentation. -/
private def homotopyZeroZero {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ e.f 0 = 0) :
    I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  I.exact_zero.descToInjective (e.f 0) (by
    dsimp
    exact comm)

@[reassoc (attr := simp)]
private lemma comp_homotopy_zero {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ e.f 0 = 0) :
    I.cocomplex.d 0 1 ≫ homotopyZeroZero e comm = e.f 0 :=
  I.exact_zero.comp_descToInjective _ _

/-- The second component of a null-homotopy for a map vanishing on the augmentation. -/
private def homotopyZeroOne {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ e.f 0 = 0) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (I.exact_succ 0).descToInjective
    (e.f 1 - homotopyZeroZero e comm ≫ J.cocomplex.d 0 1) (by
      rw [Preadditive.comp_sub, comp_homotopy_zero_assoc e comm,
        HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopy_one {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ e.f 0 = 0) :
    I.cocomplex.d 1 2 ≫ homotopyZeroOne e comm =
      e.f 1 - homotopyZeroZero e comm ≫ J.cocomplex.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/-- The inductive step for a null-homotopy. -/
private def homotopyZeroSucc {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (n : ℕ)
    (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : e.f (n + 1) =
      I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective
    (e.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2)) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        assoc, assoc, HomologicalComplex.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopy_succ {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (n : ℕ)
    (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : e.f (n + 1) =
      I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ homotopyZeroSucc e n g g' w =
      e.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/-- A cochain map which vanishes on the augmentation is null-homotopic. -/
private def homotopyZero {I : Resolution M} {J : InjectiveResolution N}
    (e : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ e.f 0 = 0) : Homotopy e 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero e comm) (by simp)
    (homotopyZeroOne e comm) (by simp) fun n ⟨g, g', w⟩ =>
      ⟨homotopyZeroSucc e n g g' (by simpa only [add_comm] using w), by simp⟩

/-- A chosen homotopy between two extensions of the same morphism. -/
def extensionHomotopy (f : M ⟶ N) (g h : I.cocomplex ⟶ J.cocomplex)
    (g_comm : I.ι ≫ g.f 0 = f ≫ J.ι.f 0)
    (h_comm : I.ι ≫ h.f 0 = f ≫ J.ι.f 0) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (homotopyZero (g - h) (by simp [g_comm, h_comm]))

/-- **Lemma II.A.10.** Any two extensions of the same morphism from an arbitrary resolution to
an injective resolution are homotopic. -/
theorem extensions_homotopic (f : M ⟶ N) (g h : I.cocomplex ⟶ J.cocomplex)
    (g_comm : I.ι ≫ g.f 0 = f ≫ J.ι.f 0)
    (h_comm : I.ι ≫ h.f 0 = f ≫ J.ι.f 0) : Nonempty (Homotopy g h) :=
  ⟨I.extensionHomotopy J f g h g_comm h_comm⟩

end Resolution

end

end Towers.CField.Homological
