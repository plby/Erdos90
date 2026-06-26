import Towers.ClassField.FormalGroups.AdicFormalGroup

/-!
# Class Field Theory, Chapter I: homomorphisms of adic formal groups

A homomorphism of formal group laws evaluates to an additive homomorphism
between the corresponding groups on an adic ideal.  Formal identity,
composition, and isomorphism therefore evaluate functorially as well.
-/

namespace Towers.CField.FGroups

open Filter MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [T2Space R] [CompleteSpace R]

namespace FGLaw

noncomputable section

namespace Hom

variable {I : Ideal R} (hI : IsAdic I)
  {F G H : FGLaw R}

private theorem eval₂_zero_eq_constantCoeff
    {sigma : Type*} (hI : IsAdic I) (f : MvPowerSeries sigma R) :
    eval₂ (RingHom.id R) (fun _ ↦ (0 : R)) f = constantCoeff f := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  have h := eval₂_unique (σ := sigma) (R := R) (S := R)
    (φ := RingHom.id R) (a := fun _ ↦ (0 : R))
    (ε := constantCoeff) continuous_id HasEval.zero
    (WithPiTopology.continuous_constantCoeff R)
    (fun p ↦ by
      rw [MvPolynomial.eval₂_zero'_apply]
      rfl)
  exact (congrFun h f).symm

private theorem eval₂_substitute_adic
    {sigma : Type*} [Finite sigma]
    (hI : IsAdic I)
    (P : BinarySeries R) (x y : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (a : sigma → R) (ha : ∀ i, a i ∈ I) :
    eval₂ (RingHom.id R) a (substitute P x y) =
      eval₂ (RingHom.id R)
        (Fin.cases (eval₂ (RingHom.id R) a x)
          (fun _ ↦ eval₂ (RingHom.id R) a y)) P := by
  have h := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (Fin.cases x (fun _ ↦ y))
    (fun i ↦ Fin.cases hx (fun _ ↦ hy) i) a ha P
  change eval₂ (RingHom.id R) a (substitute P x y) = _ at h
  rw [h]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem eval₂_compose_adic
    {sigma : Type*} [Finite sigma]
    (hI : IsAdic I)
    (f : UnarySeries R) (x : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0)
    (a : sigma → R) (ha : ∀ i, a i ∈ I) :
    eval₂ (RingHom.id R) a (compose f x) =
      eval₂ (RingHom.id R)
        (fun _ ↦ eval₂ (RingHom.id R) a x) f := by
  simpa only [compose] using
    mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
      hI (fun _ : Fin 1 ↦ x) (fun _ ↦ hx) a ha f

private theorem coe_adic_value₂
    {A B : FGLaw R} (f : Hom A B) (x : I) :
    (f.adicValue hI x : R) =
      eval₂ (RingHom.id R) (fun _ ↦ (x : R)) f.toSeries :=
  rfl

private theorem coe_law_adic₂
    (A : FGLaw R) (x y : I) :
    (A.adicValue hI x y : R) =
      eval₂ (RingHom.id R)
        (Fin.cases (x : R) (fun _ ↦ (y : R))) A.law := by
  rw [FGLaw.coe_adicValue]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- A zero-constant formal-group homomorphism evaluates to zero at zero. -/
theorem adicValue_zero (f : Hom F G) : f.adicValue hI 0 = 0 := by
  apply Subtype.ext
  rw [coe_adic_value₂]
  change eval₂ (RingHom.id R) (fun _ ↦ (0 : R)) f.toSeries = 0
  rw [eval₂_zero_eq_constantCoeff hI f.toSeries]
  exact f.constant_coeff_zero

/-- Evaluation of the defining formal homomorphism identity. -/
theorem adicValue_law (f : Hom F G) (x y : I) :
    f.adicValue hI (F.adicValue hI x y) =
      G.adicValue hI (f.adicValue hI x) (f.adicValue hI y) := by
  apply Subtype.ext
  rw [coe_law_adic₂ hI G
      (f.adicValue hI x) (f.adicValue hI y),
    coe_adic_value₂ hI f (F.adicValue hI x y),
    coe_law_adic₂ hI F x y,
    coe_adic_value₂ hI f x,
    coe_adic_value₂ hI f y]
  let a : Fin 2 → R := Fin.cases (x : R) (fun _ ↦ (y : R))
  have ha : ∀ i, a i ∈ I := by
    intro i
    exact Fin.cases x.2 (fun _ ↦ y.2) i
  have h := congrArg (eval₂ (RingHom.id R) a) f.map_law_binary
  rw [eval₂_compose_adic hI f.toSeries
      (substitute F.law binaryX binaryY)
      (by
        apply constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero (fun i ↦
            Fin.cases (by simp [binaryX]) (fun _ ↦ by simp [binaryY]) i))
        · intro i
          exact Fin.cases (by simp [binaryX]) (fun _ ↦ by simp [binaryY]) i
        · exact law_constant_coeff F)
      a ha,
    eval₂_substitute_adic hI F.law binaryX binaryY
      (by simp [binaryX]) (by simp [binaryY]) a ha,
    eval₂_substitute_adic hI G.law
      (compose f.toSeries binaryX) (compose f.toSeries binaryY)
      (constant_coeff_compose f.toSeries f.constant_coeff_zero
        binaryX (by simp [binaryX]))
      (constant_coeff_compose f.toSeries f.constant_coeff_zero
        binaryY (by simp [binaryY])) a ha,
    eval₂_compose_adic hI f.toSeries binaryX
      (by simp [binaryX]) a ha,
    eval₂_compose_adic hI f.toSeries binaryY
      (by simp [binaryY]) a ha] at h
  simpa [binaryX, binaryY, a] using h

/-- The additive homomorphism on adic points induced by a formal-group
homomorphism. -/
noncomputable def adicMap (f : Hom F G) :
    APts hI F →+ APts hI G where
  toFun x := APts.ofIdeal hI G
    (f.adicValue hI (APts.toIdeal hI F x))
  map_zero' := by
    apply APts.ext hI G
    simp only [APts.to_of_ideal, APts.toIdeal_zero]
    exact adicValue_zero hI f
  map_add' x y := by
    apply APts.ext hI G
    simp only [APts.to_of_ideal, APts.toIdeal_add]
    exact adicValue_law hI f (APts.toIdeal hI F x)
      (APts.toIdeal hI F y)

@[simp]
theorem adicMap_apply (f : Hom F G) (x : APts hI F) :
    APts.toIdeal hI G (f.adicMap hI x) =
      f.adicValue hI (APts.toIdeal hI F x) := rfl

/-- Evaluating the identity formal homomorphism gives the identity additive
homomorphism. -/
@[simp]
theorem adicMap_id : (Hom.id F).adicMap hI = AddMonoidHom.id _ := by
  ext x
  simp [adicMap, coe_adic_value₂, unaryX]

/-- Evaluation respects composition of formal-group homomorphisms. -/
@[simp]
theorem adicMap_comp (g : Hom G H) (f : Hom F G) :
    (Hom.comp g f).adicMap hI = (g.adicMap hI).comp (f.adicMap hI) := by
  ext x
  simp only [adicMap_apply, comp_toSeries, coe_adic_value₂]
  let a : Fin 1 → R := fun _ ↦ (APts.toIdeal hI F x : R)
  have ha : ∀ i, a i ∈ I := fun _ ↦ (APts.toIdeal hI F x).2
  have h := eval₂_compose_adic hI g.toSeries f.toSeries
    f.constant_coeff_zero a ha
  simpa [a] using h

end Hom

namespace Iso

variable {I : Ideal R} (hI : IsAdic I) {F G : FGLaw R}

/-- A formal-group isomorphism evaluates to an additive equivalence of the
adic formal groups. -/
noncomputable def adicEquiv (e : Iso F G) :
    APts hI F ≃+ APts hI G where
  toFun := e.hom.adicMap hI
  invFun := e.inv.adicMap hI
  left_inv x := by
    rw [← AddMonoidHom.comp_apply, ← Hom.adicMap_comp]
    rw [e.inv_hom_id, Hom.adicMap_id]
    rfl
  right_inv x := by
    rw [← AddMonoidHom.comp_apply, ← Hom.adicMap_comp]
    rw [e.hom_inv_id, Hom.adicMap_id]
    rfl
  map_add' := (e.hom.adicMap hI).map_add

@[simp]
theorem adicEquiv_apply (e : Iso F G) (x : APts hI F) :
    e.adicEquiv hI x = e.hom.adicMap hI x := rfl

@[simp]
theorem adic_equiv_symm (e : Iso F G) (y : APts hI G) :
    (e.adicEquiv hI).symm y = e.inv.adicMap hI y := rfl

end Iso

end


end FGLaw

end Towers.CField.FGroups
