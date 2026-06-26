import Submission.ClassField.FormalGroups.FirstVariable

/-!
# Constructing a formal group law from its law axioms

Exercise 2.21 constructs the formal inverse from the identity axiom.  This
file packages that construction into the `FGLaw` structure, bridging
between the unit-indexed `PowerSeries` used by the exercise and the
`Fin 1`-indexed unary series used by the structure.
-/

namespace Submission.CField.FGroups

open scoped PowerSeries
open scoped MvPowerSeries.WithPiTopology
open MvPowerSeries

noncomputable section

namespace FLConstr

variable {R : Type*} [CommRing R]

/-- The canonical equivalence between the variable of `PowerSeries` and the
single variable of `UnarySeries`. -/
def unitFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := (Fin.eq_zero i).symm

private theorem kill_compl_variable [TopologicalSpace R] :
    Continuous (killCompl (R := R) FGSeries.secondVariable) := by
  apply continuous_pi
  intro d
  change Continuous (fun p : BinarySeries R ↦
    coeff (Finsupp.embDomain FGSeries.secondVariable d) p)
  exact MvPowerSeries.WithPiTopology.continuous_coeff R
    (Finsupp.embDomain FGSeries.secondVariable d)

private theorem kill_compl_substitute (F : BinarySeries R) :
    killCompl (R := R) FGSeries.secondVariable F =
      FGLaw.substitute F 0 FGLaw.unaryX := by
  letI : UniformSpace R := ⊥
  have hcontinuous : Continuous (killCompl (R := R) FGSeries.secondVariable) :=
    kill_compl_variable
  have hunique := aeval_unique
    (R := R) (S := UnarySeries R)
    (ε := killCompl (R := R) FGSeries.secondVariable) hcontinuous
  have hx : (fun i : Fin 2 ↦
      (killCompl (R := R) FGSeries.secondVariable).toRingHom (X i)) =
      Fin.cases (0 : UnarySeries R) (fun _ ↦ FGLaw.unaryX) := by
    funext i
    fin_cases i
    · apply killCompl_X_eq_zero
      simp [FGSeries.secondVariable]
    · simpa [FGLaw.unaryX, FGSeries.secondVariable] using
        (killCompl_X (R := R) (e := FGSeries.secondVariable) (0 : Fin 1))
  rw [← AlgHom.congr_fun hunique F]
  rw [coe_aeval, ← subst_eq_eval₂]
  rw [hx]
  rfl

private theorem continuous_rename_fin [TopologicalSpace R] [ContinuousAdd R] :
    Continuous (rename (R := R) unitFinOne) := by
  apply continuous_pi
  intro d
  change Continuous (fun p : PowerSeries R ↦
    coeff d (rename (R := R) unitFinOne p))
  simp_rw [coeff_rename]
  apply continuous_finsetSum
  intro x _
  exact MvPowerSeries.WithPiTopology.continuous_coeff R x

private theorem rename_applySeries (F : BinarySeries R) (g : PowerSeries R)
    (hg0 : PowerSeries.constantCoeff g = 0) :
    rename (R := R) unitFinOne (FGSeries.applySeries F g) =
      FGLaw.substitute F FGLaw.unaryX
        (rename (R := R) unitFinOne g) := by
  let a : Fin 2 → PowerSeries R :=
    Fin.cases PowerSeries.X (fun _ ↦ g)
  let b : Fin 2 → UnarySeries R :=
    Fin.cases FGLaw.unaryX
      (fun _ ↦ rename (R := R) unitFinOne g)
  have ha0 : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    fin_cases i
    · exact constantCoeff_X ()
    · exact hg0
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hb0 : ∀ i, constantCoeff (b i) = 0 := by
    intro i
    fin_cases i
    · exact constantCoeff_X 0
    · change constantCoeff (rename (R := R) unitFinOne g) = 0
      rw [constantCoeff_rename]
      exact hg0
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero hb0
  letI : UniformSpace R := ⊥
  have hrename : Continuous (rename (R := R) unitFinOne) :=
    continuous_rename_fin
  have hcomp := comp_subst_apply (R := R) ha hrename F
  change rename (R := R) unitFinOne (subst a F) = subst b F
  rw [hcomp]
  rw [← substAlgHom_apply hb, substAlgHom_eq_aeval hb]
  congr 2
  funext i
  fin_cases i
  · change rename (R := R) unitFinOne PowerSeries.X =
      FGLaw.unaryX
    rw [PowerSeries.X, rename_X]
    rfl
  · rfl

/-- The inverse series supplied by Exercise 2.21, renamed to the unary-series
index convention used by `FGLaw`. -/
def inverseSeries (F : BinarySeries R) : UnarySeries R :=
  rename unitFinOne (FGSeries.inverseSeries F)

theorem inverse_constant_coeff {F : BinarySeries R}
    (hleft : FGLaw.substitute F 0 FGLaw.unaryX =
      FGLaw.unaryX) :
    constantCoeff (inverseSeries F) = 0 := by
  rw [inverseSeries, constantCoeff_rename]
  apply FGSeries.inverse_constant_coeff
  rwa [kill_compl_substitute]

theorem inverseSeries_law {F : BinarySeries R}
    (hleft : FGLaw.substitute F 0 FGLaw.unaryX =
      FGLaw.unaryX) :
    FGLaw.substitute F FGLaw.unaryX (inverseSeries F) = 0 := by
  rw [inverseSeries, ← rename_applySeries _ _
    (FGSeries.inverse_constant_coeff
      (by rwa [kill_compl_substitute]))]
  rw [FGSeries.inverseSeries_law]
  · simp
  · rwa [kill_compl_substitute]

theorem inverseSeries_unique {F : BinarySeries R}
    (hleft : FGLaw.substitute F 0 FGLaw.unaryX =
      FGLaw.unaryX)
    (i : UnarySeries R) (hi0 : constantCoeff i = 0)
    (hi : FGLaw.substitute F FGLaw.unaryX i = 0) :
    i = inverseSeries F := by
  let g : PowerSeries R := rename unitFinOne.symm i
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    simpa only [g, PowerSeries.constantCoeff, constantCoeff_rename] using hi0
  have hrename : rename (R := R) unitFinOne g = i := by
    simp [g]
  have hg : FGSeries.applySeries F g = 0 := by
    apply (renameEquiv R unitFinOne).injective
    change rename (R := R) unitFinOne (FGSeries.applySeries F g) =
      rename (R := R) unitFinOne 0
    rw [rename_applySeries _ _ hg0, hrename, hi]
    simp
  have hginv : g = FGSeries.inverseSeries F := by
    apply FGSeries.inverseSeries_unique
    · rwa [kill_compl_substitute]
    · exact hg0
    · exact hg
  rw [inverseSeries, ← hginv, hrename]

/-- Package a commutative, associative binary formal law with two-sided
identity into `FGLaw`.  The inverse data and its uniqueness are
constructed, rather than assumed, by Exercise 2.21. -/
def ofLaw (F : BinarySeries R)
    (left_identity : FGLaw.substitute F 0 FGLaw.unaryX =
      FGLaw.unaryX)
    (right_identity : FGLaw.substitute F FGLaw.unaryX 0 =
      FGLaw.unaryX)
    (associativity :
      FGLaw.substitute F FGLaw.ternaryX
          (FGLaw.substitute F FGLaw.ternaryY FGLaw.ternaryZ) =
        FGLaw.substitute F
          (FGLaw.substitute F FGLaw.ternaryX FGLaw.ternaryY)
          FGLaw.ternaryZ)
    (commutativity :
      FGLaw.substitute F FGLaw.binaryX FGLaw.binaryY =
        FGLaw.substitute F FGLaw.binaryY FGLaw.binaryX) :
    FGLaw R where
  law := F
  inverse := inverseSeries F
  left_identity := left_identity
  right_identity := right_identity
  associativity := associativity
  commutativity := commutativity
  inverse_constantCoeff := inverse_constant_coeff left_identity
  inverse_law := inverseSeries_law left_identity
  inverse_unique := inverseSeries_unique left_identity

@[simp]
theorem ofLaw_law (F : BinarySeries R) (hleft) (hright) (hassoc) (hcomm) :
    (ofLaw F hleft hright hassoc hcomm).law = F := rfl

@[simp]
theorem ofLaw_inverse (F : BinarySeries R) (hleft) (hright) (hassoc) (hcomm) :
    (ofLaw F hleft hright hassoc hcomm).inverse = inverseSeries F := rfl

/-- Formal group laws in the local structure are determined by their binary
law; the stored inverse is uniquely characterized by that law. -/
theorem ext_law {F G : FGLaw R} (h : F.law = G.law) : F = G := by
  cases F with
  | mk law inverse left right assoc comm inv0 invLaw invUnique =>
      cases G with
      | mk law' inverse' left' right' assoc' comm' inv0' invLaw' invUnique' =>
          dsimp at h
          subst law'
          have hinverse : inverse = inverse' :=
            invUnique' inverse inv0 invLaw
          subst inverse'
          rfl

end FLConstr

end

end Submission.CField.FGroups
