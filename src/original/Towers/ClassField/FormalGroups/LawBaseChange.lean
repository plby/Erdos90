import Towers.ClassField.FormalGroups.GroupLawConstructor
import Towers.ClassField.FormalGroups.Homomorphisms
import Towers.ClassField.FormalGroups.HomGroupRing

/-!
# Base change of one-dimensional formal group laws

A formal group law over `R` may be evaluated in a complete adic `R`-algebra
only after its coefficients have been transported to that algebra.  This
file constructs that coefficient base change and proves that the formal law
identities are preserved.  It is the relative-algebra layer needed for the
Lubin--Tate torsion fields in Chapter I, Theorem 3.6.
-/

namespace Towers.CField.FGroups

noncomputable section

open MvPowerSeries

namespace FGLaw

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem substitute_constant_zero
    (F : FGLaw R) {sigma : Type*}
    (x y : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (substitute F.law x y) = 0 := by
  apply constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero
      (fun i ↦ Fin.cases hx (fun _ ↦ hy) i))
    (fun i ↦ Fin.cases hx (fun _ ↦ hy) i)
  exact law_constant_coeff F

/-- Mapping coefficients commutes with substitution when the substituted
series have zero constant coefficient. -/
theorem substitute_constant_coeff
    (rho : R →+* S) {sigma : Type*}
    (P : BinarySeries R) (x y : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    MvPowerSeries.map rho (substitute P x y) =
      substitute (MvPowerSeries.map rho P)
        (MvPowerSeries.map rho x) (MvPowerSeries.map rho y) := by
  let a : Fin 2 → MvPowerSeries sigma R := Fin.cases x (fun _ ↦ y)
  have ha0 : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    exact Fin.cases hx (fun _ ↦ hy) i
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [substitute, substitute, MvPowerSeries.map_subst ha]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Mapping coefficients commutes with composition by a zero-constant unary
series. -/
theorem compose_constant_coeff
    (rho : R →+* S) {sigma : Type*}
    (f : UnarySeries R) (x : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) :
    MvPowerSeries.map rho (compose f x) =
      compose (MvPowerSeries.map rho f) (MvPowerSeries.map rho x) := by
  have hxSubst : HasSubst (fun _ : Fin 1 ↦ x) :=
    hasSubst_of_constantCoeff_zero (fun _ ↦ hx)
  rw [compose, compose, MvPowerSeries.map_subst hxSubst]

/-- Substituting the two coordinate variables into a binary series is the
identity substitution. -/
theorem substitute_binary_y (P : BinarySeries R) :
    substitute P binaryX binaryY = P := by
  have hcoordinates :
      (Fin.cases binaryX (fun _ ↦ binaryY) : Fin 2 → BinarySeries R) =
        MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [substitute, hcoordinates]
  exact congrFun (MvPowerSeries.subst_self (R := R)) P

/-- Coefficient base change of a one-dimensional commutative formal group
law. -/
def map (rho : R →+* S) (F : FGLaw R) : FGLaw S :=
  FLConstr.ofLaw (MvPowerSeries.map rho F.law)
    (by
      have h := congrArg (MvPowerSeries.map rho) F.left_identity
      rw [substitute_constant_coeff rho F.law 0 unaryX
        (by simp) (by simp [unaryX])] at h
      simpa [unaryX] using h)
    (by
      have h := congrArg (MvPowerSeries.map rho) F.right_identity
      rw [substitute_constant_coeff rho F.law unaryX 0
        (by simp [unaryX]) (by simp)] at h
      simpa [unaryX] using h)
    (by
      have hyz0 :
          constantCoeff (substitute F.law ternaryY ternaryZ) = 0 :=
        substitute_constant_zero F ternaryY ternaryZ
          (by simp [ternaryY]) (by simp [ternaryZ])
      have hxy0 :
          constantCoeff (substitute F.law ternaryX ternaryY) = 0 :=
        substitute_constant_zero F ternaryX ternaryY
          (by simp [ternaryX]) (by simp [ternaryY])
      have h := congrArg (MvPowerSeries.map rho) F.associativity
      rw [substitute_constant_coeff rho F.law ternaryX
          (substitute F.law ternaryY ternaryZ)
          (by simp [ternaryX]) hyz0,
        substitute_constant_coeff rho F.law ternaryY ternaryZ
          (by simp [ternaryY]) (by simp [ternaryZ]),
        substitute_constant_coeff rho F.law
          (substitute F.law ternaryX ternaryY) ternaryZ hxy0
          (by simp [ternaryZ]),
        substitute_constant_coeff rho F.law ternaryX ternaryY
          (by simp [ternaryX]) (by simp [ternaryY])] at h
      simpa [ternaryX, ternaryY, ternaryZ] using h)
    (by
      have h := congrArg (MvPowerSeries.map rho) F.commutativity
      rw [substitute_constant_coeff rho F.law binaryX binaryY
          (by simp [binaryX]) (by simp [binaryY]),
        substitute_constant_coeff rho F.law binaryY binaryX
          (by simp [binaryY]) (by simp [binaryX])] at h
      simpa [binaryX, binaryY] using h)

@[simp]
theorem map_law (rho : R →+* S) (F : FGLaw R) :
    (F.map rho).law = MvPowerSeries.map rho F.law := rfl

@[simp]
theorem map_id (F : FGLaw R) : F.map (RingHom.id R) = F := by
  apply FLConstr.ext_law
  simp

theorem map_comp {T : Type*} [CommRing T]
    (tau : S →+* T) (rho : R →+* S) (F : FGLaw R) :
    (F.map rho).map tau = F.map (tau.comp rho) := by
  apply FLConstr.ext_law
  simp

namespace Hom

variable {F G : FGLaw R}

/-- A zero-constant unary series satisfying the literal two-variable formal
group identity determines a homomorphism. -/
def lawBinary (h : UnarySeries R)
    (hzero : constantCoeff h = 0)
    (hbinary :
      compose h (substitute F.law binaryX binaryY) =
        substitute G.law (compose h binaryX) (compose h binaryY)) :
    Hom F G where
  toSeries := h
  constant_coeff_zero := hzero
  map_law {sigma} x y hx hy := by
    let z : Fin 2 → MvPowerSeries sigma R := Fin.cases x (fun _ ↦ y)
    have hz : HasSubst z := hasSubst_of_constantCoeff_zero (by
      intro i
      exact Fin.cases hx (fun _ ↦ hy) i)
    have hlawF0 : constantCoeff F.law = 0 := law_constant_coeff F
    have hconstLawF : HasSubst (fun _ : Fin 1 ↦ F.law) :=
      hasSubst_of_constantCoeff_zero (fun _ ↦ hlawF0)
    let w : Fin 2 → BinarySeries R :=
      Fin.cases (compose h binaryX) (fun _ ↦ compose h binaryY)
    have hw0 : ∀ i, constantCoeff (w i) = 0 := by
      intro i
      refine Fin.cases ?_ (fun _ ↦ ?_) i
      · exact constant_coeff_compose h hzero binaryX
          (by simp [binaryX])
      · exact constant_coeff_compose h hzero binaryY
          (by simp [binaryY])
    have hw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    change subst (fun _ : Fin 1 ↦ subst z F.law) h =
      subst (Fin.cases (subst (fun _ : Fin 1 ↦ x) h)
        (fun _ ↦ subst (fun _ : Fin 1 ↦ y) h)) G.law
    calc
      subst (fun _ : Fin 1 ↦ subst z F.law) h =
          subst z (subst (fun _ : Fin 1 ↦ F.law) h) :=
        (MvPowerSeries.subst_comp_subst_apply hconstLawF hz h).symm
      _ = subst z (subst w G.law) := by
        apply congrArg (subst z)
        rw [substitute_binary_y] at hbinary
        simpa [compose, substitute, w] using hbinary
      _ = subst (fun i ↦ subst z (w i)) G.law :=
        MvPowerSeries.subst_comp_subst_apply hw hz G.law
      _ = subst (Fin.cases (subst (fun _ : Fin 1 ↦ x) h)
          (fun _ ↦ subst (fun _ : Fin 1 ↦ y) h)) G.law := by
        congr 1
        funext i
        refine Fin.cases ?_ (fun _ ↦ ?_) i
        · change subst z (subst (fun _ : Fin 1 ↦ binaryX) h) = _
          rw [MvPowerSeries.subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero
              (fun _ : Fin 1 ↦ by simp [binaryX])) hz h]
          congr 1
          funext k
          rw [binaryX, subst_X hz]
          rfl
        · change subst z (subst (fun _ : Fin 1 ↦ binaryY) h) = _
          rw [MvPowerSeries.subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero
              (fun _ : Fin 1 ↦ by simp [binaryY])) hz h]
          congr 1
          funext k
          rw [binaryY, subst_X hz]
          rfl

/-- Coefficient base change of a formal-group homomorphism. -/
def map (rho : R →+* S) (f : Hom F G) :
    Hom (F.map rho) (G.map rho) := by
  apply lawBinary (MvPowerSeries.map rho f.toSeries)
  · simpa using congrArg rho f.constant_coeff_zero
  · have hFxy0 :
        constantCoeff (substitute F.law binaryX binaryY) = 0 :=
      substitute_constant_zero F binaryX binaryY
        (by simp [binaryX]) (by simp [binaryY])
    have hfx0 : constantCoeff (compose f.toSeries binaryX) = 0 :=
      constant_coeff_compose f.toSeries f.constant_coeff_zero
        binaryX (by simp [binaryX])
    have hfy0 : constantCoeff (compose f.toSeries binaryY) = 0 :=
      constant_coeff_compose f.toSeries f.constant_coeff_zero
        binaryY (by simp [binaryY])
    have h := congrArg (MvPowerSeries.map rho) f.map_law_binary
    rw [compose_constant_coeff rho f.toSeries
          (substitute F.law binaryX binaryY) hFxy0,
      substitute_constant_coeff rho F.law binaryX binaryY
        (by simp [binaryX]) (by simp [binaryY]),
      substitute_constant_coeff rho G.law
        (compose f.toSeries binaryX) (compose f.toSeries binaryY) hfx0 hfy0,
      compose_constant_coeff rho f.toSeries binaryX
        (by simp [binaryX]),
      compose_constant_coeff rho f.toSeries binaryY
        (by simp [binaryY])] at h
    simpa [binaryX, binaryY] using h

@[simp]
theorem map_toSeries (rho : R →+* S) (f : Hom F G) :
    (f.map rho).toSeries = MvPowerSeries.map rho f.toSeries := rfl

/-- Base change is a ring homomorphism on formal endomorphism rings. -/
def endRingMap (rho : R →+* S) (F : FGLaw R) :
    Hom F F →+* Hom (F.map rho) (F.map rho) where
  toFun f := f.map rho
  map_zero' := by
    apply Hom.ext
    simp
  map_one' := by
    apply Hom.ext
    simp [unaryX]
  map_add' f g := by
    apply Hom.ext
    change MvPowerSeries.map rho
        (substitute F.law f.toSeries g.toSeries) =
      substitute (MvPowerSeries.map rho F.law)
        (MvPowerSeries.map rho f.toSeries)
        (MvPowerSeries.map rho g.toSeries)
    exact substitute_constant_coeff rho F.law
      f.toSeries g.toSeries f.constant_coeff_zero
        g.constant_coeff_zero
  map_mul' f g := by
    apply Hom.ext
    change MvPowerSeries.map rho (compose f.toSeries g.toSeries) =
      compose (MvPowerSeries.map rho f.toSeries)
        (MvPowerSeries.map rho g.toSeries)
    exact compose_constant_coeff rho f.toSeries g.toSeries
      g.constant_coeff_zero

@[simp]
theorem end_ring (rho : R →+* S) (F : FGLaw R)
    (f : Hom F F) : endRingMap rho F f = f.map rho := rfl

end Hom

end FGLaw

end

end Towers.CField.FGroups
