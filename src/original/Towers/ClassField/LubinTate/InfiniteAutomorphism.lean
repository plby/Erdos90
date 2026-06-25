import Towers.ClassField.LubinTate.InfiniteActionIdentity
import Towers.ClassField.LubinTate.InfiniteMulPointwise

/-!
# Automorphisms of the infinite Lubin--Tate extension

Compatible quotient-unit actions on the finite torsion fields assemble into
a genuine action of the base unit group on `K_pi`.
-/

namespace Towers.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

/-- The glued endomorphisms define a multiplicative semiring action of the
base units on `K_pi`.  The group-action law is checked at a finite level
containing the element being acted on. -/
@[implicit_reducible]
noncomputable def infiniteSemiringAction
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit) :
    MulSemiringAction Aˣ (D.infiniteTorsionField K Omega) where
  smul a x := D.infiniteActionHom K Omega orbit hcompat a x
  one_smul x := DFunLike.congr_fun
    (D.infinite_action_alg K Omega orbit hcompat) x
  mul_smul a b x := by
    obtain ⟨n, hn⟩ :=
      (D.infinite_torsion_field K Omega (x : Omega)).1 x.property
    let y : D.torsionLevelField K Omega n := ⟨x, hn⟩
    have hxy : D.torsionLevelInclusion K Omega n y = x := by
      apply Subtype.ext
      rfl
    rw [← hxy]
    exact D.infinite_action_level
      K Omega orbit hcompat a b n y
  smul_zero a := map_zero (D.infiniteActionHom K Omega orbit hcompat a)
  smul_add a x y := map_add
    (D.infiniteActionHom K Omega orbit hcompat a) x y
  smul_one a := map_one (D.infiniteActionHom K Omega orbit hcompat a)
  smul_mul a x y := map_mul
    (D.infiniteActionHom K Omega orbit hcompat a) x y

/-- The infinite unit action commutes with scalar multiplication by the base
field because every glued endomorphism is a `K`-algebra homomorphism. -/
@[implicit_reducible]
noncomputable def infiniteSComm
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit) :
    letI : MulSemiringAction Aˣ (D.infiniteTorsionField K Omega) :=
      D.infiniteSemiringAction K Omega orbit hcompat
    SMulCommClass Aˣ K (D.infiniteTorsionField K Omega) := by
  letI : MulSemiringAction Aˣ (D.infiniteTorsionField K Omega) :=
    D.infiniteSemiringAction K Omega orbit hcompat
  constructor
  intro a k x
  change D.infiniteActionHom K Omega orbit hcompat a (k • x) =
    k • D.infiniteActionHom K Omega orbit hcompat a x
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rw [(D.infiniteActionHom K Omega orbit hcompat a).commutes]

/-- A base unit acts on `K_pi` by a `K`-algebra automorphism. -/
noncomputable def infiniteActionAlg
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) : D.infiniteTorsionField K Omega ≃ₐ[K]
      D.infiniteTorsionField K Omega := by
  letI : MulSemiringAction Aˣ (D.infiniteTorsionField K Omega) :=
    D.infiniteSemiringAction K Omega orbit hcompat
  letI : SMulCommClass Aˣ K (D.infiniteTorsionField K Omega) :=
    D.infiniteSComm K Omega orbit hcompat
  exact MulSemiringAction.toAlgEquiv K
    (D.infiniteTorsionField K Omega) a

/-- The compatible finite quotient-unit actions assemble into the unit
action on Milne's infinite Lubin--Tate extension `K_pi`. -/
noncomputable def infiniteUnitAction
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit) :
    Aˣ →* (D.infiniteTorsionField K Omega ≃ₐ[K]
      D.infiniteTorsionField K Omega) := by
  letI : MulSemiringAction Aˣ (D.infiniteTorsionField K Omega) :=
    D.infiniteSemiringAction K Omega orbit hcompat
  letI : SMulCommClass Aˣ K (D.infiniteTorsionField K Omega) :=
    D.infiniteSComm K Omega orbit hcompat
  exact MulSemiringAction.toAlgAut (G := Aˣ) K
    (D.infiniteTorsionField K Omega)

@[simp]
theorem infinite_unit_action
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) (x : D.infiniteTorsionField K Omega) :
    D.infiniteUnitAction K Omega orbit hcompat a x =
      D.infiniteActionHom K Omega orbit hcompat a x :=
  rfl

@[simp]
theorem infinite_action_hom
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n))
    (hcompat : CompatibleTorsionActions D orbit)
    (a : Aˣ) :
    (D.infiniteUnitAction K Omega orbit hcompat a).toAlgHom =
      D.infiniteActionHom K Omega orbit hcompat a := by
  ext x
  rfl

end LTDatum

end

end Towers.CField.LTate
