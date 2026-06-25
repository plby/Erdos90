import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Towers.ClassField.LubinTate.CyclotomicTorsion

/-!
# Class Field Theory, Chapter I, Section 3: roots of unity as a cyclic module

Milne uses exponentiation to regard the `N`th roots of unity as a free
`ZMod N`-module of rank one.  After choosing a primitive root, Mathlib's
equivalence between `ZMod N` and its powers gives the required module
structure and an explicit one-element basis.
-/

namespace Towers.CField.LTate

noncomputable section

/-- A chosen primitive `N`th root identifies the additive group `ZMod N`
with the multiplicative group of all `N`th roots of unity. -/
def zmodAddUnity
    {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    ZMod N ≃+ Additive (rootsOfUnity N R) := by
  let u : Rˣ := (hzeta.isUnit (NeZero.ne N)).unit
  have hu : IsPrimitiveRoot u N := hzeta.isUnit_unit (NeZero.ne N)
  exact hu.zmodEquivZPowers.trans
    (MulEquiv.toAdditive (MulEquiv.subgroupCongr hu.zpowers_eq))

/-- Under the preceding equivalence, a residue class acts as the indicated
power of the chosen primitive root. -/
@[simp]
theorem coe_zmod_unity
    {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) (a : ZMod N) :
    (((Additive.toMul (zmodAddUnity hzeta a) :
        rootsOfUnity N R) : Rˣ) : R) = zeta ^ a.val := by
  let u : Rˣ := (hzeta.isUnit (NeZero.ne N)).unit
  have hu : IsPrimitiveRoot u N := hzeta.isUnit_unit (NeZero.ne N)
  have hpow : hu.zmodEquivZPowers a =
      Additive.ofMul
        (⟨u ^ a.val, a.val, rfl⟩ : Subgroup.zpowers u) := by
    calc
      hu.zmodEquivZPowers a =
          hu.zmodEquivZPowers (a.val : ZMod N) :=
        congrArg hu.zmodEquivZPowers (ZMod.natCast_zmod_val a).symm
      _ = Additive.ofMul
          (⟨u ^ a.val, a.val, rfl⟩ : Subgroup.zpowers u) :=
        hu.zmodEquivZPowers_apply_coe_nat a.val
  simp only [zmodAddUnity, AddEquiv.trans_apply]
  rw [hpow]
  change ((u ^ a.val : Rˣ) : R) = zeta ^ a.val
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec (hzeta.isUnit (NeZero.ne N))]

/-- Transport the regular `ZMod N`-module structure across a chosen primitive
root.  The resulting module is canonically free of rank one relative to that
choice. -/
abbrev rootsUnityModule
    {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    Module (ZMod N) (Additive (rootsOfUnity N R)) :=
  (zmodAddUnity hzeta).symm.module (ZMod N)

/-- The source-facing `ZMod N`-linear equivalence: the roots of unity form
one copy of `ZMod N`. -/
def zmodRootsUnity
    {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    letI := rootsUnityModule hzeta
    ZMod N ≃ₗ[ZMod N] Additive (rootsOfUnity N R) := by
  letI := rootsUnityModule hzeta
  exact ((zmodAddUnity hzeta).symm.linearEquiv (ZMod N)).symm

/-- A one-element basis exhibiting the roots of unity as a free rank-one
`ZMod N`-module. -/
def rootsUnityBasis
    {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    letI := rootsUnityModule hzeta
    Module.Basis Unit (ZMod N) (Additive (rootsOfUnity N R)) := by
  letI := rootsUnityModule hzeta
  exact (Module.Basis.singleton Unit (ZMod N)).map
    (zmodRootsUnity hzeta)

namespace CTorsio

variable {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]

/-- Transport the `ZMod N`-module structure on roots of unity to the
cyclotomic Lubin--Tate torsion type. -/
abbrev module {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    Module (ZMod N) (CTorsio R N) := by
  letI := rootsUnityModule hzeta
  exact (addRootsUnity (R := R) (N := N)).module (ZMod N)

/-- Example 3.2's module isomorphism
`CTorsio R N ≃ ZMod N`, oriented from `ZMod N` to torsion. -/
def zmodLinearEquiv
    {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    letI := module hzeta
    ZMod N ≃ₗ[ZMod N] CTorsio R N := by
  letI := rootsUnityModule hzeta
  letI := module hzeta
  exact (zmodRootsUnity hzeta).trans
    ((addRootsUnity (R := R) (N := N)).linearEquiv (ZMod N)).symm

/-- A one-element basis of cyclotomic Lubin--Tate torsion. -/
def basis {zeta : R} (hzeta : IsPrimitiveRoot zeta N) :
    letI := module hzeta
    Module.Basis Unit (ZMod N) (CTorsio R N) := by
  letI := module hzeta
  exact (Module.Basis.singleton Unit (ZMod N)).map (zmodLinearEquiv hzeta)

end CTorsio

end

end Towers.CField.LTate
