import Towers.Algebra.Structures

namespace Towers
namespace Group

universe u v w

/-- A compatible inverse system of finite quotients, abstractly packaged. -/
structure cSQuotie where
  obj : ℕ → Type u
  [group_obj : ∀ n, Group (obj n)]
  [finite_obj : ∀ n, Finite (obj n)]
  map : ∀ {m n : ℕ}, m ≤ n → obj n →* obj m
  map_surjective : ∀ {m n : ℕ} (h : m ≤ n), Function.Surjective (map h)
  map_id : ∀ n, map (Nat.le_refl n) = MonoidHom.id (obj n)
  map_comp : ∀ {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n),
    (map hkm).comp (map hmn) = map (Nat.le_trans hkm hmn)

attribute [instance] cSQuotie.group_obj
attribute [instance] cSQuotie.finite_obj

/-- Named surjectivity accessor for maps in a compatible finite-quotient system. -/
theorem cSQuotie.map_surj
    (S : cSQuotie.{u}) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (S.map h) :=
  S.map_surjective h

/-- Named identity law for maps in a compatible finite-quotient system. -/
theorem cSQuotie.map_id_hom
    (S : cSQuotie.{u}) (n : ℕ) :
    S.map (Nat.le_refl n) = MonoidHom.id (S.obj n) :=
  S.map_id n



@[simp] theorem cSQuotie.map_id_apply
    (S : cSQuotie.{u}) (n : ℕ) (x : S.obj n) :
    S.map (Nat.le_refl n) x = x := by
  have h := S.map_id n
  exact congrArg (fun f : S.obj n →* S.obj n => f x) h

theorem cSQuotie.map_comp_apply
    (S : cSQuotie.{u}) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) (x : S.obj n) :
    S.map hkm (S.map hmn x) = S.map (Nat.le_trans hkm hmn) x := by
  have h := S.map_comp hkm hmn
  exact congrArg (fun f : S.obj n →* S.obj k => f x) h

/-- Package a filtration term as a normal subgroup. -/
def filtrationNormalTerm {G : Type u} [Group G] (F : DFilt G) (n : ℕ) :
    nSubgro G where
  carrier := F n
  normal' := F.normal' n

/-- The finite quotient inverse system associated to a descending filtration. -/
noncomputable def cSQuotie.ofFiltration {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n))) :
    cSQuotie.{u} where
  obj := fun n => quotientGroup (filtrationNormalTerm F n)
  group_obj := fun n => inferInstance
  finite_obj := hfin
  map := fun {m n} h =>
    quotientMapLE (filtrationNormalTerm F n) (filtrationNormalTerm F m)
      (DFilt.mono_membership F h)
  map_surjective := fun {m n} h =>
    of_le_surjective (filtrationNormalTerm F n) (filtrationNormalTerm F m)
      (DFilt.mono_membership F h)
  map_id := by
    intro n
    ext x
    simp [quotientMapLE, nSubgro.projection]
  map_comp := by
    intro k m n hkm hmn
    ext x
    simp [quotientMapLE, nSubgro.projection]


/-- Coherent threads form a subgroup of the product of the finite quotient groups. -/
def inverseLimitSubgroup (S : cSQuotie.{u}) :
    Subgroup ((n : ℕ) → S.obj n) where
  carrier := {x | ∀ {m n : ℕ} (h : m ≤ n), S.map h (x n) = x m}
  one_mem' := by intro m n h; simp
  mul_mem' := by intro x y hx hy m n h; simp [map_mul, hx h, hy h]
  inv_mem' := by intro x hx m n h; simp [map_inv, hx h]

/-- The inverse limit of a compatible system, as a bundled subgroup (hence a group). -/
abbrev inverseLimit (S : cSQuotie.{u}) : Type u :=
  inverseLimitSubgroup S

/-- Projection from an inverse limit to one finite level. -/
def inverseLimitProjection (S : cSQuotie.{u}) (n : ℕ) :
    inverseLimit S →* S.obj n where
  toFun x := (x : (k : ℕ) → S.obj k) n
  map_one' := rfl
  map_mul' _ _ := rfl


/-- Coordinates of an inverse-limit point are compatible with transition maps. -/
theorem limit_projection_compat (S : cSQuotie.{u})
    {m n : ℕ} (h : m ≤ n) (x : inverseLimit S) :
    S.map h (inverseLimitProjection S n x) = inverseLimitProjection S m x :=
  x.2 h

@[simp] theorem limit_projection (S : cSQuotie.{u})
    (n : ℕ) (x : inverseLimit S) :
    inverseLimitProjection S n x = (x : (k : ℕ) → S.obj k) n := rfl

@[simp] theorem limit_projection_one (S : cSQuotie.{u})
    (n : ℕ) : inverseLimitProjection S n 1 = 1 := rfl

@[simp] theorem limit_projection_mul (S : cSQuotie.{u})
    (n : ℕ) (x y : inverseLimit S) :
    inverseLimitProjection S n (x * y) =
      inverseLimitProjection S n x * inverseLimitProjection S n y := rfl

@[simp] theorem limit_projection_inv (S : cSQuotie.{u})
    (n : ℕ) (x : inverseLimit S) :
    inverseLimitProjection S n x⁻¹ = (inverseLimitProjection S n x)⁻¹ := rfl

/-- Universal map into an inverse limit from a compatible cone of homomorphisms. -/
def inverseLimitLift {H : Type v} [Group H] (S : cSQuotie.{u})
    (f : ∀ n, H →* S.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.map h).comp (f n) = f m) :
    H →* inverseLimit S where
  toFun x := ⟨fun n => f n x, by
    intro m n h
    change S.map h (f n x) = f m x
    exact DFunLike.congr_fun (hcompat h) x⟩
  map_one' := by
    ext n
    simp
  map_mul' x y := by
    ext n
    simp

/-- Pointwise form of the universal lift into an inverse limit. -/
@[simp] theorem limit_lift {H : Type v} [Group H]
    (S : cSQuotie.{u}) (f : ∀ n, H →* S.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.map h).comp (f n) = f m)
    (x : H) (n : ℕ) :
    inverseLimitProjection S n (inverseLimitLift S f hcompat x) = f n x := rfl

@[simp] theorem limit_projection_lift {H : Type v} [Group H]
    (S : cSQuotie.{u}) (f : ∀ n, H →* S.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.map h).comp (f n) = f m) (n : ℕ) :
    (inverseLimitProjection S n).comp (inverseLimitLift S f hcompat) = f n := by
  ext x
  rfl

/-- Homomorphisms into the inverse limit are determined by all finite-level projections. -/
theorem limit_lift_unique {H : Type v} [Group H]
    (S : cSQuotie.{u}) (f : ∀ n, H →* S.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.map h).comp (f n) = f m)
    (g : H →* inverseLimit S)
    (hg : ∀ n, (inverseLimitProjection S n).comp g = f n) :
    g = inverseLimitLift S f hcompat := by
  ext x n
  exact DFunLike.congr_fun (hg n) x

/-- The canonical map from a group to the inverse limit of its finite filtration quotients. -/
noncomputable def filtrationCompletionMap {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n))) :
    G →* inverseLimit (cSQuotie.ofFiltration F hfin) where
  toFun g := ⟨fun n => QuotientGroup.mk' (F n) g, by
    intro m n h
    have hker : F n ≤ MonoidHom.ker (QuotientGroup.mk' (F m)) := by
      intro x hx
      change QuotientGroup.mk' (F m) x = 1
      exact (QuotientGroup.eq_one_iff (N := F m) x).2 (DFilt.mono_membership F h hx)
    dsimp [cSQuotie.ofFiltration, quotientMapLE,
      nSubgro.projection, filtrationNormalTerm]
    convert (QuotientGroup.lift_mk' (F n) (φ := QuotientGroup.mk' (F m)) hker g) using 1
    ⟩
  map_one' := by
    ext n
    rfl
  map_mul' x y := by
    ext n
    rfl

/-- Its coordinates are the usual quotient maps. -/
theorem filtration_completion_coordinate {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n))) (n : ℕ) :
    (inverseLimitProjection (cSQuotie.ofFiltration F hfin) n).comp
      (filtrationCompletionMap F hfin) = QuotientGroup.mk' (F n) := by
  ext g
  rfl

/-- If the filtration is separated, the completion map has trivial kernel. -/
theorem filtration_ker_bot {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n)))
    (hsep : ∀ g : G, (∀ n, g ∈ F n) → g = 1) :
    MonoidHom.ker (filtrationCompletionMap F hfin) = ⊥ := by
  ext g
  constructor
  · intro hg
    change g = 1
    apply hsep g
    intro n
    have hcoord := congrArg (fun x => inverseLimitProjection
        (cSQuotie.ofFiltration F hfin) n x) hg
    change QuotientGroup.mk' (F n) g = 1 at hcoord
    exact (QuotientGroup.eq_one_iff (N := F n) g).1 hcoord
  · intro hg
    rw [Subgroup.mem_bot] at hg
    simp [hg]


end Group
end Towers

/-!
## Statements migrated from `Towers.Theorems`

These declarations keep their historical `Towers.Theorems` namespace while living
next to the API they describe.
-/

namespace Towers
namespace Theorems

open Towers.Group
open Towers.Algebra

universe u v w x

/-- Compatible finite filtration layers assemble into an inverse system. -/
theorem compatibleLayersSystem {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n))) :
    ∃ S : cSQuotie.{u},
      S = cSQuotie.ofFiltration F hfin
  := by
  exact ⟨cSQuotie.ofFiltration F hfin, rfl⟩
/-- An inverse limit recovers the profinite object from finite layers when the
comparison is complete and separated, not merely coordinatewise surjective. -/
theorem recoversProfiniteLayers {G : Type u} [Group G]
    (S : cSQuotie.{u}) (comparison : G →* inverseLimit S)
    (_hcoordinate : ∀ n, Function.Surjective ((inverseLimitProjection S n).comp comparison))
    (hcomplete : ∀ y : inverseLimit S, ∃ g : G, comparison g = y)
    (hseparated : ∀ g : G, comparison g = 1 → g = 1) :
    Function.Surjective comparison ∧ Function.Injective comparison
  := by
  constructor
  · intro y
    exact hcomplete y
  · intro x y hxy
    apply eq_of_mul_inv_eq_one
    apply hseparated
    rw [map_mul, map_inv, hxy, mul_inv_cancel]

end Theorems
end Towers
