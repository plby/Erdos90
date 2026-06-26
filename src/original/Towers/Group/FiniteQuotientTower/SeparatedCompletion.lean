import Towers.Group.FiniteQuotientTower.AmbientSeparation
import Towers.Group.FiniteQuotientTower.Completeness
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Lemmas


open scoped Topology

noncomputable section

namespace Towers
namespace Group

universe u v

namespace tSQuotie

variable
    (S : tSQuotie.{u})
    {H : Type v}
    [Group H]
    [TopologicalSpace H]

omit [TopologicalSpace H] in
/--
The kernel of an inverse-limit lift is exactly the subgroup invisible to every
finite-level coordinate of the compatible cone.
-/
lemma inverse_limit_ambient
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m) :
    (inverseLimitLift S.toSystem f hcompat).ker =
      S.toSystem.ambientKernel f := by
  ext x
  constructor
  · intro hx
    rw [S.toSystem.mem_ambient_iff f x]
    intro n
    have hcoordinate := congrArg
      (fun φ : H →* S.toSystem.obj n => φ x)
      (limit_projection_lift S.toSystem f hcompat n)
    change inverseLimitProjection S.toSystem n
        (inverseLimitLift S.toSystem f hcompat x) =
      f n x at hcoordinate
    calc
      f n x = inverseLimitProjection S.toSystem n
          (inverseLimitLift S.toSystem f hcompat x) := hcoordinate.symm
      _ = inverseLimitProjection S.toSystem n 1 := by
        rw [MonoidHom.mem_ker.mp hx]
      _ = 1 := map_one _
  · intro hx
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    funext n
    exact (S.toSystem.mem_ambient_iff f x).mp hx n

omit [TopologicalSpace H] in
/--
A compatible finite quotient cone induces an injective inverse-limit lift
exactly when its finite-level coordinates separate the source group.
-/
lemma limit_ambient_bot
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m) :
    Function.Injective (inverseLimitLift S.toSystem f hcompat) ↔
      S.toSystem.ambientKernel f = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff,
    S.inverse_limit_ambient f hcompat]

/--
A separated compatible cone of continuous surjective finite quotients from a
compact source fills the whole inverse limit bijectively.
-/
lemma bijective_ambient_bot
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hkernel : S.toSystem.ambientKernel f = ⊥) :
    Function.Bijective (inverseLimitLift S.toSystem f hcompat) := by
  constructor
  · exact (S.limit_ambient_bot f hcompat).mpr
      hkernel
  · exact S.limit_compact_space f hf hfsurj hcompat

/--
A separated compatible cone of continuous surjective finite quotients from a
compact source reconstructs the source as the inverse limit.
-/
def limitAmbientBot
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hkernel : S.toSystem.ambientKernel f = ⊥) :
    H ≃* inverseLimit S.toSystem :=
  MulEquiv.ofBijective
    (inverseLimitLift S.toSystem f hcompat)
    (S.bijective_ambient_bot
      f hf hfsurj hcompat hkernel)

@[simp]
lemma ambient_bot_monoid
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hkernel : S.toSystem.ambientKernel f = ⊥) :
    (S.limitAmbientBot
      f hf hfsurj hcompat hkernel).toMonoidHom =
        inverseLimitLift S.toSystem f hcompat := rfl

/--
A separated compatible cone of continuous surjective finite quotients from a
compact source reconstructs the source continuously as the inverse limit.
-/
def continuousAmbientBot
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hkernel : S.toSystem.ambientKernel f = ⊥) :
    H ≃ₜ* inverseLimit S.toSystem where
  toMulEquiv :=
    S.limitAmbientBot
      f hf hfsurj hcompat hkernel
  continuous_toFun := S.inverse_lift_continuous f hf hcompat
  continuous_invFun := by
    let e := S.limitAmbientBot
      f hf hfsurj hcompat hkernel
    have hcontinuous :
        Continuous (e : H → inverseLimit S.toSystem) := by
      change Continuous (inverseLimitLift S.toSystem f hcompat)
      exact S.inverse_lift_continuous f hf hcompat
    exact hcontinuous.continuous_symm_of_equiv_compact_to_t2

@[simp]
lemma limit_ambient_monoid
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hkernel : S.toSystem.ambientKernel f = ⊥) :
    (S.continuousAmbientBot
      f hf hfsurj hcompat hkernel).toMulEquiv.toMonoidHom =
        inverseLimitLift S.toSystem f hcompat := rfl

/--
Coordinatewise separation of nonidentity source elements is enough to
reconstruct a compact source continuously as the inverse limit.
-/
def limitSeparatesNontrivial
    [CompactSpace H]
    (f : ∀ n : ℕ, H →* S.toSystem.obj n)
    (hf : ∀ n : ℕ, Continuous (f n))
    (hfsurj : ∀ n : ℕ, Function.Surjective (f n))
    (hcompat :
      ∀ {m n : ℕ} (h : m ≤ n),
        (S.toSystem.map h).comp (f n) = f m)
    (hseparates : ∀ x : H, x ≠ 1 → ∃ n : ℕ, f n x ≠ 1) :
    H ≃ₜ* inverseLimit S.toSystem :=
  S.continuousAmbientBot
    f
    hf
    hfsurj
    hcompat
    ((S.toSystem.ambient_separates_nontrivial f).mpr
      hseparates)

end tSQuotie

end Group
end Towers
