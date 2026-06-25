import Towers.Group.FiniteQuotientTower.Completeness


noncomputable section

namespace Towers
namespace Group

universe u v

namespace cSQuotie

variable
    (S : cSQuotie.{u})
    {H : Type v}
    [Group H]

/--
An inverse-limit thread is trivial as soon as every finite-level coordinate is
trivial.
-/
lemma inverse_limit_projections
    {x : inverseLimit S}
    (hx : ∀ n : ℕ, inverseLimitProjection S n x = 1) :
    x = 1 := by
  apply Subtype.ext
  funext n
  exact hx n

/--
The kernels of all finite-level inverse-limit projections have trivial
intersection.
-/
lemma i_inf_kernels :
    (⨅ n : ℕ, (inverseLimitProjection S n).ker) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    apply S.inverse_limit_projections
    intro n
    exact MonoidHom.mem_ker.mp (Subgroup.mem_iInf.mp hx n)
  · exact bot_le

/--
A subgroup of an inverse limit is trivial exactly when every finite-level
projection kills it.
-/
lemma limit_projection_kernels
    (K : Subgroup (inverseLimit S)) :
    K = ⊥ ↔ ∀ n : ℕ, K ≤ (inverseLimitProjection S n).ker := by
  constructor
  · intro hK n
    rw [hK]
    exact bot_le
  · intro hK
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply S.inverse_limit_projections
      intro n
      exact MonoidHom.mem_ker.mp (hK n hx)
    · exact bot_le

/--
A homomorphism out of an inverse limit is injective exactly when every
finite-level projection kills its kernel.
-/
lemma injective_projection_kernels
    (φ : inverseLimit S →* H) :
    Function.Injective φ ↔
      ∀ n : ℕ, φ.ker ≤ (inverseLimitProjection S n).ker := by
  constructor
  · intro hInjective
    have hker : φ.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff φ).mpr hInjective
    exact (S.limit_projection_kernels φ.ker).mp hker
  · intro hkernel
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    exact (S.limit_projection_kernels φ.ker).mpr hkernel

/--
If a homomorphism out of an inverse limit identifies two threads, injectivity is
equivalent to finite-level coordinates still distinguishing those threads.
-/
lemma injective_projections
    (φ : inverseLimit S →* H) :
    Function.Injective φ ↔
      ∀ x y : inverseLimit S, φ x = φ y →
        ∀ n : ℕ, inverseLimitProjection S n x = inverseLimitProjection S n y := by
  constructor
  · intro hInjective x y hxy n
    rw [hInjective hxy]
  · intro hcoordinates x y hxy
    apply Subtype.ext
    funext n
    exact hcoordinates x y hxy n

end cSQuotie

end Group
end Towers
