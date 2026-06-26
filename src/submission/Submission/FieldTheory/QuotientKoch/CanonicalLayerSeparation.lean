import Submission.FieldTheory.QuotientKoch.CanonicalDescent
import Submission.Group.FiniteQuotientTower.KernelSeparation


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The desired finite quotient Koch theorem is exactly the statement that the
actual quotient defect is killed by every canonical finite relator quotient
projection.
-/
lemma extra_projection_kernels
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ,
        D.kochLimitExtra ≤
          (Group.inverseLimitProjection
            D.ZassenhausRelatorSystem n).ker := by
  rw [D.theorem_extra_bot]
  exact (Group.cSQuotie.limit_projection_kernels
      D.ZassenhausRelatorSystem
      D.kochLimitExtra)

/--
Equivalently, every canonical coherent finite-layer thread killed in the actual
initial Galois group has trivial image in each canonical finite relator quotient
layer.
-/
lemma threads_have_coordinates
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ y : D.RelatorInverseLimit,
        D.inverseLimitDescent y = 1 →
          ∀ n : ℕ,
            Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n y =
              1 := by
  rw [D.extra_projection_kernels]
  constructor
  · intro hkernel y hy n
    exact MonoidHom.mem_ker.mp (hkernel n (MonoidHom.mem_ker.mpr hy))
  · intro hcoordinates n y hy
    exact MonoidHom.mem_ker.mpr (hcoordinates y (MonoidHom.mem_ker.mp hy) n)

/--
The desired theorem says the actual initial Galois quotient never identifies two
canonical coherent finite-layer threads without every finite relator quotient
coordinate already identifying them.
-/
lemma fibers_have_equal
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ x y : D.RelatorInverseLimit,
        D.inverseLimitDescent x =
            D.inverseLimitDescent y →
          ∀ n : ℕ,
            Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n x =
              Group.inverseLimitProjection
                D.ZassenhausRelatorSystem n y := by
  rw [D.theorem_descent_injective]
  exact Group.cSQuotie.injective_projections
      D.ZassenhausRelatorSystem
      D.inverseLimitDescent

end KRData

end TBluepr
end Submission
