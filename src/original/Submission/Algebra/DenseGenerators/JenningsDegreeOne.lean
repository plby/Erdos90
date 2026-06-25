import Submission.Algebra.DenseGenerators.FirstOrder
import Submission.Group.DenseGenerators.ZassenhausDegreeTwo


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u

/-- The first positive finite Jennings kernel is exactly controlled by the elementary abelian
quotient `Λ / D₂(Λ)`. -/
lemma dense_generators_algebra
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ] [Finite Λ] :
    dGKern p Λ 1 ≤
      zassenhausFiltration p Λ 2 := by
  intro x hx
  rw [dense_algebra_kernel] at hx
  have hxcong :
      dDCongru p Λ 2 x :=
    (dense_generators_subgroup
      (p := p) (Λ := Λ) 2 x).1 hx.2
  let Ω : Type u := zassenhausSelfQuotient p Λ 2
  letI : Group Ω := instSelfQuotient p Λ 2
  letI : IsMulCommutative Ω := by
    dsimp [Ω]
    infer_instance
  letI : CommGroup Ω := by
    dsimp [Ω]
    infer_instance
  letI : Module (ZMod p) (Additive Ω) := by
    dsimp [Ω]
    exact inst_z_self (p := p) Λ
  let q : Λ →* Ω := zassenhausSelf p Λ 2
  have hxqcong :
      dDCongru p Ω 2 (q x) := by
    dsimp [q, Ω]
    exact
      dDCongru.map_zass_selfquot
        (p := p) hxcong
  have hq_one : q x = 1 := by
    exact
      element_sq_comm
        (p := p) (Λ := Ω) (x := q x)
        (by
          simpa [dDCongru] using hxqcong)
  dsimp [q, Ω] at hq_one
  exact (zassenhaus_self_quotient p Λ 2 x).mp hq_one

/-- In degree two, the finite group algebra dimension congruence forces membership in the
second Zassenhaus subgroup. -/
def dense_dimension_upper
    (p : ℕ) [Fact p.Prime] :
    DenseUpperBound.{u} (p := p) 2 := by
  refine
    { finite_group_zassenhaus := ?_ }
  intro Λ _instGroupΛ _instFiniteΛ x hx
  have hD_one : x ∈ zassenhausFiltration p Λ 1 :=
    zassenhaus_filtration_one p Λ (by norm_num) x
  have haug :
      x ∈ denseGeneratorsSubgroup p Λ 2 :=
    (dense_generators_subgroup
      (p := p) (Λ := Λ) 2 x).2 hx
  have hkernel :
      x ∈ dGKern p Λ 1 := by
    exact ⟨hD_one, by simpa using haug⟩
  exact dense_generators_algebra hkernel

end Submission
