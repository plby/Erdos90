import Submission.Group.Zassenhaus.FiltrationIdentities
import Submission.Group.HallPetresco

open scoped commutatorElement

namespace Submission
namespace Theorems
namespace RJRed

universe u

/-- The prime-power commutator bound follows formally from the additive
commutator law for the explicit Zassenhaus filtration. -/
theorem prime_commutator_filtration
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (hcomm : ∀ r s : ℕ,
      ⁅zassenhausFiltration p Q r, zassenhausFiltration p Q s⁆ ≤
        zassenhausFiltration p Q (r + s))
    {i j a b : ℕ} {x y : Q}
    (hx : x ∈ Subgroup.lowerCentralSeries Q i)
    (hy : y ∈ Subgroup.lowerCentralSeries Q j) :
    ⁅x ^ (p ^ a), y ^ (p ^ b)⁆ ∈
      zassenhausFiltration p Q
        ((i + 1) * p ^ a + (j + 1) * p ^ b) := by
  apply
    (Subgroup.commutator_le.mp
      (hcomm ((i + 1) * p ^ a) ((j + 1) * p ^ b)))
  · exact Subgroup.subset_closure ⟨i, a, x, hx, le_rfl, rfl⟩
  · exact Subgroup.subset_closure ⟨j, b, y, hy, le_rfl, rfl⟩

end RJRed
end Theorems
end Submission
