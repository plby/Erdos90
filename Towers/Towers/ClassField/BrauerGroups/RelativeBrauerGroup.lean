import Towers.ClassField.BrauerGroups.BrauerTrivialClass
import Towers.ClassField.BrauerGroups.IsSplitBy

/-!
# Chapter IV, Section 2: the relative Brauer group and splitting

The kernel definition of `Br(K/k)` agrees with Milne's description as the
classes represented by central simple algebras split by `K`.
-/

namespace Towers.CField.BGroups

noncomputable section

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A central simple algebra belongs to `Br(K/k)` exactly when scalar
extension to `K` is a full matrix algebra. -/
theorem brauer_relative_split
    (A : CSA.{u, u} k) :
    brauerClass k A ∈ relativeBrauerGroup k K ↔ ISBy k K A := by
  rw [relative_brauer_group]
  change brauerClass K (scalarExtensionCSA k K A) = 1 ↔ ISBy k K A
  rw [brauer_alg_matrix]
  constructor
  · rintro ⟨n, hn, e⟩
    exact ⟨n, ⟨hn⟩, e⟩
  · rintro ⟨n, hn, e⟩
    exact ⟨n, NeZero.ne n, e⟩

end

end Towers.CField.BGroups
