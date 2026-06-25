import Mathlib


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Towers
namespace TBluepr

/-- A strictly increasing source map on `ℕ` always lies weakly above the identity. -/
theorem hmr_id_mono
    {source : ℕ → ℕ} (hsource : StrictMono source) (n : ℕ) :
    n ≤ source n := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have hlt : source n < source (n + 1) :=
        hsource (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- Transfer source-index depth bounds to position-indexed depth bounds. -/
theorem hmr_bound_source
    {k : ℕ} {source depth : ℕ → ℕ}
    (hsource : ∀ n, n ≤ source n)
    (hdepth : ∀ n, k + source n ≤ depth n) :
    ∀ n, k + n ≤ depth n := by
  intro n
  exact (Nat.add_le_add_left (hsource n) k).trans (hdepth n)

/-- A strictly increasing source map supplies the position bound needed for depth transfer. -/
theorem hmr_mono_source
    {k : ℕ} {source depth : ℕ → ℕ}
    (hsource : StrictMono source)
    (hdepth : ∀ n, k + source n ≤ depth n) :
    ∀ n, k + n ≤ depth n :=
  hmr_bound_source
    (k := k) (source := source) (depth := depth)
    (fun n => hmr_id_mono hsource n)
    hdepth

/--
Transfer depth bounds along an explicit source-relator identification.

This is the arithmetic core behind selected cut relators: if the relator in
position `n` is the relator coming from source `source n`, and source indices
lie weakly after positions, source-depth bounds imply position-depth bounds.
-/
theorem hmr_bound_relator
    {Rel : Type*} {k : ℕ}
    (depth : Rel → ℕ)
    (cutRelatorAt sourceRelator : ℕ → Rel)
    {source : ℕ → ℕ}
    (hsource : ∀ n, n ≤ source n)
    (hcut : ∀ n, cutRelatorAt n = sourceRelator (source n))
    (hdepth : ∀ i, k + i ≤ depth (sourceRelator i)) :
    ∀ n, k + n ≤ depth (cutRelatorAt n) := by
  intro n
  rw [hcut n]
  exact (Nat.add_le_add_left (hsource n) k).trans (hdepth (source n))

/--
Version of `hmr_bound_relator` where the source-depth bound is
obtained from admissibility-like membership data.
-/
theorem hmr_bound_admissible
    {Rel G : Type*} {k : ℕ}
    (depth : Rel → ℕ)
    (cutRelatorAt sourceRelator : ℕ → Rel)
    (x : ℕ → G)
    (F : ℕ → Set G)
    {source : ℕ → ℕ}
    (hsource : ∀ n, n ≤ source n)
    (hcut : ∀ n, cutRelatorAt n = sourceRelator (source n))
    (hx : ∀ i, x i ∈ F (k + i))
    (hmem_depth :
      ∀ i, x i ∈ F (k + i) → k + i ≤ depth (sourceRelator i)) :
    ∀ n, k + n ≤ depth (cutRelatorAt n) := by
  intro n
  rw [hcut n]
  exact (Nat.add_le_add_left (hsource n) k).trans
    (hmem_depth (source n) (hx (source n)))

end TBluepr

end Towers
