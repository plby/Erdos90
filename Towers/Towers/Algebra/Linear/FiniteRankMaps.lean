import Towers.Algebra.Linear
import Towers.Group.PresentedRelatorDepth


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Towers
namespace TBluepr

/--
The coordinate-space injection promised by a finite-dimensional rank bound.

If `m ≤ finrank K V`, then the standard `m`-dimensional coordinate space embeds
linearly into `V`.  This is one of the basis-selection facts behind the
abstract kernel-covering map used below.
-/
theorem coordinate_space_finrank
    {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    {m : ℕ}
    (hm : m ≤ Module.finrank K V) :
    ∃ ι : (Fin m → K) →ₗ[K] V, Function.Injective ι := by
  classical
  have hrank : (m : Cardinal) ≤ Module.rank K V := by
    rw [← Module.finrank_eq_rank (R := K) (M := V)]
    exact_mod_cast hm
  rcases (Module.le_rank_iff_exists_linearMap
      (R := K) (M := V) (n := m)).mp hrank with
    ⟨ι, hι⟩
  exact ⟨ι, hι⟩

/-- Every finite free vector space is linearly equivalent to its coordinate
space indexed by its `finrank`. -/
theorem nonempty_finrank_space
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [Module.Free K W] [Module.Finite K W] :
    Nonempty (W ≃ₗ[K] (Fin (Module.finrank K W) → K)) := by
  classical
  let m : ℕ := Module.finrank K W
  have hcoord :
      Module.finrank K W = Module.finrank K (Fin m → K) := by
    change Module.finrank K W = Module.finrank K (Fin (Module.finrank K W) → K)
    simp
  exact
    ⟨LinearEquiv.ofFinrankEq
      (R := K) (M := W) (M' := Fin m → K) hcoord⟩

/-- A dimension inequality gives an injection in the opposite direction. -/
theorem linear_injective_finrank
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Free K W] [Module.Finite K W]
    (hdim : Module.finrank K W ≤ Module.finrank K V) :
    ∃ j : W →ₗ[K] V, Function.Injective j := by
  classical
  let m : ℕ := Module.finrank K W
  rcases nonempty_finrank_space (K := K) (W := W) with
    ⟨e⟩
  rcases coordinate_space_finrank
      (K := K) (V := V) (m := m) (by simpa [m] using hdim) with
    ⟨ι, hι⟩
  exact ⟨ι.comp e.toLinearMap, hι.comp e.injective⟩

/-- An injective linear map into a vector space splits to a left inverse. -/
theorem linear_inverse_injective
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (j : W →ₗ[K] V)
    (hj : Function.Injective j) :
    ∃ π : V →ₗ[K] W, π.comp j = LinearMap.id := by
  classical
  have hker : LinearMap.ker j = ⊥ :=
    LinearMap.ker_eq_bot.mpr hj
  rcases j.exists_leftInverse_of_injective hker with
    ⟨π, hπ⟩
  exact ⟨π, hπ⟩

/-- A linear map with a right section is surjective. -/
theorem linear_surjective_inverse
    {K V W : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W]
    (π : V →ₗ[K] W)
    (j : W →ₗ[K] V)
    (hπ : π.comp j = LinearMap.id) :
    Function.Surjective π := by
  intro w
  refine ⟨j w, ?_⟩
  have hpoint :
      (π.comp j) w = (LinearMap.id : W →ₗ[K] W) w := by
    rw [hπ]
  simpa using hpoint

/-- If `W` has dimension at most `V`, then there is a surjective linear map
`V → W`. -/
theorem linear_surjective_finrank
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Free K W] [Module.Finite K W]
    (hdim : Module.finrank K W ≤ Module.finrank K V) :
    ∃ f : V →ₗ[K] W, Function.Surjective f := by
  classical
  rcases linear_injective_finrank
      (K := K) (V := V) (W := W) hdim with
    ⟨j, hj⟩
  rcases linear_inverse_injective
      (K := K) (V := V) (W := W) j hj with
    ⟨π, hπ⟩
  exact ⟨π, linear_surjective_inverse (K := K) π j hπ⟩

/-- A surjection onto a submodule gives a map into the ambient module whose
range contains that submodule. -/
theorem subtype_covers_surjective
    {K G R : Type*} [Semiring K]
    [AddCommMonoid G] [Module K G]
    [AddCommMonoid R] [Module K R]
    (W : Submodule K G)
    (f : R →ₗ[K] W)
    (hf : Function.Surjective f) :
    W ≤ LinearMap.range (W.subtype.comp f) := by
  intro x hx
  rcases hf ⟨x, hx⟩ with ⟨r, hr⟩
  exact ⟨r, congrArg Subtype.val hr⟩

/--
Pure finite-dimensional linear algebra: if a source vector space has dimension
at least the kernel of a linear map, then some linear map from the source has
range containing that kernel.
-/
theorem linear_cover_finrank
    {K G T R : Type*} [Field K]
    [AddCommGroup G] [Module K G] [Module.Free K G] [Module.Finite K G]
    [AddCommGroup T] [Module K T]
    [AddCommGroup R] [Module K R] [Module.Free K R] [Module.Finite K R]
    (β : G →ₗ[K] T)
    (hker_dim :
      Module.finrank K (LinearMap.ker β) ≤ Module.finrank K R) :
    ∃ α : R →ₗ[K] G, LinearMap.ker β ≤ LinearMap.range α := by
  classical
  rcases linear_surjective_finrank
      (K := K) (V := R) (W := LinearMap.ker β) hker_dim with
    ⟨f, hf⟩
  exact
    ⟨(LinearMap.ker β).subtype.comp f,
      subtype_covers_surjective
        (K := K) (G := G) (R := R) (LinearMap.ker β) f hf⟩

/--
Pointwise version of `linear_cover_finrank`.
-/
theorem pointwise_preimages_finrank
    {K G T R : Type*} [Field K]
    [AddCommGroup G] [Module K G] [Module.Free K G] [Module.Finite K G]
    [AddCommGroup T] [Module K T]
    [AddCommGroup R] [Module K R] [Module.Free K R] [Module.Finite K R]
    (β : G →ₗ[K] T)
    (hker_dim :
      Module.finrank K (LinearMap.ker β) ≤ Module.finrank K R) :
    ∃ α : R →ₗ[K] G,
      ∀ x : LinearMap.ker β, ∃ y : R, α y = (x : G) := by
  classical
  rcases linear_cover_finrank
      (K := K) (G := G) (T := T) (R := R) β hker_dim with
    ⟨α, hα⟩
  refine ⟨α, ?_⟩
  intro x
  exact hα x.2

/-- If a map from `R` has range containing the kernel of `β`, then the kernel
has dimension at most `R`. -/
theorem linear_finrank_range
    {K G T R : Type*} [Field K]
    [AddCommGroup G] [Module K G]
    [AddCommGroup T] [Module K T]
    [AddCommGroup R] [Module K R] [Module.Finite K R]
    (β : G →ₗ[K] T)
    (α : R →ₗ[K] G)
    (hker : LinearMap.ker β ≤ LinearMap.range α) :
    Module.finrank K (LinearMap.ker β) ≤ Module.finrank K R := by
  classical
  have hker_le_range :
      Module.finrank K (LinearMap.ker β) ≤
        Module.finrank K (LinearMap.range α) :=
    Submodule.finrank_mono hker
  have hrange_le_source :
      Module.finrank K (LinearMap.range α) ≤ Module.finrank K R :=
    LinearMap.finrank_range_le α
  exact hker_le_range.trans hrange_le_source

/--
Filtered linear algebra: exactness plus strictness descends to enough
quotient-level exactness for the kernel of the quotient map to be covered.
-/
theorem range_exact_strict
    {K R M N : Type*} [Field K]
    [AddCommGroup R] [Module K R]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (φ : R →ₗ[K] M)
    (μ : M →ₗ[K] N)
    (SR : Submodule K R)
    (SM : Submodule K M)
    (SN : Submodule K N)
    (hSR : SR ≤ SM.comap φ)
    (hSM : SM ≤ SN.comap μ)
    (hexact : LinearMap.ker μ ≤ LinearMap.range φ)
    (hstrict : ∀ m, μ m ∈ SN → ∃ s ∈ SM, μ s = μ m) :
    LinearMap.ker (SM.mapQ SN μ hSM) ≤
      LinearMap.range (SR.mapQ SM φ hSR) := by
  classical
  intro q
  refine Submodule.Quotient.induction_on (p := SM) q ?_
  intro m hq
  have hμm : μ m ∈ SN := by
    have hq' : SN.mkQ (μ m) = 0 := by
      simpa [Submodule.mapQ_apply] using hq
    exact (Submodule.Quotient.mk_eq_zero SN).mp hq'
  rcases hstrict m hμm with ⟨s, hsSM, hsm⟩
  have hker : m - s ∈ LinearMap.ker μ := by
    rw [LinearMap.mem_ker]
    simp [map_sub, hsm]
  rcases hexact hker with ⟨r, hr⟩
  refine ⟨SR.mkQ r, ?_⟩
  have hquot : SM.mkQ (φ r) = SM.mkQ m := by
    apply (Submodule.Quotient.eq SM).mpr
    rw [hr]
    have hneg : -s ∈ SM := SM.neg_mem hsSM
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hneg
  simpa [Submodule.mapQ_apply] using hquot
end TBluepr

end Towers
