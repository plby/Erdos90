import Submission.Group.FiniteQuotientTower.KernelSeparation
import Submission.Group.FinitePRelator.RelatorKernelFactorization


noncomputable section

namespace Submission
namespace Group

open PRFact

universe u

namespace cSQuotie

variable
    (S : cSQuotie.{u})
    {H : Type u}
    [Group H]
    (φ : inverseLimit S →* H)

/--
A detected kernel thread is a coherent inverse-limit thread killed by a map out
of the inverse limit but still visible in one finite quotient coordinate.
-/
structure DKThread where
  thread : inverseLimit S
  killed : φ thread = 1
  depth : ℕ
  detected : inverseLimitProjection S depth thread ≠ 1

namespace DKThread

lemma thread_mem_ker
    (W : DKThread S φ) :
    W.thread ∈ φ.ker := by
  exact MonoidHom.mem_ker.mpr W.killed

lemma thread_ne_one
    (W : DKThread S φ) :
    W.thread ≠ 1 := by
  intro hthread
  apply W.detected
  rw [hthread]
  exact limit_projection_one S W.depth

/--
Every detected kernel thread has at least one finite coordinate where it is
visible.
-/
lemma exists_detected_at
    (W : DKThread S φ) :
    ∃ n : ℕ, inverseLimitProjection S n W.thread ≠ 1 := by
  exact ⟨W.depth, W.detected⟩

/--
The first finite quotient coordinate where a detected kernel thread is visible.
-/
noncomputable def firstDetectedDepth
    (W : DKThread S φ) :
    ℕ := by
  classical
  exact Nat.find W.exists_detected_at

/--
The first detected depth is no later than the originally stored witness depth.
-/
lemma first_detected_depth
    (W : DKThread S φ) :
    W.firstDetectedDepth ≤ W.depth := by
  classical
  exact Nat.find_min' W.exists_detected_at W.detected

/--
A detected kernel thread is visible at its first detected finite quotient
coordinate.
-/
lemma detected_first_depth
    (W : DKThread S φ) :
    inverseLimitProjection S W.firstDetectedDepth W.thread ≠ 1 := by
  classical
  exact Nat.find_spec W.exists_detected_at

/--
All earlier finite quotient coordinates miss a detected kernel thread before
its first detected depth.
-/
lemma projection_detected_depth
    (W : DKThread S φ)
    {m : ℕ}
    (hm : m < W.firstDetectedDepth) :
    inverseLimitProjection S m W.thread = 1 := by
  classical
  by_contra hdetected
  exact (Nat.find_min W.exists_detected_at hm) hdetected

end DKThread

/--
Failure of injectivity for a map out of an inverse limit is witnessed by one
kernel thread visible in one finite quotient coordinate.
-/
lemma detected_thread_injective :
    Nonempty (DKThread S φ) ↔
      ¬ Function.Injective φ := by
  constructor
  · rintro ⟨W⟩ hInjective
    exact DKThread.thread_ne_one S φ W
      (hInjective (W.killed.trans φ.map_one.symm))
  · intro hnot
    have hker : φ.ker ≠ ⊥ := by
      intro hker
      exact hnot ((MonoidHom.ker_eq_bot_iff φ).mp hker)
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hker with ⟨x, hxne⟩
    have hdetected :
        ∃ n : ℕ, inverseLimitProjection S n x ≠ 1 := by
      by_contra hnone
      have hall : ∀ n : ℕ, inverseLimitProjection S n x = 1 := by
        intro n
        by_contra hn
        exact hnone ⟨n, hn⟩
      apply hxne
      exact Subtype.ext (S.inverse_limit_projections hall)
    rcases hdetected with ⟨n, hn⟩
    exact ⟨{
      thread := x
      killed := MonoidHom.mem_ker.mp x.property
      depth := n
      detected := hn
    }⟩

/--
Equivalent unbundled form of a detected kernel thread.
-/
lemma not_detected_level :
    ¬ Function.Injective φ ↔
      ∃ x : inverseLimit S, x ∈ φ.ker ∧
        ∃ n : ℕ, inverseLimitProjection S n x ≠ 1 := by
  constructor
  · intro hnot
    rcases (S.detected_thread_injective φ).2 hnot with
      ⟨W⟩
    exact ⟨W.thread, W.thread_mem_ker, W.depth, W.detected⟩
  · rintro ⟨x, hx, n, hxn⟩
    apply (S.detected_thread_injective φ).1
    exact ⟨{
      thread := x
      killed := MonoidHom.mem_ker.mp hx
      depth := n
      detected := hxn
    }⟩

/--
Failure of injectivity is equivalently witnessed by two fibers with one finite
coordinate still distinguishing them.
-/
lemma not_fiber_counterexample :
    ¬ Function.Injective φ ↔
      ∃ x y : inverseLimit S, φ x = φ y ∧
        ∃ n : ℕ,
          inverseLimitProjection S n x ≠ inverseLimitProjection S n y := by
  constructor
  · intro hnot
    rcases (S.not_detected_level φ).1
      hnot with ⟨x, hx, n, hxn⟩
    exact ⟨x, 1, by
      rw [MonoidHom.mem_ker] at hx
      exact hx.trans φ.map_one.symm,
      n, by simpa using hxn⟩
  · rintro ⟨x, y, hxy, n, hcoord⟩ hInjective
    apply hcoord
    rw [hInjective hxy]

/--
One finite projection factors uniquely through a surjective inverse-limit
descent exactly when that descent kernel is invisible in the finite projection.
-/
lemma projection_unique_through
    (hφ : Function.Surjective φ)
    (n : ℕ) :
    FactorsUniquelyThrough φ (inverseLimitProjection S n) ↔
      φ.ker ≤ (inverseLimitProjection S n).ker := by
  letI : TopologicalSpace (inverseLimit S) := ⊤
  letI : IndiscreteTopology (inverseLimit S) := inferInstance
  letI : IsTopologicalGroup (inverseLimit S) := inferInstance
  exact PRFact.uniquely_through_ker
    φ
    (inverseLimitProjection S n)
    hφ

/--
A surjective map out of an inverse limit is injective exactly when every finite
projection factors uniquely through it.
-/
lemma forall_uniquely_through
    (hφ : Function.Surjective φ) :
    (∀ n : ℕ, FactorsUniquelyThrough φ (inverseLimitProjection S n)) ↔
      Function.Injective φ := by
  constructor
  · intro hfactor
    apply (S.injective_projection_kernels φ).mpr
    intro n
    exact (S.projection_unique_through
      φ hφ n).mp (hfactor n)
  · intro hInjective n
    apply (S.projection_unique_through
      φ hφ n).mpr
    exact (S.injective_projection_kernels φ).mp hInjective n

/--
Failure of injectivity is equivalently failure of one finite projection to
descend through a surjective inverse-limit map.
-/
lemma not_uniquely_through
    (hφ : Function.Surjective φ) :
    ¬ Function.Injective φ ↔
      ∃ n : ℕ, ¬ FactorsUniquelyThrough φ (inverseLimitProjection S n) := by
  rw [← S.forall_uniquely_through φ hφ]
  simp only [not_forall]

end cSQuotie

end Group
end Submission
