import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.GroupTheory.Divisible
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Milne, Class Field Theory, Proposition II.A.3

Injective modules over a principal ideal domain are exactly the divisible modules.
-/

namespace Submission.CField.Homological

open CategoryTheory

universe u

variable {R M : Type u} [CommRing R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

/-- A divisible module over a principal ideal ring satisfies Baer's criterion. -/
private theorem baer_of_divisible [DivisibleBy M R] : Module.Baer R M := fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨r, rfl⟩
  obtain rfl | hr := eq_or_ne r 0
  · refine ⟨0, fun x hx => ?_⟩
    rw [Submodule.span_zero_singleton] at hx
    subst x
    exact (map_zero g).symm
  let m := g ⟨r, Submodule.subset_span (Set.mem_singleton r)⟩
  refine ⟨LinearMap.toSpanSingleton R M (DivisibleBy.div m r), fun x hx => ?_⟩
  rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
  rw [LinearMap.toSpanSingleton_apply]
  calc
    (a • r) • DivisibleBy.div m r = a • (r • DivisibleBy.div m r) := by
      rw [smul_eq_mul, mul_smul]
    _ = a • m := by rw [DivisibleBy.div_cancel m hr]
    _ = g (a • ⟨r, Submodule.subset_span (Set.mem_singleton r)⟩) := (map_smul g _ _).symm
    _ = g ⟨a • r, hx⟩ := by congr

variable [IsDomain R]

/-- **Proposition II.A.3.** A module over a principal ideal domain is injective
if and only if it is divisible. -/
theorem module_injective_divisible :
    Module.Injective R M ↔ Nonempty (DivisibleBy M R) := by
  constructor
  · intro h
    refine ⟨divisibleByOfSMulRightSurj M R fun {r} hr m => ?_⟩
    let f := LinearMap.mul R R r
    have hf : Function.Injective f := mul_right_injective₀ hr
    obtain ⟨g, hg⟩ := h.out f hf (LinearMap.toSpanSingleton R M m)
    refine ⟨g 1, ?_⟩
    calc
      r • g 1 = g (r • 1) := (map_smul g r 1).symm
      _ = m := by simpa [f] using hg 1
  · rintro ⟨h⟩
    letI : DivisibleBy M R := h
    exact baer_of_divisible.injective

/-- The categorical form of Proposition II.A.3. -/
theorem injective_iff_divisible :
    CategoryTheory.Injective (ModuleCat.of R M) ↔ Nonempty (DivisibleBy M R) := by
  rw [← Module.injective_iff_injective_object]
  exact module_injective_divisible

end Submission.CField.Homological
