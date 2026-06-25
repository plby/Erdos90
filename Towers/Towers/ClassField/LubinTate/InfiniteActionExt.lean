import Towers.ClassField.LubinTate.InfiniteActionLevel

/-!
# Extensionality for the infinite Lubin--Tate tower

The infinite torsion field is the directed union of its finite levels, so
algebra homomorphisms out of it are determined level by level.
-/

namespace Towers.CField.LTate

noncomputable section

namespace LTDatum

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (Omega : Type w) [Field Omega] [Algebra K Omega]

/-- Algebra homomorphisms out of `K_pi` are determined by their values on
all finite torsion levels. -/
theorem infinite_torsion_ext
    (f g : D.infiniteTorsionField K Omega →ₐ[K]
      D.infiniteTorsionField K Omega)
    (h : ∀ (n : ℕ) (x : D.torsionLevelField K Omega n),
      f (D.torsionLevelInclusion K Omega n x) =
        g (D.torsionLevelInclusion K Omega n x)) :
    f = g := by
  apply AlgHom.ext
  intro x
  obtain ⟨n, hn⟩ :=
    (D.infinite_torsion_field K Omega (x : Omega)).1 x.property
  let y : D.torsionLevelField K Omega n := ⟨x, hn⟩
  have hxy :
      D.torsionLevelInclusion K Omega n y = x := by
    apply Subtype.ext
    rfl
  rw [← hxy]
  exact h n y

end LTDatum

end

end Towers.CField.LTate
