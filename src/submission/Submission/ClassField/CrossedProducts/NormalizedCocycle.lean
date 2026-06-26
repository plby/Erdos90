import Submission.ClassField.CrossedProducts.CocycleConstruction

/-!
# Chapter IV, Section 3: normalized multiplicative 2-cocycles

Milne constructs a crossed-product algebra from a normalized representative
of a class in `H²`.  This file records the elementary normalization step:
every multiplicative 2-cocycle is cohomologous to one whose values on
`(1, g)` and `(g, 1)` are both `1`.
-/

namespace Submission.CField.CProduca

open groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- A multiplicative 2-cocycle normalized at the identity. -/
structure NMCocycl₂ where
  toFun : G × G → M
  isMulCocycle₂ : IsMulCocycle₂ toFun
  map_one_fst : ∀ g : G, toFun (1, g) = 1
  map_one_snd : ∀ g : G, toFun (g, 1) = 1

namespace NMCocycl₂

instance : CoeFun (NMCocycl₂ (G := G) (M := M))
    (fun _ ↦ G × G → M) := ⟨toFun⟩

@[simp]
theorem apply_one_fst (f : NMCocycl₂ (G := G) (M := M)) (g : G) :
    f (1, g) = 1 :=
  f.map_one_fst g

@[simp]
theorem apply_one_snd (f : NMCocycl₂ (G := G) (M := M)) (g : G) :
    f (g, 1) = 1 :=
  f.map_one_snd g

/-- Divide a cocycle by the constant coboundary determined by `f (1, 1)`.
The resulting cocycle is normalized. -/
def normalize (f : G × G → M) (hf : IsMulCocycle₂ f) :
    NMCocycl₂ (G := G) (M := M) where
  toFun p := f p / (p.1 • f (1, 1))
  isMulCocycle₂ := by
    intro g h j
    simp only [div_eq_mul_inv]
    rw [mul_smul]
    have hcocycle := hf g h j
    calc
      (f (g * h, j) * (g • h • f (1, 1))⁻¹) *
          (f (g, h) * (g • f (1, 1))⁻¹) =
          (f (g * h, j) * f (g, h)) *
            ((g • h • f (1, 1))⁻¹ * (g • f (1, 1))⁻¹) := by
              ac_rfl
      _ = (g • f (h, j) * f (g, h * j)) *
            ((g • h • f (1, 1))⁻¹ * (g • f (1, 1))⁻¹) := by rw [hcocycle]
      _ = (g • (f (h, j) * (h • f (1, 1))⁻¹)) *
            (f (g, h * j) * (g • f (1, 1))⁻¹) := by
              simp only [smul_mul', smul_inv']
              ac_rfl
  map_one_fst g := by
    rw [one_smul, map_one_fst_of_isMulCocycle₂ hf]
    simp
  map_one_snd g := by
    rw [map_one_snd_of_isMulCocycle₂ hf]
    simp

/-- Normalization changes a cocycle by a multiplicative 2-coboundary. -/
theorem normalize_div_coboundary₂ (f : G × G → M)
    (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ (fun p ↦ normalize f hf p / f p) := by
  refine ⟨fun _ ↦ (f (1, 1))⁻¹, ?_⟩
  intro g h
  simp only [normalize, div_eq_mul_inv, smul_inv']
  simp [mul_left_comm, mul_comm]

end NMCocycl₂

end Submission.CField.CProduca
