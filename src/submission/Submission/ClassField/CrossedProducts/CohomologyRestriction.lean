import Submission.ClassField.CrossedProducts.CohomologyClass

/-!
# Restriction in normalized multiplicative second cohomology

A homomorphism `H →* G` pulls a `G`-action back to `H`.  Restricting both
arguments of a normalized multiplicative two-cocycle therefore defines the
usual restriction homomorphism on `H²`.
-/

namespace Submission.CField.CProduca

noncomputable section

open groupCohomology

universe uG uH uM

variable {G : Type uG} {H : Type uH} {M : Type uM}
  [Group G] [Group H] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]

namespace NMCocycl₂

/-- Restrict a normalized multiplicative two-cocycle along a group
homomorphism. -/
def restrict (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    NMCocycl₂ (G := H) (M := M) where
  toFun p := c (f p.1, f p.2)
  isMulCocycle₂ g h j := by
    rw [hsmul]
    simpa only [map_mul] using c.isMulCocycle₂ (f g) (f h) (f j)
  map_one_fst g := by simp
  map_one_snd g := by simp

@[simp]
theorem restrict_apply (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (c : NMCocycl₂ (G := G) (M := M)) (g h : H) :
    restrict f hsmul c (g, h) = c (f g, f h) :=
  rfl

/-- Restriction is a homomorphism on normalized cocycles. -/
def restrictionHom (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    NMCocycl₂ (G := G) (M := M) →*
      NMCocycl₂ (G := H) (M := M) where
  toFun := restrict f hsmul
  map_one' := by
    ext p
    rfl
  map_mul' c d := by
    ext p
    rfl

@[simp]
theorem restrictionHom_apply (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    restrictionHom f hsmul c = restrict f hsmul c :=
  rfl

end NMCocycl₂

namespace MHTwo

/-- Cohomologous cocycles remain cohomologous after restriction. -/
theorem isCohomologous_restrict (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : IsCohomologous c d) :
    IsCohomologous
      (NMCocycl₂.restrict f hsmul c)
      (NMCocycl₂.restrict f hsmul d) := by
  obtain ⟨x, hx⟩ := hcd
  refine ⟨fun h ↦ x (f h), ?_⟩
  intro g h
  rw [hsmul]
  simpa only [NMCocycl₂.restrict_apply, map_mul] using
    hx (f g) (f h)

/-- Restriction in normalized multiplicative second cohomology. -/
def restrictionHom (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    MHTwo G M →* MHTwo H M where
  toFun := Quotient.map (NMCocycl₂.restrict f hsmul)
    (fun _ _ h ↦ isCohomologous_restrict f hsmul h)
  map_one' := by
    change mk (NMCocycl₂.restrict f hsmul 1) = mk 1
    apply congrArg mk
    exact (NMCocycl₂.restrictionHom f hsmul).map_one
  map_mul' x y := by
    induction x, y using Quotient.inductionOn₂ with
    | _ c d =>
        change mk (NMCocycl₂.restrict f hsmul (c * d)) =
          mk (NMCocycl₂.restrict f hsmul c) *
            mk (NMCocycl₂.restrict f hsmul d)
        rw [← mk_mul]
        exact congrArg mk
          ((NMCocycl₂.restrictionHom f hsmul).map_mul c d)

@[simp]
theorem restrictionHom_mk (f : H →* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    restrictionHom f hsmul (mk c) =
      mk (NMCocycl₂.restrict f hsmul c) :=
  rfl

@[simp]
theorem restrictionHom_id
    (hsmul : ∀ g : G, ∀ m : M, g • m = (MonoidHom.id G) g • m)
    (x : MHTwo G M) :
    restrictionHom (MonoidHom.id G) hsmul x = x := by
  induction x using Quotient.inductionOn with
  | _ c => rfl

theorem restrictionHom_comp
    {J : Type*} [Group J] [MulDistribMulAction J M]
    (f : H →* G) (g : J →* H)
    (hf : ∀ h : H, ∀ m : M, h • m = f h • m)
    (hg : ∀ j : J, ∀ m : M, j • m = g j • m)
    (hfg : ∀ j : J, ∀ m : M, j • m = (f.comp g) j • m)
    (x : MHTwo G M) :
    restrictionHom g hg (restrictionHom f hf x) =
      restrictionHom (f.comp g) hfg x := by
  induction x using Quotient.inductionOn with
  | _ c => rfl

end MHTwo

end

end Submission.CField.CProduca
