import Submission.ClassField.LocalBrauer.InvariantTorsionLimit

/-!
# Chapter IV, Section 4: assembling the local invariant

The finite unramified calculations in Proposition IV.4.3 identify the group at
factorial level `r` with the multiplicative form of the
`invariantLevelDegree r`-torsion in `\mathbb{Q}/\mathbb{Z}`.  This file records
the formal direct-limit step: compatible identifications at every finite level
assemble to an identification of the direct limit with the full local invariant
group.
-/

namespace Submission.CField.LBrauer

noncomputable section

/-- The multiplicative form of the factorial torsion group at level `r`. -/
abbrev invariantTorsionLevel (r : ℕ) :=
  Multiplicative (localInvariantTorsion (invariantLevelDegree r))

/-- The transition map between multiplicative factorial torsion levels. -/
def invariantTorsionInclusion (r s : ℕ) (h : r ≤ s) :
    invariantTorsionLevel r →* invariantTorsionLevel s :=
  (localTorsionInclusion r s h).toMultiplicative

@[simp]
theorem torsion_inclusion_add
    (r s : ℕ) (h : r ≤ s) (x : invariantTorsionLevel r) :
    (invariantTorsionInclusion r s h x).toAdd =
      localTorsionInclusion r s h x.toAdd :=
  rfl

instance torsionDirectedSystem :
    DirectedSystem invariantTorsionLevel
      (fun {_ _} h ↦ invariantTorsionInclusion _ _ h) where
  map_self := by
    intro r x
    exact congrArg Multiplicative.ofAdd
      (DirectedSystem.map_self
        (f := fun {_ _} h ↦ localTorsionInclusion _ _ h) x.toAdd)
  map_map := by
    intro r s t hrs hst x
    exact congrArg Multiplicative.ofAdd
      (DirectedSystem.map_map
        (f := fun {_ _} h ↦ localTorsionInclusion _ _ h)
        hrs hst x.toAdd)

/-- The direct limit of the multiplicative factorial torsion groups. -/
abbrev localInvariantLimit :=
  DirectLimit invariantTorsionLevel invariantTorsionInclusion

/-- Inclusion of a multiplicative torsion level into the multiplicative local
invariant group. -/
def invariantTorsionMul (r : ℕ) :
    invariantTorsionLevel r →* Multiplicative LocalInvariant :=
  (localInvariantTorsion (invariantLevelDegree r)).subtype.toMultiplicative

@[simp]
theorem invariant_torsion_add
    (r : ℕ) (x : invariantTorsionLevel r) :
    (invariantTorsionMul r x).toAdd =
      (x.toAdd : LocalInvariant) :=
  rfl

section DirectLimitMonoidHom

variable {G : ℕ → Type*} [∀ r, CommGroup (G r)]
variable (f : ∀ r s : ℕ, r ≤ s → G r →* G s)
variable [DirectedSystem G (fun {_ _} h ↦ f _ _ h)]

/-- The multiplicative universal map out of a directed direct limit. -/
private def directLimitMonoid {P : Type*} [CommGroup P]
    (g : ∀ r, G r →* P)
    (hg : ∀ r s h x, g s (f r s h x) = g r x) :
    DirectLimit G f →* P where
  toFun := DirectLimit.lift f (fun r x ↦ g r x)
    (fun r s h x ↦ (hg r s h x).symm)
  map_one' := by
    rw [DirectLimit.one_def 0, DirectLimit.lift_def]
    exact map_one (g 0)
  map_mul' x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ r x y =>
        rw [DirectLimit.mul_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        exact map_mul (g r) x y

variable (e : ∀ r, G r ≃* invariantTorsionLevel r)
variable (he : ∀ r s h x,
  e s (f r s h x) = invariantTorsionInclusion r s h (e r x))

/-- Compatible finite-level invariant maps assemble to a homomorphism from the
direct limit to the local invariant group. -/
def limitAssemblyHom :
    DirectLimit G f →* Multiplicative LocalInvariant :=
  directLimitMonoid f
    (fun r ↦ (invariantTorsionMul r).comp (e r).toMonoidHom)
    (by
      intro r s h x
      change Multiplicative.ofAdd
          ((e s (f r s h x)).toAdd : LocalInvariant) =
        Multiplicative.ofAdd ((e r x).toAdd : LocalInvariant)
      rw [he r s h x]
      rfl)

@[simp]
theorem limit_assembly_mk (r : ℕ) (x : G r) :
    limitAssemblyHom f e he (⟦⟨r, x⟩⟧ : DirectLimit G f) =
      invariantTorsionMul r (e r x) :=
  rfl

theorem limit_assembly_injective :
    Function.Injective (limitAssemblyHom f e he) := by
  exact DirectLimit.lift_injective
    (f := f)
    (ih := fun r x ↦ invariantTorsionMul r (e r x))
    (compat := fun r s h x ↦ by
      change Multiplicative.ofAdd ((e r x).toAdd : LocalInvariant) =
        Multiplicative.ofAdd ((e s (f r s h x)).toAdd : LocalInvariant)
      rw [he r s h x]
      rfl)
    (fun r x y hxy ↦ by
      apply (e r).injective
      change (e r x).toAdd = (e r y).toAdd
      apply Subtype.ext
      exact congrArg (fun z : Multiplicative LocalInvariant ↦ z.toAdd) hxy)

theorem limit_assembly_surjective :
    Function.Surjective (limitAssemblyHom f e he) := by
  intro x
  obtain ⟨z, hz⟩ :=
    torsion_limit_surjective x.toAdd
  obtain ⟨r, y, hy⟩ :=
    DirectLimit.exists_eq_mk localTorsionInclusion z
  refine ⟨(⟦⟨r, (e r).symm (Multiplicative.ofAdd y)⟩⟧ : DirectLimit G f), ?_⟩
  rw [limit_assembly_mk]
  simp only [MulEquiv.apply_symm_apply]
  change (y : LocalInvariant) = x.toAdd
  rw [← hz, hy]
  rfl

/-- Abstract direct-limit assembly for Proposition IV.4.3.  Any compatible
family of finite-level multiplicative equivalences with the factorial torsion
groups induces an equivalence from its direct limit to `\mathbb{Q}/\mathbb{Z}`. -/
def invariantLimitAssembly :
    DirectLimit G f ≃* Multiplicative LocalInvariant :=
  MulEquiv.ofBijective (limitAssemblyHom f e he)
    ⟨limit_assembly_injective f e he,
      limit_assembly_surjective f e he⟩

end DirectLimitMonoidHom

/-- The multiplicative factorial torsion direct limit is canonically the
multiplicative local invariant group. -/
def torsionLimitEquiv :
    localInvariantLimit ≃* Multiplicative LocalInvariant :=
  invariantLimitAssembly
    invariantTorsionInclusion
    (fun _ ↦ MulEquiv.refl _)
    (fun _ _ _ _ ↦ rfl)

@[simp]
theorem torsion_limit_mk
    (r : ℕ) (x : invariantTorsionLevel r) :
    torsionLimitEquiv
        (⟦⟨r, x⟩⟧ : localInvariantLimit) =
      invariantTorsionMul r x :=
  rfl

end

end Submission.CField.LBrauer
