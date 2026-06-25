import Submission.FieldTheory.CentralEmbeddingBrauer

/-!
# Pullback of a central embedding problem

This file packages restriction of a central extension along an arbitrary
group homomorphism.  The pullback projection is again surjective and central,
and its kernel is canonically the kernel of the original extension.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Submission.CField.CProduca

universe u v w

/-- The group-theoretic pullback of `q : Q → G` along `f : H → G`. -/
def extensionPullbackSubgroup
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) : Subgroup (H × Q) where
  carrier := {x | f x.1 = q x.2}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨h, x⟩ ⟨k, y⟩ hx hy
    change f (h * k) = q (x * y)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    rintro ⟨h, x⟩ hx
    change f h⁻¹ = q x⁻¹
    rw [map_inv, map_inv, hx]

/-- The underlying group of the pullback extension. -/
abbrev CentralExtensionPullback
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :=
  extensionPullbackSubgroup q f

/-- Projection of the pullback extension to its new base group. -/
def extensionPullbackProjection
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :
    CentralExtensionPullback q f →* H :=
  (MonoidHom.fst H Q).comp (extensionPullbackSubgroup q f).subtype

/-- The second projection from the pullback to the original total group. -/
def extensionPullbackTotal
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :
    CentralExtensionPullback q f →* Q :=
  (MonoidHom.snd H Q).comp (extensionPullbackSubgroup q f).subtype

theorem extension_pullback_commutes
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :
    q.comp (extensionPullbackTotal q f) =
      f.comp (extensionPullbackProjection q f) := by
  ext x
  exact x.property.symm

/-- Pullback preserves surjectivity of the extension projection. -/
theorem central_pullback_projection
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (hq : Function.Surjective q) (f : H →* G) :
    Function.Surjective (extensionPullbackProjection q f) := by
  intro h
  obtain ⟨x, hx⟩ := hq (f h)
  exact ⟨⟨(h, x), hx.symm⟩, rfl⟩

/-- Pullback preserves centrality of the extension kernel. -/
theorem extension_pullback_projection
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G)
    (hcentral : q.ker ≤ Subgroup.center Q) :
    (extensionPullbackProjection q f).ker ≤
      Subgroup.center (CentralExtensionPullback q f) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Prod.ext
  · have hxfirst : x.1.1 = 1 := MonoidHom.mem_ker.mp hx
    simp [hxfirst]
  · have hxq : x.1.2 ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      have hmem := x.property
      have hxfirst : x.1.1 = 1 := MonoidHom.mem_ker.mp hx
      simpa [hxfirst] using hmem.symm
    exact Subgroup.mem_center_iff.mp (hcentral hxq) y.1.2

/-- The kernel of a pullback extension is canonically the old kernel. -/
def centralExtensionPullback
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :
    (extensionPullbackProjection q f).ker ≃* q.ker where
  toFun z := ⟨z.1.1.2, by
    have hzfirst : z.1.1.1 = 1 := MonoidHom.mem_ker.mp z.2
    have hzmem := z.1.2
    change q z.1.1.2 = 1
    simpa [hzfirst] using hzmem.symm⟩
  invFun z := ⟨⟨(1, z.1), by
    change f 1 = q z.1
    rw [map_one]
    exact z.2.symm⟩, by rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact MonoidHom.mem_ker.mp z.2 |>.symm
    · rfl
  right_inv z := rfl
  map_mul' x y := rfl

theorem extension_pullback_card
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (f : H →* G) :
    Nat.card (extensionPullbackProjection q f).ker = Nat.card q.ker :=
  Nat.card_congr (centralExtensionPullback q f).toEquiv

/-- The obstruction of the pullback extension is the restriction of the
original obstruction, after identifying the two central kernels. -/
theorem extension_pullback_obstruction
    {Q : Type u} {G : Type v} {H : Type w}
    [Group Q] [Group G] [Group H]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (f : H →* G) :
    let p := extensionPullbackProjection q f
    let hp := central_pullback_projection q hq f
    let hpc := extension_pullback_projection q f hcentral
    letI : CommGroup q.ker := centralExtensionComm q hcentral
    letI : CommGroup p.ker := centralExtensionComm p hpc
    letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
    letI : MulDistribMulAction H q.ker := trivialDistribAction H q.ker
    letI : MulDistribMulAction H p.ker := trivialDistribAction H p.ker
    MHTwo.mapCoefficientsHom
        (centralExtensionPullback q f).toMonoidHom
        (fun _ _ => rfl)
        (extensionObstructionClass p hp hpc) =
      MHTwo.restrictionHom f (fun _ _ => rfl)
        (extensionObstructionClass q hq hcentral) := by
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  letI : CommGroup q.ker := centralExtensionComm q hcentral
  letI : CommGroup p.ker := centralExtensionComm p hpc
  letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker := trivialDistribAction H q.ker
  letI : MulDistribMulAction H p.ker := trivialDistribAction H p.ker
  let e := centralExtensionPullback q f
  let cP := centralExtensionSet p hp hpc
  let cQ := centralExtensionSet q hq hcentral
  let sP : H → CentralExtensionPullback q f := normalizedSurjInv p hp
  let sQ : G → Q := normalizedSurjInv q hq
  let t : H → Q := fun h => (sP h).1.2
  have ht_maps (h : H) : q (t h) = f h := by
    have hsP := (sP h).property
    have hfirst := normalized_surj_maps p hp h
    change (sP h).1.1 = h at hfirst
    change f (sP h).1.1 = q (sP h).1.2 at hsP
    rw [hfirst] at hsP
    exact hsP.symm
  let d : H → q.ker := fun h =>
    ⟨t h * (sQ (f h))⁻¹, by
      change q (t h * (sQ (f h))⁻¹) = 1
      rw [map_mul, map_inv, ht_maps,
        show q (sQ (f h)) = f h from normalized_surj_maps q hq (f h)]
      exact mul_inv_cancel (f h)⟩
  change MHTwo.mk
      (NMCocycl₂.mapCoefficients e.toMonoidHom (fun _ _ => rfl)
        (cP.normalizedMulCocycle (fun _ _ => rfl))) =
    MHTwo.mk
      (NMCocycl₂.restrict f (fun _ _ => rfl)
        (cQ.normalizedMulCocycle (fun _ _ => rfl)))
  rw [MHTwo.mk_eq_iff]
  refine ⟨d, ?_⟩
  intro h k
  apply Subtype.ext
  simp only [NMCocycl₂.mapCoefficients_apply,
    CFSet.normalized_mul_cocycle,
    NMCocycl₂.restrict_apply]
  change
    (d k : Q) / (d (h * k) : Q) * (d h : Q) =
      (e (cP (h, k)) : Q) / (cQ (f h, f k) : Q)
  have hcP : (e (cP (h, k)) : Q) =
      t h * t k * (t (h * k))⁻¹ := rfl
  have hcQ : (cQ (f h, f k) : Q) =
      sQ (f h) * sQ (f k) * (sQ (f h * f k))⁻¹ := rfl
  rw [hcP, hcQ]
  symm
  have hd_center (a : H) (z : Q) : (d a : Q) * z = z * (d a : Q) :=
    (Subgroup.mem_center_iff.mp (hcentral (d a).property) z).symm
  have hd_inv_center (a : H) (z : Q) :
      (d a : Q)⁻¹ * z = z * (d a : Q)⁻¹ :=
    (Subgroup.mem_center_iff.mp (hcentral ((d a)⁻¹).property) z).symm
  have ht (a : H) : t a = (d a : Q) * sQ (f a) := by
    change t a = (t a * (sQ (f a))⁻¹) * sQ (f a)
    group
  rw [ht h, ht k, ht (h * k)]
  rw [map_mul]
  simp only [div_eq_mul_inv]
  calc
    ((d h : Q) * sQ (f h)) * ((d k : Q) * sQ (f k)) *
          (((d (h * k) : Q) * sQ (f h * f k))⁻¹) *
            (sQ (f h) * sQ (f k) * (sQ (f h * f k))⁻¹)⁻¹ =
        (d h : Q) * sQ (f h) * (d k : Q) * sQ (f k) *
          (sQ (f h * f k))⁻¹ * (d (h * k) : Q)⁻¹ *
            sQ (f h * f k) * (sQ (f k))⁻¹ * (sQ (f h))⁻¹ := by
      group
    _ = (d h : Q) * (d k : Q) * sQ (f h) * sQ (f k) *
          (sQ (f h * f k))⁻¹ * (d (h * k) : Q)⁻¹ *
            sQ (f h * f k) * (sQ (f k))⁻¹ * (sQ (f h))⁻¹ := by
      rw [mul_assoc (d h : Q) (sQ (f h)) (d k : Q),
        (hd_center k (sQ (f h))).symm,
        ← mul_assoc (d h : Q) (d k : Q) (sQ (f h))]
    _ = (d h : Q) * (d k : Q) *
          ((sQ (f h) * sQ (f k) * (sQ (f h * f k))⁻¹) *
            (d (h * k) : Q)⁻¹) *
          sQ (f h * f k) * (sQ (f k))⁻¹ * (sQ (f h))⁻¹ := by
      group
    _ = (d h : Q) * (d k : Q) *
          ((d (h * k) : Q)⁻¹ *
            (sQ (f h) * sQ (f k) * (sQ (f h * f k))⁻¹)) *
          sQ (f h * f k) * (sQ (f k))⁻¹ * (sQ (f h))⁻¹ := by
      rw [hd_inv_center (h * k)
        (sQ (f h) * sQ (f k) * (sQ (f h * f k))⁻¹)]
    _ = (d h : Q) * (d k : Q) * (d (h * k) : Q)⁻¹ := by
      group
    _ = (d k : Q) * (d (h * k) : Q)⁻¹ * (d h : Q) := by
      rw [mul_assoc (d h : Q) (d k : Q) (d (h * k) : Q)⁻¹,
        hd_center h ((d k : Q) * (d (h * k) : Q)⁻¹)]

/-- After a fixed coefficient embedding, the pullback obstruction is the
coefficient image of the restricted original obstruction. -/
theorem pullback_mapped_obstruction
    {Q : Type u} {G : Type v} {H : Type w} {M : Type*}
    [Group Q] [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction H M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (f : H →* G)
    (kernelToM : q.ker →* M)
    (hfixed : ∀ h : H, ∀ z : q.ker, h • kernelToM z = kernelToM z) :
    let p := extensionPullbackProjection q f
    let hp := central_pullback_projection q hq f
    let hpc := extension_pullback_projection q f hcentral
    let e := centralExtensionPullback q f
    letI : CommGroup q.ker := centralExtensionComm q hcentral
    letI : CommGroup p.ker := centralExtensionComm p hpc
    letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
    letI : MulDistribMulAction H q.ker := trivialDistribAction H q.ker
    letI : MulDistribMulAction H p.ker := trivialDistribAction H p.ker
    MHTwo.mapCoefficientsHom
        (kernelToM.comp e.toMonoidHom)
        (fun h z => (hfixed h (e z)).symm)
        (extensionObstructionClass p hp hpc) =
      MHTwo.mapCoefficientsHom kernelToM
        (fun h z => (hfixed h z).symm)
        (MHTwo.restrictionHom f (fun _ _ => rfl)
          (extensionObstructionClass q hq hcentral)) := by
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  letI : CommGroup q.ker := centralExtensionComm q hcentral
  letI : CommGroup p.ker := centralExtensionComm p hpc
  letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker := trivialDistribAction H q.ker
  letI : MulDistribMulAction H p.ker := trivialDistribAction H p.ker
  have hnat := extension_pullback_obstruction q hq hcentral f
  calc
    MHTwo.mapCoefficientsHom
          (kernelToM.comp e.toMonoidHom)
          (fun h z => (hfixed h (e z)).symm)
          (extensionObstructionClass p hp hpc) =
        MHTwo.mapCoefficientsHom kernelToM
          (fun h z => (hfixed h z).symm)
          (MHTwo.mapCoefficientsHom e.toMonoidHom
            (fun _ _ => rfl)
            (extensionObstructionClass p hp hpc)) := by
      symm
      exact MHTwo.coefficients_hom_comp
        e.toMonoidHom kernelToM (fun _ _ => rfl)
        (fun h z => (hfixed h z).symm)
        (fun h z => (hfixed h (e z)).symm)
        (extensionObstructionClass p hp hpc)
    _ = MHTwo.mapCoefficientsHom kernelToM
          (fun h z => (hfixed h z).symm)
          (MHTwo.restrictionHom f (fun _ _ => rfl)
            (extensionObstructionClass q hq hcentral)) := by
      exact congrArg
        (MHTwo.mapCoefficientsHom kernelToM
          (fun h z => (hfixed h z).symm)) hnat

/-- Galois-cohomological specialization of the pullback obstruction formula.
The quotient of the pullback is the Galois group itself, so the comparison
equivalence is the identity. -/
theorem central_extension_pullback
    {Q : Type u} {G : Type v} [Group Q] [Group G]
    {K L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (f : Gal(L/K) →* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ σ : Gal(L/K), ∀ z : q.ker,
      σ • kernelToUnits z = kernelToUnits z) :
    let p := extensionPullbackProjection q f
    let hp := central_pullback_projection q hq f
    let hpc := extension_pullback_projection q f hcentral
    let e := centralExtensionPullback q f
    letI : CommGroup q.ker := centralExtensionComm q hcentral
    letI : CommGroup p.ker := centralExtensionComm p hpc
    letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
    letI : MulDistribMulAction Gal(L/K) q.ker :=
      trivialDistribAction Gal(L/K) q.ker
    letI : MulDistribMulAction Gal(L/K) p.ker :=
      trivialDistribAction Gal(L/K) p.ker
    centralExtensionClass p hp hpc (MulEquiv.refl Gal(L/K))
        (kernelToUnits.comp e.toMonoidHom)
        (fun σ z => hfixed σ (e z)) =
      MHTwo.mapCoefficientsHom kernelToUnits
        (fun σ z => (hfixed σ z).symm)
        (MHTwo.restrictionHom f (fun _ _ => rfl)
          (extensionObstructionClass q hq hcentral)) := by
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  letI : CommGroup q.ker := centralExtensionComm q hcentral
  letI : CommGroup p.ker := centralExtensionComm p hpc
  letI : MulDistribMulAction G q.ker := trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  letI : MulDistribMulAction Gal(L/K) p.ker :=
    trivialDistribAction Gal(L/K) p.ker
  change MHTwo.mapCoefficientsHom
      (kernelToUnits.comp e.toMonoidHom)
      (fun σ z => (hfixed σ (e z)).symm)
      (MHTwo.restrictionHom (MonoidHom.id Gal(L/K))
        (fun _ _ => rfl) (extensionObstructionClass p hp hpc)) = _
  rw [MHTwo.restrictionHom_id]
  exact pullback_mapped_obstruction
    q hq hcentral f kernelToUnits hfixed

end TBluepr
end Submission
