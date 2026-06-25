import Towers.ClassField.GlobalClass.RelativeH2
import Towers.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# The absolute-invariant proof of Theorem VIII.4.7

The paragraph preceding Theorem VIII.4.7 regards the relative group
`H²(L/K)` as the kernel of restriction between two absolute cohomology
groups.  Lemma VIII.4.6 says that the two absolute invariants turn this
restriction into multiplication by `[L : K]` on `ℚ/ℤ`.  Consequently the
relative group is exactly the `[L : K]`-torsion subgroup of `ℚ/ℤ`.

This file proves that argument abstractly, but with all maps and exactness
oriented exactly as in the text.  The remaining bridge now asks only for the
absolute cohomology groups, their canonical invariants, and the restriction
sequence; it no longer assumes the conclusion of Theorem 4.7 itself.
-/

namespace Towers.CField.GClass

open Towers.CField.LBrauer

noncomputable section

universe u v w

/-- The finite-level portion of the absolute invariant construction used
immediately before Theorem VIII.4.7.

Here `relative` is `H²(L/K)`, `absoluteK` and `absoluteL` are the two
absolute idèle-class cohomology groups, `inclusion` and `restriction` form the
exact sequence

`0 → H²(L/K) → H²(Kᵃˡ/K) → H²(Kᵃˡ/L)`,

and `restriction_formula` is Lemma VIII.4.6. -/
structure ARData
    (relative : Type u) (absoluteK : Type v) (absoluteL : Type w)
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] (degree : ℕ) where
  inclusion : relative →+ absoluteK
  restriction : absoluteK →+ absoluteL
  invariantK : absoluteK ≃+ LocalInvariant
  invariantL : absoluteL ≃+ LocalInvariant
  exact_sequence : Function.Exact inclusion restriction
  inclusion_injective : Function.Injective inclusion
  restriction_formula : ∀ gamma : absoluteK,
    invariantL (restriction gamma) = degree • invariantK gamma

/-- Restrict the absolute invariant of `K` to the relative group. -/
def ARData.relativeInvariant
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ}
    (data : ARData
      relative absoluteK absoluteL degree) :
    relative →+ LocalInvariant :=
  data.invariantK.toAddMonoidHom.comp data.inclusion

/-- The relative invariant is injective because both the inclusion into
absolute cohomology and the absolute invariant are injective. -/
theorem ARData.relativeInvariant_injective
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ}
    (data : ARData
      relative absoluteK absoluteL degree) :
    Function.Injective data.relativeInvariant :=
  data.invariantK.injective.comp data.inclusion_injective

/-- The image of the relative invariant is precisely the subgroup of
`LocalInvariant = ℚ/ℤ` killed by the extension degree.  This is the
finite-level consequence of Lemma VIII.4.6 used in the printed proof. -/
theorem ARData.range_relativeInvariant
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ}
    (data : ARData
      relative absoluteK absoluteL degree) :
    Set.range data.relativeInvariant =
      (localInvariantTorsion degree : Set LocalInvariant) := by
  ext x
  constructor
  · rintro ⟨gamma, rfl⟩
    change degree • data.invariantK (data.inclusion gamma) = 0
    rw [← data.restriction_formula]
    have hzero : data.restriction (data.inclusion gamma) = 0 :=
      data.exact_sequence.apply_apply_eq_zero gamma
    rw [hzero, map_zero]
  · intro hx
    let gammaK : absoluteK := data.invariantK.symm x
    have hrestrict : data.restriction gammaK = 0 := by
      apply data.invariantL.injective
      rw [data.restriction_formula, map_zero]
      simpa [gammaK] using hx
    obtain ⟨gamma, hgamma⟩ :=
      (data.exact_sequence gammaK).mp hrestrict
    refine ⟨gamma, ?_⟩
    change data.invariantK (data.inclusion gamma) = x
    rw [hgamma]
    exact data.invariantK.apply_symm_apply x

/-- The relative invariant with codomain restricted to the degree-torsion
subgroup. -/
def ARData.relativeInvariantTorsion
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ}
    (data : ARData
      relative absoluteK absoluteL degree) :
    relative →+ localInvariantTorsion degree :=
  data.relativeInvariant.codRestrict (localInvariantTorsion degree) fun x ↦ by
    change data.relativeInvariant x ∈
      (localInvariantTorsion degree : Set LocalInvariant)
    rw [← data.range_relativeInvariant]
    exact Set.mem_range_self x

/-- The restricted relative invariant is bijective. -/
theorem ARData.relative_inv_torsionbij
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ}
    (data : ARData
      relative absoluteK absoluteL degree) :
    Function.Bijective data.relativeInvariantTorsion := by
  constructor
  · intro x y hxy
    apply data.relativeInvariant_injective
    exact congrArg Subtype.val hxy
  · intro x
    have hx : (x : LocalInvariant) ∈
        Set.range data.relativeInvariant := by
      rw [data.range_relativeInvariant]
      exact x.property
    obtain ⟨gamma, hgamma⟩ := hx
    exact ⟨gamma, Subtype.ext hgamma⟩

/-- The canonical finite relative invariant obtained from the absolute
restriction sequence, now expressed in the `ZMod degree` form used by
Theorem VIII.4.7. -/
def ARData.relative_inv_addequiv
    {relative : Type u} {absoluteK : Type v} {absoluteL : Type w}
    [AddCommGroup relative] [AddCommGroup absoluteK]
    [AddCommGroup absoluteL] {degree : ℕ} [NeZero degree]
    (data : ARData
      relative absoluteK absoluteL degree) :
    relative ≃+ ZMod degree :=
  (AddEquiv.ofBijective data.relativeInvariantTorsion
      data.relative_inv_torsionbij).trans
    (torsionZMod degree).symm

/-- The exact missing construction in the printed proof of Theorem 4.7:
absolute cohomology, the two global invariants, and their restriction
sequence satisfying Lemma 4.6. -/
def AbsoluteInvariantBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ∃ (absoluteK absoluteL : Type u)
      (_ : AddCommGroup absoluteK) (_ : AddCommGroup absoluteL),
      Nonempty (ARData
        (RelativeIdele2 K L) absoluteK absoluteL
        (Module.finrank K L))

/-- The absolute invariant construction gives the narrower invariant bridge
previously used to package Theorem VIII.4.7. -/
theorem invariant_bridge_absolute
    (hAbsolute : AbsoluteInvariantBridge.{u}) :
    InvariantBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨absoluteK, absoluteL, instK, instL, ⟨data⟩⟩ := hAbsolute K L
  letI : AddCommGroup absoluteK := instK
  letI : AddCommGroup absoluteL := instL
  letI : NeZero (Module.finrank K L) :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  exact ⟨data.relative_inv_addequiv⟩

/-- **Theorem VIII.4.7 from the preceding absolute-invariant argument.** -/
theorem absolute_invariant
    (hAbsolute : AbsoluteInvariantBridge.{u}) :
    RelativeInvariantGenerator.{u} :=
  of_invariant
    (invariant_bridge_absolute hAbsolute)

end

end Towers.CField.GClass
