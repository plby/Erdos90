import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Milne, Chapter 8, Proposition 8.13(a)

In a tower, the decomposition group over the intermediate field is the
intersection of the full decomposition group with the subgroup fixing the
intermediate field.  This is a general fact about restricting a group action
to a subgroup.
-/

namespace Towers.NumberTheory.Milne

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The stabilizer for the restricted subgroup action is the comap of the
full stabilizer. -/
theorem stabilizer_subgroup_comap (H : Subgroup G) (x : X) :
    stabilizer H x = (stabilizer G x).comap H.subtype :=
  rfl

/-- Milne, Proposition 8.13(a): viewed inside the ambient group, the
decomposition group over the intermediate field is `H ∩ G(P)`. -/
theorem stabilizer_subgroup_inf (H : Subgroup G) (x : X) :
    (stabilizer H x).map H.subtype = H ⊓ stabilizer G x := by
  ext g
  simp [mem_stabilizer_iff, and_comm]

/-- Milne, Proposition 8.13(b), in its group-action form.  When `H` is
normal, the image of the stabilizer of `x` in `G ⧸ H` consists exactly of
the cosets whose representatives preserve the `H`-orbit of `x`. -/
theorem mk_stabilizer_orbit
    (H : Subgroup G) [H.Normal] (x : X) (g : G) :
    QuotientGroup.mk' H g ∈
        (stabilizer G x).map (QuotientGroup.mk' H) ↔
      (Quotient.mk'' (g • x) : orbitRel.Quotient H X) = Quotient.mk'' x := by
  constructor
  · rintro ⟨s, hs, hsg⟩
    obtain ⟨h, hhH, rfl⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := H)).mp hsg
    apply Quotient.sound'
    rw [orbitRel_apply]
    let h' : H :=
      ⟨s * h * s⁻¹, (inferInstance : H.Normal).conj_mem h hhH s⟩
    refine ⟨h', ?_⟩
    have hsfix : s • x = x := mem_stabilizer_iff.mp hs
    have hsinv : s⁻¹ • x = x := inv_smul_eq_iff.mpr hsfix.symm
    change (s * h * s⁻¹) • x = (s * h) • x
    simp only [mul_smul, hsinv]
  · intro horbit
    have hrel : orbitRel H X (g • x) x := Quotient.exact horbit
    obtain ⟨h, hh⟩ := (orbitRel_apply.mp hrel)
    refine ⟨(h : G)⁻¹ * g, ?_, ?_⟩
    · change ((h : G)⁻¹ * g) • x = x
      rw [mul_smul]
      have hh' : (h : G) • x = g • x := hh
      have hsmul := congrArg (fun y : X ↦ (h : G)⁻¹ • y) hh'
      simpa only [inv_smul_smul] using hsmul.symm
    · have hh_one : QuotientGroup.mk' H (h : G) = 1 :=
        (QuotientGroup.eq_one_iff (h : G)).mpr h.prop
      change (QuotientGroup.mk' H (h : G))⁻¹ * QuotientGroup.mk' H g =
        QuotientGroup.mk' H g
      rw [hh_one]
      simp

/-- Milne, Proposition 8.13(b): after quotienting by a normal subgroup `H`,
the image of the original stabilizer consists exactly of the quotient elements
whose representatives preserve the `H`-orbit of `x`.  For the action on
primes, this is the decomposition group of the contracted prime. -/
theorem coe_stabilizer_orbit
    (H : Subgroup G) [H.Normal] (x : X) :
    ((stabilizer G x).map (QuotientGroup.mk' H) : Set (G ⧸ H)) =
      {q | ∃ g : G, QuotientGroup.mk' H g = q ∧
        (Quotient.mk'' (g • x) : orbitRel.Quotient H X) = Quotient.mk'' x} := by
  ext q
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    exact ⟨g, rfl,
      (mk_stabilizer_orbit H x g).mp hq⟩
  · rintro ⟨g, rfl, hg⟩
    exact (mk_stabilizer_orbit H x g).mpr hg

/-- The normal decomposition group has trivial image after passing to its
quotient.  Together with Proposition 8.13(b), this is the group-theoretic
step that turns the normality hypothesis in Proposition 8.11(d) into a
trivial decomposition group, and hence complete splitting in the
decomposition field. -/
theorem stabilizer_mk_bot
    (x : X) [(stabilizer G x).Normal] :
    (stabilizer G x).map (QuotientGroup.mk' (stabilizer G x)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- Milne, formula 8.14 for decomposition groups: the group at a conjugate
prime is the conjugate of the original decomposition group. -/
theorem decomposition_smul_conjugate (g : G) (x : X) :
    stabilizer G (g • x) =
      (stabilizer G x).map (MulAut.conj g).toMonoidHom :=
  stabilizer_smul_eq_stabilizer_map_conj g x

end Towers.NumberTheory.Milne
