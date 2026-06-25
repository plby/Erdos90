import Mathlib.Topology.Instances.AddCircle.Defs
import Towers.ClassField.LocalBrauer.DivisionAlgebraInvariant

/-!
# Chapter IV, Section 4: finite torsion in the local invariant group

For every positive `n`, the subgroup of `ℚ/ℤ` killed by `n` is canonically
isomorphic to `ZMod n`: the residue class of `m` is sent to `m / n` modulo
integers.  These are the finite targets occurring in the unramified
calculation of Proposition IV.4.3.
-/

namespace Towers.CField.LBrauer

noncomputable section

/-- The `n`-torsion subgroup of the local invariant group `ℚ/ℤ`. -/
def localInvariantTorsion (n : ℕ) : AddSubgroup LocalInvariant :=
  (nsmulAddMonoidHom n : LocalInvariant →+ LocalInvariant).ker

@[simp]
theorem local_invariant_torsion (n : ℕ) (x : LocalInvariant) :
    x ∈ localInvariantTorsion n ↔ n • x = 0 :=
  Iff.rfl

/-- The residue class of `m` modulo `n` maps to `m / n` modulo integers. -/
noncomputable def zmodLocalInvariant (n : ℕ) [NeZero n] :
    ZMod n →+ LocalInvariant :=
  ZMod.lift n
    ⟨AddMonoidHom.mk' (fun m : ℤ ↦ ((m : ℚ) / (n : ℚ) : LocalInvariant))
      (by intros; simp [add_div]), by
        have hn : (n : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
        simp [hn]⟩

theorem zmod_int_cast (n : ℕ) [NeZero n] (m : ℤ) :
    zmodLocalInvariant n (m : ZMod n) =
      ((m : ℚ) / (n : ℚ) : LocalInvariant) := by
  simp [zmodLocalInvariant]

theorem zmod_invariant_cast (n : ℕ) [NeZero n] (m : ℕ) :
    zmodLocalInvariant n (m : ZMod n) =
      ((m : ℚ) / (n : ℚ) : LocalInvariant) := by
  simpa using zmod_int_cast n (m : ℤ)

/-- Explicit representative formula, used only to prove injectivity. -/
theorem zmod_local_invariant (n : ℕ) [NeZero n] (m : ZMod n) :
    zmodLocalInvariant n m =
      ((m.val : ℚ) / (n : ℚ) : LocalInvariant) := by
  rw [← zmod_invariant_cast, ZMod.natCast_zmod_val]

theorem zmod_invariant_injective (n : ℕ) [NeZero n] :
    Function.Injective (zmodLocalInvariant n) := by
  intro x y hxy
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hxIco : (x.val : ℚ) / (n : ℚ) ∈ Set.Ico 0 (0 + 1) :=
    ⟨by positivity,
      by simpa only [zero_add, div_lt_one hn, Nat.cast_lt] using ZMod.val_lt x⟩
  have hyIco : (y.val : ℚ) / (n : ℚ) ∈ Set.Ico 0 (0 + 1) :=
    ⟨by positivity,
      by simpa only [zero_add, div_lt_one hn, Nat.cast_lt] using ZMod.val_lt y⟩
  rw [zmod_local_invariant, zmod_local_invariant,
    AddCircle.coe_eq_coe_iff_of_mem_Ico hxIco hyIco,
    div_left_inj' hn.ne', Nat.cast_inj, (ZMod.val_injective n).eq_iff] at hxy
  exact hxy

/-- The preceding map, with codomain restricted to the `n`-torsion subgroup. -/
noncomputable def zmodInvariantTorsion (n : ℕ) [NeZero n] :
    ZMod n →+ localInvariantTorsion n :=
  (zmodLocalInvariant n).codRestrict (localInvariantTorsion n) fun x ↦ by
    change n • zmodLocalInvariant n x = 0
    rw [← map_nsmul]
    simp

theorem zmod_torsion_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (zmodInvariantTorsion n) := by
  constructor
  · intro x y hxy
    apply zmod_invariant_injective n
    exact congrArg Subtype.val hxy
  · intro x
    obtain ⟨m, hm, hx⟩ :=
      (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) (NeZero.pos n)).mp x.property
    refine ⟨(m : ZMod n), Subtype.ext ?_⟩
    change zmodLocalInvariant n (m : ZMod n) = x.1
    rw [zmod_invariant_cast]
    simpa using hx

/-- Canonical identification of `ZMod n` with the subgroup of `ℚ/ℤ` killed
by `n`. -/
noncomputable def torsionZMod (n : ℕ) [NeZero n] :
    ZMod n ≃+ localInvariantTorsion n :=
  AddEquiv.ofBijective (zmodInvariantTorsion n)
    (zmod_torsion_bijective n)

@[simp]
theorem torsion_z_coe
    (n : ℕ) [NeZero n] (m : ZMod n) :
    ((torsionZMod n m : localInvariantTorsion n) :
        LocalInvariant) = zmodLocalInvariant n m :=
  rfl

end

end Towers.CField.LBrauer
