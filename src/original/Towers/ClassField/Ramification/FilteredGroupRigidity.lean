import Towers.ClassField.Ramification.UpperRamification

/-!
# Class Field Theory, Chapter I, Lemma 4.9: filtered-group rigidity

This file formalizes the group- and index-theoretic final part of Milne's
proof.  Quotient compatibility and the snake lemma supply an index
factorization.  The sharp bound on a ramification step forces the intersection
with the kernel to remain unchanged; separatedness of the filtration then
forces that kernel to be trivial.
-/

namespace Towers.CField.Ramification

/-- If an index factors as `b * c` but is at most `b`, positivity forces the
remaining intersection index `c` to equal one. -/
theorem rel_inf_factor
    {G Q : Type*} [Group G] [Group Q]
    (A B : Subgroup G) (Aq Bq : Subgroup Q) (H : Subgroup G)
    (hpos : 0 < A.relIndex B)
    (hfactor : A.relIndex B =
      Aq.relIndex Bq * (A ⊓ H).relIndex (B ⊓ H))
    (hbound : A.relIndex B ≤ Aq.relIndex Bq) :
    (A ⊓ H).relIndex (B ⊓ H) = 1 := by
  have hmulpos :
      0 < Aq.relIndex Bq * (A ⊓ H).relIndex (B ⊓ H) := by
    rwa [← hfactor]
  have hbpos : 0 < Aq.relIndex Bq :=
    pos_of_mul_pos_left hmulpos (Nat.zero_le _)
  have hcpos : 0 < (A ⊓ H).relIndex (B ⊓ H) :=
    pos_of_mul_pos_right hmulpos (Nat.zero_le _)
  have hmul : Aq.relIndex Bq * (A ⊓ H).relIndex (B ⊓ H) ≤
      Aq.relIndex Bq * 1 := by
    simpa [hfactor] using hbound
  have hle : (A ⊓ H).relIndex (B ⊓ H) ≤ 1 :=
    le_of_mul_le_mul_left hmul hbpos
  omega

/-- The filtered-group core of Lemma 4.9.  If each upper-ramification step
has the quotient/intersection index factorization and the quotient already
accounts for the whole possible index, then a subgroup meeting every step in
the same way is trivial once the filtration is separated. -/
theorem bot_filtered_rigidity
    {G Q : Type*} [Group G] [Group Q]
    (upperG : ℕ → Subgroup G) (upperQ : ℕ → Subgroup Q)
    (H : Subgroup G)
    (hanti : Antitone upperG)
    (hzero : upperG 0 = ⊤)
    (hsep : ⨅ n, upperG n = ⊥)
    (hstepPos : ∀ n, 0 < (upperG (n + 1)).relIndex (upperG n))
    (hfactor : ∀ n,
      (upperG (n + 1)).relIndex (upperG n) =
        (upperQ (n + 1)).relIndex (upperQ n) *
          ((upperG (n + 1) ⊓ H).relIndex (upperG n ⊓ H)))
    (hbound : ∀ n,
      (upperG (n + 1)).relIndex (upperG n) ≤
        (upperQ (n + 1)).relIndex (upperQ n)) :
    H = ⊥ := by
  have hinter : ∀ n, upperG n ⊓ H = H := by
    intro n
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
        have hindex :
            (upperG (n + 1) ⊓ H).relIndex (upperG n ⊓ H) = 1 :=
          rel_inf_factor
            (upperG (n + 1)) (upperG n)
            (upperQ (n + 1)) (upperQ n) H
            (hstepPos n) (hfactor n) (hbound n)
        have hforward : upperG (n + 1) ⊓ H ≤ upperG n ⊓ H :=
          inf_le_inf_right H (hanti (Nat.le_succ n))
        have hbackward : upperG n ⊓ H ≤ upperG (n + 1) ⊓ H :=
          Subgroup.relIndex_eq_one.mp hindex
        exact (le_antisymm hforward hbackward).trans ih
  apply le_antisymm
  · intro x hx
    have hxinf : x ∈ ⨅ n, upperG n := by
      rw [Subgroup.mem_iInf]
      intro n
      have hxinter : x ∈ upperG n ⊓ H := by
        rw [hinter n]
        exact hx
      exact hxinter.1
    rw [hsep] at hxinf
    exact hxinf
  · exact bot_le

end Towers.CField.Ramification
