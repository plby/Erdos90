import Towers.Group.Zassenhaus.IntegralStrictTail

/-!
# Hall-address support for signed-leaf Hall-Witt strict tails

Signed leaves remove the visible-commutator restriction from Hall-Witt
substitution.  This file records the corresponding physical Hall-weight and
lower-central support bounds over `HEAddres`.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace SLAddres

open CWTrace
open WSTrace
open STSubsti
open STMultid
open SLSubsti

universe u

/-- Signed-leaf substitution carries exactly the unsigned weighted
multidegree. -/
lemma signed_leaf_substitution
    {β : Type*}
    (wt : β → ℕ)
    (x y z : CWord β)
    (atom : Atom) :
    (signedLeafSubstitution x y z atom).weight (SLeaf.weight wt) =
      signedWeight (x.weight wt) (y.weight wt) (z.weight wt) atom := by
  rcases atom with atom | atom
  · refine Fin.cases ?_ (fun atom => ?_) atom
    · change
        (signedLeafSubstitution x y z xAtom).weight
            (SLeaf.weight wt) =
          signedWeight (x.weight wt) (y.weight wt) (z.weight wt) xAtom
      rw [leaf_substitution_x, weight_positiveWord, signedWeight_x]
    · refine Fin.cases ?_ (fun atom => ?_) atom
      · change
          (signedLeafSubstitution x y z xInvAtom).weight
              (SLeaf.weight wt) =
            signedWeight (x.weight wt) (y.weight wt) (z.weight wt) xInvAtom
        rw [leaf_substitution_inv, weight_inverseWord,
          signed_x_inv]
      · refine Fin.cases ?_ (fun atom => ?_) atom
        · change
            (signedLeafSubstitution x y z zAtom).weight
                (SLeaf.weight wt) =
              signedWeight (x.weight wt) (y.weight wt) (z.weight wt) zAtom
          rw [signed_leaf_z, weight_positiveWord,
            signedWeight_z]
        · exact
            Fin.cases
              (by
                change
                  (signedLeafSubstitution x y z zInvAtom).weight
                      (SLeaf.weight wt) =
                    signedWeight (x.weight wt) (y.weight wt) (z.weight wt)
                      zInvAtom
                rw [leaf_substitution_z, weight_inverseWord,
                  signed_z_inv])
              (fun atom => Fin.elim0 atom) atom
  · refine Fin.cases ?_ (fun atom => ?_) atom
    · change
        (signedLeafSubstitution x y z yAtom).weight
            (SLeaf.weight wt) =
          signedWeight (x.weight wt) (y.weight wt) (z.weight wt) yAtom
      rw [signed_leaf_y, weight_positiveWord, signedWeight_y]
    · exact
        Fin.cases
          (by
            change
              (signedLeafSubstitution x y z yInvAtom).weight
                  (SLeaf.weight wt) =
                signedWeight (x.weight wt) (y.weight wt) (z.weight wt)
                  yInvAtom
            rw [leaf_substitution_y, weight_inverseWord,
              signed_y_inv])
          (fun atom => Fin.elim0 atom) atom

/--
Every signed-leaf substituted strict-tail factor lies at least one physical
weight above its parent triple.
-/
lemma parent_leaf_strict
    {β : Type*}
    (wt : β → ℕ)
    (hwt : ∀ atom, 0 < wt atom)
    (x y z : CWord β)
    (coefficient : ℤ)
    (word : CWord (SLeaf β))
    (hword : word ∈ signedLeafStrict x y z coefficient) :
    x.weight wt + y.weight wt + z.weight wt + 1 ≤
      word.weight (SLeaf.weight wt) := by
  rw [signedLeafStrict, bindTrace] at hword
  rcases List.mem_map.mp hword with ⟨sourceWord, hsourceWord, rfl⟩
  rw [CWord.weight_bind]
  change
    x.weight wt + y.weight wt + z.weight wt + 1 ≤
      sourceWord.weight
        (fun atom =>
          (signedLeafSubstitution x y z atom).weight
            (SLeaf.weight wt))
  rw [show
      (fun atom =>
        (signedLeafSubstitution x y z atom).weight
          (SLeaf.weight wt)) =
        signedWeight (x.weight wt) (y.weight wt) (z.weight wt) by
      funext atom
      exact signed_leaf_substitution wt x y z atom]
  exact
    parent_strictly_higher
      (x.weight wt) (y.weight wt) (z.weight wt)
      (CWord.weight_pos wt hwt x)
      (CWord.weight_pos wt hwt y)
      (CWord.weight_pos wt hwt z)
      sourceWord
      (strictly_higher_strict coefficient sourceWord hsourceWord)

/-- Signed Hall-address leaves have positive physical weight. -/
lemma leaf_address_pos
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    ∀ atom : SLeaf (HEAddres H),
      0 < SLeaf.weight PEAddres.weight atom
  | .positive atom => PEAddres.weight_pos atom
  | .negative atom => PEAddres.weight_pos atom

/-- Signed Hall-address leaves evaluate in their selected lower-central
term. -/
lemma leaf_truncation_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    ∀ atom : SLeaf (HEAddres H),
      SLeaf.eval
          (PEAddres.freeLowerTruncation (n := n))
          atom ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (SLeaf.weight PEAddres.weight atom - 1)
  | .positive atom =>
      PEAddres.free_truncation_series
        atom
  | .negative atom =>
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (PEAddres.weight atom - 1)).inv_mem
          (PEAddres.free_truncation_series
            atom)

/-- Every Hall-address signed-leaf strict factor evaluates in the next
lower-central layer above its parent triple. -/
lemma leaf_strict_trace
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y z : CWord (HEAddres H))
    (coefficient : ℤ)
    (word : CWord (SLeaf (HEAddres H)))
    (hword : word ∈ signedLeafStrict x y z coefficient) :
    word.eval
          (SLeaf.eval
            (PEAddres.freeLowerTruncation
              (n := n))) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.weight PEAddres.weight +
            y.weight PEAddres.weight +
          z.weight PEAddres.weight) := by
  have heval :=
    CWord.eval_lower_series
      (SLeaf.eval
        (PEAddres.freeLowerTruncation (n := n)))
      (SLeaf.weight PEAddres.weight)
      leaf_address_pos
      leaf_truncation_series
      word
  exact
    Subgroup.lowerCentralSeries_antitone
      (by
        have hweight :=
          parent_leaf_strict
            PEAddres.weight
            PEAddres.weight_pos x y z coefficient word hword
        omega)
      heval

/-- The complete Hall-address signed-leaf strict trace evaluates in the next
lower-central layer above its parent triple. -/
lemma leaf_strict_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y z : CWord (HEAddres H))
    (coefficient : ℤ) :
    wordListEval
          (SLeaf.eval
            (PEAddres.freeLowerTruncation
              (n := n)))
          (signedLeafStrict x y z coefficient) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.weight PEAddres.weight +
            y.weight PEAddres.weight +
          z.weight PEAddres.weight) := by
  apply Subgroup.list_prod_mem
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨word, hword, rfl⟩
  exact
    leaf_strict_trace
      x y z coefficient word hword

/-- The explicit Jacobi residual evaluates in its next lower-central layer
without visible-commutator hypotheses on the compressed branches. -/
lemma jacobi_zpow_residual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y z : CWord (HEAddres H))
    (coefficient : ℤ) :
    ((CWord.commutator (.commutator x y) z).eval
          (PEAddres.freeLowerTruncation (n := n))
        )⁻¹ ^ coefficient *
        ((CWord.commutator (.commutator x z) y).eval
              (PEAddres.freeLowerTruncation
                (n := n)) ^
            coefficient *
          ((CWord.commutator (.commutator y z) x).eval
                (PEAddres.freeLowerTruncation
                  (n := n)))⁻¹ ^
            coefficient) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.weight PEAddres.weight +
            y.weight PEAddres.weight +
          z.weight PEAddres.weight) := by
  rw [← signed_leaf_strict
    (PEAddres.freeLowerTruncation (n := n))
      x y z coefficient]
  exact
    leaf_strict_series
      x y z coefficient

end SLAddres
end TCTex
end Towers
