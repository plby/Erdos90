import Towers.Group.HallBasic.FreeNilpotentTorsion
import Towers.Group.Edmonton.CommutatorIdentities
import Towers.Group.Edmonton.HallCommutatorIdentities
import Towers.Group.Edmonton.HallEmbeddings

/-!
# Struik (1960), preliminary commutator results

This file begins the formalization of Ruth Rebekka Struik,
*On Nilpotent Products of Cyclic Groups*, Canadian Journal of Mathematics
12 (1960), 447--462.

The paper uses Hall's commutator convention
`(x,y) = x⁻¹ y⁻¹ x y`; this is `Towers.Edmonton.hallCommutator`.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex

universe u

variable {G : Type u} [Group G]

/-- Struik (1), first identity:
`(xy,z) = (x,z) ((x,z),y) (y,z)`. -/
theorem commutatorIdentitiesFirst (x y z : G) :
    hallCommutator (x * y) z =
      hallCommutator x z *
        hallCommutator (hallCommutator x z) y *
          hallCommutator y z := by
  simp [hallCommutator, mul_assoc]

/-- Struik (1), second identity:
`(x,yz) = (x,z) (z,(y,x)) (x,y)`. -/
theorem commutatorIdentitiesSecond (x y z : G) :
    hallCommutator x (y * z) =
      hallCommutator x z *
        hallCommutator z (hallCommutator y x) *
          hallCommutator x y := by
  simp [hallCommutator, mul_assoc]

/-- The two identities displayed together as Struik's equation (1). -/
theorem commutatorIdentities (x y z : G) :
    hallCommutator (x * y) z =
        hallCommutator x z *
          hallCommutator (hallCommutator x z) y *
            hallCommutator y z ∧
      hallCommutator x (y * z) =
        hallCommutator x z *
          hallCommutator z (hallCommutator y x) *
            hallCommutator x y :=
  ⟨commutatorIdentitiesFirst x y z, commutatorIdentitiesSecond x y z⟩

/-- The existence-and-uniqueness part of Struik's Theorem H1, for the
canonical Hall family in the free nilpotent group of rank `d` and cutoff
`n`. -/
theorem commutatorIdentitiesForm
    (d n : ℕ)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : StandardExponentFamily.{u} d,
      standardHallProduct d n e = y ∧
        ∀ f : StandardExponentFamily.{u} d,
          standardHallProduct d n f = y →
          ∀ r : ℕ, 1 ≤ r → r < n → f r = e r :=
  unique_hall_coordinates d n y

/-- The final tuple-group clause of Struik's Theorem H1, in the same standard
Hall coordinates as `commutatorIdentitiesForm`.  Coordinates outside the
represented weights are fixed to zero. -/
noncomputable def identitiesStandardTuple
    (d n : ℕ) :
    StandardCoordinateTuple.{u} d n ≃*
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  standardCoordinateTuple d n

/-- The standard Hall coordinate tuples in Theorem H1 form a nilpotent
group. -/
theorem identities_tuple_nilpotent
    (d n : ℕ) :
    Group.IsNilpotent (StandardCoordinateTuple.{u} d n) :=
  Group.nilpotent_of_mulEquiv
    (identitiesStandardTuple d n).symm

/-- The polynomial multiplication clause of Struik's Theorem H1, in Hall
canonical coordinates.  Each output coordinate is represented by a
compositional expression built from integer constants, coordinate variables,
ring operations, and binomial coefficients. -/
theorem identities_multiplication_expression
    {m : ℕ}
    (b : HCBasis G m)
    (i : Fin m) :
    ∃ p : BExpr (Sum (Fin m) (Fin m)),
      ∀ (c d : Fin m → ℤ),
        BExpr.eval (Sum.elim c d) p =
          b.coord (b.coord.symm c * b.coord.symm d) i := by
  obtain ⟨p, hp⟩ :=
    (HCBasis.canonical_coordinate_expressions b).1 i
  refine ⟨p, fun c d => ?_⟩
  simpa [canonicalMulCoordinate] using hp (Sum.elim c d)

/-- The polynomial multiplication clause of Theorem H1 with the canonical
basis chosen internally for an arbitrary finitely generated torsion-free
nilpotent group. -/
theorem commutator_identities_coordinates
    [Group.FG G] [Group.IsNilpotent G] [IsMulTorsionFree G] :
    ∃ m : ℕ, ∃ b : HCBasis G m,
      ∀ i : Fin m,
        ∃ p : BExpr (Sum (Fin m) (Fin m)),
          ∀ (c d : Fin m → ℤ),
            BExpr.eval (Sum.elim c d) p =
              b.coord (b.coord.symm c * b.coord.symm d) i := by
  obtain ⟨m, ⟨b⟩⟩ :=
    Towers.Edmonton.HCBasis.fg_torsion_nilpotent
      (G := G)
  exact
    ⟨m, b, fun i =>
      identities_multiplication_expression b i⟩

/-- The full multiplication-coordinate clause of Theorem H1 for the free
nilpotent group of rank `d` and cutoff `n`, with no supplied basis or
torsion-freeness hypothesis. -/
theorem identities_free_coordinates
    (d n : ℕ) :
    ∃ m : ℕ,
      ∃ b :
          HCBasis
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) m,
        ∀ i : Fin m,
          ∃ p : BExpr (Sum (Fin m) (Fin m)),
            ∀ (c e : Fin m → ℤ),
              BExpr.eval (Sum.elim c e) p =
                b.coord (b.coord.symm c * b.coord.symm e) i :=
  commutator_identities_coordinates
    (G := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)

/-- The cyclic triple-commutator relation used in the proof of Theorem 1.
In a metabelian group it is an equality; applying it to a quotient by the
fourth lower-central term gives Struik's congruence modulo `G₄`. -/
theorem cyclic_triple_commutator
    (hG : Towers.Edmonton.Group.IsMetabelian G)
    (x y z : G) :
    hallTripleCommutator x y z *
        hallTripleCommutator z x y *
          hallTripleCommutator y z x =
      1 :=
  hall_witt_metabelian hG x y z

end P1960
end Struik
