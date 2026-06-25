import Submission.Group.NilpotentProducts.GeneralLaw


/-!
# The triangular change from equation (29) to equation (18)

The replacement commutators in Theorem 4 satisfy
`(aᵢ²,aⱼ) = (aᵢ,aⱼ)² ((aᵢ,aⱼ),aᵢ)` and similarly on the right.
Consequently the ordinary pair coordinate is Struik's
`α(cᵢⱼ) = cᵢⱼ + 2cᵢⱼ⁽²⁾ + 2cᵢⱼ⁽³⁾`.
-/

namespace Struik
namespace P1960

/-- Replace the three equation-(29) pair coordinates by the ordinary
equation-(18) pair and triple coordinates. -/
def toGeneralResidues {t : ℕ}
    (c : ELCoordi t) : GCoordi t where
  single := c.single
  pair q := ELCoordi.alpha c q
  pairLeft := c.pairLeftSquare
  pairRight := c.pairRightSquare
  tripleFirst := c.tripleFirst
  tripleSecond := c.tripleSecond

/-- The inverse triangular change of coordinates. -/
def generalExceptionalResidues {t : ℕ}
    (c : GCoordi t) : ELCoordi t where
  single := c.single
  pair q := c.pair q - 2 * c.pairLeft q - 2 * c.pairRight q
  pairLeftSquare := c.pairLeft
  pairRightSquare := c.pairRight
  tripleFirst := c.tripleFirst
  tripleSecond := c.tripleSecond

@[simp] theorem exceptional_residues_inverse
    {t : ℕ} (c : ELCoordi t) :
    generalExceptionalResidues (toGeneralResidues c) = c := by
  ext <;>
    simp [generalExceptionalResidues, toGeneralResidues,
      ELCoordi.alpha] ;
    ring

@[simp] theorem exceptional_general_residues
    {t : ℕ} (c : GCoordi t) :
    toGeneralResidues (generalExceptionalResidues c) = c := by
  ext <;>
    simp [generalExceptionalResidues, toGeneralResidues,
      ELCoordi.alpha] ;
    ring

theorem general_residues_mul
    {t : ℕ} (c d : ELCoordi t) :
    toGeneralResidues (ELCoordi.mul c d) =
      GCoordi.mul
        (toGeneralResidues c)
        (toGeneralResidues d) := by
  ext <;>
    simp [toGeneralResidues, ELCoordi.mul,
      ELCoordi.alpha, GCoordi.mul,
      Triple.ij, Triple.ik, Triple.jk] <;>
    ring

/-- Equations (18) and (29) define isomorphic integral coordinate
groups. -/
noncomputable def mulGeneralResidues (t : ℕ) :
    ELCoordi t ≃* GCoordi t where
  toFun := toGeneralResidues
  invFun := generalExceptionalResidues
  left_inv := exceptional_residues_inverse
  right_inv := exceptional_general_residues
  map_mul' := general_residues_mul

end P1960
end Struik
