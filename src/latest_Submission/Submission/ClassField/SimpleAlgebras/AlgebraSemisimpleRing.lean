import Submission.ClassField.SimpleAlgebras.MatrixDivisionAlgebra

/-!
# Milne, Class Field Theory, Proposition IV.1.18

Finite-dimensional simple algebras are semisimple rings.
-/

namespace Submission.CField.SAlgebr

universe u v

/-- **Proposition IV.1.18.** A finite-dimensional simple algebra is
semisimple. -/
theorem simple_semisimple_ring
    (k : Type u) (A : Type v)
    [Field k] [Ring A] [Algebra k A]
    [Module.Finite k A] [IsSimpleRing A] :
    IsSemisimpleRing A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  infer_instance

end Submission.CField.SAlgebr
