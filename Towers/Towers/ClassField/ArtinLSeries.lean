import Towers.ClassField.ArtinLSeries.DirichletFunctionalEquation
import Towers.ClassField.ArtinLSeries.ArtinRepresentations
import Towers.ClassField.ArtinLSeries.AbelianRepresentations
import Towers.ClassField.ArtinLSeries.SquareSumIdentity
import Towers.ClassField.ArtinLSeries.EisensteinHeckeCharacter
import Towers.ClassField.ArtinLSeries.FermatCubicCount
import Towers.ClassField.ArtinLSeries.GaussCoefficientUniqueness
import Towers.ClassField.ArtinLSeries.GaussNonsplitCount
import Towers.ClassField.ArtinLSeries.GaussSplitCount
import Towers.ClassField.ArtinLSeries.GaussBound

/-!
# Chapter VIII, Section 10: more on L-series

The imports follow the section linearly.  Mathlib supplies the functional
equation for primitive Dirichlet characters and the finite-dimensional
representation theory used in the Artin discussion.  Arithmetic Artin and
Hecke Euler products, induction formulae, and the analytic continuation
conjectures are not currently represented by the available APIs.

For Example 10.1, the integral normalization `4p = A² + 27B²` is proved, and
the Hecke-character assertion is stated on the actual idèle class group with
its unavailable local and global constructions isolated as narrow bridges.
The source's split-case point-count formula omits its `p + 1` term;
`GaussSourceStatement` gives the corrected theorem an exact finite model.
`GaussCoefficientUniqueness` proves uniqueness of the normalized coefficient
using Eisenstein unique factorization.  `GaussNonsplitPointCount` proves the
nonsplit count `Nₚ = p + 1` directly, and `GaussSplitPointCount` proves the
split formula by cubic characters and Jacobi sums.  Thus the corrected Gauss
theorem and its elementary Weil-bound consequence are both unconditional.
-/
