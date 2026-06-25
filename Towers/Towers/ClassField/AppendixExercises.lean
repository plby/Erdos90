import Towers.ClassField.QuadraticForms.ExponentCommutativity
import Towers.ClassField.ReciprocityExistence.CubicConstruction
import Towers.ClassField.RayClassGroups.PrescribedPrimeFields
import Towers.ClassField.Ideles.DenseProperSubgroups
import Towers.ClassField.CohomologyOps.NonabelianFirstCohomology
import Towers.ClassField.TateCohomology.Verlagerung
import Towers.ClassField.CohomologyOps.PrincipalCocycles
import Towers.ClassField.SimpleAlgebras.QuaternionNormCalculations
import Towers.ClassField.LocalFields.ShiftedCyclotomicEisenstein
import Towers.ClassField.ChebotarevDensity.CyclicResidueDegree
import Towers.ClassField.LocalGlobalPowers.ExceptionalEighthPower

/-!
# Appendix: exercises

The imports follow Exercises A-1 through A-11 in source order.  Algebraic,
topological, representation-theoretic, cyclotomic, density, and explicit power
claims are formalized; in particular, all three parts of A-11 are proved,
including the odd `p`-adic assertion by quadratic characters and Hensel lifting.
Exercises requiring the global class-field existence
theorem, ray ideal groups, completed cyclotomic norm compatibility, semilinear
Galois descent, or continuous cohomology of profinite inverse limits document
those exact library boundaries in their corresponding modules.

The computation requested in A-2(b) is omitted as computation-heavy, in
accordance with the project instructions.
-/
