import Submission.ClassField.Characters.DirichletCharacters
import Submission.ClassField.Characters.ZetaRegularPart
import Submission.ClassField.Characters.HasDirichletDensity
import Submission.ClassField.Characters.DedekindResidueFormula

/-!
# Milne, Class Field Theory, Chapter V, Section 2

This section records Dirichlet characters, their Euler products, the
analytic continuation and nonvanishing portions of Theorem 2.1, the
definition of Dirichlet density, Dirichlet's infinitude theorem as the
currently formalized consequence of Theorem 2.2, and the analytic
class-number formula of Theorem 2.4(a).

The exact density `1 / phi(m)` in Theorem 2.2, its cyclotomic corollary 2.3,
and the general ray-class character statements in Theorems 2.4(b) and 2.5
are not currently packaged in Mathlib.  They require analytic estimates for
prime reciprocal-power sums and a theory of ray-class `L`-functions beyond
the available Dirichlet-character development.
-/
