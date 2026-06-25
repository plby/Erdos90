import Towers.ClassField.BrauerDimension.FiniteProductRing
import Towers.ClassField.BrauerDimension.FinitePowerEndomorphism
import Towers.ClassField.BrauerDimension.CentralizerAlgRing
import Towers.ClassField.BrauerDimension.SemisimpleAlgRing
import Towers.ClassField.BrauerDimension.EveryModuleSemisimple
import Towers.ClassField.BrauerDimension.ScalarCentralSimple

/-!
# Milne, Class Field Theory, Chapter IV, Section 5

The first half of this section is Artin-Wedderburn theory. Mathlib already
contains the general semisimple-module and isotypic-component machinery, so
the local files expose the exact consequences used by Milne:

* finite products of finite-dimensional simple algebras are semisimple;
* endomorphisms of a finite direct power form a matrix algebra;
* the endomorphism algebra of a finite semisimple module is a product of
  matrix algebras over division algebras;
* every finite-dimensional semisimple algebra has such a product
  decomposition;
* every module over a semisimple ring is semisimple, and finite modules are
  finite direct sums of simple submodules;
* scalar extension preserves semisimplicity for each central simple factor.

The general form of Proposition 5.6 requires a tensor-product decomposition
over the possibly nontrivial centres of the simple factors. That API is not
currently packaged in Mathlib; `Proposition56` records the central-simple
case supplied by `BGroups.Proposition215`.
-/
