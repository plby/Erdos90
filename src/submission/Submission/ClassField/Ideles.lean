import Submission.ClassField.Ideles.Ideles
import Submission.ClassField.Ideles.FinitePlaceCompletion
import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.Ideles.IdeleNormContinuity
import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.Ideles.LocalNorms

/-!
# Milne, Class Field Theory, Chapter V, Section 4

This section defines the finite and full idele groups with the correct
restricted-product topology, identifies them algebraically with the units of
the finite and full adele rings, constructs the principal-idèle and local-place
embeddings, and proves their injectivity.  It also proves the archimedean norm
calculation in Proposition 4.12(a).  The finite and infinite local field norms
are assembled into the full idele norm; the finite restricted-product proof
uses preservation of completed valuation-ring units and contraction of the
finite set of exceptional upper primes.
The finite semilocal and archimedean principal-idèle norm formulas are proved,
so the norm descends unconditionally to idèle class groups.  Its range is
identified with the class norm subgroup used in Section 5.
`GlobalPlace` packages finite and infinite places into one index and assigns
the completion used by the idele and Brauer localization statements.

The ideal/content maps, discreteness of principal idèles, ray-class quotient
description, idèle-character correspondence, and the nonarchimedean clauses of
Proposition 4.12 require valuation, approximation, or norm-lifting
compatibilities not currently packaged for Mathlib's adele and local-field
APIs.  No axioms are introduced for those missing results.
-/
