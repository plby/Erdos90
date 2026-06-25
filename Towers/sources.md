# Sources

Known books, papers, and source manuscripts that have been autoformalized or
attempted in the `Towers` project. This is a starter list, not yet an
exhaustive audit.

“Used in main `Towers/`” means that a Lean module under `Towers/`, outside the
source's own formalization, imports one of its modules. Top-level umbrella
imports alone do not count.

| Source | Status in repo | Used in main `Towers/`? | Main repo area |
| --- | --- | --- | --- |
| J. S. Milne, *Algebraic Number Theory* (v3.08, 2020) | Substantial partial formalization. The development originally followed Milne's chapter layout and now mostly lives in topic-oriented modules; the Milne namespace/readme remains as provenance glue. | Yes | [`../../docs/ANT.pdf`](../../docs/ANT.pdf), [`../../docs/ANT.tex`](../../docs/ANT.tex), [`Towers/AlgebraicNumberTheory/Milne/README.md`](Towers/AlgebraicNumberTheory/Milne/README.md), [`Towers/AlgebraicNumberTheory/`](Towers/AlgebraicNumberTheory/) |
| Steve Wright, *Notes on the Theory of Algebraic Numbers* (arXiv:1507.07520) | Small targeted formalization. The mirrored notes are present in `docs/1507.07520`, and `Towers/AlgebraicNumberTheory/Eisenstein/Units.lean` explicitly cites Wright's Proposition 99(i). | Yes | [`docs/1507.07520/algnumber.tex`](docs/1507.07520/algnumber.tex), [`Towers/AlgebraicNumberTheory/Eisenstein/Units.lean`](Towers/AlgebraicNumberTheory/Eisenstein/Units.lean) |
| J. S. Milne, *Class Field Theory* (v4.03, 2020) | Large ongoing partial formalization of chapters, sections, and exercises; several files explicitly record which Milne statements are faithful, conditional, complete, or still missing. | Yes | [`../../docs/CFT.pdf`](../../docs/CFT.pdf), [`../../docs/CFT.tex`](../../docs/CFT.tex), [`Towers/ClassFieldTheory/`](Towers/ClassFieldTheory/) |
| Ruth Rebekka Struik, "On Nilpotent Products of Cyclic Groups," *Canadian Journal of Mathematics* 12 (1960), 447-462 | Attempted / substantial partial formalization distributed by mathematical subject under `Towers.Group.NilpotentProducts`, with source-coverage and claim-audit docs. | No | [`docs/Struik1.tex`](docs/Struik1.tex), [`docs/Struik1-coverage.md`](docs/Struik1-coverage.md), [`docs/Struik1-claim-audit.md`](docs/Struik1-claim-audit.md), [`Towers/Group/NilpotentProducts/`](Towers/Group/NilpotentProducts/) |
| Ruth Rebekka Struik, "On Nilpotent Products of Cyclic Groups. II," *Canadian Journal of Mathematics* 13 (1961), 557-568 | Attempted / partial formalization distributed through the same subject-oriented nilpotent-products modules. The audit distinguishes complete, partial, formula-only, and missing paper items. | No | [`docs/Struik2.tex`](docs/Struik2.tex), [`docs/Struik-audit.md`](docs/Struik-audit.md), [`Towers/Group/NilpotentProducts/`](Towers/Group/NilpotentProducts/) |
| Philip Hall, *The Edmonton Notes on Nilpotent Groups* (1957 lectures; reproduced by Mark Pengitore, arXiv:2507.09745) | Substantial ongoing formalization across central series, commutator identities, Hall basic commutators, embedding theorems, dimension subgroups, Petresco material, and related nilpotent-group chapters. | Yes | [`docs/2507.09745/main.tex`](docs/2507.09745/main.tex), [`Towers/CentralSeries.lean`](Towers/CentralSeries.lean), [`Towers/HallBasicCommutators.lean`](Towers/HallBasicCommutators.lean), [`Towers/HallEmbeddingTheorems.lean`](Towers/HallEmbeddingTheorems.lean), [`Towers/`](Towers/) |
| J. Petresco, "Sur les commutateurs," *Seminaire Albert Chatelet et Paul Dubreil* 7 (1953-1954), Expose no. 6, 1-11 | Substantial formalization under `Petresco1954`; the umbrella import says it formalizes Petresco's paper and covers substitutions, commutator subgroup descriptions, normal closures, commutator bounds, derived/lower-central estimates, radicals, finite-family forms, collection, and Hall's power identity. | Yes | [`docs/SD_1953-1954__7__A6_0.tex`](docs/SD_1953-1954__7__A6_0.tex), [`Towers/PetrescoSurLesCommutateurs.lean`](Towers/PetrescoSurLesCommutateurs.lean), [`Towers/PetrescoSubstitutionsAndWords.lean`](Towers/PetrescoSubstitutionsAndWords.lean), [`Towers/PetrescoProjectionCollection.lean`](Towers/PetrescoProjectionCollection.lean) |
| Michael Chapman and Ido Efrat, "Filtrations of free groups arising from the lower central series" (arXiv:1601.08006) | Substantial partial formalization across the paper's Magnus, group-algebra, unitriangular, recursive, Zassenhaus, and Massey-product material. | Yes | [`docs/1601.08006/EfratChapman_revised.tex`](docs/1601.08006/EfratChapman_revised.tex), [`Towers/Algebra/Magnus/`](Towers/Algebra/Magnus/), [`Towers/Group/Zassenhaus/`](Towers/Group/Zassenhaus/), [`Towers/Group/Cohomology/`](Towers/Group/Cohomology/) |
| Alexander Cant and Bettina Eick, "Polynomials describing the multiplication in finitely generated torsion-free nilpotent groups" (arXiv:1801.02932) | Semantic / pre-Section-5 partial formalization, with later sections represented only at specification-wrapper level according to the audit. | No | [`docs/1801.02932/hallpol.tex`](docs/1801.02932/hallpol.tex), [`docs/1801.02932/formalization-audit.md`](docs/1801.02932/formalization-audit.md), [`Towers/CantEick/`](Towers/CantEick/) |

External source links already mirrored or cited in the repo:

- Milne ANT: <https://www.jmilne.org/math/CourseNotes/ANT.pdf>
- Wright notes: <https://arxiv.org/abs/1507.07520>
- Milne CFT: <https://www.jmilne.org/math/CourseNotes/CFT.pdf>
- Struik 1960 DOI: <https://doi.org/10.4153/CJM-1960-039-X>
- Struik 1961 DOI: <https://doi.org/10.4153/CJM-1961-045-2>
- Hall Edmonton notes: <https://arxiv.org/abs/2507.09745>
- Petresco NUMDAM: <https://www.numdam.org/item/SD_1953-1954__7__A6_0/>
- Chapman--Efrat arXiv: <https://arxiv.org/abs/1601.08006>
- Cant--Eick arXiv: <https://arxiv.org/abs/1801.02932>
