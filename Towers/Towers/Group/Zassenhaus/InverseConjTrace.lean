import Towers.Group.HallPetrescoClaim

/-!
# Strict inverse-conjugation correction traces

The inverse-oriented Hall-Petresco conjugation trace keeps the original
commutator word before every correction.  This file splits off that retained
head and packages the remaining strict tail.

Every tail word gains positive weight, and the tail evaluates exactly to the
quotient between the conjugated value and the retained value.  This is the
local exact-trace ingredient needed when Hall-Witt conjugations are expanded
without reintroducing same-weight recursive normalization.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace HACoeff

/-- The strict correction tail left after retaining the original word. -/
def inverseConjCorrection
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    List (CWord (LabelledAtom M N)) :=
  (inverseConjTrace A D).tail

/-- The inverse-oriented trace always starts with the original word. -/
lemma tail_inverse_cons
    {M N : ℕ} :
    ∀ (A : List (LabelledAtom M N))
      (D : CWord (LabelledAtom M N)),
      ∃ tail, inverseConjTrace A D = D :: tail
  | [], D => ⟨[], rfl⟩
  | a :: A, D => by
      rcases tail_inverse_cons A D with ⟨tail, htail⟩
      refine
        ⟨.commutator (rootSwapWord D) (.atom a) ::
            tail.flatMap (inverseConjugateAtom a), ?_⟩
      simp [inverseConjTrace, htail, inverseConjugateAtom]

/-- Split an inverse-oriented trace into its retained head and strict tail. -/
lemma inverse_cons_correction
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    inverseConjTrace A D =
      D :: inverseConjCorrection A D := by
  rcases tail_inverse_cons A D with ⟨tail, htail⟩
  simp [inverseConjCorrection, htail]

@[simp]
lemma inverse_conj_nil
    {M N : ℕ}
    (D : CWord (LabelledAtom M N)) :
    inverseConjCorrection [] D = [] :=
  rfl

/--
Adding one conjugator emits one immediate correction and applies the same
one-atom expansion to every older correction.
-/
lemma inverse_conj_cons
    {M N : ℕ}
    (a : LabelledAtom M N)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    inverseConjCorrection (a :: A) D =
      .commutator (rootSwapWord D) (.atom a) ::
        (inverseConjCorrection A D).flatMap
          (inverseConjugateAtom a) := by
  rw [inverseConjCorrection, inverseConjTrace,
    inverse_cons_correction]
  simp [inverseConjugateAtom]

/-- Relabeling commutes with extraction of the strict correction tail. -/
lemma relabel_conj_trace
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    inverseConjCorrection (A.map (relabelLabel left right))
        (relabelWord left right D) =
      (inverseConjCorrection A D).map (relabelWord left right) := by
  rw [inverseConjCorrection, inverseConjCorrection,
    relabel_inverse_conj]
  simp

/-- One inverse-oriented conjugation step never decreases formal weight. -/
lemma conjugate_atom_trace
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (a : LabelledAtom M N)
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjugateAtom a D) :
    D.weight wt ≤ E.weight wt := by
  have hE' :
      E = D ∨ E = .commutator (rootSwapWord D) (.atom a) := by
    simpa [inverseConjugateAtom] using hE
  rcases hE' with rfl | rfl
  · exact Nat.le_refl _
  · simp [CWord.weight_commutator, weight_root_swap]

/-- A full inverse-oriented conjugation trace never decreases formal weight. -/
lemma weight_inverse_conj
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ) :
    ∀ (A : List (LabelledAtom M N))
      (D E : CWord (LabelledAtom M N)),
      E ∈ inverseConjTrace A D →
        D.weight wt ≤ E.weight wt
  | [], D, E, hE => by
      have hED : E = D := by
        simpa [inverseConjTrace] using hE
      subst E
      exact Nat.le_refl _
  | a :: A, D, E, hE => by
      rcases List.mem_flatMap.mp hE with ⟨F, hF, hEF⟩
      exact
        (weight_inverse_conj wt A D F hF).trans
          (conjugate_atom_trace wt a F E hEF)

/-- Every word in the correction tail has strictly larger formal weight. -/
lemma inverse_conj_trace
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a) :
    ∀ (A : List (LabelledAtom M N))
      (D E : CWord (LabelledAtom M N)),
      E ∈ inverseConjCorrection A D →
        D.weight wt < E.weight wt
  | [], D, E, hE => by
      simp at hE
  | a :: A, D, E, hE => by
      rw [inverse_conj_cons] at hE
      simp only [List.mem_cons, List.mem_flatMap] at hE
      rcases hE with rfl | ⟨F, hF, hEF⟩
      · simp only [CWord.weight_commutator, weight_root_swap,
          CWord.weight_atom]
        exact Nat.lt_add_of_pos_right (hwt a)
      · exact
          lt_of_lt_of_le
            (inverse_conj_trace wt hwt A D F hF)
            (conjugate_atom_trace wt a F E hEF)

/-- Every correction tail word gains at least one unit of formal weight. -/
lemma succ_conj_trace
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjCorrection A D) :
    D.weight wt + 1 ≤ E.weight wt :=
  Nat.succ_le_of_lt
    (inverse_conj_trace wt hwt A D E hE)

/-- Positive Hall-pair bidegree is inherited by every strict correction. -/
lemma inverse_correction_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    ∀ E ∈ inverseConjCorrection A D,
      (collapseWord E).PBPos := by
  intro E hE
  apply inverse_trace_positive A hD E
  rw [inverse_cons_correction]
  simp [hE]

/-- The full trace evaluates as the retained value followed by its tail. -/
lemma labelled_conj_correction
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledListEval (inverseConjTrace A D) =
      D.eval FreeGroup.of *
        labelledListEval (inverseConjCorrection A D) := by
  rw [inverse_cons_correction]
  rfl

/--
The strict tail is exactly the quotient between conjugation and the retained
word value.
-/
lemma labelled_inverse_trace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledListEval (inverseConjCorrection A D) =
      (D.eval FreeGroup.of)⁻¹ *
        (labelledAtomList A * D.eval FreeGroup.of *
          (labelledAtomList A)⁻¹) := by
  have htrace := labelled_list_inverse A D hD
  rw [labelled_conj_correction] at htrace
  rw [← htrace]
  group

/-- Strict correction tails for every word in a formal commutator list. -/
def inverseConjList
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  L.flatMap (inverseConjCorrection A)

/-- Relabeling commutes with strict list-tail extraction. -/
lemma relabel_conj_list
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    inverseConjList (A.map (relabelLabel left right))
        (L.map (relabelWord left right)) =
      (inverseConjList A L).map
        (relabelWord left right) := by
  rw [inverseConjList, inverseConjList,
    List.flatMap_map, List.map_flatMap]
  simp [relabel_conj_trace]

/--
The list trace is the interleaving of every retained source word with its
strict correction tail.
-/
lemma flat_cons_correction
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    inverseTraceList A L =
      L.flatMap fun D => D :: inverseConjCorrection A D := by
  rw [inverseTraceList]
  induction L with
  | nil =>
      rfl
  | cons D L ih =>
      simp only [List.flatMap_cons]
      rw [inverse_cons_correction, ih]

/-- Every full list-trace word points back to a source word of no larger weight. -/
lemma inverse_conj_list
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N)))
    (E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseTraceList A L) :
    ∃ D ∈ L, D.weight wt ≤ E.weight wt := by
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact
    ⟨D, hD, weight_inverse_conj wt A D E hED⟩

/-- Every list-tail correction points back to a strictly lighter source word. -/
lemma source_conj_list
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N)))
    (E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjList A L) :
    ∃ D ∈ L, D.weight wt < E.weight wt := by
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact
    ⟨D, hD,
      inverse_conj_trace wt hwt A D E hED⟩

/--
If every retained word lies in one supported stratum, every list-tail
correction lies at least one stratum higher.
-/
lemma add_conj_list
    {M N lowerWeight : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, lowerWeight ≤ D.weight wt)
    (E : CWord (LabelledAtom M N))
    (hE : E ∈ inverseConjList A L) :
    lowerWeight + 1 ≤ E.weight wt := by
  rcases
      source_conj_list
        wt hwt A L E hE with
    ⟨D, hD, hweight⟩
  have hlower := hL D hD
  omega

/-- Positive Hall-pair bidegree is inherited by every list-tail correction. -/
lemma inverse_conj_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    ∀ E ∈ inverseConjList A L,
      (collapseWord E).PBPos := by
  intro E hE
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact inverse_correction_positive A (hL D hD) E hED

end HACoeff
end Towers
