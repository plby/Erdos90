import Towers.Group.HallPetrescoClaim

/-!
# Strict ordinary-conjugation correction traces

The ordinary Hall-Petresco conjugation trace emits corrections before its
retained source word.  This file splits off that strict correction prefix.

Every prefix word gains positive formal weight, and the prefix evaluates
exactly to the quotient between the conjugated value and the retained value.
Together with the inverse-oriented strict-tail splitter, this supplies both
conjugation orientations needed by an exact Hall-Witt expansion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace HACoeff

/-- The strict correction prefix left before the retained original word. -/
def conjCorrectionTrace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    List (CWord (LabelledAtom M N)) :=
  (conjTrace A D).dropLast

/-- The ordinary conjugation trace always ends with the original word. -/
lemma init_conj_singleton
    {M N : ℕ} :
    ∀ (A : List (LabelledAtom M N))
      (D : CWord (LabelledAtom M N)),
      ∃ init, conjTrace A D = init ++ [D]
  | [], D => ⟨[], rfl⟩
  | a :: A, D => by
      rcases init_conj_singleton A D with
        ⟨init, hinit⟩
      refine
        ⟨init.flatMap (conjugateAtomTrace a) ++
            [.commutator (.atom a) D], ?_⟩
      simp [conjTrace, hinit, conjugateAtomTrace]

/-- Split an ordinary trace into its strict prefix and retained last word. -/
lemma correction_append_singleton
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    conjTrace A D =
      conjCorrectionTrace A D ++ [D] := by
  rcases init_conj_singleton A D with ⟨init, hinit⟩
  simp [conjCorrectionTrace, hinit]

@[simp]
lemma conj_correction_nil
    {M N : ℕ}
    (D : CWord (LabelledAtom M N)) :
    conjCorrectionTrace [] D = [] :=
  rfl

/--
Adding one conjugator applies the same one-atom expansion to every older
correction and appends one immediate correction before the retained word.
-/
lemma conj_correction_cons
    {M N : ℕ}
    (a : LabelledAtom M N)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    conjCorrectionTrace (a :: A) D =
      (conjCorrectionTrace A D).flatMap (conjugateAtomTrace a) ++
        [.commutator (.atom a) D] := by
  rw [conjCorrectionTrace, conjTrace,
    correction_append_singleton]
  simp [conjugateAtomTrace]

/-- Relabel one ordinary one-atom trace. -/
lemma relabel_atom_trace
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    conjugateAtomTrace (relabelLabel left right a)
        (relabelWord left right D) =
      (conjugateAtomTrace a D).map (relabelWord left right) := by
  cases a <;>
    simp [conjugateAtomTrace, relabelWord, relabelLabel]

/-- Relabeling commutes with the full ordinary conjugation trace. -/
lemma relabel_word_conj
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N') :
    ∀ A : List (LabelledAtom M N),
      ∀ D : CWord (LabelledAtom M N),
        conjTrace (A.map (relabelLabel left right))
            (relabelWord left right D) =
          (conjTrace A D).map (relabelWord left right)
  | [], D => by
      simp [conjTrace]
  | a :: A, D => by
      rw [List.map_cons, conjTrace, conjTrace, relabel_word_conj]
      rw [List.flatMap_map, List.map_flatMap]
      simp [relabel_atom_trace]

/-- Relabeling commutes with extraction of the strict correction prefix. -/
lemma relabel_correction_trace
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    conjCorrectionTrace (A.map (relabelLabel left right))
        (relabelWord left right D) =
      (conjCorrectionTrace A D).map (relabelWord left right) := by
  rw [conjCorrectionTrace, conjCorrectionTrace,
    relabel_word_conj]
  simp

/-- One ordinary conjugation step never decreases formal weight. -/
lemma weight_conjugate_atom
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (a : LabelledAtom M N)
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ conjugateAtomTrace a D) :
    D.weight wt ≤ E.weight wt := by
  have hE' :
      E = .commutator (.atom a) D ∨ E = D := by
    simpa [conjugateAtomTrace] using hE
  rcases hE' with rfl | rfl
  · simp [CWord.weight_commutator]
  · exact Nat.le_refl _

/-- Every ordinary correction-prefix word has strictly larger formal weight. -/
lemma weight_conj_trace
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a) :
    ∀ (A : List (LabelledAtom M N))
      (D E : CWord (LabelledAtom M N)),
      E ∈ conjCorrectionTrace A D →
        D.weight wt < E.weight wt
  | [], D, E, hE => by
      simp at hE
  | a :: A, D, E, hE => by
      rw [conj_correction_cons] at hE
      simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hE
      rcases hE with ⟨F, hF, hEF⟩ | rfl
      · exact
          lt_of_lt_of_le
            (weight_conj_trace wt hwt A D F hF)
            (weight_conjugate_atom wt a F E hEF)
      · simp only [CWord.weight_commutator,
          CWord.weight_atom]
        exact Nat.lt_add_of_pos_left (hwt a)

/-- Every ordinary correction prefix gains at least one unit of weight. -/
lemma succ_conj_correction
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    (D E : CWord (LabelledAtom M N))
    (hE : E ∈ conjCorrectionTrace A D) :
    D.weight wt + 1 ≤ E.weight wt :=
  Nat.succ_le_of_lt
    (weight_conj_trace wt hwt A D E hE)

/-- Positive Hall-pair bidegree is inherited by every ordinary correction. -/
lemma conj_trace_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {D : CWord (LabelledAtom M N)}
    (hD : (collapseWord D).PBPos) :
    ∀ E ∈ conjCorrectionTrace A D,
      (collapseWord E).PBPos := by
  intro E hE
  apply conjTrace_positive A hD E
  rw [correction_append_singleton]
  simp [hE]

/-- The full ordinary trace evaluates as its strict prefix and retained word. -/
lemma labelled_conj_retained
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledListEval (conjTrace A D) =
      labelledListEval (conjCorrectionTrace A D) *
        D.eval FreeGroup.of := by
  rw [correction_append_singleton,
    labelled_eval_append]
  simp [labelledListEval]

/--
The strict ordinary prefix is exactly the quotient between conjugation and
the retained word value.
-/
lemma labelled_eval_trace
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledListEval (conjCorrectionTrace A D) =
      (labelledAtomList A * D.eval FreeGroup.of *
        (labelledAtomList A)⁻¹) *
          (D.eval FreeGroup.of)⁻¹ := by
  have htrace := labelled_trace A D
  rw [labelled_conj_retained] at htrace
  rw [← htrace]
  group

/-- Strict ordinary correction prefixes for every source word in a list. -/
def conjCorrectionList
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  L.flatMap (conjCorrectionTrace A)

/-- Relabeling commutes with strict ordinary list-prefix extraction. -/
lemma relabel_correction_list
    {M N M' N' : ℕ}
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    conjCorrectionList (A.map (relabelLabel left right))
        (L.map (relabelWord left right)) =
      (conjCorrectionList A L).map (relabelWord left right) := by
  rw [conjCorrectionList, conjCorrectionList,
    List.flatMap_map, List.map_flatMap]
  simp [relabel_correction_trace]

/-- Every list-prefix correction points back to a strictly lighter source. -/
lemma conj_correction_list
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N)))
    (E : CWord (LabelledAtom M N))
    (hE : E ∈ conjCorrectionList A L) :
    ∃ D ∈ L, D.weight wt < E.weight wt := by
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact
    ⟨D, hD,
      weight_conj_trace wt hwt A D E hED⟩

/--
If every retained word lies in one supported stratum, every ordinary
list-prefix correction lies at least one stratum higher.
-/
lemma add_correction_list
    {M N lowerWeight : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, lowerWeight ≤ D.weight wt)
    (E : CWord (LabelledAtom M N))
    (hE : E ∈ conjCorrectionList A L) :
    lowerWeight + 1 ≤ E.weight wt := by
  rcases
      conj_correction_list wt hwt A L E hE with
    ⟨D, hD, hweight⟩
  have hlower := hL D hD
  omega

/-- Positive Hall-pair bidegree is inherited by ordinary list corrections. -/
lemma conj_correction_positive
    {M N : ℕ}
    (A : List (LabelledAtom M N))
    {L : List (CWord (LabelledAtom M N))}
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    ∀ E ∈ conjCorrectionList A L,
      (collapseWord E).PBPos := by
  intro E hE
  rcases List.mem_flatMap.mp hE with ⟨D, hD, hED⟩
  exact conj_trace_positive A (hL D hD) E hED

end HACoeff
end Towers
