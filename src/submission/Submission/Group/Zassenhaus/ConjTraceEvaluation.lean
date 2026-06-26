import Submission.Group.Zassenhaus.ConjCorrectionTrace
import Submission.Group.Zassenhaus.InverseConjTrace

/-!
# Substitution evaluation for strict conjugation traces

The raw Hall-Petresco trace definitions are syntactic labelled-word
expansions.  Their original semantic lemmas specialize atoms to free
generators.  Hall-Witt expansions also need signed substitutions, where some
labels are sent to inverses of ambient group elements.

This file evaluates ordinary and inverse-oriented traces under an arbitrary
group-valued substitution.  The strict prefix and strict tail continue to
compute the exact conjugation quotients.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace HACoeff

/-- Evaluate a labelled commutator-word list under an arbitrary substitution. -/
def labelledEval
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (L : List (CWord (LabelledAtom M N))) :
    G :=
  (L.map fun word => word.eval f).prod

/-- Evaluate a labelled atom list under an arbitrary substitution. -/
def labelledAtomEval
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N)) :
    G :=
  (A.map f).prod

@[simp]
lemma labelled_list_nil
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G) :
    labelledEval f [] = 1 :=
  rfl

@[simp]
lemma labelled_list_cons
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (word : CWord (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    labelledEval f (word :: L) =
      word.eval f * labelledEval f L :=
  rfl

@[simp]
lemma labelled_list_append
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (L K : List (CWord (LabelledAtom M N))) :
    labelledEval f (L ++ K) =
      labelledEval f L * labelledEval f K := by
  simp [labelledEval, List.prod_append]

lemma labelled_list_flat
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (expand :
      CWord (LabelledAtom M N) →
        List (CWord (LabelledAtom M N))) :
    ∀ L : List (CWord (LabelledAtom M N)),
      labelledEval f (L.flatMap expand) =
        (L.map fun word => labelledEval f (expand word)).prod
  | [] => by
      rfl
  | word :: L => by
      simp [labelled_list_append, labelled_list_flat f expand L]

/-- Arbitrary-substitution evaluation of one ordinary conjugation step. -/
lemma labelled_list_atom
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N)) :
    labelledEval f (conjugateAtomTrace a D) =
      f a * D.eval f * (f a)⁻¹ := by
  simp [conjugateAtomTrace, labelledEval,
    CWord.eval_commutator, commutatorElement_def]

/-- Arbitrary-substitution evaluation of an ordinary conjugation trace. -/
lemma eval_conj_trace
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledEval f (conjTrace A D) =
      labelledAtomEval f A * D.eval f *
        (labelledAtomEval f A)⁻¹ := by
  induction A with
  | nil =>
      simp [conjTrace, labelledEval, labelledAtomEval]
  | cons a A ih =>
      rw [conjTrace, labelled_list_flat]
      simp_rw [labelled_list_atom]
      rw [show
          (List.map
              (fun E => f a * E.eval f * (f a)⁻¹)
              (conjTrace A D)).prod =
            f a * labelledEval f (conjTrace A D) * (f a)⁻¹ by
          simpa [labelledEval, List.map_map, Function.comp_def] using
            (list_prod_conjugates (f a)
              ((conjTrace A D).map fun E => E.eval f))]
      rw [ih]
      simp [labelledAtomEval]
      group

/-- Arbitrary-substitution evaluation of an ordinary trace list. -/
lemma labelled_eval_conj
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N))) :
    labelledEval f (conjTraceList A L) =
      labelledAtomEval f A * labelledEval f L *
        (labelledAtomEval f A)⁻¹ := by
  rw [conjTraceList, labelled_list_flat]
  simp_rw [eval_conj_trace]
  rw [show
      (List.map
          (fun D =>
            labelledAtomEval f A * D.eval f *
              (labelledAtomEval f A)⁻¹)
          L).prod =
        labelledAtomEval f A * labelledEval f L *
          (labelledAtomEval f A)⁻¹ by
      simpa [labelledEval, List.map_map, Function.comp_def] using
        (list_prod_conjugates (labelledAtomEval f A)
          (L.map fun D => D.eval f))]

/-- Arbitrary-substitution evaluation of the strict ordinary prefix. -/
lemma labelled_correction_trace
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N)) :
    labelledEval f (conjCorrectionTrace A D) =
      (labelledAtomEval f A * D.eval f *
        (labelledAtomEval f A)⁻¹) *
          (D.eval f)⁻¹ := by
  have htrace := eval_conj_trace f A D
  rw [correction_append_singleton,
    labelled_list_append] at htrace
  simp only [labelled_list_cons, labelled_list_nil, mul_one] at htrace
  rw [← htrace]
  group

/-- Arbitrary-substitution evaluation of one inverse-oriented step. -/
lemma labelled_conjugate_atom
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (a : LabelledAtom M N)
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledEval f (inverseConjugateAtom a D) =
      f a * D.eval f * (f a)⁻¹ := by
  simp [inverseConjugateAtom, labelledEval,
    swap_collapse_positive f hD,
    commutatorElement_def, mul_assoc]

/-- Arbitrary-substitution evaluation of an inverse-oriented trace. -/
lemma labelled_list_conj
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledEval f (inverseConjTrace A D) =
      labelledAtomEval f A * D.eval f *
        (labelledAtomEval f A)⁻¹ := by
  induction A with
  | nil =>
      simp [inverseConjTrace, labelledEval, labelledAtomEval]
  | cons a A ih =>
      rw [inverseConjTrace, labelled_list_flat]
      rw [show
          (List.map
              (fun E => labelledEval f (inverseConjugateAtom a E))
              (inverseConjTrace A D)).prod =
            (List.map
              (fun E => f a * E.eval f * (f a)⁻¹)
              (inverseConjTrace A D)).prod by
          congr 1
          apply List.map_congr_left
          intro E hE
          rw [labelled_conjugate_atom f a E
            (inverse_trace_positive A hD E hE)]]
      rw [show
          (List.map
              (fun E => f a * E.eval f * (f a)⁻¹)
              (inverseConjTrace A D)).prod =
            f a * labelledEval f (inverseConjTrace A D) * (f a)⁻¹ by
          simpa [labelledEval, List.map_map, Function.comp_def] using
            (list_prod_conjugates (f a)
              ((inverseConjTrace A D).map fun E => E.eval f))]
      rw [ih]
      simp [labelledAtomEval]
      group

/-- Arbitrary-substitution evaluation of an inverse-oriented trace list. -/
lemma labelled_inverse_conj
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (L : List (CWord (LabelledAtom M N)))
    (hL : ∀ D ∈ L, (collapseWord D).PBPos) :
    labelledEval f (inverseTraceList A L) =
      labelledAtomEval f A * labelledEval f L *
        (labelledAtomEval f A)⁻¹ := by
  rw [inverseTraceList, labelled_list_flat]
  rw [show
      (List.map (fun D => labelledEval f (inverseConjTrace A D)) L).prod =
        (List.map
          (fun D =>
            labelledAtomEval f A * D.eval f *
              (labelledAtomEval f A)⁻¹)
          L).prod by
      congr 1
      apply List.map_congr_left
      intro D hD
      rw [labelled_list_conj f A D (hL D hD)]]
  rw [show
      (List.map
          (fun D =>
            labelledAtomEval f A * D.eval f *
              (labelledAtomEval f A)⁻¹)
          L).prod =
        labelledAtomEval f A * labelledEval f L *
          (labelledAtomEval f A)⁻¹ by
      simpa [labelledEval, List.map_map, Function.comp_def] using
        (list_prod_conjugates (labelledAtomEval f A)
          (L.map fun D => D.eval f))]

/-- Arbitrary-substitution evaluation of the strict inverse-oriented tail. -/
lemma labelled_conj_trace
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (f : LabelledAtom M N → G)
    (A : List (LabelledAtom M N))
    (D : CWord (LabelledAtom M N))
    (hD : (collapseWord D).PBPos) :
    labelledEval f (inverseConjCorrection A D) =
      (D.eval f)⁻¹ *
        (labelledAtomEval f A * D.eval f *
          (labelledAtomEval f A)⁻¹) := by
  have htrace := labelled_list_conj f A D hD
  rw [inverse_cons_correction] at htrace
  simp only [labelled_list_cons] at htrace
  rw [← htrace]
  group

end HACoeff
end Submission
