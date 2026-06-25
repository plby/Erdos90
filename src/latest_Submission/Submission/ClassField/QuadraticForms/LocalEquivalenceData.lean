import Submission.ClassField.QuadraticForms.DiagonalInvariance
import Submission.ClassField.QuadraticForms.SquareClass
import Submission.ClassField.QuadraticForms.OrthogonalDecomposition
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Chapter VIII, Section 6, Theorem 6.10

The source proof classifies nondegenerate local quadratic forms after choosing
orthogonal bases.  Thus forms are represented here by lists of nonzero square
classes.  `DEData` records the geometric equivalence
relation on such diagonalizations.  Its only classification-flavoured field is
`commonLine`: Proposition 6.9 supplies a scalar represented by both forms of
equal invariants and rank greater than one.  The rank induction, including the
invariant calculation for the orthogonal complements, is proved below.
-/

namespace Submission.CField.QForms

variable {G μ : Type*} [CommGroup G] [CommGroup μ]

namespace AHSym

variable (h : AHSym G μ)

/-- The diagonal presentation of local quadratic-form equivalence used in
Theorem 6.10.  The preservation fields are supplied by discriminant
invariance and Proposition 6.7; `commonLine` is exactly the representation
input from Proposition 6.9 plus Proposition 6.1's orthogonal splitting. -/
structure DEData where
  equivalent : List G → List G → Prop
  equivalence : Equivalence equivalent
  length_eq : ∀ {xs ys}, equivalent xs ys → xs.length = ys.length
  discriminant_eq : ∀ {xs ys}, equivalent xs ys →
    discriminant xs = discriminant ys
  hasse_eq : ∀ {xs ys}, equivalent xs ys → h.hasse xs = h.hasse ys
  append_singleton : ∀ {xs ys} (a : G), equivalent xs ys →
    equivalent (xs ++ [a]) (ys ++ [a])
  commonLine : ∀ {xs ys},
    xs.length = ys.length → 1 < xs.length →
    discriminant xs = discriminant ys → h.hasse xs = h.hasse ys →
    ∃ (a : G) (xs₁ ys₁ : List G),
      xs₁.length + 1 = xs.length ∧ ys₁.length + 1 = ys.length ∧
      equivalent xs (xs₁ ++ [a]) ∧ equivalent ys (ys₁ ++ [a])

namespace DEData

variable (D : h.DEData)

/-- **Theorem VIII.6.10, exact diagonal source statement.**  Two local
quadratic forms are equivalent exactly when rank, discriminant, and Hasse
invariant agree. -/
def DiagonEquivaStatem : Prop :=
  ∀ xs ys : List G,
    D.equivalent xs ys ↔
      xs.length = ys.length ∧
      discriminant xs = discriminant ys ∧
      h.hasse xs = h.hasse ys

private theorem equivalent_of_invariants :
    ∀ xs ys : List G,
      xs.length = ys.length →
      discriminant xs = discriminant ys →
      h.hasse xs = h.hasse ys →
      D.equivalent xs ys := by
  intro xs ys hlen hdisc hhasse
  by_cases hn : xs.length ≤ 1
  · cases xs with
    | nil =>
        cases ys with
        | nil => exact D.equivalence.refl []
        | cons b bs => simp at hlen
    | cons a xtail =>
        cases xtail with
        | cons x more => simp at hn
        | nil =>
            have hylen : ys.length = 1 := by simpa using hlen.symm
            obtain ⟨b, rfl⟩ : ∃ b, ys = [b] := by
              simpa [List.length_eq_one_iff] using hylen
            have hab : a = b := by
              simpa [discriminant] using hdisc
            subst b
            exact D.equivalence.refl [a]
  · have hgt : 1 < xs.length := Nat.lt_of_not_ge hn
    obtain ⟨a, xs₁, ys₁, hxslen, hyslen, hxeq, hyeq⟩ :=
      D.commonLine hlen hgt hdisc hhasse
    have hlen₁ : xs₁.length = ys₁.length := by omega
    have hdiscAppend :
        discriminant (xs₁ ++ [a]) = discriminant (ys₁ ++ [a]) :=
      (D.discriminant_eq hxeq).symm.trans
        (hdisc.trans (D.discriminant_eq hyeq))
    have hdisc₁ : discriminant xs₁ = discriminant ys₁ := by
      rw [discriminant_append_singleton, discriminant_append_singleton] at hdiscAppend
      exact mul_right_cancel hdiscAppend
    have hhasseAppend :
        h.hasse (xs₁ ++ [a]) = h.hasse (ys₁ ++ [a]) :=
      (D.hasse_eq hxeq).symm.trans (hhasse.trans (D.hasse_eq hyeq))
    have hhasse₁ : h.hasse xs₁ = h.hasse ys₁ := by
      rw [h.hasse_append_singleton, h.hasse_append_singleton, hdisc₁] at hhasseAppend
      exact mul_right_cancel (mul_right_cancel hhasseAppend)
    have hsub : D.equivalent xs₁ ys₁ :=
      equivalent_of_invariants xs₁ ys₁ hlen₁ hdisc₁ hhasse₁
    exact D.equivalence.trans hxeq
      (D.equivalence.trans (D.append_singleton a hsub) (D.equivalence.symm hyeq))
termination_by xs ys _ _ _ => xs.length
decreasing_by omega

/-- Milne's induction proves the classification from the common represented
line furnished by Proposition 6.9. -/
theorem localDiagonalEquivalence : D.DiagonEquivaStatem := by
  intro xs ys
  constructor
  · intro heq
    exact ⟨D.length_eq heq, D.discriminant_eq heq, D.hasse_eq heq⟩
  · rintro ⟨hlen, hdisc, hhasse⟩
    exact equivalent_of_invariants (h := h) D xs ys hlen hdisc hhasse

end DEData

end AHSym

noncomputable section

universe u

open Submission.CField.HSymbol

/-- An actual local quadratic form, together with a diagonalization used only
to read off its square-class discriminant and concrete Hasse invariant. -/
structure DEForm
    (K : Type u) [Field K] where
  Space : Type u
  [spaceAddGroup : AddCommGroup Space]
  [moduleSpace : Module K Space]
  [finiteDimensionalSpace : FiniteDimensional K Space]
  form : QuadraticForm K Space
  nondegenerate : form.Nondegenerate
  coefficients : List Kˣ
  diagonalization : Nonempty (form.IsometryEquiv (diagonalForm coefficients))

attribute [instance]
  DEForm.spaceAddGroup
  DEForm.moduleSpace
  DEForm.finiteDimensionalSpace

/-- The actual rank of a bundled local quadratic form. -/
def DEForm.rank
    {K : Type u} [Field K] (q : DEForm K) : ℕ :=
  Module.finrank K q.Space

/-- The square-class discriminant read from the chosen diagonalization. -/
def DEForm.discriminant
    {K : Type u} [Field K] (q : DEForm K) :
    QuadraticSquareClass K :=
  AHSym.discriminant
    (squareClassCoefficients q.coefficients)

/-- The concrete Hasse sign read from the chosen diagonalization. -/
def DEForm.hasse
    {K : Type u} [Field K] (q : DEForm K) : ℤˣ :=
  concreteHasse q.coefficients

/-- **Theorem VIII.6.10, actual nonarchimedean local-field statement.**
Two nondegenerate quadratic forms are isometric exactly when their ranks,
square-class discriminants, and concrete Hasse invariants agree. -/
def DiagonalEquivalenceClassification : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (q q' : DEForm K),
    Nonempty (q.form.IsometryEquiv q'.form) ↔
      q.rank = q'.rank ∧ q.discriminant = q'.discriminant ∧
        q.hasse = q'.hasse

/-- Square-class lists are geometrically equivalent when they have actual
coefficient representatives whose diagonal forms are isometric. -/
def SquareDiagonalEquivalent
    {K : Type u} [Field K]
    (xs ys : List (QuadraticSquareClass K)) : Prop :=
  ∃ as bs : List Kˣ,
    squareClassCoefficients as = xs ∧ squareClassCoefficients bs = ys ∧
      QuadraticMap.Equivalent (diagonalForm as) (diagonalForm bs)

private theorem exists_coefficient_representatives
    {K : Type u} [Field K] (xs : List (QuadraticSquareClass K)) :
    ∃ as : List Kˣ, squareClassCoefficients as = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.square Kˣ) x
      obtain ⟨as, has⟩ := ih
      refine ⟨a :: as, ?_⟩
      change (QuotientGroup.mk' (Subgroup.square Kˣ)) a ::
        squareClassCoefficients as = x :: xs
      rw [ha, has]

private def weightedSquaresReindex
    {K : Type u} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → K) :
    QuadraticMap.IsometryEquiv
      (QuadraticMap.weightedSumSquares K w)
      (QuadraticMap.weightedSumSquares K (w ∘ e.symm)) where
  toLinearEquiv :=
    { toFun := fun x j ↦ x (e.symm j)
      invFun := fun x i ↦ x (e i)
      left_inv := fun x ↦ by funext i; simp
      right_inv := fun x ↦ by funext j; simp
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_app' x := by
    simp only [QuadraticMap.weightedSumSquares_apply, Function.comp_apply]
    change (∑ j : κ, w (e.symm j) * (x (e.symm j) * x (e.symm j))) =
      ∑ i : ι, w i * (x i * x i)
    exact Equiv.sum_comp e.symm (fun i : ι ↦ w i * (x i * x i))

private def splitLast
    {K : Type u} [Field K] (n : ℕ) :
    (Fin (n + 1) → K) ≃ₗ[K] (Fin n → K) × (Fin 1 → K) :=
  (LinearEquiv.piCongrLeft K (fun _ : Fin (n + 1) ↦ K)
    (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))).symm.trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin 1) K K)

private def splitAppendSingleton
    {K : Type u} [Field K] (as : List Kˣ) (c : Kˣ) :
    (Fin (as ++ [c]).length → K) ≃ₗ[K]
      (Fin as.length → K) × (Fin 1 → K) :=
  let hlen : (as ++ [c]).length = as.length + 1 := by simp
  (LinearEquiv.piCongrLeft K (fun _ : Fin (as.length + 1) ↦ K)
    (finCongr hlen)).trans (splitLast as.length)

/-- A displayed diagonal form with one coefficient appended is the
orthogonal product of the original form and that one-dimensional form. -/
private def diagonalFormAppend
    {K : Type u} [Field K] (as : List Kˣ) (c : Kˣ) :
    QuadraticMap.IsometryEquiv (diagonalForm (as ++ [c]))
      ((diagonalForm as).prod (diagonalForm [c])) where
  toLinearEquiv := splitAppendSingleton as c
  map_app' x := by
    rw [QuadraticMap.prod_apply]
    simp only [diagonalForm_apply]
    have hfirst (i : Fin as.length) :
        (splitAppendSingleton as c x).1 i =
          x ⟨i.1, by simp [List.length_append]⟩ := by
      simp [splitAppendSingleton, splitLast,
        LinearEquiv.sumArrowLequivProdArrow_apply_fst,
        LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft'_apply]
      congr 1
    have hlast :
        (splitAppendSingleton as c x).2 0 =
          x ⟨as.length, by simp [List.length_append]⟩ := by
      simp [splitAppendSingleton, splitLast,
        LinearEquiv.sumArrowLequivProdArrow_apply_snd,
        LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        Equiv.piCongrLeft'_apply]
      congr 1
    have hsecond :
        (∑ i : Fin 1, ([c].get i : K) *
          ((splitAppendSingleton as c x).2 i *
            (splitAppendSingleton as c x).2 i)) =
          (c : K) * ((splitAppendSingleton as c x).2 0 *
            (splitAppendSingleton as c x).2 0) := by
      rw [Fin.sum_univ_one]
      rfl
    change (∑ i : Fin as.length,
          (as.get i : K) *
            ((splitAppendSingleton as c x).1 i *
              (splitAppendSingleton as c x).1 i)) +
        (∑ i : Fin 1, ([c].get i : K) *
          ((splitAppendSingleton as c x).2 i *
            (splitAppendSingleton as c x).2 i)) = _
    rw [hsecond]
    rw [show (∑ i : Fin as.length,
          (as.get i : K) *
            ((splitAppendSingleton as c x).1 i *
              (splitAppendSingleton as c x).1 i)) =
        ∑ i : Fin as.length, (as.get i : K) *
          (x ⟨i.1, by simp [List.length_append]⟩ *
            x ⟨i.1, by simp [List.length_append]⟩) by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfirst]]
    rw [hlast]
    let hlen : (as ++ [c]).length = as.length + 1 := by simp
    let e : Fin (as ++ [c]).length ≃ Fin (as.length + 1) := finCongr hlen
    let F : Fin (as ++ [c]).length → K := fun k ↦
      ((as ++ [c]).get k : K) * (x k * x k)
    symm
    calc
      (∑ k : Fin (as ++ [c]).length, F k) =
          ∑ j : Fin (as.length + 1), F (e.symm j) :=
        (Equiv.sum_comp e.symm F).symm
      _ = (∑ i : Fin as.length, F (e.symm i.castSucc)) +
          F (e.symm (Fin.last as.length)) := Fin.sum_univ_castSucc _
      _ = (∑ i : Fin as.length, (as.get i : K) *
          (x ⟨i.1, by simp [List.length_append]⟩ *
            x ⟨i.1, by simp [List.length_append]⟩)) +
          (c : K) *
            (x ⟨as.length, by simp [List.length_append]⟩ *
              x ⟨as.length, by simp [List.length_append]⟩) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [F]
          have heq : e.symm i.castSucc =
              ⟨i.1, by simp [List.length_append]⟩ := by
            apply Fin.ext
            rfl
          rw [heq]
          simp
        · simp only [F]
          have heq : e.symm (Fin.last as.length) =
              ⟨as.length, by simp [List.length_append]⟩ := by
            apply Fin.ext
            rfl
          rw [heq]
          simp

/-- Appending the same one-dimensional diagonal coefficient preserves
geometric equivalence. -/
theorem diagonalAppend :
    ∀ (K : Type u) [Field K]
      (xs ys : List (QuadraticSquareClass K)) (a : QuadraticSquareClass K),
      SquareDiagonalEquivalent xs ys →
        SquareDiagonalEquivalent (xs ++ [a]) (ys ++ [a]) := by
  intro K _ xs ys a he
  obtain ⟨as, bs, has, hbs, hab⟩ := he
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (Subgroup.square Kˣ) a
  have happ : QuadraticMap.Equivalent
      (diagonalForm (as ++ [c])) (diagonalForm (bs ++ [c])) :=
    let emid := (Classical.choice hab).prod
      (QuadraticMap.IsometryEquiv.refl (diagonalForm [c]))
    ⟨(diagonalFormAppend as c).trans
      (emid.trans (diagonalFormAppend bs c).symm)⟩
  refine ⟨as ++ [c], bs ++ [c], ?_, ?_, happ⟩
  · simp only [squareClassCoefficients, List.map_append, List.map_cons, List.map_nil]
    change squareClassCoefficients as ++ [squareClass c] = xs ++ [a]
    rw [has]
    congr
  · simp only [squareClassCoefficients, List.map_append, List.map_cons, List.map_nil]
    change squareClassCoefficients bs ++ [squareClass c] = ys ++ [a]
    rw [hbs]
    congr

/-- Changing every diagonal coefficient by a square gives an isometric
diagonal form. -/
private theorem diagonal_equivalent_coefficients
    {K : Type u} [Field K] {as bs : List Kˣ}
    (hclasses : squareClassCoefficients as = squareClassCoefficients bs) :
    QuadraticMap.Equivalent (diagonalForm as) (diagonalForm bs) := by
  have hlen : as.length = bs.length := by
    simpa [squareClassCoefficients] using congrArg List.length hclasses
  let e : Fin as.length ≃ Fin bs.length := finCongr hlen
  let wa : Fin bs.length → K := fun j ↦ as.get (e.symm j)
  have hclass (j : Fin bs.length) :
      squareClass (as.get (e.symm j)) = squareClass (bs.get j) := by
    have hop := congrArg (fun l : List (QuadraticSquareClass K) ↦ l[j.1]?) hclasses
    simp only [squareClassCoefficients, List.getElem?_map] at hop
    have hjAs : j.1 < as.length := by omega
    simpa [hjAs, j.isLt] using hop
  let s : Fin bs.length → Kˣ := fun j ↦
    Classical.choose (Subgroup.mem_square.mp
      (QuotientGroup.eq_iff_div_mem.mp (hclass j)))
  have hs (j : Fin bs.length) :
      as.get (e.symm j) / bs.get j = s j * s j :=
    Classical.choose_spec (Subgroup.mem_square.mp
      (QuotientGroup.eq_iff_div_mem.mp (hclass j)))
  let er := weightedSquaresReindex e
    (fun i : Fin as.length ↦ (as.get i : K))
  let es : QuadraticMap.IsometryEquiv
      (QuadraticMap.weightedSumSquares K wa) (diagonalForm bs) :=
    QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      (R := K) (u := s) (by
        intro j
        have heq : bs.get j * s j ^ 2 = as.get (e.symm j) := by
          rw [pow_two, ← hs]
          simp [div_eq_mul_inv, mul_comm]
        exact congrArg (fun z : Kˣ ↦ (z : K)) heq)
  exact ⟨er.trans es⟩

private theorem diagonal_equivalent_equivalence
    {K : Type u} [Field K] :
    Equivalence (@SquareDiagonalEquivalent K _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs
    obtain ⟨as, has⟩ := exists_coefficient_representatives xs
    exact ⟨as, as, has, has, QuadraticMap.Equivalent.refl _⟩
  · intro xs ys
    rintro ⟨as, bs, has, hbs, he⟩
    exact ⟨bs, as, hbs, has, he.symm⟩
  · intro xs ys zs
    rintro ⟨as, bs, has, hbs, hab⟩ ⟨cs, ds, hcs, hds, hcd⟩
    have hbc : QuadraticMap.Equivalent (diagonalForm bs) (diagonalForm cs) :=
      diagonal_equivalent_coefficients
        (hbs.trans hcs.symm)
    exact ⟨as, ds, has, hds, hab.trans (hbc.trans hcd)⟩

/-- A diagonal form with nonzero displayed coefficients is nondegenerate. -/
private theorem diagonalForm_nondegenerate
    {K : Type u} [Field K] [NeZero (2 : K)] (as : List Kˣ) :
    (diagonalForm as).Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
    show (diagonalForm as).radical =
        Pi.spanSubset K {i | (as.get i : K) = 0} by
      exact QuadraticForm.radical_weightedSumSquares]
  have hset : {i | (as.get i : K) = 0} = ∅ := by
    ext i
    simp [Units.ne_zero]
  rw [hset]
  simp [Pi.spanSubset]

/-- Splitting off a represented nonzero line and diagonalizing its orthogonal
complement gives a diagonalization with the represented scalar last. -/
theorem splitRepresentedLine
    {K : Type u} [Field K] [NeZero (2 : K)]
    (coeffs : List Kˣ) (a : Kˣ)
    (hrep : DiagonalRepresents coeffs a) :
    ∃ rest : List Kˣ, rest.length + 1 = coeffs.length ∧
      QuadraticMap.Equivalent (diagonalForm coeffs)
        (diagonalForm (rest ++ [a])) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  let Q := diagonalForm coeffs
  obtain ⟨v, hv, hQv⟩ := hrep
  obtain ⟨e, he, hcompl⟩ :=
    orthogonal_decomposition Q a.ne_zero ⟨v, hQv⟩
  have he0 : e ≠ 0 := representing_vector_ne Q a.ne_zero he
  let ve : Fin 1 → (Fin coeffs.length → K) := fun _ ↦ e
  have hve : LinearIndependent K ve := by
    apply LinearIndependent.of_subsingleton 0
    simpa [ve] using he0
  let U : Submodule K (Fin coeffs.length → K) :=
    Submodule.span K (Set.range ve)
  have hUeq : U = K ∙ e := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨i, rfl⟩
      exact Submodule.mem_span_singleton_self e
    · apply Submodule.span_mono
      intro x hx
      rcases hx with rfl
      exact ⟨0, rfl⟩
  let W : Submodule K (Fin coeffs.length → K) :=
    LinearMap.BilinForm.orthogonal Q.polarBilin U
  have hcomplUW : IsCompl U W := by
    simpa [W, hUeq] using hcompl
  have hpolar : Q.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr (diagonalForm_nondegenerate coeffs)
  have hnotOrtho : ¬Q.polarBilin.IsOrtho e e := by
    intro hortho
    rw [LinearMap.IsOrtho, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, he] at hortho
    exact a.ne_zero ((mul_eq_zero.mp (by simpa [nsmul_eq_mul] using hortho)).resolve_left
      (NeZero.ne (2 : K)))
  have hWpolar :
      (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate := by
    have hWpolar0 :=
      LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
      Q.polarBilin hpolar (by
        intro x y hxy
        change Q.polarBilin x y = 0 at hxy
        change Q.polarBilin y x = 0
        change QuadraticMap.polar Q y x = 0
        change QuadraticMap.polar Q x y = 0 at hxy
        rw [QuadraticMap.polar_comm]
        exact hxy) hnotOrtho
    change (LinearMap.BilinForm.restrict Q.polarBilin
      (LinearMap.BilinForm.orthogonal Q.polarBilin U)).Nondegenerate
    rw [hUeq]
    exact hWpolar0
  have hQW : (Q.restrict W).Nondegenerate := by
    apply QuadraticMap.nondegenerate_polar_iff.mp
    simpa [W, QuadraticMap.polarBilin_apply_apply, QuadraticMap.restrict_apply]
      using hWpolar
  have hQWAssociated : (QuadraticMap.associated (Q.restrict W)).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQW).1
  obtain ⟨w, ⟨ew⟩⟩ :=
    QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
      (Q.restrict W) hQWAssociated
  let rest : List Kˣ := List.ofFn w
  let erIndex : Fin (Module.finrank K W) ≃ Fin rest.length :=
    finCongr (by simp [rest])
  let er := weightedSquaresReindex erIndex
    (fun i : Fin (Module.finrank K W) ↦ (w i : K))
  have hweights :
      ((fun i : Fin (Module.finrank K W) ↦ (w i : K)) ∘ erIndex.symm) =
        fun i : Fin rest.length ↦ (rest.get i : K) := by
    funext i
    dsimp only [Function.comp_apply]
    have hget : rest.get i = w ⟨i.1, by simpa [rest] using i.2⟩ := by
      simp [rest]
    rw [hget]
    have hi : erIndex.symm i = ⟨i.1, by simpa [rest] using i.2⟩ := by
      apply Fin.ext
      rfl
    rw [hi]
  let ewRest : (Q.restrict W).IsometryEquiv (diagonalForm rest) :=
    ew.trans (er.trans
      (QuadraticForm.weightedSumSquaresCongr hweights))
  let BU : Module.Basis (Fin 1) K U := Module.Basis.span hve
  have hBU (i : Fin 1) : ((BU i : U) : Fin coeffs.length → K) = e := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [BU, U, ve]
  have hUOrtho : (QuadraticMap.associated (Q.restrict U)).IsOrthoᵢ BU := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  let eu0 := QuadraticMap.isometryEquivBasisRepr (Q.restrict U) BU
  have hUForm : (Q.restrict U).basisRepr BU = diagonalForm [a] := by
    rw [QuadraticMap.basisRepr_eq_of_iIsOrtho (Q.restrict U) BU hUOrtho]
    change QuadraticMap.weightedSumSquares K
      (fun i : Fin 1 ↦ (Q.restrict U) (BU i)) =
        QuadraticMap.weightedSumSquares K (fun _ : Fin 1 ↦ (a : K))
    congr 1
    funext i
    change Q (BU i) = (a : K)
    rw [hBU, he]
  let eu : (Q.restrict U).IsometryEquiv (diagonalForm [a]) :=
    hUForm ▸ eu0
  let eprod : ((Q.restrict U).prod (Q.restrict W)).IsometryEquiv Q :=
    { U.prodEquivOfIsCompl W hcomplUW with
      map_app' := by
        intro x
        rw [QuadraticMap.prod_apply]
        change Q (x.1 + x.2) = Q x.1 + Q x.2
        have hortho := (LinearMap.BilinForm.mem_orthogonal_iff.mp x.2.property)
          x.1 x.1.property
        change QuadraticMap.polar Q x.1 x.2 = 0 at hortho
        calc
          Q (x.1 + x.2) = Q x.1 + Q x.2 + QuadraticMap.polar Q x.1 x.2 :=
            QuadraticMap.map_add Q x.1 x.2
          _ = Q x.1 + Q x.2 := by rw [hortho, add_zero] }
  let eall : Q.IsometryEquiv (diagonalForm (rest ++ [a])) :=
    eprod.symm.trans
      ((QuadraticMap.IsometryEquiv.prodComm (Q.restrict U) (Q.restrict W)).trans
        ((ewRest.prod eu).trans (diagonalFormAppend rest a).symm))
  refine ⟨rest, ?_, ⟨eall⟩⟩
  have hdim := (U.prodEquivOfIsCompl W hcomplUW).finrank_eq
  have hUdim : Module.finrank K U = 1 := by
    rw [Module.finrank_eq_card_basis BU]
    simp
  have hrest : rest.length = Module.finrank K W := by simp [rest]
  rw [hrest, ← hUdim]
  simpa [Module.finrank_prod, add_comm] using hdim

private theorem criterion_congr
    {K : Type u} [Field K]
    (H : QHData K) (a : Kˣ)
    {as bs : List Kˣ}
    (hlen : as.length = bs.length) (hgt : 1 < as.length)
    (hdisc : AHSym.discriminant
        (squareClassCoefficients as) =
      AHSym.discriminant (squareClassCoefficients bs))
    (hhasse : H.hilbert.hasse (squareClassCoefficients as) =
      H.hilbert.hasse (squareClassCoefficients bs)) :
    Criterion H.hilbert.toAHSym as a ↔
      Criterion H.hilbert.toAHSym bs a := by
  rcases as with _ | ⟨a₁, as⟩
  · simp at hgt
  rcases as with _ | ⟨a₂, as⟩
  · simp at hgt
  rcases as with _ | ⟨a₃, as⟩
  · have hbslen : bs.length = 2 := by simpa using hlen.symm
    obtain ⟨b₁, b₂, rfl⟩ := List.length_eq_two.mp hbslen
    simp only [Criterion]
    constructor
    · intro hc
      calc
        H.hilbert.symbol (squareClass a)
              (H.hilbert.negOne *
                AHSym.discriminant
                  (squareClassCoefficients [b₁, b₂])) *
            H.hilbert.symbol H.hilbert.negOne
              (AHSym.discriminant
                (squareClassCoefficients [b₁, b₂])) =
            H.hilbert.symbol (squareClass a)
              (H.hilbert.negOne *
                AHSym.discriminant
                  (squareClassCoefficients [a₁, a₂])) *
            H.hilbert.symbol H.hilbert.negOne
              (AHSym.discriminant
                (squareClassCoefficients [a₁, a₂])) := by rw [hdisc]
        _ = H.hilbert.hasse (squareClassCoefficients [a₁, a₂]) := hc
        _ = H.hilbert.hasse (squareClassCoefficients [b₁, b₂]) := hhasse
    · intro hc
      calc
        H.hilbert.symbol (squareClass a)
              (H.hilbert.negOne *
                AHSym.discriminant
                  (squareClassCoefficients [a₁, a₂])) *
            H.hilbert.symbol H.hilbert.negOne
              (AHSym.discriminant
                (squareClassCoefficients [a₁, a₂])) =
            H.hilbert.symbol (squareClass a)
              (H.hilbert.negOne *
                AHSym.discriminant
                  (squareClassCoefficients [b₁, b₂])) *
            H.hilbert.symbol H.hilbert.negOne
              (AHSym.discriminant
                (squareClassCoefficients [b₁, b₂])) := by rw [hdisc]
        _ = H.hilbert.hasse (squareClassCoefficients [b₁, b₂]) := hc
        _ = H.hilbert.hasse (squareClassCoefficients [a₁, a₂]) := hhasse.symm
  · rcases as with _ | ⟨a₄, as⟩
    · have hbslen : bs.length = 3 := by simpa using hlen.symm
      obtain ⟨b₁, b₂, b₃, rfl⟩ := List.length_eq_three.mp hbslen
      simp only [Criterion]
      rw [hdisc, hhasse]
    · have hbslen : 4 ≤ bs.length := by simp at hlen; omega
      rcases bs with _ | ⟨b₁, bs⟩
      · simp at hbslen
      rcases bs with _ | ⟨b₂, bs⟩
      · simp at hbslen
      rcases bs with _ | ⟨b₃, bs⟩
      · simp at hbslen
      rcases bs with _ | ⟨b₄, bs⟩
      · simp at hbslen
      rfl

private theorem diagonalRepresents_head
    {K : Type u} [Field K] (a : Kˣ) (as : List Kˣ) :
    DiagonalRepresents (a :: as) a := by
  let v : Fin (a :: as).length → K := Pi.single 0 1
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hz := congrFun hv (0 : Fin (a :: as).length)
    simp [v] at hz
  · rw [diagonalForm_apply]
    simp [v, Pi.single_apply]

/-- Proposition 6.9 gives a scalar represented by both forms; splitting that
line and diagonalizing its orthogonal complement supplies the common last
coefficient used by the classification induction. -/
private theorem commonRepresentedLine
    (h69 : (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          (coeffs : List Kˣ) (a : Kˣ),
          (diagonalForm coeffs).Nondegenerate →
            (DiagonalRepresents coeffs a ↔
              ConcreteCriterion coeffs a)))
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (H : QHData K)
    (xs ys : List (QuadraticSquareClass K))
    (hlen : xs.length = ys.length) (hgt : 1 < xs.length)
    (hdisc : AHSym.discriminant xs =
      AHSym.discriminant ys)
    (hhasse : H.hilbert.hasse xs = H.hilbert.hasse ys) :
    ∃ (a : QuadraticSquareClass K)
      (xs₁ ys₁ : List (QuadraticSquareClass K)),
      xs₁.length + 1 = xs.length ∧ ys₁.length + 1 = ys.length ∧
      SquareDiagonalEquivalent xs (xs₁ ++ [a]) ∧
      SquareDiagonalEquivalent ys (ys₁ ++ [a]) := by
  obtain ⟨as, has⟩ := exists_coefficient_representatives xs
  obtain ⟨bs, hbs⟩ := exists_coefficient_representatives ys
  have hlenAB : as.length = bs.length := by
    have h := hlen
    rw [← has, ← hbs] at h
    simpa [squareClassCoefficients] using h
  have hgtA : 1 < as.length := by
    rw [← has] at hgt
    simpa [squareClassCoefficients] using hgt
  have hdiscAB : AHSym.discriminant
      (squareClassCoefficients as) =
      AHSym.discriminant (squareClassCoefficients bs) := by
    rw [has, hbs]
    exact hdisc
  have hhasseAB : H.hilbert.hasse (squareClassCoefficients as) =
      H.hilbert.hasse (squareClassCoefficients bs) := by
    rw [has, hbs]
    exact hhasse
  rcases as with _ | ⟨a, as⟩
  · simp at hgtA
  have hrepA : DiagonalRepresents (a :: as) a :=
    diagonalRepresents_head a as
  have hconcreteA : ConcreteCriterion (a :: as) a :=
    (h69 K (a :: as) a (diagonalForm_nondegenerate (a :: as))).1 hrepA
  have habstractA : Criterion H.hilbert.toAHSym
      (a :: as) a :=
    (criterion_iff_concrete H (a :: as) a).2 hconcreteA
  have habstractB : Criterion H.hilbert.toAHSym
      bs a :=
    (criterion_congr H a hlenAB hgtA hdiscAB hhasseAB).1
      habstractA
  have hconcreteB : ConcreteCriterion bs a :=
    (criterion_iff_concrete H bs a).1 habstractB
  have hrepB : DiagonalRepresents bs a :=
    (h69 K bs a (diagonalForm_nondegenerate bs)).2 hconcreteB
  obtain ⟨as₁, haslen, hasplit⟩ :=
    splitRepresentedLine (a :: as) a hrepA
  obtain ⟨bs₁, hbslen, hbspilt⟩ :=
    splitRepresentedLine bs a hrepB
  refine ⟨squareClass a, squareClassCoefficients as₁,
    squareClassCoefficients bs₁, ?_, ?_, ?_, ?_⟩
  · simpa [squareClassCoefficients, ← has] using haslen
  · simpa [squareClassCoefficients, ← hbs] using hbslen
  · refine ⟨a :: as, as₁ ++ [a], has, ?_, hasplit⟩
    simp [squareClassCoefficients]
  · refine ⟨bs, bs₁ ++ [a], hbs, ?_, hbspilt⟩
    simp [squareClassCoefficients]

private theorem discr_weighted_squares
    {K : Type u} [Field K] [Invertible (2 : K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → K) :
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares K w) = ∏ i, w i := by
  rw [QuadraticForm.discr']
  have hsingle (i : ι) (c : K) :
      QuadraticMap.weightedSumSquares K w (Pi.single i c) =
        w i * (c * c) := by
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  have hadd (i j : ι) (hij : i ≠ j) :
      QuadraticMap.weightedSumSquares K w (Pi.single i 1 + Pi.single j 1) =
        w i + w j := by
    rw [QuadraticMap.weightedSumSquares_apply]
    calc
      (∑ x : ι, w x * (((Pi.single i (1 : K) + Pi.single j 1 : ι → K)) x *
          ((Pi.single i (1 : K) + Pi.single j 1 : ι → K)) x)) =
          (∑ x : ι, ((if x = i then w i else 0) +
            (if x = j then w j else 0))) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxi : x = i <;> by_cases hxj : x = j
        · subst x; exact (hij hxj).elim
        · subst x; simp [hxj]
        · subst x; simp [hxi]
        · simp [hxi, hxj]
      _ = w i + w j := by
        rw [Finset.sum_add_distrib]
        simp
  have hm : QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares K w) =
      Matrix.diagonal w := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
        QuadraticMap.associated_apply]
      rw [show (Pi.single i (1 : K) : ι → K) + Pi.single i 1 =
          Pi.single i (2 : K) by
        ext x
        by_cases hxi : x = i
        · subst x
          simp
          norm_num
        · simp [hxi]]
      rw [hsingle i 2, hsingle i 1]
      simp only [Matrix.diagonal_apply_eq]
      change ⅟(2 : K) *
        (w i * (2 * 2) - w i * (1 * 1) - w i * (1 * 1)) = w i
      rw [invOf_eq_inv]
      field_simp [NeZero.ne (2 : K)]
      ring
    · rw [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply,
        QuadraticMap.associated_apply, hadd i j hij, hsingle i 1, hsingle j 1]
      simp [Matrix.diagonal, hij]
  rw [hm, Matrix.det_diagonal]

private theorem diagonal_discriminant_equivalent
    {K : Type u} [Field K] [NeZero (2 : K)] {as bs : List Kˣ}
    (he : QuadraticMap.Equivalent (diagonalForm as) (diagonalForm bs)) :
    AHSym.discriminant (squareClassCoefficients as) =
      AHSym.discriminant (squareClassCoefficients bs) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨f⟩ := he
  have hlen : as.length = bs.length := by
    simpa using f.toLinearEquiv.finrank_eq
  let ec : Fin bs.length ≃ Fin as.length := (finCongr hlen).symm
  let er := weightedSquaresReindex ec
    (fun j : Fin bs.length ↦ (bs.get j : K))
  let g := f.trans er
  have hcomp :
      (QuadraticMap.weightedSumSquares K
        ((fun j : Fin bs.length ↦ (bs.get j : K)) ∘ ec.symm)).comp
          g.toLinearEquiv.toLinearMap = diagonalForm as := by
    ext x
    exact g.map_app x
  have hd := QuadraticForm.discr'_comp
    (Q := QuadraticMap.weightedSumSquares K
      ((fun j : Fin bs.length ↦ (bs.get j : K)) ∘ ec.symm))
    g.toLinearEquiv.toLinearMap
  rw [hcomp] at hd
  change QuadraticForm.discr' (QuadraticMap.weightedSumSquares K
      (fun i : Fin as.length ↦ (as.get i : K))) = _ at hd
  rw [discr_weighted_squares, discr_weighted_squares] at hd
  rw [LinearMap.det_toMatrix'] at hd
  have hprodReindex :
      (∏ i : Fin as.length,
          ((fun j : Fin bs.length ↦ (bs.get j : K)) ∘ ec.symm) i) =
        ∏ j : Fin bs.length, (bs.get j : K) := by
    exact Equiv.prod_comp ec.symm (fun j : Fin bs.length ↦ (bs.get j : K))
  rw [hprodReindex] at hd
  have hunit : as.prod = LinearEquiv.det g.toLinearEquiv ^ 2 * bs.prod := by
    apply Units.ext
    change (as.prod : K) =
      (LinearEquiv.det g.toLinearEquiv : K) ^ 2 * (bs.prod : K)
    have hasProd : (as.prod : K) =
        ∏ i : Fin as.length, (as.get i : K) := by
      rw [← List.prod_ofFn]
      have h := congrArg (List.map fun a : Kˣ ↦ (a : K)) (List.ofFn_get as)
      have hof : List.ofFn (fun i : Fin as.length ↦ (as.get i : K)) =
          as.map (fun a : Kˣ ↦ (a : K)) := by
        simpa only [List.map_ofFn] using h
      rw [hof]
      exact map_list_prod (Units.coeHom K) as
    have hbsProd : (bs.prod : K) =
        ∏ j : Fin bs.length, (bs.get j : K) := by
      rw [← List.prod_ofFn]
      have h := congrArg (List.map fun b : Kˣ ↦ (b : K)) (List.ofFn_get bs)
      have hof : List.ofFn (fun j : Fin bs.length ↦ (bs.get j : K)) =
          bs.map (fun b : Kˣ ↦ (b : K)) := by
        simpa only [List.map_ofFn] using h
      rw [hof]
      exact map_list_prod (Units.coeHom K) bs
    rw [hasProd, hbsProd, LinearEquiv.coe_det, pow_two]
    exact hd
  simp only [AHSym.discriminant]
  rw [show squareClassCoefficients as =
      as.map (QuotientGroup.mk' (Subgroup.square Kˣ)) by rfl,
    show squareClassCoefficients bs =
      bs.map (QuotientGroup.mk' (Subgroup.square Kˣ)) by rfl,
    ← map_list_prod, ← map_list_prod, hunit, map_mul]
  have hsquare :
      (QuotientGroup.mk' (Subgroup.square Kˣ))
        (LinearEquiv.det g.toLinearEquiv ^ 2) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact Subgroup.mem_square.mpr
      ⟨LinearEquiv.det g.toLinearEquiv, pow_two _⟩
  rw [hsquare, one_mul]

private theorem diagonal_equivalent_discriminant
    {K : Type u} [Field K] [NeZero (2 : K)]
    {xs ys : List (QuadraticSquareClass K)}
    (he : SquareDiagonalEquivalent xs ys) :
    AHSym.discriminant xs =
      AHSym.discriminant ys := by
  obtain ⟨as, bs, rfl, rfl, hab⟩ := he
  exact diagonal_discriminant_equivalent hab

private theorem weighted_squares_orthogonal
    {K : Type u} [Field K] {n : ℕ} (w : Fin n → K) :
    (QuadraticMap.weightedSumSquares K w).polarBilin.IsOrthoᵢ
      (Pi.basisFun K (Fin n)) := by
  intro i j hij
  change LinearMap.IsOrtho (QuadraticMap.weightedSumSquares K w).polarBilin
    ((Pi.basisFun K (Fin n)) i) ((Pi.basisFun K (Fin n)) j)
  rw [LinearMap.IsOrtho]
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  change (QuadraticMap.weightedSumSquares K w).polarBilin
    (Pi.single i 1) (Pi.single j 1) = 0
  change QuadraticMap.polar (QuadraticMap.weightedSumSquares K w)
    (Pi.single i 1) (Pi.single j 1) = 0
  have hi : QuadraticMap.weightedSumSquares K w (Pi.single i 1) = w i := by
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  have hj : QuadraticMap.weightedSumSquares K w (Pi.single j 1) = w j := by
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  have hijSum : QuadraticMap.weightedSumSquares K w
      (Pi.single i 1 + Pi.single j 1) = w i + w j := by
    rw [QuadraticMap.weightedSumSquares_apply]
    calc
      (∑ x : Fin n, w x *
          (((Pi.single i (1 : K) + Pi.single j 1 : Fin n → K)) x *
            ((Pi.single i (1 : K) + Pi.single j 1 : Fin n → K)) x)) =
          (∑ x : Fin n, ((if x = i then w i else 0) +
            (if x = j then w j else 0))) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxi : x = i <;> by_cases hxj : x = j
        · subst x; exact (hij hxj).elim
        · subst x; simp [hxj]
        · subst x; simp [hxi]
        · simp [hxi, hxj]
      _ = w i + w j := by
        rw [Finset.sum_add_distrib]
        simp
  change QuadraticMap.weightedSumSquares K w
      (Pi.single i 1 + Pi.single j 1) -
    QuadraticMap.weightedSumSquares K w (Pi.single i 1) -
    QuadraticMap.weightedSumSquares K w (Pi.single j 1) = 0
  rw [hijSum, hi, hj]
  abel

private def piFinrankBasis
    (K : Type u) [Field K] (n : ℕ) :
    Module.Basis (Fin (Module.finrank K (Fin n → K))) K (Fin n → K) :=
  (Pi.basisFun K (Fin n)).reindex
    (finCongr (Module.finrank_fin_fun K).symm)

private theorem squares_pi_orthogonal
    {K : Type u} [Field K] {n : ℕ} (w : Fin n → K) :
    (QuadraticMap.weightedSumSquares K w).polarBilin.IsOrthoᵢ
      (piFinrankBasis K n) := by
  intro i j hij
  let e : Fin n ≃ Fin (Module.finrank K (Fin n → K)) :=
    finCongr (Module.finrank_fin_fun (R := K)).symm
  change LinearMap.IsOrtho (QuadraticMap.weightedSumSquares K w).polarBilin
    ((piFinrankBasis K n) i) ((piFinrankBasis K n) j)
  rw [LinearMap.IsOrtho]
  simp only [piFinrankBasis, Module.Basis.reindex_apply]
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  change (QuadraticMap.weightedSumSquares K w).polarBilin
    (Pi.single (e.symm i) 1) (Pi.single (e.symm j) 1) = 0
  have hh := weighted_squares_orthogonal w
    (fun h ↦ hij (e.symm.injective h))
  change LinearMap.IsOrtho (QuadraticMap.weightedSumSquares K w).polarBilin
    ((Pi.basisFun K (Fin n)) (e.symm i))
    ((Pi.basisFun K (Fin n)) (e.symm j)) at hh
  rw [LinearMap.IsOrtho, Pi.basisFun_apply, Pi.basisFun_apply] at hh
  exact hh

@[simp] private theorem hilbert_sign_diagonal
    {K : Type u} [Field K] (a b : K) :
    Submission.CField.QForms.quadraticHilbertSign a b =
      Submission.CField.HSymbol.quadraticHilbertSign a b := rfl

private theorem concrete_quadratic_hasse
    {K : Type u} [Field K] (as : List Kˣ) :
    concreteQuadraticHasse (as.map fun a : Kˣ ↦ (a : K)) =
      concreteHasse as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, concreteQuadraticHasse, concreteHasse]
      rw [List.map_map, ih]
      simp only [hilbert_sign_diagonal, Function.comp_def]

private theorem quadratic_hasse_squares
    {K : Type u} [Field K] {n : ℕ} (w : Fin n → K) :
    quadraticHasseBasis
      (QuadraticMap.weightedSumSquares K w) (piFinrankBasis K n) =
        concreteQuadraticHasse (List.ofFn w) := by
  unfold quadraticHasseBasis
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [piFinrankBasis, QuadraticMap.weightedSumSquares_apply,
      Pi.single_apply]

private theorem diagonal_form_hasse
    {K : Type u} [Field K] (as : List Kˣ) :
    quadraticHasseBasis (diagonalForm as)
        (piFinrankBasis K as.length) = concreteHasse as := by
  unfold diagonalForm
  rw [quadratic_hasse_squares]
  have hof : List.ofFn (fun i : Fin as.length ↦ (as.get i : K)) =
      as.map (fun a : Kˣ ↦ (a : K)) := by
    have h := congrArg (List.map fun a : Kˣ ↦ (a : K)) (List.ofFn_get as)
    simpa only [List.map_ofFn] using h
  rw [hof, concrete_quadratic_hasse]

private theorem diagonal_hasse_equivalent
    (h67 : (∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          (Q Q' : QuadraticForm K V)
          (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
          Nonempty (Q.IsometryEquiv Q') → Q.Nondegenerate →
          Q.polarBilin.IsOrthoᵢ B → Q'.polarBilin.IsOrthoᵢ B' →
            quadraticHasseBasis Q B =
              quadraticHasseBasis Q' B'))
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    {as bs : List Kˣ}
    (he : QuadraticMap.Equivalent (diagonalForm as) (diagonalForm bs)) :
    concreteHasse as = concreteHasse bs := by
  obtain ⟨f⟩ := he
  have hlen : as.length = bs.length := by
    simpa using f.toLinearEquiv.finrank_eq
  let ec : Fin bs.length ≃ Fin as.length := (finCongr hlen).symm
  let er := weightedSquaresReindex ec
    (fun j : Fin bs.length ↦ (bs.get j : K))
  let g := f.trans er
  let wbs : Fin as.length → K :=
    (fun j : Fin bs.length ↦ (bs.get j : K)) ∘ ec.symm
  have hh := h67 K (Fin as.length → K)
    (diagonalForm as) (QuadraticMap.weightedSumSquares K wbs)
    (piFinrankBasis K as.length) (piFinrankBasis K as.length)
    ⟨g⟩ (diagonalForm_nondegenerate as)
    (squares_pi_orthogonal
      (fun i : Fin as.length ↦ (as.get i : K)))
    (squares_pi_orthogonal wbs)
  rw [diagonal_form_hasse,
    quadratic_hasse_squares] at hh
  have hof : List.ofFn wbs = bs.map (fun b : Kˣ ↦ (b : K)) := by
    apply List.ext_getElem
    · simp [wbs, hlen]
    · intro n hn₁ hn₂
      simp [wbs, ec, Function.comp_def]
  rw [hof, concrete_quadratic_hasse] at hh
  exact hh

private theorem diagonal_equivalent_hasse
    (h67 : (∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          (Q Q' : QuadraticForm K V)
          (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
          Nonempty (Q.IsometryEquiv Q') → Q.Nondegenerate →
          Q.polarBilin.IsOrthoᵢ B → Q'.polarBilin.IsOrthoᵢ B' →
            quadraticHasseBasis Q B =
              quadraticHasseBasis Q' B'))
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (H : QHData K)
    {xs ys : List (QuadraticSquareClass K)}
    (he : SquareDiagonalEquivalent xs ys) :
    H.hilbert.hasse xs = H.hilbert.hasse ys := by
  obtain ⟨as, bs, has, hbs, hab⟩ := he
  rw [← has, ← hbs, H.hasse_eq_concrete, H.hasse_eq_concrete]
  exact diagonal_hasse_equivalent h67 hab

private def diagonalEquivalenceData
    (h67 : (∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          (Q Q' : QuadraticForm K V)
          (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
          Nonempty (Q.IsometryEquiv Q') → Q.Nondegenerate →
          Q.polarBilin.IsOrthoᵢ B → Q'.polarBilin.IsOrthoᵢ B' →
            quadraticHasseBasis Q B =
              quadraticHasseBasis Q' B'))
    (h69 : (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          (coeffs : List Kˣ) (a : Kˣ),
          (diagonalForm coeffs).Nondegenerate →
            (DiagonalRepresents coeffs a ↔
              ConcreteCriterion coeffs a)))
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    (H : QHData K) :
    H.hilbert.toAHSym.DEData where
  equivalent := SquareDiagonalEquivalent
  equivalence := diagonal_equivalent_equivalence
  length_eq := by
    intro xs ys he
    obtain ⟨as, bs, has, hbs, hab⟩ := he
    calc
      xs.length = as.length := by rw [← has]; simp [squareClassCoefficients]
      _ = bs.length := by
        obtain ⟨e⟩ := hab
        simpa using e.toLinearEquiv.finrank_eq
      _ = ys.length := by rw [← hbs]; simp [squareClassCoefficients]
  discriminant_eq := by
    intro xs ys he
    exact diagonal_equivalent_discriminant he
  hasse_eq := by
    intro xs ys he
    exact diagonal_equivalent_hasse h67 H he
  append_singleton := by
    intro xs ys a he
    exact diagonalAppend K xs ys a he
  commonLine := by
    intro xs ys hlen hgt hdisc hhasse
    exact commonRepresentedLine h69 K H xs ys hlen hgt hdisc hhasse

private theorem form_coefficients_length
    {K : Type u} [Field K] (q : DEForm K) :
    q.rank = q.coefficients.length := by
  obtain ⟨e⟩ := q.diagonalization
  simpa [DEForm.rank] using e.toLinearEquiv.finrank_eq

/-- The diagonal invariant induction, Proposition 6.7, and Proposition 6.9
specialize to actual nondegenerate forms over every nonarchimedean local
field. -/
theorem local_field_diagonalization
    (hHilbert : ∀ (K : Type u) [NontriviallyNormedField K]
      [IsUltrametricDist K] [ValuativeRel K]
      [IsNonarchimedeanLocalField K] [NeZero (2 : K)],
      QHData K)
    (h67 : (∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          (Q Q' : QuadraticForm K V)
          (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
          Nonempty (Q.IsometryEquiv Q') → Q.Nondegenerate →
          Q.polarBilin.IsOrthoᵢ B → Q'.polarBilin.IsOrthoᵢ B' →
            quadraticHasseBasis Q B =
              quadraticHasseBasis Q' B'))
    (h69 : (∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          (coeffs : List Kˣ) (a : Kˣ),
          (diagonalForm coeffs).Nondegenerate →
            (DiagonalRepresents coeffs a ↔
              ConcreteCriterion coeffs a))) :
    DiagonalEquivalenceClassification.{u} := by
  intro K _ _ _ _ _ q q'
  let H := hHilbert K
  let D := diagonalEquivalenceData h67 h69 K H
  have hclassification := D.localDiagonalEquivalence
  constructor
  · rintro ⟨e⟩
    obtain ⟨fq⟩ := q.diagonalization
    obtain ⟨fq'⟩ := q'.diagonalization
    have hdiag : QuadraticMap.Equivalent
        (diagonalForm q.coefficients) (diagonalForm q'.coefficients) :=
      ⟨fq.symm.trans (e.trans fq')⟩
    have hrel : SquareDiagonalEquivalent
        (squareClassCoefficients q.coefficients)
        (squareClassCoefficients q'.coefficients) :=
      ⟨q.coefficients, q'.coefficients, rfl, rfl, hdiag⟩
    have hrank : q.rank = q'.rank := by
      exact e.toLinearEquiv.finrank_eq
    have hdisc := D.discriminant_eq hrel
    have hhasse := D.hasse_eq hrel
    rw [H.hasse_eq_concrete, H.hasse_eq_concrete] at hhasse
    exact ⟨hrank, hdisc, hhasse⟩
  · rintro ⟨hrank, hdisc, hhasse⟩
    have hlen : (squareClassCoefficients q.coefficients).length =
        (squareClassCoefficients q'.coefficients).length := by
      simp only [squareClassCoefficients, List.length_map]
      rw [← form_coefficients_length q,
        ← form_coefficients_length q', hrank]
    have habstractHasse :
        H.hilbert.hasse (squareClassCoefficients q.coefficients) =
          H.hilbert.hasse (squareClassCoefficients q'.coefficients) := by
      rw [H.hasse_eq_concrete, H.hasse_eq_concrete]
      exact hhasse
    have hrel : SquareDiagonalEquivalent
        (squareClassCoefficients q.coefficients)
        (squareClassCoefficients q'.coefficients) :=
      (hclassification _ _).2 ⟨hlen, hdisc, habstractHasse⟩
    obtain ⟨as, bs, has, hbs, hab⟩ := hrel
    have hqa : QuadraticMap.Equivalent
        (diagonalForm q.coefficients) (diagonalForm as) :=
      diagonal_equivalent_coefficients has.symm
    have hbq' : QuadraticMap.Equivalent
        (diagonalForm bs) (diagonalForm q'.coefficients) :=
      diagonal_equivalent_coefficients hbs
    obtain ⟨fq⟩ := q.diagonalization
    obtain ⟨fq'⟩ := q'.diagonalization
    obtain ⟨eqa⟩ := hqa
    obtain ⟨eab⟩ := hab
    obtain ⟨ebq'⟩ := hbq'
    exact ⟨fq.trans (eqa.trans (eab.trans (ebq'.trans fq'.symm)))⟩

end

end Submission.CField.QForms
