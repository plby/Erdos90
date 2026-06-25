import Mathlib

namespace Submission.NumberTheory

open IntermediateField MvPolynomial

namespace PrimitiveElement

theorem aeval_fin_symm
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E]
    {n : ℕ} (s : Fin n → E) (y : E)
    (P : Polynomial (MvPolynomial (Fin n) F)) :
    aeval (Fin.cons y s) ((finSuccEquiv F n).symm P) =
      Polynomial.eval₂ (aeval s).toRingHom y P := by
  let lhs : Polynomial (MvPolynomial (Fin n) F) →ₐ[F] E :=
    (aeval (Fin.cons y s)).comp (finSuccEquiv F n).symm.toAlgHom
  let rhs : Polynomial (MvPolynomial (Fin n) F) →ₐ[F] E :=
    { Polynomial.eval₂RingHom (aeval s).toRingHom y with
      commutes' := fun r => by simp }
  change lhs P = rhs P
  congr 1
  apply AlgHom.ext
  have hring : lhs.toRingHom = rhs.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro p
      have hcoeff :
          lhs.toRingHom.comp Polynomial.C = rhs.toRingHom.comp Polynomial.C := by
        apply MvPolynomial.ringHom_ext
        · intro r
          have hconst :
              (finSuccEquiv F n).symm (Polynomial.C (MvPolynomial.C r)) =
                MvPolynomial.C r := by
            simpa using RingHom.congr_fun (finSuccEquiv_comp_C_eq_C (R := F) n) r
          simp [lhs, rhs, hconst]
        · intro i
          have htail :
              (finSuccEquiv F n).symm (Polynomial.C (MvPolynomial.X i)) =
                MvPolynomial.X i.succ := by
            apply (finSuccEquiv F n).injective
            rw [(finSuccEquiv F n).apply_symm_apply]
            exact (finSuccEquiv_X_succ (R := F) (j := i)).symm
          simp [lhs, rhs, htail]
      exact RingHom.congr_fun hcoeff p
    · have hzero :
          (finSuccEquiv F n).symm Polynomial.X = MvPolynomial.X 0 := by
        apply (finSuccEquiv F n).injective
        rw [(finSuccEquiv F n).apply_symm_apply]
        exact (finSuccEquiv_X_zero (R := F) (n := n)).symm
      simp [lhs, rhs, hzero]
  intro x
  exact RingHom.congr_fun hring x

theorem aeval_adjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (alpha : Fin n → E) (halpha : ∀ i, IsAlgebraic F (alpha i))
    {x : E} (hx : x ∈ adjoin F (Set.range alpha)) :
    ∃ p : MvPolynomial (Fin n) F, aeval alpha p = x := by
  have hx' : x ∈ Algebra.adjoin F (Set.range alpha) := by
    rw [← adjoin_toSubalgebra_of_isAlgebraic]
    · exact hx
    · rintro y ⟨i, rfl⟩
      exact halpha i
  rw [Algebra.adjoin_range_eq_range_aeval] at hx'
  exact hx'

theorem aeval_total_degree
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    ∀ {n : ℕ} (alpha : Fin n → E),
      (∀ i, IsAlgebraic F (alpha i)) →
      ∀ p : MvPolynomial (Fin n) F,
        ∃ q : MvPolynomial (Fin n) F,
          aeval alpha q = aeval alpha p ∧
            q.totalDegree ≤ ∑ i, ((minpoly F (alpha i)).natDegree - 1) := by
  intro n
  induction n with
  | zero =>
      intro alpha halpha p
      refine ⟨p, rfl, ?_⟩
      have hpdeg : p.totalDegree = 0 := by
        rw [totalDegree]
        apply Finset.sup_eq_zero.mpr
        intro i hi
        have hzero : i = 0 := Subsingleton.elim _ _
        simp [hzero]
      simp [hpdeg]
  | succ n ih =>
      intro alpha halpha p
      let tail : Fin n → E := fun i => alpha i.succ
      let P : Polynomial (MvPolynomial (Fin n) F) := finSuccEquiv F n p
      let f : Polynomial (MvPolynomial (Fin n) F) :=
        (minpoly F (alpha 0)).map MvPolynomial.C
      let r : Polynomial (MvPolynomial (Fin n) F) := P %ₘ f
      have hfmonic : f.Monic := by
        exact (minpoly.monic (halpha 0).isIntegral).map _
      have hfne : f ≠ 1 := by
        intro hf
        have hdeg : f.natDegree = 0 := by simp [hf]
        change ((minpoly F (alpha 0)).map MvPolynomial.C).natDegree = 0 at hdeg
        rw [Polynomial.natDegree_map] at hdeg
        exact (minpoly.natDegree_pos (halpha 0).isIntegral).ne' hdeg
      have hrdeg : r.natDegree < (minpoly F (alpha 0)).natDegree := by
        have h := Polynomial.natDegree_modByMonic_lt P hfmonic hfne
        simpa [r, f, Polynomial.natDegree_map] using h
      have htail : ∀ i, IsAlgebraic F (tail i) := fun i => halpha i.succ
      have hnorm (i : ℕ) := ih tail htail (r.coeff i)
      let c : ℕ → MvPolynomial (Fin n) F := fun i => Classical.choose (hnorm i)
      have hc_eval (i : ℕ) :
          aeval tail (c i) = aeval tail (r.coeff i) :=
        (Classical.choose_spec (hnorm i)).1
      have hc_deg (i : ℕ) :
          (c i).totalDegree ≤
            ∑ j, ((minpoly F (tail j)).natDegree - 1) :=
        (Classical.choose_spec (hnorm i)).2
      let Q : Polynomial (MvPolynomial (Fin n) F) :=
        r.sum fun i _ => Polynomial.C (c i) * Polynomial.X ^ i
      let q : MvPolynomial (Fin (n + 1)) F := (finSuccEquiv F n).symm Q
      let ev : Polynomial (MvPolynomial (Fin n) F) →+* E :=
        Polynomial.eval₂RingHom (aeval tail).toRingHom (alpha 0)
      have hQcoeff (i : ℕ) :
          Q.coeff i = if i ∈ r.support then c i else 0 := by
        change (r.sum fun j _ => Polynomial.C (c j) * Polynomial.X ^ j).coeff i = _
        rw [Polynomial.coeff_sum, Polynomial.sum_def]
        simp
      have hQeval : ev Q = ev r := by
        change ev (r.sum fun i _ => Polynomial.C (c i) * Polynomial.X ^ i) = _
        rw [Polynomial.sum_def, map_sum]
        simp only [ev, Polynomial.coe_eval₂RingHom, map_mul, map_pow,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
        change (∑ i ∈ r.support, (aeval tail) (c i) * (alpha 0) ^ i) = _
        rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc_eval]
        rfl
      have hfeval : ev f = 0 := by
        change Polynomial.eval₂ (aeval tail).toRingHom (alpha 0)
          ((minpoly F (alpha 0)).map MvPolynomial.C) = 0
        rw [Polynomial.eval₂_map]
        have hcomp : (aeval tail).toRingHom.comp MvPolynomial.C = algebraMap F E := by
          ext x
          simp
        rw [hcomp]
        exact minpoly.aeval F (alpha 0)
      have hreval : ev r = ev P := by
        change ev (P %ₘ f) = ev P
        have h := congrArg ev (Polynomial.modByMonic_add_div P f)
        rw [map_add, map_mul] at h
        rw [hfeval, zero_mul, add_zero] at h
        exact h
      refine ⟨q, ?_, ?_⟩
      · change aeval alpha ((finSuccEquiv F n).symm Q) = aeval alpha p
        have halphaCons : Fin.cons (alpha 0) tail = alpha := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [← halphaCons, aeval_fin_symm]
        have hpEval :=
          aeval_fin_symm tail (alpha 0) (finSuccEquiv F n p)
        exact hQeval.trans (hreval.trans <| by simpa [P, ev] using hpEval.symm)
      · have hqbound :
            q.totalDegree ≤ (minpoly F (alpha 0)).natDegree - 1 +
              ∑ j, ((minpoly F (tail j)).natDegree - 1) := by
          rw [totalDegree, Finset.sup_le_iff]
          intro m hm
          have htailSupport :
              m.tail ∈ (Q.coeff (m 0)).support := by
            have h' := (mem_support_coeff_finSuccEquiv
              (f := q) (i := m 0) (m := m.tail)).mpr (by
                simpa [Finsupp.cons_tail] using hm)
            simpa [q] using h'
          have hQcoeff_ne : Q.coeff (m 0) ≠ 0 := by
            intro hzero
            rw [hzero] at htailSupport
            simp at htailSupport
          have hi : m 0 ∈ r.support := by
            by_contra hi
            rw [hQcoeff, if_neg hi] at hQcoeff_ne
            exact hQcoeff_ne rfl
          have htailC : m.tail ∈ (c (m 0)).support := by
            simpa [hQcoeff, hi] using htailSupport
          have htailBound :
              m.tail.sum (fun _ e => e) ≤
                ∑ j, ((minpoly F (tail j)).natDegree - 1) :=
            (le_totalDegree htailC).trans (hc_deg (m 0))
          have hiBound : m 0 ≤ (minpoly F (alpha 0)).natDegree - 1 := by
            have himin : m 0 < (minpoly F (alpha 0)).natDegree :=
              (Polynomial.le_natDegree_of_mem_supp (m 0) hi).trans_lt hrdeg
            omega
          rw [← Finsupp.cons_tail m, Finsupp.sum_cons]
          exact Nat.add_le_add hiBound htailBound
        rw [Fin.sum_univ_succ]
        simpa [q, tail] using hqbound

/-- Proposition 12(ii): every element of a field generated by finitely many algebraic
elements is represented by a polynomial whose total degree is bounded by the sum of
one less than the generators' degrees. -/
theorem aeval_total_adjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (alpha : Fin n → E) (halpha : ∀ i, IsAlgebraic F (alpha i))
    {x : E} (hx : x ∈ adjoin F (Set.range alpha)) :
    ∃ p : MvPolynomial (Fin n) F,
      aeval alpha p = x ∧
        p.totalDegree ≤ ∑ i, ((minpoly F (alpha i)).natDegree - 1) := by
  obtain ⟨p, hp⟩ := aeval_adjoin alpha halpha hx
  obtain ⟨q, hq, hqdeg⟩ := aeval_total_degree alpha halpha p
  exact ⟨q, hq.trans hp, hqdeg⟩

/-- Lemma 13: a field generated by finitely many algebraic elements over a
characteristic-zero field is a simple extension. -/
theorem finite_adjoin_simple
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    {S : Set E} [Finite S] (hS : ∀ x ∈ S, IsAlgebraic F x) :
    ∃ theta : adjoin F S, F⟮theta⟯ = ⊤ := by
  letI : FiniteDimensional F (adjoin F S) :=
    finiteDimensional_adjoin fun x hx => (hS x hx).isIntegral
  exact Field.exists_primitive_element F (adjoin F S)

end PrimitiveElement

end Submission.NumberTheory
