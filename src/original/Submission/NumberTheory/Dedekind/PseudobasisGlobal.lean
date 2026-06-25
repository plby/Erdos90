import Submission.NumberTheory.Dedekind.DedekindModules

/-!
# Milne, Algebraic Number Theory, global pseudobases for an inclusion

Theorem 3.31(a) supplies ideal pseudobases for finite torsion-free modules over a
Dedekind domain.  Here we choose pseudobases simultaneously for a module and a
submodule and transport the inclusion to an injective linear map between finite
direct sums of ideals.  In the same-rank case its cokernel is torsion; this is the
global coordinate form to which the local diagonal-basis theorem applies.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

/-- The ideal pseudobasis theorem with the nonzeroness of every summand retained. -/
theorem direct_nonzero_ideals
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    ∃ (n : ℕ) (I : Fin n → Ideal A),
      (∀ i, I i ≠ ⊥) ∧ Nonempty (M ≃ₗ[A] ⨁ i, I i) := by
  classical
  induction h : Module.finrank A M using Nat.strong_induction_on generalizing M with
  | h n ih =>
      cases subsingleton_or_nontrivial M with
      | inl hM =>
          letI : Subsingleton M := hM
          exact ⟨0, Fin.elim0, (fun i => i.elim0),
            ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
      | inr hM =>
          letI : Nontrivial M := hM
          letI : Module.Projective A M := torsion_module_projective A M
          obtain ⟨f, hf, ⟨e⟩⟩ := projective_ker_range A M
          let I : Ideal A := LinearMap.range f
          let N : Submodule A M := LinearMap.ker f
          have hI : I ≠ ⊥ := by
            intro hI
            exact hf (LinearMap.range_eq_bot.mp hI)
          letI : Module.Finite A N :=
            Module.Finite.of_fg (IsNoetherian.noetherian N)
          have hfinI : Module.finrank A I = 1 := by
            apply Nat.le_antisymm
            · simpa using LinearMap.finrank_le_finrank_of_injective I.injective_subtype
            · exact (Submodule.one_le_finrank_iff).2 hI
          have hfinQuotient : Module.finrank A (M ⧸ N) = 1 := by
            calc
              Module.finrank A (M ⧸ N) = Module.finrank A I :=
                f.quotKerEquivRange.finrank_eq
              _ = 1 := hfinI
          have hfin : Module.finrank A N + 1 = n := by
            have hsum := N.finrank_quotient_add_finrank
            omega
          have hlt : Module.finrank A N < n := by omega
          obtain ⟨d, J, hJ, ⟨eN⟩⟩ := ih (Module.finrank A N) hlt N rfl
          let K : Option (Fin d) → Ideal A := fun
            | none => I
            | some i => J i
          refine ⟨d + 1, fun i => K (finSuccEquiv d i), ?_, ⟨?_⟩⟩
          · intro i
            cases ho : finSuccEquiv d i with
            | none => simpa [K, ho] using hI
            | some j => simpa [K, ho] using hJ j
          · exact e ≪≫ₗ (eN.prodCongr (LinearEquiv.refl A I)) ≪≫ₗ
              LinearEquiv.prodComm A _ _ ≪≫ₗ
              (DirectSum.lequivProdDirectSum
                (R := A) (ι := Fin d) (α := fun o => ↑(K o))).symm ≪≫ₗ
              DirectSum.lequivCongrLeft
                (M := fun o => ↑(K o)) A (finSuccEquiv d).symm

/-- An inclusion of finite torsion-free modules over a Dedekind domain can be
written globally as an injective map between finite direct sums of ideals. -/
theorem dedekind_pseudobasis
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M) :
    ∃ (m n : ℕ) (I : Fin m → Ideal A) (J : Fin n → Ideal A)
      (eM : M ≃ₗ[A] ⨁ i, I i) (eN : N ≃ₗ[A] ⨁ j, J j)
      (f : (⨁ j, J j) →ₗ[A] (⨁ i, I i)),
      Function.Injective f ∧ ∀ x : N, f (eN x) = eM x.1 := by
  letI : Module.Finite A N := Module.Finite.of_fg (IsNoetherian.noetherian N)
  obtain ⟨m, I, ⟨eM⟩⟩ := torsion_direct_ideals A M
  obtain ⟨n, J, ⟨eN⟩⟩ := torsion_direct_ideals A N
  let f : (⨁ j, J j) →ₗ[A] (⨁ i, I i) :=
    eM.toLinearMap.comp (N.subtype.comp eN.symm.toLinearMap)
  refine ⟨m, n, I, J, eM, eN, f, ?_, ?_⟩
  · exact eM.injective.comp (N.injective_subtype.comp eN.symm.injective)
  · intro x
    simp [f]

/-- In same rank, the coordinate inclusion furnished by global pseudobases has
torsion cokernel. -/
theorem same_submodule_pseudobasis
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (hrank : Module.finrank A N = Module.finrank A M) :
    ∃ (m n : ℕ) (I : Fin m → Ideal A) (J : Fin n → Ideal A)
      (eM : M ≃ₗ[A] ⨁ i, I i) (eN : N ≃ₗ[A] ⨁ j, J j)
      (f : (⨁ j, J j) →ₗ[A] (⨁ i, I i)),
      Function.Injective f ∧
        (∀ x : N, f (eN x) = eM x.1) ∧
        Module.finrank A (⨁ j, J j) = Module.finrank A (⨁ i, I i) ∧
        Module.IsTorsion A ((⨁ i, I i) ⧸ LinearMap.range f) := by
  obtain ⟨m, n, I, J, eM, eN, f, hf, hcomm⟩ :=
    dedekind_pseudobasis A M N
  letI : Module.Finite A (⨁ i, I i) := Module.Finite.equiv eM
  have hfinrank :
      Module.finrank A (⨁ j, J j) = Module.finrank A (⨁ i, I i) := by
    rw [← eN.finrank_eq, ← eM.finrank_eq]
    exact hrank
  have hrange : Module.finrank A (LinearMap.range f) =
      Module.finrank A (⨁ j, J j) := LinearMap.finrank_range_of_inj hf
  have hquot : Module.finrank A ((⨁ i, I i) ⧸ LinearMap.range f) = 0 := by
    have hadd := (LinearMap.range f).finrank_quotient_add_finrank
    omega
  refine ⟨m, n, I, J, eM, eN, f, hf, hcomm, hfinrank, ?_⟩
  exact Module.finrank_eq_zero_iff_isTorsion.mp hquot

/-- A same-rank inclusion admits square global pseudobases consisting of nonzero
ideals.  In these coordinates the inclusion is injective and has torsion cokernel. -/
theorem dedekind_submodule_pseudobasis
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (hrank : Module.finrank A N = Module.finrank A M) :
    ∃ (n : ℕ) (I J : Fin n → Ideal A),
      (∀ i, I i ≠ ⊥) ∧ (∀ j, J j ≠ ⊥) ∧
      ∃ (eM : M ≃ₗ[A] ⨁ i, I i) (eN : N ≃ₗ[A] ⨁ j, J j)
        (f : (⨁ j, J j) →ₗ[A] (⨁ i, I i)),
        Function.Injective f ∧
          (∀ x : N, f (eN x) = eM x.1) ∧
          Module.IsTorsion A ((⨁ i, I i) ⧸ LinearMap.range f) := by
  letI : Module.Finite A N := Module.Finite.of_fg (IsNoetherian.noetherian N)
  obtain ⟨m, I, hI, ⟨eM⟩⟩ :=
    direct_nonzero_ideals A M
  obtain ⟨n, J, hJ, ⟨eN⟩⟩ :=
    direct_nonzero_ideals A N
  have hM : Module.finrank A M = m := by
    rw [eM.finrank_eq]
    exact ideals_direct_finrank A m I hI
  have hN : Module.finrank A N = n := by
    rw [eN.finrank_eq]
    exact ideals_direct_finrank A n J hJ
  have hmn : m = n := by omega
  let eIdx : Fin m ≃ Fin n := finCongr hmn
  let I' : Fin n → Ideal A := fun i => I (eIdx.symm i)
  have hI' : ∀ i, I' i ≠ ⊥ := fun i => hI (eIdx.symm i)
  let eM' : M ≃ₗ[A] ⨁ i, I' i := eM ≪≫ₗ
    DirectSum.lequivCongrLeft (M := fun i => ↑(I i)) A eIdx
  let f : (⨁ j, J j) →ₗ[A] (⨁ i, I' i) :=
    eM'.toLinearMap.comp (N.subtype.comp eN.symm.toLinearMap)
  have hf : Function.Injective f :=
    eM'.injective.comp (N.injective_subtype.comp eN.symm.injective)
  letI : Module.Finite A (⨁ i, I' i) := Module.Finite.equiv eM'
  have hquot : Module.finrank A ((⨁ i, I' i) ⧸ LinearMap.range f) = 0 := by
    have hrange : Module.finrank A (LinearMap.range f) = n := by
      rw [LinearMap.finrank_range_of_inj hf,
        ideals_direct_finrank A n J hJ]
    have hadd := (LinearMap.range f).finrank_quotient_add_finrank
    rw [ideals_direct_finrank A n I' hI'] at hadd
    omega
  refine ⟨n, I', J, hI', hJ, eM', eN, f, hf, ?_, ?_⟩
  · intro x
    simp [f]
  · exact Module.finrank_eq_zero_iff_isTorsion.mp hquot

end Submission.NumberTheory.Milne
