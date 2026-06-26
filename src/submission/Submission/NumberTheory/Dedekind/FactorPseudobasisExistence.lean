import Submission.NumberTheory.Dedekind.FactorPseudobasisRecursive
import Submission.NumberTheory.Dedekind.RankRecursionHelpers


/-!
# Rank-sized simultaneous invariant-factor pseudobases

An invariant-factor presentation of the quotient may contain arbitrarily many zero cyclic
summands.  This file recursively removes a final nonzero cyclic summand from the ambient lattice
and returns a presentation indexed by the rank of the ambient module.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u

/-- Any antitone cyclic presentation of the quotient can be realized by simultaneous
pseudobases indexed by the rank of the ambient lattice. -/
theorem rank_invariant_pseudobasis
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin n → Ideal A) (hb : Antitone b)
    (e : (M ⧸ N) ≃ₗ[A]
      DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i))) :
    ∃ c : Fin (Module.finrank A M) → Ideal A,
      Antitone c ∧
        Nonempty
          (IFPseudo A M N (Module.finrank A M) c) ∧
        Nonempty ((M ⧸ N) ≃ₗ[A]
          DirectSum (Fin (Module.finrank A M))
            (fun i ↦ idealQuotientModule A (c i))) := by
  classical
  induction hM : Module.finrank A M using Nat.strong_induction_on generalizing M n with
  | h rank ih =>
      cases rank with
      | zero =>
          letI : Subsingleton M := Module.finrank_zero_iff.mp hM
          have hN : N = ⊤ := by
            rw [eq_top_iff]
            intro x _
            have hx : x = 0 := Subsingleton.elim _ _
            simp [hx]
          let c : Fin 0 → Ideal A := Fin.elim0
          refine ⟨c, ?_, ?_, ?_⟩
          · intro i
            exact Fin.elim0 i
          · exact invariant_pseudobasis_top A M N hN 0 c
              (fun i ↦ Fin.elim0 i) hM
          · letI : Subsingleton (M ⧸ N) := inferInstance
            letI : Subsingleton
                (DirectSum (Fin 0) (fun i ↦ idealQuotientModule A (c i))) :=
              inferInstance
            exact ⟨LinearEquiv.ofSubsingleton _ _⟩
      | succ rank =>
          cases n with
          | zero =>
              have hsource : ∀ y : M ⧸ N, y = 0 := by
                intro y
                apply e.injective
                ext i
                exact Fin.elim0 i
              have hN : N = ⊤ := by
                apply Submodule.Quotient.subsingleton_iff.mp
                exact ⟨fun x y ↦ (hsource x).trans (hsource y).symm⟩
              let c : Fin (rank + 1) → Ideal A := fun _ ↦ ⊤
              refine ⟨c, antitone_const, ?_, ?_⟩
              · exact invariant_pseudobasis_top A M N hN
                  (rank + 1) c (fun _ ↦ rfl) hM
              · letI : Subsingleton (M ⧸ N) :=
                  Submodule.Quotient.subsingleton_iff.mpr hN
                letI : ∀ i, Unique (idealQuotientModule A (c i)) :=
                  fun _ ↦ Classical.choice
                    (Submodule.unique_quotient_iff_eq_top.mpr rfl)
                exact ⟨LinearEquiv.ofSubsingleton _ _⟩
          | succ n =>
              by_cases hlast : b (Fin.last n) = ⊤
              · have hbtop : ∀ i, b i = ⊤ := by
                  intro i
                  apply top_unique
                  simpa [hlast] using hb (Fin.le_last i)
                have htarget : ∀ y : DirectSum (Fin (n + 1))
                    (fun i ↦ idealQuotientModule A (b i)), y = 0 := by
                  intro y
                  ext i
                  letI : Unique (idealQuotientModule A (b i)) :=
                    Classical.choice
                      (Submodule.unique_quotient_iff_eq_top.mpr (hbtop i))
                  exact Subsingleton.elim _ _
                have hsource : ∀ y : M ⧸ N, y = 0 := by
                  intro y
                  apply e.injective
                  simpa using htarget (e y)
                have hN : N = ⊤ := by
                  apply Submodule.Quotient.subsingleton_iff.mp
                  exact ⟨fun x y ↦ (hsource x).trans (hsource y).symm⟩
                let c : Fin (rank + 1) → Ideal A := fun _ ↦ ⊤
                refine ⟨c, antitone_const, ?_, ?_⟩
                · exact invariant_pseudobasis_top A M N hN
                    (rank + 1) c (fun _ ↦ rfl) hM
                · letI : Subsingleton (M ⧸ N) :=
                    Submodule.Quotient.subsingleton_iff.mpr hN
                  letI : ∀ i, Unique (idealQuotientModule A (c i)) :=
                    fun _ ↦ Classical.choice
                      (Submodule.unique_quotient_iff_eq_top.mpr rfl)
                  exact ⟨LinearEquiv.ofSubsingleton _ _⟩
              · obtain ⟨f, r, hr, hJ, eM, eN, ePrefix, hcomm⟩ :=
                  invariant_pseudobasis_step
                    A M N n b hb e hlast
                let K := LinearMap.ker f
                let P := Submodule.comap K.subtype N
                let J := LinearMap.range f
                letI : Module.Finite A K :=
                  Module.Finite.of_fg (IsNoetherian.noetherian _)
                letI : Module.Finite A J :=
                  Module.Finite.of_fg (IsNoetherian.noetherian _)
                have hfinJ : Module.finrank A J = 1 := by
                  apply Nat.le_antisymm
                  · simpa [J] using
                      LinearMap.finrank_le_finrank_of_injective
                        (LinearMap.range f).injective_subtype
                  · exact (Submodule.one_le_finrank_iff).2 hJ
                have hfinK : Module.finrank A K + 1 = rank + 1 := by
                  have hfinQuotient : Module.finrank A (M ⧸ K) = 1 := by
                    exact f.quotKerEquivRange.finrank_eq.trans hfinJ
                  have hsum := K.finrank_quotient_add_finrank
                  omega
                have hfinK_lt : Module.finrank A K < rank + 1 := by
                  omega
                have hfinK_eq : Module.finrank A K = rank := by
                  omega
                have hbPrefix :
                    Antitone (fun i : Fin n ↦ b i.castSucc) := by
                  intro i j hij
                  exact hb (Fin.castSucc_le_castSucc_iff.mpr hij)
                obtain ⟨c, hc, ⟨d⟩, ⟨eRecursive⟩⟩ :=
                  ih (Module.finrank A K) hfinK_lt K P n
                    (fun i : Fin n ↦ b i.castSucc) hbPrefix ePrefix rfl
                subst rank
                let I := b (Fin.last n)
                have hIM : I • (⊤ : Submodule A M) ≤ N := by
                  exact invariant_smul_submodule
                    A M N n b hb e
                have hIP : I • (⊤ : Submodule A K) ≤ P := by
                  rw [Submodule.smul_le]
                  intro a ha x _
                  change a • (x : M) ∈ N
                  exact hIM (Submodule.smul_mem_smul ha Submodule.mem_top)
                have hIann :
                    I ≤ Module.annihilator A (K ⧸ P) :=
                  annihilator_smul_top A K I P hIP
                have hIle : ∀ i, I ≤ c i := by
                  rw [eRecursive.annihilator_eq,
                    annihilator_direct_quotients] at hIann
                  intro i
                  exact hIann.trans (iInf_le c i)
                let c' : Fin (Module.finrank A K + 1) → Ideal A :=
                  Fin.snoc c I
                have hc' : Antitone c' :=
                  antitone_fin_snoc c hc I hIle
                have hd' :
                    Nonempty
                      (IFPseudo A M N
                        (Module.finrank A K + 1) c') := by
                  have dPrefix :
                      IFPseudo A K P
                        (Module.finrank A K)
                        (fun i ↦ c' i.castSucc) := by
                    simpa only [c', Fin.snoc_castSucc] using d
                  let hlast : (J * I : Ideal A) =
                      J * c' (Fin.last (Module.finrank A K)) := by
                    simp [c']
                  let eN' : N ≃ₗ[A]
                      P × (J * c' (Fin.last (Module.finrank A K)) : Ideal A) :=
                    eN ≪≫ₗ (LinearEquiv.refl A P).prodCongr
                      (LinearEquiv.ofEq _ _ hlast)
                  have hcomm' : ∀ x : N,
                      eM x.1 = ((eN' x).1.1,
                        Submodule.inclusion Ideal.mul_le_right (eN' x).2) := by
                    intro x
                    simpa [eN', hlast, LinearEquiv.prodCongr_apply] using hcomm x
                  exact ⟨dPrefix.appendLast c' P N J hJ eM eN' hcomm'⟩
                let splitOld := invariantSplitLast A n b
                let splitNew :
                    DirectSum (Fin (Module.finrank A K + 1))
                        (fun i ↦ idealQuotientModule A (c' i)) ≃ₗ[A]
                      (DirectSum (Fin (Module.finrank A K))
                          (fun i ↦ idealQuotientModule A (c i))) ×
                        idealQuotientModule A I := by
                  let raw := invariantSplitLast
                    A (Module.finrank A K) c'
                  let normalizePrefix := directCongrRight
                    (fun i : Fin (Module.finrank A K) ↦
                      idealQuotientModule A (c' i.castSucc))
                    (fun i ↦ idealQuotientModule A (c i))
                    (fun i ↦ Submodule.quotEquivOfEq _ _ (by simp [c']))
                  let normalizeLast :
                      idealQuotientModule A
                          (c' (Fin.last (Module.finrank A K))) ≃ₗ[A]
                        idealQuotientModule A I :=
                    Submodule.quotEquivOfEq _ _ (by simp [c'])
                  exact raw ≪≫ₗ normalizePrefix.prodCongr normalizeLast
                let replacePrefix :
                    DirectSum (Fin n)
                        (fun i ↦ idealQuotientModule A (b i.castSucc)) ≃ₗ[A]
                      DirectSum (Fin (Module.finrank A K))
                        (fun i ↦ idealQuotientModule A (c i)) :=
                  ePrefix.symm ≪≫ₗ eRecursive
                let e' :
                    (M ⧸ N) ≃ₗ[A]
                      DirectSum (Fin (Module.finrank A K + 1))
                        (fun i ↦ idealQuotientModule A (c' i)) :=
                  e ≪≫ₗ splitOld ≪≫ₗ
                    replacePrefix.prodCongr
                      (LinearEquiv.refl A
                        (idealQuotientModule A I)) ≪≫ₗ
                    splitNew.symm
                exact ⟨c', hc', hd', ⟨e'⟩⟩

end Submission.NumberTheory.Milne
