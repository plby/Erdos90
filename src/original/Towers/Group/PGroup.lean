import Mathlib


noncomputable section

namespace Towers

lemma p_pi_fintype
    {p : ℕ} {ι : Type*} [Finite ι]
    {Γ : ι → Type*} [∀ i, Group (Γ i)] [∀ i, Finite (Γ i)]
    [Fact p.Prime]
    (hΓ : ∀ i, IsPGroup p (Γ i)) :
    IsPGroup p (∀ i, Γ i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun i =>
    (IsPGroup.iff_card.mp (hΓ i) :
      ∃ n : ℕ, Nat.card (Γ i) = p ^ n)
  refine IsPGroup.of_card (n := ∑ i, n i) ?_
  rw [Nat.card_pi]
  calc
    (∏ i, Nat.card (Γ i)) = ∏ i, p ^ n i := by
      exact Finset.prod_congr rfl (fun i _hi => hn i)
    _ = p ^ ∑ i, n i := by
      simpa using
        (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset ι) n p)

lemma p_card_coprime
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ]
    (H : Subgroup Γ)
    (hH : IsPGroup p H)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Nat.card H = 1 := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp_not_dvd_card :
      ¬ p ∣ Nat.card Γ := by
    exact (hp.coprime_iff_not_dvd).mp hCardCoprime
  have hH_card_cases :
      Nat.card H = 1 ∨ p ∣ Nat.card H := by
    exact hH.card_eq_or_dvd
  rcases hH_card_cases with hH_card_one | hp_dvd_H
  · exact hH_card_one
  · have hH_dvd_card :
        Nat.card H ∣ Nat.card Γ := by
      exact Subgroup.card_subgroup_dvd_card H
    have hp_dvd_card :
        p ∣ Nat.card Γ := by
      exact dvd_trans hp_dvd_H hH_dvd_card
    exact False.elim (hp_not_dvd_card hp_dvd_card)

lemma bot_coprime_card
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ]
    (H : Subgroup Γ)
    (hH : IsPGroup p H)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    H = ⊥ := by
  classical
  have hH_card_one :
      Nat.card H = 1 := by
    exact
      p_card_coprime
        H hH hCardCoprime
  exact H.eq_bot_of_card_eq hH_card_one

lemma monoid_coprime_card
    {p : ℕ} [Fact p.Prime]
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ)
    (hKer : IsPGroup p χ.ker)
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Function.Injective χ := by
  classical
  have hKer_bot :
      χ.ker = ⊥ := by
    exact
      bot_coprime_card
        χ.ker hKer hCardCoprime
  exact (MonoidHom.ker_eq_bot_iff χ).mp hKer_bot

lemma monoid_ker_comp
    {Γ Δ Δ' : Type*} [Group Γ] [Group Δ] [Group Δ']
    (e : Δ ≃* Δ') (χ : Γ →* Δ) :
    (e.toMonoidHom.comp χ).ker = χ.ker := by
  ext γ
  simp [MonoidHom.mem_ker]

lemma p_ker_comp
    {p : ℕ}
    {Γ Δ Δ' : Type*} [Group Γ] [Group Δ] [Group Δ']
    (e : Δ ≃* Δ') (χ : Γ →* Δ)
    (hχ : IsPGroup p χ.ker) :
    IsPGroup p (e.toMonoidHom.comp χ).ker := by
  rw [monoid_ker_comp e χ]
  exact hχ

lemma p_group_sylow
    {p : ℕ} {Γ : Type*} [Group Γ]
    (S : Sylow p Γ) (H : Subgroup Γ)
    (hH : H ≤ (S : Subgroup Γ)) :
    IsPGroup p H := by
  classical
  have hSylow :
      IsPGroup p (S : Subgroup Γ) := by
    exact S.isPGroup'
  have hH' :
      IsPGroup p H := by
    exact hSylow.to_le hH
  exact hH'

lemma p_ker_sylow
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (S : Sylow p Γ)
    (hKer : χ.ker ≤ (S : Subgroup Γ)) :
    IsPGroup p χ.ker := by
  classical
  have hKerP :
      IsPGroup p χ.ker := by
    exact p_group_sylow S χ.ker hKer
  exact hKerP

lemma sylow_p_group
    {p : ℕ} {Γ : Type*} [Group Γ]
    (H : Subgroup Γ) (hH : IsPGroup p H) :
    ∃ S : Sylow p Γ, H ≤ (S : Subgroup Γ) := by
  classical
  have hExists :
      ∃ S : Sylow p Γ, H ≤ (S : Subgroup Γ) := by
    exact hH.exists_le_sylow
  exact hExists

lemma monoid_sylow_p
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (hKer : IsPGroup p χ.ker) :
    ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
  classical
  have hExists :
      ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
    exact sylow_p_group χ.ker hKer
  exact hExists

lemma monoid_p_sylow
    {p : ℕ} {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) :
    IsPGroup p χ.ker ↔
      ∃ S : Sylow p Γ, χ.ker ≤ (S : Subgroup Γ) := by
  constructor
  · intro hKer
    exact monoid_sylow_p χ hKer
  · rintro ⟨S, hKerS⟩
    exact p_ker_sylow χ S hKerS

lemma monoid_sylow_coprime
    {p : ℕ} [Fact p.Prime]
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    (χ : Γ →* Δ) (S : Sylow p Γ)
    (hKer : χ.ker ≤ (S : Subgroup Γ))
    (hCardCoprime : Nat.Coprime p (Nat.card Γ)) :
    Function.Injective χ := by
  classical
  have hKerP :
      IsPGroup p χ.ker := by
    exact p_ker_sylow χ S hKer
  have hInjective :
      Function.Injective χ := by
    exact
      monoid_coprime_card
        χ hKerP hCardCoprime
  exact hInjective

lemma p_no_ne
    {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : Nat.Prime p)
    (hno : ∀ {ℓ : ℕ}, Nat.Prime ℓ → ℓ ≠ p →
      ¬ ∃ g : Γ, g ≠ 1 ∧ orderOf g = ℓ) :
    IsPGroup p Γ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_card]
  have hΓ : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  suffices hprimeFactors :
      ∀ ℓ ∈ (Nat.card Γ).primeFactorsList, ℓ = p by
    refine ⟨(Nat.card Γ).primeFactorsList.length, ?_⟩
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem hprimeFactors,
      Nat.prod_primeFactorsList hΓ]
  intro ℓ hℓmem
  obtain ⟨hℓprime, hℓdvd⟩ := (Nat.mem_primeFactorsList hΓ).mp hℓmem
  by_contra hℓ_ne_p
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  obtain ⟨g, hg_order⟩ :=
    @exists_prime_orderOf_dvd_card' Γ _ _ ℓ ⟨hℓprime⟩ hℓdvd
  have hg_ne_one : g ≠ 1 := by
    intro hg_one
    have horder_one : orderOf g = 1 := by
      simp [hg_one]
    exact hℓprime.ne_one (hg_order.symm.trans horder_one)
  exact hno hℓprime hℓ_ne_p ⟨g, hg_ne_one, hg_order⟩

lemma quotient_id_surjective
    {Γ : Type*} [Group Γ]
    {H K : Subgroup Γ} [H.Normal] [K.Normal]
    (hHK : H ≤ K) :
    Function.Surjective
      (QuotientGroup.map H K (MonoidHom.id Γ) (by
        intro g hg
        exact hHK hg)) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K y
  exact ⟨QuotientGroup.mk' H g, rfl⟩

lemma bot_injective_pi
    {Γ : Type*} [Group Γ]
    {ι : Type*} {Γi : ι → Type*} [∀ i, Group (Γi i)]
    (Φ : Γ →* ∀ i, Γi i)
    (hΦ : Function.Injective Φ)
    (H : Subgroup Γ)
    (hH : ∀ σ : H, ∀ i, Φ σ i = 1) :
    H = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall H).2 ?_
  intro σ hσ
  apply hΦ
  funext i
  have hComponent : Φ (⟨σ, hσ⟩ : H) i = 1 :=
    hH ⟨σ, hσ⟩ i
  simpa using hComponent

lemma p_dvd_only
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ]
    (h : ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Γ → l = p) :
    IsPGroup p Γ := by
  classical
  have hcard_ne_zero : Nat.card Γ ≠ 0 := by
    exact (Nat.card_ne_zero).2 ⟨⟨1⟩, inferInstance⟩
  refine IsPGroup.of_card (n := (Nat.card Γ).primeFactorsList.length) ?_
  exact
    Nat.eq_prime_pow_of_unique_prime_dvd hcard_ne_zero
      (by
        intro l hl hldiv
        exact h l hl hldiv)

lemma divisor_p_group
    {p : ℕ} [Fact p.Prime]
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup p Γ) :
    ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Γ → l = p := by
  classical
  intro l hl hldiv
  obtain ⟨n, hcard⟩ :=
    (IsPGroup.iff_card.mp hΓ : ∃ n, Nat.card Γ = p ^ n)
  have hldivpow : l ∣ p ^ n := by
    simpa [hcard] using hldiv
  have hldivp : l ∣ p :=
    hl.dvd_of_dvd_pow hldivpow
  exact (Nat.prime_dvd_prime_iff_eq hl (Fact.out : Nat.Prime p)).mp hldivp

lemma dvd_card_or
    {Γ : Type*} [Group Γ] [Finite Γ]
    (N : Subgroup Γ) [N.Normal] :
    ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Γ →
      l ∣ Nat.card N ∨ l ∣ Nat.card (Γ ⧸ N) := by
  classical
  intro l hl hldiv
  have hcard : Nat.card (Γ ⧸ N) * Nat.card N = Nat.card Γ := by
    rw [← Subgroup.index_eq_card N]
    exact Subgroup.index_mul_card N
  have hldiv_mul : l ∣ Nat.card (Γ ⧸ N) * Nat.card N := by
    rw [hcard]
    exact hldiv
  rcases (Nat.Prime.dvd_mul hl).1 hldiv_mul with hquot | hsub
  · exact Or.inr hquot
  · exact Or.inl hsub

lemma prime_divisor_normal
    {p : ℕ}
    {Γ : Type*} [Group Γ] [Finite Γ]
    (N : Subgroup Γ) [N.Normal]
    (hN : ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card N → l = p)
    (hQ : ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card (Γ ⧸ N) → l = p) :
    ∀ l : ℕ, Nat.Prime l → l ∣ Nat.card Γ → l = p := by
  classical
  intro l hl hldiv
  rcases dvd_card_or N l hl hldiv with hsub | hquot
  · exact hN l hl hsub
  · exact hQ l hl hquot

lemma lift_injective_ker
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    (N : Subgroup Γ) [N.Normal]
    (ψ : Γ →* Δ)
    (hN_le : N ≤ ψ.ker)
    (hker : ψ.ker = N) :
    Function.Injective (QuotientGroup.lift N ψ hN_le) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [MonoidHom.mem_ker] at hz
    change ψ x = 1 at hz
    have hxker : x ∈ ψ.ker := hz
    have hxN : x ∈ N := by
      simpa [hker] using hxker
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).2 hxN
  · exact bot_le

end Towers
