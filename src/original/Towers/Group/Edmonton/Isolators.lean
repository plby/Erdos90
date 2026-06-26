import Towers.Group.Edmonton.HallCommutatorIdentities
import Towers.Group.Edmonton.VerbalSubgroups

/-!
# The Edmonton Notes on Nilpotent Groups: Section 4 isolators

This file begins Section 4 with Hall's bilinearity lemma for commutators.
-/

namespace Towers
namespace Edmonton

open scoped commutatorElement IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- If `[X,Y,G] = 1`, every element of `[X,Y]` commutes with every element
of `G`. -/
lemma commute_triple_bot
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥)
    {c : G} (hc : c ∈ ⁅X, Y⁆) (g : G) :
    Commute c g := by
  rw [← commutatorElement_eq_one_iff_commute]
  exact Subgroup.mem_bot.mp
    (h ▸ Subgroup.commutator_mem_commutator hc (Subgroup.mem_top g))

/-- Conjugating by a commuting element fixes an element. -/
lemma conjugate_self_commute {x y : G} (h : Commute x y) :
    hallConjugate x y = x := by
  simp [hallConjugate, mul_assoc, h.eq]

/-- Under `[X,Y,G]=1`, Hall's commutator is multiplicative in its first
argument. -/
lemma left_triple_bot
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥)
    {x₁ x₂ y : G} (hx₁ : x₁ ∈ X) (hy : y ∈ Y) :
    hallCommutator (x₁ * x₂) y =
      hallCommutator x₁ y * hallCommutator x₂ y := by
  rw [commutator_mul_left]
  rw [conjugate_self_commute
    (commute_triple_bot h
      (hall_commutator hx₁ hy) x₂)]

/-- Under `[X,Y,G]=1`, Hall's commutator is multiplicative in its second
argument. -/
lemma commutator_triple_bot
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥)
    {x y₁ y₂ : G} (hx : x ∈ X) (hy₁ : y₁ ∈ Y) :
    hallCommutator x (y₁ * y₂) =
      hallCommutator x y₁ * hallCommutator x y₂ := by
  rw [commutator_mul_right]
  rw [conjugate_self_commute
    (commute_triple_bot h
      (hall_commutator hx hy₁) y₂)]
  exact
    (commute_triple_bot h
      (hall_commutator hx hy₁) (hallCommutator x y₂)).eq.symm

/-- For fixed `y`, Hall's commutator is a homomorphism on `X` when
`[X,Y,G]=1`. -/
def commutatorLeftHom
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥) (y : Y) :
    X →* G where
  toFun x := hallCommutator x y
  map_one' := by simp [hallCommutator]
  map_mul' x₁ x₂ :=
    left_triple_bot h x₁.2 y.2

/-- For fixed `x`, Hall's commutator is a homomorphism on `Y` when
`[X,Y,G]=1`. -/
def commutatorRightHom
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥) (x : X) :
    Y →* G where
  toFun y := hallCommutator x y
  map_one' := by simp [hallCommutator]
  map_mul' y₁ y₂ :=
    commutator_triple_bot h x.2 y₁.2

/-- **Hall, Lemma 4.1.** If `[X,Y,G]=1`, the commutator function is
homomorphic in both arguments. -/
theorem commutator_homomorphic_triple
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥) :
    (∀ y : Y, ∀ x : X,
      commutatorLeftHom h y x = hallCommutator (x : G) (y : G)) ∧
      (∀ x : X, ∀ y : Y,
        commutatorRightHom h x y = hallCommutator (x : G) (y : G)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Hall's example after Lemma 4.1: `[Z₂,G'] = 1`. -/
theorem upper_series_bot :
    ⁅Subgroup.upperCentralSeries G 2, commutator G⁆ = ⊥ := by
  simpa only [Subgroup.lowerCentralSeries_one] using upper_lower_bot (G := G) 2

/-- Hall's commutator is trivial exactly when its arguments commute. -/
lemma hall_commutator_commute (x y : G) :
    hallCommutator x y = 1 ↔ Commute x y := by
  rw [hall_element_inv,
    commutatorElement_eq_one_iff_commute, Commute.inv_inv_iff]

/-- Under `[X,Y,G]=1`, Hall's commutator takes powers in its first argument
to powers. -/
lemma hall_triple_bot
    {X Y : Subgroup G} (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ = ⊥)
    {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (n : ℕ) :
    hallCommutator (x ^ n) y = hallCommutator x y ^ n := by
  simpa using (commutatorLeftHom h ⟨y, hy⟩).map_pow ⟨x, hx⟩ n

/-- If `[X,Y,G] ≤ N`, the first-argument commutator power formula holds
modulo the normal subgroup `N`. -/
lemma commutator_left_mod
    {X Y N : Subgroup G} [N.Normal]
    (h : ⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆ ≤ N)
    {x y : G} (hx : x ∈ X) (hy : y ∈ Y) (n : ℕ) :
    hallCommutator (x ^ n) y * (hallCommutator x y ^ n)⁻¹ ∈ N := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hmap0 : (⁅⁅X, Y⁆, (⊤ : Subgroup G)⁆).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa [f, QuotientGroup.ker_mk'] using h
  have hmap :
      ⁅⁅X.map f, Y.map f⁆, (⊤ : Subgroup (G ⧸ N))⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective N)] using hmap0
  have heq :=
    hall_triple_bot hmap
      (Subgroup.mem_map_of_mem f hx) (Subgroup.mem_map_of_mem f hy) n
  have himage :
      f (hallCommutator (x ^ n) y) = f (hallCommutator x y) ^ n := by
    simpa [hallCommutator] using heq
  rw [← QuotientGroup.ker_mk' N]
  change f (hallCommutator (x ^ n) y * (hallCommutator x y ^ n)⁻¹) = 1
  rw [map_mul, map_inv, map_pow, himage]
  exact mul_inv_cancel _

/-- A subgroup has exponent dividing `m` when every one of its elements has
`m`th power equal to one. -/
def SubgroupHasExponent (H : Subgroup G) (m : ℕ) : Prop :=
  ∀ x ∈ H, x ^ m = 1

/-- The base case in Hall's proof of Lemma 4.2: if `Z₁` has exponent `m`,
then `Z₂/Z₁` has exponent `m`. -/
theorem upper_mod_center {m : ℕ}
    (hcenter : SubgroupHasExponent (Subgroup.center G) m) :
    ∀ x ∈ Subgroup.upperCentralSeries G 2, x ^ m ∈ Subgroup.upperCentralSeries G 1 := by
  have htriple :
      ⁅⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact
      (Subgroup.commutator_mono
        (upper_series_commutator (G := G) 1) le_rfl).trans
          (upper_series_commutator (G := G) 0)
  intro x hx
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro y
  have hc_mem : hallCommutator x y ∈ Subgroup.center G := by
    rw [← Subgroup.upperCentralSeries_one]
    exact
      upper_series_commutator (G := G) 1
        (hall_commutator hx (Subgroup.mem_top y))
  have hpow :
      hallCommutator (x ^ m) y = 1 := by
    rw [hall_triple_bot htriple
      hx (Subgroup.mem_top y), hcenter _ hc_mem]
  exact (hall_commutator_commute (x ^ m) y).mp hpow |>.eq.symm

/-- If every successive upper-central factor has exponent `m`, then `Z_r`
has exponent `m^r`. This is the inductive second half of Hall's Lemma 4.2. -/
theorem upper_exponent_layers
    {m : ℕ}
    (hlayer : ∀ r x, x ∈ Subgroup.upperCentralSeries G (r + 1) →
      x ^ m ∈ Subgroup.upperCentralSeries G r) :
    ∀ r, SubgroupHasExponent (Subgroup.upperCentralSeries G r) (m ^ r) := by
  intro r
  induction r with
  | zero =>
      intro x hx
      rw [Subgroup.upperCentralSeries_zero] at hx
      rw [Subgroup.mem_bot.mp hx]
      simp
  | succ r ih =>
      intro x hx
      have hxm : x ^ m ∈ Subgroup.upperCentralSeries G r :=
        hlayer r x hx
      have hpow := ih (x ^ m) hxm
      simpa only [pow_mul, pow_succ, Nat.mul_comm] using hpow

/-- If the center has exponent `m`, every successive upper-central factor
has exponent `m`. -/
theorem upper_exponent_center
    {m : ℕ} (hcenter : SubgroupHasExponent (Subgroup.center G) m) :
    ∀ r x, x ∈ Subgroup.upperCentralSeries G (r + 1) →
      x ^ m ∈ Subgroup.upperCentralSeries G r := by
  intro r
  induction r with
  | zero =>
      intro x hx
      rw [Subgroup.upperCentralSeries_one] at hx
      exact Subgroup.mem_bot.mpr (hcenter x hx)
  | succ r ih =>
      intro x hx
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro y
      let N : Subgroup G := Subgroup.upperCentralSeries G r
      have htriple :
          ⁅⁅Subgroup.upperCentralSeries G ((r + 1) + 1), (⊤ : Subgroup G)⁆,
              (⊤ : Subgroup G)⁆ ≤ N := by
        calc
          ⁅⁅Subgroup.upperCentralSeries G ((r + 1) + 1), (⊤ : Subgroup G)⁆,
              (⊤ : Subgroup G)⁆ ≤
              ⁅Subgroup.upperCentralSeries G (r + 1), (⊤ : Subgroup G)⁆ :=
            Subgroup.commutator_mono
              (upper_series_commutator (G := G) (r + 1)) le_rfl
          _ ≤ N := upper_series_commutator (G := G) r
      have hmod :
          hallCommutator ((x⁻¹) ^ m) y⁻¹ *
              (hallCommutator x⁻¹ y⁻¹ ^ m)⁻¹ ∈ N :=
        commutator_left_mod htriple
          ((Subgroup.upperCentralSeries G ((r + 1) + 1)).inv_mem hx)
          (Subgroup.mem_top y⁻¹) m
      have hxy :
          ⁅x, y⁆ ∈ Subgroup.upperCentralSeries G (r + 1) :=
        upper_series_commutator (G := G) (r + 1)
          (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
      have hright : hallCommutator x⁻¹ y⁻¹ ^ m ∈ N := by
        rw [← commutator_element_inv]
        exact ih _ hxy
      have hleft : hallCommutator ((x⁻¹) ^ m) y⁻¹ ∈ N := by
        have hprod := N.mul_mem hmod hright
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hprod
      change ⁅x ^ m, y⁆ ∈ N
      rw [commutator_element_inv]
      simpa only [inv_pow] using hleft

/-- **Hall, Lemma 4.2.** If the center has exponent `m`, each factor
`Z_{r+1}/Z_r` has exponent `m`, and `Z_r` has exponent `m^r`. -/
theorem upper_exponent_bounds {m : ℕ}
    (hcenter : SubgroupHasExponent (Subgroup.center G) m) :
    (∀ r x, x ∈ Subgroup.upperCentralSeries G (r + 1) →
        x ^ m ∈ Subgroup.upperCentralSeries G r) ∧
      ∀ r, SubgroupHasExponent (Subgroup.upperCentralSeries G r) (m ^ r) := by
  have hlayer :=
    upper_exponent_center (G := G) hcenter
  exact ⟨hlayer, upper_exponent_layers hlayer⟩

/-- **Hall, Corollary to Lemma 4.2.** A finitely generated nilpotent group
whose center is a `p`-group is itself a finite `p`-group. -/
theorem p_group_center {p : ℕ} [Fact p.Prime]
    [Group.FG G] [Group.IsNilpotent G]
    (hcenterP : IsPGroup p (Subgroup.center G)) :
    Finite G ∧ IsPGroup p G := by
  have htopfg : (⊤ : Subgroup G).FG := Group.FG.out
  have hcenterfg : (Subgroup.center G).FG :=
    fg_nilpotent htopfg le_top
  letI : Group.FG (Subgroup.center G) :=
    (Group.fg_iff_subgroup_fg (Subgroup.center G)).mpr hcenterfg
  have hcenterTorsion : Monoid.IsTorsion (Subgroup.center G) := by
    intro z
    obtain ⟨k, hk⟩ := hcenterP z
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p ^ k, pow_pos (Fact.out : p.Prime).pos k, hk⟩
  letI : Finite (Subgroup.center G) :=
    CommGroup.finite_of_fg_torsion (G := Subgroup.center G) hcenterTorsion
  obtain ⟨k, hcard⟩ := IsPGroup.iff_card.mp hcenterP
  have hcenterExp :
      SubgroupHasExponent (Subgroup.center G) (p ^ k) := by
    intro x hx
    have hpow :
        (⟨x, hx⟩ : Subgroup.center G) ^
            Nat.card (Subgroup.center G) = 1 :=
      pow_card_eq_one'
    have hpow' : x ^ Nat.card (Subgroup.center G) = 1 := by
      exact congrArg (fun z : Subgroup.center G ↦ (z : G)) hpow
    simpa [hcard] using hpow'
  let c := Group.nilpotencyClass G
  have htopExp :
      SubgroupHasExponent (Subgroup.upperCentralSeries G c) ((p ^ k) ^ c) :=
    (upper_exponent_bounds (G := G) hcenterExp).2 c
  have hGpow : ∀ g : G, g ^ p ^ (k * c) = 1 := by
    intro g
    have hg : g ∈ Subgroup.upperCentralSeries G c := by
      rw [Subgroup.upperCentralSeries_nilpotencyClass]
      exact Subgroup.mem_top g
    simpa only [pow_mul] using htopExp g hg
  have hGp : IsPGroup p G := fun g ↦ ⟨k * c, hGpow g⟩
  obtain ⟨_n, S, _hScard, hSgen⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  have hSorder : ∀ x ∈ S, IsOfFinOrder x := by
    intro x _hx
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨p ^ (k * c), pow_pos (Fact.out : p.Prime).pos _, hGpow x⟩
  exact ⟨(nilpotent_order_generators S hSgen hSorder).1, hGp⟩

/-- Adjoining a normal subgroup disjoint from `H` preserves relative
indices inside `H`. This is the index form of the second isomorphism
theorem used repeatedly in Hall's Lemma 4.3. -/
lemma rel_inf_bot
    {M K H : Subgroup G} [M.Normal] (hKH : K ≤ H)
    (hMH : M ⊓ H = ⊥) :
    (M ⊔ K).relIndex (M ⊔ H) = K.relIndex H := by
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let f : H →* G ⧸ M := q.comp H.subtype
  have hfker : f.ker = ⊥ := by
    have hdisjoint : Disjoint M H := disjoint_iff.mpr hMH
    dsimp [f, q]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.comap_subtype]
    exact Subgroup.subgroupOf_eq_bot.mpr hdisjoint
  have hf : Function.Injective f :=
    (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hKmap : (K.subgroupOf H).map f = K.map q := by
    change (K.subgroupOf H).map (q.comp H.subtype) = K.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKH]
  have hHmap : (⊤ : Subgroup H).map f = H.map q := by
    change (⊤ : Subgroup H).map (q.comp H.subtype) = H.map q
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, H.range_subtype]
  calc
    (M ⊔ K).relIndex (M ⊔ H) =
        (K.map q).relIndex (H.map q) := by
      rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk', sup_comm M K,
        sup_comm M H]
    _ = (K.subgroupOf H).relIndex (⊤ : Subgroup H) := by
      rw [← hKmap, ← hHmap,
        Subgroup.relIndex_map_map_of_injective _ _ hf]
    _ = K.relIndex H := by
      simpa using
        (Subgroup.relIndex_subgroupOf
          (H := K) (K := H) (L := H) le_rfl)

/-- Hall's observation before Lemma 4.3: under its index hypotheses, a
nontrivial normal subgroup can neither be contained in `K` nor meet `H`
trivially. -/
lemma normal_index_obstructions {p : ℕ} [Fact p.Prime]
    (H K : Subgroup G) (hKH : K ≤ H)
    (hindex : K.relIndex H = 0 ∨ p ∣ K.relIndex H)
    (hnormal : ∀ M : Subgroup G, M.Normal → M ≠ ⊥ →
      (M ⊔ K).relIndex (M ⊔ H) ≠ 0 ∧
        Nat.Coprime p ((M ⊔ K).relIndex (M ⊔ H)))
    (M : Subgroup G) (hMnormal : M.Normal) (hMne : M ≠ ⊥) :
    M ⊓ H ≠ ⊥ ∧ ¬ M ≤ K := by
  have hcontradiction :
      K.relIndex H ≠ 0 → Nat.Coprime p (K.relIndex H) → False := by
    intro hne hcoprime
    rcases hindex with hzero | hp
    · exact hne hzero
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime) hp
  constructor
  · intro hMH
    letI : M.Normal := hMnormal
    obtain ⟨hne, hcoprime⟩ := hnormal M hMnormal hMne
    rw [rel_inf_bot hKH hMH] at hne hcoprime
    exact hcontradiction hne hcoprime
  · intro hMK
    obtain ⟨hne, hcoprime⟩ := hnormal M hMnormal hMne
    have hsupK : M ⊔ K = K := sup_eq_right.mpr hMK
    have hsupH : M ⊔ H = H := sup_eq_right.mpr (hMK.trans hKH)
    rw [hsupK, hsupH] at hne hcoprime
    exact hcontradiction hne hcoprime

/-- In an infinite cyclic subgroup, the subgroup generated by the `n`th
power of a generator has relative index `n`. -/
lemma rel_zpowers_order
    (a : G) (n : ℕ) (ha : ¬ IsOfFinOrder a) :
    (Subgroup.zpowers (a ^ n)).relIndex (Subgroup.zpowers a) = n := by
  let P : Subgroup (Multiplicative ℤ) :=
    AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ))
  let f : Multiplicative ℤ →* G := zpowersHom G a
  have hf : Function.Injective f := by
    intro x y hxy
    exact Multiplicative.ext
      ((injective_zpow_iff_not_isOfFinOrder.mpr ha) hxy)
  have hP :
      P = Subgroup.zpowers (Multiplicative.ofAdd (n : ℤ)) := by
    ext z
    dsimp [P]
    rw [Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Multiplicative.ext (by simp [hk, mul_comm])⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp [mul_comm]⟩
  have hPmap : P.map f = Subgroup.zpowers (a ^ n) := by
    rw [hP, MonoidHom.map_zpowers]
    simp [f]
  have htopmap : (⊤ : Subgroup (Multiplicative ℤ)).map f =
      Subgroup.zpowers a := by
    rw [← MonoidHom.range_eq_map]
    rfl
  calc
    (Subgroup.zpowers (a ^ n)).relIndex (Subgroup.zpowers a) =
        P.relIndex (⊤ : Subgroup (Multiplicative ℤ)) := by
      rw [← hPmap, ← htopmap,
        Subgroup.relIndex_map_map_of_injective _ _ hf]
    _ = P.index := Subgroup.relIndex_top_right P
    _ = n := by
      simp [P, Int.index_zmultiples]

/-- Every subgroup of the center is normal. -/
lemma normal_center (N : Subgroup G)
    (hN : N ≤ Subgroup.center G) :
    N.Normal := by
  constructor
  intro n hn g
  have hcomm : g * n = n * g :=
    (Subgroup.mem_center_iff.mp (hN hn)) g
  simpa [hcomm, mul_assoc] using hn

/-- If `B ≤ A` are central and `A ∩ K = 1`, adjoining `K` preserves the
relative index `[A:B]`. -/
lemma rel_center_inf
    {A B K : Subgroup G} (hBA : B ≤ A)
    (hAcenter : A ≤ Subgroup.center G) (hAK : A ⊓ K = ⊥) :
    (B ⊔ K).relIndex (A ⊔ K) = B.relIndex A := by
  letI : B.Normal := normal_center B (hBA.trans hAcenter)
  have hInf : (B ⊔ K) ⊓ A = B := by
    apply le_antisymm
    · intro x hx
      obtain ⟨b, hb, k, hk, hbk⟩ :=
        (Subgroup.mem_sup_of_normal_left.mp hx.1)
      have hkA : k ∈ A := by
        have hprod := A.mul_mem (A.inv_mem (hBA hb)) hx.2
        simpa [← hbk, mul_assoc] using hprod
      have hk1 : k = 1 := by
        exact Subgroup.mem_bot.mp (hAK ▸ ⟨hkA, hk⟩)
      rw [← hbk, hk1, mul_one]
      exact hb
    · exact fun x hx ↦
        ⟨(show B ≤ B ⊔ K from le_sup_left) hx, hBA hx⟩
  have hsubA : (B ⊔ K).subgroupOf A = B.subgroupOf A := by
    ext x
    constructor
    · intro hx
      exact hInf.le ⟨hx, x.2⟩
    · intro hx
      exact (show B ≤ B ⊔ K from le_sup_left) hx
  have hnorm : A ≤ Subgroup.normalizer (B ⊔ K : Subgroup G) :=
    hAcenter.trans
      (Subgroup.center_le_normalizer (G := G) (B ⊔ K : Subgroup G))
  letI : ((B ⊔ K).subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  letI : ((B ⊔ K).subgroupOf (A ⊔ (B ⊔ K))).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hcard :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient
        A (B ⊔ K) hnorm).toEquiv
  have hsup : A ⊔ (B ⊔ K) = A ⊔ K := by
    rw [← sup_assoc, sup_of_le_left hBA]
  rw [hsup] at hcard
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card,
    Subgroup.index_eq_card]
  simpa only [hsubA] using hcard.symm

/-- A nonidentity element of an infinite cyclic subgroup has infinite
order. -/
lemma not_zpowers_ne
    {a x : G} (ha : ¬ IsOfFinOrder a)
    (hxmem : x ∈ Subgroup.zpowers a) (hxne : x ≠ 1) :
    ¬ IsOfFinOrder x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hk : k ≠ 0 := by
    intro hk
    subst k
    exact hxne (zpow_zero a)
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_zpow_eq_one.mp hfin
  have heq : a ^ (k * n) = a ^ (0 : ℤ) := by
    simpa [zpow_mul] using hpow
  have hkn : k * n = 0 :=
    (injective_zpow_iff_not_isOfFinOrder.mpr ha) heq
  exact hn ((mul_eq_zero.mp hkn).resolve_left hk)

/-- **Hall, Lemma 4.3.** Let `K ≤ H ≤ G`, where `G` is finitely
generated and nilpotent. Suppose `[H:K]` is infinite or divisible by `p`,
while adjoining every nontrivial normal subgroup makes the corresponding
relative index finite and prime to `p`. Then `G` is a finite `p`-group.

Mathlib's `relIndex` is zero exactly when the relative index is infinite,
and subgroup products with normal subgroups are represented by suprema. -/
theorem p_index_conditions {p : ℕ} [Fact p.Prime]
    [Group.FG G] [Group.IsNilpotent G]
    (H K : Subgroup G) (hKH : K ≤ H)
    (hindex : K.relIndex H = 0 ∨ p ∣ K.relIndex H)
    (hnormal : ∀ M : Subgroup G, M.Normal → M ≠ ⊥ →
      (M ⊔ K).relIndex (M ⊔ H) ≠ 0 ∧
        Nat.Coprime p ((M ⊔ K).relIndex (M ⊔ H))) :
    Finite G ∧ IsPGroup p G := by
  have hcentralObstructions :
      ∀ M : Subgroup G, M ≤ Subgroup.center G → M ≠ ⊥ →
        M ⊓ H ≠ ⊥ ∧ ¬ M ≤ K := by
    intro M hMcenter hMne
    exact normal_index_obstructions H K hKH hindex hnormal M
      (normal_center M hMcenter) hMne
  have hcentralInfK :
      ∀ M : Subgroup G, M ≤ Subgroup.center G → M ⊓ K = ⊥ := by
    intro M hMcenter
    by_contra hne
    have hnormalInf : (M ⊓ K).Normal :=
      normal_center (M ⊓ K) (inf_le_left.trans hMcenter)
    exact
      (normal_index_obstructions H K hKH hindex hnormal
        (M ⊓ K) hnormalInf hne).2 inf_le_right
  have hcenterTorsion :
      ∀ a : G, a ∈ Subgroup.center G → IsOfFinOrder a := by
    intro a hacenter
    by_contra hainfinite
    have hane : a ≠ 1 := by
      intro ha
      exact hainfinite (ha ▸ IsOfFinOrder.one)
    let A₀ : Subgroup G := Subgroup.zpowers a
    have hA₀center : A₀ ≤ Subgroup.center G :=
      Subgroup.zpowers_le_of_mem hacenter
    have hA₀ne : A₀ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hane
    have hA₀meet := (hcentralObstructions A₀ hA₀center hA₀ne).1
    obtain ⟨b, hbmeet, hbne⟩ :=
      (Subgroup.bot_or_exists_ne_one (A₀ ⊓ H)).resolve_left hA₀meet
    have hbA₀ : b ∈ A₀ := hbmeet.1
    have hbH : b ∈ H := hbmeet.2
    have hbinfinite : ¬ IsOfFinOrder b :=
      not_zpowers_ne hainfinite hbA₀ hbne
    let A : Subgroup G := Subgroup.zpowers b
    have hAcenter : A ≤ Subgroup.center G :=
      Subgroup.zpowers_le_of_mem (hA₀center hbA₀)
    have hAH : A ≤ H := Subgroup.zpowers_le_of_mem hbH
    have hAne : A ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hbne
    have hAK : A ⊓ K = ⊥ := hcentralInfK A hAcenter
    let A₁ : Subgroup G := Subgroup.zpowers (b ^ p)
    have hA₁A : A₁ ≤ A :=
      Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers b p)
    have hA₁center : A₁ ≤ Subgroup.center G :=
      hA₁A.trans hAcenter
    have hbpne : b ^ p ≠ 1 := by
      intro hbp
      have heq : b ^ p = b ^ 0 := by simpa using hbp
      have hp0 := (injective_pow_iff_not_isOfFinOrder.mpr hbinfinite) heq
      exact (Fact.out : p.Prime).ne_zero hp0
    have hA₁ne : A₁ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hbpne
    have hA₁normal : A₁.Normal := normal_center A₁ hA₁center
    obtain ⟨_hfinite, hcoprime⟩ := hnormal A₁ hA₁normal hA₁ne
    have hA₁H : A₁ ≤ H := hA₁A.trans hAH
    have hcoprimeH :
        Nat.Coprime p ((A₁ ⊔ K).relIndex H) := by
      simpa [sup_eq_right.mpr hA₁H] using hcoprime
    have hfactor :
        (A₁ ⊔ K).relIndex (A ⊔ K) = p := by
      calc
        (A₁ ⊔ K).relIndex (A ⊔ K) = A₁.relIndex A :=
          rel_center_inf
            hA₁A hAcenter hAK
        _ = p :=
          rel_zpowers_order b p hbinfinite
    have htower :=
      Subgroup.relIndex_mul_relIndex (A₁ ⊔ K) (A ⊔ K) H
        (sup_le (hA₁A.trans le_sup_left) le_sup_right)
        (sup_le hAH hKH)
    rw [hfactor] at htower
    have hpdiv : p ∣ (A₁ ⊔ K).relIndex H :=
      ⟨(A ⊔ K).relIndex H, htower.symm⟩
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprimeH) hpdiv
  have hcenterP : IsPGroup p (Subgroup.center G) := by
    rw [IsPGroup.iff_orderOf]
    intro z
    let a : G := z
    have hafinite : IsOfFinOrder a := hcenterTorsion a z.2
    have haorder : orderOf a ≠ 0 := orderOf_ne_zero_iff.mpr hafinite
    have hunique : ∀ {q : ℕ}, q.Prime → q ∣ orderOf a → q = p := by
      intro q hq hqdiv
      let b : G := a ^ (orderOf a / q)
      have hborder : orderOf b = q :=
        orderOf_pow_orderOf_div haorder hqdiv
      let M : Subgroup G := Subgroup.zpowers b
      have hbcenter : b ∈ Subgroup.center G := by
        exact (Subgroup.center G).pow_mem z.2 _
      have hMcenter : M ≤ Subgroup.center G :=
        Subgroup.zpowers_le_of_mem hbcenter
      have hbne : b ≠ 1 := by
        intro hb
        have hq1 : q = 1 := by
          rw [← hborder, hb, orderOf_one]
        exact hq.ne_one hq1
      have hMne : M ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hbne
      have hMmeet := (hcentralObstructions M hMcenter hMne).1
      let J : Subgroup M := (M ⊓ H).subgroupOf M
      obtain ⟨x, hxmeet, hxne⟩ :=
        (Subgroup.bot_or_exists_ne_one (M ⊓ H)).resolve_left hMmeet
      let xM : M := ⟨x, hxmeet.1⟩
      have hxMJ : xM ∈ J := hxmeet
      have hxMne : xM ≠ 1 := by
        intro hx
        exact hxne (congrArg Subtype.val hx)
      have hJne : J ≠ ⊥ := by
        intro hJ
        exact hxMne (Subgroup.mem_bot.mp (hJ ▸ hxMJ))
      have hMcard : Nat.card M = q := by
        dsimp [M]
        rw [Nat.card_zpowers, hborder]
      letI : Fact (Nat.card M).Prime := ⟨hMcard ▸ hq⟩
      have hJtop : J = ⊤ :=
        (J.eq_bot_or_eq_top_of_prime_card).resolve_left hJne
      have hMH : M ≤ H := by
        intro y hy
        let yM : M := ⟨y, hy⟩
        have hyJ : yM ∈ J := by
          rw [hJtop]
          exact Subgroup.mem_top yM
        exact hyJ.2
      have hMK : M ⊓ K = ⊥ := hcentralInfK M hMcenter
      have hMnormal : M.Normal := normal_center M hMcenter
      obtain ⟨hfinite, hcoprime⟩ := hnormal M hMnormal hMne
      have hfiniteH : (M ⊔ K).relIndex H ≠ 0 := by
        simpa [sup_eq_right.mpr hMH] using hfinite
      have hcoprimeH : Nat.Coprime p ((M ⊔ K).relIndex H) := by
        simpa [sup_eq_right.mpr hMH] using hcoprime
      have hfactor : K.relIndex (M ⊔ K) = q := by
        simpa [hMcard] using
          (rel_center_inf
            (G := G) (A := M) (B := ⊥) (K := K) bot_le hMcenter hMK)
      have htower :=
        Subgroup.relIndex_mul_relIndex K (M ⊔ K) H le_sup_right
          (sup_le hMH hKH)
      rw [hfactor] at htower
      have hindexNe : K.relIndex H ≠ 0 := by
        rw [← htower]
        exact mul_ne_zero hq.ne_zero hfiniteH
      have hpindex : p ∣ K.relIndex H :=
        hindex.resolve_left (fun hzero ↦ hindexNe hzero)
      rw [← htower] at hpindex
      have hpq : p ∣ q := hcoprimeH.dvd_of_dvd_mul_right hpindex
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hpq |>.symm
    let k := (orderOf a).primeFactorsList.length
    have hk : orderOf a = p ^ k :=
      Nat.eq_prime_pow_of_unique_prime_dvd haorder hunique
    have hk' : orderOf (z : G) = p ^ k := hk
    exact ⟨k, (Subgroup.orderOf_coe z).symm.trans hk'⟩
  exact p_group_center hcenterP

/-- Evaluate a word on assignments whose `i`th value lies in `H i`. -/
def generalizedValueSet {ι : Type*} (word : FreeGroup ι)
    (H : ι → Subgroup G) : Set G :=
  Set.range fun a : ∀ i, H i ↦ wordEval word fun i ↦ a i

/-- Hall's generalized verbal subgroup `θ(H₁, ..., Hₙ)`. -/
def generalizedVerbalSubgroup {ι : Type*} (word : FreeGroup ι)
    (H : ι → Subgroup G) : Subgroup G :=
  Subgroup.closure (generalizedValueSet word H)

/-- Homomorphisms commute with evaluation of a group word. -/
lemma map_wordEval {ι : Type*} {G' : Type*} [Group G']
    (word : FreeGroup ι) (f : G →* G') (a : ι → G) :
    f (wordEval word a) = wordEval word (fun i ↦ f (a i)) := by
  simpa [wordEval, MonoidHom.comp_apply] using
    (FreeGroup.lift_unique (f := fun i ↦ f (a i))
      (f.comp (FreeGroup.lift a)) (by intro i; simp) (x := word))

/-- The generalized word-value set commutes with homomorphic images. -/
lemma image_generalized_set {ι : Type*} {G' : Type*} [Group G']
    (word : FreeGroup ι) (H : ι → Subgroup G) (f : G →* G') :
    f '' generalizedValueSet word H =
      generalizedValueSet word (fun i ↦ (H i).map f) := by
  classical
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨fun i ↦ ⟨f (a i), Subgroup.mem_map_of_mem f (a i).2⟩, ?_⟩
    exact (map_wordEval word f (fun i ↦ a i)).symm
  · rintro ⟨a, rfl⟩
    choose b hbH hfb using fun i ↦ Subgroup.mem_map.mp (a i).2
    let b' : ∀ i, H i := fun i ↦ ⟨b i, hbH i⟩
    refine ⟨wordEval word (fun i ↦ b' i), ⟨b', rfl⟩, ?_⟩
    calc
      f (wordEval word fun i ↦ b' i) =
          wordEval word (fun i ↦ f (b' i)) :=
        map_wordEval word f (fun i ↦ b' i)
      _ = wordEval word (fun i ↦ (a i : G')) := by
        congr
        funext i
        exact hfb i

/-- Generalized verbal subgroups commute with homomorphic images. -/
lemma generalized_verbal_subgroup {ι : Type*} {G' : Type*} [Group G']
    (word : FreeGroup ι) (H : ι → Subgroup G) (f : G →* G') :
    (generalizedVerbalSubgroup word H).map f =
      generalizedVerbalSubgroup word (fun i ↦ (H i).map f) := by
  rw [generalizedVerbalSubgroup, generalizedVerbalSubgroup,
    MonoidHom.map_closure, image_generalized_set]

/-- Generalized verbal subgroups are monotone in every argument. -/
lemma generalized_verbal_mono {ι : Type*} (word : FreeGroup ι)
    {H K : ι → Subgroup G} (hHK : ∀ i, H i ≤ K i) :
    generalizedVerbalSubgroup word H ≤ generalizedVerbalSubgroup word K := by
  rw [generalizedVerbalSubgroup, generalizedVerbalSubgroup]
  apply Subgroup.closure_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨fun i ↦ ⟨a i, hHK i (a i).2⟩, rfl⟩

/-- Passing two nested subgroups through a homomorphism can only decrease
their relative index. -/
lemma rel_index_dvd {G' : Type*} [Group G'] (f : G →* G')
    {K H : Subgroup G} (hKH : K ≤ H) :
    (K.map f).relIndex (H.map f) ∣ K.relIndex H := by
  let φ : H →* G' := f.comp H.subtype
  let ψ : H →* φ.range := φ.rangeRestrict
  let KH : Subgroup H := K.subgroupOf H
  have hKmap : (KH.map ψ).map φ.range.subtype = K.map f := by
    change ((K.subgroupOf H).map φ.rangeRestrict).map φ.range.subtype = K.map f
    rw [Subgroup.map_map]
    change (K.subgroupOf H).map (f.comp H.subtype) = K.map f
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKH]
  have hHmap : (⊤ : Subgroup H).map φ = H.map f := by
    change (⊤ : Subgroup H).map (f.comp H.subtype) = H.map f
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, H.range_subtype]
  have htopmap : (⊤ : Subgroup φ.range).map φ.range.subtype = H.map f := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa [MonoidHom.range_eq_map] using hHmap
  have hindex :
      (KH.map ψ).index ∣ KH.index :=
    Subgroup.index_map_dvd (H := KH) (f := ψ) φ.rangeRestrict_surjective
  have hindex' :
      (KH.map ψ).relIndex (⊤ : Subgroup φ.range) ∣
        KH.relIndex (⊤ : Subgroup H) := by
    simpa only [Subgroup.relIndex_top_right] using hindex
  rw [← Subgroup.relIndex_map_map_of_injective
      (KH.map ψ) (⊤ : Subgroup φ.range) φ.range.subtype_injective,
    hKmap, htopmap] at hindex'
  simpa [KH] using hindex'

/-- Under Hall's maximal condition, every nonempty property of subgroups
has a maximal example. -/
lemma maximal_subgroup_max
    (hmax : SatisfiesMaximalCondition G)
    (P : Subgroup G → Prop) {H : Subgroup G} (hH : P H) :
    ∃ M : Subgroup G, H ≤ M ∧ Maximal P M := by
  classical
  refine zorn_le_nonempty₀ {M : Subgroup G | P M} ?_ H hH
  intro c hcP hc y hy
  let U := subgroupUnionChain c hc ⟨y, hy⟩
  obtain ⟨S, hSgen, hSfinite⟩ := (Subgroup.fg_iff U).mp (hmax U)
  let T := hSfinite.toFinset
  have hgen : ∀ s ∈ T, ∃ M ∈ c, s ∈ M := by
    intro s hs
    exact subgroup_union_chain.mp
      (hSgen ▸ Subgroup.subset_closure (hSfinite.mem_toFinset.mp hs))
  have finite_chain_bound :
      ∀ A : Finset G, (∀ s ∈ A, ∃ M ∈ c, s ∈ M) →
        ∃ M ∈ c, ∀ s ∈ A, s ∈ M := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨y, hy, by simp⟩
    | @insert x A hx ih =>
        intro hA
        obtain ⟨M, hM, hxM⟩ := hA x (by simp)
        obtain ⟨N, hN, hAN⟩ := ih (by
          intro s hs
          exact hA s (by simp [hs]))
        rcases hc.total hM hN with hMN | hNM
        · exact ⟨N, hN, by
            intro s hs
            rcases Finset.mem_insert.mp hs with rfl | hs
            · exact hMN hxM
            · exact hAN s hs⟩
        · exact ⟨M, hM, by
            intro s hs
            rcases Finset.mem_insert.mp hs with rfl | hs
            · exact hxM
            · exact hNM (hAN s hs)⟩
  obtain ⟨M, hM, hTM⟩ := finite_chain_bound T hgen
  refine ⟨M, hcP hM, ?_⟩
  have hUM : U ≤ M := by
    rw [← hSgen, Subgroup.closure_le]
    intro x hxS
    exact hTM x (hSfinite.mem_toFinset.mpr hxS)
  intro N hN
  exact (union_chain hN).trans hUM

/-- A relative index in a finite `p`-group which divides a number prime to
`p` must be one. -/
lemma rel_dvd_not
    {p m : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {K H : Subgroup G} (hdvd : K.relIndex H ∣ m) (hpm : ¬ p ∣ m) :
    K.relIndex H = 1 := by
  obtain ⟨n, hHcard⟩ := IsPGroup.iff_card.mp (hG.to_subgroup H)
  apply Nat.eq_one_of_dvd_coprimes
      ((Fact.out : p.Prime).coprime_pow_of_not_dvd hpm) hdvd
  rw [← hHcard]
  exact Subgroup.relIndex_dvd_card (H := K) (K := H)

/-- Adjoining a subgroup after a surjective homomorphism computes the same
relative index as adjoining its preimage before the homomorphism. -/
lemma rel_sup_comap
    {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Surjective f)
    (N : Subgroup G') (A B : Subgroup G) :
    (N ⊔ A.map f).relIndex (N ⊔ B.map f) =
      (N.comap f ⊔ A).relIndex (N.comap f ⊔ B) := by
  rw [← Subgroup.map_comap_eq_self_of_surjective hf N,
    ← Subgroup.map_sup, ← Subgroup.map_sup, Subgroup.relIndex_map_map]
  have hker : f.ker ≤ N.comap f := by
    intro x hx
    change f x ∈ N
    rw [MonoidHom.mem_ker.mp hx]
    exact N.one_mem
  rw [Subgroup.comap_map_eq]
  have hkerA : f.ker ≤ N.comap f ⊔ A := hker.trans le_sup_left
  have hkerB : f.ker ≤ N.comap f ⊔ B := hker.trans le_sup_left
  rw [sup_of_le_left hkerA, sup_of_le_left hkerB,
    sup_of_le_left hker]

/-- Every nonzero natural number misses some prime divisor. -/
lemma prime_not_dvd (m : ℕ) (hm : m ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ m := by
  obtain ⟨p, hmp, hp⟩ := Nat.exists_infinite_primes (m + 1)
  refine ⟨p, hp, ?_⟩
  intro hpdvd
  have hpm : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpdvd
  omega

/-- **Hall, Theorem 4.4.** Generalized verbal subgroups preserve finite
index, and their relative index has no new prime divisors. -/
theorem generalized_verbal_index {ι : Type*} [Fintype ι]
    [Group.FG G] [Group.IsNilpotent G]
    (word : FreeGroup ι) (H K : ι → Subgroup G)
    (hKH : ∀ i, K i ≤ H i)
    (hfinite : ∀ i, (K i).relIndex (H i) ≠ 0) :
    (generalizedVerbalSubgroup word K).relIndex
          (generalizedVerbalSubgroup word H) ≠ 0 ∧
      ∃ k : ℕ,
        (generalizedVerbalSubgroup word K).relIndex
            (generalizedVerbalSubgroup word H) ∣
          (∏ i, (K i).relIndex (H i)) ^ k := by
  classical
  let A := generalizedVerbalSubgroup word K
  let B := generalizedVerbalSubgroup word H
  let m := ∏ i, (K i).relIndex (H i)
  have hAB : A ≤ B := generalized_verbal_mono word hKH
  have hm : m ≠ 0 := by
    dsimp [m]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hfinite i
  have hgood :
      A.relIndex B ≠ 0 ∧ (A.relIndex B).primeFactors ⊆ m.primeFactors := by
    by_contra hnot
    let Bad : Subgroup G → Prop := fun M ↦
      M.Normal ∧
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ m ∧
          ((M ⊔ A).relIndex (M ⊔ B) = 0 ∨
            p ∣ (M ⊔ A).relIndex (M ⊔ B))
    have hbadbot : Bad ⊥ := by
      refine ⟨inferInstance, ?_⟩
      by_cases hzero : A.relIndex B = 0
      · obtain ⟨p, hp, hpm⟩ := prime_not_dvd m hm
        exact ⟨p, hp, hpm, by simp [hzero]⟩
      · have hnsub :
          ¬ (A.relIndex B).primeFactors ⊆ m.primeFactors := by
          intro hsub
          exact hnot ⟨hzero, hsub⟩
        simp only [Finset.not_subset] at hnsub
        obtain ⟨p, hpindex, hpmem⟩ := hnsub
        have hp := Nat.prime_of_mem_primeFactors hpindex
        have hpdiv := Nat.dvd_of_mem_primeFactors hpindex
        have hpnot : ¬ p ∣ m := by
          intro hpdivm
          exact hpmem (hp.mem_primeFactors hpdivm hm)
        exact ⟨p, hp, hpnot, by simpa using Or.inr hpdiv⟩
    have hmax : SatisfiesMaximalCondition G :=
      polycyclic_implies_condition
        (supersoluble_implies_polycyclic
          fg_implies_supersoluble)
    obtain ⟨M, _, hMmax⟩ :=
      maximal_subgroup_max hmax Bad hbadbot
    obtain ⟨hMnormal, p, hp, hpm, hMindex⟩ := hMmax.1
    letI : M.Normal := hMnormal
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    have hqindex :
        (A.map q).relIndex (B.map q) = 0 ∨
          p ∣ (A.map q).relIndex (B.map q) := by
      simpa [q, Subgroup.relIndex_map_map, QuotientGroup.ker_mk',
        sup_comm] using hMindex
    letI : Fact p.Prime := ⟨hp⟩
    have hquotientNormal :
        ∀ N : Subgroup (G ⧸ M), N.Normal → N ≠ ⊥ →
          (N ⊔ A.map q).relIndex (N ⊔ B.map q) ≠ 0 ∧
            Nat.Coprime p ((N ⊔ A.map q).relIndex (N ⊔ B.map q)) := by
      intro N hNnormal hNne
      let L : Subgroup G := N.comap q
      have hLnormal : L.Normal := hNnormal.comap q
      have hML : M ≤ L := by
        intro x hx
        change q x ∈ N
        rw [show q x = 1 by
          exact (QuotientGroup.eq_one_iff x).mpr hx]
        exact N.one_mem
      have hLnotbad : ¬ Bad L := by
        intro hLbad
        have hLM : L ≤ M := hMmax.2 hLbad hML
        have hLeq : L = M := le_antisymm hLM hML
        apply hNne
        calc
          N = L.map q := by
            exact (Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective M) N).symm
          _ = M.map q := congrArg (fun X : Subgroup G ↦ X.map q) hLeq
          _ = ⊥ := by simp [q]
      have hindexEq :
          (N ⊔ A.map q).relIndex (N ⊔ B.map q) =
            (L ⊔ A).relIndex (L ⊔ B) :=
        rel_sup_comap
          q (QuotientGroup.mk'_surjective M) N A B
      constructor
      · intro hzero
        apply hLnotbad
        refine ⟨hLnormal, p, hp, hpm, Or.inl ?_⟩
        exact hindexEq ▸ hzero
      · exact hp.coprime_iff_not_dvd.mpr fun hpdiv ↦ hLnotbad
          ⟨hLnormal, p, hp, hpm, Or.inr (hindexEq ▸ hpdiv)⟩
    obtain ⟨hQfinite, hQp⟩ :=
      p_index_conditions (G := G ⧸ M) (B.map q) (A.map q)
        (Subgroup.map_mono hAB) hqindex hquotientNormal
    letI : Finite (G ⧸ M) := hQfinite
    have himages : ∀ i, (K i).map q = (H i).map q := by
      intro i
      have hindexDvd :
          ((K i).map q).relIndex ((H i).map q) ∣
            (K i).relIndex (H i) :=
        rel_index_dvd q (hKH i)
      have hpnoti : ¬ p ∣ (K i).relIndex (H i) := by
        intro hpdiv
        apply hpm
        exact hpdiv.trans
          (Finset.dvd_prod_of_mem
            (fun j ↦ (K j).relIndex (H j)) (Finset.mem_univ i))
      have hone :
          ((K i).map q).relIndex ((H i).map q) = 1 :=
        rel_dvd_not hQp hindexDvd hpnoti
      exact le_antisymm (Subgroup.map_mono (hKH i))
        (Subgroup.relIndex_eq_one.mp hone)
    have hABmap : A.map q = B.map q := by
      dsimp [A, B]
      rw [generalized_verbal_subgroup, generalized_verbal_subgroup]
      congr 1
      funext i
      exact himages i
    have hone : (A.map q).relIndex (B.map q) = 1 := by
      rw [hABmap]
      exact Subgroup.relIndex_eq_one.mpr le_rfl
    rcases hqindex with hzero | hpdiv
    · exact one_ne_zero (hone.symm.trans hzero)
    · exact hp.ne_one (Nat.dvd_one.mp (hone ▸ hpdiv))
  refine ⟨?_, ?_⟩
  · simpa [A, B] using hgood.1
  · obtain ⟨k, hk⟩ :=
      dvd_factors_subset hgood.1 hm hgood.2
    exact ⟨k, by simpa [A, B, m] using hk⟩

/-- A positive integer whose prime divisors all lie in `ω`. Hall assumes
that `ω` itself consists of primes; the definition works for any set. -/
def IONumber (ω : Set ℕ) (n : ℕ) : Prop :=
  n ≠ 0 ∧ (n.primeFactors : Set ℕ) ⊆ ω

/-- An element of finite order whose order is an `ω`-number. -/
def IsOmegaElement (ω : Set ℕ) (x : G) : Prop :=
  IsOfFinOrder x ∧ IONumber ω (orderOf x)

/-- Every element of the group is an `ω`-element. -/
def IsOmegaGroup (ω : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ x : G, IsOmegaElement ω x

/-- The identity is the only `ω`-element of the group. -/
def OmegaTorsionFree (ω : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ x : G, IsOmegaElement ω x → x = 1

/-- Hall's `ω`-equivalence relation on subgroups. -/
def OmegaEquivalent (ω : Set ℕ) (H K : Subgroup G) : Prop :=
  (∀ x ∈ H, ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ K) ∧
    ∀ x ∈ K, ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ H

/-- A subgroup is `ω`-isolated if taking an `ω`-number power into it
forces the original element into it. -/
def IsOmegaIsolated (ω : Set ℕ) (H : Subgroup G) : Prop :=
  ∀ x : G, ∀ n : ℕ, IONumber ω n → x ^ n ∈ H → x ∈ H

/-- Hall's `ω`-isolator: the intersection of all `ω`-isolated subgroups
containing `H`. -/
def omegaIsolator (ω : Set ℕ) (H : Subgroup G) : Subgroup G :=
  sInf {K : Subgroup G | H ≤ K ∧ IsOmegaIsolated ω K}

/-- Hall's `ω`-radical is the isolator of the trivial subgroup. -/
def omegaRadical (ω : Set ℕ) (G : Type*) [Group G] : Subgroup G :=
  omegaIsolator ω (⊥ : Subgroup G)

lemma omega_number_one (ω : Set ℕ) : IONumber ω 1 := by
  simp [IONumber]

lemma IONumber.ne_zero {ω : Set ℕ} {n : ℕ}
    (hn : IONumber ω n) : n ≠ 0 :=
  hn.1

lemma IONumber.primeFactors_subset {ω : Set ℕ} {n : ℕ}
    (hn : IONumber ω n) : (n.primeFactors : Set ℕ) ⊆ ω :=
  hn.2

lemma IONumber.mul {ω : Set ℕ} {m n : ℕ}
    (hm : IONumber ω m) (hn : IONumber ω n) :
    IONumber ω (m * n) := by
  refine ⟨mul_ne_zero hm.ne_zero hn.ne_zero, ?_⟩
  rw [Nat.primeFactors_mul hm.ne_zero hn.ne_zero]
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hm.primeFactors_subset hp
  · exact hn.primeFactors_subset hp

lemma IONumber.pow {ω : Set ℕ} {m : ℕ}
    (hm : IONumber ω m) (k : ℕ) :
    IONumber ω (m ^ k) := by
  refine ⟨pow_ne_zero k hm.ne_zero, ?_⟩
  by_cases hk : k = 0
  · subst k
    simp
  · rw [Nat.primeFactors_pow m hk]
    exact hm.primeFactors_subset

lemma IONumber.finset_prod {ω : Set ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, IONumber ω (f i)) :
    IONumber ω (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using omega_number_one ω
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hf i (by simp)).mul (ih fun j hj ↦ hf j (by simp [hj]))

lemma IONumber.of_dvd {ω : Set ℕ} {m n : ℕ}
    (hn : IONumber ω n) (hmn : m ∣ n) :
    IONumber ω m := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hn.ne_zero (zero_dvd_iff.mp hmn)
  refine ⟨hm, ?_⟩
  intro p hp
  exact hn.primeFactors_subset
    ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hp).trans hmn) hn.ne_zero)

lemma IONumber.coprime_compl {ω : Set ℕ} {m n : ℕ}
    (hm : IONumber ω m) (hn : IONumber ωᶜ n) :
    Nat.Coprime m n := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpn
  have hpω : p ∈ ω :=
    hm.primeFactors_subset (hp.mem_primeFactors hpm hm.ne_zero)
  have hpωc : p ∈ ωᶜ :=
    hn.primeFactors_subset (hp.mem_primeFactors hpn hn.ne_zero)
  exact hpωc hpω

/-- If two coprime positive powers of an element lie in a subgroup, then
the element itself lies in the subgroup. -/
lemma Subgroup.mem_coprime_powmem
    (H : Subgroup G) {x : G} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hxm : x ^ m ∈ H) (hxn : x ^ n ∈ H) :
    x ∈ H := by
  have hma : x ^ ((m : ℤ) * m.gcdA n) ∈ H := by
    rw [zpow_mul, zpow_natCast]
    exact H.zpow_mem hxm (m.gcdA n)
  have hnb : x ^ ((n : ℤ) * m.gcdB n) ∈ H := by
    rw [zpow_mul, zpow_natCast]
    exact H.zpow_mem hxn (m.gcdB n)
  have hbezout :
      (1 : ℤ) = (m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n := by
    simpa [hmn] using Nat.gcd_eq_gcd_ab m n
  rw [← zpow_one x, hbezout, zpow_add]
  exact H.mul_mem hma hnb

lemma le_omegaIsolator (ω : Set ℕ) (H : Subgroup G) :
    H ≤ omegaIsolator ω H := by
  rw [omegaIsolator, le_sInf_iff]
  exact fun K hK ↦ hK.1

lemma isolator_isolated (ω : Set ℕ) (H : Subgroup G) :
    IsOmegaIsolated ω (omegaIsolator ω H) := by
  intro x n hn hx
  rw [omegaIsolator, Subgroup.mem_sInf] at hx ⊢
  intro K hK
  exact hK.2 x n hn (hx K hK)

/-- Raising an element to the index of a subnormal subgroup lands in that
subgroup. -/
lemma Subgroup.IsSubnormal.pow_index_mem {H : Subgroup G}
    (hH : H.IsSubnormal) (g : G) :
    g ^ H.index ∈ H := by
  induction hH with
  | top =>
      simp
  | step H K hHK hKsub hHnormal ih =>
      letI : (H.subgroupOf K).Normal := hHnormal
      have hgK : g ^ K.index ∈ K := ih
      have hpow :
          (⟨g ^ K.index, hgK⟩ : K) ^ (H.subgroupOf K).index ∈
            H.subgroupOf K :=
        (H.subgroupOf K).pow_index_mem ⟨g ^ K.index, hgK⟩
      rw [← Subgroup.relIndex_mul_index hHK, mul_comm, pow_mul]
      exact hpow

/-- In a nilpotent subgroup, raising an element to the relative index of
a nested subgroup lands in the smaller subgroup. -/
lemma rel_index_nilpotent
    {K H : Subgroup G} {x : G} (hx : x ∈ H)
    [Group.IsNilpotent H] :
    x ^ K.relIndex H ∈ K := by
  have hsubnormal : (K.subgroupOf H).IsSubnormal :=
    subnormal_nilpotent (K.subgroupOf H)
  have hpow :=
    Towers.Edmonton.Subgroup.IsSubnormal.pow_index_mem hsubnormal
      (⟨x, hx⟩ : H)
  exact hpow

/-- The two-variable word `x₀x₁`. -/
def twoVariableProduct : FreeGroup Bool :=
  FreeGroup.of false * FreeGroup.of true

@[simp]
lemma word_variable_product (a : Bool → G) :
    wordEval twoVariableProduct a = a false * a true := by
  simp [twoVariableProduct, wordEval]

/-- The generalized verbal subgroup for `x₀x₁` is the join of its two
input subgroups. -/
lemma generalized_verbal_word
    (H : Bool → Subgroup G) :
    generalizedVerbalSubgroup twoVariableProduct H =
      H false ⊔ H true := by
  apply le_antisymm
  · rw [generalizedVerbalSubgroup, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    change wordEval twoVariableProduct (fun i ↦ (a i : G)) ∈
      H false ⊔ H true
    rw [word_variable_product]
    exact (H false ⊔ H true).mul_mem
      (Subgroup.mem_sup_left (a false).2)
      (Subgroup.mem_sup_right (a true).2)
  · apply sup_le
    · intro x hx
      rw [generalizedVerbalSubgroup]
      apply Subgroup.subset_closure
      let a : ∀ b : Bool, H b := fun b ↦
        match b with
        | false => ⟨x, hx⟩
        | true => ⟨1, (H true).one_mem⟩
      exact ⟨a, by simp [a]⟩
    · intro x hx
      rw [generalizedVerbalSubgroup]
      apply Subgroup.subset_closure
      let a : ∀ b : Bool, H b := fun b ↦
        match b with
        | false => ⟨1, (H false).one_mem⟩
        | true => ⟨x, hx⟩
      exact ⟨a, by simp [a]⟩

/-- In a cyclic subgroup, the subgroup generated by an `n`th power has
relative index dividing `n`. -/
lemma rel_zpowers_dvd (a : G) (n : ℕ) :
    (Subgroup.zpowers (a ^ n)).relIndex (Subgroup.zpowers a) ∣ n := by
  let P : Subgroup (Multiplicative ℤ) :=
    AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ))
  let f : Multiplicative ℤ →* G := zpowersHom G a
  have hP :
      P = Subgroup.zpowers (Multiplicative.ofAdd (n : ℤ)) := by
    ext z
    dsimp [P]
    rw [Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Multiplicative.ext (by simp [hk, mul_comm])⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp [mul_comm]⟩
  have hPmap : P.map f = Subgroup.zpowers (a ^ n) := by
    rw [hP, MonoidHom.map_zpowers]
    simp [f]
  have htopmap : (⊤ : Subgroup (Multiplicative ℤ)).map f =
      Subgroup.zpowers a := by
    rw [← MonoidHom.range_eq_map]
    rfl
  have hdiv :=
    rel_index_dvd f (show P ≤ (⊤ : Subgroup (Multiplicative ℤ)) from le_top)
  rw [hPmap, htopmap] at hdiv
  simpa [Subgroup.relIndex_top_right, P, Int.index_zmultiples] using hdiv

lemma rel_zpowers_ne (a : G) {n : ℕ} (hn : n ≠ 0) :
    (Subgroup.zpowers (a ^ n)).relIndex (Subgroup.zpowers a) ≠ 0 := by
  intro hzero
  have hdiv := rel_zpowers_dvd a n
  rw [hzero, zero_dvd_iff] at hdiv
  exact hn hdiv

/-- Two-generator consequence of Theorem 4.4. -/
theorem two_generator_index
    [Group.FG G] [Group.IsNilpotent G]
    (x y : G) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (Subgroup.zpowers (x ^ m) ⊔ Subgroup.zpowers (y ^ n)).relIndex
          (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≠ 0 ∧
      ∃ k : ℕ,
        (Subgroup.zpowers (x ^ m) ⊔ Subgroup.zpowers (y ^ n)).relIndex
            (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∣
          (m * n) ^ k := by
  let H : Bool → Subgroup G := fun b ↦
    match b with
    | false => Subgroup.zpowers x
    | true => Subgroup.zpowers y
  let K : Bool → Subgroup G := fun b ↦
    match b with
    | false => Subgroup.zpowers (x ^ m)
    | true => Subgroup.zpowers (y ^ n)
  have hKH : ∀ b, K b ≤ H b := by
    intro b
    cases b <;>
      simp only [H, K] <;>
      exact Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers _ _)
  have hfinite : ∀ b, (K b).relIndex (H b) ≠ 0 := by
    intro b
    cases b <;> simp only [H, K]
    · exact rel_zpowers_ne x hm
    · exact rel_zpowers_ne y hn
  obtain ⟨hindex, k, hk⟩ :=
    generalized_verbal_index twoVariableProduct H K hKH hfinite
  have hinputDvd :
      (∏ b, (K b).relIndex (H b)) ∣ m * n := by
    simpa [H, K, mul_comm] using
      Nat.mul_dvd_mul (rel_zpowers_dvd x m)
        (rel_zpowers_dvd y n)
  refine ⟨?_, ⟨k, ?_⟩⟩
  · simpa [generalized_verbal_word, H, K] using hindex
  · have := hk.trans (pow_dvd_pow_of_dvd hinputDvd k)
    simpa [generalized_verbal_word, H, K] using this

/-- The multiplication step in Hall's Theorem 4.5(b). -/
lemma omega_number_mul
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G)
    {x y : G} {m n : ℕ}
    (hm : IONumber ω m) (hn : IONumber ω n)
    (hx : x ^ m ∈ H) (hy : y ^ n ∈ H) :
    ∃ r : ℕ, IONumber ω r ∧ (x * y) ^ r ∈ H := by
  let P : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hPfg : P.FG := by
    apply Subgroup.FG.sup
    · exact (Subgroup.fg_iff (Subgroup.zpowers x)).mpr
        ⟨{x}, Subgroup.zpowers_eq_closure x |>.symm, Set.finite_singleton x⟩
    · exact (Subgroup.fg_iff (Subgroup.zpowers y)).mpr
        ⟨{y}, Subgroup.zpowers_eq_closure y |>.symm, Set.finite_singleton y⟩
  letI : Group.FG P := (Group.fg_iff_subgroup_fg P).mpr hPfg
  letI : Group.IsNilpotent P := hG P hPfg
  let xP : P := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩
  let yP : P := ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
  let Q : Subgroup P :=
    Subgroup.zpowers (xP ^ m) ⊔ Subgroup.zpowers (yP ^ n)
  have hPtop :
      Subgroup.zpowers xP ⊔ Subgroup.zpowers yP = (⊤ : Subgroup P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, P.range_subtype]
    rfl
  have hQmap :
      Q.map P.subtype =
        Subgroup.zpowers (x ^ m) ⊔ Subgroup.zpowers (y ^ n) := by
    simp [Q, Subgroup.map_sup, MonoidHom.map_zpowers, xP, yP]
  have hQH : Q.map P.subtype ≤ H := by
    rw [hQmap]
    exact sup_le (Subgroup.zpowers_le_of_mem hx)
      (Subgroup.zpowers_le_of_mem hy)
  obtain ⟨hindex, k, hk⟩ :=
    two_generator_index xP yP hm.ne_zero hn.ne_zero
  have hQindex : Q.index ∣ (m * n) ^ k := by
    simpa [Q, hPtop, Subgroup.relIndex_top_right] using hk
  have hQomega : IONumber ω Q.index :=
    (hm.mul hn).pow k |>.of_dvd hQindex
  have hQsubnormal : Q.IsSubnormal :=
    subnormal_nilpotent Q
  have hpowQ : (xP * yP) ^ Q.index ∈ Q :=
    Towers.Edmonton.Subgroup.IsSubnormal.pow_index_mem
      hQsubnormal (xP * yP)
  refine ⟨Q.index, hQomega, ?_⟩
  have hpowMap : P.subtype ((xP * yP) ^ Q.index) ∈ Q.map P.subtype :=
    Subgroup.mem_map_of_mem P.subtype hpowQ
  exact hQH (by simpa [xP, yP] using hpowMap)

/-- In a locally nilpotent group, the elements having an `ω`-number power
in `H` form a subgroup. -/
def omegaRootSubgroup (hG : Group.IsLocallyNilpotent G)
    (ω : Set ℕ) (H : Subgroup G) : Subgroup G where
  carrier := {x : G | ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ H}
  one_mem' := ⟨1, omega_number_one ω, by simp⟩
  mul_mem' := by
    rintro x y ⟨m, hm, hxm⟩ ⟨n, hn, hyn⟩
    exact omega_number_mul hG ω H hm hn hxm hyn
  inv_mem' := by
    rintro x ⟨n, hn, hxn⟩
    exact ⟨n, hn, by simpa using H.inv_mem hxn⟩

@[simp]
lemma omega_root_subgroup
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) (x : G) :
    x ∈ omegaRootSubgroup hG ω H ↔
      ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ H :=
  Iff.rfl

lemma omega_subgroup
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) :
    H ≤ omegaRootSubgroup hG ω H := by
  intro x hx
  exact ⟨1, omega_number_one ω, by simpa using hx⟩

lemma omega_root_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) :
    IsOmegaIsolated ω (omegaRootSubgroup hG ω H) := by
  intro x n hn hx
  obtain ⟨m, hm, hpow⟩ := hx
  exact ⟨n * m, hn.mul hm, by simpa [pow_mul] using hpow⟩

/-- **Hall, Theorem 4.5(b).** The root subgroup is the isolator. -/
theorem omega_root_isolator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) :
    omegaRootSubgroup hG ω H = omegaIsolator ω H := by
  apply le_antisymm
  · rw [omegaIsolator, le_sInf_iff]
    intro K hK x hx
    obtain ⟨n, hn, hpow⟩ := hx
    exact hK.2 x n hn (hK.1 hpow)
  · rw [omegaIsolator]
    exact sInf_le ⟨omega_subgroup hG ω H,
      omega_root_isolated hG ω H⟩

/-- **Hall, Theorem 4.5(a).** A subgroup is `ω`-equivalent to its
isolator. -/
theorem omegaEquivalent_isolator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) :
    OmegaEquivalent ω H (omegaIsolator ω H) := by
  constructor
  · intro x hx
    exact ⟨1, omega_number_one ω, by
      simpa using le_omegaIsolator ω H hx⟩
  · intro x hx
    rw [← omega_root_isolator hG ω H] at hx
    exact hx

lemma omegaIsolator_mono
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    {H K : Subgroup G} (hHK : H ≤ K) :
    omegaIsolator ω H ≤ omegaIsolator ω K := by
  rw [← omega_root_isolator hG ω H, ← omega_root_isolator hG ω K]
  rintro x ⟨n, hn, hx⟩
  exact ⟨n, hn, hHK hx⟩

lemma omega_equivalent_isolator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (H K : Subgroup G) :
    OmegaEquivalent ω H K ↔
      H ≤ omegaIsolator ω K ∧ K ≤ omegaIsolator ω H := by
  constructor
  · intro h
    constructor
    · intro x hx
      rw [← omega_root_isolator hG ω K]
      exact h.1 x hx
    · intro x hx
      rw [← omega_root_isolator hG ω H]
      exact h.2 x hx
  · rintro ⟨hHK, hKH⟩
    constructor
    · intro x hx
      exact (omegaEquivalent_isolator hG ω K).2 x (hHK hx)
    · intro x hx
      exact (omegaEquivalent_isolator hG ω H).2 x (hKH hx)

/-- **Hall, Theorem 4.5(c).** Generating subgroups from pairwise
`ω`-equivalent families preserves `ω`-equivalence. -/
theorem i_omega_equivalent
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    {Λ : Type*} (H K : Λ → Subgroup G)
    (hHK : ∀ i, OmegaEquivalent ω (H i) (K i)) :
    OmegaEquivalent ω (⨆ i, H i) (⨆ i, K i) := by
  rw [omega_equivalent_isolator hG ω]
  constructor
  · apply iSup_le
    intro i
    exact (omega_equivalent_isolator hG ω (H i) (K i)).mp
      (hHK i) |>.1 |>.trans
        (omegaIsolator_mono hG ω (le_iSup K i))
  · apply iSup_le
    intro i
    exact (omega_equivalent_isolator hG ω (H i) (K i)).mp
      (hHK i) |>.2 |>.trans
        (omegaIsolator_mono hG ω (le_iSup H i))

lemma omega_radical_element
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (x : G) :
    x ∈ omegaRadical ω G ↔ IsOmegaElement ω x := by
  rw [omegaRadical, ← omega_root_isolator hG ω (⊥ : Subgroup G)]
  constructor
  · rintro ⟨n, hn, hpow⟩
    have hpow1 : x ^ n = 1 := Subgroup.mem_bot.mp hpow
    have horddvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hpow1
    have hordne : orderOf x ≠ 0 := by
      intro hz
      exact hn.ne_zero (zero_dvd_iff.mp (hz ▸ horddvd))
    exact ⟨orderOf_ne_zero_iff.mp hordne, hn.of_dvd horddvd⟩
  · rintro ⟨hfin, hordω⟩
    exact ⟨orderOf x, hordω, Subgroup.mem_bot.mpr (pow_orderOf_eq_one x)⟩

lemma omegaRadical_characteristic
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) :
    (omegaRadical ω G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [omega_radical_element hG ω] at hy ⊢
  exact ⟨φ.injective.isOfFinOrder_iff.mpr hy.1, by
    rw [orderOf_injective φ.toMonoidHom φ.injective y]
    exact hy.2⟩

/-- **Hall, Theorem 4.5(d).** The `ω`-elements form a characteristic
subgroup, and the quotient by this subgroup is `ω`-torsion-free. -/
theorem omega_radical_characteristic
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) :
    letI : (omegaRadical ω G).Characteristic :=
      omegaRadical_characteristic hG ω
    (omegaRadical ω G).Characteristic ∧
      OmegaTorsionFree ω (G ⧸ omegaRadical ω G) := by
  letI : (omegaRadical ω G).Characteristic :=
    omegaRadical_characteristic hG ω
  refine ⟨inferInstance, ?_⟩
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (omegaRadical ω G) q
  apply (QuotientGroup.eq_one_iff x).mpr
  have hpow :
      x ^ orderOf (QuotientGroup.mk' (omegaRadical ω G) x) ∈
        omegaRadical ω G := by
    apply (QuotientGroup.eq_one_iff (x ^
      orderOf (QuotientGroup.mk' (omegaRadical ω G) x))).mp
    change (QuotientGroup.mk' (omegaRadical ω G) x) ^
      orderOf (QuotientGroup.mk' (omegaRadical ω G) x) = 1
    exact pow_orderOf_eq_one _
  exact isolator_isolated ω (⊥ : Subgroup G) x
    (orderOf (QuotientGroup.mk' (omegaRadical ω G) x)) hq.2 hpow

lemma omega_rel_powers
    [Group.FG G] [Group.IsNilpotent G]
    (ω : Set ℕ) (H : Subgroup G) (S : Finset G)
    (hS : ∀ x ∈ S, ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ H) :
    IONumber ω (H.relIndex (Subgroup.closure (S : Set G))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using omega_number_one ω
  | @insert x S hx ih =>
      obtain ⟨n, hn, hxn⟩ := hS x (by simp)
      have hrest :
          ∀ y ∈ S, ∃ n : ℕ, IONumber ω n ∧ y ^ n ∈ H := by
        intro y hy
        exact hS y (by simp [hy])
      have hAomega := ih hrest
      let A : Subgroup G := Subgroup.closure (S : Set G)
      let B : Subgroup G := H ⊓ A
      let P : Bool → Subgroup G := fun b ↦
        match b with
        | false => A
        | true => Subgroup.zpowers x
      let Q : Bool → Subgroup G := fun b ↦
        match b with
        | false => B
        | true => Subgroup.zpowers (x ^ n)
      have hQP : ∀ b, Q b ≤ P b := by
        intro b
        cases b
        · exact inf_le_right
        · exact Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers x n)
      have hfinite : ∀ b, (Q b).relIndex (P b) ≠ 0 := by
        intro b
        cases b
        · simpa [P, Q, B, A, Subgroup.inf_relIndex_right] using
            hAomega.ne_zero
        · simpa [P, Q] using rel_zpowers_ne x hn.ne_zero
      obtain ⟨_, k, hdiv⟩ :=
        generalized_verbal_index twoVariableProduct P Q hQP hfinite
      have hcyclicOmega :
          IONumber ω
            ((Subgroup.zpowers (x ^ n)).relIndex (Subgroup.zpowers x)) :=
        hn.of_dvd (rel_zpowers_dvd x n)
      have hproductOmega :
          IONumber ω (∏ b, (Q b).relIndex (P b)) := by
        simpa [P, Q, B, A, Subgroup.inf_relIndex_right, mul_comm] using
          hAomega.mul hcyclicOmega
      have hsmallOmega :
          IONumber ω
            ((B ⊔ Subgroup.zpowers (x ^ n)).relIndex
              (A ⊔ Subgroup.zpowers x)) := by
        apply (hproductOmega.pow k).of_dvd
        simpa [generalized_verbal_word, P, Q] using
          hdiv
      have hsmallLe :
          B ⊔ Subgroup.zpowers (x ^ n) ≤ H :=
        sup_le inf_le_left (Subgroup.zpowers_le_of_mem hxn)
      have htargetDvd :
          H.relIndex (A ⊔ Subgroup.zpowers x) ∣
            (B ⊔ Subgroup.zpowers (x ^ n)).relIndex
              (A ⊔ Subgroup.zpowers x) :=
        Subgroup.relIndex_dvd_of_le_left
          (L := A ⊔ Subgroup.zpowers x) hsmallLe
      have htargetOmega :
          IONumber ω (H.relIndex (A ⊔ Subgroup.zpowers x)) :=
        hsmallOmega.of_dvd htargetDvd
      have hclosure :
          Subgroup.closure ((↑(insert x S) : Set G)) =
            A ⊔ Subgroup.zpowers x := by
        change Subgroup.closure ((↑(insert x S) : Set G)) =
          Subgroup.closure (S : Set G) ⊔ Subgroup.zpowers x
        rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union,
          ← Subgroup.zpowers_eq_closure, sup_comm]
      rw [hclosure]
      exact htargetOmega

/-- **Hall, Theorem 4.5(e).** In a finitely generated locally nilpotent
group, an isolator has `ω`-number index over the original subgroup. -/
theorem isolator_rel_omega
    [Group.FG G] (hG : Group.IsLocallyNilpotent G)
    (ω : Set ℕ) (H : Subgroup G) :
    IONumber ω (H.relIndex (omegaIsolator ω H)) := by
  classical
  have htopNil : Group.IsNilpotent (⊤ : Subgroup G) :=
    hG (⊤ : Subgroup G) Group.FG.out
  letI : Group.IsNilpotent (⊤ : Subgroup G) := htopNil
  letI : Group.IsNilpotent G :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  have hIfg : (omegaIsolator ω H).FG :=
    fg_nilpotent Group.FG.out le_top
  obtain ⟨S, hSgen, hSfinite⟩ :=
    (Subgroup.fg_iff (omegaIsolator ω H)).mp hIfg
  let T : Finset G := hSfinite.toFinset
  have hpow :
      ∀ x ∈ T, ∃ n : ℕ, IONumber ω n ∧ x ^ n ∈ H := by
    intro x hx
    have hxI : x ∈ omegaIsolator ω H := by
      rw [← hSgen]
      exact Subgroup.subset_closure (hSfinite.mem_toFinset.mp hx)
    rw [← omega_root_isolator hG ω H] at hxI
    exact hxI
  have hindex :=
    omega_rel_powers ω H T hpow
  simpa [T, hSfinite.coe_toFinset, hSgen] using hindex

/-- A word value whose inputs have `ω`-number powers in the corresponding
target subgroups has an `ω`-number power in the target generalized verbal
subgroup. -/
lemma omega_number_eval
    {ι : Type*} [Finite ι]
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (word : FreeGroup ι) (K : ι → Subgroup G) (a : ι → G)
    (ha : ∀ i, ∃ n : ℕ, IONumber ω n ∧ a i ^ n ∈ K i) :
    ∃ r : ℕ, IONumber ω r ∧
      (wordEval word a) ^ r ∈ generalizedVerbalSubgroup word K := by
  classical
  letI := Fintype.ofFinite ι
  choose n hn hpowK using ha
  let P : Subgroup G := ⨆ i, Subgroup.zpowers (a i)
  have hPfg : P.FG := by
    apply Subgroup.FG.iSup
    intro i
    exact (Subgroup.fg_iff (Subgroup.zpowers (a i))).mpr
      ⟨{a i}, (Subgroup.zpowers_eq_closure (a i)).symm,
        Set.finite_singleton (a i)⟩
  letI : Group.FG P := (Group.fg_iff_subgroup_fg P).mpr hPfg
  letI : Group.IsNilpotent P := hG P hPfg
  let aP : ι → P := fun i ↦
    ⟨a i, (le_iSup (fun j ↦ Subgroup.zpowers (a j)) i)
      (Subgroup.mem_zpowers (a i))⟩
  let A : ι → Subgroup P := fun i ↦ Subgroup.zpowers (aP i)
  let B : ι → Subgroup P := fun i ↦ Subgroup.zpowers (aP i ^ n i)
  have hBA : ∀ i, B i ≤ A i := by
    intro i
    exact Subgroup.zpowers_le_of_mem
      (Subgroup.npow_mem_zpowers (aP i) (n i))
  have hfinite : ∀ i, (B i).relIndex (A i) ≠ 0 := by
    intro i
    simpa [A, B] using rel_zpowers_ne (aP i) (hn i).ne_zero
  obtain ⟨_, k, hdiv⟩ := generalized_verbal_index word A B hBA hfinite
  have hinputOmega :
      ∀ i, IONumber ω ((B i).relIndex (A i)) := by
    intro i
    apply (hn i).of_dvd
    simpa [A, B] using rel_zpowers_dvd (aP i) (n i)
  have hproductOmega :
      IONumber ω (∏ i, (B i).relIndex (A i)) := by
    simpa using IONumber.finset_prod Finset.univ
      (fun i ↦ (B i).relIndex (A i)) (fun i _ ↦ hinputOmega i)
  have hindexOmega :
      IONumber ω
        ((generalizedVerbalSubgroup word B).relIndex
          (generalizedVerbalSubgroup word A)) :=
    (hproductOmega.pow k).of_dvd hdiv
  have hwordA :
      wordEval word (fun i ↦ aP i) ∈ generalizedVerbalSubgroup word A := by
    rw [generalizedVerbalSubgroup]
    exact Subgroup.subset_closure
      ⟨fun i ↦ ⟨aP i, Subgroup.mem_zpowers (aP i)⟩, rfl⟩
  have hpowB :
      (wordEval word (fun i ↦ aP i)) ^
          (generalizedVerbalSubgroup word B).relIndex
            (generalizedVerbalSubgroup word A) ∈
        generalizedVerbalSubgroup word B :=
    rel_index_nilpotent hwordA
  have hmapB :
      (generalizedVerbalSubgroup word B).map P.subtype =
        generalizedVerbalSubgroup word
          (fun i ↦ Subgroup.zpowers (a i ^ n i)) := by
    rw [generalized_verbal_subgroup]
    congr 1
    funext i
    simp [B, aP, MonoidHom.map_zpowers]
  have hcyclicLe :
      ∀ i, Subgroup.zpowers (a i ^ n i) ≤ K i := by
    intro i
    exact Subgroup.zpowers_le_of_mem (hpowK i)
  have hmapTarget :
      (generalizedVerbalSubgroup word B).map P.subtype ≤
        generalizedVerbalSubgroup word K := by
    rw [hmapB]
    exact generalized_verbal_mono word hcyclicLe
  have hmapped :
      P.subtype
          ((wordEval word (fun i ↦ aP i)) ^
            (generalizedVerbalSubgroup word B).relIndex
              (generalizedVerbalSubgroup word A)) ∈
        generalizedVerbalSubgroup word K :=
    hmapTarget (Subgroup.mem_map_of_mem P.subtype hpowB)
  have heval :
      P.subtype (wordEval word (fun i ↦ aP i)) = wordEval word a := by
    calc
      P.subtype (wordEval word (fun i ↦ aP i)) =
          wordEval word (fun i ↦ P.subtype (aP i)) :=
        map_wordEval word P.subtype (fun i ↦ aP i)
      _ = wordEval word a := by rfl
  refine ⟨(generalizedVerbalSubgroup word B).relIndex
      (generalizedVerbalSubgroup word A), hindexOmega, ?_⟩
  rw [map_pow, heval] at hmapped
  exact hmapped

/-- **Hall, Theorem 4.6.** Generalized verbal subgroups preserve
`ω`-equivalence in locally nilpotent groups. -/
theorem generalized_verbal_equivalent
    {ι : Type*} [Finite ι]
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (word : FreeGroup ι) (H K : ι → Subgroup G)
    (hHK : ∀ i, OmegaEquivalent ω (H i) (K i)) :
    OmegaEquivalent ω
      (generalizedVerbalSubgroup word H)
      (generalizedVerbalSubgroup word K) := by
  rw [omega_equivalent_isolator hG ω]
  constructor
  · rw [← omega_root_isolator hG ω (generalizedVerbalSubgroup word K)]
    rw [generalizedVerbalSubgroup, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact omega_number_eval hG ω word K
      (fun i ↦ a i) (fun i ↦ (hHK i).1 (a i) (a i).2)
  · rw [← omega_root_isolator hG ω (generalizedVerbalSubgroup word H)]
    rw [generalizedVerbalSubgroup, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact omega_number_eval hG ω word H
      (fun i ↦ a i) (fun i ↦ (hHK i).2 (a i) (a i).2)

/-- The two-variable commutator word `[x₀,x₁]`. -/
def twoVariableWord : FreeGroup Bool :=
  ⁅FreeGroup.of false, FreeGroup.of true⁆

@[simp]
lemma word_variable_commutator (a : Bool → G) :
    wordEval twoVariableWord a = ⁅a false, a true⁆ := by
  simp [twoVariableWord, wordEval, map_commutatorElement]

/-- The generalized verbal subgroup for `[x₀,x₁]` is the subgroup
commutator of its two inputs. -/
lemma generalized_verbal_variable
    (H : Bool → Subgroup G) :
    generalizedVerbalSubgroup twoVariableWord H =
      ⁅H false, H true⁆ := by
  apply le_antisymm
  · rw [generalizedVerbalSubgroup, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    change wordEval twoVariableWord (fun i ↦ (a i : G)) ∈
      ⁅H false, H true⁆
    rw [word_variable_commutator]
    exact Subgroup.commutator_mem_commutator (a false).2 (a true).2
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [generalizedVerbalSubgroup]
    apply Subgroup.subset_closure
    let a : ∀ b : Bool, H b := fun b ↦
      match b with
      | false => ⟨x, hx⟩
      | true => ⟨y, hy⟩
    exact ⟨a, by simp [a]⟩

lemma omegaEquivalent_refl (ω : Set ℕ) (H : Subgroup G) :
    OmegaEquivalent ω H H := by
  constructor <;> intro x hx <;>
    exact ⟨1, omega_number_one ω, by simpa using hx⟩

lemma omegaEquivalent_commutator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    {H₁ H₂ K₁ K₂ : Subgroup G}
    (h₁ : OmegaEquivalent ω H₁ K₁)
    (h₂ : OmegaEquivalent ω H₂ K₂) :
    OmegaEquivalent ω ⁅H₁, H₂⁆ ⁅K₁, K₂⁆ := by
  let H : Bool → Subgroup G := fun b ↦
    match b with
    | false => H₁
    | true => H₂
  let K : Bool → Subgroup G := fun b ↦
    match b with
    | false => K₁
    | true => K₂
  have hHK : ∀ b, OmegaEquivalent ω (H b) (K b) := by
    intro b
    cases b
    · exact h₁
    · exact h₂
  simpa [H, K, generalized_verbal_variable] using
    generalized_verbal_equivalent hG ω twoVariableWord H K hHK

/-- **Hall, Corollary to Theorem 4.6.** The commutator of two isolators
lies in the isolator of the commutator. -/
theorem commutator_isolators_isolator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (U V : Subgroup G) :
    ⁅omegaIsolator ω U, omegaIsolator ω V⁆ ≤
      omegaIsolator ω ⁅U, V⁆ := by
  let H : Bool → Subgroup G := fun b ↦
    match b with
    | false => omegaIsolator ω U
    | true => omegaIsolator ω V
  let K : Bool → Subgroup G := fun b ↦
    match b with
    | false => U
    | true => V
  have hHK : ∀ b, OmegaEquivalent ω (H b) (K b) := by
    intro b
    cases b
    · exact ⟨(omegaEquivalent_isolator hG ω U).2, (omegaEquivalent_isolator hG ω U).1⟩
    · exact ⟨(omegaEquivalent_isolator hG ω V).2, (omegaEquivalent_isolator hG ω V).1⟩
  have heq :=
    generalized_verbal_equivalent hG ω twoVariableWord H K hHK
  have hle :=
    (omega_equivalent_isolator hG ω
      (generalizedVerbalSubgroup twoVariableWord H)
      (generalizedVerbalSubgroup twoVariableWord K)).mp heq |>.1
  simpa [H, K, generalized_verbal_variable] using hle

/-- The `ω`-isolator of a normal subgroup in a locally nilpotent group is
normal. -/
lemma omegaIsolator_normal
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S : Subgroup G) [S.Normal] :
    (omegaIsolator ω S).Normal := by
  apply Subgroup.commutator_top_left_le_iff.mp
  exact
    (Subgroup.commutator_mono (le_omegaIsolator ω (⊤ : Subgroup G)) le_rfl).trans
      ((commutator_isolators_isolator hG ω (⊤ : Subgroup G) S).trans
        (omegaIsolator_mono hG ω (Subgroup.commutator_le_right (⊤ : Subgroup G) S)))

/-- **Hall, Lemma 4.7(a).** The isolator of a section centralizer
centralizes the corresponding isolated section. -/
theorem isolator_section_centralizer
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S R : Subgroup G) [S.Normal] :
    letI : (omegaIsolator ω S).Normal := omegaIsolator_normal hG ω S
    omegaIsolator ω (centralizerModulo R S) ≤
      centralizerModulo (omegaIsolator ω R) (omegaIsolator ω S) := by
  letI : (omegaIsolator ω S).Normal := omegaIsolator_normal hG ω S
  apply (commutator_centralizer_modulo
    (omegaIsolator ω R)
    (omegaIsolator ω (centralizerModulo R S))
    (omegaIsolator ω S)).mp
  have hRC :
      ⁅R, centralizerModulo R S⁆ ≤ S :=
    (commutator_centralizer_modulo R (centralizerModulo R S) S).mpr
      le_rfl
  exact (commutator_isolators_isolator hG ω R (centralizerModulo R S)).trans
    (omegaIsolator_mono hG ω hRC)

/-- **Hall, Lemma 4.7(b).** If the lower subgroup of a section is already
`ω`-isolated, then its section centralizer is `ω`-isolated. -/
theorem section_centralizer_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S R : Subgroup G) [S.Normal]
    (hS : omegaIsolator ω S = S) :
    omegaIsolator ω (centralizerModulo R S) = centralizerModulo R S := by
  apply le_antisymm
  · apply (commutator_centralizer_modulo
      R (omegaIsolator ω (centralizerModulo R S)) S).mp
    have hRC :
        ⁅R, centralizerModulo R S⁆ ≤ S :=
      (commutator_centralizer_modulo R (centralizerModulo R S) S).mpr
        le_rfl
    calc
      ⁅R, omegaIsolator ω (centralizerModulo R S)⁆ ≤
          ⁅omegaIsolator ω R, omegaIsolator ω (centralizerModulo R S)⁆ :=
        Subgroup.commutator_mono (le_omegaIsolator ω R) le_rfl
      _ ≤ omegaIsolator ω ⁅R, centralizerModulo R S⁆ :=
        commutator_isolators_isolator hG ω R (centralizerModulo R S)
      _ ≤ omegaIsolator ω S :=
        omegaIsolator_mono hG ω hRC
      _ = S := hS
  · exact le_omegaIsolator ω (centralizerModulo R S)

/-- The `ω`- and `ωᶜ`-isolators of a subgroup intersect in the original
subgroup. -/
lemma omega_isolator_compl
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S : Subgroup G) {x : G}
    (hxω : x ∈ omegaIsolator ω S)
    (hxωc : x ∈ omegaIsolator ωᶜ S) :
    x ∈ S := by
  rw [← omega_root_isolator hG ω S] at hxω
  rw [← omega_root_isolator hG ωᶜ S] at hxωc
  obtain ⟨m, hm, hxm⟩ := hxω
  obtain ⟨n, hn, hxn⟩ := hxωc
  exact Towers.Edmonton.Subgroup.mem_coprime_powmem S
    (hm.coprime_compl hn) hxm hxn

/-- **Hall, Lemma 4.7(c).** If `R` lies in the `ω`-isolator of the normal
subgroup `S`, then the centralizer of `R/S` is `ωᶜ`-isolated. -/
theorem section_complement_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S R : Subgroup G) [S.Normal]
    (hSR : S ≤ R) (hR : R ≤ omegaIsolator ω S) :
    IsOmegaIsolated ωᶜ (centralizerModulo R S) := by
  intro x m hm hxmC
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers (x ^ m)
  have hYX : Y ≤ X := by
    exact Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers x m)
  have hYleC : Y ≤ centralizerModulo R S :=
    Subgroup.zpowers_le_of_mem hxmC
  have hRC :
      ⁅R, centralizerModulo R S⁆ ≤ S :=
    (commutator_centralizer_modulo R (centralizerModulo R S) S).mpr
      le_rfl
  have hRY : ⁅R, Y⁆ ≤ S :=
    (Subgroup.commutator_mono le_rfl hYleC).trans hRC
  have hXY : OmegaEquivalent ωᶜ X Y := by
    rw [omega_equivalent_isolator hG ωᶜ]
    constructor
    · rw [← omega_root_isolator hG ωᶜ Y]
      apply Subgroup.zpowers_le_of_mem
      exact ⟨m, hm, Subgroup.mem_zpowers (x ^ m)⟩
    · exact hYX.trans (le_omegaIsolator ωᶜ X)
  have hRXωc : ⁅R, X⁆ ≤ omegaIsolator ωᶜ S := by
    have heq :=
      omegaEquivalent_commutator hG ωᶜ (omegaEquivalent_refl ωᶜ R) hXY
    exact
      ((omega_equivalent_isolator hG ωᶜ ⁅R, X⁆ ⁅R, Y⁆).mp
        heq).1.trans (omegaIsolator_mono hG ωᶜ hRY)
  have hRS : OmegaEquivalent ω R S := by
    rw [omega_equivalent_isolator hG ω]
    exact ⟨hR, hSR.trans (le_omegaIsolator ω R)⟩
  have hRXω : ⁅R, X⁆ ≤ omegaIsolator ω S := by
    have heq :=
      omegaEquivalent_commutator hG ω hRS (omegaEquivalent_refl ω X)
    exact
      ((omega_equivalent_isolator hG ω ⁅R, X⁆ ⁅S, X⁆).mp
        heq).1.trans
        (omegaIsolator_mono hG ω (Subgroup.commutator_le_left S X))
  have hRX : ⁅R, X⁆ ≤ S := by
    intro z hz
    exact omega_isolator_compl hG ω S (hRXω hz) (hRXωc hz)
  have hXleC :
      X ≤ centralizerModulo R S :=
    (commutator_centralizer_modulo R X S).mp hRX
  exact hXleC (Subgroup.mem_zpowers x)

/-- **Hall, Lemma 4.7(d).** Finite-order elements of coprime orders in a
locally nilpotent group commute. -/
theorem commute_coprime_orders
    (hG : Group.IsLocallyNilpotent G) {x y : G}
    (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (hcop : Nat.Coprime (orderOf x) (orderOf y)) :
    Commute x y := by
  let ω : Set ℕ := orderOf x |>.primeFactors
  have hxω : IONumber ω (orderOf x) := by
    exact ⟨orderOf_ne_zero_iff.mpr hx, fun _ hp ↦ hp⟩
  have hyωc : IONumber ωᶜ (orderOf y) := by
    refine ⟨orderOf_ne_zero_iff.mpr hy, ?_⟩
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    change p ∉ ω
    intro hpx
    have hpox : p ∣ orderOf x := Nat.dvd_of_mem_primeFactors hpx
    have hpoy : p ∣ orderOf y := Nat.dvd_of_mem_primeFactors hp
    exact hpprime.not_dvd_one
      (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpox hpoy)
  have hxrad : x ∈ omegaIsolator ω (⊥ : Subgroup G) :=
    (omega_radical_element hG ω x).mpr ⟨hx, hxω⟩
  have hR :
      Subgroup.zpowers x ≤ omegaIsolator ω (⊥ : Subgroup G) :=
    Subgroup.zpowers_le_of_mem hxrad
  have hCisolated :
      IsOmegaIsolated ωᶜ
        (centralizerModulo (Subgroup.zpowers x) (⊥ : Subgroup G)) :=
    section_complement_isolated hG ω (⊥ : Subgroup G) (Subgroup.zpowers x) bot_le hR
  have hypow :
      y ^ orderOf y ∈
        centralizerModulo (Subgroup.zpowers x) (⊥ : Subgroup G) := by
    rw [pow_orderOf_eq_one]
    exact Subgroup.one_mem _
  have hyC :
      y ∈ centralizerModulo (Subgroup.zpowers x) (⊥ : Subgroup G) :=
    hCisolated y (orderOf y) hyωc hypow
  have hcomm :
      ⁅Subgroup.zpowers x, Subgroup.zpowers y⁆ ≤ (⊥ : Subgroup G) :=
    (commutator_centralizer_modulo
      (Subgroup.zpowers x) (Subgroup.zpowers y) (⊥ : Subgroup G)).mpr
      (Subgroup.zpowers_le_of_mem hyC)
  rw [← commutatorElement_eq_one_iff_commute]
  exact Subgroup.mem_bot.mp
    (hcomm (Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers y)))

/-- Conjugation of a normal section `R/S`. -/
def sectionConjHom
    (S R : Subgroup G) [S.Normal] [R.Normal] :
    G →* MulAut (R.map (QuotientGroup.mk' S)) :=
  (MulAut.conjNormal (H := R.map (QuotientGroup.mk' S))).comp
    (QuotientGroup.mk' S)

/-- The kernel of the conjugation action on `R/S` is its section
centralizer. -/
lemma section_conj_ker
    (S R : Subgroup G) [S.Normal] [R.Normal] :
    (sectionConjHom S R).ker = centralizerModulo R S := by
  ext x
  simp [sectionConjHom, centralizerModulo, Subgroup.mem_centralizer_iff,
    DFunLike.ext_iff, Subtype.ext_iff, eq_mul_inv_iff_mul_eq, eq_comm]

/-- The centralizer of a normal section is normal. -/
lemma centralizerModulo_normal
    (S R : Subgroup G) [S.Normal] [R.Normal] :
    (centralizerModulo R S).Normal := by
  unfold centralizerModulo
  infer_instance

/-- The quotient by the centralizer of a finite normal section is finite. -/
lemma finite_centralizer_modulo
    (S R : Subgroup G) [S.Normal] [R.Normal]
    [Finite (R.map (QuotientGroup.mk' S))] :
    letI : (centralizerModulo R S).Normal := centralizerModulo_normal S R
    Finite (G ⧸ centralizerModulo R S) := by
  letI : (centralizerModulo R S).Normal := centralizerModulo_normal S R
  let f := sectionConjHom S R
  haveI : Finite f.range := inferInstance
  haveI : f.ker.FiniteIndex := Subgroup.finiteIndex_ker f
  rw [← section_conj_ker S R]
  infer_instance

/-- A finite quotient by an `ωᶜ`-isolated normal subgroup is an
`ω`-group. -/
lemma omega_compl_isolated
    (ω : Set ℕ) (C : Subgroup G) [C.Normal]
    [Finite (G ⧸ C)] (hC : IsOmegaIsolated ωᶜ C) :
    IsOmegaGroup ω (G ⧸ C) := by
  intro q
  refine ⟨isOfFinOrder_of_finite q, ?_⟩
  refine ⟨orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite q), ?_⟩
  intro p hporder
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hporder
  by_contra hpω
  have hpωc : IONumber ωᶜ p := by
    refine ⟨hp.ne_zero, ?_⟩
    intro r hr
    have hrp : r = p := by
      simpa [hp.primeFactors] using hr
    subst r
    exact hpω
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C q
  let n := orderOf (QuotientGroup.mk' C x) / p
  have hpdiv : p ∣ orderOf (QuotientGroup.mk' C x) :=
    Nat.dvd_of_mem_primeFactors hporder
  have hordpos : 0 < orderOf (QuotientGroup.mk' C x) :=
    (isOfFinOrder_of_finite _).orderOf_pos
  have hnpos : 0 < n :=
    Nat.div_pos (Nat.le_of_dvd hordpos hpdiv) hp.pos
  have hnlt : n < orderOf (QuotientGroup.mk' C x) :=
    Nat.div_lt_self hordpos hp.one_lt
  have hpowC : (x ^ n) ^ p ∈ C := by
    apply (QuotientGroup.eq_one_iff ((x ^ n) ^ p)).mp
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, ← pow_mul,
      Nat.div_mul_cancel hpdiv]
    change (QuotientGroup.mk' C x) ^
      orderOf (QuotientGroup.mk' C x) = 1
    exact pow_orderOf_eq_one _
  have hxnC : x ^ n ∈ C :=
    hC (x ^ n) p hpωc hpowC
  have hqpow :
      (QuotientGroup.mk' C x) ^ n = 1 := by
    exact (QuotientGroup.eq_one_iff (x ^ n)).mpr hxnC
  have hordDvd : orderOf (QuotientGroup.mk' C x) ∣ n :=
    orderOf_dvd_of_pow_eq_one hqpow
  exact (Nat.not_le_of_lt hnlt) (Nat.le_of_dvd hnpos hordDvd)

/-- **Hall, Lemma 4.7(e).** If `R/S` is a finite `ω`-group and `R` is
normal, then the quotient by the centralizer of `R/S` is also a finite
`ω`-group. -/
theorem section_centralizer_omega
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (S R : Subgroup G) [S.Normal] [R.Normal]
    (hSR : S ≤ R)
    [Finite (R.map (QuotientGroup.mk' S))]
    (hsection : IsOmegaGroup ω (R.map (QuotientGroup.mk' S))) :
    letI : (centralizerModulo R S).Normal := centralizerModulo_normal S R
    Finite (G ⧸ centralizerModulo R S) ∧
      IsOmegaGroup ω (G ⧸ centralizerModulo R S) := by
  letI : (centralizerModulo R S).Normal := centralizerModulo_normal S R
  have hR : R ≤ omegaIsolator ω S := by
    intro r hr
    rw [← omega_root_isolator hG ω S]
    let rq : R.map (QuotientGroup.mk' S) :=
      ⟨QuotientGroup.mk' S r, Subgroup.mem_map_of_mem (QuotientGroup.mk' S) hr⟩
    have hrq := hsection rq
    refine ⟨orderOf rq, hrq.2, ?_⟩
    apply (QuotientGroup.eq_one_iff (r ^ orderOf rq)).mp
    rw [QuotientGroup.mk_pow]
    change (QuotientGroup.mk' S r) ^ orderOf rq = 1
    rw [← Subgroup.orderOf_coe rq]
    exact pow_orderOf_eq_one _
  have hCisolated :
      IsOmegaIsolated ωᶜ (centralizerModulo R S) :=
    section_complement_isolated hG ω S R hSR hR
  letI : Finite (G ⧸ centralizerModulo R S) :=
    finite_centralizer_modulo S R
  exact ⟨inferInstance,
    omega_compl_isolated
      ω (centralizerModulo R S) hCisolated⟩

/-- An `ω`-isolated subgroup is equal to its `ω`-isolator. -/
lemma omega_isolator_isolated
    (ω : Set ℕ) (S : Subgroup G) (hS : IsOmegaIsolated ω S) :
    omegaIsolator ω S = S := by
  apply le_antisymm
  · rw [omegaIsolator]
    exact sInf_le ⟨le_rfl, hS⟩
  · exact le_omegaIsolator ω S

/-- In an `ω`-torsion-free locally nilpotent group, the `ω`-radical is
trivial. -/
lemma omega_radical_bot
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (hfree : OmegaTorsionFree ω G) :
    omegaRadical ω G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exact Subgroup.mem_bot.mpr
    (hfree x ((omega_radical_element hG ω x).mp hx))

/-- Centralizing a subgroup modulo the trivial subgroup is ordinary
centralization. -/
lemma centralizerModulo_bot (R : Subgroup G) :
    centralizerModulo R (⊥ : Subgroup G) =
      Subgroup.centralizer (R : Set G) := by
  apply le_antisymm
  · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact le_bot_iff.mp
      ((commutator_centralizer_modulo R
        (centralizerModulo R (⊥ : Subgroup G)) ⊥).mpr le_rfl)
  · apply (commutator_centralizer_modulo R
      (Subgroup.centralizer (R : Set G)) ⊥).mp
    rw [le_bot_iff, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]

/-- Centralizing `G` modulo `Z_n` is membership in `Z_{n+1}`. -/
lemma centralizer_modulo_series (n : ℕ) :
    centralizerModulo (⊤ : Subgroup G) (Subgroup.upperCentralSeries G n) =
      Subgroup.upperCentralSeries G (n + 1) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    have hcomm :
        ⁅(⊤ : Subgroup G), centralizerModulo (⊤ : Subgroup G)
          (Subgroup.upperCentralSeries G n)⁆ ≤ Subgroup.upperCentralSeries G n :=
      (commutator_centralizer_modulo
        (⊤ : Subgroup G)
        (centralizerModulo (⊤ : Subgroup G) (Subgroup.upperCentralSeries G n))
        (Subgroup.upperCentralSeries G n)).mpr le_rfl
    rw [Subgroup.commutator_comm] at hcomm
    exact hcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))
  · apply (commutator_centralizer_modulo
      (⊤ : Subgroup G) (Subgroup.upperCentralSeries G (n + 1))
      (Subgroup.upperCentralSeries G n)).mp
    rw [Subgroup.commutator_comm]
    exact upper_series_commutator n

/-- **Hall, Lemma 4.8(a).** In an `ω`-torsion-free locally nilpotent
group, centralizers of arbitrary subsets are `ω`-isolated. -/
theorem centralizer_omega_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (hfree : OmegaTorsionFree ω G) (X : Set G) :
    IsOmegaIsolated ω (Subgroup.centralizer X) := by
  have hbot :
      omegaIsolator ω (⊥ : Subgroup G) = ⊥ := by
    exact omega_radical_bot hG ω hfree
  have hfix :=
    section_centralizer_isolated hG ω (⊥ : Subgroup G) (Subgroup.closure X) hbot
  rw [centralizerModulo_bot, Subgroup.centralizer_closure] at hfix
  rw [← hfix]
  exact isolator_isolated ω (Subgroup.centralizer X)

/-- **Hall, Lemma 4.8(b).** In an `ω`-torsion-free locally nilpotent
group, every upper-central-series term is `ω`-isolated. -/
theorem upper_omega_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (hfree : OmegaTorsionFree ω G) :
    ∀ n : ℕ, IsOmegaIsolated ω (Subgroup.upperCentralSeries G n) := by
  intro n
  induction n with
  | zero =>
      rw [Subgroup.upperCentralSeries_zero]
      have hbot :
          omegaIsolator ω (⊥ : Subgroup G) = ⊥ :=
        omega_radical_bot hG ω hfree
      rw [← hbot]
      exact isolator_isolated ω (⊥ : Subgroup G)
  | succ n ih =>
      have hfix :=
        section_centralizer_isolated hG ω (Subgroup.upperCentralSeries G n) (⊤ : Subgroup G)
          (omega_isolator_isolated ω (Subgroup.upperCentralSeries G n) ih)
      rw [centralizer_modulo_series] at hfix
      rw [← hfix]
      exact isolator_isolated ω (Subgroup.upperCentralSeries G (n + 1))

/-- Restricting an ambient upper-central-series term to a subgroup always
lies in the corresponding intrinsic term. -/
lemma comap_upper_subtype (H : Subgroup G) :
    ∀ n : ℕ,
      (Subgroup.upperCentralSeries G n).comap H.subtype ≤ Subgroup.upperCentralSeries H n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro x hx
      rw [Subgroup.mem_upperCentralSeries_succ_iff]
      intro y
      apply ih
      change H.subtype ⁅x, y⁆ ∈ Subgroup.upperCentralSeries G n
      rw [map_commutatorElement]
      exact (Subgroup.mem_upperCentralSeries_succ_iff.mp hx) y

/-- **Hall, Lemma 4.8(c), intrinsic form.** If the `ω`-isolator of `H`
is all of `G`, the upper central series induced from `G` on `H` agrees
with the intrinsic upper central series of `H`. -/
theorem upper_series_comap
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (hfree : OmegaTorsionFree ω G) (H : Subgroup G)
    (hH : omegaIsolator ω H = ⊤) :
    ∀ n : ℕ,
      (Subgroup.upperCentralSeries G n).comap H.subtype = Subgroup.upperCentralSeries H n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      apply le_antisymm
      · exact comap_upper_subtype H (n + 1)
      · intro x hx
        change (x : G) ∈ Subgroup.upperCentralSeries G (n + 1)
        rw [Subgroup.mem_upperCentralSeries_succ_iff]
        intro g
        let U : Subgroup G :=
          (Subgroup.upperCentralSeries H (n + 1)).map H.subtype
        have hxU : (x : G) ∈ U :=
          Subgroup.mem_map_of_mem H.subtype hx
        have hgIso : g ∈ omegaIsolator ω H := by
          rw [hH]
          exact Subgroup.mem_top g
        have hcommIso :
            ⁅(x : G), g⁆ ∈ omegaIsolator ω ⁅U, H⁆ :=
          commutator_isolators_isolator hG ω U H
            (Subgroup.commutator_mem_commutator
              (le_omegaIsolator ω U hxU) hgIso)
        have hUH :
            ⁅U, H⁆ ≤ (Subgroup.upperCentralSeries H n).map H.subtype := by
          change
            ⁅(Subgroup.upperCentralSeries H (n + 1)).map H.subtype, H⁆ ≤
              (Subgroup.upperCentralSeries H n).map H.subtype
          have htop : (⊤ : Subgroup H).map H.subtype = H := by
            rw [← MonoidHom.range_eq_map]
            exact H.range_subtype
          calc
            ⁅(Subgroup.upperCentralSeries H (n + 1)).map H.subtype, H⁆ =
                ⁅(Subgroup.upperCentralSeries H (n + 1)).map H.subtype,
                  (⊤ : Subgroup H).map H.subtype⁆ := by rw [htop]
            _ = ⁅Subgroup.upperCentralSeries H (n + 1), (⊤ : Subgroup H)⁆.map
                  H.subtype :=
              (Subgroup.map_commutator
                (Subgroup.upperCentralSeries H (n + 1)) (⊤ : Subgroup H)
                H.subtype).symm
            _ ≤ (Subgroup.upperCentralSeries H n).map H.subtype :=
              Subgroup.map_mono
                (upper_series_commutator (G := H) n)
        have hmap :
            (Subgroup.upperCentralSeries H n).map H.subtype ≤
              Subgroup.upperCentralSeries G n := by
          rw [Subgroup.map_le_iff_le_comap, ih]
        have hcommZGiso :
            ⁅(x : G), g⁆ ∈ omegaIsolator ω (Subgroup.upperCentralSeries G n) :=
          omegaIsolator_mono hG ω (hUH.trans hmap) hcommIso
        rw [omega_isolator_isolated ω
          (Subgroup.upperCentralSeries G n)
          (upper_omega_isolated hG ω hfree n)] at hcommZGiso
        exact hcommZGiso

/-- **Hall, Lemma 4.8(c).** If the `ω`-isolator of `H` is all of `G`,
then the intrinsic upper central series of `H`, embedded in `G`, is the
intersection of the upper central series of `G` with `H`. -/
theorem upper_series_inf
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (hfree : OmegaTorsionFree ω G) (H : Subgroup G)
    (hH : omegaIsolator ω H = ⊤) :
    ∀ n : ℕ,
      (Subgroup.upperCentralSeries H n).map H.subtype =
        Subgroup.upperCentralSeries G n ⊓ H := by
  intro n
  rw [← upper_series_comap hG ω hfree H hH n,
    Subgroup.map_comap_eq, H.range_subtype, inf_comm]

/-- The subgroup generated by the `n`th powers of elements of `H`. -/
def subgroupPower (H : Subgroup G) (n : ℕ) : Subgroup G :=
  Subgroup.closure {x : G | ∃ h ∈ H, h ^ n = x}

/-- Every `n`th power from `H` belongs to `subgroupPower H n`. -/
lemma pow_subgroup_power (H : Subgroup G) (n : ℕ)
    {x : G} (hx : x ∈ H) :
    x ^ n ∈ subgroupPower H n := by
  rw [subgroupPower]
  exact Subgroup.subset_closure ⟨x, hx, rfl⟩

/-- `subgroupPower H n` is the smallest subgroup containing all `n`th
powers from `H`. -/
lemma subgroupPower_le {H K : Subgroup G} {n : ℕ}
    (hpow : ∀ x ∈ H, x ^ n ∈ K) :
    subgroupPower H n ≤ K := by
  rw [subgroupPower, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hpow x hx

/-- The power subgroup of a normal subgroup is normal. -/
instance subgroupPower_normal (H : Subgroup G) [H.Normal] (n : ℕ) :
    (subgroupPower H n).Normal := by
  rw [subgroupPower]
  constructor
  intro x hx g
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      apply Subgroup.subset_closure
      exact ⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h hh g, conj_pow⟩
  | one =>
      simp
  | mul x y _ _ hx hy =>
      rw [← conj_mul]
      exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
      rw [← conj_inv]
      exact Subgroup.inv_mem _ hx

/-- If `G/C` is an `ω`-group, every element of `G` lies in the
`ω`-isolator of `C`. -/
lemma omega_isolator_top
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (C : Subgroup G) [C.Normal]
    (hquot : IsOmegaGroup ω (G ⧸ C)) :
    omegaIsolator ω C = ⊤ := by
  rw [← omega_root_isolator hG ω C]
  apply top_unique
  intro x _
  have hxquot := hquot (QuotientGroup.mk' C x)
  refine ⟨orderOf (QuotientGroup.mk' C x), hxquot.2, ?_⟩
  apply (QuotientGroup.eq_one_iff (x ^ orderOf (QuotientGroup.mk' C x))).mp
  rw [QuotientGroup.mk_pow]
  exact pow_orderOf_eq_one _

/-- Modulo the subgroup generated by `n`th powers, a finitely generated
nilpotent normal subgroup has finite `ω`-group image when `n` is an
`ω`-number. -/
lemma omega_subgroup_power
    [Group.FG G] [Group.IsNilpotent G]
    (ω : Set ℕ) (H : Subgroup G) [H.Normal] (n : ℕ)
    (hn : IONumber ω n) :
    Finite (H.map (QuotientGroup.mk' (subgroupPower H n))) ∧
      IsOmegaGroup ω (H.map (QuotientGroup.mk' (subgroupPower H n))) := by
  let q : G →* G ⧸ subgroupPower H n :=
    QuotientGroup.mk' (subgroupPower H n)
  let P : Subgroup (G ⧸ subgroupPower H n) := H.map q
  have hHfg : H.FG :=
    fg_nilpotent Group.FG.out le_top
  have hPfg : P.FG := by
    obtain ⟨T, hTgen, hTfinite⟩ := (Subgroup.fg_iff H).mp hHfg
    rw [Subgroup.fg_iff]
    refine ⟨q '' T, ?_, hTfinite.image q⟩
    calc
      Subgroup.closure (q '' T) = (Subgroup.closure T).map q :=
        (MonoidHom.map_closure q T).symm
      _ = P := by rw [hTgen]
  letI : Group.FG P := (Group.fg_iff_subgroup_fg P).mpr hPfg
  letI : Group.IsNilpotent P := inferInstance
  have hpow_one : ∀ p : P, p ^ n = 1 := by
    intro p
    obtain ⟨x, hx, hxp⟩ := p.2
    apply Subtype.ext
    change (p : G ⧸ subgroupPower H n) ^ n = 1
    rw [← hxp, ← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ n)).mpr
      (pow_subgroup_power H n hx)
  obtain ⟨_k, T, _hTcard, hTgen⟩ :=
    Group.fg_iff'.mp (inferInstance : Group.FG P)
  have hTorder : ∀ p ∈ T, IsOfFinOrder p := by
    intro p _
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, Nat.pos_of_ne_zero hn.ne_zero, hpow_one p⟩
  have hPfinite : Finite P := (nilpotent_order_generators T hTgen hTorder).1
  letI : Finite P := hPfinite
  change Finite P ∧ IsOmegaGroup ω P
  exact ⟨hPfinite, fun p ↦
    ⟨isOfFinOrder_of_finite p,
      hn.of_dvd (orderOf_dvd_of_pow_eq_one (hpow_one p))⟩⟩

/-- Isolators computed inside a subgroup agree with ambient isolators
intersected with that subgroup. -/
lemma omega_isolator_subgroup
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    (H P : Subgroup G) :
    (omegaIsolator (G := P) ω (H.subgroupOf P)).map P.subtype =
      omegaIsolator ω H ⊓ P := by
  have hP : Group.IsLocallyNilpotent P :=
    (locally_nilpotent_ambient P).mpr
      (fun K hKfg _ ↦ hG K hKfg)
  rw [← omega_root_isolator hP ω (H.subgroupOf P),
    ← omega_root_isolator hG ω H]
  ext x
  constructor
  · rintro ⟨y, ⟨n, hn, hpow⟩, rfl⟩
    exact ⟨⟨n, hn, by simpa using hpow⟩, y.2⟩
  · rintro ⟨⟨n, hn, hpow⟩, hxP⟩
    let y : P := ⟨x, hxP⟩
    refine ⟨y, ⟨n, hn, ?_⟩, rfl⟩
    simpa [y] using hpow

/-- **Hall, Lemma 4.9(a).** The isolator of the normalizer of `H`
normalizes the isolator of `H`. -/
theorem isolator_le_isolator
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G) :
    omegaIsolator ω (Subgroup.normalizer (H : Set G)) ≤
      Subgroup.normalizer (omegaIsolator ω H : Set G) := by
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  have hHN : ⁅H, N⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro h hh n hn
    have hn' : n ∈ Subgroup.normalizer (H : Set G) := by
      simpa [N] using hn
    have hconj :
        n * h⁻¹ * n⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hn' h⁻¹).mp (H.inv_mem hh)
    simpa [commutatorElement_def, mul_assoc] using H.mul_mem hh hconj
  apply normalizer_commutator
  calc
    ⁅omegaIsolator ω H, omegaIsolator ω N⁆ ≤
        omegaIsolator ω ⁅H, N⁆ :=
      commutator_isolators_isolator hG ω H N
    _ ≤ omegaIsolator ω H :=
      omegaIsolator_mono hG ω hHN

/-- **Hall, Lemma 4.9(b), generated-ambient core.** Under Hall's reduction
`G = ⟨overline{N_G(H)}, x⟩`, an element normalizing `overline H` lies in
`overline{N_G(H)}`. -/
theorem normalizer_isolator_ambient
    [Group.FG G] (hG : Group.IsLocallyNilpotent G)
    (ω : Set ℕ) (H : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (omegaIsolator ω H : Set G))
    (hgen :
      omegaIsolator ω (Subgroup.normalizer (H : Set G)) ⊔
          Subgroup.zpowers x =
        ⊤) :
    x ∈ omegaIsolator ω (Subgroup.normalizer (H : Set G)) := by
  have htopNil : Group.IsNilpotent (⊤ : Subgroup G) :=
    hG (⊤ : Subgroup G) Group.FG.out
  letI : Group.IsNilpotent G :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  let I : Subgroup G := omegaIsolator ω H
  have hnormIeq : Subgroup.normalizer (I : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le
      (by simpa [I] using isolator_le_isolator hG ω H)
      (by simpa [I] using Subgroup.zpowers_le_of_mem hx)
  letI : I.Normal := Subgroup.normalizer_eq_top_iff.mp hnormIeq
  let n : ℕ := H.relIndex I
  have hn : IONumber ω n := by
    simpa [n, I] using isolator_rel_omega hG ω H
  let S : Subgroup G := subgroupPower I n
  have hSH : S ≤ H := by
    dsimp [S]
    apply subgroupPower_le
    intro y hy
    dsimp [n]
    exact rel_index_nilpotent (K := H) (H := I) hy
  have hSI : S ≤ I :=
    hSH.trans (by simpa [I] using le_omegaIsolator ω H)
  have hsectionData :=
    omega_subgroup_power (G := G) ω I n hn
  have hsectionFinite :
      Finite (I.map (QuotientGroup.mk' S)) := by
    simpa [S] using hsectionData.1
  letI : Finite (I.map (QuotientGroup.mk' S)) := hsectionFinite
  have hsectionOmega :
      IsOmegaGroup ω (I.map (QuotientGroup.mk' S)) := by
    simpa [S] using hsectionData.2
  let C : Subgroup G := centralizerModulo I S
  letI : C.Normal := by
    dsimp [C]
    exact centralizerModulo_normal S I
  have hquot :
      Finite (G ⧸ C) ∧ IsOmegaGroup ω (G ⧸ C) := by
    simpa [C] using section_centralizer_omega hG ω S I hSI hsectionOmega
  have hCiso : omegaIsolator ω C = ⊤ :=
    omega_isolator_top hG ω C hquot.2
  have hIC : ⁅I, C⁆ ≤ S := by
    dsimp [C]
    exact (commutator_centralizer_modulo I
      (centralizerModulo I S) S).mpr le_rfl
  have hHC : ⁅H, C⁆ ≤ H :=
    (Subgroup.commutator_mono
      (by simpa [I] using le_omegaIsolator ω H) le_rfl).trans
        (hIC.trans hSH)
  have hCN :
      C ≤ Subgroup.normalizer (H : Set G) :=
    normalizer_commutator hHC
  have hIsoLe :
      omegaIsolator ω C ≤
        omegaIsolator ω (Subgroup.normalizer (H : Set G)) :=
    omegaIsolator_mono hG ω hCN
  rw [hCiso] at hIsoLe
  exact hIsoLe (Subgroup.mem_top x)

/-- **Hall, Lemma 4.9(b).** In a finitely generated locally nilpotent
group, the isolator of the normalizer of `H` is exactly the normalizer of
the isolator of `H`. -/
theorem isolator_normalizer
    [Group.FG G] (hG : Group.IsLocallyNilpotent G)
    (ω : Set ℕ) (H : Subgroup G) :
    omegaIsolator ω (Subgroup.normalizer (H : Set G)) =
      Subgroup.normalizer (omegaIsolator ω H : Set G) := by
  apply le_antisymm (isolator_le_isolator hG ω H)
  intro x hx
  have htopNil : Group.IsNilpotent (⊤ : Subgroup G) :=
    hG (⊤ : Subgroup G) Group.FG.out
  letI : Group.IsNilpotent G :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  let I : Subgroup G := omegaIsolator ω H
  let NI : Subgroup G := omegaIsolator ω N
  let P : Subgroup G := NI ⊔ Subgroup.zpowers x
  have hHN : H ≤ N := by
    simpa [N] using (Subgroup.le_normalizer : H ≤ Subgroup.normalizer H)
  have hNNI : N ≤ NI := by
    simpa [NI] using le_omegaIsolator ω N
  have hINI : I ≤ NI := by
    exact omegaIsolator_mono hG ω hHN
  have hNIP : NI ≤ P := by
    exact le_sup_left
  have hIP : I ≤ P := hINI.trans hNIP
  have hNP : N ≤ P := hNNI.trans hNIP
  have hHP : H ≤ P := hHN.trans hNP
  have hPfg : P.FG :=
    fg_nilpotent Group.FG.out le_top
  letI : Group.FG P := (Group.fg_iff_subgroup_fg P).mpr hPfg
  have hPnil : Group.IsNilpotent P := inferInstance
  have hPloc : Group.IsLocallyNilpotent P :=
    locally_nilpotent hPnil
  let HP : Subgroup P := H.subgroupOf P
  let NP : Subgroup P := Subgroup.normalizer (HP : Set P)
  let xP : P :=
    ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x)⟩
  have hIMap :
      (omegaIsolator (G := P) ω HP).map P.subtype = I := by
    calc
      (omegaIsolator (G := P) ω HP).map P.subtype =
          omegaIsolator ω H ⊓ P := by
        simpa [HP] using omega_isolator_subgroup hG ω H P
      _ = I := by simpa [I] using inf_of_le_left hIP
  have hNP_eq : NP = N.subgroupOf P := by
    simpa [NP, HP, N] using
      (Subgroup.subgroupOf_normalizer_eq hHP).symm
  have hNIMap :
      (omegaIsolator (G := P) ω NP).map P.subtype = NI := by
    calc
      (omegaIsolator (G := P) ω NP).map P.subtype =
          (omegaIsolator (G := P) ω (N.subgroupOf P)).map P.subtype := by
            rw [hNP_eq]
      _ = omegaIsolator ω N ⊓ P :=
        omega_isolator_subgroup hG ω N P
      _ = NI := by simpa [NI] using inf_of_le_left hNIP
  have hmemI :
      ∀ y : P, y ∈ omegaIsolator (G := P) ω HP ↔ (y : G) ∈ I := by
    intro y
    rw [← Subgroup.mem_map_iff_mem P.subtype_injective, hIMap]
    rfl
  have hxPnorm :
      xP ∈ Subgroup.normalizer (omegaIsolator (G := P) ω HP : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmemI y, hmemI (xP * y * xP⁻¹)]
    simpa [xP, I] using
      (Subgroup.mem_normalizer_iff.mp hx (y : G))
  have hgenP :
      omegaIsolator (G := P) ω NP ⊔ Subgroup.zpowers xP = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    calc
      (omegaIsolator (G := P) ω NP ⊔ Subgroup.zpowers xP).map P.subtype =
          NI ⊔ Subgroup.zpowers x := by
        rw [Subgroup.map_sup, hNIMap, MonoidHom.map_zpowers]
        rfl
      _ = P := rfl
      _ = (⊤ : Subgroup P).map P.subtype := by
        rw [← MonoidHom.range_eq_map, P.range_subtype]
  have hxlocal :
      xP ∈ omegaIsolator (G := P) ω NP := by
    simpa [NP] using
      normalizer_isolator_ambient (G := P) hPloc ω HP xP hxPnorm hgenP
  have hxmapped :
      P.subtype xP ∈ NI := by
    rw [← hNIMap]
    exact Subgroup.mem_map_of_mem P.subtype hxlocal
  simpa [xP, NI, N] using hxmapped

/-- **Hall, Lemma 4.10(a), finite-stage form.** If `H` is equal to its
`ω`-isolator, then every natural-number stage of its normalizer tower is
equal to its `ω`-isolator. -/
theorem normalizer_omega_isolated
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ) (H : Subgroup G)
    (hH : omegaIsolator ω H = H) :
    ∀ n : ℕ,
      omegaIsolator ω (normalizerTower H n) = normalizerTower H n := by
  intro n
  induction n with
  | zero =>
      simpa [normalizerTower_zero] using hH
  | succ n ih =>
      rw [normalizerTower_succ]
      apply le_antisymm
      · simpa [ih] using isolator_le_isolator hG ω (normalizerTower H n)
      · exact le_omegaIsolator ω
          (Subgroup.normalizer (normalizerTower H n : Set G))

/-- **Hall, Lemma 4.10(b), finite-subnormal form.** The `ω`-isolator of
a subnormal subgroup of a locally nilpotent group is subnormal. -/
theorem isolator_subnormal
    (hG : Group.IsLocallyNilpotent G) (ω : Set ℕ)
    {H : Subgroup G} (hH : H.IsSubnormal) :
    (omegaIsolator ω H).IsSubnormal := by
  induction hH with
  | top =>
      have htop :
          omegaIsolator ω (⊤ : Subgroup G) = ⊤ :=
        le_antisymm le_top (le_omegaIsolator ω (⊤ : Subgroup G))
      rw [htop]
      exact Subgroup.IsSubnormal.top
  | step H K hHK hKsub hHnormal ih =>
      have hIsoHK :
          omegaIsolator ω H ≤ omegaIsolator ω K :=
        omegaIsolator_mono hG ω hHK
      refine Subgroup.IsSubnormal.step
        (omegaIsolator ω H) (omegaIsolator ω K) hIsoHK ih ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIsoHK]
      letI : (H.subgroupOf K).Normal := hHnormal
      exact (omegaIsolator_mono hG ω
        (Subgroup.le_normalizer_of_normal_subgroupOf hHK)).trans
          (isolator_le_isolator hG ω H)

end Edmonton
end Towers
