import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Generic descending subgroup filtrations

This is a small interface for filtration-shaped arguments.  It deliberately does not
choose a Zassenhaus formula yet; later files can instantiate it with dimension
subgroups, lower central series, or finite quotient filtrations.
-/

namespace Submission

open scoped commutatorElement

/-- The canonical map from a quotient of a product by a product subgroup to the product
of quotients. -/
noncomputable def quotientProdMap {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] :
    (G × H) ⧸ A.prod B →* (G ⧸ A) × (H ⧸ B) :=
  QuotientGroup.lift (A.prod B)
    (((QuotientGroup.mk' A).comp (MonoidHom.fst G H)).prod
      ((QuotientGroup.mk' B).comp (MonoidHom.snd G H))) (by
        intro x hx
        rw [Subgroup.mem_prod] at hx
        ext <;> simp [hx.1, hx.2])

/-- The product-quotient map is bijective. -/
theorem quotient_prod_bijective {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] :
    Function.Bijective (quotientProdMap A B) := by
  constructor
  · intro x y h
    refine QuotientGroup.induction_on x ?_ h
    intro gx
    refine QuotientGroup.induction_on y ?_
    intro gy hxy
    apply QuotientGroup.eq.mpr
    change (gx⁻¹ * gy) ∈ A.prod B
    rw [Subgroup.mem_prod]
    constructor
    · have h1 := congrArg Prod.fst hxy
      change QuotientGroup.mk' A gx.1 = QuotientGroup.mk' A gy.1 at h1
      exact QuotientGroup.eq.mp h1
    · have h2 := congrArg Prod.snd hxy
      change QuotientGroup.mk' B gx.2 = QuotientGroup.mk' B gy.2 at h2
      exact QuotientGroup.eq.mp h2
  · intro y
    rcases y with ⟨qg, qh⟩
    refine QuotientGroup.induction_on qg ?_
    intro g
    refine QuotientGroup.induction_on qh ?_
    intro h
    refine ⟨QuotientGroup.mk' (A.prod B) (g, h), ?_⟩
    rfl

/-- The canonical equivalence `(G × H)/(A × B) ≃ (G/A) × (H/B)`. -/
noncomputable def quotientProdEquiv {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] :
    (G × H) ⧸ A.prod B ≃* (G ⧸ A) × (H ⧸ B) :=
  MulEquiv.ofBijective (quotientProdMap A B) (quotient_prod_bijective A B)

@[simp] theorem quotient_prod_equiv {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal]
    (x : (G × H) ⧸ A.prod B) :
    quotientProdEquiv A B x = quotientProdMap A B x := rfl


@[simp] theorem quotient_prod_mk {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] (g : G) (h : H) :
    quotientProdEquiv A B (QuotientGroup.mk' (A.prod B) (g, h)) =
      (QuotientGroup.mk' A g, QuotientGroup.mk' B h) := rfl

@[simp] theorem prod_symm_mk {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] (g : G) (h : H) :
    (quotientProdEquiv A B).symm (QuotientGroup.mk' A g, QuotientGroup.mk' B h) =
      QuotientGroup.mk' (A.prod B) (g, h) := by
  apply (quotientProdEquiv A B).injective
  simp only [MulEquiv.apply_symm_apply]
  change (QuotientGroup.mk' A g, QuotientGroup.mk' B h) = _
  rfl


/-- The map on product quotients induced by a pair of subgroup-respecting homomorphisms. -/
noncomputable def quotientProdFunctor {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H']
    (A : Subgroup G) (B : Subgroup H) (A' : Subgroup G') (B' : Subgroup H')
    [A.Normal] [B.Normal] [A'.Normal] [B'.Normal]
    (f : G →* G') (g : H →* H')
    (hf : A ≤ A'.comap f) (hg : B ≤ B'.comap g) :
    (G × H) ⧸ A.prod B →* (G' × H') ⧸ A'.prod B' :=
  QuotientGroup.map (A.prod B) (A'.prod B') (MonoidHom.prodMap f g) (by
    intro x hx
    rw [Subgroup.mem_prod] at hx
    change (f x.1, g x.2) ∈ A'.prod B'
    rw [Subgroup.mem_prod]
    exact ⟨hf hx.1, hg hx.2⟩)

@[simp] theorem prod_functor_mk {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H']
    (A : Subgroup G) (B : Subgroup H) (A' : Subgroup G') (B' : Subgroup H')
    [A.Normal] [B.Normal] [A'.Normal] [B'.Normal]
    (f : G →* G') (g : H →* H')
    (hf : A ≤ A'.comap f) (hg : B ≤ B'.comap g) (x : G) (y : H) :
    quotientProdFunctor A B A' B' f g hf hg
        (QuotientGroup.mk' (A.prod B) (x, y)) =
      QuotientGroup.mk' (A'.prod B') (f x, g y) := rfl

/-- Naturality of the canonical product-quotient equivalence. -/
theorem quotient_prod_naturality {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H']
    (A : Subgroup G) (B : Subgroup H) (A' : Subgroup G') (B' : Subgroup H')
    [A.Normal] [B.Normal] [A'.Normal] [B'.Normal]
    (f : G →* G') (g : H →* H')
    (hf : A ≤ A'.comap f) (hg : B ≤ B'.comap g) :
    (quotientProdEquiv A' B').toMonoidHom.comp
        (quotientProdFunctor A B A' B' f g hf hg) =
      (MonoidHom.prodMap (QuotientGroup.map A A' f hf)
        (QuotientGroup.map B B' g hg)).comp (quotientProdEquiv A B).toMonoidHom := by
  ext x <;> rfl

/-- A descending filtration of a group by normal subgroups, indexed by natural numbers.
We keep an explicit `one_eq_top` convention because Zassenhaus filtrations are usually
indexed from `1`. -/
structure DFilt (G : Type*) [Group G] where
  term : ℕ → Subgroup G
  antitone' : Antitone term
  normal' : ∀ n, (term n).Normal
  one_eq_top' : term 1 = ⊤

namespace DFilt

variable {G H : Type*} [Group G] [Group H]

instance : CoeFun (DFilt G) (fun _ => ℕ → Subgroup G) := ⟨fun F => F.term⟩

@[simp] theorem one_eq_top (F : DFilt G) : F 1 = ⊤ := F.one_eq_top'

theorem antitone (F : DFilt G) : Antitone F.term := F.antitone'

theorem mono_membership (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    F n ≤ F m := F.antitone' h

/-- Elementwise form of monotonicity for filtration terms. -/
theorem mem_of_le (F : DFilt G) {m n : ℕ} (h : m ≤ n) {g : G}
    (hg : g ∈ F n) : g ∈ F m :=
  F.mono_membership h hg

/-- Every element lies in the zeroth term. -/
theorem mem_zero (F : DFilt G) (g : G) : g ∈ F 0 := by
  have hle : F 1 ≤ F 0 := F.mono_membership (Nat.zero_le 1)
  apply hle
  rw [one_eq_top]
  trivial

/-- Every element lies in the first term. -/
theorem mem_one (F : DFilt G) (g : G) : g ∈ F 1 := by
  rw [one_eq_top]
  trivial

/-- The identity lies in every filtration term. -/
theorem one_mem (F : DFilt G) (n : ℕ) : (1 : G) ∈ F n :=
  (F n).one_mem

/-- Products of two elements in the same term remain in that term. -/
theorem mul_mem (F : DFilt G) {n : ℕ} {g h : G}
    (hg : g ∈ F n) (hh : h ∈ F n) : g * h ∈ F n :=
  (F n).mul_mem hg hh

/-- If the right factor lies in a later term, a product lies in the left factor's term. -/
theorem mem_le_right (F : DFilt G) {m n : ℕ} {g h : G}
    (hmn : m ≤ n) (hg : g ∈ F m) (hh : h ∈ F n) : g * h ∈ F m :=
  F.mul_mem hg (F.mem_of_le hmn hh)

/-- If the left factor lies in a later term, a product lies in the right factor's term. -/
theorem mem_le_left (F : DFilt G) {m n : ℕ} {g h : G}
    (hmn : m ≤ n) (hg : g ∈ F n) (hh : h ∈ F m) : g * h ∈ F m :=
  F.mul_mem (F.mem_of_le hmn hg) hh

/-- Products of elements in possibly different terms lie in the term at the smaller index. -/
theorem mul_mem_min (F : DFilt G) {m n : ℕ} {g h : G}
    (hg : g ∈ F m) (hh : h ∈ F n) : g * h ∈ F (min m n) :=
  F.mul_mem (F.mem_of_le (Nat.min_le_left _ _) hg)
    (F.mem_of_le (Nat.min_le_right _ _) hh)

/-- Inverses preserve membership in a filtration term. -/
theorem inv_mem (F : DFilt G) {n : ℕ} {g : G} (hg : g ∈ F n) :
    g⁻¹ ∈ F n :=
  (F n).inv_mem hg

/-- Integer powers preserve membership in a filtration term. -/
theorem zpow_mem (F : DFilt G) {n : ℕ} {g : G}
    (hg : g ∈ F n) (k : ℤ) : g ^ k ∈ F n :=
  Subgroup.zpow_mem (F n) hg k

/-- Products of a list of elements in a common filtration term remain in that term. -/
theorem list_prod_mem (F : DFilt G) {n : ℕ} (L : List G)
    (h : ∀ g ∈ L, g ∈ F n) : L.prod ∈ F n := by
  induction L with
  | nil => exact F.one_mem n
  | cons x xs ih =>
      exact F.mul_mem (h x (by simp))
        (ih (by intro g hg; exact h g (by simp [hg])))

/-- Conjugation preserves membership in a filtration term. -/
theorem conj_mem (F : DFilt G) {n : ℕ} {g x : G} (hg : g ∈ F n) :
    x * g * x⁻¹ ∈ F n :=
  (F.normal' n).conj_mem g hg x

/-- Division preserves membership in a common filtration term. -/
theorem div_mem (F : DFilt G) {n : ℕ} {g h : G}
    (hg : g ∈ F n) (hh : h ∈ F n) : g / h ∈ F n := by
  simpa [div_eq_mul_inv] using F.mul_mem hg (F.inv_mem hh)

/-- If the denominator lies in a later term, division lies in the numerator's term. -/
theorem div_mem_of (F : DFilt G) {m n : ℕ} {g h : G}
    (hmn : m ≤ n) (hg : g ∈ F m) (hh : h ∈ F n) : g / h ∈ F m := by
  simpa [div_eq_mul_inv] using F.mem_le_right hmn hg (F.inv_mem hh)

/-- If the numerator lies in a later term, division lies in the denominator's term. -/
theorem div_of_le (F : DFilt G) {m n : ℕ} {g h : G}
    (hmn : m ≤ n) (hg : g ∈ F n) (hh : h ∈ F m) : g / h ∈ F m := by
  simpa [div_eq_mul_inv] using F.mem_le_left hmn hg (F.inv_mem hh)

/-- Division of elements in possibly different terms lies in the smaller-index term. -/
theorem div_mem_min (F : DFilt G) {m n : ℕ} {g h : G}
    (hg : g ∈ F m) (hh : h ∈ F n) : g / h ∈ F (min m n) := by
  simpa [div_eq_mul_inv] using F.mul_mem_min hg (F.inv_mem hh)

/-- The inverse-conjugation convention also preserves term membership. -/
theorem conj_inv_mem (F : DFilt G) {n : ℕ} {g x : G} (hg : g ∈ F n) :
    x⁻¹ * g * x ∈ F n := by
  simpa using F.conj_mem (x := x⁻¹) hg

instance term_normal (F : DFilt G) (n : ℕ) : (F n).Normal := F.normal' n

/-- The zeroth term is top, as a consequence of the normalized first term. -/
@[simp] theorem zero_eq_top (F : DFilt G) : F 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.mono_membership (Nat.zero_le 1)

/-- Any term of index at most one is top. -/
theorem eq_top_of (F : DFilt G) {n : ℕ} (hn : n ≤ 1) :
    F n = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.mono_membership hn

/-- Intersections of two terms in any descending filtration are the term at the larger index. -/
theorem term_inf_max (F : DFilt G) (m n : ℕ) :
    F m ⊓ F n = F (max m n) := by
  apply le_antisymm
  · intro g hg
    have hp : g ∈ F m ∧ g ∈ F n := by
      simpa using hg
    rcases le_total m n with hmn | hnm
    · simpa [max_eq_right hmn] using hp.2
    · simpa [max_eq_left hnm] using hp.1
  · intro g hg
    constructor
    · exact F.antitone (Nat.le_max_left m n) hg
    · exact F.antitone (Nat.le_max_right m n) hg

/-- If `m ≤ n`, intersecting the two terms gives the later term. -/
theorem term_inf_right (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    F m ⊓ F n = F n := by
  rw [term_inf_max]
  simp [max_eq_right h]

/-- If `m ≤ n`, the symmetric intersection orientation gives the later term. -/
theorem term_inf_left (F : DFilt G) {m n : ℕ} (h : n ≤ m) :
    F m ⊓ F n = F m := by
  rw [term_inf_max]
  simp [max_eq_left h]

/-- Joins of two terms in any descending filtration are the term at the smaller index. -/
theorem term_sup_min (F : DFilt G) (m n : ℕ) :
    F m ⊔ F n = F (min m n) := by
  rcases le_total m n with hmn | hnm
  · have hle : F n ≤ F m := F.antitone hmn
    simpa [min_eq_left hmn] using (sup_eq_left.mpr hle)
  · have hle : F m ≤ F n := F.antitone hnm
    simpa [min_eq_right hnm] using (sup_eq_right.mpr hle)


/-- If `m ≤ n`, joining the two terms gives the earlier term. -/
theorem term_sup_left (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    F m ⊔ F n = F m := by
  rw [term_sup_min]
  simp [min_eq_left h]

/-- If `m ≤ n`, the symmetric join orientation gives the earlier term. -/
theorem term_sup_right (F : DFilt G) {m n : ℕ} (h : n ≤ m) :
    F m ⊔ F n = F n := by
  rw [term_sup_min]
  simp [min_eq_right h]

/-- A homomorphism is filtration-preserving if it sends each term into the corresponding term. -/
def Preserves (F : DFilt G) (E : DFilt H) (φ : G →* H) : Prop :=
  ∀ n, (F n).map φ ≤ E n

/-- A homomorphism is strictly/surjectively compatible with filtrations if each term maps onto the
corresponding term. This is useful for quotient functoriality statements later. -/
def MapsOnto (F : DFilt G) (E : DFilt H) (φ : G →* H) : Prop :=
  ∀ n, (F n).map φ = E n

/-- A termwise onto map is, in particular, filtration-preserving. -/
theorem MapsOnto.preserves {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (h : MapsOnto F E φ) : Preserves F E φ := by
  intro n
  rw [h n]

/-- Since filtrations have top term at index `1`, a termwise-onto filtration map is
surjective on the underlying groups. -/
theorem MapsOnto.surjective {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (h : MapsOnto F E φ) : Function.Surjective φ := by
  intro y
  have hy : y ∈ E 1 := by
    rw [one_eq_top]
    trivial
  rw [← h 1] at hy
  rcases hy with ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩


/-- For an injective termwise-onto filtration map, the preimage of each target term
is exactly the corresponding source term. -/
theorem MapsOnto.comap_eq_inj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (h : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) : (E n).comap φ = F n := by
  apply le_antisymm
  · intro x hx
    have hx' : φ x ∈ (F n).map φ := by
      simpa [h n] using hx
    rcases hx' with ⟨y, hy, hyx⟩
    have : y = x := hinj hyx
    simpa [← this] using hy
  · intro x hx
    exact (MapsOnto.preserves h n) ⟨x, hx, rfl⟩

/-- Inequality form of `MapsOnto.comap_eq_inj`. -/
theorem MapsOnto.comap_le_inj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (h : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) : (E n).comap φ ≤ F n := by
  rw [MapsOnto.comap_eq_inj h hinj n]


/-- For any termwise-onto filtration map, the preimage of a target term is the
source term multiplied by the ordinary kernel.  This is the nonsplit analogue of
the split-epi preimage formula. -/
theorem MapsOnto.comap_eq_supker {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (h : MapsOnto F E φ) (n : ℕ) :
    (E n).comap φ = F n ⊔ φ.ker := by
  apply le_antisymm
  · intro x hx
    have hx' : φ x ∈ (F n).map φ := by
      simpa [h n] using hx
    rcases hx' with ⟨y, hy, hyx⟩
    have hk : y⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hprod : y * (y⁻¹ * x) ∈ F n ⊔ φ.ker :=
      Subgroup.mul_mem_sup hy hk
    simpa [mul_assoc] using hprod
  · apply sup_le
    · intro x hx
      exact (MapsOnto.preserves h n) ⟨x, hx, rfl⟩
    · intro x hx
      change φ x ∈ E n
      rw [MonoidHom.mem_ker] at hx
      rw [hx]
      exact (E n).one_mem


/-- Under a termwise-onto map, exact preimage at a term is equivalent to the ordinary
kernel being contained in that source term. -/
theorem MapsOnto.comap_eqiff_kerle {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (h : MapsOnto F E φ) (n : ℕ) :
    (E n).comap φ = F n ↔ φ.ker ≤ F n := by
  constructor
  · intro hc x hx
    have hxpre : x ∈ (E n).comap φ := by
      change φ x ∈ E n
      rw [MonoidHom.mem_ker] at hx
      rw [hx]
      exact (E n).one_mem
    simpa [hc] using hxpre
  · intro hk
    rw [MapsOnto.comap_eq_supker h n]
    exact sup_eq_left.mpr hk

/-- An injective homomorphism has kernel contained in every term of any filtration. -/
theorem ker_term_injective {F : DFilt G} {φ : G →* H}
    (hinj : Function.Injective φ) (n : ℕ) : φ.ker ≤ F n := by
  intro x hx
  have hx1 : x = 1 := by
    apply hinj
    simpa [MonoidHom.mem_ker] using hx
  simp [hx1]

/-- Termwise-onto namespace wrapper for `ker_term_injective`. -/
theorem MapsOnto.ker_le_inj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (_h : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) : φ.ker ≤ F n :=
  ker_term_injective (F := F) hinj n

/-- Kernel containment in a deeper term of a descending filtration implies containment
in every earlier term.  This small monotonicity helper is convenient when reusing a
single small-kernel hypothesis at several quotient levels. -/
theorem ker_le_le {F : DFilt G} {φ : G →* H}
    {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n) : φ.ker ≤ F m :=
  le_trans hker (F.antitone hmn)

/-- Termwise-onto variant of `ker_le_le`, with the map hypothesis explicit for
namespace-driven rewriting. -/
theorem MapsOnto.ker_le_lea {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (_h : MapsOnto F E φ)
    {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n) : φ.ker ≤ F m :=
  ker_le_le (F := F) hker hmn

/-- Succ-specialized form of `ker_le_le`. -/
theorem ker_term_succ {F : DFilt G} {φ : G →* H}
    {n : ℕ} (hker : φ.ker ≤ F (n + 1)) : φ.ker ≤ F n :=
  ker_le_le (F := F) hker (Nat.le_succ n)

/-- Succ-specialized termwise-onto namespace wrapper for kernel-containment monotonicity. -/
theorem MapsOnto.ker_le_succ {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (h : MapsOnto F E φ)
    {n : ℕ} (hker : φ.ker ≤ F (n + 1)) : φ.ker ≤ F n :=
  h.ker_le_lea hker (Nat.le_succ n)

@[simp] theorem mapsOnto_id (F : DFilt G) : MapsOnto F F (MonoidHom.id G) := by
  intro n
  simp

/-- Composition of termwise onto filtration maps. -/
theorem MapsOnto.comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K} (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) :
    MapsOnto F D (ψ.comp φ) := by
  intro n
  rw [← Subgroup.map_map, hφ n, hψ n]

/-- A filtration-preserving equivalence in both directions is termwise onto. -/
theorem MapsOnto.of_equiv {F : DFilt G} {E : DFilt H}
    (e : G ≃* H) (hf : Preserves F E e.toMonoidHom)
    (hb : Preserves E F e.symm.toMonoidHom) : MapsOnto F E e.toMonoidHom := by
  intro n
  apply le_antisymm
  · exact hf n
  · intro y hy
    refine ⟨e.symm y, ?_, ?_⟩
    · exact hb n ⟨y, hy, rfl⟩
    · simp

/-- A split epimorphism whose section is filtration-preserving is termwise onto.
This is often the easiest way to obtain strict compatibility for split quotients. -/
theorem MapsOnto.of_rightInverse {F : DFilt G} {E : DFilt H}
    {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) : MapsOnto F E φ := by
  intro n
  apply le_antisymm
  · exact hφ n
  · intro y hy
    refine ⟨σ y, ?_, hright y⟩
    exact hσ n ⟨y, hy, rfl⟩


/-- A surjective filtration-preserving map is termwise onto as soon as every preimage
of a target term lies in the corresponding source term.  This repackages the usual
"surjective plus exact preimage" criterion in a form convenient for filtrations. -/
theorem MapsOnto.surj_comap_le {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    (hs : Function.Surjective φ) (hpre : ∀ n, (E n).comap φ ≤ F n) :
    MapsOnto F E φ := by
  intro n
  apply le_antisymm
  · exact hφ n
  · intro y hy
    rcases hs y with ⟨x, rfl⟩
    refine ⟨x, hpre n ?_, rfl⟩
    exact hy

/-- A convenient termwise-onto criterion when the preimage of each target term is
exactly the corresponding source term. -/
theorem MapsOnto.surj_comap_eq {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    (hs : Function.Surjective φ) (hpre : ∀ n, (E n).comap φ = F n) :
    MapsOnto F E φ :=
  MapsOnto.surj_comap_le hφ hs (fun n => by rw [hpre n])


/-- If a surjective homomorphism has exact preimages of all filtration terms, then it
is termwise onto; the preservation hypothesis is recovered from the same equality. -/
theorem MapsOnto.surj_comap_eqexact {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hs : Function.Surjective φ)
    (hpre : ∀ n, (E n).comap φ = F n) : MapsOnto F E φ := by
  have hφ : Preserves F E φ := by
    intro n y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx' : x ∈ (E n).comap φ := by
      simpa [hpre n] using hx
    exact hx'
  exact MapsOnto.surj_comap_eq hφ hs hpre

/-- For a split epimorphism compatible with filtrations in both directions, the preimage
of a target term is exactly the source term times the kernel. -/
theorem comap_sup_ker {F : DFilt G}
    {E : DFilt H} {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) (n : ℕ) :
    (E n).comap φ = F n ⊔ φ.ker := by
  apply le_antisymm
  · intro x hx
    let y : G := σ (φ x)
    let k : G := y⁻¹ * x
    have hy : y ∈ F n := by
      have him : σ (φ x) ∈ (E n).map σ := ⟨φ x, hx, rfl⟩
      exact hσ n him
    have hk : k ∈ φ.ker := by
      change φ k = 1
      dsimp [k, y]
      simp [map_mul, hright (φ x)]
    have hyS : y ∈ F n ⊔ φ.ker := (show F n ≤ F n ⊔ φ.ker from le_sup_left) hy
    have hkS : k ∈ F n ⊔ φ.ker := (show φ.ker ≤ F n ⊔ φ.ker from le_sup_right) hk
    have hxprod : y * k ∈ F n ⊔ φ.ker := (F n ⊔ φ.ker).mul_mem hyS hkS
    convert hxprod using 1
    dsimp [k]
    simp [y]
  · refine sup_le ?_ ?_
    · intro x hxF
      exact hφ n ⟨x, hxF, rfl⟩
    · intro x hxK
      change φ x ∈ E n
      have hx1 : φ x = 1 := by simpa using hxK
      rw [hx1]
      exact (E n).one_mem

@[simp] theorem preserves_id (F : DFilt G) : Preserves F F (MonoidHom.id G) := by
  intro n
  simp

/-- Composition of filtration-preserving homomorphisms. -/
theorem Preserves.comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K} (hφ : Preserves F E φ) (hψ : Preserves E D ψ) :
    Preserves F D (ψ.comp φ) := by
  intro n
  -- `Subgroup.map_map` rewrites the image under a composite.
  rw [← Subgroup.map_map]
  exact le_trans (Subgroup.map_mono (hφ n)) (hψ n)


/-! ### Quotient functoriality

The following small API packages the routine quotient maps attached to a
filtration-preserving homomorphism, and the transition maps inside one descending
filtration.  Keeping these in the generic filtration file avoids repeating the
same `QuotientGroup.map` boilerplate for Frattini, Zassenhaus, and later
truncated filtrations.
-/

/-- A filtration-preserving homomorphism induces a homomorphism on every quotient
`G/Fₙ → H/Eₙ`. -/
noncomputable def quotientMap {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    (G ⧸ (F n)) →* (H ⧸ (E n)) :=
  QuotientGroup.map (F n) (E n) φ ((Subgroup.map_le_iff_le_comap).1 (hφ n))

@[simp] theorem quotientMap_mk {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) (g : G) :
    quotientMap hφ n (QuotientGroup.mk' (F n) g) = QuotientGroup.mk' (E n) (φ g) := rfl

@[simp] theorem quotientMap_id (F : DFilt G) (n : ℕ) :
    quotientMap (preserves_id F) n = MonoidHom.id (G ⧸ (F n)) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

@[simp] theorem quotientMap_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ) (n : ℕ) :
    quotientMap (Preserves.comp hφ hψ) n =
      (quotientMap hψ n).comp (quotientMap hφ n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- The kernel of an induced quotient map is represented by the preimage of the
target filtration term in the source quotient. -/
theorem ker_quotient_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    MonoidHom.ker (quotientMap hφ n) =
      ((E n).comap φ).map (QuotientGroup.mk' (F n)) := by
  ext q
  constructor
  · intro hq
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    change quotientMap hφ n (QuotientGroup.mk' (F n) g) = 1 at hg
    rw [quotientMap_mk] at hg
    have hgmem : g ∈ (E n).comap φ :=
      (QuotientGroup.eq_one_iff (N := E n) (φ g)).1 hg
    exact ⟨g, hgmem, rfl⟩
  · intro hq
    rcases hq with ⟨g, hg, rfl⟩
    change quotientMap hφ n (QuotientGroup.mk' (F n) g) = 1
    rw [quotientMap_mk]
    exact (QuotientGroup.eq_one_iff (N := E n) (φ g)).2 hg


/-- The kernel of an induced quotient map is canonically isomorphic to the quotient
of the preimage subgroup by its intersection with the source term.  Since preserving
maps have `F n ≤ (E n).comap φ`, this is morally `(φ⁻¹ Eₙ)/Fₙ`. -/
noncomputable def quotientKernelEquiv {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    ((E n).comap φ) ⧸ ((F n).subgroupOf ((E n).comap φ)) ≃*
      MonoidHom.ker (quotientMap hφ n) := by
  let C : Subgroup G := (E n).comap φ
  let N : Subgroup C := (F n).subgroupOf C
  let kmap : C →* MonoidHom.ker (quotientMap hφ n) :=
  { toFun := fun c => ⟨QuotientGroup.mk' (F n) (c : G), by
      change quotientMap hφ n (QuotientGroup.mk' (F n) (c : G)) = 1
      rw [quotientMap_mk]
      exact (QuotientGroup.eq_one_iff (N := E n) (φ (c : G))).2 c.property⟩
    map_one' := by ext; simp
    map_mul' := by intro a b; ext; simp }
  have hk_surj : Function.Surjective kmap := by
    intro q
    rcases q with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    change quotientMap hφ n (QuotientGroup.mk' (F n) g) = 1 at hg
    rw [quotientMap_mk] at hg
    have gc : g ∈ C := (QuotientGroup.eq_one_iff (N := E n) (φ g)).1 hg
    refine ⟨⟨g, gc⟩, ?_⟩
    ext
    rfl
  have hker : MonoidHom.ker kmap = N := by
    ext c
    constructor
    · intro hc
      have hcval := congrArg Subtype.val hc
      change QuotientGroup.mk' (F n) (c : G) = 1 at hcval
      exact (QuotientGroup.eq_one_iff (N := F n) (c : G)).1 hcval
    · intro hc
      ext
      change QuotientGroup.mk' (F n) (c : G) = 1
      exact (QuotientGroup.eq_one_iff (N := F n) (c : G)).2 hc
  refine (QuotientGroup.quotientMulEquivOfEq ?_).trans
    (QuotientGroup.quotientKerEquivOfSurjective kmap hk_surj)
  exact hker.symm

@[simp] theorem quotient_kernel_mk {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (c : (E n).comap φ) :
    quotientKernelEquiv hφ n
        (QuotientGroup.mk' ((F n).subgroupOf ((E n).comap φ)) c) =
      ⟨QuotientGroup.mk' (F n) (c : G), by
        change quotientMap hφ n (QuotientGroup.mk' (F n) (c : G)) = 1
        rw [quotientMap_mk]
        exact (QuotientGroup.eq_one_iff (N := E n) (φ (c : G))).2 c.property⟩ := rfl

/-- Characterize the inverse of the kernel equivalence for an induced quotient map. -/
theorem quotient_kernel_symm {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (y : MonoidHom.ker (quotientMap hφ n))
    (x : ((E n).comap φ) ⧸ ((F n).subgroupOf ((E n).comap φ))) :
    (quotientKernelEquiv hφ n).symm y = x ↔
      y = quotientKernelEquiv hφ n x := by
  rw [MulEquiv.symm_apply_eq]


/-- If the underlying homomorphism is surjective, then each induced quotient map is
surjective. -/
theorem quotientMap_surjective {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (hs : Function.Surjective φ) (n : ℕ) :
    Function.Surjective (quotientMap hφ n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  rcases hs h with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (F n) g, rfl⟩

/-- For a termwise-onto filtration map with injective underlying homomorphism, the
preimage of each target term is exactly contained in the corresponding source term. -/
theorem comap_maps_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (E n).comap φ ≤ F n := by
  intro g hg
  have hmap : φ g ∈ (F n).map φ := by
    simpa [honto n] using hg
  rcases hmap with ⟨x, hx, hxeq⟩
  have hxg : (x : G) = g := hinj hxeq
  simpa [← hxg] using hx


/-- Under termwise onto plus injectivity, each target term has exactly the source
term as its preimage. -/
theorem comap_onto_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (E n).comap φ = F n := by
  apply le_antisymm
  · exact comap_maps_injective honto hinj n
  · intro g hg
    rw [← honto n]
    exact ⟨g, hg, rfl⟩

/-- A termwise-onto filtration map with injective underlying homomorphism induces
injective maps on all same-index quotients. -/
theorem quotient_injective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Injective (quotientMap (MapsOnto.preserves honto) n) := by
  intro q r hqr
  apply eq_of_mul_inv_eq_one
  refine QuotientGroup.induction_on q ?_ r hqr
  intro g r hgr
  refine QuotientGroup.induction_on r ?_ hgr
  intro h hh
  change quotientMap (MapsOnto.preserves honto) n (QuotientGroup.mk' (F n) g) =
      quotientMap (MapsOnto.preserves honto) n (QuotientGroup.mk' (F n) h) at hh
  rw [quotientMap_mk, quotientMap_mk] at hh
  have hone : QuotientGroup.mk' (E n) (φ (g * h⁻¹)) = 1 := by
    have hc := congrArg (fun z => z * (QuotientGroup.mk' (E n) (φ h))⁻¹) hh
    simpa [map_mul, map_inv] using hc
  have hmemE : φ (g * h⁻¹) ∈ E n :=
    (QuotientGroup.eq_one_iff (φ (g * h⁻¹))).1 hone
  have hpre : g * h⁻¹ ∈ F n := by
    have hmap : φ (g * h⁻¹) ∈ (F n).map φ := by
      simpa [honto n] using hmemE
    rcases hmap with ⟨x, hx, hxeq⟩
    have hxval : (x : G) = g * h⁻¹ := hinj hxeq
    simpa [← hxval] using hx
  exact (QuotientGroup.eq_one_iff (g * h⁻¹)).2 hpre

/-- Termwise-onto filtration maps with injective underlying homomorphism induce
bijections on all same-index quotients. -/
theorem quotient_bijective_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (quotientMap (MapsOnto.preserves honto) n) :=
  ⟨quotient_injective_onto honto hinj n,
    quotientMap_surjective (MapsOnto.preserves honto) (MapsOnto.surjective honto) n⟩


/-- A termwise-onto filtration map with injective underlying homomorphism induces
an equivalence on same-index quotients. -/
noncomputable def quotientOntoInjective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) : G ⧸ F n ≃* H ⧸ E n :=
  MulEquiv.ofBijective (quotientMap (MapsOnto.preserves honto) n)
    (quotient_bijective_injective honto hinj n)

@[simp] theorem quotient_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : G ⧸ F n) :
    quotientOntoInjective honto hinj n x =
      quotientMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem quotient_monoid_hom
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ) :
    (quotientOntoInjective honto hinj n).toMonoidHom =
      quotientMap (MapsOnto.preserves honto) n := rfl

/-- Inverse-characterization for the quotient equivalence from a termwise-onto
injective filtration map. -/
theorem equiv_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : H ⧸ E n) (x : G ⧸ F n) :
    (quotientOntoInjective honto hinj n).symm y = x ↔
      y = quotientMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Termwise-onto filtration maps induce surjective maps on all same-index quotients. -/
theorem quotient_surjective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    Function.Surjective (quotientMap (MapsOnto.preserves honto) n) :=
  quotientMap_surjective (MapsOnto.preserves honto) (MapsOnto.surjective honto) n

/-- Range form of surjectivity for same-index quotient maps. -/
theorem range_maps_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    (quotientMap (MapsOnto.preserves honto) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (quotient_surjective_onto honto n)

/-- An induced quotient map is injective if the preimage of the target term is contained
in the source term. -/
theorem quotient_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ}
    (hker : (E n).comap φ ≤ F n) : Function.Injective (quotientMap hφ n) := by
  intro a b hab
  refine QuotientGroup.induction_on a ?_ hab
  intro x
  refine QuotientGroup.induction_on b ?_
  intro y hxy
  change QuotientGroup.mk' (E n) (φ x) = QuotientGroup.mk' (E n) (φ y) at hxy
  apply QuotientGroup.eq.mpr
  apply hker
  change φ (x⁻¹ * y) ∈ E n
  rw [map_mul, map_inv]
  exact QuotientGroup.eq.mp hxy

/-- Injectivity of an induced quotient map is equivalent to having no extra
preimage of the target filtration term. -/
theorem quotient_injective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ} :
    Function.Injective (quotientMap hφ n) ↔ (E n).comap φ ≤ F n := by
  constructor
  · intro hinj x hx
    have hleft : quotientMap hφ n (QuotientGroup.mk' (F n) x) = 1 := by
      rw [quotientMap_mk]
      exact (QuotientGroup.eq_one_iff (N := E n) (φ x)).2 hx
    have hmap : quotientMap hφ n (QuotientGroup.mk' (F n) x) = quotientMap hφ n 1 := by
      simpa using hleft
    have hq := hinj hmap
    have : QuotientGroup.mk' (F n) x = (1 : G ⧸ F n) := hq
    exact (QuotientGroup.eq_one_iff (N := F n) x).1 (by simpa using this)
  · exact quotient_comap hφ

/-- For a surjective underlying homomorphism, bijectivity on a quotient is
equivalent to the same preimage condition as injectivity. -/
theorem quotient_bijective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    (hs : Function.Surjective φ) {n : ℕ} :
    Function.Bijective (quotientMap hφ n) ↔ (E n).comap φ ≤ F n := by
  constructor
  · intro hb
    exact (quotient_injective_comap hφ).1 hb.1
  · intro hpre
    exact ⟨(quotient_injective_comap hφ).2 hpre,
      quotientMap_surjective hφ hs n⟩


/-- For a termwise-onto filtration map, injectivity on the `n`th quotient is
equivalent to the ordinary kernel lying in the source term. -/
theorem injective_maps_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ} :
    Function.Injective (quotientMap (MapsOnto.preserves honto) n) ↔ φ.ker ≤ F n := by
  constructor
  · intro hinj
    have hc : (E n).comap φ ≤ F n :=
      (quotient_injective_comap (MapsOnto.preserves honto)).1 hinj
    have hfc : F n ≤ (E n).comap φ :=
      (Subgroup.map_le_iff_le_comap).1 ((MapsOnto.preserves honto) n)
    have heq : (E n).comap φ = F n := le_antisymm hc hfc
    exact (MapsOnto.comap_eqiff_kerle honto n).1 heq
  · intro hk
    have heq : (E n).comap φ = F n :=
      (MapsOnto.comap_eqiff_kerle honto n).2 hk
    exact (quotient_injective_comap (MapsOnto.preserves honto)).2
      (by rw [heq])

/-- For a termwise-onto filtration map, bijectivity on the `n`th quotient is
equivalent to the ordinary kernel lying in the source term. -/
theorem bijective_ker_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ} :
    Function.Bijective (quotientMap (MapsOnto.preserves honto) n) ↔ φ.ker ≤ F n := by
  constructor
  · intro hb
    exact (injective_maps_onto honto).1 hb.1
  · intro hk
    exact ⟨(injective_maps_onto honto).2 hk,
      quotient_surjective_onto honto n⟩

/-- If the kernel is contained in a deeper source term, then all earlier quotient maps
are bijective. -/
theorem quotient_bijective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n) :
    Function.Bijective (quotientMap (MapsOnto.preserves honto) m) :=
  (bijective_ker_onto honto).2
    (honto.ker_le_lea hker hmn)

/-- Succ-specialized convenience: kernel containment in `F (n+1)` gives bijectivity
on the `n`th quotient map. -/
theorem bijective_maps_succ
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1)) :
    Function.Bijective (quotientMap (MapsOnto.preserves honto) n) :=
  quotient_bijective_ker honto hker (Nat.le_succ n)


/-- A termwise-onto filtration map whose ordinary kernel lies in `F n` induces an
equivalence on the `n`th quotients. -/
noncomputable def quotientMapsKer {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hker : φ.ker ≤ F n) : (G ⧸ F n) ≃* (H ⧸ E n) :=
  MulEquiv.ofBijective (quotientMap (MapsOnto.preserves honto) n)
    ((bijective_ker_onto honto).2 hker)

/-- A deeper kernel-containment hypothesis also induces equivalences on all earlier
quotients. -/
noncomputable def quotientOntoKer {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n) :
    (G ⧸ F m) ≃* (H ⧸ E m) :=
  quotientMapsKer honto (honto.ker_le_lea hker hmn)

@[simp] theorem quotient_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n)
    (x : G ⧸ F m) :
    quotientOntoKer honto hker hmn x =
      quotientMap (MapsOnto.preserves honto) m x := rfl

@[simp] theorem maps_monoid_hom
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n) :
    (quotientOntoKer honto hker hmn).toMonoidHom =
      quotientMap (MapsOnto.preserves honto) m := rfl

/-- Inverse-characterization for the monotone-kernel quotient equivalence. -/
theorem quotient_maps_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n)
    (y : H ⧸ E m) (x : G ⧸ F m) :
    (quotientOntoKer honto hker hmn).symm y = x ↔
      y = quotientMap (MapsOnto.preserves honto) m x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

@[simp] theorem maps_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hker : φ.ker ≤ F n) (x : G ⧸ F n) :
    quotientMapsKer honto hker x =
      quotientMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem onto_ker_monoid {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hker : φ.ker ≤ F n) :
    (quotientMapsKer honto hker).toMonoidHom =
      quotientMap (MapsOnto.preserves honto) n := rfl

/-- Inverse-characterization for quotient equivalences from termwise-onto maps with
kernel contained in the source term. -/
theorem quotient_equiv_maps {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hker : φ.ker ≤ F n) (y : H ⧸ E n) (x : G ⧸ F n) :
    (quotientMapsKer honto hker).symm y = x ↔
      y = quotientMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- For a split epimorphism compatible with filtrations in both directions, injectivity
on the `n`th quotient is equivalent to the ordinary kernel lying in the source term. -/
theorem injective_ker_inverse {F : DFilt G}
    {E : DFilt H} {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (quotientMap hφ n) ↔ φ.ker ≤ F n := by
  have hcomap := comap_sup_ker hφ hσ hright n
  rw [quotient_injective_comap hφ]
  constructor
  · intro hc x hx
    apply hc
    rw [hcomap]
    exact (show φ.ker ≤ F n ⊔ φ.ker from le_sup_right) hx
  · intro hk
    rw [hcomap]
    exact sup_le le_rfl hk

/-- For a split epimorphism compatible with filtrations in both directions, bijectivity
on the `n`th quotient is equivalent to the ordinary kernel lying in the source term. -/
theorem bijective_ker_inverse {F : DFilt G}
    {E : DFilt H} {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (quotientMap hφ n) ↔ φ.ker ≤ F n := by
  have hs : Function.Surjective φ := fun y => ⟨σ y, hright y⟩
  constructor
  · intro hb
    exact (injective_ker_inverse hφ hσ hright).1 hb.1
  · intro hk
    exact ⟨(injective_ker_inverse hφ hσ hright).2 hk,
      quotientMap_surjective hφ hs n⟩

/-- Termwise-onto filtration maps are bijective on a quotient exactly when the
preimage condition holds. -/
theorem bijective_comap_maps {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ} :
    Function.Bijective (quotientMap (MapsOnto.preserves honto) n) ↔
      (E n).comap φ ≤ F n :=
  quotient_bijective_comap (MapsOnto.preserves honto)
    (MapsOnto.surjective honto)

/-- The canonical transition map `G/Fₙ → G/Fₘ` for `m ≤ n` in a descending
filtration. -/
noncomputable def quotientTransition (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) : (G ⧸ (F n)) →* (G ⧸ (F m)) :=
  QuotientGroup.map (F n) (F m) (MonoidHom.id G) (by
    simpa using F.mono_membership h)

@[simp] theorem quotientTransition_mk (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) (g : G) :
    quotientTransition F h (QuotientGroup.mk' (F n) g) = QuotientGroup.mk' (F m) g := rfl

@[simp] theorem quotientTransition_rfl (F : DFilt G) (n : ℕ) :
    quotientTransition F (le_rfl : n ≤ n) = MonoidHom.id (G ⧸ (F n)) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Representative criterion for the kernel of an arbitrary quotient transition. -/
@[simp] theorem ker_quotient_mk (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) (g : G) :
    QuotientGroup.mk' (F n) g ∈ MonoidHom.ker (quotientTransition F h) ↔ g ∈ F m := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff g

/-- The kernel of a quotient transition consists of classes represented by the target
filtration term.  This extensional form is often convenient for rewriting. -/
theorem ker_quotient_transition (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) :
    MonoidHom.ker (quotientTransition F h) =
      (F m).map (QuotientGroup.mk' (F n)) := by
  ext q
  constructor
  · intro hq
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    exact ⟨g, (ker_quotient_mk F h g).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (ker_quotient_mk F h g).2 hg

/-- Quotient transition maps are surjective: every class modulo `F_m` is represented
by the same element modulo the smaller subgroup `F_n`. -/
theorem quotientTransition_surjective (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) : Function.Surjective (quotientTransition F h) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  refine ⟨QuotientGroup.mk' (F n) g, ?_⟩
  rfl

/-- The deeper term `F n`, viewed as a subgroup of `F m` for `m ≤ n`. -/
def tSOf (F : DFilt G) {m n : ℕ} (_h : m ≤ n) :
    Subgroup (F m) :=
  (F n).subgroupOf (F m)

@[simp] theorem mem_term_of (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) (x : F m) :
    x ∈ tSOf F h ↔ (x : G) ∈ F n :=
  Subgroup.mem_subgroupOf

instance term_subgroup_normal (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    (tSOf F h).Normal where
  conj_mem := by
    intro x hx y
    rw [mem_term_of] at hx ⊢
    change (y : G) * (x : G) * (y : G)⁻¹ ∈ F n
    exact Subgroup.Normal.conj_mem (F.normal' n) (x : G) hx (y : G)

/-- A deeper concrete term, viewed inside `F m`, is contained in an intermediate
concrete term. -/
theorem of_of_le (F : DFilt G) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf F (Nat.le_trans hmn hnk) ≤ tSOf F hmn := by
  intro x hx
  rw [mem_term_of] at hx ⊢
  exact F.mono_membership hnk hx

/-- Canonical inclusion of a deeper concrete term into an intermediate concrete term. -/
def tSOf.inclusion (F : DFilt G) {m n k : ℕ}
    (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf F (Nat.le_trans hmn hnk) →* tSOf F hmn :=
  Subgroup.inclusion (of_of_le F hmn hnk)

@[simp] theorem tSOf.inclusion_apply (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F (Nat.le_trans hmn hnk)) :
    (tSOf.inclusion F hmn hnk x : F m) = x := rfl

/-- Canonical inclusions between concrete filtration terms are injective. -/
theorem tSOf.inclusion_injective (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective (tSOf.inclusion F hmn hnk) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : tSOf F hmn => (z : F m)) hxy

@[simp] theorem tSOf.inclusion_apply_eqiff (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : tSOf F (Nat.le_trans hmn hnk)) :
    tSOf.inclusion F hmn hnk x = tSOf.inclusion F hmn hnk y ↔
      x = y := by
  constructor
  · intro h
    exact tSOf.inclusion_injective F hmn hnk h
  · intro h
    simp [h]

/-- Nested inclusions of concrete filtration terms compose as expected. -/
@[simp] theorem tSOf.inclusion_comp (F : DFilt G)
    {m n k l : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (hkl : k ≤ l) :
    (tSOf.inclusion F hmn hnk).comp
        (tSOf.inclusion F (Nat.le_trans hmn hnk) hkl) =
      tSOf.inclusion F hmn (Nat.le_trans hnk hkl) := by
  ext x
  rfl

/-- The reflexive concrete-term inclusion is the identity. -/
@[simp] theorem tSOf.inclusion_refl (F : DFilt G)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf.inclusion F hmn (Nat.le_refl n) =
      MonoidHom.id (tSOf F hmn) := by
  ext x
  rfl

/-- Range criterion for the canonical inclusion between concrete filtration terms. -/
theorem tSOf.mem_range_inclusioniff (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : tSOf F hmn) :
    y ∈ (tSOf.inclusion F hmn hnk).range ↔ ((y : F m) : G) ∈ F k := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (mem_term_of F (Nat.le_trans hmn hnk) (x : F m)).1 x.property
  · intro hy
    let x : tSOf F (Nat.le_trans hmn hnk) :=
      ⟨(y : F m), (mem_term_of F (Nat.le_trans hmn hnk) (y : F m)).2 hy⟩
    refine ⟨x, ?_⟩
    ext
    rfl

/-- The range of a concrete-term inclusion is normal in the intermediate term. -/
theorem tSOf.inclusion_range_normal (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion F hmn hnk).range.Normal := by
  constructor
  intro x hx y
  rw [tSOf.mem_range_inclusioniff F hmn hnk] at hx ⊢
  change ((y : F m) : G) * ((x : F m) : G) * ((y : F m) : G)⁻¹ ∈ F k
  exact (F.normal' k).conj_mem ((x : F m) : G) hx ((y : F m) : G)

instance tSOf.iRange.instNormal (F : DFilt G)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion F hmn hnk).range.Normal :=
  tSOf.inclusion_range_normal F hmn hnk

/-- Map a filtration term into the kernel of the transition from `G/F_n` to `G/F_m`. -/
noncomputable def termTransitionKernel (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) : F m →* MonoidHom.ker (quotientTransition F h) where
  toFun x := ⟨QuotientGroup.mk' (F n) (x : G), by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (x : G)).2 x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem term_transition_coe (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) (x : F m) :
    ((termTransitionKernel F h x : MonoidHom.ker (quotientTransition F h)) :
        G ⧸ F n) = QuotientGroup.mk' (F n) (x : G) := rfl

/-- Every element of a transition kernel has a representative in the target term. -/
theorem term_transition_surjective (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) : Function.Surjective (termTransitionKernel F h) := by
  intro y
  rcases y with ⟨q, hq⟩
  refine QuotientGroup.induction_on q ?_ hq
  intro g hg
  have hgm : g ∈ F m := (ker_quotient_mk F h g).1 hg
  refine ⟨⟨g, hgm⟩, ?_⟩
  ext
  rfl

@[simp] theorem ker_term_transition (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) (x : F m) :
    x ∈ MonoidHom.ker (termTransitionKernel F h) ↔ (x : G) ∈ F n := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hv := congrArg
      (fun y : MonoidHom.ker (quotientTransition F h) => (y : G ⧸ F n)) hx
    change QuotientGroup.mk' (F n) (x : G) = 1 at hv
    exact (QuotientGroup.eq_one_iff (x : G)).1 hv
  · intro hx
    ext
    change QuotientGroup.mk' (F n) (x : G) = 1
    exact (QuotientGroup.eq_one_iff (x : G)).2 hx

/-- The kernel of the term-to-transition-kernel map is the deeper term. -/
theorem ker_transition_kernel (F : DFilt G) {m n : ℕ}
    (h : m ≤ n) :
    MonoidHom.ker (termTransitionKernel F h) = tSOf F h := by
  ext x
  rw [ker_term_transition, mem_term_of]

/-- First-isomorphism-theorem form of an arbitrary transition kernel:
`ker(G/F_n → G/F_m) ≃ F_m/F_n`. -/
noncomputable def transitionKernelEquiv (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) :
    (F m ⧸ tSOf F h) ≃* MonoidHom.ker (quotientTransition F h) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_transition_kernel F h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (termTransitionKernel F h)
      (term_transition_surjective F h))

@[simp] theorem transition_equiv_mk (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) (x : F m) :
    transitionKernelEquiv F h (QuotientGroup.mk' (tSOf F h) x) =
      termTransitionKernel F h x := by
  dsimp [transitionKernelEquiv, QuotientGroup.quotientKerEquivOfSurjective]

@[simp] theorem transition_kernel_coe (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) (x : F m) :
    ((transitionKernelEquiv F h
        (QuotientGroup.mk' (tSOf F h) x) :
        MonoidHom.ker (quotientTransition F h)) : G ⧸ F n) =
      QuotientGroup.mk' (F n) (x : G) := by
  rw [transition_equiv_mk]
  rfl

/-- Characterize the inverse of the arbitrary transition-kernel quotient equivalence. -/
theorem kernel_quotient_symm
    (F : DFilt G) {m n : ℕ} (h : m ≤ n)
    (y : MonoidHom.ker (quotientTransition F h))
    (x : F m ⧸ tSOf F h) :
    (transitionKernelEquiv F h).symm y = x ↔
      y = transitionKernelEquiv F h x := by
  rw [MulEquiv.symm_apply_eq]


/-- Explicit inverse representative for the transition-kernel quotient equivalence. -/
@[simp] theorem transition_kernel_mk (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) (g : G) (hg : g ∈ F m) :
    (transitionKernelEquiv F h).symm
        ⟨QuotientGroup.mk' (F n) g, by
          rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff g).2 hg⟩ =
      QuotientGroup.mk' (tSOf F h) (⟨g, hg⟩ : F m) := by
  apply (transitionKernelEquiv F h).injective
  rw [transition_equiv_mk]
  ext
  simp [term_transition_coe]

/-- Transition maps compose along chains of indices. -/
theorem quotientTransition_comp (F : DFilt G) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    quotientTransition F (le_trans hlm hmn) =
      (quotientTransition F hlm).comp (quotientTransition F hmn) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

/-- Quotient maps commute with the canonical transition maps of two filtrations. -/
theorem quotientTransition_naturality {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n) :
    (quotientTransition E h).comp (quotientMap hφ n) =
      (quotientMap hφ m).comp (quotientTransition F h) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl


/-! ### Generic layer kernels -/

/-- The `n`th layer of a descending filtration, represented as the kernel of the
transition `G/F_{n+1} → G/F_n`. -/
noncomputable def lKern (F : DFilt G) (n : ℕ) :
    Subgroup (G ⧸ (F (n + 1))) :=
  MonoidHom.ker (quotientTransition F (Nat.le_succ n))

@[simp] theorem layer_kernel_mk (F : DFilt G) (n : ℕ) (g : G) :
    QuotientGroup.mk' (F (n + 1)) g ∈ lKern F n ↔ g ∈ F n := by
  dsimp [lKern]
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff g

/-- The successive quotient-transition kernel is definitionally the layer kernel. -/
@[simp] theorem ker_transition_succ (F : DFilt G) (n : ℕ) :
    MonoidHom.ker (quotientTransition F (Nat.le_succ n)) = lKern F n := rfl

/-- Representative criterion for membership in the kernel of a successive transition. -/
@[simp] theorem ker_transition_mk (F : DFilt G)
    (n : ℕ) (g : G) :
    QuotientGroup.mk' (F (n + 1)) g ∈
        MonoidHom.ker (quotientTransition F (Nat.le_succ n)) ↔ g ∈ F n :=
  layer_kernel_mk F n g

/-- If commutators of elements of `F n` land in `F (n+1)`, then commutators
of representatives in the `n`th layer kernel vanish in the quotient. -/
theorem layer_commutator_succ (F : DFilt G) (n : ℕ)
    (hcomm : ∀ {x y : G}, x ∈ F n → y ∈ F n → ⁅x, y⁆ ∈ F (n + 1))
    {q r : G ⧸ F (n + 1)}
    (hq : q ∈ lKern F n) (hr : r ∈ lKern F n) : ⁅q, r⁆ = 1 := by
  refine QuotientGroup.induction_on q ?_ hq
  intro g hg
  refine QuotientGroup.induction_on r ?_ hr
  intro h hh
  have hg' : g ∈ F n := (layer_kernel_mk F n g).1 hg
  have hh' : h ∈ F n := (layer_kernel_mk F n h).1 hh
  change QuotientGroup.mk' (F (n + 1)) ⁅g, h⁆ = 1
  exact (QuotientGroup.eq_one_iff ⁅g, h⁆).2 (hcomm hg' hh')

/-- Multiplicative commutativity inside a layer kernel from the usual commutator
containment condition. -/
theorem layer_comm_succ (F : DFilt G) (n : ℕ)
    (hcomm : ∀ {x y : G}, x ∈ F n → y ∈ F n → ⁅x, y⁆ ∈ F (n + 1))
    (x y : lKern F n) : x * y = y * x := by
  ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  exact layer_commutator_succ F n hcomm x.property y.property

/-- A packaged commutative group structure on a layer kernel under the standard
commutator-containment hypothesis.  This is a local construction rather than a global
instance, so specialized filtrations can choose when to install it. -/
@[reducible] noncomputable def lKern.comm_groupcomm_memsucc
    (F : DFilt G) (n : ℕ)
    (hcomm : ∀ {x y : G}, x ∈ F n → y ∈ F n → ⁅x, y⁆ ∈ F (n + 1)) :
    CommGroup (lKern F n) :=
{ (inferInstance : Group (lKern F n)) with
  mul_comm := layer_comm_succ F n hcomm }

/-- The canonical map from the `n`th filtration term to the `n`th layer kernel,
sending an element to its class modulo the next term. -/
noncomputable def layerOfTerm (F : DFilt G) (n : ℕ) :
    F n →* lKern F n where
  toFun x := ⟨QuotientGroup.mk' (F (n + 1)) (x : G), by
    exact (layer_kernel_mk F n (x : G)).2 x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem layer_term_coe (F : DFilt G) (n : ℕ) (x : F n) :
    ((layerOfTerm F n x : lKern F n) : G ⧸ F (n + 1)) =
      QuotientGroup.mk' (F (n + 1)) (x : G) := rfl

/-- Every layer-kernel element has a representative in the corresponding filtration term. -/
theorem layer_term_surjective (F : DFilt G) (n : ℕ) :
    Function.Surjective (layerOfTerm F n) := by
  intro y
  rcases y with ⟨q, hq⟩
  refine QuotientGroup.induction_on q ?_ hq
  intro g hg
  have hgn : g ∈ F n := (layer_kernel_mk F n g).1 hg
  refine ⟨⟨g, hgn⟩, ?_⟩
  ext
  rfl

/-- The kernel of the term-to-layer map is exactly the next filtration term. -/
@[simp] theorem ker_term (F : DFilt G) (n : ℕ) (x : F n) :
    x ∈ MonoidHom.ker (layerOfTerm F n) ↔ (x : G) ∈ F (n + 1) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hv := congrArg (fun y : lKern F n => (y : G ⧸ F (n + 1))) hx
    change QuotientGroup.mk' (F (n + 1)) (x : G) = 1 at hv
    exact (QuotientGroup.eq_one_iff (x : G)).1 hv
  · intro hx
    ext
    change QuotientGroup.mk' (F (n + 1)) (x : G) = 1
    exact (QuotientGroup.eq_one_iff (x : G)).2 hx

/-- The next filtration term, viewed as a subgroup of the current term. -/
def nextTermSubgroup (F : DFilt G) (n : ℕ) : Subgroup (F n) :=
  (F (n + 1)).subgroupOf (F n)

@[simp] theorem next_term_subgroup (F : DFilt G) (n : ℕ) (x : F n) :
    x ∈ nextTermSubgroup F n ↔ (x : G) ∈ F (n + 1) :=
  Subgroup.mem_subgroupOf

instance next_subgroup_normal (F : DFilt G) (n : ℕ) :
    (nextTermSubgroup F n).Normal where
  conj_mem := by
    intro x hx y
    rw [next_term_subgroup] at hx ⊢
    change (y : G) * (x : G) * (y : G)⁻¹ ∈ F (n + 1)
    exact Subgroup.Normal.conj_mem (F.normal' (n + 1)) (x : G) hx (y : G)

/-- The kernel of the term-to-layer map is the next term as a subgroup of the current term. -/
theorem ker_next_subgroup (F : DFilt G) (n : ℕ) :
    MonoidHom.ker (layerOfTerm F n) = nextTermSubgroup F n := by
  ext x
  rw [ker_term, next_term_subgroup]

/-- First-isomorphism-theorem form of a layer: the quotient of a term by the kernel
of its term-to-layer map is equivalent to the layer kernel.  The preceding lemma
identifies this kernel with the next filtration term. -/
noncomputable def layerQuotientEquiv (F : DFilt G) (n : ℕ) :
    (F n ⧸ MonoidHom.ker (layerOfTerm F n)) ≃* lKern F n :=
  QuotientGroup.quotientKerEquivOfSurjective (layerOfTerm F n)
    (layer_term_surjective F n)

@[simp] theorem layer_quotient_mk (F : DFilt G) (n : ℕ)
    (x : F n) :
    layerQuotientEquiv F n
        (QuotientGroup.mk' (MonoidHom.ker (layerOfTerm F n)) x) =
      layerOfTerm F n x := by
  dsimp [layerQuotientEquiv, QuotientGroup.quotientKerEquivOfSurjective]

/-- Characterize the inverse of the abstract layer quotient equivalence. -/
theorem layer_quotient_symm (F : DFilt G)
    (n : ℕ) (y : lKern F n)
    (x : F n ⧸ MonoidHom.ker (layerOfTerm F n)) :
    (layerQuotientEquiv F n).symm y = x ↔ y = layerQuotientEquiv F n x := by
  rw [MulEquiv.symm_apply_eq]


/-- The more concrete quotient description of a layer as `Fₙ / Fₙ₊₁`. -/
noncomputable def layerNextEquiv (F : DFilt G) (n : ℕ) :
    (F n ⧸ nextTermSubgroup F n) ≃* lKern F n :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_next_subgroup F n).symm).trans
    (layerQuotientEquiv F n)

@[simp] theorem layer_next_mk (F : DFilt G) (n : ℕ)
    (x : F n) :
    layerNextEquiv F n (QuotientGroup.mk' (nextTermSubgroup F n) x) =
      layerOfTerm F n x := by
  dsimp [layerNextEquiv]
  rfl

/-- Characterize the inverse of the concrete consecutive-term layer equivalence. -/
theorem layer_next_symm (F : DFilt G)
    (n : ℕ) (y : lKern F n) (x : F n ⧸ nextTermSubgroup F n) :
    (layerNextEquiv F n).symm y = x ↔
      y = layerNextEquiv F n x := by
  rw [MulEquiv.symm_apply_eq]


/-- A preserving homomorphism restricts to a homomorphism between corresponding terms. -/
noncomputable def termMap {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) : F n →* E n where
  toFun x := ⟨φ x, by exact hφ n ⟨x, x.property, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem termMap_coe {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) (x : F n) :
    ((termMap hφ n x : E n) : H) = φ (x : G) := rfl

/-- A filtration-preserving homomorphism restricts to the concrete subgroup `F_n`
viewed inside `F_m`, for any `m ≤ n`. -/
noncomputable def tSOf.map {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf F hmn →* tSOf E hmn where
  toFun x :=
    ⟨termMap hφ m (x : F m), by
      rw [mem_term_of]
      rw [termMap_coe]
      exact hφ n ⟨((x : F m) : G),
        (mem_term_of F hmn (x : F m)).1 x.property, rfl⟩⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

@[simp] theorem tSOf.map_coe {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    ((tSOf.map hφ hmn x : E m) : H) = φ ((x : F m) : G) := rfl

/-- Restricted maps are natural for canonical inclusions between concrete terms. -/
theorem tSOf.inclusion_comp_map {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion E hmn hnk).comp
        (tSOf.map hφ (Nat.le_trans hmn hnk)) =
      (tSOf.map hφ hmn).comp (tSOf.inclusion F hmn hnk) := by
  ext x
  rfl

@[simp] theorem tSOf.inclusion_map_apply {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F (Nat.le_trans hmn hnk)) :
    tSOf.inclusion E hmn hnk
        (tSOf.map hφ (Nat.le_trans hmn hnk) x) =
      tSOf.map hφ hmn (tSOf.inclusion F hmn hnk x) := by
  rfl

@[simp] theorem tSOf.map_id (F : DFilt G)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf.map (preserves_id F) hmn =
      MonoidHom.id (tSOf F hmn) := by
  ext x
  rfl

@[simp] theorem tSOf.map_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf.map (Preserves.comp hφ hψ) hmn =
      (tSOf.map hψ hmn).comp (tSOf.map hφ hmn) := by
  ext x
  rfl


/-- A filtration-preserving equivalence restricts to embedded concrete terms. -/
noncomputable def tSOf.equiv_mul_equiv {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf F hmn ≃* tSOf E hmn where
  toFun := tSOf.map hf hmn
  invFun := tSOf.map hb hmn
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [tSOf.map_coe]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [tSOf.map_coe]
  map_mul' x y := by
    ext
    simp

@[simp] theorem tSOf.equiv_mulequiv_applycoe
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    (((tSOf.equiv_mul_equiv e hf hb hmn x : tSOf E hmn) : E m) : H) =
      e ((x : F m) : G) := rfl

@[simp] theorem tSOf.equivmul_equivsymm_applycoe
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (y : tSOf E hmn) :
    ((((tSOf.equiv_mul_equiv e hf hb hmn).symm y : tSOf F hmn) : F m) : G) =
      e.symm ((y : E m) : H) := rfl

@[simp] theorem tSOf.equiv_mulequiv_monoidhom
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e hf hb hmn).toMonoidHom =
      tSOf.map hf hmn := rfl

@[simp] theorem tSOf.equivmul_equivsymm_monoidhom
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e hf hb hmn).symm.toMonoidHom =
      tSOf.map hb hmn := rfl

@[simp] theorem tSOf.equiv_mul_equivrefl
    (F : DFilt G) {m n : ℕ} (hmn : m ≤ n) :
    tSOf.equiv_mul_equiv (MulEquiv.refl G)
        (preserves_id F) (preserves_id F) hmn =
      MulEquiv.refl (tSOf F hmn) := by
  ext x
  rfl

@[simp] theorem tSOf.equiv_mul_equivsymm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e hf hb hmn).symm =
      tSOf.equiv_mul_equiv e.symm hb hf hmn := by
  ext x
  rfl

@[simp] theorem tSOf.equiv_mul_equivtrans {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} (e : G ≃* H) (f : H ≃* K)
    (he : Preserves F E e.toMonoidHom)
    (he' : Preserves E F e.symm.toMonoidHom)
    (hf : Preserves E D f.toMonoidHom)
    (hf' : Preserves D E f.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e he he' hmn).trans
        (tSOf.equiv_mul_equiv f hf hf' hmn) =
      tSOf.equiv_mul_equiv (e.trans f)
        (Preserves.comp he hf) (Preserves.comp hf' he') hmn := by
  ext x
  rfl

@[simp] theorem tSOf.equivmul_equivsymm_applyself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    (tSOf.equiv_mul_equiv e hf hb hmn).symm
        (tSOf.equiv_mul_equiv e hf hb hmn x) = x :=
  (tSOf.equiv_mul_equiv e hf hb hmn).left_inv x

@[simp] theorem tSOf.equivmul_equivapply_symmself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (y : tSOf E hmn) :
    tSOf.equiv_mul_equiv e hf hb hmn
        ((tSOf.equiv_mul_equiv e hf hb hmn).symm y) = y :=
  (tSOf.equiv_mul_equiv e hf hb hmn).right_inv y

@[simp] theorem tSOf.map_symm_comp
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.map hb hmn).comp (tSOf.map hf hmn) =
      MonoidHom.id (tSOf F hmn) := by
  ext x
  simp [tSOf.map_coe]

@[simp] theorem tSOf.map_comp_symm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.map hf hmn).comp (tSOf.map hb hmn) =
      MonoidHom.id (tSOf E hmn) := by
  ext x
  simp [tSOf.map_coe]

/-- A restricted filtration map sends the range of a nested inclusion into the
corresponding range in the target filtration. -/
theorem tSOf.map_range_inclusionle {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((tSOf.inclusion F hmn hnk).range).map
        (tSOf.map hφ hmn) ≤
      (tSOf.inclusion E hmn hnk).range := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨z, hz⟩
  refine ⟨tSOf.map hφ (Nat.le_trans hmn hnk) z, ?_⟩
  rw [← hz]
  exact (tSOf.inclusion_map_apply hφ hmn hnk z).symm


/-- A filtration-preserving equivalence carries the range of a nested inclusion onto the
corresponding range. -/
theorem tSOf.map_rangeinclusion_eqequiv {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((tSOf.inclusion F hmn hnk).range).map
        (tSOf.map hf hmn) =
      (tSOf.inclusion E hmn hnk).range := by
  apply le_antisymm
  · exact tSOf.map_range_inclusionle hf hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    refine ⟨tSOf.inclusion F hmn hnk
        (tSOf.map hb (Nat.le_trans hmn hnk) z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · rw [tSOf.inclusion_map_apply hb hmn hnk]
      apply Subtype.ext
      apply Subtype.ext
      simp [tSOf.map_coe]

/-- The same range-transport statement phrased through the restricted equivalence. -/
theorem tSOf.equiv_map_rangeinclusion
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((tSOf.inclusion F hmn hnk).range).map
        (tSOf.equiv_mul_equiv e hf hb hmn).toMonoidHom =
      (tSOf.inclusion E hmn hnk).range := by
  simpa [tSOf.equiv_mulequiv_monoidhom] using
    tSOf.map_rangeinclusion_eqequiv e hf hb hmn hnk

/-- A filtration-preserving homomorphism induces a map on quotients of an intermediate
concrete term by the range of a deeper-term inclusion. -/
noncomputable def tSOf.inclusion_range_quotmap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) →*
      (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) := by
  letI := tSOf.inclusion_range_normal F hmn hnk
  letI := tSOf.inclusion_range_normal E hmn hnk
  exact QuotientGroup.map _ _ (tSOf.map hφ hmn)
    ((Subgroup.map_le_iff_le_comap).1 (tSOf.map_range_inclusionle hφ hmn hnk))

@[simp] theorem tSOf.inclusion_rangequot_mapmk
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (hφ : Preserves F E φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F hmn) :
    tSOf.inclusion_range_quotmap hφ hmn hnk
        (QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x) =
      QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range
        (tSOf.map hφ hmn x) := by
  rfl

@[simp] theorem tSOf.inclusion_rangequot_mapid
    (F : DFilt G) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf.inclusion_range_quotmap (preserves_id F) hmn hnk =
      MonoidHom.id (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem tSOf.inclusion_rangequot_mapcomp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf.inclusion_range_quotmap (Preserves.comp hφ hψ) hmn hnk =
      (tSOf.inclusion_range_quotmap hψ hmn hnk).comp
        (tSOf.inclusion_range_quotmap hφ hmn hnk) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl


/-- A filtration-preserving equivalence induces an equivalence on quotients by nested
inclusion ranges. -/
noncomputable def tSOf.inclusionrange_quotequiv_mulequiv
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) ≃*
      (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) where
  toFun := tSOf.inclusion_range_quotmap hf hmn hnk
  invFun := tSOf.inclusion_range_quotmap hb hmn hnk
  left_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range
        (tSOf.map hb hmn (tSOf.map hf hmn x)) =
      QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp [tSOf.map_coe]
  right_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro y
    change QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range
        (tSOf.map hf hmn (tSOf.map hb hmn y)) =
      QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range y
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp [tSOf.map_coe]
  map_mul' q r := by
    exact map_mul (tSOf.inclusion_range_quotmap hf hmn hnk) q r

@[simp] theorem tSOf.inclusionrange_quotequiv_mulequivmk
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (x : tSOf F hmn) :
    tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk
        (QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x) =
      QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range
        (tSOf.map hf hmn x) := rfl

@[simp] theorem tSOf.inclusionrange_quotequivmul_equivsymmmk
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (y : tSOf E hmn) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm
        (QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range y) =
      QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range
        (tSOf.map hb hmn y) := rfl

@[simp] theorem tSOf.inclus_quote_equiv
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).toMonoidHom =
      tSOf.inclusion_range_quotmap hf hmn hnk := rfl

@[simp] theorem tSOf.inclrangquot_equivmulequiv_symmmonoidhom
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm.toMonoidHom =
      tSOf.inclusion_range_quotmap hb hmn hnk := rfl

@[simp] theorem tSOf.inclusionrange_quotequiv_mulequivrefl
    (F : DFilt G) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf.inclusionrange_quotequiv_mulequiv (MulEquiv.refl G)
        (preserves_id F) (preserves_id F) hmn hnk =
      MulEquiv.refl
        (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem tSOf.inclusionrange_quotequiv_mulequivsymm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm =
      tSOf.inclusionrange_quotequiv_mulequiv e.symm hb hf hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem tSOf.inclusionrange_quotequiv_mulequivtrans
    {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} (e : G ≃* H) (f : H ≃* K)
    (he : Preserves F E e.toMonoidHom)
    (he' : Preserves E F e.symm.toMonoidHom)
    (hf : Preserves E D f.toMonoidHom)
    (hf' : Preserves D E f.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e he he' hmn hnk).trans
        (tSOf.inclusionrange_quotequiv_mulequiv f hf hf' hmn hnk) =
      tSOf.inclusionrange_quotequiv_mulequiv (e.trans f)
        (Preserves.comp he hf) (Preserves.comp hf' he') hmn hnk := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem tSOf.inclrangquot_equivmulequiv_symmapplyself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm
        (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk q) = q :=
  (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).left_inv q

@[simp] theorem tSOf.inclrangquot_equivmulequiv_applysymmself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) :
    tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk
        ((tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm q) = q :=
  (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).right_inv q

@[simp] theorem tSOf.inclus_quotm_symmc
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion_range_quotmap hb hmn hnk).comp
        (tSOf.inclusion_range_quotmap hf hmn hnk) =
      MonoidHom.id
        (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) := by
  ext x
  change QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range
      (tSOf.map hb hmn (tSOf.map hf hmn x)) =
    QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp [tSOf.map_coe]

@[simp] theorem tSOf.inclus_quotm_comps
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion_range_quotmap hf hmn hnk).comp
        (tSOf.inclusion_range_quotmap hb hmn hnk) =
      MonoidHom.id
        (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) := by
  ext x
  change QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range
      (tSOf.map hf hmn (tSOf.map hb hmn x)) =
    QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range x
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp [tSOf.map_coe]

@[simp] theorem termMap_id (F : DFilt G) (n : ℕ) :
    termMap (preserves_id F) n = MonoidHom.id (F n) := by
  ext x
  rfl

@[simp] theorem termMap_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K} (hφ : Preserves F E φ) (hψ : Preserves E D ψ)
    (n : ℕ) :
    termMap (Preserves.comp hφ hψ) n = (termMap hψ n).comp (termMap hφ n) := by
  ext x
  rfl

/-- A preserving homomorphism induces maps on arbitrary concrete term quotients
`F_m/F_n → E_m/E_n` for `m ≤ n`. -/
noncomputable def termQuotient {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n) :
    (F m ⧸ tSOf F h) →* (E m ⧸ tSOf E h) :=
  QuotientGroup.map (tSOf F h) (tSOf E h) (termMap hφ m) (by
    intro x hx
    rw [mem_term_of] at hx
    change termMap hφ m x ∈ tSOf E h
    rw [mem_term_of]
    rw [termMap_coe]
    exact hφ n ⟨(x : G), hx, rfl⟩)

@[simp] theorem term_quotient_mk {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n) (x : F m) :
    termQuotient hφ h (QuotientGroup.mk' (tSOf F h) x) =
      QuotientGroup.mk' (tSOf E h) (termMap hφ m x) := rfl

@[simp] theorem term_quotient_id (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) :
    termQuotient (preserves_id F) h =
      MonoidHom.id (F m ⧸ tSOf F h) := by
  ext x
  rfl

@[simp] theorem term_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ)
    {m n : ℕ} (h : m ≤ n) :
    termQuotient (Preserves.comp hφ hψ) h =
      (termQuotient hψ h).comp (termQuotient hφ h) := by
  ext x
  rfl


/-- A filtration-preserving equivalence induces an equivalence on arbitrary concrete
term quotients `F_m/F_n`. -/
noncomputable def termQuotientMul {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (F m ⧸ tSOf F h) ≃* (E m ⧸ tSOf E h) where
  toFun := termQuotient hf h
  invFun := termQuotient hb h
  left_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (tSOf F h)
        (termMap hb m (termMap hf m x)) = QuotientGroup.mk' (tSOf F h) x
    congr 1
    apply Subtype.ext
    simp [termMap_coe]
  right_inv q := by
    refine QuotientGroup.induction_on q ?_
    intro y
    change QuotientGroup.mk' (tSOf E h)
        (termMap hf m (termMap hb m y)) = QuotientGroup.mk' (tSOf E h) y
    congr 1
    apply Subtype.ext
    simp [termMap_coe]
  map_mul' q r := by
    exact map_mul (termQuotient hf h) q r

@[simp] theorem term_mul_mk {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (x : F m) :
    termQuotientMul e hf hb h (QuotientGroup.mk' (tSOf F h) x) =
      QuotientGroup.mk' (tSOf E h) (termMap hf m x) := rfl

@[simp] theorem term_symm_mk {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (y : E m) :
    (termQuotientMul e hf hb h).symm
        (QuotientGroup.mk' (tSOf E h) y) =
      QuotientGroup.mk' (tSOf F h) (termMap hb m y) := rfl

@[simp] theorem term_mul_monoid {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e hf hb h).toMonoidHom = termQuotient hf h := rfl

@[simp] theorem term_symm_monoid
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e hf hb h).symm.toMonoidHom =
      termQuotient hb h := rfl

@[simp] theorem term_mul_refl
    (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    termQuotientMul (MulEquiv.refl G)
        (preserves_id F) (preserves_id F) h =
      MulEquiv.refl (F m ⧸ tSOf F h) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem term_mul_symm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e hf hb h).symm =
      termQuotientMul e.symm hb hf h := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem term_mul_trans {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} (e : G ≃* H) (f : H ≃* K)
    (he : Preserves F E e.toMonoidHom)
    (he' : Preserves E F e.symm.toMonoidHom)
    (hf : Preserves E D f.toMonoidHom)
    (hf' : Preserves D E f.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e he he' h).trans
        (termQuotientMul f hf hf' h) =
      termQuotientMul (e.trans f)
        (Preserves.comp he hf) (Preserves.comp hf' he') h := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem term_mul_self
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (q : F m ⧸ tSOf F h) :
    (termQuotientMul e hf hb h).symm
        (termQuotientMul e hf hb h q) = q :=
  (termQuotientMul e hf hb h).left_inv q

@[simp] theorem mul_symm_self
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (q : E m ⧸ tSOf E h) :
    termQuotientMul e hf hb h
        ((termQuotientMul e hf hb h).symm q) = q :=
  (termQuotientMul e hf hb h).right_inv q

@[simp] theorem term_symm_comp
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotient hb h).comp (termQuotient hf h) =
      MonoidHom.id (F m ⧸ tSOf F h) := by
  ext x
  change QuotientGroup.mk' (tSOf F h)
      (termMap hb m (termMap hf m x)) =
    QuotientGroup.mk' (tSOf F h) x
  congr 1
  apply Subtype.ext
  simp [termMap_coe]

@[simp] theorem quotient_comp_symm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotient hf h).comp (termQuotient hb h) =
      MonoidHom.id (E m ⧸ tSOf E h) := by
  ext x
  change QuotientGroup.mk' (tSOf E h)
      (termMap hf m (termMap hb m x)) =
    QuotientGroup.mk' (tSOf E h) x
  congr 1
  apply Subtype.ext
  simp [termMap_coe]

/-- The map induced on kernels of arbitrary quotient transitions by a filtration map. -/
noncomputable def transitionKernelMap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n) :
    MonoidHom.ker (quotientTransition F h) →*
      MonoidHom.ker (quotientTransition E h) where
  toFun y := ⟨quotientMap hφ n y, by
    rw [MonoidHom.mem_ker]
    have hy : quotientTransition F h (y : G ⧸ F n) = 1 :=
      (MonoidHom.mem_ker).1 y.property
    have hs := congrArg
      (fun f : (G ⧸ F n) →* (H ⧸ E m) => f (y : G ⧸ F n))
      (quotientTransition_naturality (F := F) (E := E) (φ := φ) hφ h)
    change quotientTransition E h (quotientMap hφ n (y : G ⧸ F n)) = 1
    calc
      quotientTransition E h (quotientMap hφ n (y : G ⧸ F n)) =
          quotientMap hφ m (quotientTransition F h (y : G ⧸ F n)) := by
        simpa [MonoidHom.comp_apply] using hs
      _ = quotientMap hφ m 1 := by rw [hy]
      _ = 1 := map_one _⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem transition_coe {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n) (y : MonoidHom.ker (quotientTransition F h)) :
    ((transitionKernelMap hφ h y : MonoidHom.ker (quotientTransition E h)) :
        H ⧸ E n) =
      quotientMap hφ n (y : G ⧸ F n) := rfl

@[simp] theorem transition_kernel_id (F : DFilt G)
    {m n : ℕ} (h : m ≤ n) :
  transitionKernelMap (preserves_id F) h =
      MonoidHom.id (MonoidHom.ker (quotientTransition F h)) := by
  ext y
  rw [transition_coe]
  simp

@[simp] theorem kernel_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ)
    {m n : ℕ} (h : m ≤ n) :
    transitionKernelMap (Preserves.comp hφ hψ) h =
      (transitionKernelMap hψ h).comp (transitionKernelMap hφ h) := by
  ext y
  rw [transition_coe]
  rw [MonoidHom.comp_apply, transition_coe, transition_coe]
  rw [quotientMap_comp (hφ := hφ) (hψ := hψ)]
  rfl

/-- Naturality of the arbitrary transition-kernel quotient equivalence. -/
theorem transition_kernel_naturality {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    {m n : ℕ} (h : m ≤ n)
    (q : F m ⧸ tSOf F h) :
    transitionKernelMap hφ h (transitionKernelEquiv F h q) =
      transitionKernelEquiv E h (termQuotient hφ h q) := by
  refine QuotientGroup.induction_on q ?_
  intro x
  ext
  rw [transition_coe]
  change quotientMap hφ n
      (((transitionKernelEquiv F h
          (QuotientGroup.mk' (tSOf F h) x) :
          MonoidHom.ker (quotientTransition F h)) : G ⧸ F n)) =
    ((transitionKernelEquiv E h
        (termQuotient hφ h
          (QuotientGroup.mk' (tSOf F h) x)) :
        MonoidHom.ker (quotientTransition E h)) : H ⧸ E n)
  rw [transition_kernel_coe]
  rw [term_quotient_mk]
  rw [transition_kernel_coe]
  rfl

/-- An injective underlying homomorphism restricts injectively to each term. -/
theorem term_map_of {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Injective (termMap hφ n) := by
  intro x y hxy
  ext
  apply hinj
  exact congrArg (fun z : E n => (z : H)) hxy

/-- If a filtration map is termwise onto, its restriction to each term is surjective. -/
theorem term_surjective_maps {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    Function.Surjective (termMap (MapsOnto.preserves honto) n) := by
  intro y
  have hy : (y : H) ∈ E n := y.property
  have himg : (y : H) ∈ (F n).map φ := by simp [honto n] at hy ⊢
  rcases himg with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  ext
  exact hxy

/-- Range form of termwise surjectivity for a `MapsOnto` filtration map. -/
theorem term_range_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    (termMap (MapsOnto.preserves honto) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (term_surjective_maps honto n)

/-- Termwise-onto filtration maps with injective underlying homomorphism induce
injections on arbitrary term quotients. -/
theorem term_injective_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Injective (termQuotient (MapsOnto.preserves honto) h) := by
  intro q r hqr
  apply eq_of_mul_inv_eq_one
  refine QuotientGroup.induction_on q ?_ r hqr
  intro x r hx
  refine QuotientGroup.induction_on r ?_ hx
  intro y hy
  change termQuotient (MapsOnto.preserves honto) h
      (QuotientGroup.mk' (tSOf F h) x) =
    termQuotient (MapsOnto.preserves honto) h
      (QuotientGroup.mk' (tSOf F h) y) at hy
  rw [term_quotient_mk, term_quotient_mk] at hy
  have hone : QuotientGroup.mk' (tSOf E h)
      (termMap (MapsOnto.preserves honto) m (x * y⁻¹)) = 1 := by
    have hc := congrArg (fun z => z * (QuotientGroup.mk' (tSOf E h)
      (termMap (MapsOnto.preserves honto) m y))⁻¹) hy
    simpa [map_mul, map_inv] using hc
  have hmemE : (termMap (MapsOnto.preserves honto) m (x * y⁻¹) : H) ∈ E n := by
    have hsub := (QuotientGroup.eq_one_iff
      (termMap (MapsOnto.preserves honto) m (x * y⁻¹))).1 hone
    exact (mem_term_of E h _).1 hsub
  have hpre : ((x * y⁻¹ : F m) : G) ∈ F n := by
    have hmap : φ ((x * y⁻¹ : F m) : G) ∈ (F n).map φ := by
      simpa [honto n] using hmemE
    rcases hmap with ⟨z, hz, hzeq⟩
    have hzval : (z : G) = ((x * y⁻¹ : F m) : G) := hinj hzeq
    simpa [← hzval] using hz
  apply (QuotientGroup.eq_one_iff (x * y⁻¹)).2
  exact (mem_term_of F h _).2 hpre

/-- Termwise-onto filtration maps whose ordinary kernel is contained in the deeper
source term induce injections on the corresponding term quotient. -/
theorem term_injective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    Function.Injective (termQuotient (MapsOnto.preserves honto) h) := by
  intro q r hqr
  apply eq_of_mul_inv_eq_one
  refine QuotientGroup.induction_on q ?_ r hqr
  intro x r hx
  refine QuotientGroup.induction_on r ?_ hx
  intro y hy
  change termQuotient (MapsOnto.preserves honto) h
      (QuotientGroup.mk' (tSOf F h) x) =
    termQuotient (MapsOnto.preserves honto) h
      (QuotientGroup.mk' (tSOf F h) y) at hy
  rw [term_quotient_mk, term_quotient_mk] at hy
  have hone : QuotientGroup.mk' (tSOf E h)
      (termMap (MapsOnto.preserves honto) m (x * y⁻¹)) = 1 := by
    have hc := congrArg (fun z => z * (QuotientGroup.mk' (tSOf E h)
      (termMap (MapsOnto.preserves honto) m y))⁻¹) hy
    simpa [map_mul, map_inv] using hc
  have hmemE : (termMap (MapsOnto.preserves honto) m (x * y⁻¹) : H) ∈ E n := by
    have hsub := (QuotientGroup.eq_one_iff
      (termMap (MapsOnto.preserves honto) m (x * y⁻¹))).1 hone
    exact (mem_term_of E h _).1 hsub
  have hpre : ((x * y⁻¹ : F m) : G) ∈ F n := by
    have hc : ((x * y⁻¹ : F m) : G) ∈ (E n).comap φ := by
      change φ ((x * y⁻¹ : F m) : G) ∈ E n
      simpa using hmemE
    have heq : (E n).comap φ = F n :=
      (MapsOnto.comap_eqiff_kerle honto n).2 hker
    simpa [heq] using hc
  apply (QuotientGroup.eq_one_iff (x * y⁻¹)).2
  exact (mem_term_of F h _).2 hpre

/-- Termwise-surjective filtration maps induce surjections on arbitrary term quotients. -/
theorem term_surjective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Surjective
      (termQuotient (MapsOnto.preserves honto) h) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  rcases term_surjective_maps honto m y with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk' (tSOf F h) x, ?_⟩
  rw [term_quotient_mk, hx]
  rfl

/-- Range form of surjectivity for concrete term quotient maps. -/
theorem term_top_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotient (MapsOnto.preserves honto) h).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (term_surjective_onto honto h)

/-- Termwise-onto filtration maps whose ordinary kernel is contained in the deeper
source term induce bijections on the corresponding term quotient. -/
theorem term_bijective_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    Function.Bijective (termQuotient (MapsOnto.preserves honto) h) :=
  ⟨term_injective_ker honto h hker,
    term_surjective_onto honto h⟩

/-- If the kernel is contained in a still deeper term, the induced map on an earlier
term quotient is bijective. -/
theorem term_bijective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    Function.Bijective (termQuotient (MapsOnto.preserves honto) h) :=
  term_bijective_maps honto h
    (honto.ker_le_lea hker hnk)

/-- Equivalence on a term quotient induced by a termwise-onto map whose ordinary
kernel is contained in the deeper source term. -/
noncomputable def termMapsOnto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    (F m ⧸ tSOf F h) ≃* (E m ⧸ tSOf E h) :=
  MulEquiv.ofBijective (termQuotient (MapsOnto.preserves honto) h)
    (term_bijective_maps honto h hker)

@[simp] theorem term_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (x : F m ⧸ tSOf F h) :
    termMapsOnto honto h hker x =
      termQuotient (MapsOnto.preserves honto) h x := rfl

@[simp] theorem term_onto_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    (termMapsOnto honto h hker).toMonoidHom =
      termQuotient (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for term quotient equivalences from termwise-onto maps
with kernel contained in the deeper source term. -/
theorem term_equiv_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (y : E m ⧸ tSOf E h)
    (x : F m ⧸ tSOf F h) :
    (termMapsOnto honto h hker).symm y = x ↔
      y = termQuotient (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on earlier arbitrary
term quotients. -/
noncomputable def termMapsKer
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    (F m ⧸ tSOf F h) ≃* (E m ⧸ tSOf E h) :=
  termMapsOnto honto h (honto.ker_le_lea hker hnk)

@[simp] theorem term_equiv_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) (x : F m ⧸ tSOf F h) :
    termMapsKer honto h hker hnk x =
      termQuotient (MapsOnto.preserves honto) h x := rfl

@[simp] theorem term_monoid_hom
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    (termMapsKer honto h hker hnk).toMonoidHom =
      termQuotient (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for monotone-kernel term quotient equivalences. -/
theorem equiv_maps_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) (y : E m ⧸ tSOf E h)
    (x : F m ⧸ tSOf F h) :
    (termMapsKer honto h hker hnk).symm y = x ↔
      y = termQuotient (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Termwise-onto filtration maps with injective underlying homomorphism induce
bijections on arbitrary term quotients. -/
theorem term_bijective_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Bijective (termQuotient (MapsOnto.preserves honto) h) :=
  ⟨term_injective_onto honto hinj h,
    term_surjective_onto honto h⟩


/-- Equivalence on arbitrary term quotients induced by a termwise-onto injective
filtration map. -/
noncomputable def termMapsInjective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    (F m ⧸ tSOf F h) ≃* (E m ⧸ tSOf E h) :=
  MulEquiv.ofBijective (termQuotient (MapsOnto.preserves honto) h)
    (term_bijective_injective honto hinj h)

@[simp] theorem maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x : F m ⧸ tSOf F h) :
    termMapsInjective honto hinj h x =
      termQuotient (MapsOnto.preserves honto) h x := rfl

@[simp] theorem term_injective_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n) :
    (termMapsInjective honto hinj h).toMonoidHom =
      termQuotient (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for the term-quotient equivalence from a termwise-onto
injective filtration map. -/
theorem equiv_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n)
    (y : E m ⧸ tSOf E h) (x : F m ⧸ tSOf F h) :
    (termMapsInjective honto hinj h).symm y = x ↔
      y = termQuotient (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Termwise-onto filtration maps with injective underlying homomorphism induce
injections on arbitrary transition kernels. -/
theorem transition_injective_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Injective (transitionKernelMap (MapsOnto.preserves honto) h) := by
  intro x y hxy
  let qx := (transitionKernelEquiv F h).symm x
  let qy := (transitionKernelEquiv F h).symm y
  have hqmap : termQuotient (MapsOnto.preserves honto) h qx =
      termQuotient (MapsOnto.preserves honto) h qy := by
    apply (transitionKernelEquiv E h).injective
    rw [← transition_kernel_naturality (MapsOnto.preserves honto) h qx,
      ← transition_kernel_naturality (MapsOnto.preserves honto) h qy]
    dsimp [qx, qy]
    simpa using hxy
  have hq := term_injective_onto honto hinj h hqmap
  calc
    x = transitionKernelEquiv F h qx := by dsimp [qx]; simp
    _ = transitionKernelEquiv F h qy := by rw [hq]
    _ = y := by dsimp [qy]; simp

/-- Termwise-surjective filtration maps induce surjections on arbitrary transition kernels. -/
theorem transition_surjective_maps {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Surjective
      (transitionKernelMap (MapsOnto.preserves honto) h) := by
  intro y
  let qE := (transitionKernelEquiv E h).symm y
  rcases term_surjective_onto honto h qE with ⟨qF, hqF⟩
  refine ⟨transitionKernelEquiv F h qF, ?_⟩
  rw [transition_kernel_naturality]
  rw [hqF]
  exact MulEquiv.apply_symm_apply (transitionKernelEquiv E h) y

/-- Range form of surjectivity for transition-kernel maps. -/
theorem transition_top_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n : ℕ} (h : m ≤ n) :
    (transitionKernelMap (MapsOnto.preserves honto) h).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (transition_surjective_maps honto h)

/-- Termwise-onto filtration maps whose ordinary kernel is contained in the deeper
source term induce injections on the corresponding transition kernels. -/
theorem transition_injective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    Function.Injective (transitionKernelMap (MapsOnto.preserves honto) h) := by
  intro x y hxy
  let qx := (transitionKernelEquiv F h).symm x
  let qy := (transitionKernelEquiv F h).symm y
  have hqmap : termQuotient (MapsOnto.preserves honto) h qx =
      termQuotient (MapsOnto.preserves honto) h qy := by
    apply (transitionKernelEquiv E h).injective
    rw [← transition_kernel_naturality (MapsOnto.preserves honto) h qx,
      ← transition_kernel_naturality (MapsOnto.preserves honto) h qy]
    dsimp [qx, qy]
    simpa using hxy
  have hq := term_injective_ker honto h hker hqmap
  calc
    x = transitionKernelEquiv F h qx := by dsimp [qx]; simp
    _ = transitionKernelEquiv F h qy := by rw [hq]
    _ = y := by dsimp [qy]; simp

/-- Termwise-onto filtration maps whose ordinary kernel is contained in the deeper
source term induce bijections on the corresponding transition kernels. -/
theorem transition_kernel_bijective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    Function.Bijective (transitionKernelMap (MapsOnto.preserves honto) h) :=
  ⟨transition_injective_ker honto h hker,
    transition_surjective_maps honto h⟩

/-- If the kernel is contained in a still deeper term, the induced map on an earlier
transition kernel is bijective. -/
theorem transition_bijective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    Function.Bijective (transitionKernelMap (MapsOnto.preserves honto) h) :=
  transition_kernel_bijective honto h
    (honto.ker_le_lea hker hnk)

/-- Equivalence on transition kernels induced by a termwise-onto map whose ordinary
kernel is contained in the deeper source term. -/
noncomputable def transitionMapsOnto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    MonoidHom.ker (quotientTransition F h) ≃*
      MonoidHom.ker (quotientTransition E h) :=
  MulEquiv.ofBijective (transitionKernelMap (MapsOnto.preserves honto) h)
    (transition_kernel_bijective honto h hker)

@[simp] theorem kernel_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (x : MonoidHom.ker (quotientTransition F h)) :
    transitionMapsOnto honto h hker x =
      transitionKernelMap (MapsOnto.preserves honto) h x := rfl

@[simp] theorem transition_maps_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) :
    (transitionMapsOnto honto h hker).toMonoidHom =
      transitionKernelMap (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for transition-kernel equivalences from termwise-onto maps
with kernel contained in the deeper source term. -/
theorem transition_equiv_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (y : MonoidHom.ker (quotientTransition E h))
    (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionMapsOnto honto h hker).symm y = x ↔
      y = transitionKernelMap (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on earlier transition
kernels. -/
noncomputable def transitionOntoKer
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    MonoidHom.ker (quotientTransition F h) ≃*
      MonoidHom.ker (quotientTransition E h) :=
  transitionMapsOnto honto h (honto.ker_le_lea hker hnk)

@[simp] theorem kernel_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoKer honto h hker hnk x =
      transitionKernelMap (MapsOnto.preserves honto) h x := rfl

@[simp] theorem transition_onto_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) :
    (transitionOntoKer honto h hker hnk).toMonoidHom =
      transitionKernelMap (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for monotone-kernel transition-kernel equivalences. -/
theorem kernel_onto_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (y : MonoidHom.ker (quotientTransition E h))
    (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionOntoKer honto h hker hnk).symm y = x ↔
      y = transitionKernelMap (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Termwise-onto filtration maps with injective underlying homomorphism induce
bijections on arbitrary transition kernels. -/
theorem kernel_bijective_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    Function.Bijective (transitionKernelMap (MapsOnto.preserves honto) h) :=
  ⟨transition_injective_onto honto hinj h,
    transition_surjective_maps honto h⟩


/-- Equivalence on arbitrary transition kernels induced by a termwise-onto
injective filtration map. -/
noncomputable def transitionOntoInjective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) :
    MonoidHom.ker (quotientTransition F h) ≃*
      MonoidHom.ker (quotientTransition E h) :=
  MulEquiv.ofBijective (transitionKernelMap (MapsOnto.preserves honto) h)
    (kernel_bijective_injective honto hinj h)

@[simp] theorem kernel_equiv_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoInjective honto hinj h x =
      transitionKernelMap (MapsOnto.preserves honto) h x := rfl

@[simp] theorem transition_injective_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n) :
    (transitionOntoInjective honto hinj h).toMonoidHom =
      transitionKernelMap (MapsOnto.preserves honto) h := rfl

/-- Inverse-characterization for the transition-kernel equivalence from a
termwise-onto injective filtration map. -/
theorem kernel_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n)
    (y : MonoidHom.ker (quotientTransition E h))
    (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionOntoInjective honto hinj h).symm y = x ↔
      y = transitionKernelMap (MapsOnto.preserves honto) h x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Bijectivity of term restrictions from termwise surjectivity and injectivity downstairs. -/
theorem term_bijective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (termMap (MapsOnto.preserves honto) n) :=
  ⟨term_map_of (MapsOnto.preserves honto) hinj n,
    term_surjective_maps honto n⟩


/-- Equivalence between corresponding filtration terms induced by a termwise-onto
injective map.  This is often the most convenient way to transport elements before
passing to quotients. -/
noncomputable def termEquivInjective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) : F n ≃* E n :=
  MulEquiv.ofBijective (termMap (MapsOnto.preserves honto) n)
    (term_bijective_onto honto hinj n)

@[simp] theorem term_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : F n) :
    termEquivInjective honto hinj n x =
      termMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem term_maps_monoid {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (termEquivInjective honto hinj n).toMonoidHom =
      termMap (MapsOnto.preserves honto) n := rfl


@[simp] theorem term_injective_coe {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : F n) :
    ((termEquivInjective honto hinj n x : E n) : H) = φ (x : G) := rfl

/-- The inverse of the restricted term equivalence is a genuine preimage under `φ`. -/
theorem term_symm_coe {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (y : E n) :
    φ (((termEquivInjective honto hinj n).symm y : F n) : G) = (y : H) := by
  have h := (termEquivInjective honto hinj n).apply_symm_apply y
  exact congrArg (fun z : E n => (z : H)) h

/-- Inverse-characterization for the term equivalence from a termwise-onto injective map. -/
theorem maps_symm {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (y : E n) (x : F n) :
    (termEquivInjective honto hinj n).symm y = x ↔
      y = termMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl



@[simp] theorem term_equiv_id (F : DFilt G)
    (n : ℕ) :
    termEquivInjective (mapsOnto_id F) (fun _ _ h => h) n =
      MulEquiv.refl (F n) := by
  ext x
  rfl

/-- Term equivalences for termwise-onto injective maps compose as expected. -/
theorem term_injective_trans {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    (termEquivInjective hφ hinjφ n).trans
        (termEquivInjective hψ hinjψ n) =
      termEquivInjective (hφ.comp hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) n := by
  ext x
  rfl

/-- A group equivalence preserving filtrations in both directions restricts to an
 equivalence on each term. -/
noncomputable def termEquivMul {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    (n : ℕ) : F n ≃* E n :=
  termEquivInjective (MapsOnto.of_equiv e hf hb) e.injective n


@[simp] theorem term_equiv_refl (F : DFilt G) (n : ℕ) :
    termEquivMul (MulEquiv.refl G) (preserves_id F) (preserves_id F) n =
      MulEquiv.refl (F n) := by
  ext x
  rfl

/-- Restricting a composite filtration-preserving equivalence agrees with composing
restricted term equivalences. -/
theorem term_equiv_trans {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    (e : G ≃* H) (f : H ≃* K)
    (hef : Preserves F E e.toMonoidHom) (heb : Preserves E F e.symm.toMonoidHom)
    (hff : Preserves E D f.toMonoidHom) (hfb : Preserves D E f.symm.toMonoidHom)
    (n : ℕ) :
    (termEquivMul e hef heb n).trans (termEquivMul f hff hfb n) =
      termEquivMul (e.trans f) (Preserves.comp hef hff)
        (by
          -- `(e.trans f).symm` is `e.symm` after `f.symm`.
          simpa using (Preserves.comp hfb heb)) n := by
  ext x
  rfl

@[simp] theorem term_mul_coe {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    (n : ℕ) (x : F n) :
    ((termEquivMul e hf hb n x : E n) : H) = e (x : G) := rfl

@[simp] theorem mul_symm_coe {F : DFilt G}
    {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    (n : ℕ) (y : E n) :
    (((termEquivMul e hf hb n).symm y : F n) : G) = e.symm (y : H) := by
  -- Both sides are the unique preimage under the injective restricted map.
  apply e.injective
  rw [e.apply_symm_apply]
  have h := (termEquivMul e hf hb n).apply_symm_apply y
  change termEquivMul e hf hb n ((termEquivMul e hf hb n).symm y) = y at h
  exact congrArg (fun z : E n => (z : H)) h

/-- The map induced on concrete consecutive-term quotients `Fₙ/Fₙ₊₁`. -/
noncomputable def nextTermQuotient {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    (F n ⧸ nextTermSubgroup F n) →* (E n ⧸ nextTermSubgroup E n) :=
  QuotientGroup.map (nextTermSubgroup F n) (nextTermSubgroup E n) (termMap hφ n) (by
    intro x hx
    rw [next_term_subgroup] at hx
    change termMap hφ n x ∈ nextTermSubgroup E n
    rw [next_term_subgroup]
    exact hφ (n + 1) ⟨(x : G), hx, rfl⟩)

@[simp] theorem next_quotient_mk {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (x : F n) :
    nextTermQuotient hφ n (QuotientGroup.mk' (nextTermSubgroup F n) x) =
      QuotientGroup.mk' (nextTermSubgroup E n) (termMap hφ n x) := rfl

/-- Kernel membership for a represented element of a consecutive-term quotient map. -/
@[simp] theorem ker_next_mk {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (x : F n) :
    QuotientGroup.mk' (nextTermSubgroup F n) x ∈
        MonoidHom.ker (nextTermQuotient hφ n) ↔
      φ (x : G) ∈ E (n + 1) := by
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk' (nextTermSubgroup E n) (termMap hφ n x) = 1 ↔ _
  constructor
  · intro h
    have hm := (QuotientGroup.eq_one_iff (termMap hφ n x)).1 h
    exact (next_term_subgroup E n (termMap hφ n x)).1 hm
  · intro hx
    apply (QuotientGroup.eq_one_iff (termMap hφ n x)).2
    exact (next_term_subgroup E n (termMap hφ n x)).2 hx

/-- The kernel of a consecutive-term quotient map is the image of the preimage
subgroup inside the source consecutive quotient. -/
theorem ker_next_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    MonoidHom.ker (nextTermQuotient hφ n) =
      ((nextTermSubgroup E n).comap (termMap hφ n)).map
        (QuotientGroup.mk' (nextTermSubgroup F n)) := by
  ext q
  constructor
  · intro hq
    refine QuotientGroup.induction_on q ?_ hq
    intro x hx
    change nextTermQuotient hφ n
        (QuotientGroup.mk' (nextTermSubgroup F n) x) = 1 at hx
    rw [next_quotient_mk] at hx
    have hxmem : x ∈ (nextTermSubgroup E n).comap (termMap hφ n) :=
      (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n) (termMap hφ n x)).1 hx
    exact ⟨x, hxmem, rfl⟩
  · intro hq
    rcases hq with ⟨x, hx, rfl⟩
    change nextTermQuotient hφ n
        (QuotientGroup.mk' (nextTermSubgroup F n) x) = 1
    rw [next_quotient_mk]
    exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n) (termMap hφ n x)).2 hx


/-- Kernel of a consecutive-term quotient map as a quotient of the exact preimage
subgroup inside the source term. -/
noncomputable def nextTermEquiv {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    ((nextTermSubgroup E n).comap (termMap hφ n)) ⧸
      ((nextTermSubgroup F n).subgroupOf
        ((nextTermSubgroup E n).comap (termMap hφ n))) ≃*
      MonoidHom.ker (nextTermQuotient hφ n) := by
  let C : Subgroup (F n) := (nextTermSubgroup E n).comap (termMap hφ n)
  let N : Subgroup C := (nextTermSubgroup F n).subgroupOf C
  let kmap : C →* MonoidHom.ker (nextTermQuotient hφ n) :=
  { toFun := fun c => ⟨QuotientGroup.mk' (nextTermSubgroup F n) (c : F n), by
      change nextTermQuotient hφ n
        (QuotientGroup.mk' (nextTermSubgroup F n) (c : F n)) = 1
      rw [next_quotient_mk]
      exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n)
        (termMap hφ n (c : F n))).2 c.property⟩
    map_one' := by ext; simp
    map_mul' := by intro a b; ext; simp }
  have hk_surj : Function.Surjective kmap := by
    intro q
    rcases q with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro x hx
    change nextTermQuotient hφ n (QuotientGroup.mk' (nextTermSubgroup F n) x) = 1 at hx
    rw [next_quotient_mk] at hx
    have xc : x ∈ C := (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n)
      (termMap hφ n x)).1 hx
    refine ⟨⟨x, xc⟩, ?_⟩
    ext
    rfl
  have hker : MonoidHom.ker kmap = N := by
    ext c
    constructor
    · intro hc
      have hcval := congrArg Subtype.val hc
      change QuotientGroup.mk' (nextTermSubgroup F n) (c : F n) = 1 at hcval
      exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup F n) (c : F n)).1 hcval
    · intro hc
      ext
      change QuotientGroup.mk' (nextTermSubgroup F n) (c : F n) = 1
      exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup F n) (c : F n)).2 hc
  refine (QuotientGroup.quotientMulEquivOfEq ?_).trans
    (QuotientGroup.quotientKerEquivOfSurjective kmap hk_surj)
  exact hker.symm

@[simp] theorem next_term_mk {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (c : (nextTermSubgroup E n).comap (termMap hφ n)) :
    nextTermEquiv hφ n
        (QuotientGroup.mk'
          ((nextTermSubgroup F n).subgroupOf
            ((nextTermSubgroup E n).comap (termMap hφ n))) c) =
      ⟨QuotientGroup.mk' (nextTermSubgroup F n) (c : F n), by
        change nextTermQuotient hφ n
          (QuotientGroup.mk' (nextTermSubgroup F n) (c : F n)) = 1
        rw [next_quotient_mk]
        exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n)
          (termMap hφ n (c : F n))).2 c.property⟩ := rfl

/-- Characterize the inverse of the kernel equivalence for consecutive-term maps. -/
theorem next_kernel_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (hφ : Preserves F E φ) (n : ℕ)
    (y : MonoidHom.ker (nextTermQuotient hφ n))
    (x : ((nextTermSubgroup E n).comap (termMap hφ n)) ⧸
      ((nextTermSubgroup F n).subgroupOf
        ((nextTermSubgroup E n).comap (termMap hφ n)))) :
    (nextTermEquiv hφ n).symm y = x ↔
      y = nextTermEquiv hφ n x := by
  rw [MulEquiv.symm_apply_eq]


@[simp] theorem next_term_id (F : DFilt G) (n : ℕ) :
    nextTermQuotient (preserves_id F) n =
      MonoidHom.id (F n ⧸ nextTermSubgroup F n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem next_quotient_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ) (n : ℕ) :
    nextTermQuotient (Preserves.comp hφ hψ) n =
      (nextTermQuotient hψ n).comp (nextTermQuotient hφ n) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- A criterion for injectivity on consecutive-term quotients. -/
theorem term_injective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ}
    (hker : (nextTermSubgroup E n).comap (termMap hφ n) ≤ nextTermSubgroup F n) :
    Function.Injective (nextTermQuotient hφ n) := by
  intro a b hab
  refine QuotientGroup.induction_on a ?_ hab
  intro x
  refine QuotientGroup.induction_on b ?_
  intro y hxy
  change QuotientGroup.mk' (nextTermSubgroup E n) (termMap hφ n x) =
    QuotientGroup.mk' (nextTermSubgroup E n) (termMap hφ n y) at hxy
  apply QuotientGroup.eq.mpr
  apply hker
  change termMap hφ n (x⁻¹ * y) ∈ nextTermSubgroup E n
  rw [map_mul, map_inv]
  exact QuotientGroup.eq.mp hxy

/-- Injectivity on consecutive-term quotients is equivalent to the corresponding
preimage condition inside the term subgroups. -/
theorem next_term_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ} :
    Function.Injective (nextTermQuotient hφ n) ↔
      (nextTermSubgroup E n).comap (termMap hφ n) ≤ nextTermSubgroup F n := by
  constructor
  · intro hinj x hx
    have hleft : nextTermQuotient hφ n
        (QuotientGroup.mk' (nextTermSubgroup F n) x) = 1 := by
      rw [next_quotient_mk]
      exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup E n) (termMap hφ n x)).2 hx
    have hmap : nextTermQuotient hφ n
        (QuotientGroup.mk' (nextTermSubgroup F n) x) = nextTermQuotient hφ n 1 := by
      simpa using hleft
    have hq := hinj hmap
    exact (QuotientGroup.eq_one_iff (N := nextTermSubgroup F n) x).1 (by simpa using hq)
  · exact term_injective_comap hφ

/-- For a split epimorphism, the exact preimage condition inside the restricted term
subgroups is equivalent to saying that `ker φ ∩ F n` lies in the next source term. -/
theorem next_comap_inf
    {F : DFilt G} {E : DFilt H}
    {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    (nextTermSubgroup E n).comap (termMap hφ n) ≤ nextTermSubgroup F n ↔
      φ.ker ⊓ F n ≤ F (n + 1) := by
  constructor
  · intro hpre x hx
    rcases (Subgroup.mem_inf.mp hx) with ⟨hxker, hxFn⟩
    let xt : F n := ⟨x, hxFn⟩
    have him : termMap hφ n xt ∈ nextTermSubgroup E n := by
      rw [next_term_subgroup]
      change φ x ∈ E (n + 1)
      have hx1 : φ x = 1 := by simpa using hxker
      rw [hx1]
      exact (E (n + 1)).one_mem
    have hxnext := hpre him
    simpa [xt] using
      (show (xt : G) ∈ F (n + 1) from (next_term_subgroup F n xt).1 hxnext)
  · intro hker x hx
    change termMap hφ n x ∈ nextTermSubgroup E n at hx
    rw [next_term_subgroup] at hx
    rw [next_term_subgroup]
    have hxcomap : (x : G) ∈ (E (n + 1)).comap φ := by
      simpa [termMap_coe] using hx
    have hsplit := comap_sup_ker hφ hσ hright (n + 1)
    have hsup : (x : G) ∈ F (n + 1) ⊔ φ.ker := by
      simpa [hsplit] using hxcomap
    rcases (Subgroup.mem_sup_of_normal_right.mp hsup) with ⟨a, ha, k, hk, hak⟩
    have hkFn : k ∈ F n := by
      have haFn : a ∈ F n := F.mono_membership (Nat.le_succ n) ha
      have hxFn : (x : G) ∈ F n := x.property
      have hprod : a⁻¹ * (x : G) ∈ F n := (F n).mul_mem ((F n).inv_mem haFn) hxFn
      convert hprod using 1
      calc
        k = a⁻¹ * (a * k) := by simp
        _ = a⁻¹ * (x : G) := by rw [hak]
    have hkinf : k ∈ φ.ker ⊓ F n := Subgroup.mem_inf.mpr ⟨hk, hkFn⟩
    have hknext : k ∈ F (n + 1) := hker hkinf
    have hprod : a * k ∈ F (n + 1) := (F (n + 1)).mul_mem ha hknext
    simpa [hak] using hprod

/-- For a split epimorphism, injectivity on consecutive-term quotients is controlled
by the intersection of the kernel with the current source term. -/
theorem next_inf_inverse
    {F : DFilt G} {E : DFilt H}
    {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (nextTermQuotient hφ n) ↔ φ.ker ⊓ F n ≤ F (n + 1) := by
  rw [next_term_comap hφ]
  exact next_comap_inf hφ hσ hright

/-- A term-level preimage criterion for injectivity on consecutive-term quotients. -/
theorem next_injective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ}
    (hpre : (E (n + 1)).comap φ ≤ F (n + 1)) :
    Function.Injective (nextTermQuotient hφ n) := by
  apply term_injective_comap hφ
  intro x hx
  change termMap hφ n x ∈ nextTermSubgroup E n at hx
  rw [next_term_subgroup] at hx ⊢
  apply hpre
  simpa [termMap_coe] using hx

/-- Termwise onto maps induce surjections on consecutive-term quotients. -/
theorem next_surjective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    Function.Surjective (nextTermQuotient (MapsOnto.preserves honto) n) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  rcases term_surjective_maps honto n y with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk' (nextTermSubgroup F n) x, rfl⟩

/-- Range form of surjectivity for consecutive-term quotient maps. -/
theorem next_top_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    (nextTermQuotient (MapsOnto.preserves honto) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (next_surjective_onto honto n)

/-- For a split epimorphism, bijectivity on consecutive-term quotients is controlled
by the intersection of the kernel with the current source term. -/
theorem next_bijective_inf
    {F : DFilt G} {E : DFilt H}
    {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (nextTermQuotient hφ n) ↔ φ.ker ⊓ F n ≤ F (n + 1) := by
  have honto : MapsOnto F E φ := MapsOnto.of_rightInverse hφ hσ hright
  have hsurj : Function.Surjective (nextTermQuotient hφ n) := by
    simpa using (next_surjective_onto honto n)
  constructor
  · intro hb
    exact (next_inf_inverse hφ hσ hright).1 hb.1
  · intro hker
    exact ⟨(next_inf_inverse
      hφ hσ hright).2 hker, hsurj⟩

/-- For termwise-onto maps, bijectivity on consecutive-term quotients is
equivalent to the exact subgroup preimage condition. -/
theorem bijective_comap_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} :
    Function.Bijective (nextTermQuotient (MapsOnto.preserves honto) n) ↔
      (nextTermSubgroup E n).comap (termMap (MapsOnto.preserves honto) n) ≤
        nextTermSubgroup F n := by
  constructor
  · intro hb
    exact (next_term_comap
      (MapsOnto.preserves honto)).1 hb.1
  · intro hpre
    exact ⟨(next_term_comap
      (MapsOnto.preserves honto)).2 hpre,
      next_surjective_onto honto n⟩

/-- Bijectivity on consecutive quotients from termwise surjectivity and a preimage criterion. -/
theorem next_bijective_comap
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ}
    (hpre : (E (n + 1)).comap φ ≤ F (n + 1)) :
    Function.Bijective (nextTermQuotient (MapsOnto.preserves honto) n) :=
  ⟨next_injective_comap (MapsOnto.preserves honto) hpre,
    next_surjective_onto honto n⟩

/-- For a termwise-onto map, kernel containment in the next source term gives
bijectivity on the consecutive-term quotient. -/
theorem next_bijective_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1)) :
    Function.Bijective (nextTermQuotient (MapsOnto.preserves honto) n) := by
  apply next_bijective_comap honto
  exact le_of_eq ((MapsOnto.comap_eqiff_kerle honto (n + 1)).2 hker)

/-- A deeper kernel-containment hypothesis gives bijectivity on earlier consecutive
term quotients. -/
theorem next_bijective_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    Function.Bijective (nextTermQuotient (MapsOnto.preserves honto) n) :=
  next_bijective_maps honto
    (honto.ker_le_lea hker hnk)

/-- Termwise-onto injective maps induce bijections on consecutive-term quotients. -/
theorem next_bijective_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (nextTermQuotient (MapsOnto.preserves honto) n) :=
  next_bijective_comap honto
    (honto.comap_le_inj hinj (n + 1))

/-- Equivalence on consecutive-term quotients induced by a termwise-onto injective map. -/
noncomputable def nextOntoInjective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ) :
    (F n ⧸ nextTermSubgroup F n) ≃* (E n ⧸ nextTermSubgroup E n) :=
  MulEquiv.ofBijective (nextTermQuotient (MapsOnto.preserves honto) n)
    (next_bijective_injective honto hinj n)

@[simp] theorem next_term_quotient
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoInjective honto hinj n x =
      nextTermQuotient (MapsOnto.preserves honto) n x := rfl

@[simp] theorem next_injective_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ) :
    (nextOntoInjective honto hinj n).toMonoidHom =
      nextTermQuotient (MapsOnto.preserves honto) n := rfl

theorem next_term_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : E n ⧸ nextTermSubgroup E n) (x : F n ⧸ nextTermSubgroup F n) :
    (nextOntoInjective honto hinj n).symm y = x ↔
      y = nextTermQuotient (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Equivalence on consecutive-term quotients induced by a termwise-onto map whose
kernel lies in the next source term. -/
noncomputable def nextMapsKer
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1)) :
    (F n ⧸ nextTermSubgroup F n) ≃* (E n ⧸ nextTermSubgroup E n) :=
  MulEquiv.ofBijective (nextTermQuotient (MapsOnto.preserves honto) n)
    (next_bijective_maps honto hker)

@[simp] theorem next_quotient_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (x : F n ⧸ nextTermSubgroup F n) :
    nextMapsKer honto n hker x =
      nextTermQuotient (MapsOnto.preserves honto) n x := rfl

@[simp] theorem next_onto_monoid
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1)) :
    (nextMapsKer honto n hker).toMonoidHom =
      nextTermQuotient (MapsOnto.preserves honto) n := rfl

/-- Inverse-characterization for consecutive-term quotient equivalences from termwise-onto
maps with kernel contained in the next source term. -/
theorem next_equiv_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (y : E n ⧸ nextTermSubgroup E n) (x : F n ⧸ nextTermSubgroup F n) :
    (nextMapsKer honto n hker).symm y = x ↔
      y = nextTermQuotient (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on earlier consecutive-term
quotients whenever it lies below the next relevant source term. -/
noncomputable def nextOntoKer
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    (F n ⧸ nextTermSubgroup F n) ≃* (E n ⧸ nextTermSubgroup E n) :=
  nextMapsKer honto n (honto.ker_le_lea hker hnk)

@[simp] theorem next_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoKer honto n hker hnk x =
      nextTermQuotient (MapsOnto.preserves honto) n x := rfl

@[simp] theorem next_monoid_hom
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    (nextOntoKer honto n hker hnk).toMonoidHom =
      nextTermQuotient (MapsOnto.preserves honto) n := rfl

theorem next_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (y : E n ⧸ nextTermSubgroup E n) (x : F n ⧸ nextTermSubgroup F n) :
    (nextOntoKer honto n hker hnk).symm y = x ↔
      y = nextTermQuotient (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A filtration-preserving homomorphism induces a homomorphism on layer kernels. -/
noncomputable def layerMap {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    lKern F n →* lKern E n where
  toFun x := ⟨quotientMap hφ (n + 1) x, by
    rcases x with ⟨q, hq⟩
    refine QuotientGroup.induction_on q ?_ hq
    intro g hg
    change QuotientGroup.mk' (F (n + 1)) g ∈ lKern F n at hg
    have hgn : g ∈ F n := (layer_kernel_mk F n g).1 hg
    change quotientMap hφ (n + 1) (QuotientGroup.mk' (F (n + 1)) g) ∈ lKern E n
    rw [quotientMap_mk]
    exact (layer_kernel_mk E n (φ g)).2 (hφ n ⟨g, hgn, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp


@[simp] theorem layerMap_coe {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) (x : lKern F n) :
    ((layerMap hφ n x : lKern E n) : H ⧸ (E (n + 1))) =
      quotientMap hφ (n + 1) (x : G ⧸ (F (n + 1))) := rfl

/-- The term-to-layer maps are natural for filtration-preserving homomorphisms. -/
theorem layer_term_naturality {F : DFilt G} {E : DFilt H}
    {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ) :
    (layerMap hφ n).comp (layerOfTerm F n) =
      (layerOfTerm E n).comp (termMap hφ n) := by
  apply MonoidHom.ext
  intro x
  ext
  rfl

/-- Kernel membership for a term-represented layer element under a layer map. -/
@[simp] theorem ker_layer_term {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (x : F n) :
    layerOfTerm F n x ∈ MonoidHom.ker (layerMap hφ n) ↔
      φ (x : G) ∈ E (n + 1) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hv := congrArg (fun y : lKern E n => (y : H ⧸ E (n + 1))) h
    change quotientMap hφ (n + 1) (QuotientGroup.mk' (F (n + 1)) (x : G)) = 1 at hv
    rw [quotientMap_mk] at hv
    exact (QuotientGroup.eq_one_iff (φ (x : G))).1 hv
  · intro hx
    ext
    change quotientMap hφ (n + 1) (QuotientGroup.mk' (F (n + 1)) (x : G)) = 1
    rw [quotientMap_mk]
    exact (QuotientGroup.eq_one_iff (φ (x : G))).2 hx

/-- The concrete quotient description of layers is natural for preserving maps. -/
theorem layer_next_naturality {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) (n : ℕ)
    (q : F n ⧸ nextTermSubgroup F n) :
    layerNextEquiv E n (nextTermQuotient hφ n q) =
      layerMap hφ n (layerNextEquiv F n q) := by
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

@[simp] theorem layerMap_id (F : DFilt G) (n : ℕ) :
    layerMap (preserves_id F) n = MonoidHom.id (lKern F n) := by
  apply MonoidHom.ext
  intro x
  ext
  change quotientMap (preserves_id F) (n + 1) (x : G ⧸ (F (n + 1))) =
    (x : G ⧸ (F (n + 1)))
  rw [quotientMap_id]
  rfl

/-- Layer maps are functorial under composition of filtration-preserving maps. -/
@[simp] theorem layerMap_comp {K : Type*} [Group K]
    {F : DFilt G} {E : DFilt H}
    {D : DFilt K} {φ : G →* H} {ψ : H →* K}
    (hφ : Preserves F E φ) (hψ : Preserves E D ψ) (n : ℕ) :
    layerMap (Preserves.comp hφ hψ) n = (layerMap hψ n).comp (layerMap hφ n) := by
  apply MonoidHom.ext
  intro x
  ext
  rcases x with ⟨q, hq⟩
  revert hq
  refine QuotientGroup.induction_on q ?_
  intro g hg
  rfl


/-- Via the concrete consecutive-quotient description, layer-map injectivity is
equivalent to injectivity on the corresponding consecutive-term quotient. -/
theorem layer_injective_next
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (hφ : Preserves F E φ) (n : ℕ) :
    Function.Injective (layerMap hφ n) ↔
      Function.Injective (nextTermQuotient hφ n) := by
  constructor
  · intro hl q r hqr
    apply (layerNextEquiv F n).injective
    apply hl
    rw [← layer_next_naturality hφ n q,
      ← layer_next_naturality hφ n r, hqr]
  · intro hn x y hxy
    rcases (layerNextEquiv F n).surjective x with ⟨qx, rfl⟩
    rcases (layerNextEquiv F n).surjective y with ⟨qy, rfl⟩
    apply congrArg (layerNextEquiv F n)
    apply hn
    apply (layerNextEquiv E n).injective
    simpa [layer_next_naturality] using hxy

/-- Exact subgroup-preimage criterion for injectivity of a layer map. -/
theorem layer_comap
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (hφ : Preserves F E φ) {n : ℕ} :
    Function.Injective (layerMap hφ n) ↔
      (nextTermSubgroup E n).comap (termMap hφ n) ≤ nextTermSubgroup F n := by
  rw [layer_injective_next hφ n]
  exact next_term_comap hφ

/-- A term-level preimage criterion for injectivity on layer kernels. -/
theorem layer_injective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ) {n : ℕ}
    (hpre : (E (n + 1)).comap φ ≤ F (n + 1)) :
    Function.Injective (layerMap hφ n) := by
  intro x y hxy
  rcases (layerNextEquiv F n).surjective x with ⟨qx, rfl⟩
  rcases (layerNextEquiv F n).surjective y with ⟨qy, rfl⟩
  have hq : qx = qy := by
    apply next_injective_comap hφ hpre
    apply (layerNextEquiv E n).injective
    simpa [layer_next_naturality] using hxy
  simp [hq]

/-- A termwise onto filtration map induces surjective maps on layer kernels. -/
theorem layer_surjective_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    Function.Surjective (layerMap (MapsOnto.preserves honto) n) := by
  intro y
  rcases y with ⟨q, hq⟩
  refine QuotientGroup.induction_on q ?_ hq
  intro h hh
  have hhE : h ∈ E n := (layer_kernel_mk E n h).1 hh
  have himg : h ∈ (F n).map φ := by simpa [honto n] using hhE
  rcases himg with ⟨g, hg, hfg⟩
  let xq : G ⧸ (F (n + 1)) := QuotientGroup.mk' (F (n + 1)) g
  have hxmem : xq ∈ lKern F n := (layer_kernel_mk F n g).2 hg
  refine ⟨⟨xq, hxmem⟩, ?_⟩
  ext
  change quotientMap (MapsOnto.preserves honto) (n + 1)
      (QuotientGroup.mk' (F (n + 1)) g) = QuotientGroup.mk' (E (n + 1)) h
  rw [quotientMap_mk, hfg]

/-- Range form of surjectivity for layer-kernel maps. -/
theorem layer_top_onto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ) :
    (layerMap (MapsOnto.preserves honto) n).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (layer_surjective_onto honto n)

/-- For a split epimorphism, injectivity on layer kernels is controlled by the
intersection of the kernel with the current source term. -/
theorem injective_inf_inverse {F : DFilt G}
    {E : DFilt H} {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Injective (layerMap hφ n) ↔ φ.ker ⊓ F n ≤ F (n + 1) := by
  rw [layer_comap hφ]
  exact next_comap_inf hφ hσ hright

/-- For a split epimorphism, bijectivity on layer kernels is controlled by the
intersection of the kernel with the current source term. -/
theorem bijective_inf_inverse {F : DFilt G}
    {E : DFilt H} {φ : G →* H} {σ : H →* G}
    (hφ : Preserves F E φ) (hσ : Preserves E F σ)
    (hright : Function.RightInverse σ φ) {n : ℕ} :
    Function.Bijective (layerMap hφ n) ↔ φ.ker ⊓ F n ≤ F (n + 1) := by
  have honto : MapsOnto F E φ := MapsOnto.of_rightInverse hφ hσ hright
  have hsurj : Function.Surjective (layerMap hφ n) := by
    simpa using (layer_surjective_onto honto n)
  constructor
  · intro hb
    exact (injective_inf_inverse hφ hσ hright).1 hb.1
  · intro hker
    exact ⟨(injective_inf_inverse hφ hσ hright).2 hker,
      hsurj⟩

/-- For termwise-onto maps, bijectivity on layer kernels is equivalent to the
exact consecutive-term preimage condition. -/
theorem layer_bijective_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ} :
    Function.Bijective (layerMap (MapsOnto.preserves honto) n) ↔
      (nextTermSubgroup E n).comap (termMap (MapsOnto.preserves honto) n) ≤
        nextTermSubgroup F n := by
  constructor
  · intro hb
    exact (layer_comap (MapsOnto.preserves honto)).1 hb.1
  · intro hpre
    exact ⟨(layer_comap (MapsOnto.preserves honto)).2 hpre,
      layer_surjective_onto honto n⟩

/-- Bijectivity on layer kernels from termwise surjectivity and a preimage criterion. -/
theorem bijective_maps_comap {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hpre : (E (n + 1)).comap φ ≤ F (n + 1)) :
    Function.Bijective (layerMap (MapsOnto.preserves honto) n) :=
  ⟨layer_injective_comap (MapsOnto.preserves honto) hpre,
    layer_surjective_onto honto n⟩

/-- For a termwise-onto map, kernel containment in the next source term gives
bijectivity on layer kernels. -/
theorem layer_bijective_maps {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) {n : ℕ}
    (hker : φ.ker ≤ F (n + 1)) :
    Function.Bijective (layerMap (MapsOnto.preserves honto) n) := by
  apply bijective_maps_comap honto
  exact le_of_eq ((MapsOnto.comap_eqiff_kerle honto (n + 1)).2 hker)

/-- A deeper kernel-containment hypothesis gives bijectivity on earlier layer kernels. -/
theorem layer_bijective_ker {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    {k : ℕ} (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    Function.Bijective (layerMap (MapsOnto.preserves honto) n) :=
  layer_bijective_maps honto (honto.ker_le_lea hker hnk)

/-- Termwise-onto injective maps induce bijections on layer kernels. -/
theorem layer_bijective_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    Function.Bijective (layerMap (MapsOnto.preserves honto) n) :=
  bijective_maps_comap honto
    (honto.comap_le_inj hinj (n + 1))

/-- Equivalence on layer kernels induced by a termwise-onto injective map. -/
noncomputable def layerOntoInjective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    lKern F n ≃* lKern E n :=
  MulEquiv.ofBijective (layerMap (MapsOnto.preserves honto) n)
    (layer_bijective_injective honto hinj n)

@[simp] theorem equiv_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (x : lKern F n) :
    layerOntoInjective honto hinj n x =
      layerMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem layer_injective_monoid {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) :
    (layerOntoInjective honto hinj n).toMonoidHom =
      layerMap (MapsOnto.preserves honto) n := rfl

theorem layer_equiv_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) (n : ℕ) (y : lKern E n) (x : lKern F n) :
    (layerOntoInjective honto hinj n).symm y = x ↔
      y = layerMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- Equivalence on layer kernels induced by a termwise-onto map whose kernel lies in
the next source term. -/
noncomputable def layerMapsKer {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    (hker : φ.ker ≤ F (n + 1)) : lKern F n ≃* lKern E n :=
  MulEquiv.ofBijective (layerMap (MapsOnto.preserves honto) n)
    (layer_bijective_maps honto hker)

@[simp] theorem layer_maps {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    (hker : φ.ker ≤ F (n + 1)) (x : lKern F n) :
    layerMapsKer honto n hker x =
      layerMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem layer_onto_monoid {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    (hker : φ.ker ≤ F (n + 1)) :
    (layerMapsKer honto n hker).toMonoidHom =
      layerMap (MapsOnto.preserves honto) n := rfl

/-- Inverse-characterization for layer equivalences from termwise-onto maps with
kernel contained in the next source term. -/
theorem onto_symm {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    (hker : φ.ker ≤ F (n + 1)) (y : lKern E n) (x : lKern F n) :
    (layerMapsKer honto n hker).symm y = x ↔
      y = layerMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- A deeper kernel-containment hypothesis induces equivalences on earlier layer kernels
whenever it lies below the next relevant source term. -/
noncomputable def layerOntoKer {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    {k : ℕ} (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    lKern F n ≃* lKern E n :=
  layerMapsKer honto n (honto.ker_le_lea hker hnk)

@[simp] theorem layer_ker {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    {k : ℕ} (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) (x : lKern F n) :
    layerOntoKer honto n hker hnk x =
      layerMap (MapsOnto.preserves honto) n x := rfl

@[simp] theorem layer_monoid_hom {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    {k : ℕ} (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) :
    (layerOntoKer honto n hker hnk).toMonoidHom =
      layerMap (MapsOnto.preserves honto) n := rfl

theorem layer_equiv_symm {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ) (n : ℕ)
    {k : ℕ} (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (y : lKern E n) (x : lKern F n) :
    (layerOntoKer honto n hker hnk).symm y = x ↔
      y = layerMap (MapsOnto.preserves honto) n x := by
  rw [MulEquiv.symm_apply_eq]
  rfl


/-- The inverse of the injective/onto layer equivalence cancels the layer map. -/
@[simp] theorem layer_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : lKern F n) :
    (layerOntoInjective honto hinj n).symm
        (layerMap (MapsOnto.preserves honto) n x) = x := by
  exact (layerOntoInjective honto hinj n).left_inv x

/-- The layer map cancels the inverse of the injective/onto layer equivalence. -/
@[simp] theorem layer_injective_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n
        ((layerOntoInjective honto hinj n).symm y) = y := by
  change layerOntoInjective honto hinj n
      ((layerOntoInjective honto hinj n).symm y) = y
  exact (layerOntoInjective honto hinj n).right_inv y

/-- The inverse of the small-kernel layer equivalence cancels the layer map. -/
@[simp] theorem layer_equiv_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (x : lKern F n) :
    (layerMapsKer honto n hker).symm
        (layerMap (MapsOnto.preserves honto) n x) = x := by
  exact (layerMapsKer honto n hker).left_inv x

/-- The layer map cancels the inverse of the small-kernel layer equivalence. -/
@[simp] theorem layer_equiv_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n
        ((layerMapsKer honto n hker).symm y) = y := by
  change layerMapsKer honto n hker
      ((layerMapsKer honto n hker).symm y) = y
  exact (layerMapsKer honto n hker).right_inv y

/-- The inverse of the monotone small-kernel layer equivalence cancels the layer map. -/
@[simp] theorem layer_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) (x : lKern F n) :
    (layerOntoKer honto n hker hnk).symm
        (layerMap (MapsOnto.preserves honto) n x) = x := by
  exact (layerOntoKer honto n hker hnk).left_inv x

/-- The layer map cancels the inverse of the monotone small-kernel layer equivalence. -/
@[simp] theorem layer_ker_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k) (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n
        ((layerOntoKer honto n hker hnk).symm y) = y := by
  change layerOntoKer honto n hker hnk
      ((layerOntoKer honto n hker hnk).symm y) = y
  exact (layerOntoKer honto n hker hnk).right_inv y


/-- The inverse of the injective/onto consecutive-quotient equivalence cancels its map. -/
@[simp] theorem next_injective_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : F n ⧸ nextTermSubgroup F n) :
    (nextOntoInjective honto hinj n).symm
        (nextTermQuotient (MapsOnto.preserves honto) n x) = x := by
  exact (nextOntoInjective honto hinj n).left_inv x

/-- The consecutive-quotient map cancels the inverse injective/onto equivalence. -/
@[simp] theorem next_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n
        ((nextOntoInjective honto hinj n).symm y) = y := by
  change nextOntoInjective honto hinj n
      ((nextOntoInjective honto hinj n).symm y) = y
  exact (nextOntoInjective honto hinj n).right_inv y

/-- The inverse of the small-kernel consecutive-quotient equivalence cancels its map. -/
@[simp] theorem next_term_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (x : F n ⧸ nextTermSubgroup F n) :
    (nextMapsKer honto n hker).symm
        (nextTermQuotient (MapsOnto.preserves honto) n x) = x := by
  exact (nextMapsKer honto n hker).left_inv x

/-- The consecutive-quotient map cancels the inverse small-kernel equivalence. -/
@[simp] theorem next_quotient_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n
        ((nextMapsKer honto n hker).symm y) = y := by
  change nextMapsKer honto n hker
      ((nextMapsKer honto n hker).symm y) = y
  exact (nextMapsKer honto n hker).right_inv y

/-- The inverse of the monotone small-kernel consecutive-quotient equivalence cancels its map. -/
@[simp] theorem next_ker_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    (nextOntoKer honto n hker hnk).symm
        (nextTermQuotient (MapsOnto.preserves honto) n x) = x := by
  exact (nextOntoKer honto n hker hnk).left_inv x

/-- The consecutive-quotient map cancels the inverse monotone small-kernel equivalence. -/
@[simp] theorem next_term_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n
        ((nextOntoKer honto n hker hnk).symm y) = y := by
  change nextOntoKer honto n hker hnk
      ((nextOntoKer honto n hker hnk).symm y) = y
  exact (nextOntoKer honto n hker hnk).right_inv y


/-- The inverse of a small-kernel transition-kernel equivalence cancels its map. -/
@[simp] theorem transition_kernel_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionMapsOnto honto h hker).symm
        (transitionKernelMap (MapsOnto.preserves honto) h x) = x := by
  exact (transitionMapsOnto honto h hker).left_inv x

/-- The transition-kernel map cancels the inverse small-kernel equivalence. -/
@[simp] theorem transition_equiv_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h
        ((transitionMapsOnto honto h hker).symm y) = y := by
  change transitionMapsOnto honto h hker
      ((transitionMapsOnto honto h hker).symm y) = y
  exact (transitionMapsOnto honto h hker).right_inv y

/-- The inverse of a monotone small-kernel transition equivalence cancels its map. -/
@[simp] theorem transition_kernel_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionOntoKer honto h hker hnk).symm
        (transitionKernelMap (MapsOnto.preserves honto) h x) = x := by
  exact (transitionOntoKer honto h hker hnk).left_inv x

/-- The transition-kernel map cancels the inverse monotone small-kernel equivalence. -/
@[simp] theorem transition_equiv_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h
        ((transitionOntoKer honto h hker hnk).symm y) = y := by
  change transitionOntoKer honto h hker hnk
      ((transitionOntoKer honto h hker hnk).symm y) = y
  exact (transitionOntoKer honto h hker hnk).right_inv y

/-- The inverse of an injective/onto transition-kernel equivalence cancels its map. -/
@[simp] theorem equiv_injective_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x : MonoidHom.ker (quotientTransition F h)) :
    (transitionOntoInjective honto hinj h).symm
        (transitionKernelMap (MapsOnto.preserves honto) h x) = x := by
  exact (transitionOntoInjective honto hinj h).left_inv x

/-- The transition-kernel map cancels the inverse injective/onto equivalence. -/
@[simp] theorem transition_equiv_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h
        ((transitionOntoInjective honto hinj h).symm y) = y := by
  change transitionOntoInjective honto hinj h
      ((transitionOntoInjective honto hinj h).symm y) = y
  exact (transitionOntoInjective honto hinj h).right_inv y


/-- The inverse of a small-kernel term-quotient equivalence cancels its map. -/
@[simp] theorem term_quotient_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (x : F m ⧸ tSOf F h) :
    (termMapsOnto honto h hker).symm
        (termQuotient (MapsOnto.preserves honto) h x) = x := by
  exact (termMapsOnto honto h hker).left_inv x

/-- The term-quotient map cancels the inverse small-kernel equivalence. -/
@[simp] theorem term_quotient_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h
        ((termMapsOnto honto h hker).symm y) = y := by
  change termMapsOnto honto h hker
      ((termMapsOnto honto h hker).symm y) = y
  exact (termMapsOnto honto h hker).right_inv y

/-- The inverse of a monotone small-kernel term-quotient equivalence cancels its map. -/
@[simp] theorem term_quotient_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) (x : F m ⧸ tSOf F h) :
    (termMapsKer honto h hker hnk).symm
        (termQuotient (MapsOnto.preserves honto) h x) = x := by
  exact (termMapsKer honto h hker hnk).left_inv x

/-- The term-quotient map cancels the inverse monotone small-kernel equivalence. -/
@[simp] theorem term_equiv_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h
        ((termMapsKer honto h hker hnk).symm y) = y := by
  change termMapsKer honto h hker hnk
      ((termMapsKer honto h hker hnk).symm y) = y
  exact (termMapsKer honto h hker hnk).right_inv y

/-- The inverse of an injective/onto term-quotient equivalence cancels its map. -/
@[simp] theorem quotient_injective_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x : F m ⧸ tSOf F h) :
    (termMapsInjective honto hinj h).symm
        (termQuotient (MapsOnto.preserves honto) h x) = x := by
  exact (termMapsInjective honto hinj h).left_inv x

/-- The term-quotient map cancels the inverse injective/onto equivalence. -/
@[simp] theorem term_equiv_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h
        ((termMapsInjective honto hinj h).symm y) = y := by
  change termMapsInjective honto hinj h
      ((termMapsInjective honto hinj h).symm y) = y
  exact (termMapsInjective honto hinj h).right_inv y


/-- The inverse of an injective/onto quotient equivalence cancels its quotient map. -/
@[simp] theorem quotient_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : G ⧸ F n) :
    (quotientOntoInjective honto hinj n).symm
        (quotientMap (MapsOnto.preserves honto) n x) = x := by
  exact (quotientOntoInjective honto hinj n).left_inv x

/-- The quotient map cancels the inverse injective/onto quotient equivalence. -/
@[simp] theorem quotient_equiv_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : H ⧸ E n) :
    quotientMap (MapsOnto.preserves honto) n
        ((quotientOntoInjective honto hinj n).symm y) = y := by
  change quotientOntoInjective honto hinj n
      ((quotientOntoInjective honto hinj n).symm y) = y
  exact (quotientOntoInjective honto hinj n).right_inv y

/-- The inverse of a small-kernel quotient equivalence cancels its quotient map. -/
@[simp] theorem quotient_equiv_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F n)
    (x : G ⧸ F n) :
    (quotientMapsKer honto hker).symm
        (quotientMap (MapsOnto.preserves honto) n x) = x := by
  exact (quotientMapsKer honto hker).left_inv x

/-- The quotient map cancels the inverse small-kernel quotient equivalence. -/
@[simp] theorem quotient_equiv_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F n)
    (y : H ⧸ E n) :
    quotientMap (MapsOnto.preserves honto) n
        ((quotientMapsKer honto hker).symm y) = y := by
  change quotientMapsKer honto hker
      ((quotientMapsKer honto hker).symm y) = y
  exact (quotientMapsKer honto hker).right_inv y

/-- The inverse of a monotone small-kernel quotient equivalence cancels its map. -/
@[simp] theorem quotient_onto_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ}
    (hker : φ.ker ≤ F n) (hmn : m ≤ n) (x : G ⧸ F m) :
    (quotientOntoKer honto hker hmn).symm
        (quotientMap (MapsOnto.preserves honto) m x) = x := by
  exact (quotientOntoKer honto hker hmn).left_inv x

/-- The quotient map cancels the inverse monotone small-kernel quotient equivalence. -/
@[simp] theorem equiv_ker_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ}
    (hker : φ.ker ≤ F n) (hmn : m ≤ n) (y : H ⧸ E m) :
    quotientMap (MapsOnto.preserves honto) m
        ((quotientOntoKer honto hker hmn).symm y) = y := by
  change quotientOntoKer honto hker hmn
      ((quotientOntoKer honto hker hmn).symm y) = y
  exact (quotientOntoKer honto hker hmn).right_inv y


/-- The inverse term equivalence cancels the restricted term map. -/
@[simp] theorem injective_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : F n) :
    (termEquivInjective honto hinj n).symm
        (termMap (MapsOnto.preserves honto) n x) = x := by
  exact (termEquivInjective honto hinj n).left_inv x

/-- The restricted term map cancels the inverse term equivalence. -/
@[simp] theorem term_symm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (y : E n) :
    termMap (MapsOnto.preserves honto) n
        ((termEquivInjective honto hinj n).symm y) = y := by
  change termEquivInjective honto hinj n
      ((termEquivInjective honto hinj n).symm y) = y
  exact (termEquivInjective honto hinj n).right_inv y



/-- Pointwise cancellation for inverse restricted embedded-term maps. -/
@[simp] theorem tSOf.map_symm_applyself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    tSOf.map hb hmn (tSOf.map hf hmn x) = x := by
  have h := congrArg (fun f : tSOf F hmn →* tSOf F hmn => f x)
    (tSOf.map_symm_comp e hf hb hmn)
  simpa [MonoidHom.comp_apply] using h

/-- Pointwise cancellation in the other order for inverse restricted embedded-term maps. -/
@[simp] theorem tSOf.map_apply_symmself
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) (y : tSOf E hmn) :
    tSOf.map hf hmn (tSOf.map hb hmn y) = y := by
  have h := congrArg (fun f : tSOf E hmn →* tSOf E hmn => f y)
    (tSOf.map_comp_symm e hf hb hmn)
  simpa [MonoidHom.comp_apply] using h

/-- Pointwise cancellation for inverse maps on quotients by embedded terms. -/
@[simp] theorem quotient_symm_self
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (q : F m ⧸ tSOf F h) :
    termQuotient hb h (termQuotient hf h q) = q := by
  have hc := congrArg (fun f : (F m ⧸ tSOf F h) →* (F m ⧸ tSOf F h) => f q)
    (term_symm_comp e hf hb h)
  simpa [MonoidHom.comp_apply] using hc

/-- Pointwise cancellation in the other order for maps on quotients by embedded terms. -/
@[simp] theorem term_quotient_self
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) (q : E m ⧸ tSOf E h) :
    termQuotient hf h (termQuotient hb h q) = q := by
  have hc := congrArg (fun f : (E m ⧸ tSOf E h) →* (E m ⧸ tSOf E h) => f q)
    (quotient_comp_symm e hf hb h)
  simpa [MonoidHom.comp_apply] using hc

/-- Pointwise cancellation for inverse maps on nested-inclusion-range quotients. -/
@[simp] theorem tSOf.inclus_quotm_symma
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    tSOf.inclusion_range_quotmap hb hmn hnk
        (tSOf.inclusion_range_quotmap hf hmn hnk q) = q := by
  have hc := congrArg
    (fun f : (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) →*
        (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) => f q)
    (tSOf.inclus_quotm_symmc e hf hb hmn hnk)
  simpa [MonoidHom.comp_apply] using hc

/-- Pointwise cancellation in the other order for nested-inclusion-range quotient maps. -/
@[simp] theorem tSOf.inclus_quotm_apply
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) :
    tSOf.inclusion_range_quotmap hf hmn hnk
        (tSOf.inclusion_range_quotmap hb hmn hnk q) = q := by
  have hc := congrArg
    (fun f : (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) →*
        (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) => f q)
    (tSOf.inclus_quotm_comps e hf hb hmn hnk)
  simpa [MonoidHom.comp_apply] using hc


/-- Hom-level inverse composition for generic restricted embedded-term equivalences. -/
@[simp] theorem tSOf.equivmul_equivmonoid_homsymmcomp
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e hf hb hmn).symm.toMonoidHom.comp
        (tSOf.equiv_mul_equiv e hf hb hmn).toMonoidHom =
      MonoidHom.id (tSOf F hmn) := by
  simpa using tSOf.map_symm_comp e hf hb hmn

/-- Hom-level inverse composition in the other order for generic restricted terms. -/
@[simp] theorem tSOf.equivmul_equivmonoid_homcompsymm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_mul_equiv e hf hb hmn).toMonoidHom.comp
        (tSOf.equiv_mul_equiv e hf hb hmn).symm.toMonoidHom =
      MonoidHom.id (tSOf E hmn) := by
  simpa using tSOf.map_comp_symm e hf hb hmn

/-- Hom-level inverse composition for generic quotients by embedded terms. -/
@[simp] theorem term_monoid_comp
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e hf hb h).symm.toMonoidHom.comp
        (termQuotientMul e hf hb h).toMonoidHom =
      MonoidHom.id (F m ⧸ tSOf F h) := by
  simpa using term_symm_comp e hf hb h

/-- Hom-level inverse composition in the other order for generic term quotients. -/
@[simp] theorem monoid_comp_symm
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n : ℕ} (h : m ≤ n) :
    (termQuotientMul e hf hb h).toMonoidHom.comp
        (termQuotientMul e hf hb h).symm.toMonoidHom =
      MonoidHom.id (E m ⧸ tSOf E h) := by
  simpa using quotient_comp_symm e hf hb h

/-- Hom-level inverse composition for generic nested-inclusion-range quotient equivalences. -/
@[simp] theorem tSOf.inclrangquot_equivmulequiv_monhomsymcom
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm.toMonoidHom.comp
        (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).toMonoidHom =
      MonoidHom.id (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) := by
  simpa using tSOf.inclus_quotm_symmc e hf hb hmn hnk

/-- Hom-level inverse composition in the other order for generic nested-range quotients. -/
@[simp] theorem tSOf.inclrangquot_equivmulequiv_monhomcomsym
    {F : DFilt G} {E : DFilt H} (e : G ≃* H)
    (hf : Preserves F E e.toMonoidHom) (hb : Preserves E F e.symm.toMonoidHom)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).toMonoidHom.comp
        (tSOf.inclusionrange_quotequiv_mulequiv e hf hb hmn hnk).symm.toMonoidHom =
      MonoidHom.id (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) := by
  simpa using tSOf.inclus_quotm_comps e hf hb hmn hnk

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Restricted maps on embedded terms are injective when the ambient homomorphism is. -/
theorem tSOf.map_injective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (tSOf.map hφ hmn) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply hinj
  simpa [tSOf.map_coe] using
    congrArg (fun z : tSOf E hmn => ((z : E m) : H)) hxy


end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Kernel form of injectivity for restricted maps on embedded terms. -/
@[simp] theorem tSOf.map_kereq_botinj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : Preserves F E φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.map hφ hmn).ker = ⊥ := by
  exact (MonoidHom.ker_eq_bot_iff _).2 (tSOf.map_injective hφ hinj hmn)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Restricted maps on embedded terms are surjective when the ambient map is termwise onto. -/
theorem tSOf.map_surjective {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : MapsOnto F E φ)
    {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (tSOf.map (MapsOnto.preserves hφ) hmn) := by
  intro y
  have hy_n : ((y : E m) : H) ∈ E n :=
    (mem_term_of E hmn (y : E m)).1 y.property
  rw [← hφ n] at hy_n
  rcases hy_n with ⟨x, hxFn, hxy⟩
  let xFm : F m := ⟨x, F.antitone hmn hxFn⟩
  have hxTerm : xFm ∈ tSOf F hmn := by
    rw [mem_term_of]
    exact hxFn
  refine ⟨⟨xFm, hxTerm⟩, ?_⟩
  ext
  exact hxy

/-- Range form of surjectivity for restricted maps on embedded terms. -/
@[simp] theorem tSOf.maprange_eqtop_mapsonto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (hφ : MapsOnto F E φ)
    {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.map (MapsOnto.preserves hφ) hmn).range = ⊤ := by
  exact MonoidHom.range_eq_top.mpr (tSOf.map_surjective hφ hmn)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Bijectivity of restricted embedded-term maps from termwise surjectivity and injectivity. -/
theorem tSOf.map_bijmaps_ontoinj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Bijective (tSOf.map (MapsOnto.preserves honto) hmn) :=
  ⟨tSOf.map_injective (MapsOnto.preserves honto) hinj hmn,
    tSOf.map_surjective honto hmn⟩

/-- Equivalence on embedded concrete terms induced by a termwise-onto injective map. -/
noncomputable def tSOf.equiv_maps_ontoinj {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    tSOf F hmn ≃* tSOf E hmn :=
  MulEquiv.ofBijective (tSOf.map (MapsOnto.preserves honto) hmn)
    (tSOf.map_bijmaps_ontoinj honto hinj hmn)

@[simp] theorem tSOf.equiv_mapsonto_injapply {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : tSOf F hmn) :
    tSOf.equiv_maps_ontoinj honto hinj hmn x =
      tSOf.map (MapsOnto.preserves honto) hmn x := rfl

@[simp] theorem tSOf.equivmaps_ontoinj_monoidhom
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    (tSOf.equiv_maps_ontoinj honto hinj hmn).toMonoidHom =
      tSOf.map (MapsOnto.preserves honto) hmn := rfl

@[simp] theorem tSOf.equivmaps_ontoinj_applycoe
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : tSOf F hmn) :
    (((tSOf.equiv_maps_ontoinj honto hinj hmn x :
        tSOf E hmn) : E m) : H) = φ ((x : F m) : G) := rfl

/-- Characterize inverse images for the embedded-term equivalence. -/
theorem tSOf.equivmaps_ontoinj_symmapplyeq
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : tSOf E hmn) (x : tSOf F hmn) :
    (tSOf.equiv_maps_ontoinj honto hinj hmn).symm y = x ↔
      y = tSOf.map (MapsOnto.preserves honto) hmn x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Left inverse cancellation for embedded-term equivalences from onto-injective maps. -/
@[simp] theorem tSOf.equivm_ontoi_symma
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : tSOf F hmn) :
    (tSOf.equiv_maps_ontoinj honto hinj hmn).symm
        (tSOf.equiv_maps_ontoinj honto hinj hmn x) = x :=
  (tSOf.equiv_maps_ontoinj honto hinj hmn).left_inv x

/-- Right inverse cancellation for embedded-term equivalences from onto-injective maps. -/
@[simp] theorem tSOf.equivm_ontoi_apply
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : tSOf E hmn) :
    tSOf.equiv_maps_ontoinj honto hinj hmn
        ((tSOf.equiv_maps_ontoinj honto hinj hmn).symm y) = y :=
  (tSOf.equiv_maps_ontoinj honto hinj hmn).right_inv y

/-- The inverse embedded-term equivalence chooses a preimage under the ambient homomorphism. -/
theorem tSOf.equivmaps_ontoinj_symmapplycoe
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (y : tSOf E hmn) :
    φ ((((tSOf.equiv_maps_ontoinj honto hinj hmn).symm y :
        tSOf F hmn) : F m) : G) = ((y : E m) : H) := by
  have h := congrArg (fun z : tSOf E hmn => ((z : E m) : H))
    (tSOf.equivm_ontoi_apply honto hinj hmn y)
  exact h

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Maps on nested-inclusion-range quotients are surjective for termwise-onto filtration maps. -/
theorem tSOf.inclus_quotm_surjm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Surjective
      (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  rcases tSOf.map_surjective honto hmn y with ⟨x, rfl⟩
  refine ⟨QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x, ?_⟩
  rfl

/-- Range form of surjectivity for maps on nested-inclusion-range quotients. -/
@[simp] theorem tSOf.inclrangquot_maprangeeq_topmapsonto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk).range = ⊤ := by
  exact MonoidHom.range_eq_top.mpr
    (tSOf.inclus_quotm_surjm honto hmn hnk)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- A termwise-onto map carries nested-inclusion ranges onto nested-inclusion ranges. -/
theorem tSOf.maprange_inclusioneq_mapsonto {F : DFilt G}
    {E : DFilt H} {φ : G →* H} (honto : MapsOnto F E φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    ((tSOf.inclusion F hmn hnk).range).map
        (tSOf.map (MapsOnto.preserves honto) hmn) =
      (tSOf.inclusion E hmn hnk).range := by
  apply le_antisymm
  · exact tSOf.map_range_inclusionle (MapsOnto.preserves honto) hmn hnk
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    rcases tSOf.map_surjective honto (Nat.le_trans hmn hnk) z with ⟨w, hw⟩
    refine ⟨tSOf.inclusion F hmn hnk w, ?_, ?_⟩
    · exact ⟨w, rfl⟩
    · rw [← tSOf.inclusion_map_apply (MapsOnto.preserves honto) hmn hnk w]
      exact congrArg (tSOf.inclusion E hmn hnk) hw

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- A termwise-onto injective map induces an equivalence on quotients by nested inclusion ranges. -/
noncomputable def tSOf.inclus_quote_mapso
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) ≃*
      (tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) := by
  let e := tSOf.equiv_maps_ontoinj honto hinj hmn
  refine QuotientGroup.congr (tSOf.inclusion F hmn hnk).range
    (tSOf.inclusion E hmn hnk).range e ?_
  dsimp [e]
  simpa [tSOf.equivmaps_ontoinj_monoidhom] using
    tSOf.maprange_inclusioneq_mapsonto honto hmn hnk

@[simp] theorem tSOf.inclus_quote_ontoi
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (x : tSOf F hmn) :
    tSOf.inclus_quote_mapso honto hinj hmn hnk
        (QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range x) =
      QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range
        (tSOf.map (MapsOnto.preserves honto) hmn x) := by
  rfl

@[simp] theorem tSOf.inclra_equiv_injmo
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).toMonoidHom =
      tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Left inverse cancellation for onto-injective nested-range quotient equivalences. -/
@[simp] theorem tSOf.inclrangquot_equivmapsonto_injsymappsel
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm
      (tSOf.inclus_quote_mapso
        honto hinj hmn hnk q) = q :=
  (tSOf.inclus_quote_mapso
    honto hinj hmn hnk).left_inv q

/-- Right inverse cancellation for onto-injective nested-range quotient equivalences. -/
@[simp] theorem tSOf.inclrangquot_equivmapsonto_injappsymsel
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (q : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) :
    tSOf.inclus_quote_mapso
        honto hinj hmn hnk
      ((tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm q) = q :=
  (tSOf.inclus_quote_mapso
    honto hinj hmn hnk).right_inv q

/-- Characterize inverse images for onto-injective nested-range quotient equivalences. -/
theorem tSOf.inclrangquot_equivmapsonto_injsymmapplyeq
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range)
    (x : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm y = x ↔
      y = tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk x := by
  rw [MulEquiv.symm_apply_eq]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Bijectivity form for maps on nested-range quotients under termwise-onto injective maps. -/
theorem tSOf.inclus_quotm_mapso
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Bijective
      (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk) := by
  let e := tSOf.inclus_quote_mapso
    honto hinj hmn hnk
  change Function.Bijective e.toMonoidHom
  exact e.bijective

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- The inverse nested-range quotient equivalence sends a representative to the representative
chosen by the inverse embedded-term equivalence. -/
@[simp] theorem tSOf.inclra_equiv_injsa
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (y : tSOf E hmn) :
    (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm
      (QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range y) =
    QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range
      ((tSOf.equiv_maps_ontoinj honto hinj hmn).symm y) := by
  let eQ := tSOf.inclus_quote_mapso
    honto hinj hmn hnk
  let eT := tSOf.equiv_maps_ontoinj honto hinj hmn
  apply eQ.injective
  dsimp [eQ]
  rw [tSOf.inclrangquot_equivmapsonto_injappsymsel]
  symm
  change (tSOf.inclus_quote_mapso honto hinj hmn hnk)
      (QuotientGroup.mk' (tSOf.inclusion F hmn hnk).range (eT.symm y)) =
    QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range y
  rw [tSOf.inclus_quote_ontoi]
  change QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range (eT (eT.symm y)) =
    QuotientGroup.mk' (tSOf.inclusion E hmn hnk).range y
  rw [eT.apply_symm_apply]

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Injectivity form for maps on nested-range quotients under termwise-onto injective maps. -/
theorem tSOf.inclus_quotm_mapsa
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    Function.Injective
      (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk) :=
  (tSOf.inclus_quotm_mapso
    honto hinj hmn hnk).1

/-- Kernel form of injectivity for maps on nested-range quotients. -/
@[simp] theorem tSOf.inclrangquot_mapkereq_botmapsontoinj
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk).ker = ⊥ := by
  exact (MonoidHom.ker_eq_bot_iff _).2
    (tSOf.inclus_quotm_mapsa
      honto hinj hmn hnk)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Equality reflection for nested-range quotient maps under termwise-onto injective maps. -/
theorem tSOf.inclra_mapap_iffma
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x y : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk x =
        tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk y ↔
      x = y := by
  constructor
  · intro hxy
    exact (tSOf.inclus_quotm_mapsa
      honto hinj hmn hnk) hxy
  · intro h; simp [h]

/-- One-reflection form for nested-range quotient maps under termwise-onto injective maps. -/
@[simp] theorem tSOf.inclrangquot_mapapplyeqone_iffmapsontoinj
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk x = 1 ↔
      x = 1 := by
  simpa using
    (tSOf.inclra_mapap_iffma
      honto hinj hmn hnk x 1)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Inverse-after-map cancellation, stated with the concrete embedded-term map. -/
@[simp] theorem tSOf.equivmaps_ontoinj_symmapplymap
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    (tSOf.equiv_maps_ontoinj honto hinj hmn).symm
        (tSOf.map (MapsOnto.preserves honto) hmn x) = x := by
  exact tSOf.equivm_ontoi_symma honto hinj hmn x

/-- Map-after-inverse cancellation, stated with the concrete embedded-term map. -/
@[simp] theorem tSOf.mapapply_equivmaps_ontoinjsymm
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (y : tSOf E hmn) :
    tSOf.map (MapsOnto.preserves honto) hmn
        ((tSOf.equiv_maps_ontoinj honto hinj hmn).symm y) = y := by
  exact tSOf.equivm_ontoi_apply honto hinj hmn y

/-- Inverse-after-map cancellation on nested-range quotients, stated with the quotient map. -/
@[simp] theorem tSOf.inclra_equiv_injsy
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) :
    (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm
      (tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk x) = x := by
  let e := tSOf.inclus_quote_mapso
    honto hinj hmn hnk
  change e.symm (e x) = x
  exact e.left_inv x

/-- Map-after-inverse cancellation on nested-range quotients, stated with the quotient map. -/
@[simp] theorem tSOf.inclra_mapap_mapso
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (y : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) :
    tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk
      ((tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm y) = y := by
  let e := tSOf.inclus_quote_mapso
    honto hinj hmn hnk
  change e (e.symm y) = y
  exact e.right_inv y

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for onto-injective embedded-term equivalences. -/
theorem tSOf.equiv_mapsonto_injcomp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (hmn : m ≤ n) :
    tSOf.equiv_maps_ontoinj (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn =
      (tSOf.equiv_maps_ontoinj hφ hinjφ hmn).trans
        (tSOf.equiv_maps_ontoinj hψ hinjψ hmn) := by
  ext x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for onto-injective nested-range quotient equivalences. -/
theorem tSOf.inclusionrange_quotequivmaps_ontoinjcomp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf.inclus_quote_mapso
        (MapsOnto.comp hφ hψ) (fun _ _ hxy => hinjφ (hinjψ hxy)) hmn hnk =
      (tSOf.inclus_quote_mapso
        hφ hinjφ hmn hnk).trans
        (tSOf.inclus_quote_mapso
          hψ hinjψ hmn hnk) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G : Type*} [Group G]

/-- Identity law for onto-injective embedded-term equivalences. -/
@[simp] theorem tSOf.equiv_mapsonto_injid
    (F : DFilt G) {m n : ℕ} (hmn : m ≤ n) :
    tSOf.equiv_maps_ontoinj (mapsOnto_id F)
        (fun _ _ h => h) hmn = MulEquiv.refl (tSOf F hmn) := by
  ext x
  rfl

/-- Identity law for onto-injective nested-range quotient equivalences. -/
@[simp] theorem tSOf.inclusionrange_quotequivmaps_ontoinjid
    (F : DFilt G) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    tSOf.inclus_quote_mapso (mapsOnto_id F)
        (fun _ _ h => h) hmn hnk =
      MulEquiv.refl
        (tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Characterize forward images for the embedded-term equivalence. -/
theorem tSOf.equivmaps_ontoinj_applyeq
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n)
    (x : tSOf F hmn) (y : tSOf E hmn) :
    tSOf.map (MapsOnto.preserves honto) hmn x = y ↔
      x = (tSOf.equiv_maps_ontoinj honto hinj hmn).symm y := by
  let e := tSOf.equiv_maps_ontoinj honto hinj hmn
  change e x = y ↔ x = e.symm y
  constructor
  · intro h
    rw [← h]
    exact (e.left_inv x).symm
  · intro h
    rw [h]
    exact e.right_inv y

/-- Characterize forward images for onto-injective nested-range quotient equivalences. -/
theorem tSOf.inclrangquot_equivmapsonto_injapplyeq
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : tSOf F hmn ⧸ (tSOf.inclusion F hmn hnk).range)
    (y : tSOf E hmn ⧸ (tSOf.inclusion E hmn hnk).range) :
    tSOf.inclusion_range_quotmap (MapsOnto.preserves honto) hmn hnk x = y ↔
      x = (tSOf.inclus_quote_mapso
        honto hinj hmn hnk).symm y := by
  let e := tSOf.inclus_quote_mapso
    honto hinj hmn hnk
  change e x = y ↔ x = e.symm y
  constructor
  · intro h
    rw [← h]
    exact (e.left_inv x).symm
  · intro h
    rw [h]
    exact e.right_inv y

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Injectivity of embedded-term maps under termwise-onto injective maps (convenience wrapper). -/
theorem tSOf.map_injmaps_ontoinj
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (tSOf.map (MapsOnto.preserves honto) hmn) :=
  (tSOf.map_bijmaps_ontoinj honto hinj hmn).1

/-- Equality reflection for embedded-term maps under termwise-onto injective maps. -/
theorem tSOf.mapapp_eqapp_mapso
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (x y : tSOf F hmn) :
    tSOf.map (MapsOnto.preserves honto) hmn x =
        tSOf.map (MapsOnto.preserves honto) hmn y ↔ x = y := by
  constructor
  · intro hxy
    exact (tSOf.map_injmaps_ontoinj honto hinj hmn) hxy
  · intro h
    simp [h]

/-- One-reflection form for embedded-term maps under termwise-onto injective maps. -/
@[simp] theorem tSOf.mapapply_eqoneiff_mapsontoinj
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (hmn : m ≤ n) (x : tSOf F hmn) :
    tSOf.map (MapsOnto.preserves honto) hmn x = 1 ↔ x = 1 := by
  simpa using
    (tSOf.mapapp_eqapp_mapso
      honto hinj hmn x 1)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Characterize forward images for same-index quotient equivalences. -/
theorem onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : G ⧸ F n) (y : H ⧸ E n) :
    quotientMap (MapsOnto.preserves honto) n x = y ↔
      x = (quotientOntoInjective honto hinj n).symm y := by
  let e := quotientOntoInjective honto hinj n
  change e x = y ↔ x = e.symm y
  constructor
  · intro h
    rw [← h]
    exact (e.left_inv x).symm
  · intro h
    rw [h]
    exact e.right_inv y

/-- Composition law for same-index quotient equivalences from onto-injective maps. -/
theorem quotient_injective_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    quotientOntoInjective (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (quotientOntoInjective hφ hinjφ n).trans
        (quotientOntoInjective hψ hinjψ n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for same-index quotient equivalences from onto-injective maps. -/
@[simp] theorem quotient_injective_id
    (F : DFilt G) (n : ℕ) :
    quotientOntoInjective (mapsOnto_id F) (fun _ _ h => h) n =
      MulEquiv.refl (G ⧸ F n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Characterize forward images for arbitrary term-quotient equivalences. -/
theorem term_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n)
    (x : F m ⧸ tSOf F h) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h x = y ↔
      x = (termMapsInjective honto hinj h).symm y := by
  let e := termMapsInjective honto hinj h
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Composition law for arbitrary term-quotient equivalences. -/
theorem term_equiv_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (h : m ≤ n) :
    termMapsInjective (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) h =
      (termMapsInjective hφ hinjφ h).trans
        (termMapsInjective hψ hinjψ h) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for arbitrary term-quotient equivalences. -/
@[simp] theorem term_injective_id
    (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    termMapsInjective (mapsOnto_id F) (fun _ _ hx => hx) h =
      MulEquiv.refl (F m ⧸ tSOf F h) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Characterize forward images for transition-kernel equivalences. -/
theorem transition_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) {m n : ℕ} (h : m ≤ n)
    (x : MonoidHom.ker (quotientTransition F h))
    (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = y ↔
      x = (transitionOntoInjective honto hinj h).symm y := by
  let e := transitionOntoInjective honto hinj h
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Injective onto maps reflect equality on arbitrary transition kernels. -/
theorem transition_kernel_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n)
    (x y : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x =
        transitionKernelMap (MapsOnto.preserves honto) h y ↔ x = y := by
  constructor
  · intro hxy
    exact (transition_injective_onto honto hinj h) hxy
  · intro hxy
    rw [hxy]

/-- Injective onto maps reflect the identity on arbitrary transition kernels. -/
theorem transition_one_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = 1 ↔ x = 1 := by
  simpa using
    (transition_kernel_injective
      honto hinj h x 1)

/-- Identity law for transition-kernel equivalences from onto-injective maps. -/
@[simp] theorem transition_injective_id
    (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    transitionOntoInjective (mapsOnto_id F) (fun _ _ hx => hx) h =
      MulEquiv.refl (MonoidHom.ker (quotientTransition F h)) := by
  ext x
  simp [kernel_equiv_maps]

/-- Composition law for transition-kernel equivalences from onto-injective maps. -/
theorem transition_injective_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ)
    {m n : ℕ} (h : m ≤ n) :
    transitionOntoInjective (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) h =
      (transitionOntoInjective hφ hinjφ h).trans
        (transitionOntoInjective hψ hinjψ h) := by
  apply MulEquiv.toMonoidHom_injective
  change transitionKernelMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) h =
    (transitionKernelMap (MapsOnto.preserves hψ) h).comp
      (transitionKernelMap (MapsOnto.preserves hφ) h)
  exact kernel_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) h

/-- Characterize forward images for small-kernel transition-kernel equivalences. -/
theorem transition_kernel_equiv
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n)
    (x : MonoidHom.ker (quotientTransition F h))
    (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = y ↔
      x = (transitionMapsOnto honto h hker).symm y := by
  let e := transitionMapsOnto honto h hker
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for monotone small-kernel transition-kernel equivalences. -/
theorem transition_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h))
    (y : MonoidHom.ker (quotientTransition E h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = y ↔
      x = (transitionOntoKer honto h hker hnk).symm y := by
  let e := transitionOntoKer honto h hker hnk
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Small-kernel transition maps reflect equality. -/
theorem transition_kernel_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n)
    (x y : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x =
        transitionKernelMap (MapsOnto.preserves honto) h y ↔ x = y := by
  constructor
  · intro hxy
    exact (transition_injective_ker honto h hker) hxy
  · intro hxy
    rw [hxy]

/-- Small-kernel transition maps reflect the identity. -/
theorem transition_one_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = 1 ↔ x = 1 := by
  simpa using
    (transition_kernel_maps
      honto h hker x 1)

/-- Monotone small-kernel transition maps reflect equality. -/
theorem transition_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x y : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x =
        transitionKernelMap (MapsOnto.preserves honto) h y ↔ x = y :=
  transition_kernel_maps
    honto h (honto.ker_le_lea hker hnk) x y

/-- Monotone small-kernel transition maps reflect the identity. -/
theorem transition_kernel_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionKernelMap (MapsOnto.preserves honto) h x = 1 ↔ x = 1 :=
  transition_one_ker
    honto h (honto.ker_le_lea hker hnk) x

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Characterize forward images for small-kernel same-index quotient equivalences. -/
theorem maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F n)
    (x : G ⧸ F n) (y : H ⧸ E n) :
    quotientMap (MapsOnto.preserves honto) n x = y ↔
      x = (quotientMapsKer honto hker).symm y := by
  let e := quotientMapsKer honto hker
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for monotone small-kernel quotient equivalences. -/
theorem equiv_onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n)
    (x : G ⧸ F m) (y : H ⧸ E m) :
    quotientMap (MapsOnto.preserves honto) m x = y ↔
      x = (quotientOntoKer honto hker hmn).symm y := by
  let e := quotientOntoKer honto hker hmn
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for small-kernel arbitrary term-quotient equivalences. -/
theorem term_quotient_equiv
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n)
    (x : F m ⧸ tSOf F h) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h x = y ↔
      x = (termMapsOnto honto h hker).symm y := by
  let e := termMapsOnto honto h hker
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for monotone small-kernel term-quotient equivalences. -/
theorem term_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : F m ⧸ tSOf F h) (y : E m ⧸ tSOf E h) :
    termQuotient (MapsOnto.preserves honto) h x = y ↔
      x = (termMapsKer honto h hker hnk).symm y := by
  let e := termMapsKer honto h hker hnk
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Small-kernel quotient maps reflect equality. -/
theorem quotient_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F n)
    (x y : G ⧸ F n) :
    quotientMap (MapsOnto.preserves honto) n x =
        quotientMap (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact ((injective_maps_onto honto).2 hker) hxy
  · intro hxy
    rw [hxy]

/-- Small-kernel quotient maps reflect the identity. -/
theorem one_onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F n)
    (x : G ⧸ F n) :
    quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using
    (quotient_maps_onto honto hker x 1)

/-- Monotone small-kernel quotient maps reflect equality. -/
theorem quotient_onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n)
    (x y : G ⧸ F m) :
    quotientMap (MapsOnto.preserves honto) m x =
        quotientMap (MapsOnto.preserves honto) m y ↔ x = y :=
  quotient_maps_onto
    honto (honto.ker_le_lea hker hmn) x y

/-- Monotone small-kernel quotient maps reflect the identity. -/
theorem quotient_maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (hker : φ.ker ≤ F n) (hmn : m ≤ n)
    (x : G ⧸ F m) :
    quotientMap (MapsOnto.preserves honto) m x = 1 ↔ x = 1 :=
  one_onto_ker
    honto (honto.ker_le_lea hker hmn) x

/-- Small-kernel term-quotient maps reflect equality. -/
theorem term_quotient_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n)
    (x y : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x =
        termQuotient (MapsOnto.preserves honto) h y ↔ x = y := by
  constructor
  · intro hxy
    exact (term_injective_ker
      honto h hker) hxy
  · intro hxy
    rw [hxy]

/-- Small-kernel term-quotient maps reflect the identity. -/
theorem term_one_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F n) (x : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x = 1 ↔ x = 1 := by
  simpa using
    (term_quotient_ker
      honto h hker x 1)

/-- Monotone small-kernel term-quotient maps reflect equality. -/
theorem term_maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x y : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x =
        termQuotient (MapsOnto.preserves honto) h y ↔ x = y :=
  term_quotient_ker
    honto h (honto.ker_le_lea hker hnk) x y

/-- Monotone small-kernel term-quotient maps reflect the identity. -/
theorem term_maps_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {m n k : ℕ} (h : m ≤ n)
    (hker : φ.ker ≤ F k) (hnk : n ≤ k)
    (x : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x = 1 ↔ x = 1 :=
  term_one_ker
    honto h (honto.ker_le_lea hker hnk) x

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G : Type*} [Group G]

/-- The kernel of the identity homomorphism is contained in every filtration term. -/
theorem id_ker_le (F : DFilt G) (n : ℕ) :
    (MonoidHom.id G).ker ≤ F n := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  change x = 1 at hx
  rw [hx]
  exact Subgroup.one_mem _

/-- Identity law for small-kernel same-index quotient equivalences. -/
@[simp] theorem quotient_onto_id
    (F : DFilt G) (n : ℕ) :
    quotientMapsKer (mapsOnto_id F) (id_ker_le F n) =
      MulEquiv.refl (G ⧸ F n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for monotone small-kernel quotient equivalences. -/
@[simp] theorem maps_ker_id
    (F : DFilt G) {m n : ℕ} (hmn : m ≤ n) :
    quotientOntoKer (mapsOnto_id F) (id_ker_le F n) hmn =
      MulEquiv.refl (G ⧸ F m) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for small-kernel arbitrary term-quotient equivalences. -/
@[simp] theorem term_ker_id
    (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    termMapsOnto (mapsOnto_id F) h (id_ker_le F n) =
      MulEquiv.refl (F m ⧸ tSOf F h) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for monotone small-kernel arbitrary term-quotient equivalences. -/
@[simp] theorem term_onto_id
    (F : DFilt G) {m n k : ℕ} (h : m ≤ n) (hnk : n ≤ k) :
    termMapsKer (mapsOnto_id F) h (id_ker_le F k) hnk =
      MulEquiv.refl (F m ⧸ tSOf F h) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G : Type*} [Group G]

/-- Identity law for small-kernel transition-kernel equivalences. -/
@[simp] theorem transition_ker_id
    (F : DFilt G) {m n : ℕ} (h : m ≤ n) :
    transitionMapsOnto (mapsOnto_id F) h (id_ker_le F n) =
      MulEquiv.refl (MonoidHom.ker (quotientTransition F h)) := by
  ext x
  simp [kernel_equiv_ker]

/-- Identity law for monotone small-kernel transition-kernel equivalences. -/
@[simp] theorem transition_onto_id
    (F : DFilt G) {m n k : ℕ} (h : m ≤ n) (hnk : n ≤ k) :
    transitionOntoKer (mapsOnto_id F) h (id_ker_le F k) hnk =
      MulEquiv.refl (MonoidHom.ker (quotientTransition F h)) := by
  ext x
  simp [kernel_maps_onto]

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Onto-injective quotient maps reflect equality. -/
theorem quotient_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x y : G ⧸ F n) :
    quotientMap (MapsOnto.preserves honto) n x =
        quotientMap (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact (quotient_injective_onto honto hinj n) hxy
  · intro hxy
    rw [hxy]

/-- Onto-injective quotient maps reflect the identity. -/
theorem one_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : G ⧸ F n) :
    quotientMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using
    (quotient_onto_injective honto hinj n x 1)

/-- Onto-injective term-quotient maps reflect equality. -/
theorem term_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x y : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x =
        termQuotient (MapsOnto.preserves honto) h y ↔ x = y := by
  constructor
  · intro hxy
    exact (term_injective_onto
      honto hinj h) hxy
  · intro hxy
    rw [hxy]

/-- Onto-injective term-quotient maps reflect the identity. -/
theorem term_quotient_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ)
    {m n : ℕ} (h : m ≤ n) (x : F m ⧸ tSOf F h) :
    termQuotient (MapsOnto.preserves honto) h x = 1 ↔ x = 1 := by
  simpa using
    (term_maps_injective
      honto hinj h x 1)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Characterize forward images for onto-injective consecutive-term quotient equivalences. -/
theorem next_equiv_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : F n ⧸ nextTermSubgroup F n) (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoInjective honto hinj n).symm y := by
  let e := nextOntoInjective honto hinj n
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for small-kernel consecutive-term quotient equivalences. -/
theorem next_equiv_maps
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (x : F n ⧸ nextTermSubgroup F n) (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextMapsKer honto n hker).symm y := by
  let e := nextMapsKer honto n hker
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for monotone small-kernel consecutive-term quotient equivalences. -/
theorem next_term_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) (y : E n ⧸ nextTermSubgroup E n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = y ↔
      x = (nextOntoKer honto n hker hnk).symm y := by
  let e := nextOntoKer honto n hker hnk
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for onto-injective layer-kernel equivalences. -/
theorem layer_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : lKern F n) (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoInjective honto hinj n).symm y := by
  let e := layerOntoInjective honto hinj n
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for small-kernel layer-kernel equivalences. -/
theorem layer_onto
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) (hker : φ.ker ≤ F (n + 1))
    (x : lKern F n) (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerMapsKer honto n hker).symm y := by
  let e := layerMapsKer honto n hker
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

/-- Characterize forward images for monotone small-kernel layer-kernel equivalences. -/
theorem layer_equiv_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : lKern F n) (y : lKern E n) :
    layerMap (MapsOnto.preserves honto) n x = y ↔
      x = (layerOntoKer honto n hker hnk).symm y := by
  let e := layerOntoKer honto n hker hnk
  change e x = y ↔ x = e.symm y
  constructor
  · intro hxy
    rw [← hxy]
    exact (e.left_inv x).symm
  · intro hxy
    rw [hxy]
    exact e.right_inv y

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H : Type*} [Group G] [Group H]

/-- Onto-injective consecutive-term quotient maps reflect equality. -/
theorem next_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x y : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x =
        nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact (next_bijective_injective honto hinj n).1 hxy
  · intro hxy
    rw [hxy]

/-- Onto-injective consecutive-term quotient maps reflect the identity. -/
theorem next_quotient_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using
    (next_onto_injective
      honto hinj n x 1)

/-- Small-kernel consecutive-term quotient maps reflect equality. -/
theorem next_term_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1))
    (x y : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x =
        nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact (next_bijective_maps honto hker).1 hxy
  · intro hxy
    rw [hxy]

/-- Small-kernel consecutive-term quotient maps reflect the identity. -/
theorem next_quotient_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1))
    (x : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using
    (next_term_ker honto hker x 1)

/-- Monotone small-kernel consecutive-term quotient maps reflect equality. -/
theorem next_onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x y : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x =
        nextTermQuotient (MapsOnto.preserves honto) n y ↔ x = y :=
  next_term_ker
    honto (honto.ker_le_lea hker hnk) x y

/-- Monotone small-kernel consecutive-term quotient maps reflect the identity. -/
theorem next_maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextTermQuotient (MapsOnto.preserves honto) n x = 1 ↔ x = 1 :=
  next_quotient_ker
    honto (honto.ker_le_lea hker hnk) x

/-- Onto-injective layer maps reflect equality. -/
theorem layer_onto_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x y : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x =
        layerMap (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact (layer_bijective_injective honto hinj n).1 hxy
  · intro hxy
    rw [hxy]

/-- Onto-injective layer maps reflect the identity. -/
theorem one_maps_injective
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (hinj : Function.Injective φ) (n : ℕ)
    (x : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using (layer_onto_injective honto hinj n x 1)

/-- Small-kernel layer maps reflect equality. -/
theorem onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1))
    (x y : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x =
        layerMap (MapsOnto.preserves honto) n y ↔ x = y := by
  constructor
  · intro hxy
    exact (layer_bijective_maps honto hker).1 hxy
  · intro hxy
    rw [hxy]

/-- Small-kernel layer maps reflect the identity. -/
theorem one_maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) {n : ℕ} (hker : φ.ker ≤ F (n + 1))
    (x : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1 := by
  simpa using (onto_ker honto hker x 1)

/-- Monotone small-kernel layer maps reflect equality. -/
theorem layer_onto_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x y : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x =
        layerMap (MapsOnto.preserves honto) n y ↔ x = y :=
  onto_ker
    honto (honto.ker_le_lea hker hnk) x y

/-- Monotone small-kernel layer maps reflect the identity. -/
theorem layer_maps_ker
    {F : DFilt G} {E : DFilt H} {φ : G →* H}
    (honto : MapsOnto F E φ) (n : ℕ) {k : ℕ}
    (hker : φ.ker ≤ F k) (hnk : n + 1 ≤ k)
    (x : lKern F n) :
    layerMap (MapsOnto.preserves honto) n x = 1 ↔ x = 1 :=
  one_maps_ker
    honto (honto.ker_le_lea hker hnk) x

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G : Type*} [Group G]

/-- Identity law for onto-injective consecutive-term quotient equivalences. -/
@[simp] theorem next_injective_id
    (F : DFilt G) (n : ℕ) :
    nextOntoInjective (mapsOnto_id F) (fun _ _ h => h) n =
      MulEquiv.refl (F n ⧸ nextTermSubgroup F n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for small-kernel consecutive-term quotient equivalences. -/
@[simp] theorem next_maps_id
    (F : DFilt G) (n : ℕ) :
    nextMapsKer (mapsOnto_id F) n (id_ker_le F (n + 1)) =
      MulEquiv.refl (F n ⧸ nextTermSubgroup F n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for monotone small-kernel consecutive-term quotient equivalences. -/
@[simp] theorem next_onto_id
    (F : DFilt G) (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    nextOntoKer (mapsOnto_id F) n
        (id_ker_le F k) hnk =
      MulEquiv.refl (F n ⧸ nextTermSubgroup F n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Identity law for onto-injective layer-kernel equivalences. -/
@[simp] theorem layer_injective_id
    (F : DFilt G) (n : ℕ) :
    layerOntoInjective (mapsOnto_id F) (fun _ _ h => h) n =
      MulEquiv.refl (lKern F n) := by
  ext x
  simp [equiv_injective]

/-- Identity law for small-kernel layer-kernel equivalences. -/
@[simp] theorem layer_maps_id
    (F : DFilt G) (n : ℕ) :
    layerMapsKer (mapsOnto_id F) n (id_ker_le F (n + 1)) =
      MulEquiv.refl (lKern F n) := by
  ext x
  simp [layer_maps]

/-- Identity law for monotone small-kernel layer-kernel equivalences. -/
@[simp] theorem layer_onto_id
    (F : DFilt G) (n : ℕ) {k : ℕ} (hnk : n + 1 ≤ k) :
    layerOntoKer (mapsOnto_id F) n (id_ker_le F k) hnk =
      MulEquiv.refl (lKern F n) := by
  ext x
  simp [layer_ker]

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for onto-injective consecutive-term quotient equivalences. -/
theorem next_injective_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    nextOntoInjective (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (nextOntoInjective hφ hinjφ n).trans
        (nextOntoInjective hψ hinjψ n) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for onto-injective layer-kernel equivalences. -/
theorem layer_injective_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ)
    (hinjφ : Function.Injective φ) (hinjψ : Function.Injective ψ) (n : ℕ) :
    layerOntoInjective (MapsOnto.comp hφ hψ)
        (fun _ _ hxy => hinjφ (hinjψ hxy)) n =
      (layerOntoInjective hφ hinjφ n).trans
        (layerOntoInjective hψ hinjψ n) := by
  apply MulEquiv.toMonoidHom_injective
  change layerMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) n =
    (layerMap (MapsOnto.preserves hψ) n).comp
      (layerMap (MapsOnto.preserves hφ) n)
  exact layerMap_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) n

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Kernel containment for a composite of termwise-onto maps, assuming containment at
the same level for both factors. -/
theorem MapsOnto.comp_kerle_samelevel
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (_hψ : MapsOnto E D ψ) {n : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E n) :
    (ψ.comp φ).ker ≤ F n := by
  intro x hx
  have hxψ : φ x ∈ ψ.ker := by
    change ψ (φ x) = 1
    exact hx
  have hxE : φ x ∈ E n := hkψ hxψ
  have hxcomap : x ∈ (E n).comap φ := hxE
  have hcomap : (E n).comap φ = F n :=
    (MapsOnto.comap_eqiff_kerle hφ n).2 hkφ
  simpa [hcomap] using hxcomap

/-- Composition law for small-kernel consecutive-term quotient equivalences. -/
theorem next_term_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ)
    (hkφ : φ.ker ≤ F (n + 1)) (hkψ : ψ.ker ≤ E (n + 1)) :
    nextMapsKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (nextMapsKer hφ n hkφ).trans
        (nextMapsKer hψ n hkψ) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for small-kernel layer-kernel equivalences. -/
theorem equiv_maps_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ)
    (hkφ : φ.ker ≤ F (n + 1)) (hkψ : ψ.ker ≤ E (n + 1)) :
    layerMapsKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (layerMapsKer hφ n hkφ).trans
        (layerMapsKer hψ n hkψ) := by
  apply MulEquiv.toMonoidHom_injective
  change layerMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) n =
    (layerMap (MapsOnto.preserves hψ) n).comp
      (layerMap (MapsOnto.preserves hφ) n)
  exact layerMap_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) n

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for monotone small-kernel consecutive quotient equivalences
at a common depth. -/
theorem next_same_level
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E k) (hnk : n + 1 ≤ k) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (nextOntoKer hφ n hkφ hnk).trans
        (nextOntoKer hψ n hkψ hnk) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for monotone small-kernel layer equivalences at a common depth. -/
theorem layer_same_level
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E k) (hnk : n + 1 ≤ k) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (layerOntoKer hφ n hkφ hnk).trans
        (layerOntoKer hψ n hkψ hnk) := by
  apply MulEquiv.toMonoidHom_injective
  change layerMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) n =
    (layerMap (MapsOnto.preserves hψ) n).comp
      (layerMap (MapsOnto.preserves hφ) n)
  exact layerMap_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) n

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for small-kernel same-index quotient equivalences. -/
theorem quotient_ker_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {n : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E n) :
    quotientMapsKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (quotientMapsKer hφ hkφ).trans
        (quotientMapsKer hψ hkψ) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for small-kernel arbitrary term-quotient equivalences. -/
theorem term_quotient_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E n) :
    termMapsOnto (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (termMapsOnto hφ h hkφ).trans
        (termMapsOnto hψ h hkψ) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for small-kernel transition-kernel equivalences. -/
theorem transition_equiv_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E n) :
    transitionMapsOnto (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) =
      (transitionMapsOnto hφ h hkφ).trans
        (transitionMapsOnto hψ h hkψ) := by
  apply MulEquiv.toMonoidHom_injective
  change transitionKernelMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) h =
    (transitionKernelMap (MapsOnto.preserves hψ) h).comp
      (transitionKernelMap (MapsOnto.preserves hφ) h)
  exact kernel_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) h

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composition law for monotone small-kernel same-index quotient equivalences at a common depth. -/
theorem ker_same_level
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m k : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E k) (hmk : m ≤ k) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hmk =
      (quotientOntoKer hφ hkφ hmk).trans
        (quotientOntoKer hψ hkψ hmk) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for monotone small-kernel term-quotient equivalences at a common depth. -/
theorem term_same_level
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E k) (hnk : n ≤ k) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (termMapsKer hφ h hkφ hnk).trans
        (termMapsKer hψ h hkψ hnk) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Composition law for monotone small-kernel transition-kernel equivalences at a common depth. -/
theorem transition_same_level
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E k) (hnk : n ≤ k) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_samelevel hφ hψ hkφ hkψ) hnk =
      (transitionOntoKer hφ h hkφ hnk).trans
        (transitionOntoKer hψ h hkψ hnk) := by
  apply MulEquiv.toMonoidHom_injective
  change transitionKernelMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) h =
    (transitionKernelMap (MapsOnto.preserves hψ) h).comp
      (transitionKernelMap (MapsOnto.preserves hφ) h)
  exact kernel_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) h

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Kernel containment for a composite when the two factor kernels are known at
(possibly different) deeper levels. -/
theorem MapsOnto.comp_ker_lele
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {n a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hna : n ≤ a) (hnb : n ≤ b) :
    (ψ.comp φ).ker ≤ F n :=
  MapsOnto.comp_kerle_samelevel hφ hψ
    (hφ.ker_le_lea hkφ hna) (hψ.ker_le_lea hkψ hnb)

/-- Heterogeneous-depth composition law for monotone small-kernel quotient equivalences. -/
theorem quotient_maps_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk =
      (quotientOntoKer hφ hkφ (le_trans hmk hka)).trans
        (quotientOntoKer hψ hkψ (le_trans hmk hkb)) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Heterogeneous-depth composition law for monotone small-kernel term-quotient equivalences. -/
theorem term_ker_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).trans
        (termMapsKer hψ h hkψ (le_trans hnk hkb)) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Heterogeneous-depth composition law for monotone small-kernel transition-kernel equivalences. -/
theorem transition_kernel_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).trans
        (transitionOntoKer hψ h hkψ (le_trans hnk hkb)) := by
  apply MulEquiv.toMonoidHom_injective
  change transitionKernelMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) h =
    (transitionKernelMap (MapsOnto.preserves hψ) h).comp
      (transitionKernelMap (MapsOnto.preserves hφ) h)
  exact kernel_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) h

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Heterogeneous-depth composition law for monotone small-kernel consecutive-term quotients. -/
theorem next_ker_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (nextOntoKer hψ n hkψ (le_trans hnk hkb)) := by
  ext q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- Heterogeneous-depth composition law for monotone small-kernel layer equivalences. -/
theorem layer_ker_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (layerOntoKer hψ n hkψ (le_trans hnk hkb)) := by
  apply MulEquiv.toMonoidHom_injective
  change layerMap (MapsOnto.preserves (MapsOnto.comp hφ hψ)) n =
    (layerMap (MapsOnto.preserves hψ) n).comp (layerMap (MapsOnto.preserves hφ) n)
  exact layerMap_comp (MapsOnto.preserves hφ) (MapsOnto.preserves hψ) n

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Inverse pointwise form of heterogeneous-depth quotient-equivalence composition. -/
theorem maps_ker_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k) (z : K ⧸ D m) :
    (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmk hka)).symm
        ((quotientOntoKer hψ hkψ (le_trans hmk hkb)).symm z) := by
  rw [quotient_maps_comp (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hmk := hmk)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Inverse pointwise form of heterogeneous-depth term-quotient composition. -/
theorem term_ker_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : D m ⧸ tSOf D h) :
    (termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ h hkψ (le_trans hnk hkb)).symm z) := by
  rw [term_ker_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise form of heterogeneous-depth transition-kernel composition. -/
theorem transition_ker_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (quotientTransition D h)) :
    (transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ h hkψ (le_trans hnk hkb)).symm z) := by
  rw [transition_kernel_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise form of heterogeneous-depth consecutive-quotient composition. -/
theorem next_maps_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : D n ⧸ nextTermSubgroup D n) :
    (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z) := by
  rw [next_ker_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise form of heterogeneous-depth layer-kernel composition. -/
theorem layer_maps_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : lKern D n) :
    (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z) := by
  rw [layer_ker_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Pointwise form of heterogeneous-depth quotient-equivalence composition. -/
theorem quotient_onto_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hmk : m ≤ k) (x : G ⧸ F m) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hmk x =
      quotientOntoKer hψ hkψ (le_trans hmk hkb)
        (quotientOntoKer hφ hkφ (le_trans hmk hka) x) := by
  rw [quotient_maps_comp (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hmk := hmk)]
  rfl

/-- Pointwise form of heterogeneous-depth term-quotient composition. -/
theorem term_onto_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : F m ⧸ tSOf F h) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      termMapsKer hψ h hkψ (le_trans hnk hkb)
        (termMapsKer hφ h hkφ (le_trans hnk hka) x) := by
  rw [term_ker_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise form of heterogeneous-depth transition-kernel composition. -/
theorem transition_ker_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      transitionOntoKer hψ h hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ h hkφ (le_trans hnk hka) x) := by
  rw [transition_kernel_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise form of heterogeneous-depth consecutive-quotient composition. -/
theorem next_onto_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x) := by
  rw [next_ker_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise form of heterogeneous-depth layer-kernel composition. -/
theorem layer_onto_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b)
    (hka : k ≤ a) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : lKern F n) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hka hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x) := by
  rw [layer_ker_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hkb := hkb) (hnk := hnk)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composite-kernel containment when the left kernel is known at the target level and
the right kernel is known at a deeper level. -/
theorem MapsOnto.comp_kerle_leftle
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {n b : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E b) (hnb : n ≤ b) :
    (ψ.comp φ).ker ≤ F n :=
  MapsOnto.comp_ker_lele hφ hψ hkφ hkψ le_rfl hnb

/-- Composite-kernel containment when the right kernel is known at the target level and
the left kernel is known at a deeper level. -/
theorem MapsOnto.comp_kerle_rightle
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {a n : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E n) (hna : n ≤ a) :
    (ψ.comp φ).ker ≤ F n :=
  MapsOnto.comp_ker_lele hφ hψ hkφ hkψ hna le_rfl

/-- Succ-specialized composite-kernel containment: kernels lying in the next terms give
containment in the current source term. -/
theorem MapsOnto.comp_ker_lesucc
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {n : ℕ}
    (hkφ : φ.ker ≤ F (n + 1)) (hkψ : ψ.ker ≤ E (n + 1)) :
    (ψ.comp φ).ker ≤ F n :=
  MapsOnto.comp_ker_lele hφ hψ hkφ hkψ (Nat.le_succ n) (Nat.le_succ n)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Composite-kernel containment at the minimum of two available kernel depths. -/
theorem MapsOnto.comp_ker_lemin
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) :
    (ψ.comp φ).ker ≤ F (min a b) :=
  MapsOnto.comp_ker_lele hφ hψ hkφ hkψ (Nat.min_le_left a b) (Nat.min_le_right a b)

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Minimum-depth specialization of heterogeneous quotient-equivalence composition. -/
theorem onto_ker_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hm : m ≤ min a b) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm =
      (quotientOntoKer hφ hkφ (le_trans hm (Nat.min_le_left a b))).trans
        (quotientOntoKer hψ hkψ (le_trans hm (Nat.min_le_right a b))) := by
  exact quotient_maps_comp hφ hψ hkφ hkψ
    (Nat.min_le_left a b) (Nat.min_le_right a b) hm

/-- Minimum-depth specialization of heterogeneous term-quotient composition. -/
theorem term_onto_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (termMapsKer hφ h hkφ (le_trans hn (Nat.min_le_left a b))).trans
        (termMapsKer hψ h hkψ (le_trans hn (Nat.min_le_right a b))) := by
  exact term_ker_comp hφ hψ h hkφ hkψ
    (Nat.min_le_left a b) (Nat.min_le_right a b) hn

/-- Minimum-depth specialization of heterogeneous transition-kernel composition. -/
theorem transition_maps_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (transitionOntoKer hφ h hkφ
          (le_trans hn (Nat.min_le_left a b))).trans
        (transitionOntoKer hψ h hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  exact transition_kernel_comp hφ hψ h hkφ hkψ
    (Nat.min_le_left a b) (Nat.min_le_right a b) hn

/-- Minimum-depth specialization of heterogeneous consecutive-quotient composition. -/
theorem next_onto_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (nextOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b))).trans
        (nextOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))) := by
  exact next_ker_comp hφ hψ n hkφ hkψ
    (Nat.min_le_left a b) (Nat.min_le_right a b) hn

/-- Minimum-depth specialization of heterogeneous layer-kernel composition. -/
theorem layer_onto_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn =
      (layerOntoKer hφ n hkφ (le_trans hn (Nat.min_le_left a b))).trans
        (layerOntoKer hψ n hkψ (le_trans hn (Nat.min_le_right a b))) := by
  exact layer_ker_comp hφ hψ n hkφ hkψ
    (Nat.min_le_left a b) (Nat.min_le_right a b) hn

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Pointwise minimum-depth quotient composition formula. -/
theorem maps_onto_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hm : m ≤ min a b)
    (x : G ⧸ F m) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm x =
      quotientOntoKer hψ hkψ
        (le_trans hm (Nat.min_le_right a b))
        (quotientOntoKer hφ hkφ
          (le_trans hm (Nat.min_le_left a b)) x) := by
  rw [onto_ker_min (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hm := hm)]
  rfl

/-- Pointwise minimum-depth term-quotient composition formula. -/
theorem term_comp_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b)
    (x : F m ⧸ tSOf F h) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      termMapsKer hψ h hkψ
        (le_trans hn (Nat.min_le_right a b))
        (termMapsKer hφ h hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  rw [term_onto_min (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Pointwise minimum-depth transition-kernel composition formula. -/
theorem transition_onto_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      transitionOntoKer hψ h hkψ
        (le_trans hn (Nat.min_le_right a b))
        (transitionOntoKer hφ h hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  rw [transition_maps_min (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Pointwise minimum-depth consecutive-quotient composition formula. -/
theorem next_comp_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      nextOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (nextOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  rw [next_onto_min (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Pointwise minimum-depth layer-kernel composition formula. -/
theorem layer_comp_min
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b)
    (x : lKern F n) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn x =
      layerOntoKer hψ n hkψ
        (le_trans hn (Nat.min_le_right a b))
        (layerOntoKer hφ n hkφ
          (le_trans hn (Nat.min_le_left a b)) x) := by
  rw [layer_onto_min (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Inverse pointwise minimum-depth quotient composition formula. -/
theorem maps_min_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hm : m ≤ min a b)
    (z : K ⧸ D m) :
    (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hm).symm z =
      (quotientOntoKer hφ hkφ
        (le_trans hm (Nat.min_le_left a b))).symm
        ((quotientOntoKer hψ hkψ
          (le_trans hm (Nat.min_le_right a b))).symm z) := by
  rw [onto_ker_min (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hm := hm)]
  rfl

/-- Inverse pointwise minimum-depth term-quotient composition formula. -/
theorem term_min_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b)
    (z : D m ⧸ tSOf D h) :
    (termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (termMapsKer hφ h hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((termMapsKer hψ h hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  rw [term_onto_min (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Inverse pointwise minimum-depth transition-kernel composition formula. -/
theorem transition_min_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n ≤ min a b)
    (z : MonoidHom.ker (quotientTransition D h)) :
    (transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (transitionOntoKer hφ h hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((transitionOntoKer hψ h hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  rw [transition_maps_min (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Inverse pointwise minimum-depth consecutive-quotient composition formula. -/
theorem next_min_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b)
    (z : D n ⧸ nextTermSubgroup D n) :
    (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (nextOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((nextOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  rw [next_onto_min (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

/-- Inverse pointwise minimum-depth layer-kernel composition formula. -/
theorem layer_min_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a b : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E b) (hn : n + 1 ≤ min a b)
    (z : lKern D n) :
    (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_ker_lemin hφ hψ hkφ hkψ) hn).symm z =
      (layerOntoKer hφ n hkφ
        (le_trans hn (Nat.min_le_left a b))).symm
        ((layerOntoKer hψ n hkψ
          (le_trans hn (Nat.min_le_right a b))).symm z) := by
  rw [layer_onto_min (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hn := hn)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- One-sided specialization of heterogeneous quotient-equivalence composition when the
left kernel is already known at the target depth. -/
theorem onto_ker_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n b : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E b) (hnb : n ≤ b) (hmn : m ≤ n) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn =
      (quotientOntoKer hφ hkφ hmn).trans
        (quotientOntoKer hψ hkψ (le_trans hmn hnb)) := by
  exact quotient_maps_comp hφ hψ hkφ hkψ
    (le_rfl : n ≤ n) hnb hmn

/-- One-sided specialization of heterogeneous quotient-equivalence composition when the
right kernel is already known at the target depth. -/
theorem onto_ker_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a n : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E n) (hna : n ≤ a) (hmn : m ≤ n) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).trans
        (quotientOntoKer hψ hkψ hmn) := by
  exact quotient_maps_comp hφ hψ hkφ hkψ
    hna (le_rfl : n ≤ n) hmn

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- One-sided specialization of heterogeneous term-quotient composition (left depth fixed). -/
theorem term_onto_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (termMapsKer hφ h hkφ hnk).trans
        (termMapsKer hψ h hkψ (le_trans hnk hkb)) := by
  exact term_ker_comp hφ hψ h hkφ hkψ
    (le_rfl : k ≤ k) hkb hnk

/-- One-sided specialization of heterogeneous term-quotient composition (right depth fixed). -/
theorem term_maps_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).trans
        (termMapsKer hψ h hkψ hnk) := by
  exact term_ker_comp hφ hψ h hkφ hkψ
    hka (le_rfl : k ≤ k) hnk

/-- One-sided specialization of heterogeneous transition-kernel composition (left depth fixed). -/
theorem transition_maps_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (transitionOntoKer hφ h hkφ hnk).trans
        (transitionOntoKer hψ h hkψ (le_trans hnk hkb)) := by
  exact transition_kernel_comp hφ hψ h hkφ hkψ
    (le_rfl : k ≤ k) hkb hnk

/-- One-sided specialization of heterogeneous transition-kernel composition (right depth fixed). -/
theorem transition_onto_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).trans
        (transitionOntoKer hψ h hkψ hnk) := by
  exact transition_kernel_comp hφ hψ h hkφ hkψ
    hka (le_rfl : k ≤ k) hnk

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- One-sided specialization of heterogeneous consecutive-quotient composition
(left depth fixed). -/
theorem next_onto_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (nextOntoKer hφ n hkφ hnk).trans
        (nextOntoKer hψ n hkψ (le_trans hnk hkb)) := by
  exact next_ker_comp hφ hψ n hkφ hkψ
    (le_rfl : k ≤ k) hkb hnk

/-- One-sided specialization of heterogeneous consecutive-quotient composition
(right depth fixed). -/
theorem next_maps_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (nextOntoKer hψ n hkψ hnk) := by
  exact next_ker_comp hφ hψ n hkφ hkψ
    hka (le_rfl : k ≤ k) hnk

/-- One-sided specialization of heterogeneous layer-kernel composition (left depth fixed). -/
theorem layer_onto_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk =
      (layerOntoKer hφ n hkφ hnk).trans
        (layerOntoKer hψ n hkψ (le_trans hnk hkb)) := by
  exact layer_ker_comp hφ hψ n hkφ hkψ
    (le_rfl : k ≤ k) hkb hnk

/-- One-sided specialization of heterogeneous layer-kernel composition (right depth fixed). -/
theorem layer_maps_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).trans
        (layerOntoKer hψ n hkψ hnk) := by
  exact layer_ker_comp hφ hψ n hkφ hkψ
    hka (le_rfl : k ≤ k) hnk

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Pointwise left-depth composition formula for quotient equivalences. -/
theorem maps_onto_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n b : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E b) (hnb : n ≤ b) (hmn : m ≤ n)
    (x : G ⧸ F m) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn x =
      quotientOntoKer hψ hkψ (le_trans hmn hnb)
        (quotientOntoKer hφ hkφ hmn x) := by
  rw [onto_ker_left (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hnb := hnb) (hmn := hmn)]
  rfl

/-- Pointwise right-depth composition formula for quotient equivalences. -/
theorem maps_onto_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a n : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E n) (hna : n ≤ a) (hmn : m ≤ n)
    (x : G ⧸ F m) :
    quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn x =
      quotientOntoKer hψ hkψ hmn
        (quotientOntoKer hφ hkφ (le_trans hmn hna) x) := by
  rw [onto_ker_right (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hna := hna) (hmn := hmn)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Inverse pointwise left-depth composition formula for quotient equivalences. -/
theorem comp_left_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n b : ℕ}
    (hkφ : φ.ker ≤ F n) (hkψ : ψ.ker ≤ E b) (hnb : n ≤ b) (hmn : m ≤ n)
    (z : K ⧸ D m) :
    (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hnb) hmn).symm z =
      (quotientOntoKer hφ hkφ hmn).symm
        ((quotientOntoKer hψ hkψ (le_trans hmn hnb)).symm z) := by
  rw [onto_ker_left (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hnb := hnb) (hmn := hmn)]
  rfl

/-- Inverse pointwise right-depth composition formula for quotient equivalences. -/
theorem comp_right_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m a n : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E n) (hna : n ≤ a) (hmn : m ≤ n)
    (z : K ⧸ D m) :
    (quotientOntoKer (MapsOnto.comp hφ hψ)
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hna) hmn).symm z =
      (quotientOntoKer hφ hkφ (le_trans hmn hna)).symm
        ((quotientOntoKer hψ hkψ hmn).symm z) := by
  rw [onto_ker_right (hφ := hφ) (hψ := hψ)
    (hkφ := hkφ) (hkψ := hkψ) (hna := hna) (hmn := hmn)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Pointwise left-depth composition formula for term quotients. -/
theorem term_comp_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : F m ⧸ tSOf F h) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      termMapsKer hψ h hkψ (le_trans hnk hkb)
        (termMapsKer hφ h hkφ hnk x) := by
  rw [term_onto_left (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise right-depth composition formula for term quotients. -/
theorem term_comp_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : F m ⧸ tSOf F h) :
    termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      termMapsKer hψ h hkψ hnk
        (termMapsKer hφ h hkφ (le_trans hnk hka) x) := by
  rw [term_maps_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Pointwise left-depth composition formula for transition kernels. -/
theorem transition_onto_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      transitionOntoKer hψ h hkψ (le_trans hnk hkb)
        (transitionOntoKer hφ h hkφ hnk x) := by
  rw [transition_maps_left (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise right-depth composition formula for transition kernels. -/
theorem transition_onto_comp
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k)
    (x : MonoidHom.ker (quotientTransition F h)) :
    transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      transitionOntoKer hψ h hkψ hnk
        (transitionOntoKer hφ h hkφ (le_trans hnk hka) x) := by
  rw [transition_onto_right (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Pointwise left-depth composition formula for consecutive quotients. -/
theorem next_comp_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      nextOntoKer hψ n hkψ (le_trans hnk hkb)
        (nextOntoKer hφ n hkφ hnk x) := by
  rw [next_onto_left (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise right-depth composition formula for consecutive quotients. -/
theorem next_comp_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : F n ⧸ nextTermSubgroup F n) :
    nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      nextOntoKer hψ n hkψ hnk
        (nextOntoKer hφ n hkφ (le_trans hnk hka) x) := by
  rw [next_maps_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Pointwise left-depth composition formula for layer kernels. -/
theorem layer_comp_left
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (x : lKern F n) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk x =
      layerOntoKer hψ n hkψ (le_trans hnk hkb)
        (layerOntoKer hφ n hkφ hnk x) := by
  rw [layer_onto_left (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Pointwise right-depth composition formula for layer kernels. -/
theorem layer_comp_right
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (x : lKern F n) :
    layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk x =
      layerOntoKer hψ n hkψ hnk
        (layerOntoKer hφ n hkφ (le_trans hnk hka) x) := by
  rw [layer_maps_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

end DFilt
end Submission

namespace Submission
namespace DFilt

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Inverse pointwise left-depth composition formula for term quotients. -/
theorem term_maps_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : D m ⧸ tSOf D h) :
    (termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (termMapsKer hφ h hkφ hnk).symm
        ((termMapsKer hψ h hkψ (le_trans hnk hkb)).symm z) := by
  rw [term_onto_left (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise right-depth composition formula for term quotients. -/
theorem term_onto_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : D m ⧸ tSOf D h) :
    (termMapsKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (termMapsKer hφ h hkφ (le_trans hnk hka)).symm
        ((termMapsKer hψ h hkψ hnk).symm z) := by
  rw [term_maps_comp (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Inverse pointwise left-depth composition formula for transition kernels. -/
theorem transition_maps_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n k b : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n ≤ k)
    (z : MonoidHom.ker (quotientTransition D h)) :
    (transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (transitionOntoKer hφ h hkφ hnk).symm
        ((transitionOntoKer hψ h hkψ (le_trans hnk hkb)).symm z) := by
  rw [transition_maps_left (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise right-depth composition formula for transition kernels. -/
theorem transition_onto_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) {m n a k : ℕ} (h : m ≤ n)
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n ≤ k)
    (z : MonoidHom.ker (quotientTransition D h)) :
    (transitionOntoKer (MapsOnto.comp hφ hψ) h
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (transitionOntoKer hφ h hkφ (le_trans hnk hka)).symm
        ((transitionOntoKer hψ h hkψ hnk).symm z) := by
  rw [transition_onto_right (hφ := hφ) (hψ := hψ)
    (h := h) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Inverse pointwise left-depth composition formula for consecutive quotients. -/
theorem next_onto_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : D n ⧸ nextTermSubgroup D n) :
    (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (nextOntoKer hφ n hkφ hnk).symm
        ((nextOntoKer hψ n hkψ (le_trans hnk hkb)).symm z) := by
  rw [next_onto_left (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise right-depth composition formula for consecutive quotients. -/
theorem next_comp_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : D n ⧸ nextTermSubgroup D n) :
    (nextOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (nextOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((nextOntoKer hψ n hkψ hnk).symm z) := by
  rw [next_maps_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

/-- Inverse pointwise left-depth composition formula for layer kernels. -/
theorem layer_onto_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {k b : ℕ}
    (hkφ : φ.ker ≤ F k) (hkψ : ψ.ker ≤ E b) (hkb : k ≤ b) (hnk : n + 1 ≤ k)
    (z : lKern D n) :
    (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_leftle hφ hψ hkφ hkψ hkb) hnk).symm z =
      (layerOntoKer hφ n hkφ hnk).symm
        ((layerOntoKer hψ n hkψ (le_trans hnk hkb)).symm z) := by
  rw [layer_onto_left (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hkb := hkb) (hnk := hnk)]
  rfl

/-- Inverse pointwise right-depth composition formula for layer kernels. -/
theorem layer_comp_symm
    {F : DFilt G} {E : DFilt H} {D : DFilt K}
    {φ : G →* H} {ψ : H →* K}
    (hφ : MapsOnto F E φ) (hψ : MapsOnto E D ψ) (n : ℕ) {a k : ℕ}
    (hkφ : φ.ker ≤ F a) (hkψ : ψ.ker ≤ E k) (hka : k ≤ a) (hnk : n + 1 ≤ k)
    (z : lKern D n) :
    (layerOntoKer (MapsOnto.comp hφ hψ) n
        (MapsOnto.comp_kerle_rightle hφ hψ hkφ hkψ hka) hnk).symm z =
      (layerOntoKer hφ n hkφ (le_trans hnk hka)).symm
        ((layerOntoKer hψ n hkψ hnk).symm z) := by
  rw [layer_maps_comp (hφ := hφ) (hψ := hψ)
    (n := n) (hkφ := hkφ) (hkψ := hkψ) (hka := hka) (hnk := hnk)]
  rfl

end DFilt
end Submission
