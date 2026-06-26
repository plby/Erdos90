import Towers.Group.Zassenhaus.Core

open scoped commutatorElement

namespace Towers
namespace GroupAlgebra

noncomputable section

variable (p : ℕ) (G : Type*) [Group G]

/-! ### Product decompositions for consecutive Zassenhaus layers -/

/-- Under the product equivalence on Zassenhaus terms, the next term is the product
of the next terms. -/
theorem next_term_prod (H : Type*) [Group H] (n : ℕ) :
    (zNTerm p (G × H) n).map
      (zassenhausProdEquiv p G H n).toMonoidHom =
    (zNTerm p G n).prod (zNTerm p H n) :=
  dimension_next_term (R := ZMod p) G H n

/-- Consecutive Zassenhaus quotients commute with binary products. -/
noncomputable def zNQuot.prodEquiv (H : Type*) [Group H] (n : ℕ) :
    (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) ≃*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n)) :=
  dNQuot.prodEquiv (R := ZMod p) G H n

@[simp] theorem zNQuot.prodEquiv_mk (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n) :
    zNQuot.prodEquiv p G H n
        (QuotientGroup.mk' (zNTerm p (G × H) n) x) =
      (QuotientGroup.mk' (zNTerm p G n)
          ((zassenhausProdEquiv p G H n x).1),
        QuotientGroup.mk' (zNTerm p H n)
          ((zassenhausProdEquiv p G H n x).2)) := rfl

@[simp] theorem zNQuot.prod_equiv_symmmk (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p G n) (y : zSubgro p H n) :
    (zNQuot.prodEquiv p G H n).symm
        (QuotientGroup.mk' (zNTerm p G n) x,
          QuotientGroup.mk' (zNTerm p H n) y) =
      QuotientGroup.mk' (zNTerm p (G × H) n)
        ((zassenhausProdEquiv p G H n).symm (x, y)) :=
  dNQuot.prod_equiv_symmmk (R := ZMod p) G H n x y

/-- Cardinality formula for consecutive Zassenhaus quotients of products. -/
theorem nat_zassenhaus_prod (H : Type*) [Group H] (n : ℕ) :
    Nat.card (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) =
      Nat.card (zSubgro p G n ⧸ zNTerm p G n) *
        Nat.card (zSubgro p H n ⧸ zNTerm p H n) :=
  dimension_next_prod (R := ZMod p) G H n

/-- Zassenhaus layer kernels commute with binary products. -/
noncomputable def zLKern.prodEquiv (H : Type*) [Group H] (n : ℕ) :
    zLKern p (G × H) n ≃*
      (zLKern p G n × zLKern p H n) :=
  dLKern.prodEquiv (R := ZMod p) G H n

@[simp] theorem zLKern.prod_equiv_term (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n) :
    zLKern.prodEquiv p G H n (zLKern.ofTerm p (G × H) n x) =
      (zLKern.ofTerm p G n ((zassenhausProdEquiv p G H n x).1),
        zLKern.ofTerm p H n ((zassenhausProdEquiv p G H n x).2)) :=
  dLKern.prod_equiv_term (R := ZMod p) G H n x

@[simp] theorem zLKern.prod_equiv_symmterm (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p G n) (y : zSubgro p H n) :
    (zLKern.prodEquiv p G H n).symm
        (zLKern.ofTerm p G n x,
          zLKern.ofTerm p H n y) =
      zLKern.ofTerm p (G × H) n
        ((zassenhausProdEquiv p G H n).symm (x, y)) :=
  dLKern.prod_equiv_symmterm (R := ZMod p) G H n x y

/-- Additive form of the product equivalence for consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.prodAddEquiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) ≃+
      (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
{ toFun := fun x =>
    (Additive.ofMul ((zNQuot.prodEquiv p G H n x.toMul).1),
      Additive.ofMul ((zNQuot.prodEquiv p G H n x.toMul).2))
  invFun := fun y =>
    Additive.ofMul ((zNQuot.prodEquiv p G H n).symm (y.1.toMul, y.2.toMul))
  left_inv := by
    intro x
    cases x using Additive.rec
    simp
  right_inv := by
    intro y
    rcases y with ⟨a, b⟩
    cases a using Additive.rec
    cases b using Additive.rec
    simp
  map_add' := by
    intro x y
    cases x using Additive.rec
    cases y using Additive.rec
    simp [ofMul_mul] }

@[simp] theorem zNQuot.prod_add_equivmul [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) (x : zSubgro p (G × H) n) :
    zNQuot.prodAddEquiv p G H n
        (Additive.ofMul (QuotientGroup.mk' (zNTerm p (G × H) n) x)) =
      (Additive.ofMul (QuotientGroup.mk' (zNTerm p G n)
          ((zassenhausProdEquiv p G H n x).1)),
        Additive.ofMul (QuotientGroup.mk' (zNTerm p H n)
          ((zassenhausProdEquiv p G H n x).2))) := rfl

/-- Linear form of the product equivalence for consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.prodLinearEquiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive
        (zSubgro p (G × H) n ⧸
          zNTerm p (G × H) n) ≃ₗ[ZMod p]
      (Additive (zSubgro p G n ⧸ zNTerm p G n) ×
        Additive (zSubgro p H n ⧸ zNTerm p H n)) :=
  let e := zNQuot.prodAddEquiv p G H n
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) <| by
    constructor
    · intro x y h
      exact e.injective h
    · intro y
      rcases e.surjective y with ⟨x, hx⟩
      exact ⟨x, hx⟩

@[simp] theorem zNQuot.prod_lin_equivapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)) :
    zNQuot.prodLinearEquiv p G H n x =
      zNQuot.prodAddEquiv p G H n x := rfl


/-- Additive form of the product equivalence for Zassenhaus layer kernels. -/
noncomputable def zLKern.prodAddEquiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive (zLKern p (G × H) n) ≃+
      (Additive (zLKern p G n) × Additive (zLKern p H n)) :=
{ toFun := fun x =>
    (Additive.ofMul ((zLKern.prodEquiv p G H n x.toMul).1),
      Additive.ofMul ((zLKern.prodEquiv p G H n x.toMul).2))
  invFun := fun y =>
    Additive.ofMul ((zLKern.prodEquiv p G H n).symm (y.1.toMul, y.2.toMul))
  left_inv := by
    intro x
    cases x using Additive.rec
    simp
  right_inv := by
    intro y
    rcases y with ⟨a, b⟩
    cases a using Additive.rec
    cases b using Additive.rec
    simp
  map_add' := by
    intro x y
    cases x using Additive.rec
    cases y using Additive.rec
    simp [ofMul_mul] }

@[simp] theorem zLKern.prod_add_equivterm [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) (x : zSubgro p (G × H) n) :
    zLKern.prodAddEquiv p G H n
        (Additive.ofMul (zLKern.ofTerm p (G × H) n x)) =
      (Additive.ofMul (zLKern.ofTerm p G n
          ((zassenhausProdEquiv p G H n x).1)),
        Additive.ofMul (zLKern.ofTerm p H n
          ((zassenhausProdEquiv p G H n x).2))) := by
  change (Additive.ofMul ((zLKern.prodEquiv p G H n
        (zLKern.ofTerm p (G × H) n x)).1),
      Additive.ofMul ((zLKern.prodEquiv p G H n
        (zLKern.ofTerm p (G × H) n x)).2)) = _
  rw [zLKern.prod_equiv_term]

/-- Linear form of the product equivalence for Zassenhaus layer kernels. -/
noncomputable def zLKern.prodLinearEquiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive (zLKern p (G × H) n) ≃ₗ[ZMod p]
      (Additive (zLKern p G n) × Additive (zLKern p H n)) :=
  let e := zLKern.prodAddEquiv p G H n
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) <| by
    constructor
    · intro x y h
      exact e.injective h
    · intro y
      rcases e.surjective y with ⟨x, hx⟩
      exact ⟨x, hx⟩

@[simp] theorem zLKern.prod_lin_equivapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p (G × H) n)) :
    zLKern.prodLinearEquiv p G H n x =
      zLKern.prodAddEquiv p G H n x := rfl




/-- Projecting after the left-inclusion map on consecutive Zassenhaus quotients is the identity. -/
@[simp] theorem zNQuot.map_fst_compinl (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.fst G H) n).comp
        (zNQuot.map p G (MonoidHom.inl G H) n) =
      MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← zNQuot.map_comp (p := p) (G := G) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, zNQuot.map_id]

/-- Projecting after the right-inclusion map on consecutive Zassenhaus quotients is the identity. -/
@[simp] theorem zNQuot.map_snd_compinr (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.snd G H) n).comp
        (zNQuot.map p H (MonoidHom.inr G H) n) =
      MonoidHom.id (zSubgro p H n ⧸ zNTerm p H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← zNQuot.map_comp (p := p) (G := H) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, zNQuot.map_id]


/-- The consecutive Zassenhaus quotient map induced by the first product projection
is surjective. -/
theorem zNQuot.map_fst_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zNQuot.map p (G × H) (MonoidHom.fst G H) n) := by
  intro q
  refine ⟨zNQuot.map p G (MonoidHom.inl G H) n q, ?_⟩
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The consecutive Zassenhaus quotient map induced by the second product projection
is surjective. -/
theorem zNQuot.map_snd_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zNQuot.map p (G × H) (MonoidHom.snd G H) n) := by
  intro q
  refine ⟨zNQuot.map p H (MonoidHom.inr G H) n q, ?_⟩
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The first projection map on product Zassenhaus consecutive quotients has full range. -/
theorem zNQuot.range_mapfst_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zNQuot.map_fst_surjective (p := p) (G := G) H n)

/-- The second projection map on product Zassenhaus consecutive quotients has full range. -/
theorem zNQuot.range_mapsnd_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zNQuot.map_snd_surjective (p := p) (G := G) H n)

/-- The consecutive Zassenhaus quotient map induced by the left product inclusion is injective. -/
theorem zNQuot.map_inl_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zNQuot.map p G (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (zNQuot.map p (G × H) (MonoidHom.fst G H) n)
      (zNQuot.map p G (MonoidHom.inl G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  exact hleft.injective

/-- The consecutive Zassenhaus quotient map induced by the right product inclusion is injective. -/
theorem zNQuot.map_inr_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zNQuot.map p H (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (zNQuot.map p (G × H) (MonoidHom.snd G H) n)
      (zNQuot.map p H (MonoidHom.inr G H) n) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    rfl
  exact hleft.injective

/-- The left product-inclusion map on consecutive Zassenhaus quotients has trivial kernel. -/
theorem zNQuot.ker_mapinl_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p G (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zNQuot.map_inl_injective (p := p) (G := G) H n)

/-- The right product-inclusion map on consecutive Zassenhaus quotients has trivial kernel. -/
theorem zNQuot.ker_mapinr_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p H (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zNQuot.map_inr_injective (p := p) (G := G) H n)

/-- The product equivalence carries the next-quotient map induced by the left inclusion
to the left inclusion of Zassenhaus next-quotient factors. -/
@[simp] theorem zNQuot.prodEquiv_inl (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.prodEquiv p G H n).toMonoidHom.comp
        (zNQuot.map p G (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The product equivalence carries the next-quotient map induced by the right inclusion
to the right inclusion of Zassenhaus next-quotient factors. -/
@[simp] theorem zNQuot.prodEquiv_inr (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.prodEquiv p G H n).toMonoidHom.comp
        (zNQuot.map p H (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The inverse product equivalence sends a left-factor consecutive Zassenhaus quotient
element to the map induced by the left product inclusion. -/
@[simp] theorem zNQuot.prod_equiv_symminl (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p G n ⧸ zNTerm p G n) :
    (zNQuot.prodEquiv p G H n).symm (x, 1) =
      zNQuot.map p G (MonoidHom.inl G H) n x := by
  apply (zNQuot.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : (zSubgro p G n ⧸
      zNTerm p G n) →*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n)) => f x)
    (zNQuot.prodEquiv_inl (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor consecutive Zassenhaus quotient
element to the map induced by the right product inclusion. -/
@[simp] theorem zNQuot.prod_equiv_symminr (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p H n ⧸ zNTerm p H n) :
    (zNQuot.prodEquiv p G H n).symm (1, x) =
      zNQuot.map p H (MonoidHom.inr G H) n x := by
  apply (zNQuot.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : (zSubgro p H n ⧸
      zNTerm p H n) →*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n)) => f x)
    (zNQuot.prodEquiv_inr (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The first projection after the product equivalence on consecutive Zassenhaus quotients
is the map induced by the first projection of groups. -/
@[simp] theorem zNQuot.prodEquiv_fst (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp
        (zNQuot.prodEquiv p G H n).toMonoidHom =
      zNQuot.map p (G × H) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl

/-- The second projection after the product equivalence on consecutive Zassenhaus quotients
is the map induced by the second projection of groups. -/
@[simp] theorem zNQuot.prodEquiv_snd (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp
        (zNQuot.prodEquiv p G H n).toMonoidHom =
      zNQuot.map p (G × H) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl



/-- Product equivalence on consecutive Zassenhaus quotients is the pair of projections. -/
@[simp] theorem zNQuot.prodEquiv_apply (H : Type*) [Group H]
    (n : ℕ)
    (x : zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) :
    zNQuot.prodEquiv p G H n x =
      (zNQuot.map p (G × H) (MonoidHom.fst G H) n x,
        zNQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) →*
        (zSubgro p G n ⧸ zNTerm p G n) => f x)
      (zNQuot.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) →*
        (zSubgro p H n ⧸ zNTerm p H n) => f x)
      (zNQuot.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h

/-- Every product consecutive Zassenhaus quotient element splits as the product of its
projected inclusion components. -/
theorem zNQuot.eq_inl_mulinr (H : Type*) [Group H] (n : ℕ)
    (x : zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) :
    x = zNQuot.map p G (MonoidHom.inl G H) n
          (zNQuot.map p (G × H) (MonoidHom.fst G H) n x) *
        zNQuot.map p H (MonoidHom.inr G H) n
          (zNQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
  let e := zNQuot.prodEquiv p G H n
  have hf : (e x).1 = zNQuot.map p (G × H) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) →*
        (zSubgro p G n ⧸ zNTerm p G n) => f x)
      (zNQuot.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = zNQuot.map p (G × H) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) →*
        (zSubgro p H n ⧸ zNTerm p H n) => f x)
      (zNQuot.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = zNQuot.map p G (MonoidHom.inl G H) n
          (zNQuot.map p (G × H) (MonoidHom.fst G H) n x) *
        zNQuot.map p H (MonoidHom.inr G H) n
          (zNQuot.map p (G × H) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]


/-- Left- and right-inclusion images commute in a product consecutive Zassenhaus quotient. -/
theorem zNQuot.map_inlmul_inrcomm (H : Type*) [Group H] (n : ℕ)
    (x : zSubgro p G n ⧸ zNTerm p G n)
    (y : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p G (MonoidHom.inl G H) n x *
        zNQuot.map p H (MonoidHom.inr G H) n y =
      zNQuot.map p H (MonoidHom.inr G H) n y *
        zNQuot.map p G (MonoidHom.inl G H) n x := by
  let e := zNQuot.prodEquiv p G H n
  apply e.injective
  have hx : e (zNQuot.map p G (MonoidHom.inl G H) n x) =
      (x, 1) := by
    have h := congrArg (fun f : (zSubgro p G n ⧸
        zNTerm p G n) →*
        ((zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n)) => f x)
      (zNQuot.prodEquiv_inl (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (zNQuot.map p H (MonoidHom.inr G H) n y) =
      (1, y) := by
    have h := congrArg (fun f : (zSubgro p H n ⧸
        zNTerm p H n) →*
        ((zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n)) => f y)
      (zNQuot.prodEquiv_inr (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first consecutive Zassenhaus quotient is trivial. -/
@[simp] theorem zNQuot.map_fst_compinr (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.fst G H) n).comp
        (zNQuot.map p H (MonoidHom.inr G H) n) =
      (1 : (zSubgro p H n ⧸ zNTerm p H n) →*
        (zSubgro p G n ⧸ zNTerm p G n)) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : (zSubgro p H n ⧸
      zNTerm p H n) →*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n)) => f x)
    (zNQuot.prodEquiv_inr (p := p) (G := G) H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, zNQuot.prodEquiv_apply] using hf

/-- Projecting the left-inclusion map to the second consecutive Zassenhaus quotient is trivial. -/
@[simp] theorem zNQuot.map_snd_compinl (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.snd G H) n).comp
        (zNQuot.map p G (MonoidHom.inl G H) n) =
      (1 : (zSubgro p G n ⧸ zNTerm p G n) →*
        (zSubgro p H n ⧸ zNTerm p H n)) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : (zSubgro p G n ⧸
      zNTerm p G n) →*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n)) => f x)
    (zNQuot.prodEquiv_inl (p := p) (G := G) H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, zNQuot.prodEquiv_apply] using hs

@[simp] theorem zNQuot.map_fst_inrapply (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.map p (G × H) (MonoidHom.fst G H) n
        (zNQuot.map p H (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : (zSubgro p H n ⧸
      zNTerm p H n) →*
      (zSubgro p G n ⧸ zNTerm p G n) => f x)
    (zNQuot.map_fst_compinr (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem zNQuot.map_snd_inlapply (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.map p (G × H) (MonoidHom.snd G H) n
        (zNQuot.map p G (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : (zSubgro p G n ⧸
      zNTerm p G n) →*
      (zSubgro p H n ⧸ zNTerm p H n) => f x)
    (zNQuot.map_snd_compinl (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product consecutive Zassenhaus quotient element lies in the right-inclusion range iff
its first projection is trivial. -/
theorem zNQuot.memrange_inriffmap_fsteqone (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    x ∈ (zNQuot.map p H (MonoidHom.inr G H) n).range ↔
      zNQuot.map p (G × H) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : (zSubgro p H n ⧸
        zNTerm p H n) →*
        (zSubgro p G n ⧸ zNTerm p G n) => f y)
      (zNQuot.map_fst_compinr (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zNQuot.map p (G × H) (MonoidHom.snd G H) n x, ?_⟩
    have h := zNQuot.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product consecutive Zassenhaus quotient element lies in the left-inclusion range iff
its second projection is trivial. -/
theorem zNQuot.memrange_inliffmap_sndeqone (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    x ∈ (zNQuot.map p G (MonoidHom.inl G H) n).range ↔
      zNQuot.map p (G × H) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : (zSubgro p G n ⧸
        zNTerm p G n) →*
        (zSubgro p H n ⧸ zNTerm p H n) => f y)
      (zNQuot.map_snd_compinl (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zNQuot.map p (G × H) (MonoidHom.fst G H) n x, ?_⟩
    have h := zNQuot.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product consecutive Zassenhaus quotient is the
right-inclusion range. -/
theorem zNQuot.kermap_fsteq_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.fst G H) n).ker =
      (zNQuot.map p H (MonoidHom.inr G H) n).range := by
  ext x
  exact (zNQuot.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).symm

/-- The kernel of the second projection on a product consecutive Zassenhaus quotient is the
left-inclusion range. -/
theorem zNQuot.kermap_sndeq_rangeinl (H : Type*) [Group H]
    (n : ℕ) :
    (zNQuot.map p (G × H) (MonoidHom.snd G H) n).ker =
      (zNQuot.map p G (MonoidHom.inl G H) n).range := by
  ext x
  exact (zNQuot.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).symm

/-- The left- and right-inclusion ranges in a product consecutive Zassenhaus quotient
meet only at `1`. -/
theorem zNQuot.eqone_memrangeinl_memrangeinr (H : Type*) [Group H]
    (n : ℕ) {x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n}
    (hxL : x ∈ (zNQuot.map p G (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (zNQuot.map p H (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (zNQuot.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).1 hxR
  have hsnd := (zNQuot.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).1 hxL
  have h := zNQuot.eq_inl_mulinr (p := p) (G := G) H n x
  simpa [hfst, hsnd] using h

/-- The left- and right-inclusion ranges in a product consecutive Zassenhaus quotient
are disjoint. -/
theorem zNQuot.disjoint_rangeinl_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    Disjoint (zNQuot.map p G (MonoidHom.inl G H) n).range
      (zNQuot.map p H (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact zNQuot.eqone_memrangeinl_memrangeinr
    (p := p) (G := G) H n hxL hxR

/-- Projecting after the left-inclusion map on Zassenhaus layer kernels is the identity. -/
@[simp] theorem zLKern.map_fst_compinl (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.fst G H) n).comp
        (zLKern.map p G (MonoidHom.inl G H) n) =
      MonoidHom.id (zLKern p G n) := by
  have h : (MonoidHom.fst G H).comp (MonoidHom.inl G H) = MonoidHom.id G := by
    ext g
    rfl
  rw [← zLKern.map_comp (p := p) (G := G) (MonoidHom.inl G H)
    (MonoidHom.fst G H) n, h, zLKern.map_id]

/-- Projecting after the right-inclusion map on Zassenhaus layer kernels is the identity. -/
@[simp] theorem zLKern.map_snd_compinr (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.snd G H) n).comp
        (zLKern.map p H (MonoidHom.inr G H) n) =
      MonoidHom.id (zLKern p H n) := by
  have h : (MonoidHom.snd G H).comp (MonoidHom.inr G H) = MonoidHom.id H := by
    ext h
    rfl
  rw [← zLKern.map_comp (p := p) (G := H) (MonoidHom.inr G H)
    (MonoidHom.snd G H) n, h, zLKern.map_id]

/-- The Zassenhaus layer-kernel map induced by the first product projection is surjective. -/
theorem zLKern.map_fst_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zLKern.map p (G × H) (MonoidHom.fst G H) n) := by
  intro x
  refine ⟨zLKern.map p G (MonoidHom.inl G H) n x, ?_⟩
  have h := congrArg (fun f : zLKern p G n →* zLKern p G n => f x)
    (zLKern.map_fst_compinl (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The Zassenhaus layer-kernel map induced by the second product projection is surjective. -/
theorem zLKern.map_snd_surjective (H : Type*) [Group H] (n : ℕ) :
    Function.Surjective (zLKern.map p (G × H) (MonoidHom.snd G H) n) := by
  intro x
  refine ⟨zLKern.map p H (MonoidHom.inr G H) n x, ?_⟩
  have h := congrArg (fun f : zLKern p H n →* zLKern p H n => f x)
    (zLKern.map_snd_compinr (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The first projection map on product Zassenhaus layer kernels has full range. -/
theorem zLKern.range_mapfst_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.fst G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zLKern.map_fst_surjective (p := p) (G := G) H n)

/-- The second projection map on product Zassenhaus layer kernels has full range. -/
theorem zLKern.range_mapsnd_eqtop (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.snd G H) n).range = ⊤ :=
  MonoidHom.range_eq_top_of_surjective _
    (zLKern.map_snd_surjective (p := p) (G := G) H n)

/-- The Zassenhaus layer-kernel map induced by the left product inclusion is injective. -/
theorem zLKern.map_inl_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zLKern.map p G (MonoidHom.inl G H) n) := by
  have hleft : Function.LeftInverse
      (zLKern.map p (G × H) (MonoidHom.fst G H) n)
      (zLKern.map p G (MonoidHom.inl G H) n) := by
    intro x
    have h := congrArg (fun f : zLKern p G n →* zLKern p G n => f x)
      (zLKern.map_fst_compinl (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  exact hleft.injective

/-- The Zassenhaus layer-kernel map induced by the right product inclusion is injective. -/
theorem zLKern.map_inr_injective (H : Type*) [Group H] (n : ℕ) :
    Function.Injective (zLKern.map p H (MonoidHom.inr G H) n) := by
  have hleft : Function.LeftInverse
      (zLKern.map p (G × H) (MonoidHom.snd G H) n)
      (zLKern.map p H (MonoidHom.inr G H) n) := by
    intro x
    have h := congrArg (fun f : zLKern p H n →* zLKern p H n => f x)
      (zLKern.map_snd_compinr (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  exact hleft.injective

/-- The left product-inclusion map on Zassenhaus layer kernels has trivial kernel. -/
theorem zLKern.ker_mapinl_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p G (MonoidHom.inl G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zLKern.map_inl_injective (p := p) (G := G) H n)

/-- The right product-inclusion map on Zassenhaus layer kernels has trivial kernel. -/
theorem zLKern.ker_mapinr_eqbot (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p H (MonoidHom.inr G H) n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2
    (zLKern.map_inr_injective (p := p) (G := G) H n)

/-- The product equivalence carries the layer-kernel map induced by the left inclusion
to the left inclusion of Zassenhaus layer factors. -/
@[simp] theorem zLKern.prodEquiv_inl (H : Type*) [Group H] (n : ℕ) :
    (zLKern.prodEquiv p G H n).toMonoidHom.comp
        (zLKern.map p G (MonoidHom.inl G H) n) =
      MonoidHom.inl _ _ := by
  apply MonoidHom.ext
  intro x
  rcases zLKern.ofTerm_surjective p G n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  have h := congrArg
    (fun (u : zSubgro p G n →*
        zLKern p (G × H) n) => u t)
    (zLKern.ofTerm_naturality p G (MonoidHom.inl G H) n)
  dsimp [MonoidHom.comp_apply] at h
  rw [h]
  rw [zLKern.prod_equiv_term]
  rfl

/-- The product equivalence carries the layer-kernel map induced by the right inclusion
to the right inclusion of Zassenhaus layer factors. -/
@[simp] theorem zLKern.prodEquiv_inr (H : Type*) [Group H] (n : ℕ) :
    (zLKern.prodEquiv p G H n).toMonoidHom.comp
        (zLKern.map p H (MonoidHom.inr G H) n) =
      MonoidHom.inr _ _ := by
  apply MonoidHom.ext
  intro x
  rcases zLKern.ofTerm_surjective p H n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  have h := congrArg
    (fun (u : zSubgro p H n →*
        zLKern p (G × H) n) => u t)
    (zLKern.ofTerm_naturality p H (MonoidHom.inr G H) n)
  dsimp [MonoidHom.comp_apply] at h
  rw [h]
  rw [zLKern.prod_equiv_term]
  rfl

/-- The inverse product equivalence sends a left-factor Zassenhaus layer element to the
map induced by the left product inclusion. -/
@[simp] theorem zLKern.prod_equiv_symminl (H : Type*) [Group H] (n : ℕ)
    (x : zLKern p G n) :
    (zLKern.prodEquiv p G H n).symm (x, 1) =
      zLKern.map p G (MonoidHom.inl G H) n x := by
  apply (zLKern.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : zLKern p G n →*
      (zLKern p G n × zLKern p H n) => f x)
    (zLKern.prodEquiv_inl (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The inverse product equivalence sends a right-factor Zassenhaus layer element to the
map induced by the right product inclusion. -/
@[simp] theorem zLKern.prod_equiv_symminr (H : Type*) [Group H] (n : ℕ)
    (x : zLKern p H n) :
    (zLKern.prodEquiv p G H n).symm (1, x) =
      zLKern.map p H (MonoidHom.inr G H) n x := by
  apply (zLKern.prodEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  have h := congrArg (fun f : zLKern p H n →*
      (zLKern p G n × zLKern p H n) => f x)
    (zLKern.prodEquiv_inr (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h.symm

/-- The first projection after the product equivalence on Zassenhaus layer kernels
is the map induced by the first projection of groups. -/
@[simp] theorem zLKern.prodEquiv_fst (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.fst _ _).comp
        (zLKern.prodEquiv p G H n).toMonoidHom =
      zLKern.map p (G × H) (MonoidHom.fst G H) n := by
  apply MonoidHom.ext
  intro x
  rcases zLKern.ofTerm_surjective p (G × H) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  rw [zLKern.prod_equiv_term]
  rfl

/-- The second projection after the product equivalence on Zassenhaus layer kernels
is the map induced by the second projection of groups. -/
@[simp] theorem zLKern.prodEquiv_snd (H : Type*) [Group H] (n : ℕ) :
    (MonoidHom.snd _ _).comp
        (zLKern.prodEquiv p G H n).toMonoidHom =
      zLKern.map p (G × H) (MonoidHom.snd G H) n := by
  apply MonoidHom.ext
  intro x
  rcases zLKern.ofTerm_surjective p (G × H) n x with ⟨t, rfl⟩
  dsimp [MonoidHom.comp_apply]
  rw [zLKern.prod_equiv_term]
  rfl

/-- Cardinality formula for Zassenhaus layer kernels of products. -/
theorem nat_kernel_prod (H : Type*) [Group H] (n : ℕ) :
    Nat.card (zLKern p (G × H) n) =
      Nat.card (zLKern p G n) * Nat.card (zLKern p H n) :=
  nat_dimension_prod (R := ZMod p) G H n



/-- Product equivalence on Zassenhaus layer kernels is the pair of projection maps. -/
@[simp] theorem zLKern.prodEquiv_apply (H : Type*) [Group H] (n : ℕ)
    (x : zLKern p (G × H) n) :
    zLKern.prodEquiv p G H n x =
      (zLKern.map p (G × H) (MonoidHom.fst G H) n x,
        zLKern.map p (G × H) (MonoidHom.snd G H) n x) := by
  apply Prod.ext
  · have h := congrArg (fun f : zLKern p (G × H) n →*
        zLKern p G n => f x)
      (zLKern.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h
  · have h := congrArg (fun f : zLKern p (G × H) n →*
        zLKern p H n => f x)
      (zLKern.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply] using h

/-- Every product Zassenhaus-layer element splits as the product of its two projected
inclusion components. -/
theorem zLKern.eq_inl_mulinr (H : Type*) [Group H] (n : ℕ)
    (x : zLKern p (G × H) n) :
    x = zLKern.map p G (MonoidHom.inl G H) n
          (zLKern.map p (G × H) (MonoidHom.fst G H) n x) *
        zLKern.map p H (MonoidHom.inr G H) n
          (zLKern.map p (G × H) (MonoidHom.snd G H) n x) := by
  let e := zLKern.prodEquiv p G H n
  have hf : (e x).1 = zLKern.map p (G × H) (MonoidHom.fst G H) n x := by
    have h := congrArg (fun f : zLKern p (G × H) n →*
        zLKern p G n => f x)
      (zLKern.prodEquiv_fst (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hs : (e x).2 = zLKern.map p (G × H) (MonoidHom.snd G H) n x := by
    have h := congrArg (fun f : zLKern p (G × H) n →*
        zLKern p H n => f x)
      (zLKern.prodEquiv_snd (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (((e x).1, 1) * (1, (e x).2)) := by
      cases h : e x
      simp
    _ = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [map_mul]
    _ = zLKern.map p G (MonoidHom.inl G H) n
          (zLKern.map p (G × H) (MonoidHom.fst G H) n x) *
        zLKern.map p H (MonoidHom.inr G H) n
          (zLKern.map p (G × H) (MonoidHom.snd G H) n x) := by
      rw [hf, hs]
      simp [e]

/-- Naturality of the product equivalence for consecutive Zassenhaus quotients. -/
theorem zNQuot.prodEquiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zNQuot.prodEquiv p G₂ H₂ n).toMonoidHom.comp
        (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (zNQuot.map p G₁ f n)
        (zNQuot.map p H₁ g n)).comp
        (zNQuot.prodEquiv p G₁ H₁ n).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rfl


/-- Associator followed by its inverse is identity on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.mapprod_assocsymm_prodassoc
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :
    zNQuot.map p (G × H × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (zNQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zNQuot.map_comp (p := p) (G := (G × H) × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) →*
      (zSubgro p ((G × H) × K) n ⧸
        zNTerm p ((G × H) × K) n) => f x)
    (zNQuot.map_id (p := p) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Mapping by the product associator and then its inverse is the identity on Zassenhaus layers. -/
@[simp] theorem zLKern.mapprod_assocsymm_prodassoc
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((G × H) × K) n) :
    zLKern.map p (G × H × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
      (zLKern.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zLKern.map_comp (p := p) (G := (G × H) × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) =
      MonoidHom.id ((G × H) × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zLKern p ((G × H) × K) n →*
      zLKern p ((G × H) × K) n => f x)
    (zLKern.map_id (p := p) ((G × H) × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on consecutive
Zassenhaus quotients. -/
@[simp] theorem zNQuot.mapprod_assocprod_assocsymm
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p (G × H × K) n ⧸
      zNTerm p (G × H × K) n) :
    zNQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (zNQuot.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zNQuot.map_comp (p := p) (G := G × H × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (zSubgro p (G × H × K) n ⧸
      zNTerm p (G × H × K) n) →*
      (zSubgro p (G × H × K) n ⧸
        zNTerm p (G × H × K) n) => f x)
    (zNQuot.map_id (p := p) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- The inverse associator followed by the associator is identity on Zassenhaus layers. -/
@[simp] theorem zLKern.mapprod_assocprod_assocsymm
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p (G × H × K) n) :
    zLKern.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      (zLKern.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zLKern.map_comp (p := p) (G := G × H × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n]
  have hcomp :
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom).comp
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) =
      MonoidHom.id (G × H × K) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zLKern p (G × H × K) n →*
      zLKern p (G × H × K) n => f x)
    (zLKern.map_id (p := p) (G × H × K) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Associativity coherence for consecutive Zassenhaus quotient product equivalences. -/
theorem zNQuot.prod_equiv_assocnatural
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap
        (MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n))
        (zNQuot.prodEquiv p H K n).toMonoidHom).comp
      (zNQuot.prodEquiv p G (H × K) n).toMonoidHom).comp
        (zNQuot.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        ((zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n)) ×
          (zSubgro p K n ⧸ zNTerm p K n) ≃*
        (zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n) ×
          (zSubgro p K n ⧸ zNTerm p K n)).toMonoidHom).comp
      ((MonoidHom.prodMap (zNQuot.prodEquiv p G H n).toMonoidHom
        (MonoidHom.id (zSubgro p K n ⧸ zNTerm p K n))).comp
        (zNQuot.prodEquiv p (G × H) K n).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro ghk
  rfl

/-- Pointwise associativity coherence for consecutive Zassenhaus quotient products. -/
@[simp] theorem zNQuot.prod_equiv_assocapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :
    (MonoidHom.prodMap
        (MonoidHom.id (zSubgro p G n ⧸ zNTerm p G n))
        (zNQuot.prodEquiv p H K n).toMonoidHom)
      (zNQuot.prodEquiv p G (H × K) n
        (zNQuot.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        ((zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n)) ×
          (zSubgro p K n ⧸ zNTerm p K n) ≃*
        (zSubgro p G n ⧸ zNTerm p G n) ×
          (zSubgro p H n ⧸ zNTerm p H n) ×
          (zSubgro p K n ⧸ zNTerm p K n))
        ((MonoidHom.prodMap (zNQuot.prodEquiv p G H n).toMonoidHom
          (MonoidHom.id (zSubgro p K n ⧸ zNTerm p K n)))
          (zNQuot.prodEquiv p (G × H) K n x)) := by
  have h := congrArg (fun f : (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) →*
      ((zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n) ×
        (zSubgro p K n ⧸ zNTerm p K n)) => f x)
    (zNQuot.prod_equiv_assocnatural (p := p) (G := G) H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Inverse-form associativity coherence for consecutive Zassenhaus quotient products. -/
@[simp] theorem zNQuot.prod_equivassoc_symmapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (a : zSubgro p G n ⧸ zNTerm p G n)
    (b : zSubgro p H n ⧸ zNTerm p H n)
    (c : zSubgro p K n ⧸ zNTerm p K n) :
    zNQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((zNQuot.prodEquiv p (G × H) K n).symm
        ((zNQuot.prodEquiv p G H n).symm (a, b), c)) =
      (zNQuot.prodEquiv p G (H × K) n).symm
        (a, (zNQuot.prodEquiv p H K n).symm (b, c)) := by
  apply (zNQuot.prodEquiv p G (H × K) n).injective
  let x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n :=
    (zNQuot.prodEquiv p (G × H) K n).symm
      ((zNQuot.prodEquiv p G H n).symm (a, b), c)
  have h := zNQuot.prod_equiv_assocapply (p := p) (G := G) H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (zNQuot.prodEquiv p H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Pointwise form of naturality for consecutive Zassenhaus quotient product equivalences. -/
@[simp] theorem zNQuot.prod_equiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zSubgro p (G₁ × H₁) n ⧸
      zNTerm p (G₁ × H₁) n) :
    zNQuot.prodEquiv p G₂ H₂ n
        (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      (zNQuot.map p G₁ f n
          (zNQuot.prodEquiv p G₁ H₁ n x).1,
        zNQuot.map p H₁ g n
          (zNQuot.prodEquiv p G₁ H₁ n x).2) := by
  have h := congrArg (fun F : (zSubgro p (G₁ × H₁) n ⧸
      zNTerm p (G₁ × H₁) n) →*
      ((zSubgro p G₂ n ⧸ zNTerm p G₂ n) ×
        (zSubgro p H₂ n ⧸ zNTerm p H₂ n)) => F x)
    (zNQuot.prodEquiv_naturality (p := p) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality on inverse product representatives for consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prod_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : (zSubgro p G₁ n ⧸ zNTerm p G₁ n) ×
      (zSubgro p H₁ n ⧸ zNTerm p H₁ n)) :
    zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zNQuot.prodEquiv p G₁ H₁ n).symm y) =
      (zNQuot.prodEquiv p G₂ H₂ n).symm
        (zNQuot.map p G₁ f n y.1,
          zNQuot.map p H₁ g n y.2) := by
  apply (zNQuot.prodEquiv p G₂ H₂ n).injective
  have h := zNQuot.prod_equiv_naturalapply (p := p) f g n
    ((zNQuot.prodEquiv p G₁ H₁ n).symm y)
  simpa using h

/-- Product-commuting the factors is compatible with the consecutive Zassenhaus-quotient
product equivalence. -/
theorem zNQuot.prod_equiv_swapnatural (H : Type*) [Group H]
    (n : ℕ) :
    (zNQuot.prodEquiv p H G n).toMonoidHom.comp
        (zNQuot.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm :
        (zSubgro p G n ⧸ zNTerm p G n) ×
        (zSubgro p H n ⧸ zNTerm p H n) ≃*
        (zSubgro p H n ⧸ zNTerm p H n) ×
        (zSubgro p G n ⧸ zNTerm p G n)).toMonoidHom).comp
        (zNQuot.prodEquiv p G H n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro gh
  rfl

/-- Applying the product-commuting map twice on consecutive Zassenhaus quotients is the identity. -/
@[simp] theorem zNQuot.map_prodcomm_prodcomm (H : Type*) [Group H]
    (n : ℕ)
    (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.map p (H × G)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zNQuot.map_comp (p := p) (G := G × H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) →*
      (zSubgro p (G × H) n ⧸
        zNTerm p (G × H) n) => f x)
    (zNQuot.map_id (p := p) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Applying the product-commuting map twice on Zassenhaus layer kernels is the identity. -/
@[simp] theorem zLKern.map_prodcomm_prodcomm (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.map p (H × G)
      ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
      (zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [← zLKern.map_comp (p := p) (G := G × H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom)
    ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n]
  have hcomp : ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom).comp
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) =
      MonoidHom.id (G × H) := by
    ext z <;> rfl
  rw [hcomp]
  have hid := congrArg (fun f : zLKern p (G × H) n →*
      zLKern p (G × H) n => f x)
    (zLKern.map_id (p := p) (G × H) n)
  simpa only [MonoidHom.id_apply] using hid

/-- Pointwise form of swap-naturality for consecutive Zassenhaus quotient product equivalences. -/
@[simp] theorem zNQuot.prod_equiv_swapapply (H : Type*) [Group H]
    (n : ℕ)
    (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodEquiv p H G n
        (zNQuot.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((zNQuot.prodEquiv p G H n x).2,
        (zNQuot.prodEquiv p G H n x).1) := by
  have h := congrArg (fun f : (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) →*
      ((zSubgro p H n ⧸ zNTerm p H n) ×
        (zSubgro p G n ⧸ zNTerm p G n)) => f x)
    (zNQuot.prod_equiv_swapnatural (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h

/-- Product-commuting the factors is compatible with the Zassenhaus layer-kernel product
equivalence. -/
theorem zLKern.prod_equiv_swapnatural (H : Type*) [Group H]
    (n : ℕ) :
    (zLKern.prodEquiv p H G n).toMonoidHom.comp
        (zLKern.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) =
      ((MulEquiv.prodComm : zLKern p G n × zLKern p H n ≃*
          zLKern p H n × zLKern p G n).toMonoidHom).comp
        (zLKern.prodEquiv p G H n).toMonoidHom := by
  exact dLKern.prod_equiv_swapnatural (R := ZMod p) G H n

/-- Pointwise form of swap-naturality for Zassenhaus layer-kernel product equivalences. -/
@[simp] theorem zLKern.prod_equiv_swapapply (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodEquiv p H G n
        (zLKern.map p (G × H)
          ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) =
      ((zLKern.prodEquiv p G H n x).2,
        (zLKern.prodEquiv p G H n x).1) := by
  have h := congrArg (fun f : zLKern p (G × H) n →*
      (zLKern p H n × zLKern p G n) => f x)
    (zLKern.prod_equiv_swapnatural (p := p) (G := G) H n)
  simpa [MonoidHom.comp_apply] using h

/-- Associativity coherence for Zassenhaus layer-kernel product equivalences. -/
theorem zLKern.prod_equiv_assocnatural
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    ((MonoidHom.prodMap (MonoidHom.id (zLKern p G n))
        (zLKern.prodEquiv p H K n).toMonoidHom).comp
      (zLKern.prodEquiv p G (H × K) n).toMonoidHom).comp
        (zLKern.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) =
    ((MulEquiv.prodAssoc :
        (zLKern p G n × zLKern p H n) ×
          zLKern p K n ≃*
        zLKern p G n × zLKern p H n ×
          zLKern p K n).toMonoidHom).comp
      ((MonoidHom.prodMap (zLKern.prodEquiv p G H n).toMonoidHom
        (MonoidHom.id (zLKern p K n))).comp
        (zLKern.prodEquiv p (G × H) K n).toMonoidHom) := by
  exact dLKern.prod_equiv_assocnatural (R := ZMod p) G H K n

/-- Pointwise associativity coherence for Zassenhaus layer-kernel product equivalences. -/
@[simp] theorem zLKern.prod_equiv_assocapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((G × H) × K) n) :
    (MonoidHom.prodMap (MonoidHom.id (zLKern p G n))
        (zLKern.prodEquiv p H K n).toMonoidHom)
      (zLKern.prodEquiv p G (H × K) n
        (zLKern.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) =
      (MulEquiv.prodAssoc :
        (zLKern p G n × zLKern p H n) ×
          zLKern p K n ≃*
        zLKern p G n × zLKern p H n ×
          zLKern p K n)
        ((MonoidHom.prodMap (zLKern.prodEquiv p G H n).toMonoidHom
          (MonoidHom.id (zLKern p K n)))
          (zLKern.prodEquiv p (G × H) K n x)) := by
  have h := congrArg (fun f : zLKern p ((G × H) × K) n →*
      (zLKern p G n × zLKern p H n ×
        zLKern p K n) => f x)
    (zLKern.prod_equiv_assocnatural (p := p) (G := G) H K n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality of the product equivalence for Zassenhaus layer kernels. -/
theorem zLKern.prodEquiv_naturality
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zLKern.prodEquiv p G₂ H₂ n).toMonoidHom.comp
        (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (MonoidHom.prodMap (zLKern.map p G₁ f n)
        (zLKern.map p H₁ g n)).comp
        (zLKern.prodEquiv p G₁ H₁ n).toMonoidHom := by
  exact dLKern.prodEquiv_naturality (R := ZMod p) f g n


/-- Inverse-form associativity coherence for Zassenhaus layer-kernel product equivalences. -/
@[simp] theorem zLKern.prod_equivassoc_symmapply
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (a : zLKern p G n) (b : zLKern p H n)
    (c : zLKern p K n) :
    zLKern.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n
      ((zLKern.prodEquiv p (G × H) K n).symm
        ((zLKern.prodEquiv p G H n).symm (a, b), c)) =
      (zLKern.prodEquiv p G (H × K) n).symm
        (a, (zLKern.prodEquiv p H K n).symm (b, c)) := by
  apply (zLKern.prodEquiv p G (H × K) n).injective
  let x : zLKern p ((G × H) × K) n :=
    (zLKern.prodEquiv p (G × H) K n).symm
      ((zLKern.prodEquiv p G H n).symm (a, b), c)
  have h := zLKern.prod_equiv_assocapply (p := p) (G := G) H K n x
  dsimp [x] at h ⊢
  simp only [MulEquiv.apply_symm_apply] at h ⊢
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    simpa [x] using h1
  · apply (zLKern.prodEquiv p H K n).injective
    have h2 := congrArg Prod.snd h
    simpa [x] using h2

/-- Pointwise form of naturality for Zassenhaus layer-kernel product equivalences. -/
@[simp] theorem zLKern.prod_equiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zLKern p (G₁ × H₁) n) :
    zLKern.prodEquiv p G₂ H₂ n
        (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      (zLKern.map p G₁ f n
          (zLKern.prodEquiv p G₁ H₁ n x).1,
        zLKern.map p H₁ g n
          (zLKern.prodEquiv p G₁ H₁ n x).2) := by
  have h := congrArg (fun F : zLKern p (G₁ × H₁) n →*
      (zLKern p G₂ n × zLKern p H₂ n) => F x)
    (zLKern.prodEquiv_naturality (p := p) f g n)
  simpa [MonoidHom.comp_apply] using h

/-- Naturality on inverse product representatives for Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prod_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : zLKern p G₁ n × zLKern p H₁ n) :
    zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zLKern.prodEquiv p G₁ H₁ n).symm y) =
      (zLKern.prodEquiv p G₂ H₂ n).symm
        (zLKern.map p G₁ f n y.1,
          zLKern.map p H₁ g n y.2) := by
  apply (zLKern.prodEquiv p G₂ H₂ n).injective
  have h := zLKern.prod_equiv_naturalapply (p := p) f g n
    ((zLKern.prodEquiv p G₁ H₁ n).symm y)
  simpa using h

/-- Naturality of the linear product equivalence for consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_lin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zNQuot.prodLinearEquiv p G₂ H₂ n).toLinearMap.comp
        (zNQuot.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      ((zNQuot.mapLinear p G₁ f n).prodMap
        (zNQuot.mapLinear p H₁ g n)).comp
        (zNQuot.prodLinearEquiv p G₁ H₁ n).toLinearMap := by
  ext x <;> cases x using Additive.rec
  · rename_i q
    change Additive.ofMul (((zNQuot.prodEquiv p G₂ H₂ n)
        ((zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) q)).1) =
      Additive.ofMul (((MonoidHom.prodMap (zNQuot.map p G₁ f n)
        (zNQuot.map p H₁ g n))
        ((zNQuot.prodEquiv p G₁ H₁ n) q)).1)
    congr 1
    have h := congrArg (fun (u : _ →* _) => u q)
      (zNQuot.prodEquiv_naturality (p := p) f g n)
    exact congrArg Prod.fst h
  · rename_i q
    change Additive.ofMul (((zNQuot.prodEquiv p G₂ H₂ n)
        ((zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) q)).2) =
      Additive.ofMul (((MonoidHom.prodMap (zNQuot.map p G₁ f n)
        (zNQuot.map p H₁ g n))
        ((zNQuot.prodEquiv p G₁ H₁ n) q)).2)
    congr 1
    have h := congrArg (fun (u : _ →* _) => u q)
      (zNQuot.prodEquiv_naturality (p := p) f g n)
    exact congrArg Prod.snd h




/-- Naturality of the linear product equivalence for Zassenhaus layer kernels. -/
theorem zLKern.prod_lin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zLKern.prodLinearEquiv p G₂ H₂ n).toLinearMap.comp
        (zLKern.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      ((zLKern.mapLinear p G₁ f n).prodMap
        (zLKern.mapLinear p H₁ g n)).comp
        (zLKern.prodLinearEquiv p G₁ H₁ n).toLinearMap := by
  apply LinearMap.ext
  intro x
  cases x using Additive.rec
  rename_i q
  apply Prod.ext
  · apply Additive.ext
    have h := congrArg (fun (u : _ →* _) => u q)
      (zLKern.prodEquiv_naturality (p := p) f g n)
    exact congrArg Prod.fst h
  · apply Additive.ext
    have h := congrArg (fun (u : _ →* _) => u q)
      (zLKern.prodEquiv_naturality (p := p) f g n)
    exact congrArg Prod.snd h

/-- Left- and right-inclusion images commute in a product Zassenhaus layer kernel. -/
theorem zLKern.map_inlmul_inrcomm (H : Type*) [Group H] (n : ℕ)
    (x : zLKern p G n) (y : zLKern p H n) :
    zLKern.map p G (MonoidHom.inl G H) n x *
        zLKern.map p H (MonoidHom.inr G H) n y =
      zLKern.map p H (MonoidHom.inr G H) n y *
        zLKern.map p G (MonoidHom.inl G H) n x := by
  let e := zLKern.prodEquiv p G H n
  apply e.injective
  have hx : e (zLKern.map p G (MonoidHom.inl G H) n x) =
      (x, 1) := by
    have h := congrArg (fun f : zLKern p G n →*
        (zLKern p G n × zLKern p H n) => f x)
      (zLKern.prodEquiv_inl (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  have hy : e (zLKern.map p H (MonoidHom.inr G H) n y) =
      (1, y) := by
    have h := congrArg (fun f : zLKern p H n →*
        (zLKern p G n × zLKern p H n) => f y)
      (zLKern.prodEquiv_inr (p := p) (G := G) H n)
    simpa only [e, MonoidHom.comp_apply] using h
  simp [map_mul, hx, hy]

/-- Projecting the right-inclusion map to the first Zassenhaus layer kernel is trivial. -/
@[simp] theorem zLKern.map_fst_compinr (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.fst G H) n).comp
        (zLKern.map p H (MonoidHom.inr G H) n) =
      (1 : zLKern p H n →* zLKern p G n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : zLKern p H n →*
      (zLKern p G n × zLKern p H n) => f x)
    (zLKern.prodEquiv_inr (p := p) (G := G) H n)
  have hf := congrArg Prod.fst h
  simpa [MonoidHom.comp_apply, zLKern.prodEquiv_apply] using hf

/-- Projecting the left-inclusion map to the second Zassenhaus layer kernel is trivial. -/
@[simp] theorem zLKern.map_snd_compinl (H : Type*) [Group H] (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.snd G H) n).comp
        (zLKern.map p G (MonoidHom.inl G H) n) =
      (1 : zLKern p G n →* zLKern p H n) := by
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun f : zLKern p G n →*
      (zLKern p G n × zLKern p H n) => f x)
    (zLKern.prodEquiv_inl (p := p) (G := G) H n)
  have hs := congrArg Prod.snd h
  simpa [MonoidHom.comp_apply, zLKern.prodEquiv_apply] using hs

@[simp] theorem zLKern.map_fst_inrapply (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p H n) :
    zLKern.map p (G × H) (MonoidHom.fst G H) n
        (zLKern.map p H (MonoidHom.inr G H) n x) = 1 := by
  have h := congrArg (fun f : zLKern p H n →*
      zLKern p G n => f x)
    (zLKern.map_fst_compinr (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

@[simp] theorem zLKern.map_snd_inlapply (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p G n) :
    zLKern.map p (G × H) (MonoidHom.snd G H) n
        (zLKern.map p G (MonoidHom.inl G H) n x) = 1 := by
  have h := congrArg (fun f : zLKern p G n →*
      zLKern p H n => f x)
    (zLKern.map_snd_compinl (p := p) (G := G) H n)
  simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h

/-- A product Zassenhaus-layer element lies in the right-inclusion range iff its first
projection is trivial. -/
theorem zLKern.memrange_inriffmap_fsteqone (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    x ∈ (zLKern.map p H (MonoidHom.inr G H) n).range ↔
      zLKern.map p (G × H) (MonoidHom.fst G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : zLKern p H n →*
        zLKern p G n => f y)
      (zLKern.map_fst_compinr (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zLKern.map p (G × H) (MonoidHom.snd G H) n x, ?_⟩
    have h := zLKern.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, one_mul] at h
    exact h.symm

/-- A product Zassenhaus-layer element lies in the left-inclusion range iff its second
projection is trivial. -/
theorem zLKern.memrange_inliffmap_sndeqone (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    x ∈ (zLKern.map p G (MonoidHom.inl G H) n).range ↔
      zLKern.map p (G × H) (MonoidHom.snd G H) n x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : zLKern p G n →*
        zLKern p H n => f y)
      (zLKern.map_snd_compinl (p := p) (G := G) H n)
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  · intro hx
    refine ⟨zLKern.map p (G × H) (MonoidHom.fst G H) n x, ?_⟩
    have h := zLKern.eq_inl_mulinr (p := p) (G := G) H n x
    rw [hx, map_one, mul_one] at h
    exact h.symm

/-- The kernel of the first projection on a product Zassenhaus layer kernel is the
right-inclusion range. -/
theorem zLKern.kermap_fsteq_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.fst G H) n).ker =
      (zLKern.map p H (MonoidHom.inr G H) n).range := by
  ext x
  exact (zLKern.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).symm

/-- The kernel of the second projection on a product Zassenhaus layer kernel is the
left-inclusion range. -/
theorem zLKern.kermap_sndeq_rangeinl (H : Type*) [Group H]
    (n : ℕ) :
    (zLKern.map p (G × H) (MonoidHom.snd G H) n).ker =
      (zLKern.map p G (MonoidHom.inl G H) n).range := by
  ext x
  exact (zLKern.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).symm

/-- The left- and right-inclusion ranges in a product Zassenhaus layer kernel meet only at `1`. -/
theorem zLKern.eqone_memrangeinl_memrangeinr (H : Type*) [Group H]
    (n : ℕ) {x : zLKern p (G × H) n}
    (hxL : x ∈ (zLKern.map p G (MonoidHom.inl G H) n).range)
    (hxR : x ∈ (zLKern.map p H (MonoidHom.inr G H) n).range) :
    x = 1 := by
  have hfst := (zLKern.memrange_inriffmap_fsteqone
    (p := p) (G := G) H n x).1 hxR
  have hsnd := (zLKern.memrange_inliffmap_sndeqone
    (p := p) (G := G) H n x).1 hxL
  have h := zLKern.eq_inl_mulinr (p := p) (G := G) H n x
  simpa [hfst, hsnd] using h

/-- The left- and right-inclusion ranges in a product Zassenhaus layer kernel are disjoint. -/
theorem zLKern.disjoint_rangeinl_rangeinr (H : Type*) [Group H]
    (n : ℕ) :
    Disjoint (zLKern.map p G (MonoidHom.inl G H) n).range
      (zLKern.map p H (MonoidHom.inr G H) n).range := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxR
  exact zLKern.eqone_memrangeinl_memrangeinr
    (p := p) (G := G) H n hxL hxR


/-- Reassociation equivalence for consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.prodAssocEquiv (H K : Type*) [Group H] [Group K]
    (n : ℕ) :
    (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) ≃*
      (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) :=
  MulEquiv.ofBijective
    (zNQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg
        (fun z => zNQuot.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n z) hxy
      calc
        x = zNQuot.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zNQuot.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) :=
          (zNQuot.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n x).symm
        _ = zNQuot.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zNQuot.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n y) := h
        _ = y := zNQuot.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n y
    · intro y
      refine ⟨zNQuot.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y, ?_⟩
      exact zNQuot.mapprod_assocprod_assocsymm
        (p := p) (G := G) H K n y



@[simp] theorem zNQuot.prod_assoc_equivapply (H K : Type*) [Group H]
    [Group K] (n : ℕ)
    (x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :
    zNQuot.prodAssocEquiv p G H K n x =
      zNQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := rfl

@[simp] theorem zNQuot.prod_assocequiv_monoidhom (H K : Type*)
    [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodAssocEquiv p G H K n).toMonoidHom =
      zNQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := rfl



@[simp] theorem zNQuot.prod_assocequiv_symmapply (H K : Type*)
    [Group H] [Group K] (n : ℕ)
    (y : zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :
    (zNQuot.prodAssocEquiv p G H K n).symm y =
      zNQuot.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y := by
  apply (zNQuot.prodAssocEquiv p G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zNQuot.mapprod_assocprod_assocsymm
    (p := p) (G := G) H K n y).symm

/-- Reassociation equivalence for Zassenhaus layer kernels. -/
noncomputable def zLKern.prodAssocEquiv (H K : Type*) [Group H] [Group K]
    (n : ℕ) :
    zLKern p ((G × H) × K) n ≃*
      zLKern p (G × (H × K)) n :=
  MulEquiv.ofBijective
    (zLKern.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg
        (fun z => zLKern.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n z) hxy
      calc
        x = zLKern.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zLKern.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) :=
          (zLKern.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n x).symm
        _ = zLKern.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zLKern.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n y) := h
        _ = y := zLKern.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n y
    · intro y
      refine ⟨zLKern.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y, ?_⟩
      exact zLKern.mapprod_assocprod_assocsymm
        (p := p) (G := G) H K n y


@[simp] theorem zLKern.prod_assoc_equivapply (H K : Type*) [Group H]
    [Group K] (n : ℕ) (x : zLKern p ((G × H) × K) n) :
    zLKern.prodAssocEquiv p G H K n x =
      zLKern.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := rfl

@[simp] theorem zLKern.prod_assocequiv_monoidhom (H K : Type*)
    [Group H] [Group K] (n : ℕ) :
    (zLKern.prodAssocEquiv p G H K n).toMonoidHom =
      zLKern.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := rfl


@[simp] theorem zLKern.prod_assocequiv_symmapply (H K : Type*)
    [Group H] [Group K] (n : ℕ) (y : zLKern p (G × (H × K)) n) :
    (zLKern.prodAssocEquiv p G H K n).symm y =
      zLKern.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y := by
  apply (zLKern.prodAssocEquiv p G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zLKern.mapprod_assocprod_assocsymm
    (p := p) (G := G) H K n y).symm


/-- The product associator induces a bijective linear map on prime Zassenhaus layer kernels. -/
theorem zLKern.map_linprod_assocbij [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    Function.Bijective (zLKern.mapLinear p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) := by
  have hb : Function.Bijective (zLKern.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) :=
    (zLKern.prodAssocEquiv p G H K n).bijective
  constructor
  · intro x y hxy
    cases x with
    | ofMul x' =>
      cases y with
      | ofMul y' =>
        apply congrArg Additive.ofMul
        apply hb.1
        exact congrArg Additive.toMul hxy
  · intro y
    cases y with
    | ofMul y' =>
      rcases hb.2 y' with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- Linear reassociation equivalence for prime Zassenhaus layer kernels. -/
noncomputable def zLKern.prod_assoc_linequiv [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    Additive (zLKern p ((G × H) × K) n) ≃ₗ[ZMod p]
      Additive (zLKern p (G × (H × K)) n) :=
  LinearEquiv.ofBijective (zLKern.mapLinear p ((G × H) × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n)
    (zLKern.map_linprod_assocbij (p := p) (G := G) H K n)

@[simp] theorem zLKern.prod_assoclin_equivapply [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p ((G × H) × K) n)) :
    zLKern.prod_assoc_linequiv p G H K n x =
      zLKern.mapLinear p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := rfl


/-- The product associator induces a bijective linear map on prime consecutive quotients. -/
theorem zNQuot.map_linprod_assocbij [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    Function.Bijective (zNQuot.mapLinear p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) := by
  have hb : Function.Bijective (zNQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) :=
    (zNQuot.prodAssocEquiv p G H K n).bijective
  constructor
  · intro x y hxy
    cases x with
    | ofMul x' =>
      cases y with
      | ofMul y' =>
        apply congrArg Additive.ofMul
        apply hb.1
        exact congrArg Additive.toMul hxy
  · intro y
    cases y with
    | ofMul y' =>
      rcases hb.2 y' with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- Linear reassociation equivalence for prime consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.prod_assoc_linequiv [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) ≃ₗ[ZMod p]
      Additive (zSubgro p (G × (H × K)) n ⧸
        zNTerm p (G × (H × K)) n) :=
  LinearEquiv.ofBijective (zNQuot.mapLinear p ((G × H) × K)
    ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n)
    (zNQuot.map_linprod_assocbij (p := p) (G := G) H K n)

@[simp] theorem zNQuot.prod_assoclin_equivapply [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :
    zNQuot.prod_assoc_linequiv p G H K n x =
      zNQuot.mapLinear p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := rfl


@[simp] theorem zLKern.prodassoc_linequiv_symmapply [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (y : Additive (zLKern p (G × (H × K)) n)) :
    (zLKern.prod_assoc_linequiv p G H K n).symm y =
      zLKern.mapLinear p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y := by
  apply (zLKern.prod_assoc_linequiv p G H K n).injective
  rw [LinearEquiv.apply_symm_apply]
  cases y with
  | ofMul y' =>
    apply congrArg Additive.ofMul
    exact (zLKern.mapprod_assocprod_assocsymm
      (p := p) (G := G) H K n y').symm

@[simp] theorem zNQuot.prodassoc_linequiv_symmapply [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (y : Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :
    (zNQuot.prod_assoc_linequiv p G H K n).symm y =
      zNQuot.mapLinear p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y := by
  apply (zNQuot.prod_assoc_linequiv p G H K n).injective
  rw [LinearEquiv.apply_symm_apply]
  cases y with
  | ofMul y' =>
    apply congrArg Additive.ofMul
    exact (zNQuot.mapprod_assocprod_assocsymm
      (p := p) (G := G) H K n y').symm


/-- Swap equivalence for consecutive Zassenhaus quotients of a product. -/
noncomputable def zNQuot.prodCommEquiv (H : Type*) [Group H] (n : ℕ) :
    (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n) ≃*
      (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) :=
  MulEquiv.ofBijective
    (zNQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg (fun z => zNQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n z) hxy
      calc
        x = zNQuot.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zNQuot.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) :=
          (zNQuot.map_prodcomm_prodcomm (p := p) (G := G) H n x).symm
        _ = zNQuot.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zNQuot.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n y) := h
        _ = y := zNQuot.map_prodcomm_prodcomm (p := p) (G := G) H n y
    · intro y
      refine ⟨zNQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y, ?_⟩
      exact zNQuot.map_prodcomm_prodcomm (p := p) (G := H) G n y

/-- Swap equivalence for Zassenhaus layer kernels of a product. -/
noncomputable def zLKern.prodCommEquiv (H : Type*) [Group H] (n : ℕ) :
    zLKern p (G × H) n ≃* zLKern p (H × G) n :=
  MulEquiv.ofBijective
    (zLKern.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg (fun z => zLKern.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n z) hxy
      calc
        x = zLKern.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zLKern.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) :=
          (zLKern.map_prodcomm_prodcomm (p := p) (G := G) H n x).symm
        _ = zLKern.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zLKern.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n y) := h
        _ = y := zLKern.map_prodcomm_prodcomm (p := p) (G := G) H n y
    · intro y
      refine ⟨zLKern.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y, ?_⟩
      exact zLKern.map_prodcomm_prodcomm (p := p) (G := H) G n y


@[simp] theorem zNQuot.prod_comm_equivapply (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p G H n x =
      zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := rfl

@[simp] theorem zNQuot.prod_commequiv_monoidhom (H : Type*)
    [Group H] (n : ℕ) :
    (zNQuot.prodCommEquiv p G H n).toMonoidHom =
      zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := rfl

@[simp] theorem zNQuot.prod_commequiv_symmapply (H : Type*)
    [Group H] (n : ℕ) (y : zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n) :
    (zNQuot.prodCommEquiv p G H n).symm y =
      zNQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y := by
  apply (zNQuot.prodCommEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zNQuot.map_prodcomm_prodcomm (p := p) (G := H) G n y).symm

@[simp] theorem zLKern.prod_comm_equivapply (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p G H n x =
      zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := rfl

@[simp] theorem zLKern.prod_commequiv_monoidhom (H : Type*)
    [Group H] (n : ℕ) :
    (zLKern.prodCommEquiv p G H n).toMonoidHom =
      zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := rfl

@[simp] theorem zLKern.prod_commequiv_symmapply (H : Type*)
    [Group H] (n : ℕ) (y : zLKern p (H × G) n) :
    (zLKern.prodCommEquiv p G H n).symm y =
      zLKern.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y := by
  apply (zLKern.prodCommEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zLKern.map_prodcomm_prodcomm (p := p) (G := H) G n y).symm


/-- The product swap induces a bijective linear map on prime Zassenhaus layer kernels. -/
theorem zLKern.map_linprod_commbij [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Function.Bijective (zLKern.mapLinear p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) := by
  have hb : Function.Bijective (zLKern.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) :=
    (zLKern.prodCommEquiv p G H n).bijective
  constructor
  · intro x y hxy
    cases x with | ofMul x' =>
      cases y with | ofMul y' =>
        apply congrArg Additive.ofMul
        apply hb.1
        exact congrArg Additive.toMul hxy
  · intro y
    cases y with | ofMul y' =>
      rcases hb.2 y' with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- Linear product-swap equivalence for prime Zassenhaus layer kernels. -/
noncomputable def zLKern.prod_comm_linequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive (zLKern p (G × H) n) ≃ₗ[ZMod p]
      Additive (zLKern p (H × G) n) :=
  LinearEquiv.ofBijective (zLKern.mapLinear p (G × H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)
    (zLKern.map_linprod_commbij (p := p) (G := G) H n)

@[simp] theorem zLKern.prod_commlin_equivapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p (G × H) n)) :
    zLKern.prod_comm_linequiv p G H n x =
      zLKern.mapLinear p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := rfl

/-- The product swap induces a bijective linear map on prime consecutive quotients. -/
theorem zNQuot.map_linprod_commbij [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Function.Bijective (zNQuot.mapLinear p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) := by
  have hb : Function.Bijective (zNQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) :=
    (zNQuot.prodCommEquiv p G H n).bijective
  constructor
  · intro x y hxy
    cases x with | ofMul x' =>
      cases y with | ofMul y' =>
        apply congrArg Additive.ofMul
        apply hb.1
        exact congrArg Additive.toMul hxy
  · intro y
    cases y with | ofMul y' =>
      rcases hb.2 y' with ⟨x, rfl⟩
      exact ⟨Additive.ofMul x, rfl⟩

/-- Linear product-swap equivalence for prime consecutive Zassenhaus quotients. -/
noncomputable def zNQuot.prod_comm_linequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    Additive
        (zSubgro p (G × H) n ⧸
          zNTerm p (G × H) n) ≃ₗ[ZMod p]
      Additive (zSubgro p (H × G) n ⧸ zNTerm p (H × G) n) :=
  LinearEquiv.ofBijective (zNQuot.mapLinear p (G × H)
    ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)
    (zNQuot.map_linprod_commbij (p := p) (G := G) H n)

@[simp] theorem zNQuot.prod_commlin_equivapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p (G × H) n ⧸ zNTerm p (G × H) n)) :
    zNQuot.prod_comm_linequiv p G H n x =
      zNQuot.mapLinear p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := rfl


@[simp] theorem zLKern.prodcomm_linequiv_symmapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (y : Additive (zLKern p (H × G) n)) :
    (zLKern.prod_comm_linequiv p G H n).symm y =
      zLKern.mapLinear p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y := by
  apply (zLKern.prod_comm_linequiv p G H n).injective
  rw [LinearEquiv.apply_symm_apply]
  cases y with | ofMul y' =>
    apply congrArg Additive.ofMul
    exact (zLKern.map_prodcomm_prodcomm (p := p) (G := H) G n y').symm

@[simp] theorem zNQuot.prodcomm_linequiv_symmapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (y : Additive (zSubgro p (H × G) n ⧸
      zNTerm p (H × G) n)) :
    (zNQuot.prod_comm_linequiv p G H n).symm y =
      zNQuot.mapLinear p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y := by
  apply (zNQuot.prod_comm_linequiv p G H n).injective
  rw [LinearEquiv.apply_symm_apply]
  cases y with | ofMul y' =>
    apply congrArg Additive.ofMul
    exact (zNQuot.map_prodcomm_prodcomm (p := p) (G := H) G n y').symm



/-- The inverse of the layer-kernel swap equivalence is the swap in the opposite direction. -/
@[simp] theorem zLKern.prod_commequiv_symmeq (H : Type*) [Group H]
    (n : ℕ) :
    (zLKern.prodCommEquiv p G H n).symm =
      zLKern.prodCommEquiv p H G n := by
  ext y
  simp [zLKern.prod_commequiv_symmapply,
    zLKern.prod_comm_equivapply]

/-- The inverse of the consecutive-quotient swap equivalence is the opposite swap. -/
@[simp] theorem zNQuot.prod_commequiv_symmeq (H : Type*) [Group H]
    (n : ℕ) :
    (zNQuot.prodCommEquiv p G H n).symm =
      zNQuot.prodCommEquiv p H G n := by
  ext y
  simp [zNQuot.prod_commequiv_symmapply,
    zNQuot.prod_comm_equivapply]

/-- The inverse of the linear layer-kernel swap equivalence is the opposite linear swap. -/
@[simp] theorem zLKern.prodcomm_linequiv_symmeq [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    (zLKern.prod_comm_linequiv p G H n).symm =
      zLKern.prod_comm_linequiv p H G n := by
  ext y
  simp [zLKern.prodcomm_linequiv_symmapply,
    zLKern.prod_commlin_equivapply]

/-- The inverse of the linear consecutive-quotient swap equivalence is the opposite swap. -/
@[simp] theorem zNQuot.prodcomm_linequiv_symmeq [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p G H n).symm =
      zNQuot.prod_comm_linequiv p H G n := by
  ext y
  simp [zNQuot.prodcomm_linequiv_symmapply,
    zNQuot.prod_commlin_equivapply]


/-- Applying the layer-kernel swap twice is the identity. -/
@[simp] theorem zLKern.prod_commequiv_applyapply (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p H G n
      (zLKern.prodCommEquiv p G H n x) = x := by
  rw [← zLKern.prod_commequiv_symmeq (p := p) (G := G) H n]
  exact MulEquiv.symm_apply_apply (zLKern.prodCommEquiv p G H n) x

/-- Applying the consecutive-quotient swap twice is the identity. -/
@[simp] theorem zNQuot.prod_commequiv_applyapply (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p H G n
      (zNQuot.prodCommEquiv p G H n x) = x := by
  rw [← zNQuot.prod_commequiv_symmeq (p := p) (G := G) H n]
  exact MulEquiv.symm_apply_apply (zNQuot.prodCommEquiv p G H n) x

/-- Applying the linear layer-kernel swap twice is the identity. -/
@[simp] theorem zLKern.prodcomm_linequiv_applyapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p (G × H) n)) :
    zLKern.prod_comm_linequiv p H G n
      (zLKern.prod_comm_linequiv p G H n x) = x := by
  rw [← zLKern.prodcomm_linequiv_symmeq (p := p) (G := G) H n]
  exact LinearEquiv.symm_apply_apply (zLKern.prod_comm_linequiv p G H n) x

/-- Applying the linear consecutive-quotient swap twice is the identity. -/
@[simp] theorem zNQuot.prodcomm_linequiv_applyapply [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :
    zNQuot.prod_comm_linequiv p H G n
      (zNQuot.prod_comm_linequiv p G H n x) = x := by
  rw [← zNQuot.prodcomm_linequiv_symmeq (p := p) (G := G) H n]
  exact LinearEquiv.symm_apply_apply (zNQuot.prod_comm_linequiv p G H n) x


/-- The product-swap equivalence sends the left inclusion to the right inclusion. -/
@[simp] theorem zLKern.prod_commequiv_mapinl (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p G n) :
    zLKern.prodCommEquiv p G H n
      (zLKern.map p G (MonoidHom.inl G H) n x) =
    zLKern.map p G (MonoidHom.inr H G) n x := by
  change zLKern.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zLKern.map p G (MonoidHom.inl G H) n x) = _
  change ((zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zLKern.map p G (MonoidHom.inl G H) n)) x = _
  rw [← zLKern.map_comp]
  rfl

/-- The product-swap equivalence sends the right inclusion to the left inclusion. -/
@[simp] theorem zLKern.prod_commequiv_mapinr (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p H n) :
    zLKern.prodCommEquiv p G H n
      (zLKern.map p H (MonoidHom.inr G H) n x) =
    zLKern.map p H (MonoidHom.inl H G) n x := by
  change zLKern.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zLKern.map p H (MonoidHom.inr G H) n x) = _
  change ((zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zLKern.map p H (MonoidHom.inr G H) n)) x = _
  rw [← zLKern.map_comp]
  rfl


/-- The product-swap equivalence sends the left inclusion on consecutive quotients
to the right inclusion. -/
@[simp] theorem zNQuot.prod_commequiv_mapinl (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p G n ⧸ zNTerm p G n) :
    zNQuot.prodCommEquiv p G H n
      (zNQuot.map p G (MonoidHom.inl G H) n x) =
    zNQuot.map p G (MonoidHom.inr H G) n x := by
  change zNQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zNQuot.map p G (MonoidHom.inl G H) n x) = _
  change ((zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zNQuot.map p G (MonoidHom.inl G H) n)) x = _
  rw [← zNQuot.map_comp]
  rfl

/-- The product-swap equivalence sends the right inclusion on consecutive quotients
to the left inclusion. -/
@[simp] theorem zNQuot.prod_commequiv_mapinr (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p H n ⧸ zNTerm p H n) :
    zNQuot.prodCommEquiv p G H n
      (zNQuot.map p H (MonoidHom.inr G H) n x) =
    zNQuot.map p H (MonoidHom.inl H G) n x := by
  change zNQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zNQuot.map p H (MonoidHom.inr G H) n x) = _
  change ((zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zNQuot.map p H (MonoidHom.inr G H) n)) x = _
  rw [← zNQuot.map_comp]
  rfl


/-- The linear swap sends the additive left layer inclusion to the additive right inclusion. -/
@[simp] theorem zLKern.prodcomm_linequiv_maplininl [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p G n)) :
    zLKern.prod_comm_linequiv p G H n
      (zLKern.mapLinear p G (MonoidHom.inl G H) n x) =
    zLKern.mapLinear p G (MonoidHom.inr H G) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.prod_commequiv_mapinl (p := p) (G := G) H n x'

/-- The linear swap sends the additive right layer inclusion to the additive left inclusion. -/
@[simp] theorem zLKern.prodcomm_linequiv_maplininr [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p H n)) :
    zLKern.prod_comm_linequiv p G H n
      (zLKern.mapLinear p H (MonoidHom.inr G H) n x) =
    zLKern.mapLinear p H (MonoidHom.inl H G) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.prod_commequiv_mapinr (p := p) (G := G) H n x'

/-- The linear swap sends the additive left quotient inclusion to the additive right inclusion. -/
@[simp] theorem zNQuot.prodcomm_linequiv_maplininl [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p G n ⧸ zNTerm p G n)) :
    zNQuot.prod_comm_linequiv p G H n
      (zNQuot.mapLinear p G (MonoidHom.inl G H) n x) =
    zNQuot.mapLinear p G (MonoidHom.inr H G) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.prod_commequiv_mapinl (p := p) (G := G) H n x'

/-- The linear swap sends the additive right quotient inclusion to the additive left inclusion. -/
@[simp] theorem zNQuot.prodcomm_linequiv_maplininr [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p H n ⧸ zNTerm p H n)) :
    zNQuot.prod_comm_linequiv p G H n
      (zNQuot.mapLinear p H (MonoidHom.inr G H) n x) =
    zNQuot.mapLinear p H (MonoidHom.inl H G) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.prod_commequiv_mapinr (p := p) (G := G) H n x'


/-- Projecting the swapped layer kernel on the first factor equals the original
second projection. -/
@[simp] theorem zLKern.map_fstprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.map p (H × G) (MonoidHom.fst H G) n
      (zLKern.prodCommEquiv p G H n x) =
    zLKern.map p (G × H) (MonoidHom.snd G H) n x := by
  change zLKern.map p (H × G) (MonoidHom.fst H G) n
      (zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zLKern.map p (H × G) (MonoidHom.fst H G) n).comp
      (zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zLKern.map_comp]
  rfl

/-- Projecting the swapped layer kernel on the second factor equals the original
first projection. -/
@[simp] theorem zLKern.map_sndprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.map p (H × G) (MonoidHom.snd H G) n
      (zLKern.prodCommEquiv p G H n x) =
    zLKern.map p (G × H) (MonoidHom.fst G H) n x := by
  change zLKern.map p (H × G) (MonoidHom.snd H G) n
      (zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zLKern.map p (H × G) (MonoidHom.snd H G) n).comp
      (zLKern.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zLKern.map_comp]
  rfl


/-- Projecting the swapped consecutive quotient on the first factor equals the original
second projection. -/
@[simp] theorem zNQuot.map_fstprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.map p (H × G) (MonoidHom.fst H G) n
      (zNQuot.prodCommEquiv p G H n x) =
    zNQuot.map p (G × H) (MonoidHom.snd G H) n x := by
  change zNQuot.map p (H × G) (MonoidHom.fst H G) n
      (zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zNQuot.map p (H × G) (MonoidHom.fst H G) n).comp
      (zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zNQuot.map_comp]
  rfl

/-- Projecting the swapped consecutive quotient on the second factor equals the original
first projection. -/
@[simp] theorem zNQuot.map_sndprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.map p (H × G) (MonoidHom.snd H G) n
      (zNQuot.prodCommEquiv p G H n x) =
    zNQuot.map p (G × H) (MonoidHom.fst G H) n x := by
  change zNQuot.map p (H × G) (MonoidHom.snd H G) n
      (zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zNQuot.map p (H × G) (MonoidHom.snd H G) n).comp
      (zNQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zNQuot.map_comp]
  rfl


/-- Linear projection after swapping a layer kernel agrees with the original second projection. -/
@[simp] theorem zLKern.maplin_fstprod_commlinequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p (G × H) n)) :
    zLKern.mapLinear p (H × G) (MonoidHom.fst H G) n
      (zLKern.prod_comm_linequiv p G H n x) =
    zLKern.mapLinear p (G × H) (MonoidHom.snd G H) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.map_fstprod_commequiv (p := p) (G := G) H n x'

/-- Linear projection after swapping a layer kernel agrees with the original first projection. -/
@[simp] theorem zLKern.maplin_sndprod_commlinequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zLKern p (G × H) n)) :
    zLKern.mapLinear p (H × G) (MonoidHom.snd H G) n
      (zLKern.prod_comm_linequiv p G H n x) =
    zLKern.mapLinear p (G × H) (MonoidHom.fst G H) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.map_sndprod_commequiv (p := p) (G := G) H n x'

/-- Linear projection after swapping a consecutive quotient agrees with the original
second projection. -/
@[simp] theorem zNQuot.maplin_fstprod_commlinequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :
    zNQuot.mapLinear p (H × G) (MonoidHom.fst H G) n
      (zNQuot.prod_comm_linequiv p G H n x) =
    zNQuot.mapLinear p (G × H) (MonoidHom.snd G H) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.map_fstprod_commequiv (p := p) (G := G) H n x'

/-- Linear projection after swapping a consecutive quotient agrees with the original
first projection. -/
@[simp] theorem zNQuot.maplin_sndprod_commlinequiv [Fact p.Prime]
    (H : Type*) [Group H] (n : ℕ)
    (x : Additive (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n)) :
    zNQuot.mapLinear p (H × G) (MonoidHom.snd H G) n
      (zNQuot.prod_comm_linequiv p G H n x) =
    zNQuot.mapLinear p (G × H) (MonoidHom.fst G H) n x := by
  cases x with
  | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.map_sndprod_commequiv (p := p) (G := G) H n x'


/-- Under product swap, the left-inclusion range in a layer becomes the right-inclusion range. -/
theorem zLKern.prodcomm_equivmem_rangeinliff (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p G H n x ∈
        (zLKern.map p G (MonoidHom.inr H G) n).range ↔
      x ∈ (zLKern.map p G (MonoidHom.inl G H) n).range := by
  rw [zLKern.memrange_inriffmap_fsteqone (p := p) (G := H) G n,
    zLKern.map_fstprod_commequiv (p := p) (G := G) H n,
    ← zLKern.memrange_inliffmap_sndeqone (p := p) (G := G) H n]

/-- Under product swap, the right-inclusion range in a layer becomes the left-inclusion range. -/
theorem zLKern.prodcomm_equivmem_rangeinriff (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p G H n x ∈
        (zLKern.map p H (MonoidHom.inl H G) n).range ↔
      x ∈ (zLKern.map p H (MonoidHom.inr G H) n).range := by
  rw [zLKern.memrange_inliffmap_sndeqone (p := p) (G := H) G n,
    zLKern.map_sndprod_commequiv (p := p) (G := G) H n,
    ← zLKern.memrange_inriffmap_fsteqone (p := p) (G := G) H n]


/-- Under product swap, the left-inclusion range in a consecutive quotient becomes
the right range. -/
theorem zNQuot.prodcomm_equivmem_rangeinliff (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p G H n x ∈
        (zNQuot.map p G (MonoidHom.inr H G) n).range ↔
      x ∈ (zNQuot.map p G (MonoidHom.inl G H) n).range := by
  rw [zNQuot.memrange_inriffmap_fsteqone (p := p) (G := H) G n,
    zNQuot.map_fstprod_commequiv (p := p) (G := G) H n,
    ← zNQuot.memrange_inliffmap_sndeqone (p := p) (G := G) H n]

/-- Under product swap, the right-inclusion range in a consecutive quotient becomes
the left range. -/
theorem zNQuot.prodcomm_equivmem_rangeinriff (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p G H n x ∈
        (zNQuot.map p H (MonoidHom.inl H G) n).range ↔
      x ∈ (zNQuot.map p H (MonoidHom.inr G H) n).range := by
  rw [zNQuot.memrange_inliffmap_sndeqone (p := p) (G := H) G n,
    zNQuot.map_sndprod_commequiv (p := p) (G := G) H n,
    ← zNQuot.memrange_inriffmap_fsteqone (p := p) (G := G) H n]


/-- Swap converts the first-projection kernel on layer kernels to the second-projection kernel. -/
theorem zLKern.prodcomm_equivmem_kerfstiff (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p G H n x ∈
        (zLKern.map p (H × G) (MonoidHom.fst H G) n).ker ↔
      x ∈ (zLKern.map p (G × H) (MonoidHom.snd G H) n).ker := by
  change zLKern.map p (H × G) (MonoidHom.fst H G) n
        (zLKern.prodCommEquiv p G H n x) = 1 ↔
      zLKern.map p (G × H) (MonoidHom.snd G H) n x = 1
  rw [zLKern.map_fstprod_commequiv]

/-- Swap converts the second-projection kernel on layer kernels to the first-projection kernel. -/
theorem zLKern.prodcomm_equivmem_kersndiff (H : Type*) [Group H]
    (n : ℕ) (x : zLKern p (G × H) n) :
    zLKern.prodCommEquiv p G H n x ∈
        (zLKern.map p (H × G) (MonoidHom.snd H G) n).ker ↔
      x ∈ (zLKern.map p (G × H) (MonoidHom.fst G H) n).ker := by
  change zLKern.map p (H × G) (MonoidHom.snd H G) n
        (zLKern.prodCommEquiv p G H n x) = 1 ↔
      zLKern.map p (G × H) (MonoidHom.fst G H) n x = 1
  rw [zLKern.map_sndprod_commequiv]


/-- Swap converts the first-projection kernel on consecutive quotients to the second one. -/
theorem zNQuot.prodcomm_equivmem_kerfstiff (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p G H n x ∈
        (zNQuot.map p (H × G) (MonoidHom.fst H G) n).ker ↔
      x ∈ (zNQuot.map p (G × H) (MonoidHom.snd G H) n).ker := by
  change zNQuot.map p (H × G) (MonoidHom.fst H G) n
        (zNQuot.prodCommEquiv p G H n x) = 1 ↔
      zNQuot.map p (G × H) (MonoidHom.snd G H) n x = 1
  rw [zNQuot.map_fstprod_commequiv]

/-- Swap converts the second-projection kernel on consecutive quotients to the first one. -/
theorem zNQuot.prodcomm_equivmem_kersndiff (H : Type*) [Group H]
    (n : ℕ) (x : zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) :
    zNQuot.prodCommEquiv p G H n x ∈
        (zNQuot.map p (H × G) (MonoidHom.snd H G) n).ker ↔
      x ∈ (zNQuot.map p (G × H) (MonoidHom.fst G H) n).ker := by
  change zNQuot.map p (H × G) (MonoidHom.snd H G) n
        (zNQuot.prodCommEquiv p G H n x) = 1 ↔
      zNQuot.map p (G × H) (MonoidHom.fst G H) n x = 1
  rw [zNQuot.map_sndprod_commequiv]


/-- Swap equivalence for ordinary Zassenhaus quotients of a product. -/
noncomputable def zQuot.prodCommEquiv (H : Type*) [Group H] (n : ℕ) :
    zQuot p (G × H) n ≃* zQuot p (H × G) n :=
  MulEquiv.ofBijective
    (zQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg (fun z => zQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n z) hxy
      calc
        x = zQuot.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zQuot.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) :=
          (zQuot.map_prodcomm_prodcomm (p := p) (G := G) H n x).symm
        _ = zQuot.map p (H × G)
            ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n
            (zQuot.map p (G × H)
              ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n y) := h
        _ = y := zQuot.map_prodcomm_prodcomm (p := p) (G := G) H n y
    · intro y
      refine ⟨zQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y, ?_⟩
      exact zQuot.map_prodcomm_prodcomm (p := p) (G := H) G n y

@[simp] theorem zQuot.prod_comm_equivapply (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p G H n x =
      zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x := rfl

@[simp] theorem zQuot.prod_commequiv_monoidhom (H : Type*) [Group H]
    (n : ℕ) :
    (zQuot.prodCommEquiv p G H n).toMonoidHom =
      zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n := rfl

@[simp] theorem zQuot.prod_commequiv_symmapply (H : Type*) [Group H]
    (n : ℕ) (y : zQuot p (H × G) n) :
    (zQuot.prodCommEquiv p G H n).symm y =
      zQuot.map p (H × G)
        ((MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom) n y := by
  apply (zQuot.prodCommEquiv p G H n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zQuot.map_prodcomm_prodcomm (p := p) (G := H) G n y).symm

@[simp] theorem zQuot.prod_commequiv_symmeq (H : Type*) [Group H]
    (n : ℕ) :
    (zQuot.prodCommEquiv p G H n).symm =
      zQuot.prodCommEquiv p H G n := by
  ext y
  simp [zQuot.prod_commequiv_symmapply,
    zQuot.prod_comm_equivapply]

/-- Projecting the swapped ordinary quotient on the first factor equals the original
second projection. -/
@[simp] theorem zQuot.map_fstprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.map p (H × G) (MonoidHom.fst H G) n
      (zQuot.prodCommEquiv p G H n x) =
    zQuot.map p (G × H) (MonoidHom.snd G H) n x := by
  change zQuot.map p (H × G) (MonoidHom.fst H G) n
      (zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zQuot.map p (H × G) (MonoidHom.fst H G) n).comp
      (zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zQuot.map_comp]
  rfl

/-- Projecting the swapped ordinary quotient on the second factor equals the original
first projection. -/
@[simp] theorem zQuot.map_sndprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.map p (H × G) (MonoidHom.snd H G) n
      (zQuot.prodCommEquiv p G H n x) =
    zQuot.map p (G × H) (MonoidHom.fst G H) n x := by
  change zQuot.map p (H × G) (MonoidHom.snd H G) n
      (zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n x) = _
  change ((zQuot.map p (H × G) (MonoidHom.snd H G) n).comp
      (zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n)) x = _
  rw [← zQuot.map_comp]
  rfl

/-- Under product swap, the left-inclusion range in an ordinary quotient becomes the right range. -/
theorem zQuot.prodcomm_equivmem_rangeinliff (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p G H n x ∈
        (zQuot.map p G (MonoidHom.inr H G) n).range ↔
      x ∈ (zQuot.map p G (MonoidHom.inl G H) n).range := by
  rw [zQuot.memrange_inriffmap_fsteqone (p := p) (G := H) G n,
    zQuot.map_fstprod_commequiv (p := p) (G := G) H n,
    ← zQuot.memrange_inliffmap_sndeqone (p := p) (G := G) H n]

/-- Under product swap, the right-inclusion range in an ordinary quotient becomes the left range. -/
theorem zQuot.prodcomm_equivmem_rangeinriff (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p G H n x ∈
        (zQuot.map p H (MonoidHom.inl H G) n).range ↔
      x ∈ (zQuot.map p H (MonoidHom.inr G H) n).range := by
  rw [zQuot.memrange_inliffmap_sndeqone (p := p) (G := H) G n,
    zQuot.map_sndprod_commequiv (p := p) (G := G) H n,
    ← zQuot.memrange_inriffmap_fsteqone (p := p) (G := G) H n]


/-- Applying the ordinary quotient swap twice is the identity. -/
@[simp] theorem zQuot.prod_commequiv_applyapply (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p H G n
      (zQuot.prodCommEquiv p G H n x) = x := by
  rw [← zQuot.prod_commequiv_symmeq (p := p) (G := G) H n]
  exact MulEquiv.symm_apply_apply (zQuot.prodCommEquiv p G H n) x

/-- Swap converts the first-projection kernel on ordinary quotients to the
second-projection kernel. -/
theorem zQuot.prodcomm_equivmem_kerfstiff (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p G H n x ∈
        (zQuot.map p (H × G) (MonoidHom.fst H G) n).ker ↔
      x ∈ (zQuot.map p (G × H) (MonoidHom.snd G H) n).ker := by
  change zQuot.map p (H × G) (MonoidHom.fst H G) n
        (zQuot.prodCommEquiv p G H n x) = 1 ↔
      zQuot.map p (G × H) (MonoidHom.snd G H) n x = 1
  rw [zQuot.map_fstprod_commequiv]

/-- Swap converts the second-projection kernel on ordinary quotients to the
first-projection kernel. -/
theorem zQuot.prodcomm_equivmem_kersndiff (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodCommEquiv p G H n x ∈
        (zQuot.map p (H × G) (MonoidHom.snd H G) n).ker ↔
      x ∈ (zQuot.map p (G × H) (MonoidHom.fst G H) n).ker := by
  change zQuot.map p (H × G) (MonoidHom.snd H G) n
        (zQuot.prodCommEquiv p G H n x) = 1 ↔
      zQuot.map p (G × H) (MonoidHom.fst G H) n x = 1
  rw [zQuot.map_sndprod_commequiv]


/-- The product-swap equivalence sends the left inclusion on ordinary quotients
to the right inclusion. -/
@[simp] theorem zQuot.prod_commequiv_mapinl (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p G n) :
    zQuot.prodCommEquiv p G H n
      (zQuot.map p G (MonoidHom.inl G H) n x) =
    zQuot.map p G (MonoidHom.inr H G) n x := by
  change zQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zQuot.map p G (MonoidHom.inl G H) n x) = _
  change ((zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zQuot.map p G (MonoidHom.inl G H) n)) x = _
  rw [← zQuot.map_comp]
  rfl

/-- The product-swap equivalence sends the right inclusion on ordinary quotients
to the left inclusion. -/
@[simp] theorem zQuot.prod_commequiv_mapinr (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p H n) :
    zQuot.prodCommEquiv p G H n
      (zQuot.map p H (MonoidHom.inr G H) n x) =
    zQuot.map p H (MonoidHom.inl H G) n x := by
  change zQuot.map p (G × H)
      ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n
      (zQuot.map p H (MonoidHom.inr G H) n x) = _
  change ((zQuot.map p (G × H)
        ((MulEquiv.prodComm : G × H ≃* H × G).toMonoidHom) n).comp
      (zQuot.map p H (MonoidHom.inr G H) n)) x = _
  rw [← zQuot.map_comp]
  rfl


/-- Reassociation equivalence for ordinary Zassenhaus quotients. -/
noncomputable def zQuot.prodAssocEquiv (H K : Type*) [Group H] [Group K]
    (n : ℕ) :
    zQuot p ((G × H) × K) n ≃*
      zQuot p (G × (H × K)) n :=
  MulEquiv.ofBijective
    (zQuot.map p ((G × H) × K)
      ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n) <| by
    constructor
    · intro x y hxy
      have h := congrArg
        (fun z => zQuot.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n z) hxy
      calc
        x = zQuot.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zQuot.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) :=
          (zQuot.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n x).symm
        _ = zQuot.map p (G × H × K)
            ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n
            (zQuot.map p ((G × H) × K)
              ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n y) := h
        _ = y := zQuot.mapprod_assocsymm_prodassoc
            (p := p) (G := G) H K n y
    · intro y
      refine ⟨zQuot.map p (G × H × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y, ?_⟩
      exact zQuot.mapprod_assocprod_assocsymm
        (p := p) (G := G) H K n y

@[simp] theorem zQuot.prod_assoc_equivapply (H K : Type*) [Group H]
    [Group K] (n : ℕ) (x : zQuot p ((G × H) × K) n) :
    zQuot.prodAssocEquiv p G H K n x =
      zQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x := rfl

@[simp] theorem zQuot.prod_assocequiv_monoidhom (H K : Type*)
    [Group H] [Group K] (n : ℕ) :
    (zQuot.prodAssocEquiv p G H K n).toMonoidHom =
      zQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n := rfl

@[simp] theorem zQuot.prod_assocequiv_symmapply (H K : Type*)
    [Group H] [Group K] (n : ℕ) (y : zQuot p (G × (H × K)) n) :
    (zQuot.prodAssocEquiv p G H K n).symm y =
      zQuot.map p (G × H × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).symm.toMonoidHom) n y := by
  apply (zQuot.prodAssocEquiv p G H K n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (zQuot.mapprod_assocprod_assocsymm
    (p := p) (G := G) H K n y).symm

/-- Applying the ordinary quotient reassociation equivalence and its inverse is identity. -/
@[simp] theorem zQuot.prodassoc_equivapply_symmapply (H K : Type*)
    [Group H] [Group K] (n : ℕ) (y : zQuot p (G × (H × K)) n) :
    zQuot.prodAssocEquiv p G H K n
      ((zQuot.prodAssocEquiv p G H K n).symm y) = y := by
  exact MulEquiv.apply_symm_apply (zQuot.prodAssocEquiv p G H K n) y


/-- Product decomposition of the ordinary quotient swap: it swaps the two coordinates. -/
@[simp] theorem zQuot.prod_equivprod_commequiv (H : Type*) [Group H]
    (n : ℕ) (x : zQuot p (G × H) n) :
    zQuot.prodEquiv p H G n
        (zQuot.prodCommEquiv p G H n x) =
      ((zQuot.prodEquiv p G H n x).2,
        (zQuot.prodEquiv p G H n x).1) := by
  simpa [zQuot.prod_comm_equivapply] using
    zQuot.prod_equiv_swapapply (p := p) (G := G) H n x

/-- Product decomposition of the inverse ordinary quotient swap. -/
@[simp] theorem zQuot.prodequiv_prodcomm_equivsymm (H : Type*) [Group H]
    (n : ℕ) (y : zQuot p (H × G) n) :
    zQuot.prodEquiv p G H n
        ((zQuot.prodCommEquiv p G H n).symm y) =
      ((zQuot.prodEquiv p H G n y).2,
        (zQuot.prodEquiv p H G n y).1) := by
  rw [zQuot.prod_commequiv_symmeq]
  exact zQuot.prod_equivprod_commequiv (p := p) (G := H) G n y


@[simp] theorem zQuot.prod_assoc_equivmk (H K : Type*) [Group H]
    [Group K] (n : ℕ) (g : G) (h : H) (k : K) :
    zQuot.prodAssocEquiv p G H K n
        (QuotientGroup.mk' (zSubgro p ((G × H) × K) n) ((g, h), k)) =
      QuotientGroup.mk' (zSubgro p (G × (H × K)) n) (g, (h, k)) := rfl

@[simp] theorem zQuot.prod_assocequiv_symmmk (H K : Type*) [Group H]
    [Group K] (n : ℕ) (g : G) (h : H) (k : K) :
    (zQuot.prodAssocEquiv p G H K n).symm
        (QuotientGroup.mk' (zSubgro p (G × (H × K)) n) (g, (h, k))) =
      QuotientGroup.mk' (zSubgro p ((G × H) × K) n) ((g, h), k) := by
  rw [zQuot.prod_assocequiv_symmapply]
  rfl


@[simp] theorem zQuot.prod_comm_equivmk (H : Type*) [Group H]
    (n : ℕ) (g : G) (h : H) :
    zQuot.prodCommEquiv p G H n
        (QuotientGroup.mk' (zSubgro p (G × H) n) (g, h)) =
      QuotientGroup.mk' (zSubgro p (H × G) n) (h, g) := rfl

@[simp] theorem zQuot.prod_commequiv_symmmk (H : Type*) [Group H]
    (n : ℕ) (h : H) (g : G) :
    (zQuot.prodCommEquiv p G H n).symm
        (QuotientGroup.mk' (zSubgro p (H × G) n) (h, g)) =
      QuotientGroup.mk' (zSubgro p (G × H) n) (g, h) := by
  rw [zQuot.prod_commequiv_symmapply]
  rfl


/-- The first projection after reassociating an ordinary quotient is the iterated
first projection. -/
@[simp] theorem zQuot.mapfst_fstprod_assocequiv (H K : Type*)
    [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    zQuot.map p (G × (H × K)) (MonoidHom.fst G (H × K)) n
      (zQuot.prodAssocEquiv p G H K n x) =
    zQuot.map p (G × H) (MonoidHom.fst G H) n
      (zQuot.map p ((G × H) × K) (MonoidHom.fst (G × H) K) n x) := by
  change zQuot.map p (G × H × K) (MonoidHom.fst G (H × K)) n
      (zQuot.map p ((G × H) × K)
        ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x) = _
  rw [← MonoidHom.comp_apply]
  rw [← zQuot.map_comp]
  rw [← MonoidHom.comp_apply]
  rw [← zQuot.map_comp]
  rfl

/-- The last projection after reassociating an ordinary quotient is the original last projection. -/
@[simp] theorem zQuot.mapsnd_sndprod_assocequiv (H K : Type*)
    [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    zQuot.map p (H × K) (MonoidHom.snd H K) n
      (zQuot.map p (G × (H × K)) (MonoidHom.snd G (H × K)) n
        (zQuot.prodAssocEquiv p G H K n x)) =
    zQuot.map p ((G × H) × K) (MonoidHom.snd (G × H) K) n x := by
  change zQuot.map p (H × K) (MonoidHom.snd H K) n
      (zQuot.map p (G × H × K) (MonoidHom.snd G (H × K)) n
        (zQuot.map p ((G × H) × K)
          ((MulEquiv.prodAssoc : (G × H) × K ≃* G × H × K).toMonoidHom) n x)) = _
  rw [← MonoidHom.comp_apply, ← zQuot.map_comp]
  rw [← MonoidHom.comp_apply, ← zQuot.map_comp]
  rfl


/-- Pentagon coherence for ordinary Zassenhaus-quotient associator maps. -/
theorem zQuot.map_prod_assocpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zQuot p (((G × H) × K) × L) n) :
    zQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (zQuot.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    zQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zQuot.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (zQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨abc, d⟩
  rcases abc with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl


/-- Pentagon coherence for packaged ordinary Zassenhaus-quotient associators. -/
theorem zQuot.prod_assoc_equivpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zQuot p (((G × H) × K) × L) n) :
    zQuot.prodAssocEquiv p G H (K × L) n
      (zQuot.prodAssocEquiv p (G × H) K L n x) =
    zQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zQuot.prodAssocEquiv p G (H × K) L n
        (zQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [zQuot.prod_assoc_equivapply] using
    zQuot.map_prod_assocpentagon (p := p) (G := G) H K L n x



/-- Pentagon coherence for consecutive Zassenhaus-quotient associator maps. -/
theorem zNQuot.map_prod_assocpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zSubgro p (((G × H) × K) × L) n ⧸
      zNTerm p (((G × H) × K) × L) n) :
    zNQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (zNQuot.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    zNQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zNQuot.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (zNQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨abc, d⟩
  rcases abc with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl



/-- Pentagon coherence for packaged consecutive Zassenhaus-quotient associators. -/
theorem zNQuot.prod_assoc_equivpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zSubgro p (((G × H) × K) × L) n ⧸
      zNTerm p (((G × H) × K) × L) n) :
    zNQuot.prodAssocEquiv p G H (K × L) n
      (zNQuot.prodAssocEquiv p (G × H) K L n x) =
    zNQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zNQuot.prodAssocEquiv p G (H × K) L n
        (zNQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [zNQuot.prod_assoc_equivapply] using
    zNQuot.map_prod_assocpentagon (p := p) (G := G) H K L n x



/-- Pentagon coherence for Zassenhaus layer-kernel associator maps. -/
theorem zLKern.map_prod_assocpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zLKern p (((G × H) × K) × L) n) :
    zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (zLKern.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    zLKern.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zLKern.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (zLKern.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  change (((zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
    (zLKern.map p (((G × H) × K) × L)
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n)) x) = _
  rw [← zLKern.map_comp (p := p) (G := (((G × H) × K) × L))
    (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n]
  change (zLKern.map p (((G × H) × K) × L) _ n x) =
    (((zLKern.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zLKern.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zLKern.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)))) x
  rw [← zLKern.map_comp (p := p) (G := (((G × H) × K) × L))
    (MonoidHom.prodMap
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
      (MonoidHom.id L))
    (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n]
  rw [← zLKern.map_comp (p := p) (G := (((G × H) × K) × L))
    ((MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom.comp
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
        (MonoidHom.id L)))
    (MonoidHom.prodMap (MonoidHom.id G)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n]
  rfl



/-- Pentagon coherence for packaged Zassenhaus layer-kernel associators. -/
theorem zLKern.prod_assoc_equivpentagon
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : zLKern p (((G × H) × K) × L) n) :
    zLKern.prodAssocEquiv p G H (K × L) n
      (zLKern.prodAssocEquiv p (G × H) K L n x) =
    zLKern.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zLKern.prodAssocEquiv p G (H × K) L n
        (zLKern.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [zLKern.prod_assoc_equivapply] using
    zLKern.map_prod_assocpentagon (p := p) (G := G) H K L n x



/-- Linear pentagon coherence for consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.map_linprod_assocpentagon [Fact p.Prime]
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zSubgro p (((G × H) × K) × L) n ⧸
      zNTerm p (((G × H) × K) × L) n)) :
    zNQuot.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (zNQuot.mapLinear p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    zNQuot.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zNQuot.mapLinear p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (zNQuot.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.map_prod_assocpentagon (p := p) (G := G) H K L n x'



/-- Linear pentagon coherence for Zassenhaus layer kernels (prime case). -/
theorem zLKern.map_linprod_assocpentagon [Fact p.Prime]
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zLKern p (((G × H) × K) × L) n)) :
    zLKern.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n
      (zLKern.mapLinear p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n x) =
    zLKern.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zLKern.mapLinear p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n
        (zLKern.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.map_prod_assocpentagon (p := p) (G := G) H K L n x'



/-- Pentagon coherence for packaged linear consecutive Zassenhaus associators. -/
theorem zNQuot.prod_assoclin_equivpentagon [Fact p.Prime]
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zSubgro p (((G × H) × K) × L) n ⧸
      zNTerm p (((G × H) × K) × L) n)) :
    zNQuot.prod_assoc_linequiv p G H (K × L) n
      (zNQuot.prod_assoc_linequiv p (G × H) K L n x) =
    zNQuot.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zNQuot.prod_assoc_linequiv p G (H × K) L n
        (zNQuot.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [zNQuot.prod_assoclin_equivapply] using
    zNQuot.map_linprod_assocpentagon (p := p) (G := G) H K L n x

/-- Pentagon coherence for packaged linear Zassenhaus layer-kernel associators. -/
theorem zLKern.prod_assoclin_equivpentagon [Fact p.Prime]
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zLKern p (((G × H) × K) × L) n)) :
    zLKern.prod_assoc_linequiv p G H (K × L) n
      (zLKern.prod_assoc_linequiv p (G × H) K L n x) =
    zLKern.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n
      (zLKern.prod_assoc_linequiv p G (H × K) L n
        (zLKern.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n x)) := by
  simpa [zLKern.prod_assoclin_equivapply] using
    zLKern.map_linprod_assocpentagon (p := p) (G := G) H K L n x



/-- Hexagon coherence for moving a left factor past a binary product on Zassenhaus quotients. -/
theorem zQuot.mapprod_commassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p (G × (H × K)) n) :
    zQuot.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    zQuot.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (zQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (zQuot.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (zQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (zQuot.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor on Zassenhaus quotients. -/
theorem zQuot.mapprod_commassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    zQuot.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    zQuot.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (zQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (zQuot.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (zQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (zQuot.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl



/-- Packaged hexagon coherence for moving a left factor past a binary product
on Zassenhaus quotients. -/
theorem zQuot.prodcomm_equivassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p (G × (H × K)) n) :
    zQuot.prodCommEquiv p G (H × K) n x =
      (zQuot.prodAssocEquiv p H K G n).symm
        (zQuot.map p (H × (G × K))
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (zQuot.prodAssocEquiv p H G K n
            (zQuot.map p ((G × H) × K)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((zQuot.prodAssocEquiv p G H K n).symm x)))) := by
  simpa [zQuot.prod_comm_equivapply,
    zQuot.prod_assoc_equivapply,
    zQuot.prod_assocequiv_symmapply] using
    zQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor
on Zassenhaus quotients. -/
theorem zQuot.prodcomm_equivassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((G × H) × K) n) :
    zQuot.prodCommEquiv p (G × H) K n x =
      zQuot.prodAssocEquiv p K G H n
        (zQuot.map p ((G × K) × H)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((zQuot.prodAssocEquiv p G K H n).symm
            (zQuot.map p (G × (H × K))
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (zQuot.prodAssocEquiv p G H K n x)))) := by
  simpa [zQuot.prod_comm_equivapply,
    zQuot.prod_assoc_equivapply,
    zQuot.prod_assocequiv_symmapply] using
    zQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x



/-- Hexagon coherence for moving a left factor past a binary product
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mapprod_commassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :
    zNQuot.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    zNQuot.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (zNQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (zNQuot.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (zNQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (zNQuot.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨a, bc⟩
  rcases bc with ⟨b, c⟩
  rfl

/-- Hexagon coherence for moving a binary product past a right factor
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mapprod_commassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :
    zNQuot.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    zNQuot.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (zNQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (zNQuot.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (zNQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (zNQuot.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨ab, c⟩
  rcases ab with ⟨a, b⟩
  rfl



/-- Packaged hexagon coherence for moving a left factor past a binary product
on consecutive Zassenhaus quotients. -/
theorem zNQuot.prodcomm_equivassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) :
    zNQuot.prodCommEquiv p G (H × K) n x =
      (zNQuot.prodAssocEquiv p H K G n).symm
        (zNQuot.map p (H × (G × K))
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (zNQuot.prodAssocEquiv p H G K n
            (zNQuot.map p ((G × H) × K)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((zNQuot.prodAssocEquiv p G H K n).symm x)))) := by
  simpa [zNQuot.prod_comm_equivapply,
    zNQuot.prod_assoc_equivapply,
    zNQuot.prod_assocequiv_symmapply] using
    zNQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor
on consecutive Zassenhaus quotients. -/
theorem zNQuot.prodcomm_equivassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) :
    zNQuot.prodCommEquiv p (G × H) K n x =
      zNQuot.prodAssocEquiv p K G H n
        (zNQuot.map p ((G × K) × H)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((zNQuot.prodAssocEquiv p G K H n).symm
            (zNQuot.map p (G × (H × K))
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (zNQuot.prodAssocEquiv p G H K n x)))) := by
  simpa [zNQuot.prod_comm_equivapply,
    zNQuot.prod_assoc_equivapply,
    zNQuot.prod_assocequiv_symmapply] using
    zNQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x



/-- Hexagon coherence for moving a left factor past a binary product on Zassenhaus
layer kernels. -/
theorem zLKern.mapprod_commassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p (G × (H × K)) n) :
    zLKern.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    zLKern.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (zLKern.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (zLKern.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (zLKern.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (zLKern.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [zLKern.map_coe]
  exact zQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K (n + 1)
    (x : zQuot p (G × (H × K)) (n + 1))


/-- Hexagon coherence for moving a binary product past a right factor on Zassenhaus
layer kernels. -/
theorem zLKern.mapprod_commassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((G × H) × K) n) :
    zLKern.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    zLKern.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (zLKern.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (zLKern.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (zLKern.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (zLKern.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [zLKern.map_coe]
  exact zQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K (n + 1)
    (x : zQuot p ((G × H) × K) (n + 1))


/-- Packaged hexagon coherence for moving a left factor past a binary product
on Zassenhaus layer kernels. -/
theorem zLKern.prodcomm_equivassoc_hexagonleft
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p (G × (H × K)) n) :
    zLKern.prodCommEquiv p G (H × K) n x =
      (zLKern.prodAssocEquiv p H K G n).symm
        (zLKern.map p (H × (G × K))
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (zLKern.prodAssocEquiv p H G K n
            (zLKern.map p ((G × H) × K)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((zLKern.prodAssocEquiv p G H K n).symm x)))) := by
  simpa [zLKern.prod_comm_equivapply,
    zLKern.prod_assoc_equivapply,
    zLKern.prod_assocequiv_symmapply] using
    zLKern.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x

/-- Packaged hexagon coherence for moving a binary product past a right factor
on Zassenhaus layer kernels. -/
theorem zLKern.prodcomm_equivassoc_hexagonright
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((G × H) × K) n) :
    zLKern.prodCommEquiv p (G × H) K n x =
      zLKern.prodAssocEquiv p K G H n
        (zLKern.map p ((G × K) × H)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((zLKern.prodAssocEquiv p G K H n).symm
            (zLKern.map p (G × (H × K))
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (zLKern.prodAssocEquiv p G H K n x)))) := by
  simpa [zLKern.prod_comm_equivapply,
    zLKern.prod_assoc_equivapply,
    zLKern.prod_assocequiv_symmapply] using
    zLKern.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x


/-- Linear hexagon coherence for moving a left factor past a binary product on
consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.maplin_prodcomm_assohexaleft [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :
    zNQuot.mapLinear p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    zNQuot.mapLinear p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (zNQuot.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (zNQuot.mapLinear p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (zNQuot.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (zNQuot.mapLinear p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x'


/-- Linear hexagon coherence for moving a binary product past a right factor on
consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.maplin_prodcomm_assohexarigh [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :
    zNQuot.mapLinear p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    zNQuot.mapLinear p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (zNQuot.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (zNQuot.mapLinear p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (zNQuot.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (zNQuot.mapLinear p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x'

/-- Linear hexagon coherence for moving a left factor past a binary product on
Zassenhaus layer kernels (prime case). -/
theorem zLKern.maplin_prodcomm_assohexaleft [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p (G × (H × K)) n)) :
    zLKern.mapLinear p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n x =
    zLKern.mapLinear p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n
      (zLKern.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
        (zLKern.mapLinear p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n
          (zLKern.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n
            (zLKern.mapLinear p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x'

/-- Linear hexagon coherence for moving a binary product past a right factor on
Zassenhaus layer kernels (prime case). -/
theorem zLKern.maplin_prodcomm_assohexarigh [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p ((G × H) × K) n)) :
    zLKern.mapLinear p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n x =
    zLKern.mapLinear p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n
      (zLKern.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n
        (zLKern.mapLinear p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n
          (zLKern.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
            (zLKern.mapLinear p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x'


/-- Packaged linear hexagon coherence for moving a left factor past a binary product
on consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.prodcomm_linequiv_assohexaleft [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n)) :
    zNQuot.prod_comm_linequiv p G (H × K) n x =
      (zNQuot.prod_assoc_linequiv p H K G n).symm
        (zNQuot.mapLinear p (H × (G × K))
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (zNQuot.prod_assoc_linequiv p H G K n
            (zNQuot.mapLinear p ((G × H) × K)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((zNQuot.prod_assoc_linequiv p G H K n).symm x)))) := by
  simpa [zNQuot.prod_commlin_equivapply,
    zNQuot.prod_assoclin_equivapply,
    zNQuot.prodassoc_linequiv_symmapply] using
    zNQuot.maplin_prodcomm_assohexaleft (p := p) (G := G) H K n x

/-- Packaged linear hexagon coherence for moving a binary product past a right factor
on consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.prodcomm_linequiv_assohexarigh [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n)) :
    zNQuot.prod_comm_linequiv p (G × H) K n x =
      zNQuot.prod_assoc_linequiv p K G H n
        (zNQuot.mapLinear p ((G × K) × H)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((zNQuot.prod_assoc_linequiv p G K H n).symm
            (zNQuot.mapLinear p (G × (H × K))
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (zNQuot.prod_assoc_linequiv p G H K n x)))) := by
  simpa [zNQuot.prod_commlin_equivapply,
    zNQuot.prod_assoclin_equivapply,
    zNQuot.prodassoc_linequiv_symmapply] using
    zNQuot.maplin_prodcomm_assohexarigh (p := p) (G := G) H K n x


/-- Packaged linear hexagon coherence for moving a left factor past a binary product
on Zassenhaus layer kernels (prime case). -/
theorem zLKern.prodcomm_linequiv_assohexaleft [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p (G × (H × K)) n)) :
    zLKern.prod_comm_linequiv p G (H × K) n x =
      (zLKern.prod_assoc_linequiv p H K G n).symm
        (zLKern.mapLinear p (H × (G × K))
          (MonoidHom.prodMap (MonoidHom.id H)
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n
          (zLKern.prod_assoc_linequiv p H G K n
            (zLKern.mapLinear p ((G × H) × K)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
                (MonoidHom.id K)) n
              ((zLKern.prod_assoc_linequiv p G H K n).symm x)))) := by
  simpa [zLKern.prod_commlin_equivapply,
    zLKern.prod_assoclin_equivapply,
    zLKern.prodassoc_linequiv_symmapply] using
    zLKern.maplin_prodcomm_assohexaleft (p := p) (G := G) H K n x

/-- Packaged linear hexagon coherence for moving a binary product past a right factor
on Zassenhaus layer kernels (prime case). -/
theorem zLKern.prodcomm_linequiv_assohexarigh [Fact p.Prime]
    (H K : Type*) [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p ((G × H) × K) n)) :
    zLKern.prod_comm_linequiv p (G × H) K n x =
      zLKern.prod_assoc_linequiv p K G H n
        (zLKern.mapLinear p ((G × K) × H)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
            (MonoidHom.id H)) n
          ((zLKern.prod_assoc_linequiv p G K H n).symm
            (zLKern.mapLinear p (G × (H × K))
              (MonoidHom.prodMap (MonoidHom.id G)
                (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n
              (zLKern.prod_assoc_linequiv p G H K n x)))) := by
  simpa [zLKern.prod_commlin_equivapply,
    zLKern.prod_assoclin_equivapply,
    zLKern.prodassoc_linequiv_symmapply] using
    zLKern.maplin_prodcomm_assohexarigh (p := p) (G := G) H K n x


/-- Coordinate swaps are natural for maps of Zassenhaus quotients. -/
@[simp] theorem zQuot.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zQuot p (G₁ × H₁) n) :
    zQuot.prodCommEquiv p G₂ H₂ n
        (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      zQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n
        (zQuot.prodCommEquiv p G₁ H₁ n x) := by
  change (((zQuot.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
      (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n)) x =
    ((zQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
      ((zQuot.prodCommEquiv p G₁ H₁ n).toMonoidHom)) x
  rw [zQuot.prod_commequiv_monoidhom,
    zQuot.prod_commequiv_monoidhom]
  rw [← zQuot.map_comp (p := p) (G := G₁ × H₁) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← zQuot.map_comp (p := p) (G := G₁ × H₁)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl


/-- Coordinate swaps are natural for maps of consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zSubgro p (G₁ × H₁) n ⧸
      zNTerm p (G₁ × H₁) n) :
    zNQuot.prodCommEquiv p G₂ H₂ n
        (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n
        (zNQuot.prodCommEquiv p G₁ H₁ n x) := by
  change (((zNQuot.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
      (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n)) x =
    ((zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
      ((zNQuot.prodCommEquiv p G₁ H₁ n).toMonoidHom)) x
  rw [zNQuot.prod_commequiv_monoidhom,
    zNQuot.prod_commequiv_monoidhom]
  rw [← zNQuot.map_comp (p := p) (G := G₁ × H₁) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← zNQuot.map_comp (p := p) (G := G₁ × H₁)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl

/-- Coordinate swaps are natural for maps of Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prod_commequiv_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : zLKern p (G₁ × H₁) n) :
    zLKern.prodCommEquiv p G₂ H₂ n
        (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n
        (zLKern.prodCommEquiv p G₁ H₁ n x) := by
  change (((zLKern.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
      (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n)) x =
    ((zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
      ((zLKern.prodCommEquiv p G₁ H₁ n).toMonoidHom)) x
  rw [zLKern.prod_commequiv_monoidhom,
    zLKern.prod_commequiv_monoidhom]
  rw [← zLKern.map_comp (p := p) (G := G₁ × H₁) (MonoidHom.prodMap f g)
    ((MulEquiv.prodComm : G₂ × H₂ ≃* H₂ × G₂).toMonoidHom) n]
  rw [← zLKern.map_comp (p := p) (G := G₁ × H₁)
    ((MulEquiv.prodComm : G₁ × H₁ ≃* H₁ × G₁).toMonoidHom)
    (MonoidHom.prodMap g f) n]
  rfl


/-- Reassociation is natural for maps of Zassenhaus quotients. -/
@[simp] theorem zQuot.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : zQuot p ((G₁ × H₁) × K₁) n) :
    zQuot.prodAssocEquiv p G₂ H₂ K₂ n
        (zQuot.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      zQuot.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (zQuot.prodAssocEquiv p G₁ H₁ K₁ n x) := by
  change (((zQuot.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
      (zQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((zQuot.map p (G₁ × (H₁ × K₁))
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((zQuot.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom)) x
  rw [zQuot.prod_assocequiv_monoidhom,
    zQuot.prod_assocequiv_monoidhom]
  rw [← zQuot.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← zQuot.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl


/-- Reassociation is natural for maps of consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : zSubgro p ((G₁ × H₁) × K₁) n ⧸
      zNTerm p ((G₁ × H₁) × K₁) n) :
    zNQuot.prodAssocEquiv p G₂ H₂ K₂ n
        (zNQuot.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      zNQuot.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (zNQuot.prodAssocEquiv p G₁ H₁ K₁ n x) := by
  change (((zNQuot.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
      (zNQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((zNQuot.map p (G₁ × (H₁ × K₁))
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((zNQuot.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom)) x
  rw [zNQuot.prod_assocequiv_monoidhom,
    zNQuot.prod_assocequiv_monoidhom]
  rw [← zNQuot.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← zNQuot.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl

/-- Reassociation is natural for maps of Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prod_assocequiv_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : zLKern p ((G₁ × H₁) × K₁) n) :
    zLKern.prodAssocEquiv p G₂ H₂ K₂ n
        (zLKern.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      zLKern.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (zLKern.prodAssocEquiv p G₁ H₁ K₁ n x) := by
  change (((zLKern.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
      (zLKern.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n)) x =
    ((zLKern.map p (G₁ × (H₁ × K₁))
      (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
      ((zLKern.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom)) x
  rw [zLKern.prod_assocequiv_monoidhom,
    zLKern.prod_assocequiv_monoidhom]
  rw [← zLKern.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    (MonoidHom.prodMap (MonoidHom.prodMap f g) h)
    ((MulEquiv.prodAssoc : (G₂ × H₂) × K₂ ≃* G₂ × H₂ × K₂).toMonoidHom) n]
  rw [← zLKern.map_comp (p := p) (G := (G₁ × H₁) × K₁)
    ((MulEquiv.prodAssoc : (G₁ × H₁) × K₁ ≃* G₁ × H₁ × K₁).toMonoidHom)
    (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n]
  rfl


end
end GroupAlgebra
end Towers


namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Linear coordinate swaps are natural for maps of consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodcomm_linequiv_naturalapply [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : Additive (zSubgro p (G₁ × H₁) n ⧸
      zNTerm p (G₁ × H₁) n)) :
    zNQuot.prod_comm_linequiv p G₂ H₂ n
        (zNQuot.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      zNQuot.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n
        (zNQuot.prod_comm_linequiv p G₁ H₁ n x) := by
  cases x with
  | ofMul q =>
      change Additive.ofMul
          (zNQuot.prodCommEquiv p G₂ H₂ n
            (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n q)) =
        Additive.ofMul
          (zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n
            (zNQuot.prodCommEquiv p G₁ H₁ n q))
      rw [zNQuot.prod_commequiv_naturalapply]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Linear coordinate swaps are natural for maps of Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodcomm_linequiv_naturalapply [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (x : Additive (zLKern p (G₁ × H₁) n)) :
    zLKern.prod_comm_linequiv p G₂ H₂ n
        (zLKern.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n x) =
      zLKern.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n
        (zLKern.prod_comm_linequiv p G₁ H₁ n x) := by
  cases x with
  | ofMul q =>
      change Additive.ofMul
          (zLKern.prodCommEquiv p G₂ H₂ n
            (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n q)) =
        Additive.ofMul
          (zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n
            (zLKern.prodCommEquiv p G₁ H₁ n q))
      rw [zLKern.prod_commequiv_naturalapply]

/-- Linear reassociation is natural for maps of consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodassoc_linequiv_naturalapply [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : Additive (zSubgro p ((G₁ × H₁) × K₁) n ⧸
      zNTerm p ((G₁ × H₁) × K₁) n)) :
    zNQuot.prod_assoc_linequiv p G₂ H₂ K₂ n
        (zNQuot.mapLinear p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      zNQuot.mapLinear p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (zNQuot.prod_assoc_linequiv p G₁ H₁ K₁ n x) := by
  cases x with
  | ofMul q =>
      change Additive.ofMul
          (zNQuot.prodAssocEquiv p G₂ H₂ K₂ n
            (zNQuot.map p ((G₁ × H₁) × K₁)
              (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n q)) =
        Additive.ofMul
          (zNQuot.map p (G₁ × (H₁ × K₁))
            (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
            (zNQuot.prodAssocEquiv p G₁ H₁ K₁ n q))
      rw [zNQuot.prod_assocequiv_naturalapply]

/-- Linear reassociation is natural for maps of Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodassoc_linequiv_naturalapply [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (x : Additive (zLKern p ((G₁ × H₁) × K₁) n)) :
    zLKern.prod_assoc_linequiv p G₂ H₂ K₂ n
        (zLKern.mapLinear p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n x) =
      zLKern.mapLinear p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
        (zLKern.prod_assoc_linequiv p G₁ H₁ K₁ n x) := by
  cases x with
  | ofMul q =>
      change Additive.ofMul
          (zLKern.prodAssocEquiv p G₂ H₂ K₂ n
            (zLKern.map p ((G₁ × H₁) × K₁)
              (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n q)) =
        Additive.ofMul
          (zLKern.map p (G₁ × (H₁ × K₁))
            (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n
            (zLKern.prodAssocEquiv p G₁ H₁ K₁ n q))
      rw [zLKern.prod_assocequiv_naturalapply]

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Naturality square for coordinate swaps on Zassenhaus quotients. -/
theorem zQuot.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zQuot.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
        (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (zQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
        ((zQuot.prodCommEquiv p G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prod_commequiv_naturalapply (p := p) f g n x

/-- Naturality square for coordinate swaps on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zNQuot.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
        (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
        ((zNQuot.prodCommEquiv p G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.prod_commequiv_naturalapply (p := p) f g n x

/-- Naturality square for coordinate swaps on Zassenhaus layer kernels. -/
theorem zLKern.prod_comm_equivnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zLKern.prodCommEquiv p G₂ H₂ n).toMonoidHom).comp
        (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
        ((zLKern.prodCommEquiv p G₁ H₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.prod_commequiv_naturalapply (p := p) f g n x)

/-- Naturality square for reassociation on Zassenhaus quotients. -/
theorem zQuot.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zQuot.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
        (zQuot.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (zQuot.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((zQuot.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prod_assocequiv_naturalapply (p := p) f g h n x

/-- Naturality square for reassociation on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zNQuot.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
        (zNQuot.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (zNQuot.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((zNQuot.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.prod_assocequiv_naturalapply (p := p) f g h n x

/-- Naturality square for reassociation on Zassenhaus layer kernels. -/
theorem zLKern.prod_assoc_equivnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zLKern.prodAssocEquiv p G₂ H₂ K₂ n).toMonoidHom).comp
        (zLKern.map p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (zLKern.map p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        ((zLKern.prodAssocEquiv p G₁ H₁ K₁ n).toMonoidHom) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.prod_assocequiv_naturalapply (p := p) f g h n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Naturality square for linear coordinate swaps on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_commlin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zNQuot.prod_comm_linequiv p G₂ H₂ n).toLinearMap.comp
        (zNQuot.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (zNQuot.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
        (zNQuot.prod_comm_linequiv p G₁ H₁ n).toLinearMap := by
  ext x
  exact zNQuot.prodcomm_linequiv_naturalapply (p := p) f g n x

/-- Naturality square for linear coordinate swaps on Zassenhaus layer kernels. -/
theorem zLKern.prod_commlin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    (zLKern.prod_comm_linequiv p G₂ H₂ n).toLinearMap.comp
        (zLKern.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n) =
      (zLKern.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n).comp
        (zLKern.prod_comm_linequiv p G₁ H₁ n).toLinearMap := by
  ext x
  simpa using congrArg
    (fun y => (Additive.toMul y : zLKern p (H₂ × G₂) n).1)
    (zLKern.prodcomm_linequiv_naturalapply (p := p) f g n x)

/-- Naturality square for linear reassociation on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_assoclin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    (zNQuot.prod_assoc_linequiv p G₂ H₂ K₂ n).toLinearMap.comp
        (zNQuot.mapLinear p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (zNQuot.mapLinear p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        (zNQuot.prod_assoc_linequiv p G₁ H₁ K₁ n).toLinearMap := by
  ext x
  exact zNQuot.prodassoc_linequiv_naturalapply (p := p) f g h n x

/-- Naturality square for linear reassociation on Zassenhaus layer kernels. -/
theorem zLKern.prod_assoclin_equivnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    (zLKern.prod_assoc_linequiv p G₂ H₂ K₂ n).toLinearMap.comp
        (zLKern.mapLinear p ((G₁ × H₁) × K₁)
          (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n) =
      (zLKern.mapLinear p (G₁ × (H₁ × K₁))
        (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n).comp
        (zLKern.prod_assoc_linequiv p G₁ H₁ K₁ n).toLinearMap := by
  ext x
  simpa using congrArg
    (fun y => (Additive.toMul y : zLKern p (G₂ × (H₂ × K₂)) n).1)
    (zLKern.prodassoc_linequiv_naturalapply (p := p) f g h n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse coordinate swaps are natural on Zassenhaus quotients. -/
@[simp] theorem zQuot.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : zQuot p (H₁ × G₁) n) :
    (zQuot.prodCommEquiv p G₂ H₂ n).symm
        (zQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n y) =
      zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zQuot.prodCommEquiv p G₁ H₁ n).symm y) := by
  simpa [zQuot.prod_commequiv_symmeq] using
    zQuot.prod_commequiv_naturalapply (p := p)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse coordinate swaps are natural on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : zSubgro p (H₁ × G₁) n ⧸
      zNTerm p (H₁ × G₁) n) :
    (zNQuot.prodCommEquiv p G₂ H₂ n).symm
        (zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n y) =
      zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zNQuot.prodCommEquiv p G₁ H₁ n).symm y) := by
  simpa [zNQuot.prod_commequiv_symmeq] using
    zNQuot.prod_commequiv_naturalapply (p := p)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

/-- Inverse coordinate swaps are natural on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodcomm_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : zLKern p (H₁ × G₁) n) :
    (zLKern.prodCommEquiv p G₂ H₂ n).symm
        (zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n y) =
      zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zLKern.prodCommEquiv p G₁ H₁ n).symm y) := by
  simpa [zLKern.prod_commequiv_symmeq] using
    zLKern.prod_commequiv_naturalapply (p := p)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse reassociation is natural on Zassenhaus quotients. -/
@[simp] theorem zQuot.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : zQuot p (G₁ × (H₁ × K₁)) n) :
    (zQuot.prodAssocEquiv p G₂ H₂ K₂ n).symm
        (zQuot.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      zQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((zQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm y) := by
  apply (zQuot.prodAssocEquiv p G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := zQuot.prod_assocequiv_naturalapply (p := p) f g h n
    ((zQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse reassociation is natural on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : zSubgro p (G₁ × (H₁ × K₁)) n ⧸
      zNTerm p (G₁ × (H₁ × K₁)) n) :
    (zNQuot.prodAssocEquiv p G₂ H₂ K₂ n).symm
        (zNQuot.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      zNQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((zNQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm y) := by
  apply (zNQuot.prodAssocEquiv p G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := zNQuot.prod_assocequiv_naturalapply (p := p) f g h n
    ((zNQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

/-- Inverse reassociation is natural on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodassoc_equivsymm_naturalapply
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : zLKern p (G₁ × (H₁ × K₁)) n) :
    (zLKern.prodAssocEquiv p G₂ H₂ K₂ n).symm
        (zLKern.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      zLKern.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((zLKern.prodAssocEquiv p G₁ H₁ K₁ n).symm y) := by
  apply (zLKern.prodAssocEquiv p G₂ H₂ K₂ n).injective
  rw [MulEquiv.apply_symm_apply]
  have hnat := zLKern.prod_assocequiv_naturalapply (p := p) f g h n
    ((zLKern.prodAssocEquiv p G₁ H₁ K₁ n).symm y)
  rw [MulEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse linear coordinate swaps are natural on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodcomm_linequiv_symmnatuappl
    [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : Additive (zSubgro p (H₁ × G₁) n ⧸
      zNTerm p (H₁ × G₁) n)) :
    (zNQuot.prod_comm_linequiv p G₂ H₂ n).symm
        (zNQuot.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n y) =
      zNQuot.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zNQuot.prod_comm_linequiv p G₁ H₁ n).symm y) := by
  simpa [zNQuot.prodcomm_linequiv_symmeq] using
    zNQuot.prodcomm_linequiv_naturalapply (p := p)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

/-- Inverse linear coordinate swaps are natural on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodcomm_linequiv_symmnatuappl
    [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ)
    (y : Additive (zLKern p (H₁ × G₁) n)) :
    (zLKern.prod_comm_linequiv p G₂ H₂ n).symm
        (zLKern.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n y) =
      zLKern.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n
        ((zLKern.prod_comm_linequiv p G₁ H₁ n).symm y) := by
  simpa [zLKern.prodcomm_linequiv_symmeq] using
    zLKern.prodcomm_linequiv_naturalapply (p := p)
      (G₁ := H₁) (G₂ := H₂) (H₁ := G₁) (H₂ := G₂) g f n y

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Inverse linear reassociation is natural on consecutive Zassenhaus quotients. -/
@[simp] theorem zNQuot.prodassoc_linequiv_symmnatuappl
    [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : Additive (zSubgro p (G₁ × (H₁ × K₁)) n ⧸
      zNTerm p (G₁ × (H₁ × K₁)) n)) :
    (zNQuot.prod_assoc_linequiv p G₂ H₂ K₂ n).symm
        (zNQuot.mapLinear p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      zNQuot.mapLinear p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((zNQuot.prod_assoc_linequiv p G₁ H₁ K₁ n).symm y) := by
  apply (zNQuot.prod_assoc_linequiv p G₂ H₂ K₂ n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hnat := zNQuot.prodassoc_linequiv_naturalapply (p := p) f g h n
    ((zNQuot.prod_assoc_linequiv p G₁ H₁ K₁ n).symm y)
  rw [LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm

/-- Inverse linear reassociation is natural on Zassenhaus layer kernels. -/
@[simp] theorem zLKern.prodassoc_linequiv_symmnatuappl
    [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ)
    (y : Additive (zLKern p (G₁ × (H₁ × K₁)) n)) :
    (zLKern.prod_assoc_linequiv p G₂ H₂ K₂ n).symm
        (zLKern.mapLinear p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n y) =
      zLKern.mapLinear p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n
        ((zLKern.prod_assoc_linequiv p G₁ H₁ K₁ n).symm y) := by
  apply (zLKern.prod_assoc_linequiv p G₂ H₂ K₂ n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hnat := zLKern.prodassoc_linequiv_naturalapply (p := p) f g h n
    ((zLKern.prod_assoc_linequiv p G₁ H₁ K₁ n).symm y)
  rw [LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Naturality square for inverse coordinate swaps on Zassenhaus quotients. -/
theorem zQuot.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zQuot.prodCommEquiv p G₂ H₂ n).symm.toMonoidHom).comp
        (zQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n) =
      (zQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n).comp
        ((zQuot.prodCommEquiv p G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    zQuot.prodcomm_equivsymm_naturalapply (p := p) f g n y

/-- Naturality square for inverse coordinate swaps on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zNQuot.prodCommEquiv p G₂ H₂ n).symm.toMonoidHom).comp
        (zNQuot.map p (H₁ × G₁) (MonoidHom.prodMap g f) n) =
      (zNQuot.map p (G₁ × H₁) (MonoidHom.prodMap f g) n).comp
        ((zNQuot.prodCommEquiv p G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    zNQuot.prodcomm_equivsymm_naturalapply (p := p) f g n y

/-- Naturality square for inverse coordinate swaps on Zassenhaus layer kernels. -/
theorem zLKern.prod_commequiv_symmnatural
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zLKern.prodCommEquiv p G₂ H₂ n).symm.toMonoidHom).comp
        (zLKern.map p (H₁ × G₁) (MonoidHom.prodMap g f) n) =
      (zLKern.map p (G₁ × H₁) (MonoidHom.prodMap f g) n).comp
        ((zLKern.prodCommEquiv p G₁ H₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (zLKern.prodcomm_equivsymm_naturalapply (p := p) f g n y)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Naturality square for inverse reassociation on Zassenhaus quotients. -/
theorem zQuot.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zQuot.prodAssocEquiv p G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (zQuot.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (zQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((zQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    zQuot.prodassoc_equivsymm_naturalapply (p := p) f g h n y

/-- Naturality square for inverse reassociation on consecutive Zassenhaus quotients. -/
theorem zNQuot.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zNQuot.prodAssocEquiv p G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (zNQuot.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (zNQuot.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((zNQuot.prodAssocEquiv p G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using
    zNQuot.prodassoc_equivsymm_naturalapply (p := p) f g h n y

/-- Naturality square for inverse reassociation on Zassenhaus layer kernels. -/
theorem zLKern.prod_assocequiv_symmnatural
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zLKern.prodAssocEquiv p G₂ H₂ K₂ n).symm.toMonoidHom).comp
        (zLKern.map p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (zLKern.map p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((zLKern.prodAssocEquiv p G₁ H₁ K₁ n).symm.toMonoidHom) := by
  ext y
  simpa [MonoidHom.comp_apply] using congrArg Subtype.val
    (zLKern.prodassoc_equivsymm_naturalapply (p := p) f g h n y)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Naturality square for inverse linear coordinate swaps on consecutive Zassenhaus quotients. -/
theorem zNQuot.prodcomm_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zNQuot.prod_comm_linequiv p G₂ H₂ n).symm.toLinearMap).comp
        (zNQuot.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n) =
      (zNQuot.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n).comp
        ((zNQuot.prod_comm_linequiv p G₁ H₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg Additive.toMul
    (zNQuot.prodcomm_linequiv_symmnatuappl (p := p) f g n y)

/-- Naturality square for inverse linear coordinate swaps on Zassenhaus layer kernels. -/
theorem zLKern.prodcomm_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (n : ℕ) :
    ((zLKern.prod_comm_linequiv p G₂ H₂ n).symm.toLinearMap).comp
        (zLKern.mapLinear p (H₁ × G₁) (MonoidHom.prodMap g f) n) =
      (zLKern.mapLinear p (G₁ × H₁) (MonoidHom.prodMap f g) n).comp
        ((zLKern.prod_comm_linequiv p G₁ H₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg
    (fun z => (Additive.toMul z : zLKern p (G₂ × H₂) n).1)
    (zLKern.prodcomm_linequiv_symmnatuappl (p := p) f g n y)

/-- Naturality square for inverse linear reassociation on consecutive Zassenhaus quotients. -/
theorem zNQuot.prodassoc_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zNQuot.prod_assoc_linequiv p G₂ H₂ K₂ n).symm.toLinearMap).comp
        (zNQuot.mapLinear p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (zNQuot.mapLinear p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((zNQuot.prod_assoc_linequiv p G₁ H₁ K₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg Additive.toMul
    (zNQuot.prodassoc_linequiv_symmnatuappl (p := p) f g h n y)

/-- Naturality square for inverse linear reassociation on Zassenhaus layer kernels. -/
theorem zLKern.prodassoc_linequiv_symmnatural [Fact p.Prime]
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type*}
    [Group G₁] [Group G₂] [Group H₁] [Group H₂] [Group K₁] [Group K₂]
    (f : G₁ →* G₂) (g : H₁ →* H₂) (h : K₁ →* K₂) (n : ℕ) :
    ((zLKern.prod_assoc_linequiv p G₂ H₂ K₂ n).symm.toLinearMap).comp
        (zLKern.mapLinear p (G₁ × (H₁ × K₁))
          (MonoidHom.prodMap f (MonoidHom.prodMap g h)) n) =
      (zLKern.mapLinear p ((G₁ × H₁) × K₁)
        (MonoidHom.prodMap (MonoidHom.prodMap f g) h) n).comp
        ((zLKern.prod_assoc_linequiv p G₁ H₁ K₁ n).symm.toLinearMap) := by
  ext y
  simpa using congrArg
    (fun z => (Additive.toMul z : zLKern p ((G₂ × H₂) × K₂) n).1)
    (zLKern.prodassoc_linequiv_symmnatuappl (p := p) f g h n y)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Reverse pentagon coherence for ordinary Zassenhaus-quotient associator maps. -/
theorem zQuot.map_prodassoc_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zQuot p (G × (H × (K × L))) n) :
    zQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (zQuot.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    zQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (zQuot.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (zQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Reverse pentagon coherence for consecutive Zassenhaus-quotient associator maps. -/
theorem zNQuot.map_prodassoc_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zSubgro p (G × (H × (K × L))) n ⧸
      zNTerm p (G × (H × (K × L))) n) :
    zNQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (zNQuot.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    zNQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (zNQuot.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (zNQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨a, bcd⟩
  rcases bcd with ⟨b, cd⟩
  rcases cd with ⟨c, d⟩
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Packaged reverse pentagon coherence for ordinary Zassenhaus-quotient associators. -/
theorem zQuot.prod_assocequiv_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zQuot p (G × (H × (K × L))) n) :
    (zQuot.prodAssocEquiv p (G × H) K L n).symm
      ((zQuot.prodAssocEquiv p G H (K × L) n).symm x) =
    zQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((zQuot.prodAssocEquiv p G (H × K) L n).symm
        (zQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [zQuot.prod_assocequiv_symmapply] using
    zQuot.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x

/-- Packaged reverse pentagon coherence for consecutive Zassenhaus-quotient associators. -/
theorem zNQuot.prod_assocequiv_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zSubgro p (G × (H × (K × L))) n ⧸
      zNTerm p (G × (H × (K × L))) n) :
    (zNQuot.prodAssocEquiv p (G × H) K L n).symm
      ((zNQuot.prodAssocEquiv p G H (K × L) n).symm x) =
    zNQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((zNQuot.prodAssocEquiv p G (H × K) L n).symm
        (zNQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [zNQuot.prod_assocequiv_symmapply] using
    zNQuot.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Reverse pentagon coherence for Zassenhaus layer-kernel associator maps. -/
theorem zLKern.map_prodassoc_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zLKern p (G × (H × (K × L))) n) :
    zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (zLKern.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    zLKern.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (zLKern.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (zLKern.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  change (((zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
    (zLKern.map p (G × (H × (K × L)))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n)) x) = _
  rw [← zLKern.map_comp (p := p) (G := G × (H × (K × L)))
    (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom
    (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n]
  change (zLKern.map p (G × (H × (K × L))) _ n x) =
    (((zLKern.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zLKern.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zLKern.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)))) x
  rw [← zLKern.map_comp (p := p) (G := G × (H × (K × L)))
    (MonoidHom.prodMap (MonoidHom.id G)
      (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom)
    (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n]
  rw [← zLKern.map_comp (p := p) (G := G × (H × (K × L)))
    ((MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom.comp
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom))
    (MonoidHom.prodMap
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
      (MonoidHom.id L)) n]
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Packaged reverse pentagon coherence for Zassenhaus layer-kernel associators. -/
theorem zLKern.prod_assocequiv_symmpentagon
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : zLKern p (G × (H × (K × L))) n) :
    (zLKern.prodAssocEquiv p (G × H) K L n).symm
      ((zLKern.prodAssocEquiv p G H (K × L) n).symm x) =
    zLKern.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((zLKern.prodAssocEquiv p G (H × K) L n).symm
        (zLKern.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [zLKern.prod_assocequiv_symmapply] using
    zLKern.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

/-- Reverse linear pentagon coherence for consecutive Zassenhaus quotients (prime case). -/
theorem zNQuot.maplin_prodassoc_symmpentagon [Fact p.Prime]
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zSubgro p (G × (H × (K × L))) n ⧸
      zNTerm p (G × (H × (K × L))) n)) :
    zNQuot.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (zNQuot.mapLinear p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    zNQuot.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (zNQuot.mapLinear p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (zNQuot.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x'

/-- Reverse linear pentagon coherence for Zassenhaus layer kernels (prime case). -/
theorem zLKern.maplin_prodassoc_symmpentagon [Fact p.Prime]
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zLKern p (G × (H × (K × L))) n)) :
    zLKern.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n
      (zLKern.mapLinear p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n x) =
    zLKern.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      (zLKern.mapLinear p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n
        (zLKern.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x'

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

set_option maxHeartbeats 400000 in
-- Elaborating the nested packaged linear associators requires more reduction than the default.
/-- Reverse pentagon coherence for packaged linear consecutive Zassenhaus associators. -/
theorem zNQuot.prodassoc_linequiv_symmpentagon [Fact p.Prime]
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zSubgro p (G × (H × (K × L))) n ⧸
      zNTerm p (G × (H × (K × L))) n)) :
    (zNQuot.prod_assoc_linequiv p (G × H) K L n).symm
      ((zNQuot.prod_assoc_linequiv p G H (K × L) n).symm x) =
    zNQuot.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((zNQuot.prod_assoc_linequiv p G (H × K) L n).symm
        (zNQuot.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [zNQuot.prodassoc_linequiv_symmapply] using
    zNQuot.maplin_prodassoc_symmpentagon (p := p) (G := G) H K L n x

/-- Reverse pentagon coherence for packaged linear Zassenhaus layer-kernel associators. -/
theorem zLKern.prodassoc_linequiv_symmpentagon [Fact p.Prime]
    (H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ)
    (x : Additive (zLKern p (G × (H × (K × L))) n)) :
    (zLKern.prod_assoc_linequiv p (G × H) K L n).symm
      ((zLKern.prod_assoc_linequiv p G H (K × L) n).symm x) =
    zLKern.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n
      ((zLKern.prod_assoc_linequiv p G (H × K) L n).symm
        (zLKern.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n x)) := by
  simpa [zLKern.prodassoc_linequiv_symmapply] using
    zLKern.maplin_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level reverse linear pentagon for consecutive Zassenhaus associators. -/
theorem zNQuot.prodas_lineq_pentb
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    ((zNQuot.prod_assoc_linequiv p (G × H) K L n).symm.toLinearMap).comp
      ((zNQuot.prod_assoc_linequiv p G H (K × L) n).symm.toLinearMap) =
    (zNQuot.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((zNQuot.prod_assoc_linequiv p G (H × K) L n).symm.toLinearMap).comp
        (zNQuot.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodassoc_linequiv_symmpentagon (p := p) (G := G) H K L n x

/-- Hom-level reverse linear pentagon for Zassenhaus layer associators. -/
theorem zLKern.prodas_lineq_pentb
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    ((zLKern.prod_assoc_linequiv p (G × H) K L n).symm.toLinearMap).comp
      ((zLKern.prod_assoc_linequiv p G H (K × L) n).symm.toLinearMap) =
    (zLKern.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((zLKern.prod_assoc_linequiv p G (H × K) L n).symm.toLinearMap).comp
        (zLKern.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodassoc_linequiv_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level linear pentagon for consecutive Zassenhaus associators. -/
theorem zNQuot.prodas_lineq_penta
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.prod_assoc_linequiv p G H (K × L) n).toLinearMap.comp
      (zNQuot.prod_assoc_linequiv p (G × H) K L n).toLinearMap =
    (zNQuot.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zNQuot.prod_assoc_linequiv p G (H × K) L n).toLinearMap.comp
        (zNQuot.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prod_assoclin_equivpentagon (p := p) (G := G) H K L n x

/-- Hom-level linear pentagon for Zassenhaus layer associators. -/
theorem zLKern.prodas_lineq_penta
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.prod_assoc_linequiv p G H (K × L) n).toLinearMap.comp
      (zLKern.prod_assoc_linequiv p (G × H) K L n).toLinearMap =
    (zLKern.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zLKern.prod_assoc_linequiv p G (H × K) L n).toLinearMap.comp
        (zLKern.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prod_assoclin_equivpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level raw-map linear pentagon for consecutive Zassenhaus quotients. -/
theorem zNQuot.maplin_prodassoc_pentagonlinmap
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (zNQuot.mapLinear p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (zNQuot.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zNQuot.mapLinear p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zNQuot.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.map_linprod_assocpentagon (p := p) (G := G) H K L n x

/-- Hom-level raw-map linear pentagon for Zassenhaus layer kernels. -/
theorem zLKern.maplin_prodassoc_pentagonlinmap
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (zLKern.mapLinear p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (zLKern.mapLinear p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zLKern.mapLinear p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zLKern.mapLinear p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.map_linprod_assocpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level raw-map reverse linear pentagon for consecutive Zassenhaus quotients. -/
theorem zNQuot.maplin_proda_penta
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (zNQuot.mapLinear p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (zNQuot.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zNQuot.mapLinear p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zNQuot.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.maplin_prodassoc_symmpentagon (p := p) (G := G) H K L n x

/-- Hom-level raw-map reverse linear pentagon for Zassenhaus layer kernels. -/
theorem zLKern.maplin_proda_penta
    [Fact p.Prime] (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.mapLinear p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (zLKern.mapLinear p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (zLKern.mapLinear p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zLKern.mapLinear p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zLKern.mapLinear p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.maplin_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level pentagon for ordinary Zassenhaus quotient associator maps. -/
theorem zQuot.map_prodassoc_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (zQuot.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (zQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zQuot.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.map_prod_assocpentagon (p := p) (G := G) H K L n x

/-- Hom-level reverse pentagon for ordinary Zassenhaus quotient associator maps. -/
theorem zQuot.mapprod_assocsymm_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (zQuot.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (zQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zQuot.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level pentagon for consecutive Zassenhaus quotient associator maps. -/
theorem zNQuot.map_prodassoc_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (zNQuot.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (zNQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zNQuot.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zNQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.map_prod_assocpentagon (p := p) (G := G) H K L n x

/-- Hom-level reverse pentagon for consecutive Zassenhaus quotient associator maps. -/
theorem zNQuot.mapprod_assocsymm_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (zNQuot.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (zNQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zNQuot.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zNQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level pentagon for Zassenhaus layer-kernel associator maps. -/
theorem zLKern.map_prodassoc_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).toMonoidHom n).comp
      (zLKern.map p (((G × H) × K) × L)
        (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).toMonoidHom n) =
    (zLKern.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zLKern.map p ((G × (H × K)) × L)
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).toMonoidHom n).comp
        (zLKern.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val (zLKern.map_prod_assocpentagon (p := p) (G := G) H K L n x)

/-- Hom-level reverse pentagon for Zassenhaus layer-kernel associator maps. -/
theorem zLKern.mapprod_assocsymm_pentagonhom
    (H K L : Type*) [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.map p ((G × H) × (K × L))
      (MulEquiv.prodAssoc (M := G × H) (N := K) (P := L)).symm.toMonoidHom n).comp
      (zLKern.map p (G × (H × (K × L)))
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K × L)).symm.toMonoidHom n) =
    (zLKern.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      ((zLKern.map p (G × ((H × K) × L))
        (MulEquiv.prodAssoc (M := G) (N := H × K) (P := L)).symm.toMonoidHom n).comp
        (zLKern.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.map_prodassoc_symmpentagon (p := p) (G := G) H K L n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level hexagon for moving a left factor past a binary product on Zassenhaus quotients. -/
theorem zQuot.mapprod_commassoc_hexagonlefthom
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zQuot.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (zQuot.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((zQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zQuot.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((zQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (zQuot.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x

/-- Hom-level hexagon for moving a binary product past a right factor on Zassenhaus quotients. -/
theorem zQuot.mappro_comma_hexag
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zQuot.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (zQuot.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((zQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((zQuot.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((zQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zQuot.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level hexagon for moving a left factor past a binary product
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mapprod_commassoc_hexagonlefthom
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zNQuot.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (zNQuot.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((zNQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zNQuot.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((zNQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (zNQuot.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x

/-- Hom-level hexagon for moving a binary product past a right factor
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mappro_comma_hexag
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zNQuot.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (zNQuot.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((zNQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((zNQuot.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((zNQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zNQuot.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x

/-- Hom-level hexagon for moving a left factor past a binary product on Zassenhaus layer kernels. -/
theorem zLKern.mapprod_commassoc_hexagonlefthom
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zLKern.map p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (zLKern.map p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((zLKern.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zLKern.map p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((zLKern.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (zLKern.map p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.mapprod_commassoc_hexagonleft (p := p) (G := G) H K n x)

/-- Hom-level hexagon for moving a binary product past a right factor
on Zassenhaus layer kernels. -/
theorem zLKern.mappro_comma_hexag
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zLKern.map p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (zLKern.map p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((zLKern.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((zLKern.map p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((zLKern.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zLKern.map p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.mapprod_commassoc_hexagonright (p := p) (G := G) H K n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level packaged linear hexagon (left orientation) for consecutive Zassenhaus quotients. -/
theorem zNQuot.prodco_equia_leftl
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p G (H × K) n).toLinearMap =
    ((zNQuot.prod_assoc_linequiv p H K G n).symm.toLinearMap).comp
      ((zNQuot.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zNQuot.prod_assoc_linequiv p H G K n).toLinearMap.comp
          ((zNQuot.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((zNQuot.prod_assoc_linequiv p G H K n).symm.toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodcomm_linequiv_assohexaleft (p := p) (G := G) H K n x

/-- Hom-level packaged linear hexagon (right orientation) for consecutive Zassenhaus quotients. -/
theorem zNQuot.prodco_equia_righa
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p (G × H) K n).toLinearMap =
    (zNQuot.prod_assoc_linequiv p K G H n).toLinearMap.comp
      ((zNQuot.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((zNQuot.prod_assoc_linequiv p G K H n).symm.toLinearMap).comp
          ((zNQuot.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zNQuot.prod_assoc_linequiv p G H K n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodcomm_linequiv_assohexarigh (p := p) (G := G) H K n x

/-- Hom-level packaged linear hexagon (left orientation) for Zassenhaus layer kernels. -/
theorem zLKern.prodco_equia_leftl
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    (zLKern.prod_comm_linequiv p G (H × K) n).toLinearMap =
    ((zLKern.prod_assoc_linequiv p H K G n).symm.toLinearMap).comp
      ((zLKern.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zLKern.prod_assoc_linequiv p H G K n).toLinearMap.comp
          ((zLKern.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((zLKern.prod_assoc_linequiv p G H K n).symm.toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodcomm_linequiv_assohexaleft (p := p) (G := G) H K n x

/-- Hom-level packaged linear hexagon (right orientation) for Zassenhaus layer kernels. -/
theorem zLKern.prodco_equia_righa
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    (zLKern.prod_comm_linequiv p (G × H) K n).toLinearMap =
    (zLKern.prod_assoc_linequiv p K G H n).toLinearMap.comp
      ((zLKern.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((zLKern.prod_assoc_linequiv p G K H n).symm.toLinearMap).comp
          ((zLKern.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zLKern.prod_assoc_linequiv p G H K n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodcomm_linequiv_assohexarigh (p := p) (G := G) H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ} {G : Type*} [Group G]

/-- Hom-level raw linear hexagon (left orientation) for consecutive Zassenhaus quotient maps. -/
theorem zNQuot.maplin_comma_leftl
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zNQuot.mapLinear p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (zNQuot.mapLinear p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((zNQuot.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zNQuot.mapLinear p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((zNQuot.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (zNQuot.mapLinear p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.maplin_prodcomm_assohexaleft (p := p) (G := G) H K n x

/-- Hom-level raw linear hexagon (right orientation) for consecutive Zassenhaus quotient maps. -/
theorem zNQuot.maplin_comma_right
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zNQuot.mapLinear p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (zNQuot.mapLinear p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((zNQuot.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((zNQuot.mapLinear p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((zNQuot.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zNQuot.mapLinear p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.maplin_prodcomm_assohexarigh (p := p) (G := G) H K n x

/-- Hom-level raw linear hexagon (left orientation) for Zassenhaus layer-kernel maps. -/
theorem zLKern.maplin_comma_leftl
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zLKern.mapLinear p (G × (H × K))
      (MulEquiv.prodComm (M := G) (N := H × K)).toMonoidHom n =
    (zLKern.mapLinear p (H × (K × G))
      (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).symm.toMonoidHom n).comp
      ((zLKern.mapLinear p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zLKern.mapLinear p ((H × G) × K)
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).toMonoidHom n).comp
          ((zLKern.mapLinear p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            (zLKern.mapLinear p (G × (H × K))
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.maplin_prodcomm_assohexaleft (p := p) (G := G) H K n x

/-- Hom-level raw linear hexagon (right orientation) for Zassenhaus layer-kernel maps. -/
theorem zLKern.maplin_comma_right
    [Fact p.Prime] (H K : Type*) [Group H] [Group K] (n : ℕ) :
    zLKern.mapLinear p ((G × H) × K)
      (MulEquiv.prodComm (M := G × H) (N := K)).toMonoidHom n =
    (zLKern.mapLinear p ((K × G) × H)
      (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).toMonoidHom n).comp
      ((zLKern.mapLinear p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        ((zLKern.mapLinear p (G × (K × H))
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).symm.toMonoidHom n).comp
          ((zLKern.mapLinear p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zLKern.mapLinear p ((G × H) × K)
              (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.maplin_prodcomm_assohexarigh (p := p) (G := G) H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on Zassenhaus quotients. -/
theorem zQuot.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((H × K) × G) n) :
    zQuot.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    zQuot.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (zQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (zQuot.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (zQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (zQuot.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨hk, g⟩
  rcases hk with ⟨h, k⟩
  rfl

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on Zassenhaus quotients. -/
theorem zQuot.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zQuot p (K × (G × H)) n) :
    zQuot.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    zQuot.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (zQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (zQuot.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (zQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (zQuot.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨k, gh⟩
  rcases gh with ⟨g, h⟩
  rfl

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((H × K) × G) n ⧸
      zNTerm p ((H × K) × G) n) :
    zNQuot.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    zNQuot.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (zNQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (zNQuot.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (zNQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (zNQuot.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨hk, g⟩
  rcases hk with ⟨h, k⟩
  rfl

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on consecutive Zassenhaus quotients. -/
theorem zNQuot.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zSubgro p (K × (G × H)) n ⧸
      zNTerm p (K × (G × H)) n) :
    zNQuot.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    zNQuot.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (zNQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (zNQuot.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (zNQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (zNQuot.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  refine QuotientGroup.induction_on x ?_
  intro a
  rcases a with ⟨v, hv⟩
  rcases v with ⟨k, gh⟩
  rcases gh with ⟨g, h⟩
  rfl

/-- Reverse hexagon coherence for moving a binary product back past a left factor
on Zassenhaus layer kernels. -/
theorem zLKern.mappro_comma_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((H × K) × G) n) :
    zLKern.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    zLKern.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (zLKern.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (zLKern.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (zLKern.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (zLKern.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [zLKern.map_coe]
  exact zQuot.mappro_comma_symmh (p := p) G H K (n + 1)
    (x : zQuot p ((H × K) × G) (n + 1))

/-- Reverse hexagon coherence for moving a right factor back past a binary product
on Zassenhaus layer kernels. -/
theorem zLKern.mapprod_commassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zLKern p (K × (G × H)) n) :
    zLKern.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    zLKern.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (zLKern.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (zLKern.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (zLKern.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (zLKern.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  apply Subtype.ext
  simp only [zLKern.map_coe]
  exact zQuot.mapprod_commassoc_symmhexarigh (p := p) G H K (n + 1)
    (x : zQuot p (K × (G × H)) (n + 1))

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level reverse hexagon for Zassenhaus quotient maps (left orientation). -/
theorem zQuot.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zQuot.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (zQuot.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((zQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((zQuot.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((zQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zQuot.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.mappro_comma_symmh (p := p) G H K n x

/-- Hom-level reverse hexagon for Zassenhaus quotient maps (right orientation). -/
theorem zQuot.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zQuot.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (zQuot.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((zQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zQuot.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((zQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (zQuot.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.mapprod_commassoc_symmhexarigh (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level reverse hexagon for consecutive Zassenhaus quotient maps (left orientation). -/
theorem zNQuot.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zNQuot.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (zNQuot.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((zNQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((zNQuot.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((zNQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zNQuot.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.mappro_comma_symmh (p := p) G H K n x

/-- Hom-level reverse hexagon for consecutive Zassenhaus quotient maps (right orientation). -/
theorem zNQuot.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zNQuot.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (zNQuot.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((zNQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zNQuot.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((zNQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (zNQuot.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.mapprod_commassoc_symmhexarigh (p := p) G H K n x

/-- Hom-level reverse hexagon for Zassenhaus layer-kernel maps (left orientation). -/
theorem zLKern.mappro_comma_hexaa
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zLKern.map p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (zLKern.map p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((zLKern.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((zLKern.map p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((zLKern.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zLKern.map p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.mappro_comma_symmh (p := p) G H K n x)

/-- Hom-level reverse hexagon for Zassenhaus layer-kernel maps (right orientation). -/
theorem zLKern.mappro_comma_hexab
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zLKern.map p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (zLKern.map p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((zLKern.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zLKern.map p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((zLKern.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (zLKern.map p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.mapprod_commassoc_symmhexarigh (p := p) G H K n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Linear reverse hexagon coherence for consecutive Zassenhaus quotients (left orientation). -/
theorem zNQuot.maplin_prodc_symmh
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p ((H × K) × G) n ⧸
      zNTerm p ((H × K) × G) n)) :
    zNQuot.mapLinear p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    zNQuot.mapLinear p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (zNQuot.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (zNQuot.mapLinear p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (zNQuot.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (zNQuot.mapLinear p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.mappro_comma_symmh (p := p) G H K n x'

/-- Linear reverse hexagon coherence for consecutive Zassenhaus quotients (right orientation). -/
theorem zNQuot.maplin_prodc_symma
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p (K × (G × H)) n ⧸
      zNTerm p (K × (G × H)) n)) :
    zNQuot.mapLinear p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    zNQuot.mapLinear p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (zNQuot.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (zNQuot.mapLinear p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (zNQuot.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (zNQuot.mapLinear p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zNQuot.mapprod_commassoc_symmhexarigh (p := p) G H K n x'

/-- Linear reverse hexagon coherence for Zassenhaus layer kernels (left orientation). -/
theorem zLKern.maplin_prodc_symmh
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p ((H × K) × G) n)) :
    zLKern.mapLinear p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n x =
    zLKern.mapLinear p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n
      (zLKern.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n
        (zLKern.mapLinear p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n
          (zLKern.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
            (zLKern.mapLinear p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.mappro_comma_symmh (p := p) G H K n x'

/-- Linear reverse hexagon coherence for Zassenhaus layer kernels (right orientation). -/
theorem zLKern.maplin_prodc_symma
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p (K × (G × H)) n)) :
    zLKern.mapLinear p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n x =
    zLKern.mapLinear p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n
      (zLKern.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
        (zLKern.mapLinear p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n
          (zLKern.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n
            (zLKern.mapLinear p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n x)))) := by
  cases x with | ofMul x' =>
    apply congrArg Additive.ofMul
    exact zLKern.mapprod_commassoc_symmhexarigh (p := p) G H K n x'

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level raw linear reverse hexagon for consecutive Zassenhaus quotient maps (left). -/
theorem zNQuot.maplin_comma_hexle
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zNQuot.mapLinear p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (zNQuot.mapLinear p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((zNQuot.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((zNQuot.mapLinear p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((zNQuot.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zNQuot.mapLinear p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.maplin_prodc_symmh (p := p) G H K n x

/-- Hom-level raw linear reverse hexagon for consecutive Zassenhaus quotient maps (right). -/
theorem zNQuot.maplin_comma_hexri
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zNQuot.mapLinear p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (zNQuot.mapLinear p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((zNQuot.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zNQuot.mapLinear p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((zNQuot.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (zNQuot.mapLinear p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.maplin_prodc_symma (p := p) G H K n x

/-- Hom-level raw linear reverse hexagon for Zassenhaus layer-kernel maps (left). -/
theorem zLKern.maplin_comma_hexle
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zLKern.mapLinear p ((H × K) × G)
      (MulEquiv.prodComm (M := H × K) (N := G)).toMonoidHom n =
    (zLKern.mapLinear p ((G × H) × K)
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom n).comp
      ((zLKern.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        ((zLKern.mapLinear p (H × (G × K))
          (MulEquiv.prodAssoc (M := H) (N := G) (P := K)).symm.toMonoidHom n).comp
          ((zLKern.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zLKern.mapLinear p ((H × K) × G)
              (MulEquiv.prodAssoc (M := H) (N := K) (P := G)).toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.maplin_prodc_symmh (p := p) G H K n x

/-- Hom-level raw linear reverse hexagon for Zassenhaus layer-kernel maps (right). -/
theorem zLKern.maplin_comma_hexri
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    zLKern.mapLinear p (K × (G × H))
      (MulEquiv.prodComm (M := K) (N := G × H)).toMonoidHom n =
    (zLKern.mapLinear p (G × (H × K))
      (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom n).comp
      ((zLKern.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zLKern.mapLinear p ((G × K) × H)
          (MulEquiv.prodAssoc (M := G) (N := K) (P := H)).toMonoidHom n).comp
          ((zLKern.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            (zLKern.mapLinear p (K × (G × H))
              (MulEquiv.prodAssoc (M := K) (N := G) (P := H)).symm.toMonoidHom n)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.maplin_prodc_symma (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Packaged prime-field linear reverse hexagon for consecutive Zassenhaus quotients (left). -/
theorem zNQuot.prodco_lineq_symmh
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p ((H × K) × G) n ⧸
      zNTerm p ((H × K) × G) n)) :
    zNQuot.prod_comm_linequiv p (H × K) G n x =
      zNQuot.prod_assoc_linequiv p G H K n
        (zNQuot.mapLinear p ((H × G) × K)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((zNQuot.prod_assoc_linequiv p H G K n).symm
            (zNQuot.mapLinear p (H × (K × G))
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (zNQuot.prod_assoc_linequiv p H K G n x)))) := by
  simpa [zNQuot.prod_commlin_equivapply,
    zNQuot.prod_assoclin_equivapply,
    zNQuot.prodassoc_linequiv_symmapply] using
    zNQuot.maplin_prodc_symmh (p := p) G H K n x

/-- Packaged prime-field linear reverse hexagon for consecutive Zassenhaus quotients (right). -/
theorem zNQuot.prodco_lineq_symma
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zSubgro p (K × (G × H)) n ⧸
      zNTerm p (K × (G × H)) n)) :
    zNQuot.prod_comm_linequiv p K (G × H) n x =
      (zNQuot.prod_assoc_linequiv p G H K n).symm
        (zNQuot.mapLinear p (G × (K × H))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (zNQuot.prod_assoc_linequiv p G K H n
            (zNQuot.mapLinear p ((K × G) × H)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((zNQuot.prod_assoc_linequiv p K G H n).symm x)))) := by
  simpa [zNQuot.prod_commlin_equivapply,
    zNQuot.prod_assoclin_equivapply,
    zNQuot.prodassoc_linequiv_symmapply] using
    zNQuot.maplin_prodc_symma (p := p) G H K n x

/-- Packaged prime-field linear reverse hexagon for Zassenhaus layer kernels (left). -/
theorem zLKern.prodco_lineq_symmh
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p ((H × K) × G) n)) :
    zLKern.prod_comm_linequiv p (H × K) G n x =
      zLKern.prod_assoc_linequiv p G H K n
        (zLKern.mapLinear p ((H × G) × K)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((zLKern.prod_assoc_linequiv p H G K n).symm
            (zLKern.mapLinear p (H × (K × G))
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (zLKern.prod_assoc_linequiv p H K G n x)))) := by
  simpa [zLKern.prod_commlin_equivapply,
    zLKern.prod_assoclin_equivapply,
    zLKern.prodassoc_linequiv_symmapply] using
    zLKern.maplin_prodc_symmh (p := p) G H K n x

/-- Packaged prime-field linear reverse hexagon for Zassenhaus layer kernels (right). -/
theorem zLKern.prodco_lineq_symma
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : Additive (zLKern p (K × (G × H)) n)) :
    zLKern.prod_comm_linequiv p K (G × H) n x =
      (zLKern.prod_assoc_linequiv p G H K n).symm
        (zLKern.mapLinear p (G × (K × H))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (zLKern.prod_assoc_linequiv p G K H n
            (zLKern.mapLinear p ((K × G) × H)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((zLKern.prod_assoc_linequiv p K G H n).symm x)))) := by
  simpa [zLKern.prod_commlin_equivapply,
    zLKern.prod_assoclin_equivapply,
    zLKern.prodassoc_linequiv_symmapply] using
    zLKern.maplin_prodc_symma (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level packaged linear reverse hexagon for consecutive Zassenhaus quotients (left). -/
theorem zNQuot.prodco_equiv_hexle
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p (H × K) G n).toLinearMap =
    (zNQuot.prod_assoc_linequiv p G H K n).toLinearMap.comp
      ((zNQuot.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((zNQuot.prod_assoc_linequiv p H G K n).symm.toLinearMap).comp
          ((zNQuot.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zNQuot.prod_assoc_linequiv p H K G n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodco_lineq_symmh (p := p) G H K n x

/-- Hom-level packaged linear reverse hexagon for consecutive Zassenhaus quotients (right). -/
theorem zNQuot.prodco_equiv_hexri
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p K (G × H) n).toLinearMap =
    ((zNQuot.prod_assoc_linequiv p G H K n).symm.toLinearMap).comp
      ((zNQuot.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zNQuot.prod_assoc_linequiv p G K H n).toLinearMap.comp
          ((zNQuot.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((zNQuot.prod_assoc_linequiv p K G H n).symm.toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodco_lineq_symma (p := p) G H K n x

/-- Hom-level packaged linear reverse hexagon for Zassenhaus layer kernels (left). -/
theorem zLKern.prodco_equiv_hexle
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prod_comm_linequiv p (H × K) G n).toLinearMap =
    (zLKern.prod_assoc_linequiv p G H K n).toLinearMap.comp
      ((zLKern.mapLinear p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((zLKern.prod_assoc_linequiv p H G K n).symm.toLinearMap).comp
          ((zLKern.mapLinear p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zLKern.prod_assoc_linequiv p H K G n).toLinearMap))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodco_lineq_symmh (p := p) G H K n x

/-- Hom-level packaged linear reverse hexagon for Zassenhaus layer kernels (right). -/
theorem zLKern.prodco_equiv_hexri
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prod_comm_linequiv p K (G × H) n).toLinearMap =
    ((zLKern.prod_assoc_linequiv p G H K n).symm.toLinearMap).comp
      ((zLKern.mapLinear p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zLKern.prod_assoc_linequiv p G K H n).toLinearMap.comp
          ((zLKern.mapLinear p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((zLKern.prod_assoc_linequiv p K G H n).symm.toLinearMap)))) := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodco_lineq_symma (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Packaged reverse hexagon coherence for Zassenhaus quotient equivalences (left). -/
theorem zQuot.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zQuot p ((H × K) × G) n) :
    zQuot.prodCommEquiv p (H × K) G n x =
      zQuot.prodAssocEquiv p G H K n
        (zQuot.map p ((H × G) × K)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((zQuot.prodAssocEquiv p H G K n).symm
            (zQuot.map p (H × (K × G))
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (zQuot.prodAssocEquiv p H K G n x)))) := by
  simpa [zQuot.prod_comm_equivapply,
    zQuot.prod_assoc_equivapply,
    zQuot.prod_assocequiv_symmapply] using
    zQuot.mappro_comma_symmh (p := p) G H K n x

/-- Packaged reverse hexagon coherence for Zassenhaus quotient equivalences (right). -/
theorem zQuot.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zQuot p (K × (G × H)) n) :
    zQuot.prodCommEquiv p K (G × H) n x =
      (zQuot.prodAssocEquiv p G H K n).symm
        (zQuot.map p (G × (K × H))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (zQuot.prodAssocEquiv p G K H n
            (zQuot.map p ((K × G) × H)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((zQuot.prodAssocEquiv p K G H n).symm x)))) := by
  simpa [zQuot.prod_comm_equivapply,
    zQuot.prod_assoc_equivapply,
    zQuot.prod_assocequiv_symmapply] using
    zQuot.mapprod_commassoc_symmhexarigh (p := p) G H K n x

/-- Packaged reverse hexagon coherence for consecutive Zassenhaus quotient equivalences (left). -/
theorem zNQuot.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zSubgro p ((H × K) × G) n ⧸
      zNTerm p ((H × K) × G) n) :
    zNQuot.prodCommEquiv p (H × K) G n x =
      zNQuot.prodAssocEquiv p G H K n
        (zNQuot.map p ((H × G) × K)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((zNQuot.prodAssocEquiv p H G K n).symm
            (zNQuot.map p (H × (K × G))
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (zNQuot.prodAssocEquiv p H K G n x)))) := by
  simpa [zNQuot.prod_comm_equivapply,
    zNQuot.prod_assoc_equivapply,
    zNQuot.prod_assocequiv_symmapply] using
    zNQuot.mappro_comma_symmh (p := p) G H K n x

/-- Packaged reverse hexagon coherence for consecutive Zassenhaus quotient equivalences (right). -/
theorem zNQuot.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zSubgro p (K × (G × H)) n ⧸
      zNTerm p (K × (G × H)) n) :
    zNQuot.prodCommEquiv p K (G × H) n x =
      (zNQuot.prodAssocEquiv p G H K n).symm
        (zNQuot.map p (G × (K × H))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (zNQuot.prodAssocEquiv p G K H n
            (zNQuot.map p ((K × G) × H)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((zNQuot.prodAssocEquiv p K G H n).symm x)))) := by
  simpa [zNQuot.prod_comm_equivapply,
    zNQuot.prod_assoc_equivapply,
    zNQuot.prod_assocequiv_symmapply] using
    zNQuot.mapprod_commassoc_symmhexarigh (p := p) G H K n x

/-- Packaged reverse hexagon coherence for Zassenhaus layer-kernel equivalences (left). -/
theorem zLKern.prodco_equiv_symmh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zLKern p ((H × K) × G) n) :
    zLKern.prodCommEquiv p (H × K) G n x =
      zLKern.prodAssocEquiv p G H K n
        (zLKern.map p ((H × G) × K)
          (MonoidHom.prodMap
            (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
            (MonoidHom.id K)) n
          ((zLKern.prodAssocEquiv p H G K n).symm
            (zLKern.map p (H × (K × G))
              (MonoidHom.prodMap (MonoidHom.id H)
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n
              (zLKern.prodAssocEquiv p H K G n x)))) := by
  simpa [zLKern.prod_comm_equivapply,
    zLKern.prod_assoc_equivapply,
    zLKern.prod_assocequiv_symmapply] using
    zLKern.mappro_comma_symmh (p := p) G H K n x

/-- Packaged reverse hexagon coherence for Zassenhaus layer-kernel equivalences (right). -/
theorem zLKern.prodcomm_equivassoc_symmhexarigh
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ)
    (x : zLKern p (K × (G × H)) n) :
    zLKern.prodCommEquiv p K (G × H) n x =
      (zLKern.prodAssocEquiv p G H K n).symm
        (zLKern.map p (G × (K × H))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n
          (zLKern.prodAssocEquiv p G K H n
            (zLKern.map p ((K × G) × H)
              (MonoidHom.prodMap
                (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
                (MonoidHom.id H)) n
              ((zLKern.prodAssocEquiv p K G H n).symm x)))) := by
  simpa [zLKern.prod_comm_equivapply,
    zLKern.prod_assoc_equivapply,
    zLKern.prod_assocequiv_symmapply] using
    zLKern.mapprod_commassoc_symmhexarigh (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level packaged reverse hexagon for Zassenhaus quotient equivalences (left). -/
theorem zQuot.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zQuot.prodCommEquiv p (H × K) G n).toMonoidHom =
    (zQuot.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((zQuot.prodAssocEquiv p H G K n).symm.toMonoidHom).comp
          ((zQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zQuot.prodAssocEquiv p H K G n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prodco_equiv_symmh (p := p) G H K n x

/-- Hom-level packaged reverse hexagon for Zassenhaus quotient equivalences (right). -/
theorem zQuot.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zQuot.prodCommEquiv p K (G × H) n).toMonoidHom =
    ((zQuot.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      ((zQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zQuot.prodAssocEquiv p G K H n).toMonoidHom.comp
          ((zQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((zQuot.prodAssocEquiv p K G H n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prodcomm_equivassoc_symmhexarigh (p := p) G H K n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level packaged reverse hexagon for consecutive Zassenhaus quotient equivalences (left). -/
theorem zNQuot.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodCommEquiv p (H × K) G n).toMonoidHom =
    (zNQuot.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zNQuot.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((zNQuot.prodAssocEquiv p H G K n).symm.toMonoidHom).comp
          ((zNQuot.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zNQuot.prodAssocEquiv p H K G n).toMonoidHom))) := by
  ext x
  exact
    zNQuot.prodco_equiv_symmh (p := p) G H K n x

/-- Hom-level packaged reverse hexagon for consecutive Zassenhaus quotient equivalences (right). -/
theorem zNQuot.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodCommEquiv p K (G × H) n).toMonoidHom =
    ((zNQuot.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      ((zNQuot.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zNQuot.prodAssocEquiv p G K H n).toMonoidHom.comp
          ((zNQuot.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((zNQuot.prodAssocEquiv p K G H n).symm.toMonoidHom)))) := by
  ext x
  exact
    zNQuot.prodcomm_equivassoc_symmhexarigh (p := p) G H K n x

/-- Hom-level packaged reverse hexagon for Zassenhaus layer-kernel equivalences (left). -/
theorem zLKern.prodco_assos_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prodCommEquiv p (H × K) G n).toMonoidHom =
    (zLKern.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zLKern.map p ((H × G) × K)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := H) (N := G)).toMonoidHom
          (MonoidHom.id K)) n).comp
        (((zLKern.prodAssocEquiv p H G K n).symm.toMonoidHom).comp
          ((zLKern.map p (H × (K × G))
            (MonoidHom.prodMap (MonoidHom.id H)
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom) n).comp
            (zLKern.prodAssocEquiv p H K G n).toMonoidHom))) := by
  ext x
  exact
    congrArg Subtype.val
      (zLKern.prodco_equiv_symmh (p := p) G H K n x)

/-- Hom-level packaged reverse hexagon for Zassenhaus layer-kernel equivalences (right). -/
theorem zLKern.prodco_assos_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prodCommEquiv p K (G × H) n).toMonoidHom =
    ((zLKern.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      ((zLKern.map p (G × (K × H))
        (MonoidHom.prodMap (MonoidHom.id G)
          (MulEquiv.prodComm (M := K) (N := H)).toMonoidHom) n).comp
        ((zLKern.prodAssocEquiv p G K H n).toMonoidHom.comp
          ((zLKern.map p ((K × G) × H)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := K) (N := G)).toMonoidHom
              (MonoidHom.id H)) n).comp
            ((zLKern.prodAssocEquiv p K G H n).symm.toMonoidHom)))) := by
  ext x
  exact
    congrArg Subtype.val
      (zLKern.prodcomm_equivassoc_symmhexarigh (p := p) G H K n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level packaged forward hexagon for Zassenhaus quotient equivalences (left). -/
theorem zQuot.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zQuot.prodCommEquiv p G (H × K) n).toMonoidHom =
    ((zQuot.prodAssocEquiv p H K G n).symm.toMonoidHom).comp
      ((zQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zQuot.prodAssocEquiv p H G K n).toMonoidHom.comp
          ((zQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((zQuot.prodAssocEquiv p G H K n).symm.toMonoidHom)))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prodcomm_equivassoc_hexagonleft (p := p) (G := G) H K n x

/-- Hom-level packaged forward hexagon for Zassenhaus quotient equivalences (right). -/
theorem zQuot.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zQuot.prodCommEquiv p (G × H) K n).toMonoidHom =
    (zQuot.prodAssocEquiv p K G H n).toMonoidHom.comp
      ((zQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((zQuot.prodAssocEquiv p G K H n).symm.toMonoidHom).comp
          ((zQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zQuot.prodAssocEquiv p G H K n).toMonoidHom))) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prodcomm_equivassoc_hexagonright (p := p) (G := G) H K n x

/-- Hom-level packaged forward hexagon for consecutive Zassenhaus quotient equivalences (left). -/
theorem zNQuot.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodCommEquiv p G (H × K) n).toMonoidHom =
    ((zNQuot.prodAssocEquiv p H K G n).symm.toMonoidHom).comp
      ((zNQuot.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zNQuot.prodAssocEquiv p H G K n).toMonoidHom.comp
          ((zNQuot.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((zNQuot.prodAssocEquiv p G H K n).symm.toMonoidHom)))) := by
  ext x
  exact
    zNQuot.prodcomm_equivassoc_hexagonleft (p := p) (G := G) H K n x

/-- Hom-level packaged forward hexagon for consecutive Zassenhaus quotient equivalences (right). -/
theorem zNQuot.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodCommEquiv p (G × H) K n).toMonoidHom =
    (zNQuot.prodAssocEquiv p K G H n).toMonoidHom.comp
      ((zNQuot.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((zNQuot.prodAssocEquiv p G K H n).symm.toMonoidHom).comp
          ((zNQuot.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zNQuot.prodAssocEquiv p G H K n).toMonoidHom))) := by
  ext x
  exact
    zNQuot.prodcomm_equivassoc_hexagonright (p := p) (G := G) H K n x

/-- Hom-level packaged forward hexagon for Zassenhaus layer-kernel equivalences (left). -/
theorem zLKern.prodco_equia_leftm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prodCommEquiv p G (H × K) n).toMonoidHom =
    ((zLKern.prodAssocEquiv p H K G n).symm.toMonoidHom).comp
      ((zLKern.map p (H × (G × K))
        (MonoidHom.prodMap (MonoidHom.id H)
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom) n).comp
        ((zLKern.prodAssocEquiv p H G K n).toMonoidHom.comp
          ((zLKern.map p ((G × H) × K)
            (MonoidHom.prodMap
              (MulEquiv.prodComm (M := G) (N := H)).toMonoidHom
              (MonoidHom.id K)) n).comp
            ((zLKern.prodAssocEquiv p G H K n).symm.toMonoidHom)))) := by
  ext x
  exact
    congrArg Subtype.val
      (zLKern.prodcomm_equivassoc_hexagonleft (p := p) (G := G) H K n x)

/-- Hom-level packaged forward hexagon for Zassenhaus layer-kernel equivalences (right). -/
theorem zLKern.prodco_equia_right
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prodCommEquiv p (G × H) K n).toMonoidHom =
    (zLKern.prodAssocEquiv p K G H n).toMonoidHom.comp
      ((zLKern.map p ((G × K) × H)
        (MonoidHom.prodMap
          (MulEquiv.prodComm (M := G) (N := K)).toMonoidHom
          (MonoidHom.id H)) n).comp
        (((zLKern.prodAssocEquiv p G K H n).symm.toMonoidHom).comp
          ((zLKern.map p (G × (H × K))
            (MonoidHom.prodMap (MonoidHom.id G)
              (MulEquiv.prodComm (M := H) (N := K)).toMonoidHom) n).comp
            (zLKern.prodAssocEquiv p G H K n).toMonoidHom))) := by
  ext x
  exact
    congrArg Subtype.val
      (zLKern.prodcomm_equivassoc_hexagonright (p := p) (G := G) H K n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Hom-level packaged pentagon for ordinary Zassenhaus quotient associators. -/
theorem zQuot.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (zQuot.prodAssocEquiv p G H (K × L) n).toMonoidHom.comp
      (zQuot.prodAssocEquiv p (G × H) K L n).toMonoidHom =
    (zQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zQuot.prodAssocEquiv p G (H × K) L n).toMonoidHom.comp
        (zQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prod_assoc_equivpentagon (p := p) (G := G) H K L n x

/-- Hom-level packaged pentagon for consecutive Zassenhaus quotient associators. -/
theorem zNQuot.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (zNQuot.prodAssocEquiv p G H (K × L) n).toMonoidHom.comp
      (zNQuot.prodAssocEquiv p (G × H) K L n).toMonoidHom =
    (zNQuot.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zNQuot.prodAssocEquiv p G (H × K) L n).toMonoidHom.comp
        (zNQuot.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zNQuot.prod_assoc_equivpentagon (p := p) (G := G) H K L n x

/-- Hom-level packaged pentagon for Zassenhaus layer-kernel associators. -/
theorem zLKern.prodas_equiv_monoi
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    (zLKern.prodAssocEquiv p G H (K × L) n).toMonoidHom.comp
      (zLKern.prodAssocEquiv p (G × H) K L n).toMonoidHom =
    (zLKern.map p (G × ((H × K) × L))
      (MonoidHom.prodMap (MonoidHom.id G)
        (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).toMonoidHom) n).comp
      ((zLKern.prodAssocEquiv p G (H × K) L n).toMonoidHom.comp
        (zLKern.map p (((G × H) × K) × L)
          (MonoidHom.prodMap
            (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).toMonoidHom
            (MonoidHom.id L)) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.prod_assoc_equivpentagon (p := p) (G := G) H K L n x)

/-- Hom-level packaged reverse pentagon for ordinary Zassenhaus quotient associators. -/
theorem zQuot.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((zQuot.prodAssocEquiv p (G × H) K L n).symm.toMonoidHom).comp
      ((zQuot.prodAssocEquiv p G H (K × L) n).symm.toMonoidHom) =
    (zQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((zQuot.prodAssocEquiv p G (H × K) L n).symm.toMonoidHom).comp
        (zQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    zQuot.prod_assocequiv_symmpentagon (p := p) (G := G) H K L n x

/-- Hom-level packaged reverse pentagon for consecutive Zassenhaus quotient associators. -/
theorem zNQuot.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((zNQuot.prodAssocEquiv p (G × H) K L n).symm.toMonoidHom).comp
      ((zNQuot.prodAssocEquiv p G H (K × L) n).symm.toMonoidHom) =
    (zNQuot.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((zNQuot.prodAssocEquiv p G (H × K) L n).symm.toMonoidHom).comp
        (zNQuot.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  exact
    zNQuot.prod_assocequiv_symmpentagon (p := p) (G := G) H K L n x

/-- Hom-level packaged reverse pentagon for Zassenhaus layer-kernel associators. -/
theorem zLKern.prodassoc_equivsymm_pentmonohom
    (G H K L : Type*) [Group G] [Group H] [Group K] [Group L] (n : ℕ) :
    ((zLKern.prodAssocEquiv p (G × H) K L n).symm.toMonoidHom).comp
      ((zLKern.prodAssocEquiv p G H (K × L) n).symm.toMonoidHom) =
    (zLKern.map p ((G × (H × K)) × L)
      (MonoidHom.prodMap
        (MulEquiv.prodAssoc (M := G) (N := H) (P := K)).symm.toMonoidHom
        (MonoidHom.id L)) n).comp
      (((zLKern.prodAssocEquiv p G (H × K) L n).symm.toMonoidHom).comp
        (zLKern.map p (G × (H × (K × L)))
          (MonoidHom.prodMap (MonoidHom.id G)
            (MulEquiv.prodAssoc (M := H) (N := K) (P := L)).symm.toMonoidHom) n)) := by
  ext x
  simpa [MonoidHom.comp_apply] using
    congrArg Subtype.val
      (zLKern.prod_assocequiv_symmpentagon (p := p) (G := G) H K L n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Swapping twice is the identity on ordinary Zassenhaus quotient homs. -/
theorem zQuot.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((zQuot.prodCommEquiv p H G n).toMonoidHom).comp
      ((zQuot.prodCommEquiv p G H n).toMonoidHom) =
    MonoidHom.id (zQuot p (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, zQuot.prod_comm_equivapply] using
    zQuot.map_prodcomm_prodcomm (p := p) (G := G) H n x

/-- Swapping twice is the identity on consecutive Zassenhaus quotient homs. -/
theorem zNQuot.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((zNQuot.prodCommEquiv p H G n).toMonoidHom).comp
      ((zNQuot.prodCommEquiv p G H n).toMonoidHom) =
    MonoidHom.id (zSubgro p (G × H) n ⧸
      zNTerm p (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, zNQuot.prod_commequiv_monoidhom] using
    zNQuot.map_prodcomm_prodcomm (p := p) (G := G) H n x

/-- Swapping twice is the identity on Zassenhaus layer-kernel homs. -/
theorem zLKern.prodcomm_equivcomp_selfmonoidhom
    (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((zLKern.prodCommEquiv p H G n).toMonoidHom).comp
      ((zLKern.prodCommEquiv p G H n).toMonoidHom) =
    MonoidHom.id (zLKern p (G × H) n) := by
  ext x
  simpa [MonoidHom.comp_apply, zLKern.prod_comm_equivapply] using
    congrArg Subtype.val
      (zLKern.map_prodcomm_prodcomm (p := p) (G := G) H n x)

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Associator followed by its inverse is identity on Zassenhaus quotient homs. -/
theorem zQuot.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((zQuot.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      (zQuot.prodAssocEquiv p G H K n).toMonoidHom =
    MonoidHom.id (zQuot p ((G × H) × K) n) := by
  ext x
  simp

/-- Inverse associator followed by associator is identity on Zassenhaus quotient homs. -/
theorem zQuot.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zQuot.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zQuot.prodAssocEquiv p G H K n).symm.toMonoidHom) =
    MonoidHom.id (zQuot p (G × (H × K)) n) := by
  ext x
  simp

/-- Associator followed by its inverse is identity on consecutive Zassenhaus quotient homs. -/
theorem zNQuot.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((zNQuot.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      (zNQuot.prodAssocEquiv p G H K n).toMonoidHom =
    MonoidHom.id (zSubgro p ((G × H) × K) n ⧸
      zNTerm p ((G × H) × K) n) := by
  ext x
  simp

/-- Inverse then associator is identity on consecutive Zassenhaus quotient homs. -/
theorem zNQuot.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zNQuot.prodAssocEquiv p G H K n).symm.toMonoidHom) =
    MonoidHom.id (zSubgro p (G × (H × K)) n ⧸
      zNTerm p (G × (H × K)) n) := by
  ext x
  simp

/-- Associator followed by its inverse is identity on Zassenhaus layer-kernel homs. -/
theorem zLKern.prodas_equiv_compm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((zLKern.prodAssocEquiv p G H K n).symm.toMonoidHom).comp
      (zLKern.prodAssocEquiv p G H K n).toMonoidHom =
    MonoidHom.id (zLKern p ((G × H) × K) n) := by
  ext x
  simp

/-- Inverse associator followed by associator is identity on Zassenhaus layer-kernel homs. -/
theorem zLKern.prodas_equiv_symmm
    (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prodAssocEquiv p G H K n).toMonoidHom.comp
      ((zLKern.prodAssocEquiv p G H K n).symm.toMonoidHom) =
    MonoidHom.id (zLKern p (G × (H × K)) n) := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Linear associator followed by its inverse is identity on prime consecutive quotients. -/
theorem zNQuot.prodas_lineq_compl
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((zNQuot.prod_assoc_linequiv p G H K n).symm.toLinearMap).comp
      (zNQuot.prod_assoc_linequiv p G H K n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- Inverse linear associator followed by associator is identity on prime consecutive quotients. -/
theorem zNQuot.prodas_lineq_symml
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zNQuot.prod_assoc_linequiv p G H K n).toLinearMap.comp
      ((zNQuot.prod_assoc_linequiv p G H K n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

/-- Linear associator followed by its inverse is identity on prime layer kernels. -/
theorem zLKern.prodas_lineq_compl
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    ((zLKern.prod_assoc_linequiv p G H K n).symm.toLinearMap).comp
      (zLKern.prod_assoc_linequiv p G H K n).toLinearMap =
    LinearMap.id := by
  ext x
  simp

/-- Inverse linear associator followed by associator is identity on prime layer kernels. -/
theorem zLKern.prodas_lineq_symml
    [Fact p.Prime] (G H K : Type*) [Group G] [Group H] [Group K] (n : ℕ) :
    (zLKern.prod_assoc_linequiv p G H K n).toLinearMap.comp
      ((zLKern.prod_assoc_linequiv p G H K n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simp

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- Swapping twice is identity on prime consecutive quotient linear maps. -/
theorem zNQuot.prodcomm_linequivcomp_selflinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p H G n).toLinearMap.comp
      (zNQuot.prod_comm_linequiv p G H n).toLinearMap =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodcomm_linequiv_applyapply (p := p) (G := G) H n x

/-- Swapping twice is identity on prime layer-kernel linear maps. -/
theorem zLKern.prodcomm_linequivcomp_selflinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (zLKern.prod_comm_linequiv p H G n).toLinearMap.comp
      (zLKern.prod_comm_linequiv p G H n).toLinearMap =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodcomm_linequiv_applyapply (p := p) (G := G) H n x

end GroupAlgebra
end Towers

namespace Towers
namespace GroupAlgebra

variable {p : ℕ}

/-- A prime consecutive-quotient linear swap followed by its inverse is identity. -/
theorem zNQuot.prodcomm_linequivsymm_complinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((zNQuot.prod_comm_linequiv p G H n).symm.toLinearMap).comp
      (zNQuot.prod_comm_linequiv p G H n).toLinearMap =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodcomm_linequiv_applyapply (p := p) (G := G) H n x

/-- The inverse prime consecutive-quotient linear swap followed by swap is identity. -/
theorem zNQuot.prodcomm_linequivcomp_symmlinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (zNQuot.prod_comm_linequiv p G H n).toLinearMap.comp
      ((zNQuot.prod_comm_linequiv p G H n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zNQuot.prodcomm_linequiv_applyapply (p := p) (G := H) G n x

/-- A prime layer-kernel linear swap followed by its inverse is identity. -/
theorem zLKern.prodcomm_linequivsymm_complinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    ((zLKern.prod_comm_linequiv p G H n).symm.toLinearMap).comp
      (zLKern.prod_comm_linequiv p G H n).toLinearMap =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodcomm_linequiv_applyapply (p := p) (G := G) H n x

/-- The inverse prime layer-kernel linear swap followed by swap is identity. -/
theorem zLKern.prodcomm_linequivcomp_symmlinmap
    [Fact p.Prime] (G H : Type*) [Group G] [Group H] (n : ℕ) :
    (zLKern.prod_comm_linequiv p G H n).toLinearMap.comp
      ((zLKern.prod_comm_linequiv p G H n).symm.toLinearMap) =
    LinearMap.id := by
  ext x
  simpa [LinearMap.comp_apply] using
    zLKern.prodcomm_linequiv_applyapply (p := p) (G := H) G n x

end GroupAlgebra
end Towers
