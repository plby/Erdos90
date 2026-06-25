import Submission.Group.Zassenhaus.AFiltration
import Submission.Group.Zassenhaus.ZassenhausEquality
import Submission.Group.Edmonton.CentralSeries


/-!
# Epimorphic descent for the recursive filtrations

This file proves that the filtrations and their closed product formulas
commute with surjective group homomorphisms.  It packages the descent step
used in Sections 7 and 8 of Efrat--Chapman.
-/

noncomputable section

namespace EChapma

variable {G Q : Type*} [Group G] [Group Q]

/-- Relative power-commutator subgroups commute with surjective images. -/
theorem relative_commutator_surjective
    (H : Subgroup G) (a : ℕ) (f : G →* Q)
    (hf : Function.Surjective f) :
    (relativePowerCommutator H a).map f =
      relativePowerCommutator (H.map f) a := by
  rw [relativePowerCommutator, relativePowerCommutator,
    Subgroup.map_sup, subgroup_power_surjective H a f hf,
    Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]

/-- A finite list of `A`-filtration steps commutes with surjective images. -/
theorem filtration_list_surjective
    (exponents : List ℕ) (f : G →* Q)
    (hf : Function.Surjective f) :
    (filtrationList (G := G) exponents).map f =
      filtrationList (G := Q) exponents := by
  induction exponents using List.reverseRecOn with
  | nil =>
      simpa using Subgroup.map_top_of_surjective f hf
  | append_singleton exponents a ih =>
      rw [filtration_append_singleton,
        filtration_append_singleton,
        relative_commutator_surjective _ a f hf, ih]

/-- The paper's `A`-filtration commutes with surjective images. -/
theorem a_map_of
    (A : ℕ → ℕ) (n : ℕ) (f : G →* Q)
    (hf : Function.Surjective f) :
    (aFiltration (G := G) A n).map f =
      aFiltration (G := Q) A n := by
  unfold aFiltration aFiltrationPrefix
  exact filtration_list_surjective _ f hf

/-- The closed sequence lower-central product commutes with surjective
images. -/
theorem sequence_lower_surjective
    (A : ℕ → ℕ) (n : ℕ) (f : G →* Q)
    (hf : Function.Surjective f) :
    (sequenceLowerProduct (G := G) A n).map f =
      sequenceLowerProduct (G := Q) A n := by
  unfold sequenceLowerProduct
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro i
  rw [subgroup_power_surjective _ _ f hf,
    Submission.Edmonton.central_series_surjective f hf]

/-- The recursive q-Zassenhaus filtration commutes with surjective images. -/
theorem q_filtration_surjective
    (p q n : ℕ) (hp : p.Prime) (f : G →* Q)
    (hf : Function.Surjective f) :
    (qZassenhausFiltration G p q hp n).map f =
      qZassenhausFiltration Q p q hp n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | n
      · simpa using Subgroup.map_top_of_surjective f hf
      · simpa using Subgroup.map_top_of_surjective f hf
      · rw [q_filtration_succ,
          q_filtration_succ, Subgroup.map_sup,
          subgroup_power_surjective _ _ f hf,
          ih ((n + 2) ⌈/⌉ p)
            (ceil_div_self p (n + 2) hp (by omega)),
          Subgroup.map_iSup]
        congr 1
        apply iSup_congr
        intro st
        rw [Subgroup.map_commutator,
          ih st.1.1 (by omega), ih st.1.2 (by omega)]

/-- Equality of the `A`-filtration and its product formula descends along
any surjective group homomorphism. -/
theorem filtration_sequence_surjective
    (A : ℕ → ℕ) (n : ℕ) (f : G →* Q)
    (hf : Function.Surjective f)
    (hsource :
      aFiltration (G := G) A n =
        sequenceLowerProduct (G := G) A n) :
    aFiltration (G := Q) A n =
      sequenceLowerProduct (G := Q) A n := by
  have hmap := congrArg (fun H : Subgroup G => H.map f) hsource
  simpa [a_map_of A n f hf,
    sequence_lower_surjective A n f hf] using hmap

/-- Equality of the recursive q-Zassenhaus filtration and its product formula
descends along any surjective group homomorphism. -/
theorem q_logarithmic_surjective
    (p r n : ℕ) (hp : p.Prime) (f : G →* Q)
    (hf : Function.Surjective f)
    (hsource :
      qZassenhausFiltration G p (p ^ r) hp n =
        logarithmicLowerProduct (G := G) p r hp n) :
    qZassenhausFiltration Q p (p ^ r) hp n =
      logarithmicLowerProduct (G := Q) p r hp n := by
  have hmap := congrArg (fun H : Subgroup G => H.map f) hsource
  change
    (qZassenhausFiltration G p (p ^ r) hp n).map f =
      (logarithmicLowerProduct (G := G) p r hp n).map f at hmap
  rw [q_filtration_surjective p (p ^ r) n hp f hf] at hmap
  unfold logarithmicLowerProduct at hmap ⊢
  rw [Subgroup.map_iSup] at hmap
  simpa only [subgroup_power_surjective _ _ f hf,
    Submission.Edmonton.central_series_surjective f hf] using hmap

section FiniteGroup

variable [Finite G]

/-- Theorem 7.4 for finite groups, obtained by epimorphic descent from the
finite-basis free-group theorem. -/
theorem filtration_sequence_group
    (A : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := G) A n =
      sequenceLowerProduct (G := G) A n := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Encodable G := Fintype.toEncodable G
  let π : FreeGroup G →* G := FreeGroup.lift id
  have hπ : Function.Surjective π := by
    intro g
    exact ⟨FreeGroup.of g, by simp [π]⟩
  exact
    filtration_sequence_surjective
      A n π hπ
      (filtration_sequence_product
        (X := G) A n hn)

/-- Corollary 7.5 for finite groups. -/
theorem constant_filtration_group
    (a n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := G) (fun _ => a) n =
      ⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ n},
        subgroupPower (Subgroup.lowerCentralSeries G (i.1 - 1))
          (a ^ (n - i.1)) := by
  rw [filtration_sequence_group
    (fun _ => a) n hn]
  unfold sequenceLowerProduct
  congr 1
  funext i
  rw [MDescen.sequenceCoefficient_const
    a n i.1 i.property.1 i.property.2]

/-- Theorem 8.3 for finite groups, obtained by epimorphic descent from the
finite-basis free-group theorem. -/
theorem q_filtration_logarithmic
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    qZassenhausFiltration G p (p ^ r) hp n =
      logarithmicLowerProduct (G := G) p r hp n := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Encodable G := Fintype.toEncodable G
  let π : FreeGroup G →* G := FreeGroup.lift id
  have hπ : Function.Surjective π := by
    intro g
    exact ⟨FreeGroup.of g, by simp [π]⟩
  exact
    q_logarithmic_surjective
      p r n hp π hπ
      (q_logarithmic_product
        (X := G) p r n hp hr hn)

end FiniteGroup

end EChapma
