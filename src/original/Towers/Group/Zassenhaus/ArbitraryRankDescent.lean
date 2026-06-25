import Towers.Group.Zassenhaus.EpimorphicDescent
import Towers.Group.FreeGroupSeparation


/-!
# Finite-support and arbitrary-group descent

Every element of an arbitrarily generated free group uses only finitely many
letters.  This file combines that reduction with the finite-basis results and
epimorphic descent to obtain the unrestricted forms of Theorem 7.4,
Corollary 7.5, and Theorem 8.3.
-/

noncomputable section

namespace EChapma

open Towers
open Towers.TBluepr

variable {G Q : Type*} [Group G] [Group Q]

/-- Relative power subgroups are functorial in the forward direction under
an arbitrary group homomorphism. -/
theorem subgroup_power
    (H : Subgroup G) (a : ℕ) (f : G →* Q) :
    (subgroupPower H a).map f ≤
      subgroupPower (H.map f) a := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold subgroupPower
  apply Subgroup.normalClosure_le_normal
  rintro y ⟨x, hx, rfl⟩
  change f (x ^ a) ∈ subgroupPower (H.map f) a
  rw [map_pow]
  exact
    pow_subgroup_power (H.map f) a
      (Subgroup.mem_map_of_mem f hx)

/-- The closed sequence lower-central product is forward-functorial under
every group homomorphism. -/
theorem sequence_lower_product
    (A : ℕ → ℕ) (n : ℕ) (f : G →* Q) :
    (sequenceLowerProduct (G := G) A n).map f ≤
      sequenceLowerProduct (G := Q) A n := by
  unfold sequenceLowerProduct
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro i
  refine
    (subgroup_power
      (Subgroup.lowerCentralSeries G (i.1 - 1))
      ((MDescen.ofSequence A) n i.1) f).trans ?_
  refine le_iSup_of_le i ?_
  exact subgroupPower_mono
    (Subgroup.lowerCentralSeries.map f (i.1 - 1))
    ((MDescen.ofSequence A) n i.1)

/-- The logarithmic lower-central product is forward-functorial under every
group homomorphism. -/
theorem logarithmic_lower_product
    (p r n : ℕ) (hp : p.Prime) (f : G →* Q) :
    (logarithmicLowerProduct (G := G) p r hp n).map f ≤
      logarithmicLowerProduct (G := Q) p r hp n := by
  unfold logarithmicLowerProduct
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro i
  refine
    (subgroup_power
      (Subgroup.lowerCentralSeries G (i.1 - 1))
      ((MDescen.logarithmicPrimePower
        p r hp) n i.1) f).trans ?_
  refine le_iSup_of_le i ?_
  exact subgroupPower_mono
    (Subgroup.lowerCentralSeries.map f (i.1 - 1))
    ((MDescen.logarithmicPrimePower
      p r hp) n i.1)

section FiniteAlphabet

universe u

variable {X : Type u} {w : FreeGroup X}

/-- The canonical projection associated to a finite alphabet model: retained
letters map back to their finite generators and all other letters map to
one. -/
def finiteAlphabetProjection
    (M : FGAlphab X w) :
    FreeGroup X →* FreeGroup M.support := by
  classical
  exact
    FreeGroup.lift fun x =>
      if h : ∃ s : M.support, M.letterEmbedding s = x then
        FreeGroup.of (Classical.choose h)
      else
        1

@[simp]
theorem alphabet_projection_inclusion
    (M : FGAlphab X w) (x : M.support) :
    finiteAlphabetProjection M
        (M.inclusionMap (FreeGroup.of x)) =
      FreeGroup.of x := by
  rw [M.inclusion_on_generators]
  have hmem :
      ∃ s : M.support,
        M.letterEmbedding s = M.letterEmbedding x :=
    ⟨x, rfl⟩
  have hchoose : Classical.choose hmem = x :=
    M.letterEmbedding.injective
      (Classical.choose_spec hmem)
  simp [finiteAlphabetProjection]

theorem alphabet_comp_inclusion
    (M : FGAlphab X w) :
    (finiteAlphabetProjection M).comp M.inclusionMap =
      MonoidHom.id (FreeGroup M.support) := by
  ext x
  exact alphabet_projection_inclusion M x

theorem alphabet_projection_surjective
    (M : FGAlphab X w) :
    Function.Surjective (finiteAlphabetProjection M) := by
  intro y
  refine ⟨M.inclusionMap y, ?_⟩
  change
    ((finiteAlphabetProjection M).comp M.inclusionMap) y = y
  rw [alphabet_comp_inclusion]
  rfl

theorem alphabet_projection_word
    (M : FGAlphab X w) :
    finiteAlphabetProjection M w = M.modelWord := by
  calc
    finiteAlphabetProjection M w =
        finiteAlphabetProjection M
          (M.inclusionMap M.modelWord) := by
            exact congrArg (finiteAlphabetProjection M)
              M.inclusion_model_word.symm
    _ =
        ((finiteAlphabetProjection M).comp M.inclusionMap)
          M.modelWord := rfl
    _ = M.modelWord := by
      rw [alphabet_comp_inclusion]
      rfl

end FiniteAlphabet

section ArbitraryFreeGroup

variable {X : Type*}

/-- Efrat--Chapman, Theorem 7.4 for a free group on an arbitrary set. -/
theorem filtration_sequence_arbitrary
    (A : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := FreeGroup X) A n =
      sequenceLowerProduct (G := FreeGroup X) A n := by
  apply le_antisymm
  · intro w hw
    classical
    obtain ⟨M⟩ := free_alphabet_any w
    let π : FreeGroup X →* FreeGroup M.support :=
      finiteAlphabetProjection M
    have hπ : Function.Surjective π :=
      alphabet_projection_surjective M
    have hmodelA :
        M.modelWord ∈
          aFiltration (G := FreeGroup M.support) A n := by
      have himage :
          π w ∈
            (aFiltration (G := FreeGroup X) A n).map π :=
        Subgroup.mem_map_of_mem π hw
      rw [a_map_of A n π hπ] at himage
      simpa [π, alphabet_projection_word M] using himage
    letI : DecidableEq M.support := Classical.decEq _
    letI : Encodable M.support := Fintype.toEncodable _
    have hmodelProduct :
        M.modelWord ∈
          sequenceLowerProduct
            (G := FreeGroup M.support) A n := by
      rw [← filtration_sequence_product
        (X := M.support) A n hn]
      exact hmodelA
    have himage :
        M.inclusionMap M.modelWord ∈
          (sequenceLowerProduct
            (G := FreeGroup M.support) A n).map
              M.inclusionMap :=
      Subgroup.mem_map_of_mem M.inclusionMap hmodelProduct
    have hambient :=
      sequence_lower_product A n
        M.inclusionMap himage
    simpa [M.inclusion_model_word] using hambient
  · exact sequence_lower_filtration A n

/-- Efrat--Chapman, Theorem 8.3 for a free group on an arbitrary set. -/
theorem q_logarithmic_arbitrary
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    qZassenhausFiltration (FreeGroup X) p (p ^ r) hp n =
      logarithmicLowerProduct
        (G := FreeGroup X) p r hp n := by
  apply le_antisymm
  · intro w hw
    classical
    obtain ⟨M⟩ := free_alphabet_any w
    let π : FreeGroup X →* FreeGroup M.support :=
      finiteAlphabetProjection M
    have hπ : Function.Surjective π :=
      alphabet_projection_surjective M
    have hmodelZ :
        M.modelWord ∈
          qZassenhausFiltration
            (FreeGroup M.support) p (p ^ r) hp n := by
      have himage :
          π w ∈
            (qZassenhausFiltration
              (FreeGroup X) p (p ^ r) hp n).map π :=
        Subgroup.mem_map_of_mem π hw
      rw [q_filtration_surjective
        p (p ^ r) n hp π hπ] at himage
      simpa [π, alphabet_projection_word M] using himage
    letI : DecidableEq M.support := Classical.decEq _
    letI : Encodable M.support := Fintype.toEncodable _
    have hmodelProduct :
        M.modelWord ∈
          logarithmicLowerProduct
            (G := FreeGroup M.support) p r hp n := by
      rw [← q_logarithmic_product
        (X := M.support) p r n hp hr hn]
      exact hmodelZ
    have himage :
        M.inclusionMap M.modelWord ∈
          (logarithmicLowerProduct
            (G := FreeGroup M.support) p r hp n).map
              M.inclusionMap :=
      Subgroup.mem_map_of_mem M.inclusionMap hmodelProduct
    have hambient :=
      logarithmic_lower_product
        p r n hp M.inclusionMap himage
    simpa [M.inclusion_model_word] using hambient
  · exact
      logarithmic_q_filtration
        p r n hp

end ArbitraryFreeGroup

section ArbitraryGroup

/-- Efrat--Chapman, Theorem 7.4 for an arbitrary group. -/
theorem filtration_arbitrary_group
    (A : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := G) A n =
      sequenceLowerProduct (G := G) A n := by
  let π : FreeGroup G →* G := FreeGroup.lift id
  have hπ : Function.Surjective π := by
    intro g
    exact ⟨FreeGroup.of g, by simp [π]⟩
  exact
    filtration_sequence_surjective
      A n π hπ
      (filtration_sequence_arbitrary
        (X := G) A n hn)

/-- Efrat--Chapman, Corollary 7.5 for an arbitrary group. -/
theorem constant_filtration_arbitrary
    (a n : ℕ) (hn : 1 ≤ n) :
    aFiltration (G := G) (fun _ => a) n =
      ⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ n},
        subgroupPower (Subgroup.lowerCentralSeries G (i.1 - 1))
          (a ^ (n - i.1)) := by
  rw [filtration_arbitrary_group
    (G := G) (fun _ => a) n hn]
  unfold sequenceLowerProduct
  congr 1
  funext i
  rw [MDescen.sequenceCoefficient_const
    a n i.1 i.property.1 i.property.2]

/-- Efrat--Chapman, Theorem 8.3 for an arbitrary group. -/
theorem filtration_logarithmic_arbitrary
    (p r n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    qZassenhausFiltration G p (p ^ r) hp n =
      logarithmicLowerProduct (G := G) p r hp n := by
  let π : FreeGroup G →* G := FreeGroup.lift id
  have hπ : Function.Surjective π := by
    intro g
    exact ⟨FreeGroup.of g, by simp [π]⟩
  exact
    q_logarithmic_surjective
      p r n hp π hπ
      (q_logarithmic_arbitrary
        (X := G) p r n hp hr hn)

end ArbitraryGroup

end EChapma
