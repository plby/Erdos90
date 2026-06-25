import Mathlib


open scoped BigOperators

namespace Struik

abbrev Choice (α : Type*) (i : ℕ) := Set.powersetCard α i

abbrev Configuration (α β : Type*) (i j k : ℕ) :=
  Set.powersetCard (Choice α i × Choice β j) k

noncomputable def leftSupport
    {α β : Type*} {i j k : ℕ}
    (T : Configuration α β i j k) : Finset α := by
  classical
  exact T.1.biUnion fun z => z.1.1

noncomputable def rightSupport
    {α β : Type*} {i j k : ℕ}
    (T : Configuration α β i j k) : Finset β := by
  classical
  exact T.1.biUnion fun z => z.2.1

lemma mem_leftSupport
    {α β : Type*} {i j k : ℕ}
    (T : Configuration α β i j k) (x : α) :
    x ∈ leftSupport T ↔ ∃ z ∈ T.1, x ∈ z.1.1 := by
  classical
  simp [leftSupport]

lemma mem_rightSupport
    {α β : Type*} {i j k : ℕ}
    (T : Configuration α β i j k) (x : β) :
    x ∈ rightSupport T ↔ ∃ z ∈ T.1, x ∈ z.2.1 := by
  classical
  simp [rightSupport]

def FullSupport
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k) : Prop :=
  leftSupport T = Finset.univ ∧ rightSupport T = Finset.univ

abbrev FullConfiguration
    (α β : Type*) [Fintype α] [Fintype β]
    (i j k : ℕ) :=
  {T : Configuration α β i j k // FullSupport T}

noncomputable def coefficient (i j k a b : ℕ) : ℕ :=
  Nat.card (FullConfiguration (Fin a) (Fin b) i j k)

noncomputable def choiceEquiv
    {α α' : Type*} (e : α ≃ α') (i : ℕ) :
    Choice α i ≃ Choice α' i where
  toFun := Set.powersetCard.map i e.toEmbedding
  invFun := Set.powersetCard.map i e.symm.toEmbedding
  left_inv s := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]
  right_inv s := by
    apply Subtype.ext
    ext x
    simp [Set.powersetCard.map]

@[simp]
lemma choiceEquiv_val
    {α α' : Type*} (e : α ≃ α') (i : ℕ) (s : Choice α i) :
    (choiceEquiv e i s).1 = s.1.map e.toEmbedding :=
  rfl

noncomputable def configurationEquiv
    {α α' β β' : Type*}
    (e : α ≃ α') (f : β ≃ β') (i j k : ℕ) :
    Configuration α β i j k ≃ Configuration α' β' i j k :=
  choiceEquiv ((choiceEquiv e i).prodCongr (choiceEquiv f j)) k

lemma left_support_configuration
    {α α' β β' : Type*}
    (e : α ≃ α') (f : β ≃ β') (i j k : ℕ)
    (T : Configuration α β i j k) :
    leftSupport (configurationEquiv e f i j k T) =
      (leftSupport T).map e.toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map]
    rw [leftSupport, Finset.mem_biUnion] at hx
    rcases hx with ⟨z', hz'T, hxz'⟩
    change z' ∈ T.1.map
      ((choiceEquiv e i).prodCongr (choiceEquiv f j)).toEmbedding at hz'T
    rw [Finset.mem_map] at hz'T
    rcases hz'T with ⟨z, hzT, rfl⟩
    change x ∈ z.1.1.map e.toEmbedding at hxz'
    rw [Finset.mem_map] at hxz'
    rcases hxz' with ⟨y, hyz, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [leftSupport, Finset.mem_biUnion]
    exact ⟨z, hzT, hyz⟩
  · intro hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [leftSupport, Finset.mem_biUnion] at hy
    rcases hy with ⟨z, hzT, hyz⟩
    rw [leftSupport, Finset.mem_biUnion]
    refine ⟨((choiceEquiv e i).prodCongr (choiceEquiv f j)) z, ?_, ?_⟩
    · change
        ((choiceEquiv e i).prodCongr (choiceEquiv f j)) z ∈
          T.1.map
            ((choiceEquiv e i).prodCongr
              (choiceEquiv f j)).toEmbedding
      rw [Finset.mem_map]
      exact ⟨z, hzT, rfl⟩
    · change e y ∈ z.1.1.map e.toEmbedding
      rw [Finset.mem_map]
      exact ⟨y, hyz, rfl⟩

lemma right_support_configuration
    {α α' β β' : Type*}
    (e : α ≃ α') (f : β ≃ β') (i j k : ℕ)
    (T : Configuration α β i j k) :
    rightSupport (configurationEquiv e f i j k T) =
      (rightSupport T).map f.toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map]
    rw [rightSupport, Finset.mem_biUnion] at hx
    rcases hx with ⟨z', hz'T, hxz'⟩
    change z' ∈ T.1.map
      ((choiceEquiv e i).prodCongr (choiceEquiv f j)).toEmbedding at hz'T
    rw [Finset.mem_map] at hz'T
    rcases hz'T with ⟨z, hzT, rfl⟩
    change x ∈ z.2.1.map f.toEmbedding at hxz'
    rw [Finset.mem_map] at hxz'
    rcases hxz' with ⟨y, hyz, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [rightSupport, Finset.mem_biUnion]
    exact ⟨z, hzT, hyz⟩
  · intro hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [rightSupport, Finset.mem_biUnion] at hy
    rcases hy with ⟨z, hzT, hyz⟩
    rw [rightSupport, Finset.mem_biUnion]
    refine ⟨((choiceEquiv e i).prodCongr (choiceEquiv f j)) z, ?_, ?_⟩
    · change
        ((choiceEquiv e i).prodCongr (choiceEquiv f j)) z ∈
          T.1.map
            ((choiceEquiv e i).prodCongr
              (choiceEquiv f j)).toEmbedding
      rw [Finset.mem_map]
      exact ⟨z, hzT, rfl⟩
    · change f y ∈ z.2.1.map f.toEmbedding
      rw [Finset.mem_map]
      exact ⟨y, hyz, rfl⟩

noncomputable def fullConfigurationEquiv
    {α α' β β' : Type*}
    [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (i j k : ℕ) :
    FullConfiguration α β i j k ≃ FullConfiguration α' β' i j k where
  toFun T := ⟨configurationEquiv e f i j k T.1, by
    rcases T.2 with ⟨hleft, hright⟩
    constructor
    · rw [left_support_configuration, hleft]
      exact Finset.map_univ_of_surjective e.surjective
    · rw [right_support_configuration, hright]
      exact Finset.map_univ_of_surjective f.surjective⟩
  invFun T := ⟨configurationEquiv e.symm f.symm i j k T.1, by
    rcases T.2 with ⟨hleft, hright⟩
    constructor
    · rw [left_support_configuration, hleft]
      exact Finset.map_univ_of_surjective e.symm.surjective
    · rw [right_support_configuration, hright]
      exact Finset.map_univ_of_surjective f.symm.surjective⟩
  left_inv T := by
    apply Subtype.ext
    exact (configurationEquiv e f i j k).left_inv T.1
  right_inv T := by
    apply Subtype.ext
    exact (configurationEquiv e f i j k).right_inv T.1

lemma card_choice (α : Type*) [Finite α] (i : ℕ) :
    Nat.card (Choice α i) = (Nat.card α).choose i :=
  Set.powersetCard.card α i

lemma card_configuration (α β : Type*) [Finite α] [Finite β] (i j k : ℕ) :
    Nat.card (Configuration α β i j k) =
      ((Nat.card α).choose i * (Nat.card β).choose j).choose k := by
  rw [Set.powersetCard.card, Nat.card_prod, card_choice, card_choice]

lemma left_support_card
    {α β : Type*}
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    (leftSupport T).card ≤ i * k := by
  classical
  calc
    (leftSupport T).card
        ≤ ∑ z ∈ T.1, z.1.1.card := Finset.card_biUnion_le
    _ = ∑ _z ∈ T.1, i := by
      apply Finset.sum_congr rfl
      intro z hz
      exact z.1.2
    _ = i * k := by simp [Nat.mul_comm]

lemma right_support_card
    {α β : Type*}
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    (rightSupport T).card ≤ j * k := by
  classical
  calc
    (rightSupport T).card
        ≤ ∑ z ∈ T.1, z.2.1.card := Finset.card_biUnion_le
    _ = ∑ _z ∈ T.1, j := by
      apply Finset.sum_congr rfl
      intro z hz
      exact z.2.2
    _ = j * k := by simp [Nat.mul_comm]

lemma left_choice_support
    {α β : Type*}
    {i j k : ℕ}
    (T : Configuration α β i j k)
    (z : Choice α i × Choice β j)
    (hz : z ∈ T.1) :
    z.1.1 ⊆ leftSupport T := by
  classical
  intro x hx
  rw [leftSupport, Finset.mem_biUnion]
  exact ⟨z, hz, hx⟩

lemma choice_subset_support
    {α β : Type*}
    {i j k : ℕ}
    (T : Configuration α β i j k)
    (z : Choice α i × Choice β j)
    (hz : z ∈ T.1) :
    z.2.1 ⊆ rightSupport T := by
  classical
  intro x hx
  rw [rightSupport, Finset.mem_biUnion]
  exact ⟨z, hz, hx⟩

noncomputable def restrictChoice
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice α i) (hA : A.1 ⊆ X) :
    Choice X i := by
  classical
  refine ⟨A.1.subtype (· ∈ X), Set.powersetCard.mem_iff.mpr ?_⟩
  have hmap :
      (A.1.subtype (· ∈ X)).map (Function.Embedding.subtype _) = A.1 :=
    Finset.subtype_map_of_mem (fun x hx => hA hx)
  calc
    (A.1.subtype (· ∈ X)).card =
        ((A.1.subtype (· ∈ X)).map
          (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
    _ = A.1.card := congrArg Finset.card hmap
    _ = i := A.2

lemma mem_restrictChoice
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice α i) (hA : A.1 ⊆ X) (x : X) :
    x ∈ (restrictChoice X A hA).1 ↔ (x : α) ∈ A.1 := by
  classical
  simp [restrictChoice]

noncomputable def extendChoice
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice X i) :
    Choice α i :=
  ⟨A.1.map (Function.Embedding.subtype _),
    Set.powersetCard.mem_iff.mpr (by simp)⟩

lemma mem_extendChoice
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice X i) (x : α) :
    x ∈ (extendChoice X A).1 ↔
      ∃ y ∈ A.1, (y : α) = x := by
  classical
  simp [extendChoice]

@[simp]
lemma extend_choice_restrict
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice α i) (hA : A.1 ⊆ X) :
    extendChoice X (restrictChoice X A hA) = A := by
  classical
  apply Subtype.ext
  exact Finset.subtype_map_of_mem (fun x hx => hA hx)

@[simp]
lemma restrict_choice_extend
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α)
    (A : Choice X i) :
    restrictChoice X (extendChoice X A) (by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.2) = A := by
  classical
  apply Subtype.ext
  ext x
  simp [restrictChoice, extendChoice]

noncomputable def restrictPair
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k)
    (z : {z : Choice α i × Choice β j // z ∈ T.1}) :
    Choice (leftSupport T) i × Choice (rightSupport T) j :=
  (restrictChoice (leftSupport T) z.1.1
      (left_choice_support T z.1 z.2),
    restrictChoice (rightSupport T) z.1.2
      (choice_subset_support T z.1 z.2))

noncomputable def restrictPairEmbedding
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    {z : Choice α i × Choice β j // z ∈ T.1} ↪
      Choice (leftSupport T) i × Choice (rightSupport T) j where
  toFun := restrictPair T
  inj' := by
    intro z z' h
    apply Subtype.ext
    apply Prod.ext
    · have hleft := congrArg (fun w =>
          extendChoice (leftSupport T) w.1) h
      simpa [restrictPair] using hleft
    · have hright := congrArg (fun w =>
          extendChoice (rightSupport T) w.2) h
      simpa [restrictPair] using hright

noncomputable def restrictConfiguration
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    Configuration (leftSupport T) (rightSupport T) i j k := by
  classical
  refine ⟨T.1.attach.map (restrictPairEmbedding T),
    Set.powersetCard.mem_iff.mpr ?_⟩
  rw [Finset.card_map, Finset.card_attach]
  exact T.2

lemma restrictConfiguration_full
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    FullSupport (restrictConfiguration T) := by
  classical
  constructor
  · apply Finset.eq_univ_of_forall
    intro x
    rcases x.2 with hx
    change x.1 ∈ T.1.biUnion (fun z => z.1.1) at hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨z, hzT, hxz⟩
    rw [mem_leftSupport]
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hzT⟩
    refine ⟨restrictPair T zT, ?_, ?_⟩
    · change restrictPair T zT ∈ T.1.attach.map (restrictPairEmbedding T)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    · change x ∈ (restrictChoice (leftSupport T) z.1
        (left_choice_support T z hzT)).1
      simp [restrictChoice, hxz]
  · apply Finset.eq_univ_of_forall
    intro x
    rcases x.2 with hx
    change x.1 ∈ T.1.biUnion (fun z => z.2.1) at hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨z, hzT, hxz⟩
    rw [mem_rightSupport]
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hzT⟩
    refine ⟨restrictPair T zT, ?_, ?_⟩
    · change restrictPair T zT ∈ T.1.attach.map (restrictPairEmbedding T)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    · change x ∈ (restrictChoice (rightSupport T) z.2
        (choice_subset_support T z hzT)).1
      simp [restrictChoice, hxz]

lemma extendChoice_injective
    {α : Type*} [Fintype α]
    {i : ℕ} (X : Finset α) :
    Function.Injective (extendChoice (i := i) X) := by
  intro A B h
  apply Subtype.ext
  exact Finset.map_injective (Function.Embedding.subtype _) (congrArg Subtype.val h)

noncomputable def extendPairEmbedding
    {α β : Type*} [Fintype α] [Fintype β]
    {i j : ℕ}
    (X : Finset α) (Y : Finset β) :
    Choice X i × Choice Y j ↪ Choice α i × Choice β j where
  toFun z := (extendChoice X z.1, extendChoice Y z.2)
  inj' := by
    intro z z' h
    apply Prod.ext
    · exact extendChoice_injective X (congrArg Prod.fst h)
    · exact extendChoice_injective Y (congrArg Prod.snd h)

noncomputable def extendConfiguration
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (U : Configuration X Y i j k) :
    Configuration α β i j k :=
  Set.powersetCard.map k (extendPairEmbedding X Y) U

lemma left_extend_configuration
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (U : Configuration X Y i j k)
    (hU : FullSupport U) :
    leftSupport (extendConfiguration X Y U) = X := by
  classical
  ext x
  rw [mem_leftSupport]
  constructor
  · rintro ⟨z, hz, hx⟩
    change z ∈ U.1.map (extendPairEmbedding X Y) at hz
    rw [Finset.mem_map] at hz
    rcases hz with ⟨w, hwU, rfl⟩
    change x ∈ (extendChoice X w.1).1 at hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    let y : X := ⟨x, hx⟩
    have hy : y ∈ leftSupport U := by
      rw [hU.1]
      exact Finset.mem_univ y
    rw [mem_leftSupport] at hy
    rcases hy with ⟨w, hwU, hyw⟩
    refine ⟨(extendPairEmbedding X Y) w, ?_, ?_⟩
    · change (extendPairEmbedding X Y) w ∈ U.1.map (extendPairEmbedding X Y)
      rw [Finset.mem_map]
      exact ⟨w, hwU, rfl⟩
    · change x ∈ (extendChoice X w.1).1
      exact (mem_extendChoice X w.1 x).2 ⟨y, hyw, rfl⟩

lemma support_extend_configuration
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (U : Configuration X Y i j k)
    (hU : FullSupport U) :
    rightSupport (extendConfiguration X Y U) = Y := by
  classical
  ext x
  rw [mem_rightSupport]
  constructor
  · rintro ⟨z, hz, hx⟩
    change z ∈ U.1.map (extendPairEmbedding X Y) at hz
    rw [Finset.mem_map] at hz
    rcases hz with ⟨w, hwU, rfl⟩
    change x ∈ (extendChoice Y w.2).1 at hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    let y : Y := ⟨x, hx⟩
    have hy : y ∈ rightSupport U := by
      rw [hU.2]
      exact Finset.mem_univ y
    rw [mem_rightSupport] at hy
    rcases hy with ⟨w, hwU, hyw⟩
    refine ⟨(extendPairEmbedding X Y) w, ?_, ?_⟩
    · change (extendPairEmbedding X Y) w ∈ U.1.map (extendPairEmbedding X Y)
      rw [Finset.mem_map]
      exact ⟨w, hwU, rfl⟩
    · change x ∈ (extendChoice Y w.2).1
      exact (mem_extendChoice Y w.2 x).2 ⟨y, hyw, rfl⟩

@[simp]
lemma extend_pair
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k)
    (z : {z : Choice α i × Choice β j // z ∈ T.1}) :
    extendPairEmbedding (leftSupport T) (rightSupport T)
      (restrictPair T z) = z.1 := by
  apply Prod.ext <;> simp [extendPairEmbedding, restrictPair]

lemma extend_configuration
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (T : Configuration α β i j k) :
    extendConfiguration (leftSupport T) (rightSupport T)
      (restrictConfiguration T) = T := by
  classical
  apply Subtype.ext
  ext z
  constructor
  · intro hz
    change z ∈
      (restrictConfiguration T).1.map
        (extendPairEmbedding (leftSupport T) (rightSupport T)) at hz
    rw [Finset.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    change w ∈ T.1.attach.map (restrictPairEmbedding T) at hw
    rw [Finset.mem_map] at hw
    rcases hw with ⟨zT, hzT, rfl⟩
    change
      extendPairEmbedding (leftSupport T) (rightSupport T)
          (restrictPair T zT) ∈ T.1
    rw [extend_pair]
    exact zT.2
  · intro hz
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hz⟩
    have hrestrict :
        restrictPair T zT ∈ (restrictConfiguration T).1 := by
      change restrictPair T zT ∈ T.1.attach.map (restrictPairEmbedding T)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    change z ∈
      (restrictConfiguration T).1.map
        (extendPairEmbedding (leftSupport T) (rightSupport T))
    rw [Finset.mem_map]
    exact ⟨restrictPair T zT, hrestrict,
      extend_pair T zT⟩

abbrev SupportFiber
    {α β : Type*} [Fintype α] [Fintype β]
    (X : Finset α) (Y : Finset β)
    (i j k : ℕ) :=
  {T : Configuration α β i j k //
    leftSupport T = X ∧ rightSupport T = Y}

noncomputable def restrictPairTo
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y)
    (z : {z : Choice α i × Choice β j // z ∈ T.1}) :
    Choice X i × Choice Y j :=
  (restrictChoice X z.1.1 (by
      rw [← hX]
      exact left_choice_support T z.1 z.2),
    restrictChoice Y z.1.2 (by
      rw [← hY]
      exact choice_subset_support T z.1 z.2))

noncomputable def restrictEmbedding
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y) :
    {z : Choice α i × Choice β j // z ∈ T.1} ↪
      Choice X i × Choice Y j where
  toFun := restrictPairTo X Y T hX hY
  inj' := by
    intro z z' h
    apply Subtype.ext
    apply Prod.ext
    · have hleft := congrArg (fun w => extendChoice X w.1) h
      simpa [restrictPairTo] using hleft
    · have hright := congrArg (fun w => extendChoice Y w.2) h
      simpa [restrictPairTo] using hright

noncomputable def restrictConfigurationTo
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y) :
    Configuration X Y i j k := by
  classical
  refine ⟨T.1.attach.map (restrictEmbedding X Y T hX hY),
    Set.powersetCard.mem_iff.mpr ?_⟩
  rw [Finset.card_map, Finset.card_attach]
  exact T.2

lemma restrict_configuration_full
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y) :
    FullSupport (restrictConfigurationTo X Y T hX hY) := by
  classical
  constructor
  · apply Finset.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ leftSupport T := by simp [hX]
    rw [mem_leftSupport] at hx
    rcases hx with ⟨z, hzT, hxz⟩
    rw [mem_leftSupport]
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hzT⟩
    refine ⟨restrictPairTo X Y T hX hY zT, ?_, ?_⟩
    · change restrictPairTo X Y T hX hY zT ∈
        T.1.attach.map (restrictEmbedding X Y T hX hY)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    · have hsub : z.1.1 ⊆ X := by
        rw [← hX]
        exact left_choice_support T z hzT
      exact (mem_restrictChoice X z.1 hsub x).2 hxz
  · apply Finset.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ rightSupport T := by simp [hY]
    rw [mem_rightSupport] at hx
    rcases hx with ⟨z, hzT, hxz⟩
    rw [mem_rightSupport]
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hzT⟩
    refine ⟨restrictPairTo X Y T hX hY zT, ?_, ?_⟩
    · change restrictPairTo X Y T hX hY zT ∈
        T.1.attach.map (restrictEmbedding X Y T hX hY)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    · have hsub : z.2.1 ⊆ Y := by
        rw [← hY]
        exact choice_subset_support T z hzT
      exact (mem_restrictChoice Y z.2 hsub x).2 hxz

@[simp]
lemma extend_pair_restrict
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y)
    (z : {z : Choice α i × Choice β j // z ∈ T.1}) :
    extendPairEmbedding X Y (restrictPairTo X Y T hX hY z) = z.1 := by
  apply Prod.ext <;> simp [extendPairEmbedding, restrictPairTo]

lemma extend_configuration_restrict
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (T : Configuration α β i j k)
    (hX : leftSupport T = X) (hY : rightSupport T = Y) :
    extendConfiguration X Y (restrictConfigurationTo X Y T hX hY) = T := by
  classical
  apply Subtype.ext
  ext z
  constructor
  · intro hz
    change z ∈ (restrictConfigurationTo X Y T hX hY).1.map
      (extendPairEmbedding X Y) at hz
    rw [Finset.mem_map] at hz
    rcases hz with ⟨w, hw, rfl⟩
    change w ∈ T.1.attach.map (restrictEmbedding X Y T hX hY) at hw
    rw [Finset.mem_map] at hw
    rcases hw with ⟨zT, hzT, rfl⟩
    change extendPairEmbedding X Y
      (restrictPairTo X Y T hX hY zT) ∈ T.1
    rw [extend_pair_restrict]
    exact zT.2
  · intro hz
    let zT : {z : Choice α i × Choice β j // z ∈ T.1} := ⟨z, hz⟩
    have hr :
        restrictPairTo X Y T hX hY zT ∈
          (restrictConfigurationTo X Y T hX hY).1 := by
      change restrictPairTo X Y T hX hY zT ∈
        T.1.attach.map (restrictEmbedding X Y T hX hY)
      rw [Finset.mem_map]
      exact ⟨zT, by simp [zT], rfl⟩
    change z ∈ (restrictConfigurationTo X Y T hX hY).1.map
      (extendPairEmbedding X Y)
    rw [Finset.mem_map]
    exact ⟨restrictPairTo X Y T hX hY zT, hr,
      extend_pair_restrict X Y T hX hY zT⟩

@[simp]
lemma restrict_pair_extend
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (U : Configuration X Y i j k)
    (hX : leftSupport (extendConfiguration X Y U) = X)
    (hY : rightSupport (extendConfiguration X Y U) = Y)
    (w : Choice X i × Choice Y j)
    (hw : w ∈ U.1) :
    restrictPairTo X Y (extendConfiguration X Y U) hX hY
      ⟨extendPairEmbedding X Y w, by
        change extendPairEmbedding X Y w ∈ U.1.map (extendPairEmbedding X Y)
        rw [Finset.mem_map]
        exact ⟨w, hw, rfl⟩⟩ = w := by
  apply Prod.ext <;>
    simp [restrictPairTo, extendPairEmbedding]

lemma restrict_configuration_extend
    {α β : Type*} [Fintype α] [Fintype β]
    {i j k : ℕ}
    (X : Finset α) (Y : Finset β)
    (U : Configuration X Y i j k)
    (_hU : FullSupport U)
    (hX : leftSupport (extendConfiguration X Y U) = X)
    (hY : rightSupport (extendConfiguration X Y U) = Y) :
    restrictConfigurationTo X Y (extendConfiguration X Y U) hX hY = U := by
  classical
  apply Subtype.ext
  ext w
  constructor
  · intro hw
    change w ∈
      (extendConfiguration X Y U).1.attach.map
        (restrictEmbedding X Y (extendConfiguration X Y U) hX hY) at hw
    rw [Finset.mem_map] at hw
    rcases hw with ⟨zT, hzT, rfl⟩
    have hz : zT.1 ∈ (extendConfiguration X Y U).1 := by
      simp
    change zT.1 ∈ U.1.map (extendPairEmbedding X Y) at hz
    rw [Finset.mem_map] at hz
    rcases hz with ⟨u, hu, hzu⟩
    let uT :
        {z : Choice α i × Choice β j //
          z ∈ (extendConfiguration X Y U).1} :=
      ⟨extendPairEmbedding X Y u, by
        change extendPairEmbedding X Y u ∈ U.1.map (extendPairEmbedding X Y)
        rw [Finset.mem_map]
        exact ⟨u, hu, rfl⟩⟩
    have hzTu : zT = uT := Subtype.ext hzu.symm
    rw [hzTu]
    change
      restrictPairTo X Y (extendConfiguration X Y U) hX hY uT ∈ U.1
    have hpair :
        restrictPairTo X Y (extendConfiguration X Y U) hX hY uT = u := by
      exact restrict_pair_extend X Y U hX hY u hu
    rw [hpair]
    exact hu
  · intro hw
    have hz :
        extendPairEmbedding X Y w ∈ (extendConfiguration X Y U).1 := by
      change extendPairEmbedding X Y w ∈ U.1.map (extendPairEmbedding X Y)
      rw [Finset.mem_map]
      exact ⟨w, hw, rfl⟩
    let zT :
        {z : Choice α i × Choice β j //
          z ∈ (extendConfiguration X Y U).1} :=
      ⟨extendPairEmbedding X Y w, hz⟩
    change w ∈
      (extendConfiguration X Y U).1.attach.map
        (restrictEmbedding X Y (extendConfiguration X Y U) hX hY)
    rw [Finset.mem_map]
    refine ⟨zT, by simp [zT], ?_⟩
    exact restrict_pair_extend X Y U hX hY w hw

noncomputable def supportFiberConfiguration
    {α β : Type*} [Fintype α] [Fintype β]
    (X : Finset α) (Y : Finset β)
    (i j k : ℕ) :
    SupportFiber X Y i j k ≃ FullConfiguration X Y i j k where
  toFun T :=
    ⟨restrictConfigurationTo X Y T.1 T.2.1 T.2.2,
      restrict_configuration_full X Y T.1 T.2.1 T.2.2⟩
  invFun U :=
    ⟨extendConfiguration X Y U.1,
      left_extend_configuration X Y U.1 U.2,
      support_extend_configuration X Y U.1 U.2⟩
  left_inv T := by
    apply Subtype.ext
    exact extend_configuration_restrict
      X Y T.1 T.2.1 T.2.2
  right_inv U := by
    apply Subtype.ext
    exact restrict_configuration_extend
      X Y U.1 U.2
        (left_extend_configuration X Y U.1 U.2)
        (support_extend_configuration X Y U.1 U.2)

lemma card_supportFiber
    {α β : Type*} [Fintype α] [Fintype β]
    (X : Finset α) (Y : Finset β)
    (i j k : ℕ) :
    Nat.card (SupportFiber X Y i j k) =
      coefficient i j k X.card Y.card := by
  unfold coefficient
  exact Nat.card_congr <|
    (supportFiberConfiguration X Y i j k).trans <|
      fullConfigurationEquiv X.equivFin Y.equivFin i j k

noncomputable def supportPair
    {α β : Type*} {i j k : ℕ}
    (T : Configuration α β i j k) : Finset α × Finset β :=
  (leftSupport T, rightSupport T)

noncomputable def supportPairFiber
    {α β : Type*} [Fintype α] [Fintype β]
    (X : Finset α) (Y : Finset β)
    (i j k : ℕ) :
    {T : Configuration α β i j k // supportPair T = (X, Y)} ≃
      SupportFiber X Y i j k where
  toFun T := ⟨T.1, by
    simpa [supportPair, Prod.ext_iff] using T.2⟩
  invFun T := ⟨T.1, by
    simpa [supportPair, Prod.ext_iff] using T.2⟩
  left_inv T := rfl
  right_inv T := rfl

lemma card_configuration_coefficients
    (α β : Type*) [Fintype α] [Fintype β]
    (i j k : ℕ) :
    Nat.card (Configuration α β i j k) =
      ∑ X : Finset α, ∑ Y : Finset β,
        coefficient i j k X.card Y.card := by
  calc
    Nat.card (Configuration α β i j k) =
        Nat.card (Σ S : Finset α × Finset β,
          {T : Configuration α β i j k // supportPair T = S}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv supportPair).symm
    _ = ∑ S : Finset α × Finset β,
          Nat.card {T : Configuration α β i j k // supportPair T = S} := by
      rw [Nat.card_sigma]
    _ = ∑ X : Finset α, ∑ Y : Finset β,
          Nat.card {T : Configuration α β i j k //
            supportPair T = (X, Y)} := by
      rw [Fintype.sum_prod_type]
    _ = ∑ X : Finset α, ∑ Y : Finset β,
          coefficient i j k X.card Y.card := by
      apply Finset.sum_congr rfl
      intro X hX
      apply Finset.sum_congr rfl
      intro Y hY
      rw [Nat.card_congr (supportPairFiber X Y i j k),
        card_supportFiber]

lemma coefficient_zero_left
    {i j k a b : ℕ} (h : i * k < a) :
    coefficient i j k a b = 0 := by
  unfold coefficient
  rw [Finite.card_eq_zero_iff]
  constructor
  intro T
  have hcard := left_support_card T.1
  rw [T.2.1, Finset.card_univ, Fintype.card_fin] at hcard
  omega

lemma coefficient_zero_right
    {i j k a b : ℕ} (h : j * k < b) :
    coefficient i j k a b = 0 := by
  unfold coefficient
  rw [Finite.card_eq_zero_iff]
  constructor
  intro T
  have hcard := right_support_card T.1
  rw [T.2.2, Finset.card_univ, Fintype.card_fin] at hcard
  omega

lemma sum_finset_card
    (α : Type*) [Fintype α]
    (f : ℕ → ℕ) :
    (∑ X : Finset α, f X.card) =
      ∑ a ∈ Finset.range (Fintype.card α + 1),
        (Fintype.card α).choose a * f a := by
  classical
  calc
    (∑ X : Finset α, f X.card) =
        ∑ X ∈ (Finset.univ : Finset α).powerset, f X.card := by simp
    _ = ∑ a ∈ Finset.range ((Finset.univ : Finset α).card + 1),
          ∑ X ∈ (Finset.univ : Finset α).powersetCard a, f X.card :=
      Finset.sum_powerset (Finset.univ : Finset α) (fun X => f X.card)
    _ = ∑ a ∈ Finset.range (Fintype.card α + 1),
          (Fintype.card α).choose a * f a := by
      apply Finset.sum_congr
      · simp
      · intro a ha
        rw [Finset.sum_powersetCard]
        simp []

lemma eq_range_succ
    (f : ℕ → ℕ) (m n : ℕ)
    (hm : ∀ x, m < x → f x = 0)
    (hn : ∀ x, n < x → f x = 0) :
    (∑ x ∈ Finset.range (m + 1), f x) =
      ∑ x ∈ Finset.range (n + 1), f x := by
  by_cases hmn : m ≤ n
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmn))
    intro x hx hxm
    have hmx : m < x := by
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range, not_lt] at hxm
      omega
    exact hm x hmx
  · symm
    have hnm : n ≤ m := Nat.le_of_lt (lt_of_not_ge hmn)
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hnm))
    intro x hx hxn
    have hnx : n < x := by
      rw [Finset.mem_range] at hx
      rw [Finset.mem_range, not_lt] at hxn
      omega
    exact hn x hnx

/-- Struik's Lemma 5. The coefficients are uniform in `r` and `s` and
are cardinalities, hence nonnegative. -/
theorem choose_coeff_mul (i j k r s : ℕ) :
    Nat.choose (Nat.choose r i * Nat.choose s j) k =
      ∑ a ∈ Finset.range (i * k + 1),
        ∑ b ∈ Finset.range (j * k + 1),
          coefficient i j k a b *
            Nat.choose r a * Nat.choose s b := by
  have hcard :
      Nat.choose (Nat.choose r i * Nat.choose s j) k =
        ∑ X : Finset (Fin r), ∑ Y : Finset (Fin s),
          coefficient i j k X.card Y.card := by
    calc
      Nat.choose (Nat.choose r i * Nat.choose s j) k =
          Nat.card (Configuration (Fin r) (Fin s) i j k) := by
        symm
        simpa using card_configuration (Fin r) (Fin s) i j k
      _ = ∑ X : Finset (Fin r), ∑ Y : Finset (Fin s),
            coefficient i j k X.card Y.card :=
        card_configuration_coefficients (Fin r) (Fin s) i j k
  have hcard' :
      Nat.choose (Nat.choose r i * Nat.choose s j) k =
        ∑ a ∈ Finset.range (r + 1),
          Nat.choose r a *
            (∑ b ∈ Finset.range (s + 1),
              Nat.choose s b * coefficient i j k a b) := by
    refine hcard.trans ?_
    have hout := sum_finset_card (Fin r)
      (fun a => ∑ Y : Finset (Fin s),
        coefficient i j k a Y.card)
    rw [hout]
    simp only [Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    have hin := sum_finset_card (Fin s)
      (fun b => coefficient i j k a b)
    rw [hin]
    simp
  rw [hcard']
  have hinner (a : ℕ) :
      (∑ b ∈ Finset.range (s + 1),
          Nat.choose s b * coefficient i j k a b) =
        ∑ b ∈ Finset.range (j * k + 1),
          Nat.choose s b * coefficient i j k a b := by
    apply eq_range_succ
    · intro b hb
      rw [Nat.choose_eq_zero_of_lt hb, zero_mul]
    · intro b hb
      rw [coefficient_zero_right hb, mul_zero]
  simp_rw [hinner] at hcard' ⊢
  have houter :
      (∑ a ∈ Finset.range (r + 1),
          Nat.choose r a *
            (∑ b ∈ Finset.range (j * k + 1),
              Nat.choose s b * coefficient i j k a b)) =
        ∑ a ∈ Finset.range (i * k + 1),
          Nat.choose r a *
            (∑ b ∈ Finset.range (j * k + 1),
              Nat.choose s b * coefficient i j k a b) := by
    apply eq_range_succ
    · intro a ha
      rw [Nat.choose_eq_zero_of_lt ha, zero_mul]
    · intro a ha
      have hcoeff :
          ∀ b, coefficient i j k a b = 0 :=
        fun b => coefficient_zero_left ha
      simp [hcoeff]
  rw [houter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ac_rfl

end Struik
