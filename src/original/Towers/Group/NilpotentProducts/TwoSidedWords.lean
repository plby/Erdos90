import Towers.Group.Petresco.PositiveOneSided

open scoped BigOperators

namespace Struik

open Towers Edmonton

/-- Formal commutator words in the two letters `b` and `a`. -/
abbrev Word := FormalCommutator Bool

def basicWord : Word :=
  formalBracket (FreeMagma.of false) (FreeMagma.of true)

def bChain : ℕ → Word
  | 0 => basicWord
  | n + 1 => formalBracket (bChain n) (FreeMagma.of false)

def aChain : ℕ → Word
  | 0 => basicWord
  | n + 1 => formalBracket (aChain n) (FreeMagma.of true)

/-- A rectangular commutator: first extend `[b,a]` by `q` copies of `b`,
then by `t` copies of `a`. -/
def gridWord (q : ℕ) : ℕ → Word
  | 0 => bChain q
  | t + 1 => formalBracket (gridWord q t) (FreeMagma.of true)

def conjugateExpansion (u : Word) : List Word :=
  [u, formalBracket u (FreeMagma.of true)]

/-- The exact uncollected correction word in
`b^s * a^r = a^r * b^s * correction`. -/
def twoSidedWord (s : ℕ) : ℕ → List Word
  | 0 => []
  | r + 1 =>
      positiveSidedOrbit s ++
        (twoSidedWord s r).flatMap conjugateExpansion

@[simp]
lemma eval_conjugate_expansion
    {G : Type*} [Group G] (b a : G) (u : Word) :
    evalFormalWord
        (fun | false => b | true => a)
        (conjugateExpansion u) =
      hallConjugate
        (generatorFormalCommutator b a u) a := by
  simp [conjugateExpansion, generatorFormalCommutator,
    hall_conjugate_commutator]
  rfl

lemma flat_conjugate_expansion
    {G : Type*} [Group G] (b a : G) (words : List Word) :
    evalFormalWord
        (fun | false => b | true => a)
        (words.flatMap conjugateExpansion) =
      hallConjugate
        (evalFormalWord
          (fun | false => b | true => a) words) a := by
  induction words with
  | nil => simp [hallConjugate]
  | cons u words ih =>
      simp only [List.flatMap_cons, eval_formal_append,
        eval_formal_cons]
      rw [eval_conjugate_expansion, ih]
      change hallConjugate
          (generatorFormalCommutator b a u) a *
          hallConjugate
            (evalFormalWord (fun | false => b | true => a) words) a =
        hallConjugate
          (generatorFormalCommutator b a u *
            evalFormalWord (fun | false => b | true => a) words) a
      simp [hallConjugate, mul_assoc]

theorem eval_sided_word
    {G : Type*} [Group G] (b a : G) (s : ℕ) :
    ∀ r : ℕ,
      evalFormalWord
          (fun | false => b | true => a)
          (twoSidedWord s r) =
        hallCommutator (b ^ s) (a ^ r) := by
  intro r
  induction r with
  | zero => simp [twoSidedWord, hallCommutator]
  | succ r ih =>
      rw [twoSidedWord, eval_formal_append,
        flat_conjugate_expansion, ih]
      apply Eq.trans
        (congrArg
          (fun z => z * hallConjugate (hallCommutator (b ^ s) (a ^ r)) a)
          (positive_sided_orbit b a s))
      rw [pow_succ, commutator_mul_right]

/-- The raw, uncollected word identity underlying equation (31).

This does not yet prove Struik's Lemma 4: that lemma concerns the exponents
of standard commutators after Hall collection in a nilpotent group. -/
theorem raw_sided_identity
    {G : Type*} [Group G] (b a : G) (s r : ℕ) :
    b ^ s * a ^ r =
      a ^ r * b ^ s *
        evalFormalWord
          (fun | false => b | true => a)
          (twoSidedWord s r) := by
  rw [eval_sided_word]
  simp [hallCommutator]
  group

lemma b_chain_ne (n : ℕ) :
    bChain (n + 1) ≠ basicWord := by
  intro h
  unfold bChain basicWord formalBracket at h
  injection h with _ hright
  have hfalse : false = true := by
    injection hright
  exact Bool.noConfusion hfalse

lemma chain_succ_ne (n : ℕ) :
    aChain (n + 1) ≠ basicWord := by
  intro h
  unfold aChain basicWord formalBracket at h
  injection h with hleft _
  cases n with
  | zero =>
      unfold aChain basicWord formalBracket at hleft
      cases hleft
  | succ n =>
      unfold aChain formalBracket at hleft
      cases hleft

lemma bracket_b_chain (u : Word) (n : ℕ) :
    formalBracket u (FreeMagma.of false) = bChain (n + 1) ↔
      u = bChain n := by
  constructor
  · intro h
    unfold bChain formalBracket at h
    injection h
  · intro h
    rw [h, bChain]

lemma formal_bracket_chain (u : Word) (n : ℕ) :
    formalBracket u (FreeMagma.of true) = aChain (n + 1) ↔
      u = aChain n := by
  constructor
  · intro h
    unfold aChain formalBracket at h
    injection h
  · intro h
    rw [h, aChain]

lemma formal_bracket_word (u : Word) :
    formalBracket u (FreeMagma.of true) = basicWord ↔
      u = FreeMagma.of false := by
  constructor
  · intro h
    unfold basicWord formalBracket at h
    injection h
  · intro h
    rw [h]
    rfl

lemma count_b_chain
    (words : List Word) (q : ℕ) :
    (words.flatMap formalConjugateLeft).count (bChain q) =
      words.count (bChain q) +
        if q = 0 then 0 else words.count (bChain (q - 1)) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      cases q with
      | zero =>
          simp only [List.flatMap_cons, formalConjugateLeft,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          have hne :
              formalBracket u (FreeMagma.of false) ≠ basicWord := by
            intro h
            unfold basicWord formalBracket at h
            injection h with _ hright
            have hfalse : false = true := by
              injection hright
            exact Bool.noConfusion hfalse
          simp only [bChain, beq_iff_eq, hne, ↓reduceIte]
          omega
      | succ q =>
          simp only [List.flatMap_cons, formalConjugateLeft,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          simp only [if_neg (Nat.succ_ne_zero q), Nat.succ_sub_one,
            beq_iff_eq, bracket_b_chain]
          omega

lemma count_chain_flat
    (words : List Word) (q : ℕ) :
    (words.flatMap conjugateExpansion).count (aChain q) =
      words.count (aChain q) +
        if q = 0 then words.count (FreeMagma.of false)
        else words.count (aChain (q - 1)) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      cases q with
      | zero =>
          simp only [List.flatMap_cons, conjugateExpansion,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          simp only [aChain, beq_iff_eq, formal_bracket_word,
            ite_true]
          omega
      | succ q =>
          simp only [List.flatMap_cons, conjugateExpansion,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          simp only [if_neg (Nat.succ_ne_zero q), Nat.succ_sub_one,
            beq_iff_eq, formal_bracket_chain]
          omega

lemma formal_ne_chain (u : Word) (q : ℕ) :
    formalBracket u (FreeMagma.of false) ≠ aChain q := by
  intro h
  cases q with
  | zero =>
      unfold aChain basicWord formalBracket at h
      injection h with _ hright
      have hfalse : false = true := by
        injection hright
      exact Bool.noConfusion hfalse
  | succ q =>
      unfold aChain formalBracket at h
      injection h with _ hright
      have hfalse : false = true := by
        injection hright
      exact Bool.noConfusion hfalse

lemma chain_flat_left
    (words : List Word) (q : ℕ) :
    (words.flatMap formalConjugateLeft).count (aChain q) =
      words.count (aChain q) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      simp only [List.flatMap_cons, formalConjugateLeft,
        List.count_append, List.count_cons, List.count_nil, zero_add]
      rw [ih]
      simp only [beq_iff_eq, formal_ne_chain, ↓reduceIte]
      omega

lemma formal_b_chain (u : Word) (q : ℕ) :
    formalBracket u (FreeMagma.of true) ≠ bChain (q + 1) := by
  intro h
  unfold bChain formalBracket at h
  injection h with _ hright
  have hfalse : true = false := by
    injection hright
  exact Bool.noConfusion hfalse

lemma b_chain_flat
    (words : List Word) (q : ℕ) :
    (words.flatMap conjugateExpansion).count (bChain q) =
      words.count (bChain q) +
        if q = 0 then words.count (FreeMagma.of false) else 0 := by
  induction words with
  | nil => simp
  | cons u words ih =>
      cases q with
      | zero =>
          simp only [List.flatMap_cons, conjugateExpansion,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          simp only [bChain, beq_iff_eq, formal_bracket_word,
            ite_true]
          omega
      | succ q =>
          simp only [List.flatMap_cons, conjugateExpansion,
            List.count_append, List.count_cons, List.count_nil, zero_add]
          rw [ih]
          simp only [if_neg (Nat.succ_ne_zero q), beq_iff_eq,
            formal_b_chain, ↓reduceIte]
          omega

lemma letter_flat_left
    (words : List Word) (x : Bool) :
    (words.flatMap formalConjugateLeft).count (FreeMagma.of x) =
      words.count (FreeMagma.of x) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      simp only [List.flatMap_cons, formalConjugateLeft,
        List.count_append, List.count_cons, List.count_nil, zero_add]
      rw [ih]
      have hne :
          formalBracket u (FreeMagma.of false) ≠ FreeMagma.of x := by
        intro h
        unfold formalBracket at h
        cases h
      simp only [beq_iff_eq, hne, ↓reduceIte]
      omega

lemma count_letter_flat
    (words : List Word) (x : Bool) :
    (words.flatMap conjugateExpansion).count (FreeMagma.of x) =
      words.count (FreeMagma.of x) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      simp only [List.flatMap_cons, conjugateExpansion,
        List.count_append, List.count_cons, List.count_nil, zero_add]
      rw [ih]
      have hne :
          formalBracket u (FreeMagma.of true) ≠ FreeMagma.of x := by
        intro h
        unfold formalBracket at h
        cases h
      simp only [beq_iff_eq, hne, ↓reduceIte]
      omega

theorem b_chain_sided (s q : ℕ) :
    (positiveSidedOrbit s).count (bChain q) =
      Nat.choose s (q + 1) := by
  induction s generalizing q with
  | zero =>
      simp [positiveSidedOrbit]
  | succ s ih =>
      cases q with
      | zero =>
          rw [positiveSidedOrbit, List.count_append,
            count_b_chain, ih 0]
          simp [bChain, basicWord, positiveSidedWord,
            Nat.choose_succ_succ, Nat.add_comm]
      | succ q =>
          rw [positiveSidedOrbit, List.count_append,
            count_b_chain, ih (q + 1)]
          simp only [if_neg (Nat.succ_ne_zero q), Nat.succ_sub_one]
          have hne :
              positiveSidedWord ≠ bChain (q + 1) := by
            intro h
            apply b_chain_ne q
            simpa [positiveSidedWord, basicWord] using h.symm
          simp only [List.count_cons, List.count_nil, beq_iff_eq, hne,
            ↓reduceIte, zero_add]
          rw [Nat.choose_succ_succ]
          rw [ih q]
          simp only [Nat.succ_eq_add_one]
          omega

theorem count_chain_sided (s q : ℕ) :
    (positiveSidedOrbit s).count (aChain q) =
      if q = 0 then s else 0 := by
  induction s generalizing q with
  | zero =>
      simp [positiveSidedOrbit]
  | succ s ih =>
      cases q with
      | zero =>
          rw [positiveSidedOrbit, List.count_append,
            chain_flat_left, ih 0]
          simp [aChain, basicWord, positiveSidedWord]
      | succ q =>
          rw [positiveSidedOrbit, List.count_append,
            chain_flat_left, ih (q + 1)]
          have hne :
              positiveSidedWord ≠ aChain (q + 1) := by
            intro h
            apply chain_succ_ne q
            simpa [positiveSidedWord, basicWord] using h.symm
          simp only [if_neg (Nat.succ_ne_zero q), List.count_cons,
            List.count_nil, beq_iff_eq, hne, ↓reduceIte]

theorem count_letter_sided (s : ℕ) (x : Bool) :
    (positiveSidedOrbit s).count (FreeMagma.of x) = 0 := by
  induction s with
  | zero =>
      simp [positiveSidedOrbit]
  | succ s ih =>
      rw [positiveSidedOrbit, List.count_append,
        letter_flat_left, ih]
      have hne :
          positiveSidedWord ≠ FreeMagma.of x := by
        intro h
        unfold positiveSidedWord formalBracket at h
        cases h
      simp [hne]

theorem letter_sided_word (s r : ℕ) (x : Bool) :
    (twoSidedWord s r).count (FreeMagma.of x) = 0 := by
  induction r with
  | zero =>
      simp [twoSidedWord]
  | succ r ih =>
      rw [twoSidedWord, List.count_append,
        count_letter_sided,
        count_letter_flat, ih]

/-- The raw count underlying the pure `a`-chain exponent singled out after
Struik's equation (34). -/
theorem chain_sided_word (s r q : ℕ) :
    (twoSidedWord s r).count (aChain q) =
      s * Nat.choose r (q + 1) := by
  induction r generalizing q with
  | zero =>
      simp [twoSidedWord]
  | succ r ih =>
      rw [twoSidedWord, List.count_append,
        count_chain_sided,
        count_chain_flat, ih q]
      rw [letter_sided_word]
      cases q with
      | zero =>
          simp [Nat.choose_succ_succ, Nat.mul_add]
      | succ q =>
          simp only [if_neg (Nat.succ_ne_zero q), Nat.succ_sub_one]
          rw [ih q, Nat.choose_succ_succ, Nat.mul_add]
          simp only [Nat.succ_eq_add_one]
          omega

/-- The raw count underlying the pure `b`-chain exponent singled out after
Struik's equation (34). -/
theorem count_b_sided (s r q : ℕ) :
    (twoSidedWord s r).count (bChain q) =
      r * Nat.choose s (q + 1) := by
  induction r with
  | zero =>
      simp [twoSidedWord]
  | succ r ih =>
      rw [twoSidedWord, List.count_append,
        b_chain_sided,
        b_chain_flat, ih]
      rw [letter_sided_word]
      simp [Nat.add_mul, Nat.add_comm]

lemma grid_ne_letter (q t : ℕ) (x : Bool) :
    gridWord q t ≠ FreeMagma.of x := by
  cases t with
  | zero =>
      cases q with
      | zero =>
          intro h
          unfold gridWord bChain basicWord formalBracket at h
          cases h
      | succ q =>
          intro h
          unfold gridWord bChain formalBracket at h
          cases h
  | succ t =>
      intro h
      unfold gridWord formalBracket at h
      cases h

lemma grid_ne_basic (q t : ℕ) :
    gridWord q (t + 1) ≠ basicWord := by
  intro h
  unfold gridWord basicWord formalBracket at h
  injection h with hleft _
  exact grid_ne_letter q t false hleft

lemma formal_bracket_succ (u : Word) (q t : ℕ) :
    formalBracket u (FreeMagma.of true) = gridWord q (t + 1) ↔
      u = gridWord q t := by
  constructor
  · intro h
    unfold gridWord formalBracket at h
    injection h
  · intro h
    rw [h, gridWord]

lemma formal_bracket_grid (u : Word) (q t : ℕ) :
    formalBracket u (FreeMagma.of false) ≠ gridWord q (t + 1) := by
  intro h
  unfold gridWord formalBracket at h
  injection h with _ hright
  have hfalse : false = true := by
    injection hright
  exact Bool.noConfusion hfalse

lemma grid_flat_left
    (words : List Word) (q t : ℕ) :
    (words.flatMap formalConjugateLeft).count
        (gridWord q (t + 1)) =
      words.count (gridWord q (t + 1)) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      simp only [List.flatMap_cons, formalConjugateLeft,
        List.count_append, List.count_cons, List.count_nil, zero_add]
      rw [ih]
      simp only [beq_iff_eq, formal_bracket_grid,
        ↓reduceIte]
      omega

lemma count_grid_flat
    (words : List Word) (q t : ℕ) :
    (words.flatMap conjugateExpansion).count (gridWord q (t + 1)) =
      words.count (gridWord q (t + 1)) +
        words.count (gridWord q t) := by
  induction words with
  | nil => simp
  | cons u words ih =>
      simp only [List.flatMap_cons, conjugateExpansion,
        List.count_append, List.count_cons, List.count_nil, zero_add]
      rw [ih]
      simp only [beq_iff_eq, formal_bracket_succ]
      omega

theorem count_grid_sided
    (s q t : ℕ) :
    (positiveSidedOrbit s).count (gridWord q (t + 1)) = 0 := by
  induction s with
  | zero =>
      simp [positiveSidedOrbit]
  | succ s ih =>
      rw [positiveSidedOrbit, List.count_append,
        grid_flat_left, ih]
      have hne :
          positiveSidedWord ≠ gridWord q (t + 1) := by
        intro h
        apply grid_ne_basic q t
        simpa [positiveSidedWord, basicWord] using h.symm
      simp [hne]

/-- Count one rectangular factor in the raw, uncollected two-sided word.

The formula is useful input to a proof of Struik's Lemma 4, but it is not the
lemma's collected-standard-commutator conclusion. -/
theorem grid_raw_sided (s r q t : ℕ) :
    (twoSidedWord s r).count (gridWord q t) =
      Nat.choose s (q + 1) * Nat.choose r (t + 1) := by
  induction r generalizing t with
  | zero =>
      simp [twoSidedWord]
  | succ r ih =>
      cases t with
      | zero =>
          change (twoSidedWord s (r + 1)).count (bChain q) =
            Nat.choose s (q + 1) * Nat.choose (r + 1) 1
          rw [count_b_sided]
          simp [Nat.choose_one_right, Nat.mul_comm]
      | succ t =>
          rw [twoSidedWord, List.count_append,
            count_grid_sided,
            count_grid_flat, ih (t + 1), ih t,
            zero_add, Nat.choose_succ_succ, Nat.mul_add]
          simp only [Nat.succ_eq_add_one]
          omega

theorem sided_b_chain
    {s : ℕ} {w : Word} (hw : w ∈ positiveSidedOrbit s) :
    ∃ q, w = bChain q := by
  induction s generalizing w with
  | zero =>
      simp [positiveSidedOrbit] at hw
  | succ s ih =>
      simp only [positiveSidedOrbit, List.mem_append,
        List.mem_flatMap, formalConjugateLeft,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ⟨u, hu, rfl | rfl⟩ | rfl
      · exact ih hu
      · obtain ⟨q, rfl⟩ := ih hu
        exact ⟨q + 1, by rw [bChain]⟩
      · exact ⟨0, rfl⟩

/-- Every factor in the raw word underlying Lemma 4 is one of the rectangular
words covered by `grid_raw_sided`. -/
theorem two_sided_grid
    {s r : ℕ} {w : Word} (hw : w ∈ twoSidedWord s r) :
    ∃ q t, w = gridWord q t := by
  induction r generalizing w with
  | zero =>
      simp [twoSidedWord] at hw
  | succ r ih =>
      simp only [twoSidedWord, List.mem_append, List.mem_flatMap,
        conjugateExpansion, List.mem_cons, List.not_mem_nil, or_false]
        at hw
      rcases hw with hw | ⟨u, hu, rfl | rfl⟩
      · obtain ⟨q, rfl⟩ := sided_b_chain hw
        exact ⟨q, 0, rfl⟩
      · exact ih hu
      · obtain ⟨q, t, rfl⟩ := ih hu
        exact ⟨q, t + 1, by rw [gridWord]⟩

/-- Every factor in the raw word has a rectangular binomial count.

Further Hall collection can merge and create standard commutator factors, so
this theorem is only a precursor to Lemma 4's coefficient assertion. -/
theorem raw_binomial_count
    {s r : ℕ} {w : Word} (hw : w ∈ twoSidedWord s r) :
    ∃ q t,
      w = gridWord q t ∧
      (twoSidedWord s r).count w =
        Nat.choose s (q + 1) * Nat.choose r (t + 1) := by
  obtain ⟨q, t, rfl⟩ := two_sided_grid hw
  exact ⟨q, t, rfl, grid_raw_sided s r q t⟩

end Struik
