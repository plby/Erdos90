import Towers.Group.Zassenhaus.CoordinateStratumScheduling
import Towers.Group.Zassenhaus.TruncatedConcretePackets

/-!
# Supported correction-packet factories for symbolic Hall powers

The group-theoretic input to one symbolic Hall-power stratum is a supply of
truncated correction packets for supported adjacent factors.  Once such a
packet is supplied, the next-stratum semantic normalizer replaces its strictly
higher correction list by a normalized coordinate endpoint.

This file isolates that packet-supply obligation and constructs it in the
class-two terminal region.  It also packages the normalized adjacent rewrite
made available by any supported packet factory.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A supply of physically truncated correction packets for pairs supported in
one ordinary Hall-weight stratum.
-/
structure TSFtrya
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (lowerWeight : ℕ) where
  packet :
    ∀ (B A : SPFactora H inputWeight),
      lowerWeight ≤ B.word.weight PEAddres.weight →
      lowerWeight ≤ A.word.weight PEAddres.weight →
        TCPkt n B A

namespace TSFtrya

/--
Any explicit packet constructor for supported pairs supplies a supported
packet factory.
-/
def ofPacket
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (packet :
      ∀ (B A : SPFactora H inputWeight),
        lowerWeight ≤ B.word.weight PEAddres.weight →
        lowerWeight ≤ A.word.weight PEAddres.weight →
          TCPkt n B A) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  packet := packet

/--
If three times the active stratum reaches the cutoff, every supported pair has
the automatic class-two empty-or-singleton correction packet.
-/
def of_classTwo
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hterminal : n ≤ 3 * lowerWeight) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  packet B A hB hA :=
    TCPkt.n_min_weight
      B A (by
        have hlowerMin :
            lowerWeight ≤
              min
                (B.word.weight PEAddres.weight)
                (A.word.weight PEAddres.weight) :=
          Nat.le_min.mpr ⟨hB, hA⟩
        omega)

/--
A supported packet factory and a next-stratum normalizer produce one
normalized adjacent semantic obstruction.
-/
lemma supported_semantic_step
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight) :
    ∃ normalization :
        TSNorma
          lowerWeight (factory.packet B A hB hA),
      SSStep
        (n := n) H inputWeight lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) :=
  (factory.packet B A hB hA).supported_semantic_left
    P S B A hB normalizer

/--
The normalized adjacent obstruction supplied by a packet factory is also a
finite semantic rewrite run.
-/
lemma supported_semantic_rewrites
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight) :
    ∃ normalization :
        TSNorma
          lowerWeight (factory.packet B A hB hA),
      SCRw
        (n := n) (lowerWeight := lowerWeight)
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) := by
  rcases factory.supported_semantic_step normalizer P S B A hB hA with
    ⟨normalization, hstep⟩
  exact
    ⟨normalization,
      SCRw.single
        hstep⟩

end TSFtrya

end TCTex
end Towers
