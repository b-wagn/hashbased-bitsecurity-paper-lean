import XmssSecurity.Proof.TargetSum.Attack.NeighborAccounting
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The neighboring-encoding adversary requests one message and forges a different
one. Its counted standard and strong games are identical, so its concrete attack
against 128 bits also establishes the standard-unforgeability upper bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Attack

open SUFCMA

theorem neighbor_request_fresh (answer : Option Generic.Signature) (signature : Generic.Signature) :
    ¬ EUFCMA.SigningTranscript.ContainsRequest [⟨neighborRequest, answer⟩]
      (neighborForgery signature) := by
  simp only [EUFCMA.SigningTranscript.ContainsRequest, List.mem_singleton, exists_eq_left]
  intro heq
  exact neighborMessage_ne_request
    (congrArg (fun request : SignRequest => request.message) heq).symm

theorem neighbor_euf_gameCounted_eq_strong :
    EUFCMA.gameCounted CountingMode.everything (RandomOracleModel.hashCost HashInput Digest)
      Generic.xmss neighborSufCmaAdversary =
    SUFCMA.gameCounted CountingMode.everything (RandomOracleModel.hashCost HashInput Digest)
      Generic.xmss neighborSufCmaAdversary := by
  rw [neighbor_gameCounted_everything]
  unfold EUFCMA.gameCounted
  simp only [CountingMode.everything, costIf, if_true, Modes.charge_hashCost_eq_countHashQueries]
  have hmain := fun (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) =>
    neighborMain_counted Generic.xmss secretKey publicKey
  simp only [neighborSufCmaAdversary, hmain, bind_assoc, pure_bind, neighbor_request_fresh, not_false_eq_true,
    show ∀ answer : Option Generic.Signature, SigningTranscript.Valid [⟨neighborRequest, answer⟩] from
      fun _ => by simp [SUFCMA.SigningTranscript.Valid], and_true, decide_true, Bool.true_and]
  rfl

theorem neighbor_euf_everything_advantage :
    (EUFCMA.notion CountingMode.everything).advantage Generic.xmss neighborSufCmaAdversary =
      forgeAdvantage Seeded.scheme neighborAdversary := by
  rw [← neighbor_everything_advantage]
  simp only [SecurityNotion.advantage, EUFCMA.notion, SUFCMA.notion]
  rw [neighbor_euf_gameCounted_eq_strong]

theorem neighbor_euf_everything_queryBound :
    (EUFCMA.notion CountingMode.everything).HasQueryBound Generic.xmss neighborSufCmaAdversary
      neighborEverythingBudget :=
  (EUFCMA.hasQueryBound_iff_strong _ _ _ _).2 neighbor_everything_queryBound

theorem neighbor_euf_everything_attack :
    ¬ (EUFCMA.notion CountingMode.everything).HasClassicalSecurityBits Generic.xmss 128 := by
  intro hsecure
  have hbound := hsecure neighborEverythingBudget (by norm_num [neighborEverythingBudget])
    neighborSufCmaAdversary neighbor_euf_everything_queryBound
  rw [neighbor_euf_everything_advantage, neighborEverythingBudget_ratio] at hbound
  exact (not_lt_of_ge hbound) neighbor_seeded_advantage_exceeds_five_sixtyfourths

/-- info: 'XmssSecurity.TargetSum.Attack.neighbor_euf_everything_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_euf_everything_attack

end XmssSecurity.TargetSum.Attack
