import SlhDsaSecurity.Proof.KeygenUniform

/-! Pure-message framing restricts the remaining message/randomizer input overlap. -/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FramingOverlap

def firstByte (root : Digest) : BitVec 8 := root.extractLsb' 120 8

theorem bytesBE_head (root : Digest) :
    (bytesBE n root).head? = some (UInt8.ofBitVec (firstByte root)) := by
  unfold bytesBE
  change (List.ofFn (fun i : Fin (15 + 1) =>
    UInt8.ofBitVec (root.extractLsb' (8 * i.val) 8))).reverse.head? = _
  rw [List.ofFn_succ_last]
  simp [firstByte]

theorem frame_head {request : Message} {framed : Bytes}
    (hframe : request.frame = some framed) : framed.head? = some 0 := by
  unfold Message.frame at hframe
  split at hframe
  · obtain rfl := Option.some.inj hframe
    rfl
  · cases hframe

/-- An actual framed PRF-message can overlap H_msg only if the public root starts with zero. -/
theorem overlap_requires_zero {randomizer prf : Digest} {pk : PublicKey}
    {message framed : Bytes} {request : Message}
    (hframe : request.frame = some framed)
    (hoverlap : Hashing.messageInput randomizer pk message =
      Hashing.randomizerInput prf pk.seed framed) :
    randomizer = prf ∧ firstByte pk.root = 0 := by
  have heq : bytesBE n randomizer ++
      (bytesBE n pk.seed ++ (bytesBE n pk.root ++ message)) =
      bytesBE n prf ++ (bytesBE n pk.seed ++ framed) := by
    simpa only [Hashing.messageInput, Hashing.randomizerInput, List.append_assoc] using hoverlap
  obtain ⟨hrandomizer, hrest⟩ := List.append_inj heq (by simp)
  have hmessage := List.append_cancel_left hrest
  refine ⟨bytesBE_injective n hrandomizer, ?_⟩
  have hhead := frame_head hframe
  rw [← hmessage, List.head?_append, bytesBE_head] at hhead
  have hbyte : UInt8.ofBitVec (firstByte pk.root) = 0 := Option.some.inj hhead
  exact congrArg UInt8.toBitVec hbyte

def splitRoot (root : Digest) : BitVec 8 × BitVec 120 :=
  (firstByte root, root.extractLsb' 0 120)

theorem splitRoot_bijective : Function.Bijective splitRoot := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro left right h
    have hl : firstByte left ++ left.extractLsb' 0 120 = left :=
      BitVec.extractLsb'_append_extractLsb'
    have hr : firstByte right ++ right.extractLsb' 0 120 = right :=
      BitVec.extractLsb'_append_extractLsb'
    rw [← hl, ← hr]
    exact congrArg₂ HAppend.hAppend (congrArg Prod.fst h) (congrArg Prod.snd h)
  · norm_num [Digest, n, Fintype.card_prod, card_bitVec]

theorem firstByte_uniform :
    𝒟[firstByte <$> ($ᵗ Digest : ProbComp Digest)] =
      𝒟[($ᵗ (BitVec 8) : ProbComp (BitVec 8))] := by
  have hmap : firstByte <$> ($ᵗ Digest : ProbComp Digest) =
      Prod.fst <$> (splitRoot <$> ($ᵗ Digest : ProbComp Digest)) := by
    simp [Functor.map_map, splitRoot]
  have hsplit := evalDist_map_bijective_uniform_cross (α := Digest)
    (β := BitVec 8 × BitVec 120) splitRoot splitRoot_bijective
  rw [hmap, evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

theorem uniform_zero_probability :
    Pr[fun root => firstByte root = 0 | ($ᵗ Digest : ProbComp Digest)] = 1 / 256 := by
  rw [show (fun root => firstByte root = 0) = (fun byte => byte = 0) ∘ firstByte from rfl,
    ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) firstByte_uniform,
    probEvent_eq_eq_probOutput, probOutput_uniformSample]
  norm_num [card_bitVec]

/-- The framing restriction has probability exactly 1/256 under actual key generation. -/
theorem keygen_zero_probability :
    Pr[fun keys : SecretKey × PublicKey => firstByte keys.2.root = 0 |
      XmssSecurity.RandomOracleModel.run
        (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey))] = 1 / 256 := by
  rw [show (fun keys : SecretKey × PublicKey => firstByte keys.2.root = 0) =
    (fun pair : Digest × Digest => firstByte pair.2 = 0) ∘ KeygenUniform.publicPair from rfl,
    ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) KeygenUniform.publicPair_uniform]
  rw [show (fun pair : Digest × Digest => firstByte pair.2 = 0) =
    (fun root => firstByte root = 0) ∘ Prod.snd from rfl, ← probEvent_map]
  have hsnd : 𝒟[Prod.snd <$> ($ᵗ (Digest × Digest) : ProbComp (Digest × Digest))] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
    have hswap := evalDist_map_bijective_uniform_cross (α := Digest × Digest)
      (β := Digest × Digest) (Equiv.prodComm Digest Digest)
        (Equiv.prodComm Digest Digest).bijective
    have hmap : Prod.snd <$> ($ᵗ (Digest × Digest) : ProbComp (Digest × Digest)) =
        Prod.fst <$> ((Equiv.prodComm Digest Digest) <$> ($ᵗ (Digest × Digest))) := by
      simp [Functor.map_map]
    rw [hmap, evalDist_map, hswap, ← evalDist_map]
    exact evalDist_map_fst_uniformSample_prod
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hsnd]
  exact uniform_zero_probability

end SlhDsaSecurity.FramingOverlap
