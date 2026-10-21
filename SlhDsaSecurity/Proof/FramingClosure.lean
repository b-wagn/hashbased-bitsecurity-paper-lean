import SlhDsaSecurity.Statement.Hashing

/-!
Pure byte-framing closure and finite families of framed inputs. These lemmas
concern only `Message.frame`, list concatenation, and lengths.
-/

namespace SlhDsaSecurity.FramingClosure

/-- Every sufficiently long byte string beginning with zero is a pure frame. -/
theorem exists_frame_of_head_zero (framed : Bytes)
    (hlength : 257 ≤ framed.length) (hhead : framed.head? = some 0) :
    ∃ request : Message, request.frame = some framed := by
  cases framed with
  | nil => simp at hlength
  | cons first rest =>
    cases rest with
    | nil => simp at hlength
    | cons tag payload =>
      have hfirst : first = 0 := Option.some.inj hhead
      subst first
      have htag : tag.toNat ≤ 255 := by have := tag.toNat_lt; omega
      have hpayload : tag.toNat ≤ payload.length := by
        simp only [List.length_cons] at hlength
        omega
      refine ⟨⟨payload.drop tag.toNat, payload.take tag.toNat⟩, ?_⟩
      simp only [Message.frame, List.length_take, Nat.min_eq_left hpayload,
        htag, ↓reduceIte, UInt8.ofNat_toNat]
      simp

@[simp] theorem digest_bytes_length (root : Digest) : (bytesBE n root).length = 16 := by
  simp [bytesBE, n]

/-- The leading serialized byte is the most significant eight-bit slice. -/
theorem digest_head_zero (root : Digest) (hzero : root.extractLsb' 120 8 = 0) :
    (bytesBE n root).head? = some 0 := by
  unfold bytesBE
  change (List.ofFn (fun i : Fin (15 + 1) =>
    UInt8.ofBitVec (root.extractLsb' (8 * i.val) 8))).reverse.head? = _
  rw [List.ofFn_succ_last]
  simpa using congrArg (fun value : BitVec 8 => some (UInt8.ofBitVec value)) hzero

/-- A zero-leading digest preserves representability of every sufficiently long suffix. -/
theorem prepend_digest_exists_frame (root : Digest) (base : Bytes)
    (hzero : root.extractLsb' 120 8 = 0) (hlength : 257 ≤ base.length) :
    ∃ request : Message, request.frame = some (bytesBE n root ++ base) := by
  apply exists_frame_of_head_zero
  · simp only [List.length_append, digest_bytes_length]
    omega
  · rw [List.head?_append, digest_head_zero root hzero]
    rfl

/-- Repeatedly prepend the same standard sixteen-byte digest. -/
def chainFrame (root : Digest) (base : Bytes) : Nat → Bytes
  | 0 => base
  | step + 1 => bytesBE n root ++ chainFrame root base step

@[simp] theorem chainFrame_length (root : Digest) (base : Bytes) (step : Nat) :
    (chainFrame root base step).length = base.length + 16 * step := by
  induction step with
  | zero => simp [chainFrame]
  | succ step ih => simp [chainFrame, ih]; omega

/-- All members of a chain remain frames once its base is a sufficiently long frame. -/
theorem chainFrame_exists_frame (root : Digest) (base : Bytes)
    (hzero : root.extractLsb' 120 8 = 0) (hlength : 257 ≤ base.length)
    (hbase : ∃ request : Message, request.frame = some base) (step : Nat) :
    ∃ request : Message, request.frame = some (chainFrame root base step) := by
  cases step with
  | zero => exact hbase
  | succ step =>
    apply prepend_digest_exists_frame root (chainFrame root base step) hzero
    rw [chainFrame_length]
    omega

/-- A sixty-four-member chain from a 1024-byte base has lengths from 1024 through 2032. -/
theorem chainFrame_length_bounds (root : Digest) (base : Bytes)
    (hbase : base.length = 1024) (step : Fin 64) :
    1024 ≤ (chainFrame root base step.val).length ∧
      (chainFrame root base step.val).length ≤ 2032 := by
  rw [chainFrame_length, hbase]
  have := step.isLt
  omega

/-- A common prefix can be cancelled at any fixed chain position. -/
theorem chainFrame_injective (root : Digest) (step : Nat) :
    Function.Injective (fun base => chainFrame root base step) := by
  induction step with
  | zero => intro left right h; exact h
  | succ step ih =>
    intro left right h
    exact ih (List.append_cancel_left h)

/-- For equally long bases, equality identifies both the position and the base. -/
theorem chainFrame_eq_iff (root : Digest) {left right : Bytes} {i j : Nat}
    (hlength : left.length = right.length) :
    chainFrame root left i = chainFrame root right j ↔ i = j ∧ left = right := by
  constructor
  · intro h
    have hsize := congrArg List.length h
    rw [chainFrame_length, chainFrame_length, hlength] at hsize
    have hij : i = j := by omega
    subst j
    exact ⟨rfl, chainFrame_injective root i h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Distinct 1024-byte bases give disjoint sixty-four-member chains. -/
theorem chainFrame_family_injective {α : Type*} (root : Digest) (bases : α → Bytes)
    (hinjective : Function.Injective bases) (hsize : ∀ index, (bases index).length = 1024) :
    Function.Injective (fun index : α × Fin 64 =>
      chainFrame root (bases index.1) index.2.val) := by
  intro left right h
  obtain ⟨hposition, hbase⟩ := (chainFrame_eq_iff root
    ((hsize left.1).trans (hsize right.1).symm)).1 h
  exact Prod.ext (hinjective hbase) (Fin.ext hposition)

end SlhDsaSecurity.FramingClosure
