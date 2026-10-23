import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-!
# The arithmetic of the collision potential

For an epoch not yet signed, the potential
`C/(pD) + V (q' - K)/(NpD) + b Z² (q' - K) + Σ_m (γ z_m² + δ n_m²)`
pays for the signer accepting a cached randomizer whose digest collides (`C` such cached
decodable inputs), and for later queries hitting a cached randomizer the signer accepted (`V`
cached decodable inputs, at most `q' - K` later queries). Here `K` counts the cached encoding
inputs of the epoch, `Z = V - pK` and, for each message `m`, `z_m = v_m - p n_m`. The lemmas
are stated for abstract positive constants `N` (digests and randomizers), `D` (`N` minus the
signing attempts), and balancing constants `M`, `β`.

* `leaf_drift_le`: one fresh query raises the expected potential by at most `rate`.
* `race_le_leaf`: the signer's race bound is at most the potential.
* `rate_le`: for `N = 2^128`, `D = N - 2^32`, `M = 2^70`, `β = 2^78`,
  `rate ≤ (q' - 1 + 2^85)/(ND)`.
-/

namespace Xmss.TargetSum.Direct.CollisionMath

noncomputable section

variable (N D M β p q' : ℝ)

def bCoef : ℝ := 1 / (2 * N * p * D * M)
def γCoef : ℝ := 3 * β / (4 * p * D * (D - q'))
def δCoef : ℝ := 3 / (4 * β * p * D * (D - q'))

/-- The epoch part of the potential, without the per-message terms. -/
def leafMain (K V C : ℝ) : ℝ :=
  C / (p * D) + V * (q' - K) / (N * p * D) + bCoef N D M p * (V - p * K) ^ 2 * (q' - K)

/-- The per-message term of the potential. -/
def msgTerm (n v : ℝ) : ℝ :=
  γCoef D β p q' * (v - p * n) ^ 2 + δCoef D β p q' * n ^ 2

/-- The expected increase of the potential per fresh query. -/
def rate : ℝ :=
  (q' - 1) / (N * D) + M / (2 * N * p * D) + q' / (2 * N * D * M) + γCoef D β p q' * p +
    δCoef D β p q' * (2 * q' + 1)

/-- The standing assumptions on the constants and on `q'`. -/
structure Hypotheses : Prop where
  N_pos : 0 < N
  D_le : D ≤ N
  D_large : 7 * N / 8 ≤ D
  M_pos : 0 < M
  β_pos : 0 < β
  p_pos : 0 < p
  p_le : p ≤ 1
  one_le : 1 ≤ q'
  q_le : q' ≤ N / 2

variable {N D M β p q'}

namespace Hypotheses

variable (h : Hypotheses N D M β p q')
include h

theorem D_pos : 0 < D := by have := h.N_pos; have := h.D_large; linarith

theorem D_sub_pos : 0 < D - q' := by
  have := h.N_pos; have := h.D_large; have := h.q_le; linarith

theorem D_sub_large : 7 * N / 8 - N / 2 ≤ D - q' := by
  have := h.D_large; have := h.q_le; linarith

theorem bCoef_pos : 0 < bCoef N D M p := by
  have := h.N_pos; have := h.D_pos; have := h.M_pos; have := h.p_pos
  unfold bCoef
  positivity

theorem γCoef_nonneg : 0 ≤ γCoef D β p q' := by
  have := h.D_sub_pos; have := h.D_pos; have := h.β_pos; have := h.p_pos
  unfold γCoef
  positivity

theorem δCoef_nonneg : 0 ≤ δCoef D β p q' := by
  have := h.D_sub_pos; have := h.D_pos; have := h.β_pos; have := h.p_pos
  unfold δCoef
  positivity

theorem msgTerm_nonneg (n v : ℝ) : 0 ≤ msgTerm D β p q' n v := by
  have := h.γCoef_nonneg; have := h.δCoef_nonneg
  unfold msgTerm
  positivity

theorem leafMain_nonneg {K V C : ℝ} (hK : K ≤ q') (hV : 0 ≤ V) (hC : 0 ≤ C) :
    0 ≤ leafMain N D M p q' K V C := by
  have := h.N_pos; have := h.D_pos; have := h.bCoef_pos; have := h.p_pos
  have hL : 0 ≤ q' - K := by linarith
  unfold leafMain
  positivity

end Hypotheses

/-- `x / c - b x² ≤ 1 / (4 b c²)` for `b, c > 0`. -/
theorem linear_sub_square_le {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    x / c - b * x ^ 2 ≤ 1 / (4 * b * c ^ 2) := by
  have hkey : 0 ≤ (2 * b * c * x - 1) ^ 2 := sq_nonneg _
  rw [div_sub' (ne_of_gt hc), div_le_div_iff₀ hc (by positivity)]
  nlinarith [hkey, mul_pos hb hc]

/-- One fresh query at the epoch: valid with probability `p`, and then colliding with a cached
decodable input with probability `hit ≤ V/N`, which raises `C` by at most `2`. -/
theorem leaf_drift_le (h : Hypotheses N D M β p q')
    {K V C n v hit : ℝ} (hKq : K + 1 ≤ q') (hnK : n ≤ K) (hn : 0 ≤ n)
    (_hhit : 0 ≤ hit) (hhitV : hit ≤ V / N) :
    hit * (2 / (p * D)) +
        p * (leafMain N D M p q' (K + 1) (V + 1) C + msgTerm D β p q' (n + 1) (v + 1)) +
        (1 - p) * (leafMain N D M p q' (K + 1) V C + msgTerm D β p q' (n + 1) v) ≤
      leafMain N D M p q' K V C + msgTerm D β p q' n v + rate N D M β p q' := by
  have hN := h.N_pos; have hD := h.D_pos; have hM := h.M_pos; have hp := h.p_pos
  have hp1 := h.p_le
  have hb := h.bCoef_pos
  have hγ := h.γCoef_nonneg; have hδ := h.δCoef_nonneg
  have hDq := h.D_sub_pos
  set L := q' - K with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hexpect :
      p * (leafMain N D M p q' (K + 1) (V + 1) C + msgTerm D β p q' (n + 1) (v + 1)) +
          (1 - p) * (leafMain N D M p q' (K + 1) V C + msgTerm D β p q' (n + 1) v) =
        leafMain N D M p q' K V C + msgTerm D β p q' n v +
          ((-V + p * L - p) / (N * p * D) - bCoef N D M p * (V - p * K) ^ 2 +
            bCoef N D M p * p * (1 - p) * (L - 1) + γCoef D β p q' * (p * (1 - p)) +
            δCoef D β p q' * (2 * n + 1)) := by
    unfold leafMain msgTerm
    rw [show q' - (K + 1) = L - 1 by rw [hLdef]; ring]
    have hpD : p * D ≠ 0 := by positivity
    have hNpD : N * p * D ≠ 0 := by positivity
    field_simp
    ring
  have hhitle : hit * (2 / (p * D)) ≤ 2 * V / (N * p * D) := by
    calc
      hit * (2 / (p * D)) ≤ V / N * (2 / (p * D)) :=
        mul_le_mul_of_nonneg_right hhitV (by positivity)
      _ = 2 * V / (N * p * D) := by field_simp
  have hsquare := linear_sub_square_le hb (show 0 < N * p * D by positivity) (V - p * K)
  have hbsq : bCoef N D M p * p * (1 - p) * (L - 1) ≤ q' / (2 * N * D * M) := by
    have h1p : 1 - p ≤ 1 := by linarith
    have hL : L - 1 ≤ q' := by linarith
    calc
      bCoef N D M p * p * (1 - p) * (L - 1) ≤ bCoef N D M p * p * 1 * q' := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1p (by positivity)) hL (by linarith)
          (by positivity)
      _ = q' / (2 * N * D * M) := by
        unfold bCoef
        field_simp
  have hbcoef : 1 / (4 * bCoef N D M p * (N * p * D) ^ 2) = M / (2 * N * p * D) := by
    unfold bCoef
    field_simp
    ring
  have hγterm : γCoef D β p q' * (p * (1 - p)) ≤ γCoef D β p q' * p := by
    apply mul_le_mul_of_nonneg_left _ hγ
    nlinarith
  have hδterm : δCoef D β p q' * (2 * n + 1) ≤ δCoef D β p q' * (2 * q' + 1) := by
    apply mul_le_mul_of_nonneg_left _ hδ
    linarith
  have hmain : (-V + p * L - p) / (N * p * D) + 2 * V / (N * p * D) =
      (V - p * K) / (N * p * D) + (q' - 1) / (N * D) := by
    rw [hLdef]
    field_simp
    ring
  rw [add_assoc, hexpect]
  unfold rate
  rw [← hbcoef]
  linarith [hhitle, hsquare, hbsq, hγterm, hδterm, hmain]

/-- The signer's race bound is at most the epoch potential. Here `s ≤ C` cached decodable
inputs with a partner, `v ≤ V` cached decodable inputs and `n ≤ K` cached inputs for the
requested message, and the weight `w ≤ (q' - K)/N` of a cached input without a partner. -/
theorem race_le_leaf (h : Hypotheses N D M β p q')
    {K V C n v s w : ℝ} (hKq : K ≤ q') (hn : 0 ≤ n) (hnK : n ≤ K) (hs : 0 ≤ s) (hsv : s ≤ v)
    (hsC : s ≤ C) (hvV : v ≤ V) (hw : 0 ≤ w) (hwL : w ≤ (q' - K) / N) :
    (s + w * (v - s)) / (v + p * (D - n)) ≤
      leafMain N D M p q' K V C + msgTerm D β p q' n v := by
  have hN := h.N_pos; have hD := h.D_pos; have hDq := h.D_sub_pos; have hp := h.p_pos
  have hb := h.bCoef_pos
  have hγ := h.γCoef_nonneg; have hδ := h.δCoef_nonneg
  have hq := h.q_le
  have hv : 0 ≤ v := le_trans hs hsv
  have hDn : 0 < D - n := by linarith
  have hden : 0 < v + p * (D - n) := by positivity
  set u := s + w * (v - s) with hudef
  have hL : 0 ≤ q' - K := by linarith
  have hw1 : w ≤ 1 / 2 := by
    refine hwL.trans ?_
    rw [div_le_iff₀ hN]
    nlinarith
  have hu_main : u ≤ C + V * (q' - K) / N := by
    have : w * (v - s) ≤ V * (q' - K) / N := by
      calc
        w * (v - s) ≤ (q' - K) / N * V :=
          mul_le_mul hwL (by linarith) (by linarith) (by positivity)
        _ = V * (q' - K) / N := by ring
    linarith
  have hu_v : u ≤ 3 / 2 * v := by
    have : w * (v - s) ≤ 1 / 2 * v := by nlinarith
    linarith
  have hu0 : 0 ≤ u := by
    have : 0 ≤ w * (v - s) := mul_nonneg hw (by linarith)
    linarith
  have hmainbound : (C + V * (q' - K) / N) / (p * D) ≤ leafMain N D M p q' K V C := by
    unfold leafMain
    have : 0 ≤ bCoef N D M p * (V - p * K) ^ 2 * (q' - K) := by positivity
    have heq : (C + V * (q' - K) / N) / (p * D) =
        C / (p * D) + V * (q' - K) / (N * p * D) := by
      field_simp
    linarith
  by_cases hz : p * n ≤ v
  · have hdenD : p * D ≤ v + p * (D - n) := by nlinarith
    calc
      u / (v + p * (D - n)) ≤ u / (p * D) :=
        div_le_div_of_nonneg_left hu0 (by positivity) hdenD
      _ ≤ (C + V * (q' - K) / N) / (p * D) :=
        div_le_div_of_nonneg_right hu_main (by positivity)
      _ ≤ _ := by
        have := h.msgTerm_nonneg n v
        linarith
  · push Not at hz
    have hzpos : 0 < p * n - v := by linarith
    have hsplit : u / (v + p * (D - n)) =
        u / (p * D) + u * (p * n - v) / (p * D * (v + p * (D - n))) := by
      field_simp
      ring
    have hdeficit : u * (p * n - v) / (p * D * (v + p * (D - n))) ≤
        3 / 2 * n * (p * n - v) / (p * D * (D - q')) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hfirst : u * (p * n - v) ≤ 3 / 2 * (p * n) * (p * n - v) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hzpos.le
      have hsecond : p * (D - q') ≤ v + p * (D - n) := by nlinarith
      have hpos1 : 0 ≤ 3 / 2 * n * (p * n - v) := by positivity
      calc
        u * (p * n - v) * (p * D * (D - q')) ≤
            3 / 2 * (p * n) * (p * n - v) * (p * D * (D - q')) :=
          mul_le_mul_of_nonneg_right hfirst (by positivity)
        _ = 3 / 2 * n * (p * n - v) * (p * D * (p * (D - q'))) := by ring
        _ ≤ 3 / 2 * n * (p * n - v) * (p * D * (v + p * (D - n))) := by
          apply mul_le_mul_of_nonneg_left _ hpos1
          exact mul_le_mul_of_nonneg_left hsecond (by positivity)
    have hamgm : 3 / 2 * n * (p * n - v) / (p * D * (D - q')) ≤ msgTerm D β p q' n v := by
      have hβ := h.β_pos
      have hkey : n * (p * n - v) ≤ (β * (v - p * n) ^ 2 + n ^ 2 / β) / 2 := by
        have : 0 ≤ (β * (p * n - v) - n) ^ 2 / β := by positivity
        have hexp : (β * (p * n - v) - n) ^ 2 / β =
            β * (v - p * n) ^ 2 + n ^ 2 / β - 2 * (n * (p * n - v)) := by
          field_simp
          ring
        linarith
      have hc : 0 < p * D * (D - q') := by positivity
      unfold msgTerm γCoef δCoef
      calc
        3 / 2 * n * (p * n - v) / (p * D * (D - q')) =
            3 / 2 * (n * (p * n - v)) / (p * D * (D - q')) := by ring
        _ ≤ 3 / 2 * ((β * (v - p * n) ^ 2 + n ^ 2 / β) / 2) / (p * D * (D - q')) := by
          apply div_le_div_of_nonneg_right _ hc.le
          linarith
        _ = _ := by
          field_simp
          ring
    calc
      u / (v + p * (D - n)) = u / (p * D) + u * (p * n - v) / (p * D * (v + p * (D - n))) :=
        hsplit
      _ ≤ (C + V * (q' - K) / N) / (p * D) + msgTerm D β p q' n v := by
        apply add_le_add (div_le_div_of_nonneg_right hu_main (by positivity))
        exact hdeficit.trans hamgm
      _ ≤ _ := by linarith

/-- For `N = 2^128`, `D ≥ 7N/8`, `M = 2^70`, `β = 2^78` and `p ≥ 2^-15`, the rate is at most
`(q' - 1 + 2^85)/(ND)`. -/
theorem rate_le (h : Hypotheses N D M β p q') (hNval : N = 2 ^ 128) (hMval : M = 2 ^ 70)
    (hβval : β = 2 ^ 78) (hp : 1 / 2 ^ 15 ≤ p) :
    rate N D M β p q' ≤ (q' - 1 + 2 ^ 85) / (N * D) := by
  have hN := h.N_pos; have hD := h.D_pos; have hM := h.M_pos; have hβ := h.β_pos
  have hp0 := h.p_pos
  have hDq := h.D_sub_pos
  have hDq' : 7 * N / 8 - N / 2 ≤ D - q' := h.D_sub_large
  have hq := h.q_le
  have hND : 0 < N * D := by positivity
  have h2 : M / (2 * N * p * D) ≤ 2 ^ 84 / (N * D) := by
    rw [div_le_div_iff₀ (by positivity) hND]
    have : M ≤ 2 ^ 85 * p := by
      rw [hMval]
      calc
        (2 : ℝ) ^ 70 = 2 ^ 85 * (1 / 2 ^ 15) := by norm_num
        _ ≤ 2 ^ 85 * p := mul_le_mul_of_nonneg_left hp (by positivity)
    have hpos : 0 < N * D := hND
    nlinarith
  have h3 : q' / (2 * N * D * M) ≤ 2 ^ 56 / (N * D) := by
    rw [div_le_div_iff₀ (by positivity) hND]
    have : q' ≤ 2 ^ 57 * M := by
      rw [hMval]
      rw [hNval] at hq
      norm_num at hq ⊢
      linarith
    have hpos : 0 < N * D := hND
    nlinarith
  have h4 : γCoef D β p q' * p ≤ 2 ^ 79 / (N * D) := by
    unfold γCoef
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hND]
    have hkey : 3 * β * N ≤ 2 ^ 79 * (4 * (D - q')) := by
      rw [hβval]
      linarith
    have hpD : 0 < p * D := by positivity
    nlinarith
  have h5 : δCoef D β p q' * (2 * q' + 1) ≤ 2 ^ 67 / (N * D) := by
    unfold δCoef
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hND]
    have hpβ : 2 ^ 63 ≤ β * p := by
      rw [hβval]
      calc
        (2 : ℝ) ^ 63 = 2 ^ 78 * (1 / 2 ^ 15) := by norm_num
        _ ≤ 2 ^ 78 * p := mul_le_mul_of_nonneg_left hp (by positivity)
    have hq2 : 2 * q' + 1 ≤ 2 * N := by
      have hone : (1 : ℝ) ≤ N := by rw [hNval]; norm_num
      linarith
    have hlhs : 3 * (2 * q' + 1) * (N * D) ≤ 3 * (2 * N) * (N * D) := by
      nlinarith
    have hrhs : 3 * (2 * N) * (N * D) ≤ 2 ^ 67 * (4 * β * p * D * (D - q')) := by
      have hb : 2 ^ 67 * (4 * (2 ^ 63) * D * (7 * N / 8 - N / 2)) ≤
          2 ^ 67 * (4 * (β * p) * D * (D - q')) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpβ (by norm_num)) hD.le) hDq' (by nlinarith)
          (by positivity)
      have heq : 2 ^ 67 * (4 * (β * p) * D * (D - q')) =
          2 ^ 67 * (4 * β * p * D * (D - q')) := by ring
      rw [← heq]
      refine le_trans (le_of_eq ?_) hb
      rw [hNval]
      ring
    linarith
  unfold rate
  have hsum : (q' - 1) / (N * D) + 2 ^ 84 / (N * D) + 2 ^ 56 / (N * D) + 2 ^ 79 / (N * D) +
      2 ^ 67 / (N * D) ≤ (q' - 1 + 2 ^ 85) / (N * D) := by
    rw [← add_div, ← add_div, ← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hND.le
    norm_num
    linarith
  linarith

end

end Xmss.TargetSum.Direct.CollisionMath
