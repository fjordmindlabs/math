/-
Erdős #647 modular sieve (rungs 1+2), kernel-clean.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).
-/
import Mathlib

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Modular reduction for Erdős problem 647: `2520 ∣ n`, kernel-clean

A *candidate* is `n` with `∀ m < n, m + τ(m) ≤ n + 2` (universally quantified
form of the inner predicate of the formal-conjectures statement of Erdős 647).
This file proves, with no `native_decide` and no extra axioms, that every
candidate `n > 1800` is divisible by `2520 = 2³·3²·5·7` (Hughes's reduction,
first rung; cf. arXiv:2608.17880 §future work).

Method (divisor budgets): a candidate has `τ(n - k) ≤ k + 2` for `1 ≤ k ≤ n`.
The engine is `two_mul_tau_le`: if `m = d * t` with `t > d` then
`τ(m) ≥ 2·τ(d)`, because `divisors d` and `t · divisors d` are disjoint sets
of divisors of `m`. Choosing, for each nonzero residue of `n` modulo a prime
power, a shift `k ≤ 6` where the known divisibilities stack into a `d` with
`2·τ(d) > k + 2` yields a contradiction in every case.
-/

namespace Erdos647Mod

open ArithmeticFunction

/-- The candidate predicate for Erdős 647. -/
def Cand (n : ℕ) : Prop := ∀ m < n, m + (ArithmeticFunction.sigma 0) m ≤ n + 2

/-- Budget extraction: a candidate bounds the divisor count at each shift. -/
lemma cand_budget {n : ℕ} (H : Cand n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (ArithmeticFunction.sigma 0) (n - k) ≤ k + 2 := by
  have h := H (n - k) (by omega)
  omega

/-- **Doubling engine.** If `m = d * t` with `d < t`, then `τ(m) ≥ 2 τ(d)`:
the divisors of `d` and their `t`-multiples are `2 τ(d)` distinct divisors. -/
lemma two_mul_tau_le (d t : ℕ) (hd : 0 < d) (ht : d < t) :
    2 * (ArithmeticFunction.sigma 0) d ≤ (ArithmeticFunction.sigma 0) (d * t) := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
  have ht0 : 0 < t := lt_trans hd ht
  have hdt : d * t ≠ 0 := by positivity
  have hsub : d.divisors ∪ d.divisors.image (t * ·) ⊆ (d * t).divisors := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hdt⟩
    rcases hx with hx | hx
    · exact dvd_mul_of_dvd_left (Nat.mem_divisors.mp hx).1 t
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have : t * y ∣ t * d := mul_dvd_mul_left t (Nat.mem_divisors.mp hy).1
      rwa [mul_comm d t]
  have hdisj : Disjoint d.divisors (d.divisors.image (t * ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ d := Nat.le_of_dvd hd (Nat.mem_divisors.mp hx).1
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    have h2 : 0 < y := Nat.pos_of_mem_divisors hy
    have : t ≤ t * y := Nat.le_mul_of_pos_right t h2
    omega
  have hinj : (d.divisors.image (t * ·)).card = d.divisors.card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ (by omega))
  calc 2 * d.divisors.card
      = d.divisors.card + (d.divisors.image (t * ·)).card := by omega
    _ = (d.divisors ∪ d.divisors.image (t * ·)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (d * t).divisors.card := Finset.card_le_card hsub

/-- One contradiction step: if `d ∣ n - k`, `n - k > d²`, and `2 τ(d) > k + 2`,
then `n` is not a candidate. Stated as deriving `False` from the budget. -/
lemma rung {n k d : ℕ} (H : Cand n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hd : 0 < d) (hdvd : n - k = d * ((n - k) / d)) (hbig : d < (n - k) / d)
    (hτ : k + 2 < 2 * (ArithmeticFunction.sigma 0) d) : False := by
  have h2 := two_mul_tau_le d ((n - k) / d) hd hbig
  rw [← hdvd] at h2
  have hb := cand_budget H hk1 hkn
  omega

/-- Every candidate `n > 1800` is divisible by 8. -/
theorem eight_dvd {n : ℕ} (hn : 1800 < n) (H : Cand n) : 8 ∣ n := by
  have hτ4 : (ArithmeticFunction.sigma 0) 4 = 3 := by decide
  have hτ8 : (ArithmeticFunction.sigma 0) 8 = 4 := by decide
  have hr : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 8
  · omega
  · exfalso
    exact rung H (k := 1) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 8) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 1) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 4) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- Every candidate `n > 1800` is divisible by 3 (uses `8 ∣ n`). -/
theorem three_dvd {n : ℕ} (hn : 1800 < n) (H : Cand n) (h8 : 8 ∣ n) : 3 ∣ n := by
  have hτ6 : (ArithmeticFunction.sigma 0) 6 = 4 := by decide
  have hτ12 : (ArithmeticFunction.sigma 0) 12 = 6 := by decide
  have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 3
  · omega
  · -- n ≡ 1 (mod 3): k = 4, d = 12
    exfalso
    exact rung H (k := 4) (d := 12) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · -- n ≡ 2 (mod 3): k = 2, d = 6
    exfalso
    exact rung H (k := 2) (d := 6) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- Every candidate `n > 1800` is divisible by 9 (uses `8 ∣ n`, `3 ∣ n`). -/
theorem nine_dvd {n : ℕ} (hn : 1800 < n) (H : Cand n) (h8 : 8 ∣ n) (h3 : 3 ∣ n) :
    9 ∣ n := by
  have hτ9 : (ArithmeticFunction.sigma 0) 9 = 3 := by decide
  have hτ18 : (ArithmeticFunction.sigma 0) 18 = 6 := by decide
  have hr : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 9
  · omega
  · omega
  · omega
  · -- n ≡ 3 (mod 9): k = 3, d = 9
    exfalso
    exact rung H (k := 3) (d := 9) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · omega
  · -- n ≡ 6 (mod 9): k = 6, d = 18
    exfalso
    exact rung H (k := 6) (d := 18) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · omega

/-- Every candidate `n > 1800` is divisible by 5 (uses `8 ∣ n`, `3 ∣ n`). -/
theorem five_dvd {n : ℕ} (hn : 1800 < n) (H : Cand n) (h8 : 8 ∣ n) (h3 : 3 ∣ n) :
    5 ∣ n := by
  have hτ5 : (ArithmeticFunction.sigma 0) 5 = 2 := by decide
  have hτ10 : (ArithmeticFunction.sigma 0) 10 = 4 := by decide
  have hτ15 : (ArithmeticFunction.sigma 0) 15 = 4 := by decide
  have hτ20 : (ArithmeticFunction.sigma 0) 20 = 6 := by decide
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5
  · omega
  · exfalso
    exact rung H (k := 1) (d := 5) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 10) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 15) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 20) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- Every candidate `n > 1800` is divisible by 7 (uses `8 ∣ n`, `3 ∣ n`, `5 ∣ n`). -/
theorem seven_dvd {n : ℕ} (hn : 1800 < n) (H : Cand n) (h8 : 8 ∣ n) (h3 : 3 ∣ n)
    (h5 : 5 ∣ n) : 7 ∣ n := by
  have hτ7 : (ArithmeticFunction.sigma 0) 7 = 2 := by decide
  have hτ14 : (ArithmeticFunction.sigma 0) 14 = 4 := by decide
  have hτ21 : (ArithmeticFunction.sigma 0) 21 = 4 := by decide
  have hτ28 : (ArithmeticFunction.sigma 0) 28 = 6 := by decide
  have hτ35 : (ArithmeticFunction.sigma 0) 35 = 4 := by decide
  have hτ42 : (ArithmeticFunction.sigma 0) 42 = 8 := by decide
  have hr : n % 7 < 7 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 7
  · omega
  · exfalso
    exact rung H (k := 1) (d := 7) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 14) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 21) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 28) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 5) (d := 35) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 6) (d := 42) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- **Main theorem.** Every Erdős-647 candidate `n > 1800` satisfies `2520 ∣ n`. -/
theorem mod2520_of_cand {n : ℕ} (hn : 1800 < n) (H : Cand n) : 2520 ∣ n := by
  have h8 := eight_dvd hn H
  have h3 := three_dvd hn H h8
  have h9 := nine_dvd hn H h8 h3
  have h5 := five_dvd hn H h8 h3
  have h7 := seven_dvd hn H h8 h3 h5
  omega

/-! ## Rung 2a: full elimination mod 11 and mod 13 (given `2520 ∣ n`) -/

theorem eleven_dvd {n : ℕ} (hn : 100000 < n) (H : Cand n) (h2520 : 2520 ∣ n) :
    11 ∣ n := by
  have ht11 : (ArithmeticFunction.sigma 0) 11 = 2 := by decide
  have ht22 : (ArithmeticFunction.sigma 0) 22 = 4 := by decide
  have ht33 : (ArithmeticFunction.sigma 0) 33 = 4 := by decide
  have ht44 : (ArithmeticFunction.sigma 0) 44 = 6 := by decide
  have ht55 : (ArithmeticFunction.sigma 0) 55 = 4 := by decide
  have ht66 : (ArithmeticFunction.sigma 0) 66 = 8 := by decide
  have ht88 : (ArithmeticFunction.sigma 0) 88 = 8 := by decide
  have ht99 : (ArithmeticFunction.sigma 0) 99 = 6 := by decide
  have ht110 : (ArithmeticFunction.sigma 0) 110 = 8 := by decide
  have ht198 : (ArithmeticFunction.sigma 0) 198 = 12 := by decide
  have hr : n % 11 < 11 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 11
  · omega
  · exfalso
    exact rung H (k := 1) (d := 11) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 22) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 33) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 44) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 5) (d := 55) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 6) (d := 66) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 18) (d := 198) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 8) (d := 88) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 9) (d := 99) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 10) (d := 110) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

theorem thirteen_dvd {n : ℕ} (hn : 100000 < n) (H : Cand n) (h2520 : 2520 ∣ n) :
    13 ∣ n := by
  have ht13 : (ArithmeticFunction.sigma 0) 13 = 2 := by decide
  have ht26 : (ArithmeticFunction.sigma 0) 26 = 4 := by decide
  have ht39 : (ArithmeticFunction.sigma 0) 39 = 4 := by decide
  have ht52 : (ArithmeticFunction.sigma 0) 52 = 6 := by decide
  have ht65 : (ArithmeticFunction.sigma 0) 65 = 4 := by decide
  have ht78 : (ArithmeticFunction.sigma 0) 78 = 8 := by decide
  have ht104 : (ArithmeticFunction.sigma 0) 104 = 8 := by decide
  have ht117 : (ArithmeticFunction.sigma 0) 117 = 6 := by decide
  have ht130 : (ArithmeticFunction.sigma 0) 130 = 8 := by decide
  have ht156 : (ArithmeticFunction.sigma 0) 156 = 12 := by decide
  have ht260 : (ArithmeticFunction.sigma 0) 260 = 12 := by decide
  have ht312 : (ArithmeticFunction.sigma 0) 312 = 16 := by decide
  have hr : n % 13 < 13 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 13
  · omega
  · exfalso
    exact rung H (k := 1) (d := 13) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 26) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 39) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 52) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 5) (d := 65) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 6) (d := 78) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 20) (d := 260) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 8) (d := 104) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 9) (d := 117) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 10) (d := 130) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 24) (d := 312) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 12) (d := 156) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- **Rung 2a headline.** Every candidate `n > 100000` satisfies `360360 ∣ n`
(`360360 = 2520 · 11 · 13`). -/
theorem mod360360_of_cand {n : ℕ} (hn : 100000 < n) (H : Cand n) : 360360 ∣ n := by
  have h2520 := mod2520_of_cand (by omega) H
  have h11 := eleven_dvd hn H h2520
  have h13 := thirteen_dvd hn H h2520
  omega

/-! ## Rung 2b: residue sieve mod 17 and mod 19 (given `360360 ∣ n`) -/

theorem mod17_cases {n : ℕ} (hn : 250000000 < n) (H : Cand n) (hL : 360360 ∣ n) :
    n % 17 = 0 ∨ n % 17 = 11 ∨ n % 17 = 13 ∨ n % 17 = 14 ∨ n % 17 = 15 ∨ n % 17 = 16 := by
  have ht17 : (ArithmeticFunction.sigma 0) 17 = 2 := by decide
  have ht34 : (ArithmeticFunction.sigma 0) 34 = 4 := by decide
  have ht51 : (ArithmeticFunction.sigma 0) 51 = 4 := by decide
  have ht68 : (ArithmeticFunction.sigma 0) 68 = 6 := by decide
  have ht85 : (ArithmeticFunction.sigma 0) 85 = 4 := by decide
  have ht102 : (ArithmeticFunction.sigma 0) 102 = 8 := by decide
  have ht136 : (ArithmeticFunction.sigma 0) 136 = 8 := by decide
  have ht153 : (ArithmeticFunction.sigma 0) 153 = 6 := by decide
  have ht170 : (ArithmeticFunction.sigma 0) 170 = 8 := by decide
  have ht204 : (ArithmeticFunction.sigma 0) 204 = 12 := by decide
  have ht408 : (ArithmeticFunction.sigma 0) 408 = 16 := by decide
  have h2520 : n % 2520 = 0 := by omega
  clear hL
  have hr : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 17
  · omega
  · exfalso
    exact rung H (k := 1) (d := 17) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 34) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 51) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 68) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 5) (d := 85) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 6) (d := 102) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 24) (d := 408) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 8) (d := 136) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 9) (d := 153) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 10) (d := 170) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · exfalso
    exact rung H (k := 12) (d := 204) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · omega
  · omega
  · omega

theorem mod19_cases {n : ℕ} (hn : 250000000 < n) (H : Cand n) (hL : 360360 ∣ n) :
    n % 19 = 0 ∨ n % 19 = 7 ∨ n % 19 = 11 ∨ n % 19 = 13 ∨ n % 19 = 14 ∨ n % 19 = 15 ∨ n % 19 = 16 ∨ n % 19 = 17 := by
  have ht19 : (ArithmeticFunction.sigma 0) 19 = 2 := by decide
  have ht38 : (ArithmeticFunction.sigma 0) 38 = 4 := by decide
  have ht57 : (ArithmeticFunction.sigma 0) 57 = 4 := by decide
  have ht76 : (ArithmeticFunction.sigma 0) 76 = 6 := by decide
  have ht95 : (ArithmeticFunction.sigma 0) 95 = 4 := by decide
  have ht114 : (ArithmeticFunction.sigma 0) 114 = 8 := by decide
  have ht152 : (ArithmeticFunction.sigma 0) 152 = 8 := by decide
  have ht171 : (ArithmeticFunction.sigma 0) 171 = 6 := by decide
  have ht190 : (ArithmeticFunction.sigma 0) 190 = 8 := by decide
  have ht228 : (ArithmeticFunction.sigma 0) 228 = 12 := by decide
  have ht342 : (ArithmeticFunction.sigma 0) 342 = 12 := by decide
  have h2520 : n % 2520 = 0 := by omega
  clear hL
  have hr : n % 19 < 19 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 19
  · omega
  · exfalso
    exact rung H (k := 1) (d := 19) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 2) (d := 38) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 3) (d := 57) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 4) (d := 76) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 5) (d := 95) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 6) (d := 114) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · exfalso
    exact rung H (k := 8) (d := 152) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 9) (d := 171) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    exact rung H (k := 10) (d := 190) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · exfalso
    exact rung H (k := 12) (d := 228) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · exfalso
    exact rung H (k := 18) (d := 342) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)

/-- The 41 residue classes of `(n % 17, n % 19)` not excluded by divisor budgets.
Matches (independently re-derives) the class count of Hughes's reduction mod 46189. -/
def survivors : List (ℕ × ℕ) :=
  [(0, 0), (0, 7), (0, 11), (0, 13), (0, 14), (0, 15),
   (0, 16), (0, 17), (11, 0), (11, 13), (11, 14), (11, 15),
   (11, 16), (11, 17), (13, 0), (13, 7), (13, 14), (13, 15),
   (13, 16), (13, 17), (14, 0), (14, 7), (14, 11), (14, 13),
   (14, 15), (14, 16), (14, 17), (15, 0), (15, 7), (15, 11),
   (15, 13), (15, 14), (15, 16), (15, 17), (16, 0), (16, 7),
   (16, 11), (16, 13), (16, 14), (16, 15), (16, 17)]

private lemma tau2584 : (ArithmeticFunction.sigma 0) 2584 = 16 := by decide
private lemma tau3553 : (ArithmeticFunction.sigma 0) 3553 = 8 := by decide
private lemma tau4199 : (ArithmeticFunction.sigma 0) 4199 = 8 := by decide
private lemma tau4522 : (ArithmeticFunction.sigma 0) 4522 = 16 := by decide
private lemma tau4845 : (ArithmeticFunction.sigma 0) 4845 = 16 := by decide
private lemma tau9690 : (ArithmeticFunction.sigma 0) 9690 = 32 := by decide
private lemma tau14535 : (ArithmeticFunction.sigma 0) 14535 = 24 := by decide

set_option maxHeartbeats 8000000 in
/-- **Rung 2b headline.** For every candidate `n > 250000000`, the pair
`(n % 17, n % 19)` lies in the 41-class survivor list. -/
theorem mod_17_19_of_cand {n : ℕ} (hn : 250000000 < n) (H : Cand n) :
    (n % 17, n % 19) ∈ survivors := by
  have hL : 360360 ∣ n := mod360360_of_cand (by omega) H
  have h8 : n % 8 = 0 := by omega
  have h11 : n % 11 = 0 := by omega
  have h13 : n % 13 = 0 := by omega
  have h14 : n % 14 = 0 := by omega
  have h15 : n % 15 = 0 := by omega
  have h30 : n % 30 = 0 := by omega
  have h45 : n % 45 = 0 := by omega
  have hc17 := mod17_cases hn H hL
  have hc19 := mod19_cases hn H hL
  clear hL
  rcases hc17 with h17|h17|h17|h17|h17|h17 <;>
    rcases hc19 with h19|h19|h19|h19|h19|h19|h19|h19
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · exfalso
    have ht := tau14535
    clear h8 h11 h13 h14 h15 h30
    exact rung H (k := 45) (d := 14535) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    have ht := tau3553
    clear h8 h13 h14 h15 h30 h45
    exact rung H (k := 11) (d := 3553) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · exfalso
    have ht := tau9690
    clear h8 h11 h13 h14 h15 h45
    exact rung H (k := 30) (d := 9690) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · exfalso
    have ht := tau4199
    clear h8 h11 h14 h15 h30 h45
    exact rung H (k := 13) (d := 4199) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · exfalso
    have ht := tau4522
    clear h8 h11 h13 h15 h30 h45
    exact rung H (k := 14) (d := 4522) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · exfalso
    have ht := tau4845
    clear h8 h11 h13 h14 h30 h45
    exact rung H (k := 15) (d := 4845) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · rw [h17, h19]; decide
  · exfalso
    have ht := tau2584
    clear h11 h13 h14 h15 h30 h45
    exact rung H (k := 16) (d := 2584) (by omega) (by omega)
      (by norm_num) (by omega) (by omega) (by omega)
  · rw [h17, h19]; decide

/-! ## Bridge to the formal-conjectures inner predicate

The formal-conjectures statement of Erdős 647 (google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/647.lean`, commit `c252a41`; same vocabulary as
the decanus rung theorems, arXiv:2608.17880) uses the inner predicate
`⨆ m : Fin n, ↑m + σ 0 m ≤ n + 2`. `Cand` is its universally quantified form;
the two are equivalent, so the sieve theorems above apply verbatim to the
upstream statement. -/

/-- The formal-conjectures inner predicate implies `Cand`. -/
theorem cand_of_sup {n : ℕ}
    (h : ⨆ m : Fin n, ↑m + (ArithmeticFunction.sigma 0) m ≤ n + 2) : Cand n := by
  intro m hm
  have hle : m + (ArithmeticFunction.sigma 0) m ≤
      ⨆ k : Fin n, ((k : ℕ) + (ArithmeticFunction.sigma 0) k) := by
    have h' := le_ciSup (f := fun k : Fin n => ((k : ℕ) + (ArithmeticFunction.sigma 0) k))
      (Set.Finite.bddAbove (Set.finite_range _)) (⟨m, hm⟩ : Fin n)
    simpa using h'
  omega

/-- `Cand` implies the formal-conjectures inner predicate. -/
theorem sup_of_cand {n : ℕ} (H : Cand n) :
    ⨆ m : Fin n, ↑m + (ArithmeticFunction.sigma 0) m ≤ n + 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ciSup_of_empty]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact ciSup_le fun k => H k k.isLt

/-- **Bridge.** `Cand` is exactly the inner predicate of the formal-conjectures
statement of Erdős 647. -/
theorem sup_iff_cand {n : ℕ} :
    (⨆ m : Fin n, ↑m + (ArithmeticFunction.sigma 0) m ≤ n + 2) ↔ Cand n :=
  ⟨cand_of_sup, sup_of_cand⟩

/-- Rungs 1+2 in the upstream vocabulary: any `n > 250000000` satisfying the
formal-conjectures inner predicate has `360360 ∣ n` and `(n % 17, n % 19)` in
the 41-class survivor list. -/
theorem sieve_of_sup {n : ℕ} (hn : 250000000 < n)
    (h : ⨆ m : Fin n, ↑m + (ArithmeticFunction.sigma 0) m ≤ n + 2) :
    360360 ∣ n ∧ (n % 17, n % 19) ∈ survivors :=
  ⟨mod360360_of_cand (by omega) (cand_of_sup h), mod_17_19_of_cand hn (cand_of_sup h)⟩

end Erdos647Mod
