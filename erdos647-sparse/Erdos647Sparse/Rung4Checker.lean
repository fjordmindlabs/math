/-
Erdős #647 rung 4: mod 23·29 class-kill checker and soundness.
Fjordmind Labs (Eero Tölö), 2026-10. Builds on decanus (Mian–Siddique, Apache-2.0).

Flat class grid: index i < 27347 encodes (pairIdx, c23, c29) with
pairIdx = i / 667 indexing the 41 rung-2b survivor pairs, c23 = i % 667 / 29,
c29 = i % 29. A killed class carries a cert (k, ps): shift k and the full
factorization ps of the forced divisor stack

  d = gcd(360360, k) · 17^[k≡c17] · 19^[k≡c19] · 23^[k≡c23] · 29^[k≡c29].

`classKillOk` checks the cert; its soundness lemma turns a passing check
into: no candidate n > 10^11 on the 360360-grid has the class's residues.
The walker `rung4Walk` consumes one cert per killed class and matches the
survivor list positionally; chunked `decide` certificates live in
`Erdos647Sparse/Rung4Chunks/`, the composed theorem in
`Erdos647Sparse/Rung4.lean`.
-/
import Erdos647.TauLower
import Erdos647Sparse.Mod

namespace Erdos647Sparse

open Erdos647 (Pairs witnessOk certTau smoothVal smoothTau witness_tau)
open Erdos647Mod (Cand rung)

/-- The 41 rung-2b survivor pairs, indexed. Out-of-range indices return
`(1, 1)`, which is in no survivor class (17 ∤ anything ≡ 1 forced below);
the walker never queries out of range. -/
def pairAt : ℕ → ℕ × ℕ
  | 0 => (0, 0) | 1 => (0, 7) | 2 => (0, 11) | 3 => (0, 13)
  | 4 => (0, 14) | 5 => (0, 15) | 6 => (0, 16) | 7 => (0, 17)
  | 8 => (11, 0) | 9 => (11, 13) | 10 => (11, 14) | 11 => (11, 15)
  | 12 => (11, 16) | 13 => (11, 17) | 14 => (13, 0) | 15 => (13, 7)
  | 16 => (13, 14) | 17 => (13, 15) | 18 => (13, 16) | 19 => (13, 17)
  | 20 => (14, 0) | 21 => (14, 7) | 22 => (14, 11) | 23 => (14, 13)
  | 24 => (14, 15) | 25 => (14, 16) | 26 => (14, 17) | 27 => (15, 0)
  | 28 => (15, 7) | 29 => (15, 11) | 30 => (15, 13) | 31 => (15, 14)
  | 32 => (15, 16) | 33 => (15, 17) | 34 => (16, 0) | 35 => (16, 7)
  | 36 => (16, 11) | 37 => (16, 13) | 38 => (16, 14) | 39 => (16, 15)
  | 40 => (16, 17) | _ => (1, 1)

/-- The forced divisor stack for shift `k` against class `(c17, c19, c23, c29)`. -/
def stackD (c17 c19 c23 c29 k : ℕ) : ℕ :=
  Nat.gcd 360360 k
    * (if k % 17 = c17 then 17 else 1)
    * (if k % 19 = c19 then 19 else 1)
    * (if k % 23 = c23 then 23 else 1)
    * (if k % 29 = c29 then 29 else 1)

/-- One class kill at flat index `i`: the stack `d` is fully factored by
`ps` (so `certTau d ps` is exactly `τ(d)`), the rung applies to every
`n > 10^11` (`d² + k ≤ 10^11`), and the divisor budget is beaten. The
`witnessOk d 0 ps` reuse gives `0 < d`, wellformed pairs, and maximality. -/
def classKillOk (i k : ℕ) (ps : Pairs) : Bool :=
  let c := pairAt (i / 667)
  let d := stackD c.1 c.2 (i % 667 / 29) (i % 29) k
  decide (0 < k) && witnessOk d 0 ps && decide (smoothVal ps = d)
    && decide (d * d + k ≤ 100000000000) && decide (k + 2 < 2 * smoothTau ps)

/-- Class `i` is dead: no candidate `n > 10^11` on the 360360-grid has its
residues. -/
def KilledClass (i : ℕ) : Prop :=
  ∀ n : ℕ, 100000000000 < n → Cand n → 360360 ∣ n →
    n % 17 = (pairAt (i / 667)).1 → n % 19 = (pairAt (i / 667)).2 →
    n % 23 = i % 667 / 29 → n % 29 = i % 29 → False

/-- An `if _ then p else 1` stack factor divides `n - k` when the class
residue matches `n`'s. -/
private lemma if_factor_dvd {n k p c : ℕ} (hkn : k ≤ n) (hc : n % p = c) :
    (if k % p = c then p else 1) ∣ n - k := by
  by_cases h : k % p = c
  · rw [if_pos h]
    exact (Nat.modEq_iff_dvd' hkn).mp (show k ≡ n [MOD p] from h.trans hc.symm)
  · rw [if_neg h]
    exact one_dvd _

/-- Coprimality with an `if _ then p else 1` factor. -/
private lemma coprime_if {x p : ℕ} {c : Prop} [Decidable c]
    (h : Nat.Coprime x p) : Nat.Coprime x (if c then p else 1) := by
  by_cases hc : c
  · rwa [if_pos hc]
  · rw [if_neg hc]
    exact Nat.coprime_one_right x

/-- Coprimality between two `if` stack factors with coprime primes. -/
private lemma coprime_if_if {p q : ℕ} {c c' : Prop} [Decidable c] [Decidable c']
    (h : Nat.Coprime p q) :
    Nat.Coprime (if c then p else 1) (if c' then q else 1) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact coprime_if h
  · rw [if_neg hc]
    exact Nat.coprime_one_left _

/-- **Soundness of one class kill.** -/
theorem classKillOk_sound {i k : ℕ} {ps : Pairs}
    (hc : classKillOk i k ps = true) : KilledClass i := by
  intro n hn H hL h17 h19 h23 h29
  rw [classKillOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk0, hw⟩, hsv⟩, hdn⟩, hbudget⟩ := hc
  set c17 := (pairAt (i / 667)).1 with hc17
  set c19 := (pairAt (i / 667)).2 with hc19
  set d := stackD c17 c19 (i % 667 / 29) (i % 29) k with hd
  -- 0 < d from witnessOk's `decide (0 < d)` head (d < C with C = d, offset 0)
  have hd0 : 0 < d := by
    rw [Erdos647.witnessOk, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at hw
    omega
  have hkn : k ≤ n := by omega
  -- τ(d) lower bound: smoothTau ps ≤ σ₀ d via decanus witness_tau at C = d, offset 0
  have htau : smoothTau ps ≤ (ArithmeticFunction.sigma 0) d := by
    have h := witness_tau (C := d) (d := 0) (ps := ps) hw
    rw [Nat.sub_zero] at h
    rw [Erdos647.certTau, hsv, if_neg (lt_irrefl d)] at h
    rwa [ArithmeticFunction.sigma_zero_apply]
  -- divisibility: d ∣ n - k, factor by factor
  have hg : Nat.gcd 360360 k ∣ n - k :=
    Nat.dvd_sub (dvd_trans (Nat.gcd_dvd_left _ _) hL) (Nat.gcd_dvd_right _ _)
  have h17d : (if k % 17 = c17 then 17 else 1) ∣ n - k := if_factor_dvd hkn h17
  have h19d : (if k % 19 = c19 then 19 else 1) ∣ n - k := if_factor_dvd hkn h19
  have h23d : (if k % 23 = i % 667 / 29 then 23 else 1) ∣ n - k :=
    if_factor_dvd hkn h23
  have h29d : (if k % 29 = i % 29 then 29 else 1) ∣ n - k := if_factor_dvd hkn h29
  have cg : ∀ p : ℕ, Nat.Coprime 360360 p → Nat.Coprime (Nat.gcd 360360 k) p :=
    fun p hp => Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hp
  have hdvd : d ∣ n - k := by
    rw [hd]
    unfold stackD
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ h29d
    · exact ((((coprime_if (cg 29 (by decide))).mul_left
        (coprime_if_if (by decide))).mul_left
        (coprime_if_if (by decide))).mul_left
        (coprime_if_if (by decide)))
    · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ h23d
      · exact (((coprime_if (cg 23 (by decide))).mul_left
          (coprime_if_if (by decide))).mul_left
          (coprime_if_if (by decide)))
      · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ h19d
        · exact ((coprime_if (cg 19 (by decide))).mul_left
            (coprime_if_if (by decide)))
        · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
            (coprime_if (cg 17 (by decide))) hg h17d
  -- geometry: d² < n - k, hence d < (n-k)/d
  have hbig2 : d * d < n - k := by omega
  have hdivmul : n - k = d * ((n - k) / d) := (Nat.mul_div_cancel' hdvd).symm
  have hbig : d < (n - k) / d := by
    rcases Nat.lt_or_ge d ((n - k) / d) with hlt | hle
    · exact hlt
    · exfalso
      have : d * ((n - k) / d) ≤ d * d := Nat.mul_le_mul (Nat.le_refl d) hle
      omega
  exact rung H (by omega) hkn hd0 hdivmul hbig (by omega)

/-- The class walk: `fuel` flat indices starting at `i`, matching the
survivor list positionally and consuming one kill cert per non-survivor.
Both lists must be exactly consumed. -/
def rung4Walk : ℕ → ℕ → List ℕ → List (ℕ × Pairs) → Bool
  | 0, _, ss, ks => ss.isEmpty && ks.isEmpty
  | fuel + 1, i, j :: st, (k, ps) :: kt =>
      if i = j then rung4Walk fuel (i + 1) st ((k, ps) :: kt)
      else classKillOk i k ps && rung4Walk fuel (i + 1) (j :: st) kt
  | fuel + 1, i, j :: st, [] => decide (i = j) && rung4Walk fuel (i + 1) st []
  | fuel + 1, i, [], (k, ps) :: kt => classKillOk i k ps && rung4Walk fuel (i + 1) [] kt
  | _ + 1, _, [], [] => false

/-- Soundness of the walk: every index in the walked span is a listed
survivor or a killed class. -/
theorem rung4Walk_sound : ∀ {fuel i0 : ℕ} {ss : List ℕ} {ks : List (ℕ × Pairs)},
    rung4Walk fuel i0 ss ks = true →
    ∀ i : ℕ, i0 ≤ i → i < i0 + fuel → i ∈ ss ∨ KilledClass i := by
  intro fuel
  induction fuel with
  | zero =>
    intro i0 ss ks _ i h1 h2
    omega
  | succ fuel ih =>
    intro i0 ss ks h i h1 h2
    rcases ss with _ | ⟨j, st⟩
    · rcases ks with _ | ⟨⟨k, ps⟩, kt⟩
      · rw [rung4Walk] at h
        exact absurd h (by decide)
      · rw [rung4Walk, Bool.and_eq_true] at h
        obtain ⟨hk, hrest⟩ := h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hij
        · exact Or.inr (classKillOk_sound hk)
        · exact ih hrest i hij (by omega)
    · rcases ks with _ | ⟨⟨k, ps⟩, kt⟩
      · rw [rung4Walk, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hij0, hrest⟩ := h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hij
        · exact Or.inl (hij0 ▸ List.mem_cons_self)
        · rcases ih hrest i hij (by omega) with hm | hk
          · exact Or.inl (List.mem_cons_of_mem j hm)
          · exact Or.inr hk
      · rw [rung4Walk] at h
        by_cases hij0 : i0 = j
        · rw [if_pos hij0] at h
          rcases Nat.eq_or_lt_of_le h1 with rfl | hij
          · exact Or.inl (hij0 ▸ List.mem_cons_self)
          · rcases ih h i hij (by omega) with hm | hk
            · exact Or.inl (List.mem_cons_of_mem j hm)
            · exact Or.inr hk
        · rw [if_neg hij0, Bool.and_eq_true] at h
          obtain ⟨hk, hrest⟩ := h
          rcases Nat.eq_or_lt_of_le h1 with rfl | hij
          · exact Or.inr (classKillOk_sound hk)
          · exact ih hrest i hij (by omega)

/-- Kernel-friendly Bool membership in an index list. -/
def inIdx (a : ℕ) : List ℕ → Bool
  | [] => false
  | x :: t => a == x || inIdx a t

theorem inIdx_of_mem {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → inIdx a l = true := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x t ih =>
    intro h
    rw [inIdx, Bool.or_eq_true, beq_iff_eq]
    rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (ih h)

/-- Bool sublist test: every element of the first list is in the second. -/
def inSub : List ℕ → List ℕ → Bool
  | [], _ => true
  | x :: t, L => inIdx x L && inSub t L

theorem inSub_mem {L : List ℕ} {a : ℕ} : ∀ {l : List ℕ},
    inSub l L = true → a ∈ l → inIdx a L = true := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x t ih =>
    intro hs h
    rw [inSub, Bool.and_eq_true] at hs
    rcases List.mem_cons.mp h with rfl | h
    · exact hs.1
    · exact ih hs.2 h

end Erdos647Sparse
