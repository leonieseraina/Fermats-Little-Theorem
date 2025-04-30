import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic
-- necessary imports are shown when hovering above a theorem


-- How to approach a proof in Lean:
-- 1. Write out the structure of the proof (lemmas, intermediate steps, etc.) using sorrys
-- 2. Break down big steps into smaller steps
-- 3. Prove each sorry


open Int
open Nat
-- this makes theorems more readable
-- does not work with all theorems because of ambiguity (e.g. Nat.modEq_iff_dvd)


-- Important theorems for this proof:
#check Commute.add_pow_prime_eq
#check Nat.modEq_iff_dvd
#check Int.toNat -- convert from ℤ to ℕ


-- Proof of a^p ≡ a [MOD p] for a ∈ ℕ (by induction)
lemma frobenius_identity {p a: ℕ} (hp_Nat_prime : p.Prime): a^p ≡ a [MOD p] := by
  induction' a with a ih
  -- Base Case: Prove 0^p ≡ 0 [MOD p]
  · rw [zero_pow hp_Nat_prime.ne_zero]
  -- Induction Step: Prove (a + 1)^p ≡ a + 1 [MOD p] given a^p ≡ a [MOD p] for some a ≥ 0
  · have : (a + 1)^p ≡ a^p + 1 [MOD p] := by
      have : Commute a 1 := by
        apply Commute.one_right
      rw [Commute.add_pow_prime_eq hp_Nat_prime this] -- directly factor out p in the binomial expansion
      rw [Nat.modEq_iff_dvd]
      simp
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply ih


-- Proof of a^(p - 1) ≡ 1 [ZMOD p] for a ∈ ℤ
theorem fermat_little {p : ℕ} {a : ℤ} (hp_Nat_prime : p.Prime) (hap_coprime : gcd p a = 1) :
  a^(p - 1) ≡ 1 [ZMOD p] := by
  -- Step 1: Prove a^p ≡ a [ZMOD p] for a ∈ ℤ
  have ha_frobenius : a^p ≡ a [ZMOD p] := by
    -- Step 1.1: Prove a^p ≡ a [ZMOD p] for a ≥ 0 (using lemma frobenius_identity)
    have ha_frobenius_pos {a : ℤ} (ha_pos : a ≥ 0) : a^p ≡ a [ZMOD p] := by -- before actual case distiction so we can use it in both cases
      let a' := a.toNat -- turning a into a natural number (type sensibility of lean)
      have : a = a' := by
        rw [eq_comm]
        exact Int.toNat_of_nonneg ha_pos
      rw [this]
      have : (a' : ℤ)^p = ↑(a'^p) := by -- ↑(a'^p) means coerce (convert) a'^p from ℕ to ℤ
        rw [Int.natCast_pow a' p]
      have : (a' : ℤ)^p ≡ a' [ZMOD p] := by
        rw [this, Int.natCast_modEq_iff]
        exact frobenius_identity hp_Nat_prime -- use previous lemma
      exact this
    -- Step 1.2: Split into cases a ≥ 0 and a < 0
    by_cases ha_pos : a ≥ 0
    -- Step 1.2.1: Prove a^p ≡ a [ZMOD p] for a ≥ 0 (using ha_frobenius_pos)
    · exact ha_frobenius_pos ha_pos -- use step 1.1
    -- Step 1.2.2: Prove a^p ≡ a [ZMOD p] for a < 0 (split into cases p = 2 and p > 2)
    · by_cases hp_two : p = 2
      -- Step 1.2.2.1: Prove a^p ≡ a [ZMOD p] for a < 0 and p = 2 (using ha_frobenius_pos)
      · subst hp_two
        rw [Int.modEq_comm, Int.modEq_iff_dvd] -- going backwards compared to the written proof (rewrite goal)
        have : -a = a - 2*a := by
          ring
        rw [Int.sub_eq_add_neg, this, ← add_sub_assoc]
        apply Int.dvd_sub
        · have : a = -(-a) := by
            rw [eq_comm]
            exact neg_neg a
          rw [this, ← Int.sub_eq_add_neg, ← Int.modEq_iff_dvd, Int.modEq_comm]
          simp
          rw [← neg_sq]
          have : -a ≥ 0 := by
            linarith
          apply ha_frobenius_pos this -- use step 1.1
        · simp
      -- Step 1.2.2.2: Prove a^p ≡ a [ZMOD p] for a < 0 and p > 2 (using ha_frobenius_pos)
      · have : a^p = -(-a)^p := by
          rw [neg_pow]
          have : Odd p := by
            push_neg at hp_two
            exact hp_Nat_prime.odd_of_ne_two hp_two
          rw [Odd.neg_one_pow this]
          norm_num
        rw [this]
        have : a = -(-a) := by
          rw [eq_comm]
          exact neg_neg a
        rw [this]
        apply Int.ModEq.neg
        rw [← this]
        have : -a ≥ 0 := by
          linarith
        exact ha_frobenius_pos this -- use step 1.1
  -- Step 2: Use a^p ≡ a [ZMOD p] to prove a^(p - 1) ≡ 1 [ZMOD p]
  -- Step 2.1: Prove p ∣ a * (a^(p - 1) - 1)
  have : (p : ℤ) ∣ a * (a^(p - 1) - 1) := by
    rw [mul_sub_left_distrib]
    rw [mul_one]
    rw [mul_comm]
    rw [← pow_succ a (p - 1)]
    have : 1 ≤ p := by
      exact hp_Nat_prime.one_le
    rw [Nat.sub_add_cancel this]
    rw [← Int.modEq_iff_dvd]
    apply Int.ModEq.symm
    apply ha_frobenius -- use step 1
  -- Step 2.2: Prove that either p ∣ a or p ∣ (a^(p - 1) - 1)
  have h_disj : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ (a^(p - 1) - 1) := by
    have hp_prime : Prime (p : ℤ) := by
      apply prime_iff_prime_int.mp hp_Nat_prime
    rw [← Prime.dvd_mul hp_prime]
    apply this
  -- Step 2.3: Prove that we cannot have p ∣ a
  have : ¬ (p : ℤ) ∣ a := by
    by_contra h
    have : gcd p a = p := by
      apply gcd_eq_left h
    rw [hap_coprime] at this
    rw [eq_comm] at this
    apply hp_Nat_prime.ne_one
    apply this
  -- Step 2.4: Prove that we must have p ∣ (a^(p - 1) - 1)
  have : (p : ℤ) ∣ (a^(p - 1) - 1) := by
    cases h_disj with
    | inl h₁ => contradiction
    | inr h₂ => exact h₂
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact this
