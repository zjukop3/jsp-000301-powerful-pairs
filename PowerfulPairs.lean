import Mathlib

/-!
# Consecutive powerful nonsquares: a uniform construction from any seed

The classical seed is due to Golomb (1970); infinitely many pairs were proved
by Walker (1976). This development formalizes a seed-parametric Pell orbit,
its preservation properties, and a uniform multiplicative gap bound.
-/

namespace PowerfulPairs

def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

def GoodPair (n : ℕ) : Prop :=
  Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1)

theorem powerful_mul {a b : ℕ} (ha : Powerful a) (hb : Powerful b) :
    Powerful (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha.2 p hp h) b
  · exact dvd_mul_of_dvd_right (hb.2 p hp h) a

theorem powerful_square {a : ℕ} (ha : 0 < a) : Powerful (a ^ 2) := by
  refine ⟨pow_pos ha 2, ?_⟩
  intro p hp hd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2

theorem powerful_cube {a : ℕ} (ha : 0 < a) : Powerful (a ^ 3) := by
  refine ⟨pow_pos ha 3, ?_⟩
  intro p hp hd
  have h : p ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2
  exact h.trans (pow_dvd_pow a (by omega))

theorem nonsquare_mul_square {a x : ℕ} (ha : ¬ IsSquare a) (hx : 0 < x) :
    ¬ IsSquare (a * x ^ 2) := by
  rintro ⟨y, hy⟩
  have hd : x ^ 2 ∣ y ^ 2 := by
    rw [pow_two, ← hy]
    exact dvd_mul_left _ _
  have hd' : x ∣ y := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hd
  obtain ⟨z, hz⟩ := hd'
  apply ha
  refine ⟨z, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hx 2)
  calc
    a * x ^ 2 = y * y := hy
    _ = (z * z) * x ^ 2 := by rw [hz]; ring

def orbit (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
      let v := orbit n k
      ((2 * n + 1) * v.1 + 2 * (n + 1) * v.2,
       2 * n * v.1 + (2 * n + 1) * v.2)

theorem orbit_positive (n k : ℕ) :
    0 < (orbit n k).1 ∧ 0 < (orbit n k).2 := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
      dsimp [orbit]
      constructor <;> positivity

theorem orbit_equation (n k : ℕ) :
    n * (orbit n k).1 ^ 2 + 1 = (n + 1) * (orbit n k).2 ^ 2 := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
      dsimp [orbit]
      nlinarith only [ih]

theorem orbit_order (n k : ℕ) : (orbit n k).2 ≤ (orbit n k).1 := by
  cases k with
  | zero => simp [orbit]
  | succ k => dsimp [orbit]; omega

theorem orbit_step_upper (n k : ℕ) :
    (orbit n (k + 1)).1 ≤ (4 * n + 3) * (orbit n k).1 := by
  have h := Nat.mul_le_mul_left (2 * (n + 1)) (orbit_order n k)
  dsimp [orbit]
  nlinarith only [h]

theorem orbit_step_strict (n k : ℕ) :
    (orbit n k).1 < (orbit n (k + 1)).1 := by
  have hp := orbit_positive n k
  dsimp [orbit]
  nlinarith

def value (n k : ℕ) : ℕ := n * (orbit n k).1 ^ 2

@[simp] theorem value_zero (n : ℕ) : value n 0 = n := by simp [value, orbit]

theorem value_add_one (n k : ℕ) :
    value n k + 1 = (n + 1) * (orbit n k).2 ^ 2 := orbit_equation n k

theorem value_strictMono {n : ℕ} (hn : 0 < n) : StrictMono (value n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold value
  apply Nat.mul_lt_mul_of_pos_left _ hn
  exact Nat.pow_lt_pow_left (orbit_step_strict n k) (by decide)

theorem goodPair_value {n : ℕ} (hn : GoodPair n) (k : ℕ) : GoodPair (value n k) := by
  have hp := orbit_positive n k
  refine ⟨powerful_mul hn.1 (powerful_square hp.1), ?_,
    nonsquare_mul_square hn.2.2.1 hp.1, ?_⟩
  · rw [value_add_one]
    exact powerful_mul hn.2.1 (powerful_square hp.2)
  · rw [value_add_one]
    exact nonsquare_mul_square hn.2.2.2 hp.2

theorem value_step_upper (n k : ℕ) :
    value n (k + 1) ≤ (4 * n + 3) ^ 2 * value n k := by
  have h := Nat.pow_le_pow_left (orbit_step_upper n k) 2
  have h' := Nat.mul_le_mul_left n h
  simpa [value, mul_pow, mul_assoc, mul_comm, mul_left_comm] using h'

theorem value_geometric_upper (n k : ℕ) :
    value n k ≤ n * ((4 * n + 3) ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        value n (k + 1) ≤ (4 * n + 3) ^ 2 * value n k := value_step_upper n k
        _ ≤ (4 * n + 3) ^ 2 * (n * ((4 * n + 3) ^ 2) ^ k) :=
          Nat.mul_le_mul_left _ ih
        _ = n * ((4 * n + 3) ^ 2) ^ (k + 1) := by ring

/-- Every valid seed produces a further pair in each sufficiently high
multiplicative interval, with an explicit constant depending only on the seed. -/
theorem bounded_multiplicative_gaps {n : ℕ} (hn : GoodPair n)
    (B : ℕ) (hB : n ≤ B) :
    ∃ m : ℕ, B < m ∧ m ≤ (4 * n + 3) ^ 2 * B ∧ GoodPair m := by
  have hmono := value_strictMono hn.1.1
  have hex : ∃ k, B < value n k :=
    ⟨B + 1, lt_of_lt_of_le (Nat.lt_succ_self B) (hmono.id_le (B + 1))⟩
  have hmin := Nat.find_spec hex
  cases heq : Nat.find hex with
  | zero => simp [heq] at hmin; omega
  | succ j =>
      have hj : value n j ≤ B := by
        apply Nat.le_of_not_gt
        exact Nat.find_min hex (by omega)
      refine ⟨value n (j + 1), ?_, ?_, goodPair_value hn (j + 1)⟩
      · simpa [heq] using hmin
      · exact (value_step_upper n j).trans (Nat.mul_le_mul_left _ hj)

theorem golomb_seed : GoodPair 12167 := by
  have h₁ : Powerful 12167 := by
    convert powerful_cube (by decide : 0 < (23 : ℕ)) using 1 <;> norm_num
  have h₂ : Powerful 12168 := by
    convert powerful_mul (powerful_cube (by decide : 0 < (2 : ℕ)))
      (powerful_square (by decide : 0 < (39 : ℕ))) using 1 <;> norm_num
  exact ⟨h₁, h₂, by norm_num [IsSquare], by norm_num [IsSquare]⟩

theorem jsp_000301 :
    ¬ (∀ n : ℕ, Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 golomb_seed.1 golomb_seed.2.1 with h | h
  · exact golomb_seed.2.2.1 h
  · exact golomb_seed.2.2.2 h

theorem explicit_gap_bound (B : ℕ) (hB : 12167 ≤ B) :
    ∃ n : ℕ, B < n ∧ n ≤ 2368866241 * B ∧ GoodPair n := by
  simpa using bounded_multiplicative_gaps golomb_seed B hB

theorem infinitely_many_pairs : Set.Infinite {n : ℕ | GoodPair n} := by
  apply Set.infinite_of_injective_forall_mem (value_strictMono golomb_seed.1.1).injective
  exact goodPair_value golomb_seed

end PowerfulPairs
