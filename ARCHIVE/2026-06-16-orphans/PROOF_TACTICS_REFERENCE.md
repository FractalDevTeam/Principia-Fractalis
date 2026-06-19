# Lean 4 Proof Tactics Reference for Interval Arithmetic

Quick reference for tactics used in `IntervalArithmetic.lean` theorem proofs.

---

## Core Computational Tactics

### `norm_num`
**Purpose**: Verifies numerical computations and inequalities automatically.

**Examples**:
```lean
-- Verify arithmetic
_ = 1.86803398 := by norm_num  -- 1.61803398 + 0.25

-- Verify inequality
_ > 1.41421357 := by norm_num  -- 1.86803398 > 1.41421357

-- Verify positivity
· norm_num  -- (0 : ℝ) < 2
```

**When to use**: Any time you need to prove a concrete numerical equality or inequality.

---

### `linarith`
**Purpose**: Linear arithmetic solver for inequalities involving additions/multiplications by constants.

**Examples**:
```lean
-- Combine known bounds
_ ≥ 1.61803398 + 1/4 := by linarith [phi_lower]

-- Prove from hypotheses
linarith [sqrt2_upper]

-- Multiple hypotheses
constructor; linarith; linarith
```

**When to use**: When you have inequalities involving sums/differences and want to combine them.

---

## Square Root Tactics

### `Real.le_sqrt`
**Purpose**: Converts `a ≤ √b` to `a² ≤ b`.

**Signature**:
```lean
Real.le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ≤ √b ↔ a² ≤ b
```

**Example**:
```lean
rw [Real.le_sqrt]
· norm_num  -- Prove 1.41421356² ≤ 2
· norm_num  -- Prove 0 ≤ 1.41421356
· norm_num  -- Prove 0 ≤ 2
```

**When to use**: Proving lower bounds on √n.

---

### `Real.sqrt_le_left`
**Purpose**: Converts `√a ≤ b` to `a ≤ b²` (when b ≥ 0).

**Signature**:
```lean
Real.sqrt_le_left {a b : ℝ} (hb : 0 ≤ b) : √a ≤ b ↔ a ≤ b²
```

**Example**:
```lean
rw [Real.sqrt_le_left]
· norm_num  -- Prove 2 ≤ 1.41421357²
· norm_num  -- Prove 0 ≤ 1.41421357
```

**When to use**: Proving upper bounds on √n.

---

## Division and Multiplication Tactics

### `div_lt_div_of_pos_left`
**Purpose**: For `c / a < c / b` when `c > 0` and `a > b > 0`.

**Signature**:
```lean
div_lt_div_of_pos_left {a b c : ℝ} (ha : 0 < a) (hb : a < b) (hc : 0 < c) : c / b < c / a
```

**Example**:
```lean
apply div_lt_div_of_pos_left
· norm_num  -- 0 < numerator
· apply mul_pos; norm_num; apply Real.sqrt_pos.mpr; norm_num  -- 0 < denominator
· apply mul_lt_mul_of_pos_left sqrt2_upper; norm_num  -- denominator increase
· exact pi_lower_bound  -- numerator increase
```

**When to use**: Proving bounds on fractions a/b when a or b varies.

---

### `div_le_iff`
**Purpose**: Converts `a / b ≤ c` to `a ≤ c * b` (when b > 0).

**Signature**:
```lean
div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b
```

**Example**:
```lean
rw [div_le_iff]
· calc
    1.61803398 * 2 = 3.23606796 := by norm_num
    _ ≤ 1 + Real.sqrt 5 := ...
· norm_num  -- Prove 0 < 2
```

**When to use**: Eliminating division from inequality.

---

### `mul_lt_mul_of_pos_left`
**Purpose**: For `a < b`, proves `c * a < c * b` when `c > 0`.

**Signature**:
```lean
mul_lt_mul_of_pos_left {a b c : ℝ} (hab : a < b) (hc : 0 < c) : c * a < c * b
```

**Example**:
```lean
apply mul_lt_mul_of_pos_left sqrt2_upper
· norm_num  -- Prove 0 < 10
```

---

## Calculus Tactics

### `deriv`
**Purpose**: Computes derivative of a function.

**Example**:
```lean
deriv (fun x => Real.log x / x) b
```

**Supporting lemmas**:
- `Real.deriv_log`: d/dx[ln x] = 1/x
- `deriv_div`: quotient rule
- `deriv_pow`: power rule

---

### `Real.log_lt_log`
**Purpose**: For `a < b`, proves `ln a < ln b`.

**Signature**:
```lean
Real.log_lt_log {a b : ℝ} (ha : 0 < a) (hab : a < b) : Real.log a < Real.log b
```

**Example**:
```lean
apply Real.log_lt_log _ hb
apply Real.exp_pos  -- Show 0 < exp(3/2)
```

---

### `Real.log_exp`
**Purpose**: Proves `ln(eˣ) = x`.

**Example**:
```lean
_ = 3/2 := Real.log_exp (3/2)
```

---

## Structural Tactics

### `calc`
**Purpose**: Chain equalities and inequalities step-by-step.

**Example**:
```lean
calc
  Real.sqrt 2 ≤ 1.41421357 := sqrt2_upper
  _ < 1.415 := by norm_num
```

**When to use**: Any multi-step numerical proof.

---

### `constructor`
**Purpose**: Splits conjunction `A ∧ B` into two goals.

**Example**:
```lean
theorem sqrt2_in_interval_ultra : lower ≤ √2 ∧ √2 ≤ upper := by
  constructor
  · [prove lower ≤ √2]
  · [prove √2 ≤ upper]
```

---

### `exact`
**Purpose**: Directly provides a proof term.

**Example**:
```lean
theorem sqrt2_lower : √2 ≥ 1.41421356 := by
  exact sqrt2_in_interval_ultra.1  -- Use first part of conjunction
```

---

### `rfl`
**Purpose**: Reflexivity (proves `a = a`).

**Example**:
```lean
phi + 1/4 = (1 + Real.sqrt 5) / 2 + 1/4 := rfl
```

---

## Induction Tactics

### `Nat.le_induction`
**Purpose**: Induction starting from a non-zero natural number.

**Signature**:
```lean
Nat.le_induction {P : ℕ → Prop} {m : ℕ}
  (base : P m)
  (succ : ∀ n ≥ m, P n → P (n + 1))
  : ∀ n ≥ m, P n
```

**Example**:
```lean
theorem Q_4_ge_Q_larger :
    ∀ (b : ℕ), b ≥ 4 → Q(4) ≥ Q(b) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => rfl.le  -- Q(4) ≥ Q(4)
  | succ n hn ih =>
    calc
      Q(4) ≥ Q(n) := ih
      _ ≥ Q(n+1) := Q_decreasing_from_4 n hn
```

---

## Absolute Value Tactics

### `abs_sub_lt_iff`
**Purpose**: Converts `|a - b| < c` to `b - c < a ∧ a < b + c`.

**Signature**:
```lean
abs_sub_lt_iff {a b c : ℝ} : |a - b| < c ↔ b - c < a ∧ a < b + c
```

**Example**:
```lean
theorem lambda_0_P_precise : |λ₀(P) - 0.2221441469| < 1e-10 := by
  rw [abs_sub_lt_iff]
  constructor
  · -- Prove lower bound
  · -- Prove upper bound
```

---

## Common Proof Patterns

### Pattern 1: Interval Bound via Squaring
```lean
-- Prove a ≤ √n ≤ b
theorem sqrt_n_bounds : a ≤ Real.sqrt n ∧ Real.sqrt n ≤ b := by
  constructor
  · -- Lower: a ≤ √n
    rw [Real.le_sqrt]
    · norm_num  -- a² ≤ n
    · norm_num  -- 0 ≤ a
    · norm_num  -- 0 ≤ n
  · -- Upper: √n ≤ b
    rw [Real.sqrt_le_left]
    · norm_num  -- n ≤ b²
    · norm_num  -- 0 ≤ b
```

---

### Pattern 2: Division Interval Bounds
```lean
-- Prove c/a > L given c ∈ [c₁, c₂] and a ∈ [a₁, a₂]
theorem div_lower_bound : c / a > L := by
  calc
    c / a = c / a := rfl
    _ > c₁ / a₂ := by  -- Lower numerator, upper denominator
      apply div_lt_div_of_pos_left
      · [positivity of numerator]
      · [denominator increase]
      · [numerator increase]
    _ = [concrete value] := by norm_num
    _ > L := by norm_num
```

---

### Pattern 3: Chaining Interval Bounds
```lean
-- Combine multiple bounds
theorem combined_bound : f(x) > L := by
  calc
    f(x) = g(x) + h(x) := [definition]
    _ ≥ g_lower + h_lower := by linarith [g_lower_bound, h_lower_bound]
    _ = [concrete value] := by norm_num
    _ > L := by norm_num
```

---

### Pattern 4: Proving from Conjunction
```lean
-- Extract from A ∧ B
theorem use_bound : statement := by
  exact previous_theorem.1  -- Use first part (.1)
  exact previous_theorem.2  -- Use second part (.2)
```

---

## Common Lemmas Reference

### Positivity
```lean
Real.sqrt_pos : 0 < n → 0 < Real.sqrt n
Real.exp_pos : ∀ x, 0 < Real.exp x
mul_pos : 0 < a → 0 < b → 0 < a * b
```

### Inequalities
```lean
add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b
add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c
mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b
```

### Division
```lean
div_mul_cancel₀ : b ≠ 0 → (a / b) * b = a
div_lt_one : 0 < b → (a / b < 1 ↔ a < b)
div_lt_zero_iff : a / b < 0 ↔ (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)
```

---

## Debugging Tips

### When `norm_num` fails:
1. Check decimal precision (use enough digits)
2. Verify all terms are concrete numbers
3. Try breaking into smaller steps

### When `linarith` fails:
1. Provide explicit hypotheses: `linarith [h1, h2]`
2. Check for nonlinear terms (×, ÷, √)
3. Try `nlinarith` for polynomial nonlinear terms

### When division proofs fail:
1. Prove denominator > 0 explicitly
2. Use `apply mul_pos` for products
3. Use `Real.sqrt_pos.mpr` for square roots

---

## External Resources

- **Mathlib Docs**: https://leanprover-community.github.io/mathlib4_docs/
- **Lean 4 Manual**: https://lean-lang.org/lean4/doc/
- **Tactics Cheatsheet**: https://github.com/madvorak/lean4-tactics

---

**File**: `/home/xluxx/pablo_context/Principia_Fractalis_COMPLETE_2025-11-16_0250AM/PROOF_TACTICS_REFERENCE.md`
**Last Updated**: 2025-11-16
