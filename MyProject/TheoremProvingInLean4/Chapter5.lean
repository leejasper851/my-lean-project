-- 1

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro h
    constructor
    exact h.right
    exact h.left
  . intro h
    constructor
    exact h.right
    exact h.left

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro h
    cases h
    . apply Or.inr
      assumption
    . apply Or.inl
      assumption
  . intro h
    cases h
    . apply Or.inr
      assumption
    . apply Or.inl
      assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro h
    constructor
    exact h.left.left
    constructor
    exact h.left.right
    exact h.right
  . intro h
    constructor
    constructor
    exact h.left
    exact h.right.left
    exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hpoq =>
      cases hpoq
      . apply Or.inl
        assumption
      . apply Or.inr
        apply Or.inl
        assumption
    | inr hr =>
      apply Or.inr
      apply Or.inr
      assumption
  . intro h
    cases h with
    | inl hp =>
      apply Or.inl
      apply Or.inl
      assumption
    | inr hqor =>
      cases hqor
      . apply Or.inl
        apply Or.inr
        assumption
      . apply Or.inr
        assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h
    cases h.right
    . apply Or.inl
      constructor; exact h.left; assumption
    . apply Or.inr
      constructor; exact h.left; assumption
  . intro h
    cases h with
    | inl hpq =>
      constructor
      exact hpq.left
      apply Or.inl; exact hpq.right
    | inr hpr =>
      constructor
      exact hpr.left
      apply Or.inr; exact hpr.right

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hp =>
      constructor
      apply Or.inl; assumption
      apply Or.inl; assumption
    | inr hqr =>
      constructor
      apply Or.inr; exact hqr.left
      apply Or.inr; exact hqr.right
  . intro h
    cases h.left
    . apply Or.inl; assumption
    . simp [*]

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h
    intro hpq
    exact h hpq.left hpq.right
  . intro h
    intro hp
    intro hq
    simp [*]

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h
    constructor
    . intro hp; simp [*]
    . intro hq; simp [*]
  . intro h
    intro hpoq
    cases hpoq
    simp [*]
    simp [*]

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h
    constructor
    intro hp
    exact h (Or.inl hp)
    intro hq
    exact h (Or.inr hq)
  . intro h
    intro hpoq
    cases hpoq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  intro hpq
  cases h with
  | inl hnp => exact hnp hpq.left
  | inr hnq => exact hnq hpq.right

example : ¬(p ∧ ¬p) := by
  simp [*]

example : p ∧ ¬q → ¬(p → q) := by
  simp [*]

example : ¬p → (p → q) := by
  intro hnp
  simp [*]

example : (¬p ∨ q) → (p → q) := by
  intro h
  intro hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  simp [*]

example : p ∧ False ↔ False := by
  simp [*]

example : (p → q) → (¬q → ¬p) := by
  intro h
  intro hnq
  intro hp
  exact hnq (h hp)

namespace C
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry

  example : ¬(p ↔ ¬p) := sorry
end C

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  sorry

namespace C
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r := sorry
  example (a : α) : r → (∃ x : α, r) := sorry
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end C

-- 2

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry
