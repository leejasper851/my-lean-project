-- 1

section Chapter3
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

  section Classical
    open Classical

    variable (p q r : Prop)

    example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
      intro h
      cases (em p) with
      | inl hp => simp [*]
      | inr hnp => simp [*]

    example : ¬(p ∧ q) → ¬p ∨ ¬q := by
      intro h
      cases (em p) with
      | inl hp =>
        cases (em q) with
        | inl hq =>
          have : p ∧ q := by constructor; exact hp; exact hq
          contradiction
        | inr hnq => apply Or.inr; assumption
      | inr hnp =>
        simp [*]

    example : ¬(p → q) → p ∧ ¬q := by
      intro h
      cases (em p) with
      | inl hp =>
        constructor
        assumption
        cases (em q) with
        | inl hq =>
          have : p → q := by intro; assumption
          contradiction
        | inr hnq => assumption
      | inr hnp =>
        have : p → q := by simp [*]
        contradiction

    example : (p → q) → (¬p ∨ q) := by
      intro h
      cases (em p) with
      | inl hp => simp [*]
      | inr hnp => simp [*]

    example : (¬q → ¬p) → (p → q) := by
      intro h
      intro hp
      cases (em q) with
      | inl hq => simp [*]
      | inr hnq =>
        have : ¬p := by exact h hnq
        contradiction

    example : p ∨ ¬p := by
      simp [em]

    example : (((p → q) → p) → p) := by
      intro h
      cases (em p) with
      | inl hp => assumption
      | inr hnp =>
        have : p → q := by simp [*]
        exact h this
  end Classical

  example : ¬(p ↔ ¬p) := by
    simp
end Chapter3

section Chapter4_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
    constructor
    . intro h
      simp [*]
    . intro h
      simp [*]

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
    intro h
    intro hap
    simp [*]

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
    intro h
    intro y
    cases h
    . simp [*]
    . simp [*]
end Chapter4_1

section Chapter4_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) := by
    intro y
    constructor
    . intro har
      exact (har y)
    . intro hr
      simp [*]

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
    constructor
    . intro h
      cases Classical.em r with
      | inl hr => simp [*]
      | inr hnr =>
        apply Or.inl
        intro y
        cases h y
        . simp [*]
        . contradiction
    . intro h
      intro y
      cases h
      . simp [*]
      . simp [*]

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
    constructor
    . intro h
      intro hr
      simp [*]
    . intro h
      intro y
      intro hr
      simp [*]
end Chapter4_2

section Chapter4_3
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
    have : ¬(shaves barber barber ↔ ¬shaves barber barber) := by
      simp
    exact this (h barber)
end Chapter4_3

section Chapter4_4
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r := by
    simp

  example (a : α) : r → (∃ x : α, r) := by
    intro hr
    exists a

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
    simp

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
    constructor
    . intro h
      cases h with
      | intro y hpyoqy =>
        cases hpyoqy
        . apply Or.inl; exists y
        . apply Or.inr; exists y
    . intro h
      cases h with
      | inl hep =>
        cases hep with
        | intro y hpy =>
          exists y
          simp [*]
      | inr heq =>
        cases heq with
        | intro y hqy =>
          exists y
          simp [*]

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
    simp

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
    simp

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
    simp

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
    simp

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
    simp

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
    constructor
    . intro heptr
      intro hap
      cases heptr with
      | intro y hpytr =>
        simp [*]
    . intro haptr
      cases em (∀ x, p x) with
      | inl hap =>
        have : r := by exact haptr hap
        exists a
        intro
        assumption
      | inr hnap =>
        have : ∃ x, ¬p x := by
          cases em (∃ x, ¬p x) with
          | inl henp => assumption
          | inr hnenp =>
            have : ∀ x, p x := by
              intro y
              cases (em (p y)) with
              | inl hpy => assumption
              | inr hnpy =>
                have : False := by
                  apply hnenp
                  exists y
                contradiction
            contradiction
        cases this with
        | intro y hnpy =>
          exists y
          simp [*]

  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
    constructor
    . intro h
      intro hr
      cases h with
      | intro y hrtpy =>
        exists y
        exact hrtpy hr
    . intro h
      cases (em r) with
      | inl hr => simp [*]
      | inr hnr =>
        exists a
        simp [*]
end Chapter4_4

-- 2

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)
