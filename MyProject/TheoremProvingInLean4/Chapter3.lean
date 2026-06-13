variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨h.right, h.left⟩)
    (fun h : q ∧ p => ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h : q ∨ p => h.elim (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h : p ∧ (q ∧ r) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r => h.elim (fun hpq => hpq.elim (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq))) (fun hr => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) => h.elim (fun hp => Or.inl (Or.inl hp)) (fun hqr => hqr.elim (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) => h.right.elim (fun hq => Or.inl ⟨h.left, hq⟩) (fun hr => Or.inr ⟨h.left, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) => h.elim (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩) (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) => h.elim (fun hp => ⟨Or.inl hp, Or.inl hp⟩) (fun hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) => h.left.elim (fun hp => Or.inl hp) (fun hq => h.right.elim (fun hp => Or.inl hp) (fun hr => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) => (fun hpq => h hpq.left hpq.right))
    (fun h : p ∧ q → r => (fun hp => (fun hq => h ⟨hp, hq⟩)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun h : (p → r) ∧ (q → r) => (fun hpq => hpq.elim (fun hp => h.left hp) (fun hq => h.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun h : ¬p ∧ ¬q => (fun hpq => hpq.elim (fun hp => h.left hp) (fun hq => h.right hq)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q => (fun hpq => h.elim (fun hnp => hnp hpq.left) (fun hnq => hnq hpq.right))

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q => (fun h₂ : p → q => h.right (h₂ h.left))

example : ¬p → (p → q) :=
  fun hnp : ¬p => (fun hp => False.elim (hnp hp))

example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q => (fun hp => h.elim (fun hnp => absurd hp hnp) (fun hq => hq))

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False => h.elim (fun hp => hp) (fun hfalse => False.elim hfalse))
    (fun hp : p => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => h.right)
    (fun hfalse : False => False.elim hfalse)

example : (p → q) → (¬q → ¬p) :=
  fun h : p → q => (fun hnq => (fun hp => hnq (h hp)))


open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r => ((em p).elim (fun hp => (h hp).elim (fun hq => Or.inl (fun _ => hq)) (fun hr => Or.inr (fun _ => hr)))
    (fun hnp => Or.inl (fun hp => absurd hp hnp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) => ((em p).elim (fun hp => (em q).elim (fun hq => absurd ⟨hp, hq⟩ h) (fun hnq => Or.inr hnq))
    (fun hnp => Or.inl hnp))

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) => ((em p).elim (fun hp => (em q).elim (fun hq => False.elim (h (fun _ => hq))) (fun hnq => ⟨hp, hnq⟩))
    (fun hnp => False.elim (h (fun hp => absurd hp hnp))))

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q => ((em p).elim (fun hp => Or.inr (h hp)) (fun hnp => Or.inl hnp))

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p => (fun hp => (em q).elim (fun hq => hq) (fun hnq => absurd hp (h hnq)))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun h : (p → q) → p => (em p).elim (fun hp => hp) (fun hnp => h (fun hp => absurd hp hnp))


example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p => (have hp := h.mpr (fun hp => (h.mp hp) hp)
    (h.mp hp) hp)
