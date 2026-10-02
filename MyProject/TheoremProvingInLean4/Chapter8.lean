import Mathlib.Tactic

namespace Hidden

-- 1

def add : Nat → Nat → Nat
  | a, 0 => a
  | a, Nat.succ b' => Nat.succ (add a b')

def mul : Nat → Nat → Nat
  | _, 0 => 0
  | a, Nat.succ b' => add (mul a b') a

def pow : Nat → Nat → Nat
  | _, 0 => 1
  | a, Nat.succ b' => mul (pow a b') a

-- 2

def reverse {α} : List α → List α
  | [] => []
  | a :: as => List.append (reverse as) [a]

theorem cons_append {α} (a : α) : ∀ as bs : List α,
    List.append (List.cons a as) bs = List.cons a (List.append as bs)
  | _, _ => rfl

theorem append_assoc {α} : ∀ as bs cs : List α,
    List.append (List.append as bs) cs = List.append as (List.append bs cs)
  | _, _ => by simp

theorem reverse_append {α} : ∀ xs ys : List α,
    reverse (List.append xs ys) = List.append (reverse ys) (reverse xs)
  | [], _ => by simp [reverse]
  | a :: as, _ => by
    rw [cons_append, reverse, reverse_append, append_assoc]
    simp [reverse]

theorem reverse_reverse {α} : ∀ xs : List α, reverse (reverse xs) = xs
  | [] => rfl
  | a :: as => by
    rw [reverse, reverse_append, reverse_reverse, reverse, reverse]
    simp

end Hidden

-- 3

def Nat_below {motive : Nat → Sort u} (n : Nat) := ∀ m, m < n → motive m

def Nat_brecOn {motive : Nat → Sort u} (n : Nat) (F_1 : (n : Nat) → @Nat_below motive n → motive n)
    : motive n := by
  have zero : @Nat_below motive Nat.zero := by
    unfold Nat_below
    intro m
    intro m_lt_0
    contradiction
  let succ (n : Nat) (below_n : @Nat_below motive n) : @Nat_below motive (Nat.succ n) := by
    intro m
    by_cases hmn : m = n
    · intro
      rw [hmn]
      exact F_1 n below_n
    · intro hltns
      have hmltn : m < n := by
        have hmlen := Nat.le_of_lt_succ hltns
        have hmorn := Nat.lt_or_lt_of_ne hmn
        cases hmorn with
        | inl hmltn => exact hmltn
        | inr hnltm =>
          have hnnltm := Nat.le_lt_asymm hmlen
          contradiction
      exact below_n m hmltn
  have hbns := @Nat.rec (@Nat_below motive) zero succ (Nat.succ n)
  apply hbns
  simp

noncomputable def WellFounded_fix {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hmwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)
    (x : α) : C x :=
  let x_acc : Acc r x := WellFounded.apply hmwf x
  let intro := fun (x : α) (_ : ∀ (y : α), r y x → Acc r y)
    (f : (y : α) → (a : r y x) → C y) => F x f
  Acc.rec intro x_acc

-- 4

inductive Vect (α : Type u) : Nat → Type u
  | nil : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

def appendAux : Vect α n1 → Vect α n2 → n1 + n2 = m → Vect α m
  | Vect.nil, v2, h => ((Nat.zero_add n2).symm.trans h) ▸ v2
  | Vect.cons a v1', v2, h => ((Nat.succ_add _ n2).symm.trans h) ▸
      Vect.cons a (appendAux v1' v2 rfl)

def append (v1 : Vect α n1) (v2 : Vect α n2) : Vect α (n1 + n2) :=
  appendAux v1 v2 rfl
