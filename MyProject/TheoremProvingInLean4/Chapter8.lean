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
