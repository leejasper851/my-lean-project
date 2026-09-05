-- 1

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n' => add (mul m n') m

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n' => n'

def trunc_sub (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n' => pred (trunc_sub m n')

def pow (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.succ Nat.zero
  | Nat.succ n' => mul (pow m n') m

end Hidden

-- 2

namespace Hidden

inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) :
    append as nil = as :=
  List.recOn (motive := fun xs => append xs nil = xs) as
    rfl
    (fun x xs' => by simp [cons_append])

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun xs => append (append xs bs) cs = append xs (append bs cs)) as
  rfl
  (fun x xs' => by simp [cons_append])

def length {α} (as : List α) : Nat :=
  match as with
  | nil => Nat.zero
  | cons _ as => Nat.succ (length as)

def reverse {α} (as : List α) : List α :=
  match as with
  | nil => nil
  | cons a as => append (reverse as) (cons a nil)

example {α} (xs ys : List α) : length (append xs ys) = add (length xs) (length ys) := by
  induction ys
  · sorry
  · sorry

example {α} (xs : List α) : length (reverse xs) = length xs := sorry

example {α} (xs : List α) : reverse (reverse xs) = xs := sorry

end List

end Hidden
