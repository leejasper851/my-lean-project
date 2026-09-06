-- 1

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

theorem add_zero (m : Nat) : add m zero = m := rfl

theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add (n : Nat) : add zero n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : add (succ m) n = succ (add m n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : add m n = add n m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : add (add m n) k = add m (add n k) := by
  induction k <;> simp [*, add_zero, add_succ]

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

end Nat

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

open Nat

theorem length_append {α} (xs ys : List α) : length (append xs ys) = add (length xs) (length ys) := by
  induction xs with
  | nil =>
    simp [nil_append, length, zero_add]
  | cons x xs' ih =>
    simp [cons_append, length, succ_add, ih]

theorem length_reverse {α} (xs : List α) : length (reverse xs) = length xs := by
  induction xs with
  | nil =>
    rfl
  | cons x xs' ih =>
    simp [reverse, length_append, ih]
    simp [length, add_succ, add_zero]

theorem reverse_append {α} (xs ys : List α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | nil =>
    simp [nil_append, reverse, append_nil]
  | cons x xs' ih =>
    simp [cons_append, reverse, ih, append_assoc]

theorem reverse_reverse {α} (xs : List α) : reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    rfl
  | cons x xs' ih =>
    rw [reverse, reverse_append, ih, reverse, reverse, nil_append, append, nil_append]

end List

end Hidden

-- 3
