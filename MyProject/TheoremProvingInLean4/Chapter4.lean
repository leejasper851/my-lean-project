-- 1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h : ∀ x, p x ∧ q x => ⟨fun x => (h x).left, fun x => (h x).right⟩)
    (fun h : (∀ x, p x) ∧ (∀ x, q x) => (fun x => ⟨h.left x, h.right x⟩))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 : ∀ x, p x → q x => fun h2 : ∀ x, p x => (fun x => (h1 x) (h2 x))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) => (fun x => h.elim
    (fun hap => Or.inl (hap x))
    (fun haq => Or.inr (haq x)))

-- 2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  (fun y : α => Iff.intro
    (fun h : (∀ x : α, r) => h y)
    (fun h : r => (fun x => h)))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h : ∀ x, p x ∨ r => (Classical.em r).elim
      (fun hr => Or.inr hr)
      (fun hnr => Or.inl (fun x => (h x).elim
        (fun hpx => hpx)
        (fun hr => absurd hr hnr))))
    (fun h : (∀ x, p x) ∨ r =>
      (fun x => h.elim
        (fun hap => Or.inl (hap x))
        (fun hr => Or.inr hr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : ∀ x, r → p x => (fun hr => (fun x => h x hr)))
    (fun h : r → ∀ x, p x => (fun x => (fun hr => h hr x)))

-- 3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hsbb := (h barber).mpr (fun hsbb => absurd hsbb ((h barber).mp hsbb))
  absurd hsbb ((h barber).mp hsbb)

-- 4

def even (n : Nat) : Prop := ∃ x, n = 2 * x

def prime (n : Nat) : Prop := ¬∃ x y, x ≥ 2 ∧ y ≥ 2 ∧ n = x * y

def infinitely_many_primes : Prop := ∀ n, ∃ x, prime x ∧ x > n

def Fermat_prime (n : Nat) : Prop := prime n ∧ (∃ n', n = 2 ^ 2 ^ n' + 1)

def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ x, Fermat_prime x ∧ x > n

def goldbach_conjecture : Prop := ∀ n, n > 2 ∧ even n → ∃ p q, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop := ∀ n, n > 5 ∧ ¬even n → ∃ p q r, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop := ¬∃ a b c n, a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a ^ n + b ^ n = c ^ n

-- 5

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  fun hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨y, hpyar⟩ => ⟨Exists.intro y hpyar.left, hpyar.right⟩)
    (fun ⟨⟨y, hpy⟩, hr⟩ => Exists.intro y ⟨hpy, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨y, hpyoqy⟩ => hpyoqy.elim
      (fun hpy => Or.inl (Exists.intro y hpy))
      (fun hqy => Or.inr (Exists.intro y hqy)))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) => h.elim
      (fun ⟨y, hpy⟩ => Exists.intro y (Or.inl hpy))
      (fun ⟨y, hqy⟩ => Exists.intro y (Or.inr hqy)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hap : ∀ x, p x => (fun ⟨y, hnpy⟩ => absurd (hap y) hnpy))
    (fun hnenp : ¬ (∃ x, ¬ p x) => (fun y => (em (p y)).elim
      (fun hpy => hpy)
      (fun hnpy => absurd (Exists.intro y hnpy) hnenp)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨y, hpy⟩ => (fun hanp : ∀ x, ¬ p x => absurd hpy (hanp y)))
    (fun hnanp : ¬ (∀ x, ¬ p x) => byContradiction
      (fun hnep : ¬ (∃ x, p x) => absurd
        (fun y => (em (p y)).elim
          (fun hpy => False.elim (hnep ⟨y, hpy⟩))
          (fun hnpy => hnpy))
        hnanp))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hnep : ¬ ∃ x, p x => (fun y => (em (p y)).elim
      (fun hpy => False.elim (hnep ⟨y, hpy⟩))
      (fun hnpy => hnpy)))
    (fun hanp : ∀ x, ¬ p x => (fun ⟨y, hpy⟩ => absurd hpy (hanp y)))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hnap : ¬ ∀ x, p x => byContradiction
      (fun hnenp : ¬ (∃ x, ¬ p x) => absurd
        (fun y => (em (p y)).elim
          (fun hpy => hpy)
          (fun hnpy => False.elim (hnenp ⟨y, hnpy⟩)))
        hnap))
    (fun ⟨y, hnpy⟩ => (fun hap : ∀ x, p x => absurd (hap y) hnpy))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun haptr : ∀ x, p x → r => (fun ⟨y, hpy⟩ => haptr y hpy))
    (fun heptr : (∃ x, p x) → r => (fun y => (fun hpy => heptr ⟨y, hpy⟩)))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨y, hpytr⟩ => (fun hap : ∀ x, p x => hpytr (hap y)))
    (fun haptr : (∀ x, p x) → r => (em (∀ x, p x)).elim
      (fun hap => ⟨a, fun _ => haptr hap⟩)
      (fun hnap => (em (∃ x, ¬ p x)).elim
        (fun ⟨y, hnpy⟩ => ⟨y, fun hpy => absurd hpy hnpy⟩)
        (fun hnenp => absurd
          (fun y => (em (p y)).elim
            (fun hpy => hpy)
            (fun hnpy => False.elim (hnenp ⟨y, hnpy⟩)))
          hnap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨y, hrtpy⟩ => (fun hr => ⟨y, hrtpy hr⟩))
    (fun hrtep : r → ∃ x, p x => (em r).elim
      (fun hr => let ⟨y, hpy⟩ := hrtep hr
        ⟨y, fun _ => hpy⟩)
      (fun hnr => ⟨a, fun hr => absurd hr hnr⟩))
