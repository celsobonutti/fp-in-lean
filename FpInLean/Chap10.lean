def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.lengthHelper (acc : Nat) : List α → Nat
  | [] => acc
  | _ :: xs => Tail.lengthHelper (1 + acc) xs

def Tail.length : List α → Nat :=
  Tail.lengthHelper 0

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.factorialHelper (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => Tail.factorialHelper (acc * (n + 1)) n

def Tail.factorial : Nat → Nat := Tail.factorialHelper 1

#eval NonTail.factorial 5
#eval Tail.factorial 5

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filterHelper (acc : List α) (f : α → Bool) : List α → List α
  | [] => acc
  | x :: xs => let acc₁ := if f x then acc ++ [x] else acc
               Tail.filterHelper acc₁ f xs

def Tail.filter : (α → Bool) → List α → List α := Tail.filterHelper []

def Nat.even :=
  fun
    | Nat.zero => true
    | Nat.succ x => not (even x)

#eval Tail.filter Nat.even [1, 2, 3, 4, 5]

theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
  (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n
           rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc, Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ m =>
    simp [Add.add]

theorem succ_add : ∀ (x y : Nat), (Nat.succ x) + y = x + (Nat.succ y)
  | _, 0 => by rfl
  | n, m + 1 => congrArg Nat.succ (succ_add n m)

theorem succ_add_rev : ∀ (x y : Nat), Nat.succ (x + y) = Nat.succ x + y
  | _, 0 => by rfl
  | n, m + 1 => congrArg Nat.succ (succ_add_rev n m)

theorem add_succ (n m : Nat) : n + Nat.succ m = Nat.succ (n + m) := by rfl

theorem add_assoc : ∀ (x y z : Nat), (x + y) + z = x + (y + z) := by
  intro x
  induction x with
  | zero =>
    intro y
    intro z
    rw [zero_add (y + z), zero_add y]
  | succ m ih =>
    intro y
    intro z
    simp [succ_add]
    rw [succ_add_rev]
    exact ih (Nat.succ y) z

theorem add_comm : ∀ (x y : Nat), x + y = y + x := by
  intro x
  induction x with
  | zero =>
    simp [zero_add]
  | succ x₁ ih =>
    intro y
    simp [succ_add]
    rw [←succ_add y x₁]
    exact ih (Nat.succ y)

#eval NonTail.reverse [1, 2, 3, 4]
#eval Tail.reverse [1, 2, 3, 4]

theorem tail_reverse_eq_helper_accum (xs : List α) :
  ∀ (xs₁ : List α), NonTail.reverse xs ++ xs₁ = Tail.reverseHelper xs₁ xs := by
  induction xs with
  | nil =>
    intro x
    rfl

  | cons x xs₁ ih =>
    intro xs₂
    simp [NonTail.reverse, Tail.reverseHelper, List.append_assoc]
    exact ih (x :: xs₂)

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  simp [Tail.reverse]
  rw [←List.append_nil (NonTail.reverse xs)]
  exact tail_reverse_eq_helper_accum xs []

theorem factorial_eq_helper_accum (x : Nat) :
  ∀ (y : Nat), NonTail.factorial x * y = Tail.factorialHelper y x := by
  induction x with
  | zero =>
    intro y
    simp [NonTail.factorial, Tail.factorialHelper]
  | succ x₁ ih =>
    intro y
    simp [NonTail.factorial, Tail.factorialHelper]
    rw [Nat.mul_assoc, Nat.mul_comm y (x₁ + 1)]
    exact ih ((x₁ + 1) * y)

theorem non_tail_factorial_eq_tail_factorial : NonTail.factorial = Tail.factorial := by
  funext x
  simp [Tail.factorial]
  rw [←Nat.one_mul (NonTail.factorial x), Nat.mul_comm]
  exact factorial_eq_helper_accum x 1
