import FpInLean.Chap4

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

def Vect.toList : Vect α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList

instance [ToString α] : ToString (Vect α n) where
  toString := toString ∘ Vect.toList


def Vect.fromList : (x : List α) → Vect α x.length
  | [] => nil
  | x :: xs => cons x (Vect.fromList xs)

instance : CoeDep (List α) x (Vect α x.length) where
  coe := Vect.fromList x

def List.flatten : List (List α) → List α
  | [] => []
  | x :: xs => x ++ xs.flatten

#check (Vect.fromList [1, 2, 3])

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (Vect.zip xs ys)

def Vect.map : (α → β) → Vect α n → Vect β n
  | _, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)

def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | _, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (Vect.zipWith f xs ys)

def Vect.unzip : Vect (α × β) n → (Vect α n × Vect β n)
  | .nil => (.nil, .nil)
  | .cons (x, y) v =>
    let (xs, ys) := v.unzip
    (.cons x xs, .cons y ys)

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons x xs, x₁ => .cons x (xs.snoc x₁)

#eval (Vect.fromList [1, 2, 3, 4, 5]).snoc 6

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.snoc x

#eval (Vect.fromList [1, 2, 3, 4]).reverse

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons x xs => xs.drop n

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, xs => .nil
  | n + 1, .cons x xs => .cons x (xs.take n)

inductive Finite where
  | empty : Finite
  | unit : Finite
  | bool : Finite
  | option : Finite → Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .empty => Empty
  | .option t => Option t.asType
  | .unit => Unit
  | .bool => Bool
  | .pair t₁ t₂ => asType t₁ × asType t₂
  | .arr t₁ t₂ => asType t₁ → asType t₂

def List.product' (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .empty => []
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product' t2.enumerate
    | .arr t1 t2 => t1.functions t2.enumerate
    | .option t => .none :: t.enumerate.map .some


  def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
    match t with
    | .empty => []
    | .unit => results.map λ r => const r
    | .bool => (results.product' results).map λ (r₁, r₂) =>
      λ
        | true => r₁
        | false => r₂
    | .option t₁ => sorry
    | .pair t₁ t₂ =>
      let f₁s := t₁.functions <| t₂.functions results
      f₁s.map λ f =>
        λ (x, y) => f x y
    | .arr t₁ t₂ =>
      let args := t₁.enumerate
      let base :=
        results.map λ r => λ _ => r
      let fn arg rest :=
        (t₂.functions rest).map
            λ more =>
              λ f => more (f arg) f
      args.foldr fn base
end

def Finite.beq : (t : Finite) → t.asType → t.asType → Bool
  | .empty, _, _ => false
  | .unit, _, _ => true
  | .option t, .some x, .some y => beq t x y
  | .option _, .none, .none => true
  | .option _, _, _ => false
  | .bool, x, y => x == y
  | .pair t₁ t₂, (x₁, y₁), (x₂, y₂) => beq t₁ x₁ x₂ && beq t₂ y₁ y₂
  | .arr t₁ t₂, x, y =>
    t₁.enumerate.all λ arg => beq t₂ (x arg) (y arg)

def List.index [DecidableEq α] : (x : α) → {xs : List α // x ∈ xs} → Nat
  | x, ⟨a :: xs, ok⟩ =>
    if h : x = a then
      0
    else
      have t : Mem x xs :=
        match ok with
        | List.Mem.head _ => nomatch h rfl
        | List.Mem.tail _ t => t
      1 + List.index x ⟨xs, t⟩

#check List.index 2 ⟨[1, 2, 3], by simp⟩

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_zero_left k)

def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)

def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
