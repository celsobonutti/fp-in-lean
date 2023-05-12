inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  (step (step (step refl)))

def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else
    soFar
termination_by arrayMapHelper _ arr _ i _ => arr.size - i

def Array.map' (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else
      findHelper arr p (i + 1)
  else none
termination_by findHelper arr _ i => arr.size - i

def Array.find' (arr : Array α) (p : α → Bool) : Option (Nat × α) :=
  findHelper arr p 0

def forMHelper [Monad m] (i : Nat) (arr : Array α) (f : α → m PUnit) : m PUnit :=
  if h : i < arr.size then do
    f arr[i]
    forMHelper (i + 1) arr f
  else
    pure ()
termination_by forMHelper i arr f => arr.size - i

def Array.forM' [Monad m] : Array α → (α → m PUnit) → m PUnit :=
  forMHelper 0

def reverseHelper (acc : Array α) (i : Nat) (xs : Array α) : Array α :=
  match i with
    | Nat.zero => acc
    | Nat.succ index =>
      if h : index < xs.size then
        reverseHelper (acc.push xs[index]) index xs
      else
        acc

def Array.reverse' (xs : Array α) : Array α :=
  reverseHelper Array.empty xs.size xs

#eval #[1, 2, 3, 4].reverse'

def Array.map'' (f : α → β) (xs : Array α) : Array β := Id.run do
  let mut ys := #[]
  for x in xs do
    ys := ys.push (f x)
  return ys

def Array.find'' (f : α → Bool) (xs : Array α) : Option (Nat × α) := Id.run do
  let mut i := 0
  for x in xs do
    if f x then
      return some (i, x)
    else
      i := i + 1
  return none

def Array.forM'' [Monad m] (xs : Array α) (f : α → m PUnit) : m PUnit := do
  for x in xs do
    f x

def Array.reverse'' (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for x in xs do
    ys := #[x] ++ ys
  return ys

#eval #[1, 2, 3, 4].reverse''
