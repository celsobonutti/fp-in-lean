import Init.Data.Int.Basic

inductive BinaryTree (α : Type) where
  | null : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α
deriving Repr

-- inductive BinaryTree.Mem (a : α) : BinaryTree α → Prop
--   | here (left : BinaryTree α) (right : BinaryTree α) : BinaryTree.Mem a (BinaryTree.node left a right)
--   | left (b : α) { left right : BinaryTree α } : BinaryTree.Mem a left → BinaryTree.Mem a (BinaryTree.node left b right)
--   | right (b : α) { left right : BinaryTree α } : BinaryTree.Mem a right → BinaryTree.Mem a (BinaryTree.node left b right)

def BinaryTree.Mem (x : α) : BinaryTree α → Prop
  | .null => False
  | .node left y right => x = y ∨ Mem x left ∨ Mem x right

instance : Membership α (BinaryTree α) where
  mem := BinaryTree.Mem

instance Mem.decidable [DecidableEq α] (x : α) : ∀ xs : BinaryTree α, Decidable (x ∈ xs)
  | BinaryTree.null => by
    apply Decidable.isFalse
    simp [Membership.mem, BinaryTree.Mem]
  | BinaryTree.node left y right =>
    if h : x = y then
      isTrue <| by
        constructor
        exact h
    else by
      have := Mem.decidable x left
      have := Mem.decidable x right
      have : (x ∈ left ∨ x ∈ right) ↔ (x ∈ BinaryTree.node left y right) := by
        simp [(· ∈ ·), BinaryTree.Mem, h]
      exact decidable_of_decidable_of_iff this

theorem Or.elimLeft (xs : α ∨ β) (x: ¬α) : β :=
  match xs with
  | Or.inl y => absurd y x
  | Or.inr b => b

def BinaryTree.depthOf [DecidableEq α] [BEq α] : (x : α) → {xs : BinaryTree α // x ∈ xs} → Nat
  | x, ⟨BinaryTree.node left a right, ok⟩ =>
    if here : x = a then
      0
    else
      if l : x ∈ left then
        if r : x ∈ right then
          1 + (min (BinaryTree.depthOf x ⟨ left, l ⟩) (BinaryTree.depthOf x ⟨ right, r ⟩))
        else
          1 + BinaryTree.depthOf x ⟨ left, l ⟩
      else
        1 + BinaryTree.depthOf x ⟨ right, (ok.elimLeft here).elimLeft l ⟩

open BinaryTree in
def tree := node (node null 2 (node null 10 (node null 1 null))) 5 (node null 9 (node null 8 (node null 25 null)))


open BinaryTree in
def BinaryTree.size : BinaryTree α → Nat
  | null => 0
  | node left _ right => 1 + left.size + right.size

def BinaryTree.depth : BinaryTree α → Nat
  | null => 0
  | node left _ right => 1 + max left.size right.size

#eval (BinaryTree.node BinaryTree.null 1 (BinaryTree.node BinaryTree.null 2 (BinaryTree.node BinaryTree.null 3 BinaryTree.null))).depth

def Node : BinaryTree α → α → BinaryTree α → BinaryTree α := BinaryTree.node
def Null : BinaryTree α := BinaryTree.null

def BinaryTree.leaves : BinaryTree α → List α
  | BinaryTree.null => []
  | BinaryTree.node BinaryTree.null x BinaryTree.null => [x]
  | BinaryTree.node left _ right => left.leaves ++ right.leaves

#eval (Node (Node Null 1 Null) 2 (Node Null 3 Null)).leaves
#eval (Node Null 1 (Node Null 2 (Node Null 3 Null))).leaves

def BinaryTree.map : (α → β) → BinaryTree α → BinaryTree β
  | _, BinaryTree.null => BinaryTree.null
  | f, BinaryTree.node left x right =>
    BinaryTree.node (map f left) (f x) (map f right)

instance : Functor BinaryTree where
  map := BinaryTree.map

def BinaryTree.elem : Int → BinaryTree Int → Bool
  | _, BinaryTree.null => False
  | x, BinaryTree.node left x' right =>
    x == x' || left.elem x || right.elem x

def BinaryTree.maximum : BinaryTree Int → Int
  | BinaryTree.null => 0
  | BinaryTree.node left x right => max (max left.maximum x) right.maximum

def BinaryTree.minimum : BinaryTree Int → Int
  | BinaryTree.null => 0
  | BinaryTree.node left x right => min (min left.minimum x) right.minimum

def BinaryTree.flatten : BinaryTree α → List α
  | BinaryTree.null => []
  | BinaryTree.node left x right => left.flatten ++ [x] ++ right.flatten

#eval (Node Null 1 (Node Null 2 (Node Null 3 Null))).flatten

inductive RoseTree (α : Type) where
  | node : α → List (RoseTree α) → RoseTree α
deriving Repr

partial def RoseTree.size : RoseTree α → Int
  | RoseTree.node _ xs =>
    1 + (xs.map RoseTree.size).foldl (· + ·) 0

#eval (RoseTree.node 1 [RoseTree.node 2 [], RoseTree.node 3 [RoseTree.node 4 []]]).size

partial def RoseTree.leaves : RoseTree α → List α
  | RoseTree.node x [] => [x]
  | RoseTree.node _ ys => (ys.map RoseTree.leaves).foldl (· ++ ·) []

inductive Direction where
  | right
  | left

inductive Rotation where
  | none : Rotation
  | single : Direction → Rotation
  | double: Direction → Rotation

def necessaryRotation : BinaryTree α → BinaryTree α → Rotation
  | x, y =>
    let sizeDifference := (x.depth : Int) - (y.depth : Int)
    if [-1, 0, 1].elem sizeDifference then
      Rotation.none
    else
      Rotation.none

def BinaryTree.balance : BinaryTree α → BinaryTree α
  | BinaryTree.null => BinaryTree.null
  | BinaryTree.node left x right =>
    match necessaryRotation left right with
      | Rotation.none => BinaryTree.node left x right
      | Rotation.single Direction.right => BinaryTree.node left x right
      | Rotation.single Direction.left => BinaryTree.node left x right
      | Rotation.double Direction.right => BinaryTree.node left x right
      | Rotation.double Direction.left => BinaryTree.node left x right
