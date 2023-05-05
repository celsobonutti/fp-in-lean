import Init.Data.Int.Basic

inductive BinaryTree (α : Type) where
  | null : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α
deriving Repr

inductive BinaryTree.Mem (a : α) : BinaryTree α → Prop
  | here (left : BinaryTree α) (right : BinaryTree α) : BinaryTree.Mem a (BinaryTree.node left a right)
  | left (b : α) { left right : BinaryTree α } : BinaryTree.Mem a left → BinaryTree.Mem a (BinaryTree.node left b right)
  | right (b : α) { left right : BinaryTree α } : BinaryTree.Mem a right → BinaryTree.Mem a (BinaryTree.node left b right)

instance : Membership α (BinaryTree α) where
  mem := BinaryTree.Mem

def BinaryTree.depthOf [DecidableEq α] : (x : α) → {xs : BinaryTree α // x ∈ xs} → Nat
  | x, ⟨BinaryTree.node left a right, ok⟩ =>
    if h : x = a then
      0
    else
      let t : Mem x left ∨ Mem x right :=
      match ok with
      | BinaryTree.Mem.here _ _ => nomatch h rfl
      | .left _ t => Or.inl t
      | .right _ t => Or.inr t
      sorry

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
