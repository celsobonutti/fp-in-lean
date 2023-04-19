inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := (· + ·)

open Plus (plus)

#eval plus 2 4

def Pos.plus : Pos → Pos → Pos
| Pos.one, n => Pos.succ n
| Pos.succ m, n => Pos.succ (m.plus n)

instance : Plus Pos where
  plus := Pos.plus

instance : Add Pos where
  add := Pos.plus

def Pos.toNat : Pos → Nat
| Pos.one => 1
| Pos.succ m => 1 + m.toNat

instance : ToString Pos where
  toString := toString ∘ Pos.toNat

def Pos.mul : Pos → Pos → Pos
| Pos.one, n => n
| Pos.succ m, n => n + (m.mul n)

instance : Mul Pos where
  mul := Pos.mul

#eval (Pos.succ Pos.one) + (Pos.succ (Pos.succ (Pos.one)))
#eval (Pos.succ Pos.one) * (Pos.succ (Pos.succ Pos.one))

instance : OfNat Pos (Nat.succ m) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | Nat.succ n => Pos.succ (natPlusOne n)
    natPlusOne m

#eval (5 : Pos) * (10 : Pos)

structure Pos' where
  succ ::
  pred : Nat

def Pos'.add : Pos' → Pos' → Pos'
| { pred := 0 }, n => Pos'.succ (n.pred + 1)
| { pred := Nat.succ m }, n =>  Pos'.succ <| ((Pos'.succ 0).add ((Pos'.succ m).add n)).pred

def Pos'.toNat : Pos' → Nat :=
  (· + 1) ∘ Pos'.pred

instance : ToString Pos' where
  toString := toString ∘ Pos'.toNat

instance : Add Pos' where
  add := Pos'.add

def Pos'.mul : Pos' → Pos' → Pos'
| { pred := 0 }, n => n
| { pred := Nat.succ m }, n => n + (({ pred := m } : Pos').mul n)

instance : Mul Pos' where
  mul := Pos'.mul

#eval (Pos'.succ 4) + (Pos'.succ 8) -- Should be 14
#eval (Pos'.succ 2) * (Pos'.succ 8) -- Should be 27
#eval (Pos'.succ 4) * (Pos'.succ 8) -- Should be 45

instance : OfNat Pos' (Nat.succ m) where
  ofNat := Pos'.succ m

#eval (2 : Pos')
#eval (2 + 5 : Pos')

mutual
  inductive Even' : Type where
  | zero : Even'
  | succ : Odd' → Even'

  inductive Odd' : Type where
  | succ : Even' → Odd'
end

def Even'.add : Even' → Even' → Even'
| Even'.zero, m => m
| Even'.succ (Odd'.succ n), m => Even'.succ (Odd'.succ (n.add m))

mutual
  def Even'.toNat : Even' → Nat
  | Even'.zero => 0
  | Even'.succ m => 1 + m.toNat

  def Odd'.toNat : Odd' → Nat
  | Odd'.succ n => 1 + n.toNat
end

def four := Even'.succ (Odd'.succ (Even'.succ (Odd'.succ Even'.zero)))

instance : Add Even' where
  add := Even'.add

instance : ToString Even' where
  toString := toString ∘ Even'.toNat

instance : ToString Odd' where
  toString := toString ∘ Odd'.toNat

#eval (four + Even'.succ (Odd'.succ four))

def Even'.mul : Even' → Even' → Even'
| Even'.zero, _ => Even'.zero
| Even'.succ (Odd'.succ n), m => m + m + (n.mul m)

instance : Mul Even' where
  mul := Even'.mul

#eval (four * four)

#check @IO.println

def List.sum [Add α] [OfNat α 0] : List α → α
| [] => 0
| x :: xs => x + xs.sum

#check @OfNat.ofNat
#check (OfNat.ofNat 5 : Pos)

instance : OfNat Even' (Nat.zero) where
  ofNat := Even'.zero

instance [OfNat Even' n]: OfNat Odd' (Nat.succ n) where
  ofNat := Odd'.succ (OfNat.ofNat n)

instance [OfNat Odd' n]: OfNat Even' (Nat.succ n) where
  ofNat := Even'.succ (OfNat.ofNat n)

#check (5 : Odd')
#check (6 : Even')

def Odd'.add : Odd' → Odd' → Even'
| Odd'.succ m, Odd'.succ n => Even'.succ (Odd'.succ (m + n))


instance : HAdd Even' Odd' Odd' where
  hAdd
  | Even'.zero, p => p
  | Even'.succ m, p => Odd'.succ (m.add p)

instance : HAdd Odd' Even' Odd' where
  hAdd
  | n, m => m + n

#eval ((8 : Even') + (5 : Odd') : Odd')
#eval ((5 : Odd') + (8 : Even') )

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := flip addNatPos

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := flip addNatPos

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p n :=
    ⟨ p.x * n, p.y * n ⟩

#eval { x := 2.5, y := 3.7 : PPoint Float } * 2.0

def northernTrees : Array String :=
  #["beech", "birch", "elm", "oak"]

structure NonEmpty (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmpty String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmpty α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

abbrev NonEmpty.inBounds (xs : NonEmpty α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmpty.length : NonEmpty α → Nat
  | xs => xs.tail.length + 1

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by simp
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by simp

def NonEmpty.get (xs : NonEmpty α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmpty α) Nat α NonEmpty.inBounds where
  getElem := NonEmpty.get

#eval idahoSpiders[1]

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

deriving instance BEq for Pos
deriving instance Repr for NonEmpty

#check compare (5 : Pos) (2 : Pos)

def hashPos : Pos → UInt64
| Pos.one => 0
| Pos.succ n => mixHash 1 (hashPos n)

instance [Hashable α] : Hashable (NonEmpty α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

instance : Append (NonEmpty α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmpty α) (List α) (NonEmpty α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["memes"]

instance : Functor NonEmpty where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

instance : HAppend (List α) (NonEmpty α) (NonEmpty α) where
  hAppend
  | h :: t, nonEmpty => { head := h, tail := t ++ nonEmpty.head :: nonEmpty.tail }
  | [], nonEmpty => nonEmpty

#eval ([1, 2, 3] ++ { head := 1, tail := [4, 5, 6] : NonEmpty Nat } : NonEmpty Nat)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

deriving instance BEq, Hashable, Repr for BinTree

def BinTree.bmap : (α → β) → BinTree α → BinTree β
  | _, BinTree.leaf => BinTree.leaf
  | f, BinTree.branch left value right => BinTree.branch (left.bmap f) (f value) (right.bmap f)

instance : Functor BinTree where
  map := BinTree.bmap

def binTree := BinTree.branch (BinTree.branch BinTree.leaf 5 BinTree.leaf) 5 BinTree.leaf

#eval ToString.toString <$> binTree

#eval [1, 2, 3, 4].drop 2

instance : Coe Pos Nat where
  coe := Pos.toNat

#check [1, 2, 3, 4].drop (2 : Pos)

def oneInt : Int := Pos.one

inductive A where
  | a

inductive B where
  | b

def const : α → β → α
  | x, _ => x

instance : Coe A B where
  coe := const B.b

instance : Coe B A where
  coe := const A.a

instance : Coe Unit A where
  coe := const A.a

def coercedToB : B := ()

def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

instance : CoeDep (List α) (x :: xs) (NonEmpty α) where
  coe := { head := x, tail := xs }

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }


def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap' (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

structure Adder where
  howMuch : Nat

def memes : Option String := "memes"
#eval memes

def add5 : Adder := ⟨5⟩

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object
    [ ("title", JSON.string title)
    , ("status", JSON.number 200)
    , ("record", R record)
    ]

example : NonEmpty String :=
  ["memes"]

example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
