def hello := "world"

def joinStringsWith (sep : String) (first : String) (second : String) :=
  String.join [first, sep, second]

def joinStringsWith' : String → String → String → String := λ sep first second =>
  String.join [first, sep, second]

#eval joinStringsWith ", " "one" "and another"

def volume : Nat → Nat → Nat → Nat := λ height width depth =>
  width * depth * height

structure Point where
  point ::
  x : Float
  y : Float
deriving Repr

def fourAndThree : Point := { x := 4.3, y := 3.4 }

def Point.modifyBoth : (Float → Float) → Point → Point := λ f p =>
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

#eval origin.x

def addPoints : Point → Point → Point := λ p1 p2 =>
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance : Point → Point → Float := λ p1 p2 =>
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

def zeroX : Point → Point := λ p =>
  { p with x := 0 }

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def RectangularPrism.volume : RectangularPrism -> Float := λ prism =>
  prism.width * prism.depth * prism.height

structure Segment where
  startPoint : Point
  endPoint : Point
deriving Repr

def Segment.length : Segment → Float := λ seg =>
  distance seg.startPoint seg.endPoint

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'

def isZero : Nat → Bool :=
  fun
    | Nat.zero => true
    | Nat.succ _ => false

def pred : Nat → Nat :=
  fun
    | Nat.zero => Nat.zero
    | Nat.succ x => x


def Point3D.depth : Point3D → Float :=
  fun
    | { z, .. } => z

def even : Nat → Bool :=
  fun
    | Nat.zero => true
    | Nat.succ x => not (even x)

def plus : Nat → Nat → Nat := λ n m =>
  match m with
  | Nat.zero => n
  | Nat.succ m' => Nat.succ (plus n m')

inductive Either (α : Nat) β where
  | left : Nat → Either α β
  | right : β → Either α β

#check Either (5 : Nat)
#check (Either 9 Nat)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Float :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (3 : Float)

inductive List' (α : Type) where
  | nil : List' α
  | cons : α → List' α → List' α

def length : { α : Type } → List α → Nat :=
  fun
  | List.nil => Nat.zero
  | List.cons _ ls => Nat.succ (length ls)

inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)
  deriving Repr

def fromList : (xs : List α) -> Vector α (List.length xs) :=
  fun
  | [] => Vector.nil
  | x :: xs => Vector.cons x (fromList xs)

def vectLength { α : Type u } { length : Nat } (_ : Vector α length) : Nat :=
  length

#eval (fromList [1, 2, 3, 4])
#eval (vectLength <| fromList <| [1, 2, 3, 4])

inductive Maybe (α : Type) : Type where
  | nothing : Maybe α
  | just : α → Maybe α

def Maybe.withDefault : α → Maybe α → α := λ f =>
  fun
  | nothing => f
  | just x => x

#eval (Maybe.just 5).withDefault 4
#eval Maybe.nothing.withDefault 4

def Vector.head : { n : Nat} → Vector α (Nat.succ n) → α :=
  fun
  | Vector.cons x _ => x


structure Prod' (α : Type) (β : Type) : Type where
  fst : α
  snd : β

def fives : String × Int := ("five", 5)

inductive Sum' (α : Type) (β : Type) : Type where
  | inl : α → Sum' α β
  | inr : β → Sum' α β

def nOrLength : Nat ⊕ String → Nat :=
  fun
  | Sum.inl n => n
  | Sum.inr s => s.length

-- Exercises : Polymorphism

def last : {α : Type} → List α → Maybe α :=
  fun
  | [] => Maybe.nothing
  | x :: [] => Maybe.just x
  | _ :: xs => last xs

def List.findFirst? : { α : Type } → List α → (α → Bool) → Maybe α :=
  λ xs pred =>
  match xs with
  | [] => Maybe.nothing
  | x :: xs => if pred x then Maybe.just x else xs.findFirst? pred

def Prod.swap : α × β → β × α :=
  fun
  | (x, y) => (y, x)

inductive Pet where
  | dog : String → Pet
  | cat : String → Pet

def zip : List α → List β → List (α × β)
  | List.cons x xs', List.cons y ys' => (x, y) :: (zip xs' ys')
  | _, _ => []

def take : List α → Nat → List α
  | x :: xs, Nat.succ n => x :: xs.take n
  | _, _ => []

def distrib : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | (x, Sum.inl y) => Sum.inl (x, y)
  | (x, Sum.inr z) => Sum.inr (x, z)

def mulBy2 : Bool × α → α ⊕ α
  | (false, x) => Sum.inl x
  | (true, x) => Sum.inr x

#check (⟨1, 2⟩ : Point)

structure Sigma' (α : Type) (β : α → Type) where
  fst : α
  snd : β fst

def Test (b : Bool) : Type := if b then Nat else String

def test : Sigma' Bool Test := Sigma'.mk True (5 : Nat)
def test2 : Sigma' Bool Test := Sigma'.mk False "test"

structure Trigma (α : Type) (β : α → Type) (γ : (x : α) → β x → Type) where
  fst : α
  snd : β fst
  thr : γ fst snd
