import FpInLean.Chap4

def andThen : Option α → (α → Option β) → Option β
  | none, _ => none
  | some x, f => f x

infixl:55 " ~~> " => andThen

def firstAndThird [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α) := do
    pure (← lookup xs 0, ← lookup xs 2)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstAndThird (fun xs i => xs[i]?) slowMammals
#eval firstAndThird (fun xs i => xs[i]?) fastBirds

-- def mapM [Monad m] : (α → m β) → List α → m (List β)
--   | _, [] => pure []
--   | f, (x :: xs) =>
--     mapM f xs
--     >>= λ xs' =>
--       f x
--       >>= λ x' =>
--         pure (x' :: xs')

def mapM [Monad m] : (α → m β) → List α → m (List β)
  | _, [] => pure []
  | f, (x :: xs) =>
    f x
    >>= λ x' =>
    mapM f xs
    >>= λ xs' =>
    pure (x' :: xs')

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := λ s => (s, x)
  bind first next :=
    λ s =>
      let (s', x) := first s
      next x s'

def increment : Int → State Int Int
  | n => do
  let s ← get
  set (s + n)
  pure s

#eval mapM increment [1, 2, 3, 4, 5] 0
#eval (increment 5 8)

def Id' (t : Type) : Type := t

instance : Monad Id' where
  pure x := x
  bind x f := f x

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure (BinTree.leaf)
  | BinTree.branch left x right => do
    let x' ← f x
    let left' ← left.mapM f
    let right' ← right.mapM f
    pure (BinTree.branch left' x' right')

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith (special : Type) where
  | plus
  | minus
  | times
  | other : special → Arith special

inductive CanFail where
  | div

abbrev Arith' := (Arith CanFail)

open Expr in
open Arith in
def twoPlusThree : Expr Arith' :=
  prim Arith.plus (const 2) (const 3)

def applyDivOption : CanFail → Int → Int → Option Int
  | CanFail.div, _, 0 => none
  | CanFail.div, x, y => x / y

def applyDivExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, 0 => Except.error (s!"Tried to divide {x} by zero")
  | CanFail.div, x, y => pure (x / y)

def applyEmpty [Monad m] (op : Empty) : Int → Int → m Int :=
  nomatch op

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Arith special → Int → Int → m Int
  | Arith.plus, x, y =>  pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Arith special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
    let v1 ← evaluateM applySpecial e1
    let v2 ← evaluateM applySpecial e2
    applyPrim applySpecial p v1 v2

#eval (evaluateM applyDivOption (Expr.prim Arith.plus (Expr.const 5) (Expr.const 2)))

open Expr Arith in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (λ () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys =>
    Many.more x (λ () => Many.union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (λ () => Many.fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= λ answer =>
          pure (x :: answer))

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else
      Many.one (x / y)

open Expr Arith NeedsSearch

#eval (evaluateM applySearch (prim plus (prim (other choose) (const 1) (const 30)) (prim (other choose) (const 2) (const 5)))).takeAll

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := λ env => env

def Reader.pure (x : α) : Reader ρ α := λ _ => x

def Reader.bind (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  λ env => next (result env) env

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int := do
  let env ← read
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

open Expr Arith in

#eval evaluateM applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def readOption : ReaderOption ρ ρ := λ env => env

def ReaderOption.pure (x : α) : ReaderOption ρ α :=
  λ _ => x

def ReaderOption.bind {α : Type} {ρ : Type} {β : Type}
  (result : ρ → Option α) (next : α → ρ → Option β) : ρ → Option β :=
  λ env => result env >>=
    λ x => next x env

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def applyPrimReaderOption (op : String) (x : Int) (y : Int) : ReaderOption Env Int :=
  readOption >>= λ env =>
    match env.lookup op with
    | none => λ _ => none
    | some f => λ _ => some (f x y)

#eval evaluateM applyPrimReaderOption (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α :=
  λ _ => (Except.ok x)

def ReaderExcept.bind (result : ρ → Except ε α) (next : α → ρ → Except ε β) : ρ → Except ε β :=
  λ env => result env >>=
    λ x => next x env

instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

def readExcept : ReaderExcept ε ρ ρ := λ env => Except.ok env

def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int :=
  readExcept >>= λ env =>
  match env.lookup op with
  | none => λ _ => Except.error s!"Operator not found: {op}"
  | some f => λ _ => Except.ok (f x y)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def WithLog.pure (x : β) : WithLog α β := { log := [], val := x }

def WithLog.bind (x : WithLog α β) (f : β → WithLog α γ) : WithLog α γ :=
  let log := f x.val
  { log := x.log ++ log.log, val := log.val }

instance : Monad (WithLog α) where
  pure := WithLog.pure
  bind := WithLog.bind


inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

def applyTraced : ToTrace (Arith Empty) → Int → Int → WithLog (Arith Empty × Int × Int) Int
  | .trace .plus, x, y => { val := x + y, log := [(Arith.plus, x, y)] }
  | .trace .minus, x, y => { val := x - y, log := [(Arith.minus, x, y)] }
  | .trace .times, x, y => { val := x * y, log := [(Arith.times, x, y)] }

deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Arith

open Expr Arith ToTrace in
#eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))

#print Nat
#print IO
#print Char.isAlpha
