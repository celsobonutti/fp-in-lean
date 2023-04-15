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

def Even'.toNat : Even' → Nat
| Even'.zero => 0
| Even'.succ (Odd'.succ m) => 2 + toNat m

def four := Even'.succ (Odd'.succ (Even'.succ (Odd'.succ Even'.zero)))

instance : Add Even' where
  add := Even'.add

instance : ToString Even' where
  toString := toString ∘ Even'.toNat

#eval (four + Even'.succ (Odd'.succ four))

def Even'.mul : Even' → Even' → Even'
| Even'.zero, m => Even'.zero
| Even'.succ (Odd'.succ n), m => m + m + (n.mul m)

instance : Mul Even' where
  mul := Even'.mul

#eval (four * four)
