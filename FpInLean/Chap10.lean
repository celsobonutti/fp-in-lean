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
  | 0 => 1 * acc
  | 5 => 2
  | n + 1 => Tail.factorialHelper (acc * n) n

def Tail.factorial (x : Nat) : Nat := Tail.factorialHelper x x

#eval NonTail.factorial 5
#eval Tail.factorial 5
