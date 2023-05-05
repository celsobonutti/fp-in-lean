import Std.Data.HashMap.Basic
import FpInLean.Chap4

structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := { x with second := f x.second }

class Monoid' (α : Type) where
  mempty : α
  mconcat : α → α → α

infixl:50 "  <>  " => Monoid.mconcat

instance [Monoid' α] : Applicative (Pair α) where
  pure x := ⟨ Monoid'.mempty, x ⟩
  seq f x := { x () with second :=  f.second (x ()).second }

structure RawInput where
  name : String
  birthYear : String
deriving Repr

structure SubType {α : Type} (p : α → Prop) where
  val : α
  property : p val

def FastPos : Type := { x : Nat // x > 0 }

#eval (⟨ 1, by simp ⟩ : FastPos)

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨ n + 1, by simp_arith ⟩

structure CheckedInput (thisYear : Nat) : Type where
  name : { x : String // x ≠ "" }
  birthYear : { y : Nat // y > 1900 ∧ y ≤ thisYear }
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmpty ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | Validate.ok x => Validate.ok (f x)
    | Validate.errors e => Validate.errors e

instance : Applicative (Validate ε) where
  pure := Validate.ok
  seq f x :=
    match f, x () with
    | .ok f', .ok x' => .ok (f' x')
    | .errors err, .errors err' => .errors (err ++ err')
    | .ok _, .errors e => .errors e
    | .errors err, .ok _ => .errors err

abbrev Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors err => .errors err
  | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen λ birthYearAsNat =>
      checkBirthYear year birthYearAsNat

#eval checkInput 2023 ⟨ "David", "1984" ⟩
#eval checkInput 2023 ⟨ "Carlos", "2024" ⟩

-- inductive List' (α : Type) : Type where
--   | nil : List' α
--   | cons : α → List' α → List' α

-- open List'

-- def List'.map : List' α → (α → β) → List' β
--   | nil, _ => nil
--   | cons a as, f => cons (f a) (as.map f)

-- def List'.append : List' α → List' α → List' α
--   | nil, ys => ys
--   | cons a as, ys => cons a (append as ys)

-- instance : Append (List' α) where
--   append := List'.append

-- def List'.flatten : List' (List' α) → List' α
--   | nil => nil
--   | cons a as => a ++ as.flatten

-- instance : Monad List' where
--   pure x := List'.cons x List'.nil
--   bind x f := (x.map f).flatten

abbrev NonEmptyString := {s : String // s ≠ ""}

abbrev ElemInList α := {v : (α × List α) // v.fst ∈ v.snd}

#eval (⟨ (1, [2, 5, 1]), by simp ⟩ : ElemInList Nat)

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : { y : Nat // y > 999 ∧ y < 1970 }) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : { y : Nat // y > 1970 }) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    .company <$> checkName input.name

infix:50 " :| " => NonEmpty.mk

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε { x : α // p x } :=
  if h : p v then
    .ok ⟨v, h⟩
  else
    .errors (err :| [])

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen λ y =>
    .humanBefore1970 <$>
      checkSubtype y (λ x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
        pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen λ y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput : RawInput → Validate (Field × String) LegacyCheckedInput
  | input => checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"", "1970"⟩

inductive Result (ε α : Type) : Type where
  | ok : α → Result ε α
  | errors : ε → Result ε α
deriving Repr

instance [Append ε] : Applicative (Result ε) where
  pure := .ok
  seq f x :=
    match f, x () with
    | .ok f₁, .ok x₁ => .ok (f₁ x₁)
    | .ok _, .errors x₁ => .errors x₁
    | .errors f₁, .ok _ => .errors f₁
    | .errors f₁, .errors x₁ => .errors (f₁ ++ x₁)

instance [Append ε] : OrElse (Result ε α) where
  orElse fst snd :=
    match fst, snd () with
    | .ok x, _ => .ok x
    | .errors _, .ok x => .ok x
    | .errors e₁, .errors e₂ => .errors (e₁ ++ e₂)

def Result.andThen (val : Result ε α) (next : α → Result ε β) : Result ε β :=
  match val with
  | .errors err => .errors err
  | .ok x => next x

def Result.mapErrors : Result ε α → (ε → ε') → Result ε' α
  | .ok x, _ => .ok x
  | .errors err, f => .errors (f err)

abbrev Path := String

inductive TreeError where
  | field : Field → String → TreeError
  | path : Path → TreeError → TreeError
  | both : TreeError → TreeError → TreeError
deriving Repr

instance : Append TreeError where
  append := .both

def reportErrorTree : Option Path → (Field × String) → Result TreeError α
  | none, (field, error) => .errors (.field field error)
  | some path, (field, error) => .errors (.path path (.field field error))

def TreeError.hasPath : Path → TreeError → Bool
  | _, .field _ _ => false
  | p, .path p₁ _ => p == p₁
  | p, .both t t₁ => t.hasPath p || t₁.hasPath p

-- def TreeError.addError : Path → (Field × String) → TreeError → TreeError
--   | pathName, (fieldName, error), tree@(.field _ _) =>
--     .both (.path pathName (.field fieldName error)) tree
--   | pathName, (fieldName, error), tree@(.path p errors) =>
--     if p == pathName then
--       .path p (.both (.field fieldName error) errors)
--     else
--       .both (.path pathName (.field fieldName error)) tree
--   | pathName, error, tree@(.both p₁ p₂) =>
--     match p₁.hasPath pathName, p₂.hasPath pathName with
--     | true, _ => p₁.addError pathName error
--     | false, true => p₂.addError pathName error
--     | false, false => .both (.path pathName (.field error.fst error.snd)) tree

def verifyThat (condition : Bool) (path : Option Path) (field : Field) (msg : String) : Result TreeError Unit :=
  if condition then pure () else reportErrorTree path (field, msg)

def verifyName (name : String) (path : Option Path) : Result TreeError {n : String // n ≠ ""} :=
  if h : name = "" then
    reportErrorTree path ("name", "Required")
  else pure ⟨name, h⟩

def verifyCompany (input : RawInput) : Result TreeError LegacyCheckedInput :=
  let path := "Company"
  verifyThat (input.birthYear == "FIRM") path "birth year" "FIRM if a company" *>
  .company <$> verifyName input.name path

def verifySubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : TreeError) : Result TreeError { x : α // p x } :=
  if h : p v then
    .ok ⟨v, h⟩
  else
    .errors err

def verifyYearIsNat (year : String) (path : Option Path) : Result TreeError Nat :=
  match year.trim.toNat? with
  | none => reportErrorTree path ("birth year", "Must be digits")
  | some n => pure n

def verifyHumanBefore1970 (input : RawInput) : Result TreeError LegacyCheckedInput :=
  let path := "Before 1970"
  (verifyYearIsNat input.birthYear (some path)).andThen λ y =>
    .humanBefore1970 <$>
      verifySubtype y (λ x => x > 999 ∧ x < 1970) (.path path (.field "birth year" "less than 1970")) <*>
        pure input.name

def verifyHumanAfter1970 (input : RawInput) : Result TreeError LegacyCheckedInput :=
  let path := "After 1970"
  (verifyYearIsNat input.birthYear (some path)).andThen λ y =>
    .humanAfter1970 <$>
      verifySubtype y (· > 1970) (.path path (.field "birth year" "greater than 1970")) <*>
      verifyName input.name path

def verifyLegacyInput : RawInput → Result TreeError LegacyCheckedInput
  | input => verifyCompany input <|> verifyHumanBefore1970 input <|> verifyHumanAfter1970 input

def List.flatMap : (α → List β) → List α → List β
  | _, [] => []
  | f, (x :: xs) => f x ++ xs.flatMap f

def TreeError.collect : TreeError → Std.HashMap String (List (Field × String))
  | .field field' error => Std.HashMap.empty.insert "" [(field', error)]
  | .both p₁ p₂ => Std.HashMap.mergeWith (λ _ x y => x ++ y) p₁.collect p₂.collect
  | .path p errs => Std.HashMap.empty.insert p (errs.collect.toList.flatMap Prod.snd)

def printError : Field × String → String
  | (field, msg) => s!"Field: {field} has an error: {msg}"

def reportPath : (Path × List (Field × String)) → String
  | (path, ls) =>
    let errors := String.intercalate "\n" (ls.map printError)
    s!"PATH: {path}
" ++ errors

def TreeError.report : TreeError → String
  | tree => String.intercalate "\n\n" (tree.collect.toList.map reportPath)

#eval (verifyLegacyInput ⟨"", "FIRM"⟩).mapErrors TreeError.report

#check Prop

example : (n : Nat) → n + 0 = n ∧ n = n + 0 := by simp

inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α

inductive Sum'' (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum'' α β
  | inr : β → Sum'' α β

def stringOrType : Sum'' String Type := .inr Nat

def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
