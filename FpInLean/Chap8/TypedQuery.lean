inductive DBType where
  | int | string | bool
deriving BEq

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

#eval ("Mount Hood" : DBType.string.asType)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema := [
  ⟨"name", DBType.string⟩,
  ⟨"location", DBType.string⟩,
  ⟨"elevation", DBType.int⟩,
  ⟨"lastVisited", .int⟩
]

def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]

abbrev travelDiary : Schema := [
  ⟨"name", .string⟩
]

def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
    | [] => true
    | [_] => r1 == r2
    | _ :: _ :: _ =>
      match r1, r2 with
        | (v1, r1'), (v2, r2') =>
          v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

def x : HasCol peak "elevation" DBType.int :=
  .there (.there .here)

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
    | [_], .here, v => v
    | _ :: _ :: _, .here, (v, _) => v
    | _ :: _ :: _, .there col, (_, v) => get v col

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger

example : Subschema [] peak := by constructor

example : Subschema [⟨"location", .string⟩] peak := by repeat constructor

example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor

def Subschema.addColumn : Subschema smaller bigger → Subschema smaller (c :: bigger)
  | .nil => .nil
  | .cons col sub => .cons (.there col) sub.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | .nil => .nil
  | .cons _ xs => .cons .here (reflexive xs).addColumn

def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)

inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e₁ e₂ : DBExpr s t) : DBExpr s .bool
  | lt (e₁ e₂ : DBExpr s .int) : DBExpr s .bool
  | and (e₁ e₂ : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e₁ e₂ => evaluate row e₁ == evaluate row e₂
  | .lt e₁ e₂ => evaluate row e₁ < evaluate row e₂
  | .and e₁ e₂ => evaluate row e₁ && evaluate row e₂
  | .const v => v

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => { c with name := n' } :: cs
  | _ :: cs, .there col, n' => Schema.renameColumn cs col n'

inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
  | project : Query s → (s' : Schema) → Subschema s s' → Query s'
  | product :
    Query s₁ → Query s₂ →
    disjoint (s₁.map Column.name) (s₂.map Column.name) →
    Query (s₁ ++ s₂)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) → !((s.map Column.name).contains n') →
      Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map λ c => {c with name := n ++ "." ++ c.name})
