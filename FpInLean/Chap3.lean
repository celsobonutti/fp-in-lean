import Init.Data.List.Basic

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

inductive Belongs {α : Type} (x : α) : List α → Prop where
| here : {xs : List α} → Belongs x (x :: xs)
| there {y : α} { xs : List α } : Belongs x xs → Belongs x (y::xs)

#check Belongs 1 [1]

theorem onePlusOneIsTwo' : OnePlusOneIsTwo := rfl

#check onePlusOneIsTwo'

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  simp

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp

theorem andImpliesOr : A ∧ B → A ∨ B
| And.intro a _ => Or.inl a

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third [1, 2, 3] (by simp)

#check (rfl : 2 + 3 = 5)
#check (rfl : 15 - 8 = 7)
#check (rfl : "Hello, ".append "world" = "Hello, world")

theorem fst : 2 + 3 = 5 := by simp
theorem snd : 15 - 8 = 7 := by simp
theorem thd : "Hello, ".append "world" = "Hello, world" := by simp
theorem fourth : 5 < 18 := by simp

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]
