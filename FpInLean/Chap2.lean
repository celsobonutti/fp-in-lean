def fn : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be adressed?"
  let input <- stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def twice : IO Unit → IO Unit
  | action => do
    action
    action

def nTimes : IO Unit → Nat → IO Unit
  | _, 0 => pure ()
  | action, n + 1 => do
    action
    nTimes action n

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions =>
    act >>= λ _ => runActions actions

def doNotation : Except α β → (β → γ) → Except α γ := λ x f => do
  let y ← x
  let z := f y
  pure z

#eval "Hello!!!!".dropRightWhile (· == '!')
