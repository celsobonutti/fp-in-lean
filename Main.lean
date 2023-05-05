import «FpInLean»
import «Anu»

def bufsize : USize := 20 * 1024

partial def dump : IO.FS.Stream → IO Unit
| stream => do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

def fileStream : System.FilePath → IO (Option IO.FS.Stream)
| filename => do
  if not (← filename.pathExists) then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure <| some <| IO.FS.Stream.ofHandle handle

def process : UInt32 → List String → IO UInt32
| exitCode, [] => pure exitCode
| exitCode, "-" :: args => do
  let stdin ← IO.getStdin
  dump stdin
  process exitCode args
| exitCode, filename :: args => do
  match (← fileStream ⟨ filename ⟩) with
  | none =>
    process 1 args
  | some stream =>
    dump stream
    process exitCode args

def help : IO UInt32 := do
  IO.println "Ayuda senor"
  pure 0

def main : List String → IO UInt32
| [] => process 0 ["-"]
| ["--help"] => help
| args => process 0 args
