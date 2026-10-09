import Export.Parse
import Lean

def runKernel (solution : Export.ExportedEnv) : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Adding `Quot` also creates `Quot.mk`, `Quot.lift`, and `Quot.ind`.
  -- Remove their exported entries to avoid adding the primitives twice.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.toKernelEnv.replay constMap
  IO.println s!"Accepted {constMap.size} declarations."


def main (args : List String) : IO Unit := do
  let (inputPath, parseOnly) ← match args with
    | ["--parse-only", inputPath] => pure (inputPath, true)
    | [inputPath] => pure (inputPath, false)
    | _ => throw <| .userError "Usage: kernel [--parse-only] INPUT"
  let handle ← IO.FS.Handle.mk inputPath .read
  let env ← Export.parseStream (.ofHandle handle)
  if parseOnly then
    IO.println "Parse successful."
  else
    runKernel env
