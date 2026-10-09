import Comparator
import Export.Parse

-- Standalone native driver for the maintained comparator APIs; the primitive
-- list is identical to Main.lean at d03acab154d269c06e60e4de7e4cc85deebff94b.
def main : IO Unit := do
  let challenge := (← IO.getEnv "AUDIT_CHALLENGE").getD ""
  let solution := (← IO.getEnv "AUDIT_SOLUTION").getD ""
  let theoremName := (← IO.getEnv "AUDIT_THEOREM").getD ""
  let ch ← IO.FS.Handle.mk challenge .read
  let sh ← IO.FS.Handle.mk solution .read
  let c ← Export.parseStream (IO.FS.Stream.ofHandle ch)
  let s ← Export.parseStream (IO.FS.Stream.ofHandle sh)
  let axioms := #[`propext, `Quot.sound, `Classical.choice]
  let targets := #[theoremName.toName]
  let primitives := #[`Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div,
    `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft,
    `Nat.shiftRight, `String.ofList, `Char.ofNat, `List, `eagerReduce, `Nat,
    `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam]
  IO.ofExcept <| Comparator.compareAt c s (targets ++ axioms) #[] primitives
  IO.ofExcept <| Comparator.checkAxioms s targets #[] axioms
  IO.println s!"PASS: compiled statement, definition closure, axiom allowlist: {theoremName}"
