/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/
import CheckDecls

unsafe def main (args : List String) : IO UInt32 := CheckDecls.run args
