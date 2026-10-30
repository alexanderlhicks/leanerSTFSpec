/-
Copyright (c) 2026 The STFspec Contributors. Licensed under Apache-2.0 OR MIT.
-/

/-!
# Execution entry-kind vocabulary

Library `EthVmRunner`. Project vocabulary for the three specified execution entries.
The execution relation and its meaning remain open; this carrier supplies no runner.
Spec guidance: `STFSpec/informal/modules/EthVmRunner.md` §§3/5/7.
-/

namespace STFSpec.Vm.Runner

/-- The three entry kinds specified for the prospective execution relation. -/
inductive ExecKind
  /-- The opcode loop of one frame (`runFrame`); the `while` loop in pinned EELS
  `process_call`, `src/ethereum/forks/amsterdam/vm/interpreter.py:444–452`. -/
  | frameLoop
  /-- A message call (`processCall`); pinned EELS `process_call`,
  `src/ethereum/forks/amsterdam/vm/interpreter.py:401`. -/
  | call
  /-- A contract creation (`processCreate`); pinned EELS `process_create`,
  `src/ethereum/forks/amsterdam/vm/interpreter.py:330`. -/
  | create

end STFSpec.Vm.Runner
