# Instructions for Working on This Project

This is a Lean 4 project using Mathlib.

- Before modifying code, inspect the relevant existing `.lean` files and project structure.
- After every substantive change, run `lake build`.
- Never claim a theorem is verified unless Lean accepts it with no errors.
- Do not use `sorry`, `admit`, `axiom`, or other placeholders unless the user explicitly requests them.
- Prefer existing Mathlib lemmas over reproving standard results.
- When a proof fails, inspect the Lean error message and iteratively repair the proof.
- Keep changes minimal and mathematically faithful to the stated theorem.
- Do not commit or push changes unless the user explicitly asks.

At the end of a task, report:

1. Which files were changed.
2. Which declarations were added or modified.
3. Whether `lake build` succeeds.
4. Any remaining mathematical or Mathlib-related issues.
