# Proof task

Work only in `Solution.lean`. It starts as an exact copy of `Challenge.lean`.

Prove every theorem listed in `config.json`. You may add helper definitions and lemmas to
`Solution.lean`, but do not change the target theorem statements or the definitions used by those
statements. Do not import `Challenge`, and do not use `sorry`, `admit`, new axioms, or unsafe escape
hatches. Do not use the network or retrieve external repositories, solutions, or proof files.

The dLean library source is available under `dLean/Core` and `dLean/Tactic`. Inspect and use it.
Before proving, read and follow `.agents/skills/dlean-prover/SKILL.md`.
Check progress with:

    lake env lean Solution.lean

Finish only after `Solution.lean` compiles and the target theorem has no placeholder.
