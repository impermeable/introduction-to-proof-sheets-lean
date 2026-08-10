/-
  Custom tactics for Waterproof Lean exercise sheets.

  These extend the Verbose library with natural-language tactics that
  fill gaps in the existing automation:

  1. `Contradiction` — matches the Rocq Waterproof style. Closes any goal
     by finding contradictory hypotheses (P and ¬P), then falls back to
     arithmetic contradiction (linarith, omega, nlinarith, ring_nf+omega).

  2. `This is contradictory` — same as `Contradiction` (alias for the
     arithmetic contradiction path, kept for backwards compatibility).

  3. `We conclude by arithmetic` — closes arithmetic goals (equations,
     inequalities) using full-context automation.

  All use natural-language syntax that fits the Verbose style.
  Students never see the implementation (it's in the hidden preamble).
-/

import Verbose.English.All
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Lean Elab Tactic Meta Mathlib.Tactic.Linarith

/-- Collect all propositional hypotheses from the local context. -/
private def collectContextProofs : TacticM (List Expr × Array Term) := do
  let mut prfs : List Expr := []
  let mut prfTerms : Array Term := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if ← isProp ldecl.type then
      prfs := ldecl.toExpr :: prfs
      prfTerms := prfTerms.push (⟨mkIdent ldecl.userName⟩)
  return (prfs, prfTerms)


/--
  `This is contradictory` — closes a `False` goal by trying progressively
  stronger arithmetic tactics with the full local context:
  1. linarith (with all hypotheses)
  2. omega
  3. nlinarith (with all hypotheses)
  4. ring_nf + omega (handles parity contradictions like 2k+1 = 2r)
-/
elab "This" " is contradictory" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let (prfs, prfTerms) ← collectContextProofs
  let state ← saveState
  -- Try linarith with all context
  try
    linarith true prfs
      {preprocessors := defaultPreprocessors, splitNe := true} goal
    return
  catch _ => state.restore
  -- Try omega
  try evalTactic (← `(tactic| omega)); return catch _ => state.restore
  -- Try nlinarith with all context
  try
    evalTactic (← `(tactic| nlinarith [$[$prfTerms:term],*]))
    return
  catch _ => state.restore
  -- Try ring_nf + omega (parity contradictions)
  try
    evalTactic
      (← `(tactic| exfalso; revert $[$prfTerms:term]*; ring_nf; omega))
    return
  catch _ => state.restore
  -- Try subst all equalities, then ring_nf + omega (nonlinear parity)
  try
    evalTactic (← `(tactic| subst_eqs; ring_nf at *; omega))
    return
  catch _ => state.restore
  throwError "Could not derive a contradiction from the hypotheses."

/--
  `Contradiction` — matches the Rocq Waterproof tactic. Closes any goal
  by finding contradictory hypotheses. Tries in order:
  1. Lean's built-in `contradiction` (finds `P` and `¬P`, or `False` in context)
  2. `exfalso` + `contradiction` (when goal isn't `False`)
  3. All arithmetic approaches (linarith, omega, nlinarith, ring_nf+omega)
  4. `exfalso` + arithmetic approaches (when goal isn't `False`)

  Usage: replaces `Since ¬P and P we conclude that False` with just `Contradiction`
-/
private def tryContradictionArithmetic : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let (prfs, prfTerms) ← collectContextProofs
  let state ← saveState
  try
    linarith true prfs
      {preprocessors := defaultPreprocessors, splitNe := true} goal
    return
  catch _ => state.restore
  try evalTactic (← `(tactic| omega)); return catch _ => state.restore
  try
    evalTactic (← `(tactic| nlinarith [$[$prfTerms:term],*]))
    return
  catch _ => state.restore
  try
    evalTactic
      (← `(tactic| exfalso; revert $[$prfTerms:term]*; ring_nf; omega))
    return
  catch _ => state.restore
  try
    evalTactic (← `(tactic| subst_eqs; ring_nf at *; omega))
    return
  catch _ => state.restore
  throwError "Could not derive a contradiction from the hypotheses."

syntax &"Contradiction" : tactic

elab_rules : tactic
  | `(tactic| Contradiction) => do
  let state ← saveState
  -- Try Lean's built-in contradiction (handles P and ¬P)
  try evalTactic (← `(tactic| contradiction)); return catch _ => state.restore
  -- Try exfalso + contradiction (when goal isn't False)
  try evalTactic (← `(tactic| exfalso; contradiction)); return catch _ => state.restore
  -- Try arithmetic contradiction directly
  try tryContradictionArithmetic; return catch _ => state.restore
  -- Try exfalso + arithmetic (when goal isn't False)
  try
    evalTactic (← `(tactic| exfalso))
    tryContradictionArithmetic
    return
  catch _ => state.restore
  throwError "Could not derive a contradiction from the hypotheses."

/--
  `We conclude by arithmetic` — closes arithmetic goals (equations,
  inequalities) by trying progressively stronger tactics:
  1. assumption
  2. linarith (with all hypotheses)
  3. omega
  4. nlinarith (with all hypotheses)
  5. norm_num
-/
elab "We" " conclude by arithmetic" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let (prfs, prfTerms) ← collectContextProofs
  let state ← saveState
  -- Try assumption
  try assumption'; return catch _ => state.restore
  -- Try linarith with all context
  try
    linarith true prfs
      {preprocessors := defaultPreprocessors, splitNe := true} goal
    return
  catch _ => state.restore
  -- Try omega
  try evalTactic (← `(tactic| omega)); return catch _ => state.restore
  -- Try nlinarith with all context
  try
    evalTactic (← `(tactic| nlinarith [$[$prfTerms:term],*]))
    return
  catch _ => state.restore
  -- Try norm_num
  try evalTactic (← `(tactic| norm_num)); return catch _ => state.restore
  throwError "Could not conclude by arithmetic."
