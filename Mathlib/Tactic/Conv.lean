/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathlib.Tactic.RunCmd

/-!
Additional `conv` tactics.
-/

namespace Mathlib.Tactic.Conv
open Lean Parser.Tactic Parser.Tactic.Conv

syntax (name := convLHS) "conv_lhs" (" at " ident)? (" in " (occs)? term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_lhs $[at $id]? $[in $[$occs]? $pat]? => $seq) =>
    `(tactic| conv $[at $id]? $[in $[$occs]? $pat]? => lhs; ($seq:convSeq))

syntax (name := convRHS) "conv_rhs" (" at " ident)? (" in " (occs)? term)? " => " convSeq : tactic
macro_rules
  | `(tactic| conv_rhs $[at $id]? $[in $[$occs]? $pat]? => $seq) =>
    `(tactic| conv $[at $id]? $[in $[$occs]? $pat]? => rhs; ($seq:convSeq))

macro "run_conv" e:doSeq : conv => `(conv| tactic' => run_tac $e)
