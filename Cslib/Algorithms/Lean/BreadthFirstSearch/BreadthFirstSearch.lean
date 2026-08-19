/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Fintype.Card

/-!
TODO: Write docs
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

namespace BFS

-- V is the type of values traversed by the search.
variable {V : Type*} [DecidableEq V]

structure State (V : Type*) [DecidableEq V] where
  queue : Std.Queue V
  seen : Finset V
  reverseOrder : List V -- this is a list of the de-queued vertices (will help with proof)

/-- The initial search state. -/
def initialState (source : V) : State V where
  queue := Std.Queue.enqueue source ⟨[], []⟩
  seen := {source}
  reverseOrder := []

/-- Enqueues an unseen vertex. -/
def discover (state : State V) (v : V) : State V :=
  if v ∈ state.seen then state
  else
    { state with
      queue := Std.Queue.enqueue v state.queue
      seen := insert v state.seen 
    }

/-- Inspects a list of successors from left to right. -/
def inspectNeighbors : List V → State V → TimeM ℕ (State V):=
  fun neighbors => 
    match neighbors with
    | [] => fun state => pure state -- no nbrs 
    | v:: vs => 
      fun state => do 
        ✓ let state := discover state v
        inspectNeighbors vs state


def bfsLoop_alt (succ : V -> List V) (fuel: ℕ) (init_state: State V) : TimeM ℕ (State V):=
  match fuel with 
  | 0 => pure (init_state)
  | fuel + 1 => 
    match init_state.queue.dequeue? with 
    | none => pure init_state 
    | some (v, queue) => do
      TimeM.tick 1 
      let state: State V := {init_state with queue, reverseOrder:= v::init_state.reverseOrder}
      let state <- inspectNeighbors (succ v) state 
      bfsLoop_alt succ fuel state
/-
Given fuel (number of steps to run for), a starting state, 
Return a new State wrapped in a TimeM monad.
-/
def bfsLoop (successors : V → List V) : ℕ → State V → TimeM ℕ (State V) := 
  fun fuel' => match fuel' with
    | 0 => fun init_state => pure init_state
    | fuel + 1 => fun curr_state =>
        match curr_state.queue.dequeue? with
        | none => pure curr_state -- queue is empty, we are done
        | some (v, queue) => do
            ✓ let state : State V := 
              { curr_state with queue, reverseOrder := v :: curr_state.reverseOrder }
            let state ← inspectNeighbors (successors v) state
            bfsLoop successors fuel state
/--
Runs breadth-first search from `source`.
-/
def bfs [Fintype V] (successors : V → List V) (source : V) : TimeM ℕ (List V) := do
  let final ← bfsLoop successors (Fintype.card V) (initialState source)
  return final.reverseOrder.reverse

def bfs_alt [Fintype V] (successors : V → List V) (source : V) : TimeM ℕ (List V) := do
  let final ← bfsLoop_alt successors (Fintype.card V) (initialState source)
  return final.reverseOrder.reverse


end BFS

end Cslib.Algorithms.Lean.TimeM
