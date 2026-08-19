/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

module

public import Cslib.Algorithms.Lean.BreadthFirstSearch.BreadthFirstSearch
public import Cslib.Algorithms.Lean.BreadthFirstSearch.NoDup
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import all Init.Data.Queue

/-!
TODO: docs
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped BigOperators

namespace BFS

variable {V : Type*}

variable [DecidableEq V]

/-- The total number of entries produced by the successor enumeration. -/
def entries [Fintype V] (successors : V → List V) : ℕ :=
  ∑ v, (successors v).length

/-- The total ticks accounted for by a dequeue-order: one per vertex dequeued, plus the
length of each of their successor lists. -/
abbrev cost (succ : V -> List V) (order : List V) : ℕ :=
  order.length + (order.map fun v => (succ v).length).sum

omit [DecidableEq V] in
theorem cost_cons (succ : V -> List V) (v : V) (order : List V) :
    cost succ (v :: order) = cost succ order + 1 + (succ v).length := by
  unfold cost
  rw [List.length_cons, List.map_cons, List.sum_cons]
  omega

-- reversing a dequeue-order changes neither its length nor the sum of the
-- successor-list lengths of its vertices
omit [DecidableEq V] in
theorem cost_reverse (succ : V -> List V) (order : List V) :
    cost succ order.reverse = cost succ order := by 
    simp only [cost]
    have h_rev: order.reverse.length = order.length := by exact List.length_reverse
    rw [h_rev]
    congr 1
    /- simp only [List.Perm.sum_eq] -/
    rw [List.map_reverse]
    exact List.sum_reverse_nat (List.map (fun v => (succ v).length) order)

theorem discover_same_order (state : State V) (v : V) :
    (discover state v).reverseOrder = state.reverseOrder := by
  unfold discover
  split_ifs <;> rfl

-- Inspecting neighbours costs time exactly equal to the number of neighbours.
theorem scan_time_eq_length (xs : List V) (state : State V) :
    (inspectNeighbors xs state).time = xs.length := by
  induction xs generalizing state with
  | nil =>
      simp only [inspectNeighbors, pure, TimeM.pure]
      rfl
  | cons v vs ih =>
    simp only [inspectNeighbors, bind, TimeM.bind, tick]
    rw [ih, Nat.add_comm _ _]
    simp only [List.length_cons]

-- Scanning the neighbours does not affect the list of dequeued vertices.
theorem scan_same_order (xs : List V) (state : State V) :
    (inspectNeighbors xs state).ret.reverseOrder = state.reverseOrder := by
  induction xs generalizing state with
  | nil => rfl
  | cons v vs ih =>
    simp only [inspectNeighbors, bind, TimeM.bind, ih]
    exact discover_same_order _ _

theorem bfsLoop_alt_cost (succ : V -> List V) (fuel : ℕ) (state : State V) :
    (bfsLoop_alt succ fuel state).time + cost succ state.reverseOrder =
      cost succ (bfsLoop_alt succ fuel state).ret.reverseOrder := by
  induction fuel generalizing state with
  | zero =>
      simp only [bfsLoop_alt, pure, TimeM.pure, Nat.zero_add]
  | succ fuel ih =>
      simp only [bfsLoop_alt]
      cases hdequeue : state.queue.dequeue? with
      | none =>
          simp only [pure, TimeM.pure, Nat.zero_add]
      | some pair =>
          rcases pair with ⟨v, remQ⟩
          simp only [tick, bind, TimeM.bind]
          -- First record the state immediately after dequeueing `v`.
          let dequeuedState : State V :=
            { state with
              queue := remQ
              reverseOrder := v :: state.reverseOrder }
          -- Then record the state after inspecting all successors of `v`.
          let inspectedState : State V :=
            (inspectNeighbors (succ v) dequeuedState).ret
          have hInspectionTime :
              (inspectNeighbors (succ v) dequeuedState).time = (succ v).length :=
            scan_time_eq_length (succ v) dequeuedState
          have hInspectionOrder :
              inspectedState.reverseOrder = v :: state.reverseOrder := by
            calc
              inspectedState.reverseOrder
                  = dequeuedState.reverseOrder := scan_same_order (succ v) dequeuedState
              _ = v :: state.reverseOrder := rfl
          have hRemainingCost :
              (bfsLoop_alt succ fuel inspectedState).time +
                  cost succ inspectedState.reverseOrder =
                cost succ (bfsLoop_alt succ fuel inspectedState).ret.reverseOrder :=
            ih inspectedState
          calc
            1 + ((inspectNeighbors (succ v) dequeuedState).time +
                  (bfsLoop_alt succ fuel inspectedState).time) +
                cost succ state.reverseOrder =
              (bfsLoop_alt succ fuel inspectedState).time +
                cost succ inspectedState.reverseOrder := by
                  rw [hInspectionTime, hInspectionOrder, cost_cons]
                  omega
            _ = cost succ (bfsLoop_alt succ fuel inspectedState).ret.reverseOrder :=
              hRemainingCost

theorem alt_time_eq_cost [Fintype V] (succ : V -> List V) (source : V) :
    let timeMonad := bfs_alt succ source
    let final_list := timeMonad.ret
    timeMonad.time = cost succ final_list := by
  intro timeMonad final_list
  simp only [timeMonad, final_list, bfs_alt, time_bind, time_pure, Nat.add_zero,
    ret_bind, ret_pure, cost_reverse]
  have haccount := bfsLoop_alt_cost succ (Fintype.card V) (initialState source)
  -- not a huge fan of what i did here, so i'll clean this up later.
  simpa [initialState, cost] using haccount
      

theorem final_list_has_no_dups [Fintype V] (succ : V -> List V) (source : V) :
    let final_list := (bfs_alt succ source).ret
    final_list.Nodup := by
  intro final_list
  simp only [final_list, bfs_alt, ret_bind, ret_pure]
  exact List.nodup_reverse.mpr
    (bfsLoop_alt_dequeueInvariant (DequeueInvariant.initial source) succ
      (Fintype.card V)).order_nodup

-- the neighbours actually scanned are a sub-list of all successor-list entries in the input
theorem scan_cost_le_entries [Fintype V] (succ : V -> List V) (source : V) :
    let final_list := TimeM.ret (bfs_alt succ source)
    (final_list.map fun v => (succ v).length).sum ≤ entries succ := by
  intro final_list
  have hnodup : final_list.Nodup := final_list_has_no_dups _ _ 
  rw [← List.sum_toFinset (fun v => (succ v).length) hnodup]
  unfold entries
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

-- bfs_alt starting at `source` over structure `succ` returns a final list of visted nodes
-- we show that the length of this list is less than equal to the size of 
-- the cardinality of our type V.
theorem num_dqs_le_card [Fintype V] (succ : V -> List V) (source: V):
    (bfs_alt succ source).ret.length <= Fintype.card V
    := by
  have hnodup : (bfs_alt succ source).ret.Nodup := final_list_has_no_dups _ _ 
  exact hnodup.length_le_card

-- The main theorem 
theorem bfs_run_time [Fintype V] (succ : V -> List V) (source : V) :
    (bfs_alt succ source).time <= Fintype.card V + entries succ := by
  let time_monad := bfs_alt succ source
  let final_list := time_monad.ret
  have h1 : final_list.length <= Fintype.card V := num_dqs_le_card succ source
  have h2 : (final_list.map fun v => (succ v).length).sum ≤ entries succ :=
    scan_cost_le_entries succ source
  calc time_monad.time
      = final_list.length + (final_list.map fun v => (succ v).length).sum :=
        alt_time_eq_cost succ source
    _ <= Fintype.card V + entries succ := by gcongr

end BFS


end Cslib.Algorithms.Lean.TimeM
