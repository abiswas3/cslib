/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

module

public import Cslib.Algorithms.Lean.BreadthFirstSearch.BreadthFirstSearch
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

/-! ## Logical model of the queue -/

/- Logical FIFO List representation of a `Std.Queue`. 
Things enqueue list has first element or head as the most recent
so we need to reverse it.
-/
def queueContents (queue : Std.Queue V) : List V :=
  queue.dList ++ queue.eList.reverse

@[simp] theorem queueContents_empty : queueContents (⟨[], []⟩ : Std.Queue V) = [] := rfl

@[simp] theorem queueContents_enqueue (queue : Std.Queue V) (v : V) :
    queueContents (Std.Queue.enqueue v queue) = queueContents queue ++ [v] := by
  simp [queueContents, Std.Queue.enqueue, List.reverse_cons, List.append_assoc]

theorem queueContents_of_dequeue?_eq_some {queue queue' : Std.Queue V} {v : V}
    (h : queue.dequeue? = some (v, queue')) :
    queueContents queue = v :: queueContents queue' := by
  cases queue with
  | mk eList dList =>
      cases dList with
      | cons d ds =>
          simp only [Std.Queue.dequeue?, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
      | nil =>
          cases hr : eList.reverse with
          | nil => simp [Std.Queue.dequeue?, hr] at h
          | cons d ds =>
              simp only [Std.Queue.dequeue?, hr, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [queueContents, hr]

variable [DecidableEq V]

@[simp] theorem discover_reverseOrder (state : State V) (v : V) :
    (discover state v).reverseOrder = state.reverseOrder := by
  by_cases h : v ∈ state.seen <;> simp [discover, h]

/-! ## Successor-list scanning -/

@[simp] theorem inspectNeighbors_time (xs : List V) (state : State V) :
    (inspectNeighbors xs state).time = xs.length := by
  induction xs generalizing state with
  | nil => rfl
  | cons v vs ih => simp [inspectNeighbors, ih, Nat.add_comm]

@[simp] theorem inspectNeighbors_reverseOrder (xs : List V) (state : State V) :
    (inspectNeighbors xs state).ret.reverseOrder = state.reverseOrder := by
  induction xs generalizing state with
  | nil => rfl
  | cons v vs ih => simp [inspectNeighbors, ih]

/-! ## Duplicate-free processing -/

/-- The state properties needed to show that BFS never processes a value twice. -/
structure NodupInvariant (state : State V) : Prop where
  queue_nodup : (queueContents state.queue).Nodup
  queue_seen : ∀ ⦃v⦄, v ∈ queueContents state.queue → v ∈ state.seen
  queue_order_disjoint :
    ∀ ⦃v⦄, v ∈ queueContents state.queue → v ∉ state.reverseOrder
  order_seen : ∀ ⦃v⦄, v ∈ state.reverseOrder → v ∈ state.seen
  order_nodup : state.reverseOrder.Nodup

variable {state : State V} {v : V}

namespace NodupInvariant

/-- Enqueuing an unseen value preserves duplicate-freedom. -/
theorem discover (h : NodupInvariant state) (v : V) :
    NodupInvariant (BFS.discover state v) := by
  by_cases hseen : v ∈ state.seen
  · simpa [BFS.discover, hseen] using h
  · have hv_not_queue : v ∉ queueContents state.queue := by
      intro hvq
      exact hseen (h.queue_seen hvq)
    have hv_not_order : v ∉ state.reverseOrder := by
      intro hvo
      exact hseen (h.order_seen hvo)
    refine
      { queue_nodup := ?_
        queue_seen := ?_
        queue_order_disjoint := ?_
        order_seen := ?_
        order_nodup := by simpa [BFS.discover, hseen] using h.order_nodup }
    · simp only [BFS.discover, hseen, ↓reduceIte, queueContents_enqueue,
          List.nodup_append]
      refine ⟨h.queue_nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hav
      subst a
      exact hv_not_queue ha
    · intro w hw
      simp only [BFS.discover, hseen, ↓reduceIte, queueContents_enqueue,
        List.mem_append, List.mem_singleton, Finset.mem_insert] at hw ⊢
      rcases hw with hw | rfl
      · exact Or.inr (h.queue_seen hw)
      · exact Or.inl rfl
    · intro w hw
      simp only [BFS.discover, hseen, ↓reduceIte, queueContents_enqueue,
        List.mem_append, List.mem_singleton] at hw ⊢
      rcases hw with hw | rfl
      · exact h.queue_order_disjoint hw
      · exact hv_not_order
    · intro w hw
      simp only [BFS.discover, hseen, ↓reduceIte, Finset.mem_insert] at hw ⊢
      exact Or.inr (h.order_seen hw)

/-- Scanning a successor list preserves duplicate-freedom. -/
theorem inspectNeighbors (h : NodupInvariant state) (xs : List V) :
    NodupInvariant (BFS.inspectNeighbors xs state).ret := by
  induction xs generalizing state with
  | nil => exact h
  | cons v vs ih =>
      simp only [BFS.inspectNeighbors, ret_bind]
      exact ih (h.discover v)

variable {queue : Std.Queue V}

/-- Moving the queue head to the processed order preserves duplicate-freedom. -/
theorem dequeue (h : NodupInvariant state)
    (hdequeue : state.queue.dequeue? = some (v, queue)) :
    NodupInvariant { state with queue, reverseOrder := v :: state.reverseOrder } := by
  have hcontents := queueContents_of_dequeue?_eq_some hdequeue
  have hv_queue : v ∈ queueContents state.queue := by
    rw [hcontents]
    simp
  have hv_seen : v ∈ state.seen := h.queue_seen hv_queue
  have hv_not_order : v ∉ state.reverseOrder := h.queue_order_disjoint hv_queue
  have hqueue_nodup := h.queue_nodup
  rw [hcontents] at hqueue_nodup
  have htail_nodup : (queueContents queue).Nodup := hqueue_nodup.tail
  have hv_not_tail : v ∉ queueContents queue :=
    (List.nodup_cons.mp hqueue_nodup).1
  refine
    { queue_nodup := htail_nodup
      queue_seen := ?_
      queue_order_disjoint := ?_
      order_seen := ?_
      order_nodup := by simp [hv_not_order, h.order_nodup] }
  · intro w hw
    apply h.queue_seen
    rw [hcontents]
    exact List.mem_cons_of_mem v hw
  · intro w hw
    simp only [List.mem_cons, not_or]
    constructor
    · intro hwv
      subst w
      exact hv_not_tail hw
    · apply h.queue_order_disjoint
      rw [hcontents]
      exact List.mem_cons_of_mem v hw
  · intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hv_seen
    · exact h.order_seen hw

/-- Processing a queue head and scanning its successors preserves duplicate-freedom. -/
theorem afterInspect {successors : V → List V} (h : NodupInvariant state)
    (hdequeue : state.queue.dequeue? = some (v, queue)) :
    NodupInvariant
      (BFS.inspectNeighbors (successors v)
        { state with queue, reverseOrder := v :: state.reverseOrder }).ret := by
  exact (h.dequeue hdequeue).inspectNeighbors (successors v)

/-- The initial one-element queue satisfies the duplicate-freedom invariant. -/
theorem initial (source : V) : NodupInvariant (initialState source) := by
  refine
    { queue_nodup := by simp [initialState]
      queue_seen := ?_
      queue_order_disjoint := by simp [initialState]
      order_seen := by simp [initialState]
      order_nodup := by simp [initialState] }
  intro v hv
  simpa [initialState] using hv

end NodupInvariant

variable {successors : V → List V}

/-- The duplicate-freedom invariant is preserved by the worker loop. -/
theorem bfsLoop_nodupInvariant (h : NodupInvariant state) (fuel : ℕ) :
    NodupInvariant (bfsLoop successors fuel state).ret := by
  induction fuel generalizing state with
  | zero => exact h
  | succ fuel ih =>
      unfold bfsLoop
      cases hdequeue : state.queue.dequeue? with
      | none => simpa [hdequeue] using h
      | some pair =>
          obtain ⟨v, queue⟩ := pair
          simp only [ret_bind]
          exact ih (h.afterInspect hdequeue)

/-! ## Cost accounting -/

omit [DecidableEq V] in
/-- The total number of entries produced by the successor enumeration. -/
def entries [Fintype V] (successors : V → List V) : ℕ :=
  ∑ v, (successors v).length

/-- Work associated with the values already removed from the queue. -/
def bfsWork (successors : V → List V) (reverseOrder : List V) : ℕ :=
  reverseOrder.length + (reverseOrder.map fun v => (successors v).length).sum

omit [DecidableEq V] in
theorem bfsWork_cons (successors : V → List V) (v : V) (reverseOrder : List V) :
    bfsWork successors (v :: reverseOrder) =
      bfsWork successors reverseOrder + 1 + (successors v).length := by
  simp [bfsWork]
  omega

omit [DecidableEq V] in
@[simp] theorem bfsWork_reverse (successors : V → List V) (order : List V) :
    bfsWork successors order.reverse = bfsWork successors order := by
  simp [bfsWork]

/-- The time used by the worker is exactly the increase in processed work. -/
theorem bfsLoop_time_add_work (successors : V → List V) (fuel : ℕ) (state : State V) :
    (bfsLoop successors fuel state).time + bfsWork successors state.reverseOrder =
      bfsWork successors (bfsLoop successors fuel state).ret.reverseOrder := by
  induction fuel generalizing state with
  | zero => simp [bfsLoop]
  | succ fuel ih =>
      unfold bfsLoop
      cases hdequeue : state.queue.dequeue? with
      | none => simp
      | some pair =>
          obtain ⟨v, queue⟩ := pair
          simp only [time_bind, time_tick, ret_bind, inspectNeighbors_time]
          let popped : State V :=
            { state with queue, reverseOrder := v :: state.reverseOrder }
          let scanned := (inspectNeighbors (successors v) popped).ret
          have hi := ih scanned
          change 1 + ((successors v).length + (bfsLoop successors fuel scanned).time) +
              bfsWork successors state.reverseOrder =
            bfsWork successors (bfsLoop successors fuel scanned).ret.reverseOrder
          have hwork : bfsWork successors scanned.reverseOrder =
              bfsWork successors state.reverseOrder + 1 + (successors v).length := by
            rw [show scanned.reverseOrder = v :: state.reverseOrder by simp [scanned, popped]]
            exact bfsWork_cons successors v state.reverseOrder
          rw [← hi, hwork]
          omega

section Finite

variable [Fintype V]

/-- Breadth-first search never processes a value twice. -/
theorem bfs_nodup (successors : V → List V) (source : V) :
    ⟪bfs successors source⟫.Nodup := by
  change
    (bfsLoop successors (Fintype.card V) (initialState source)).ret.reverseOrder.reverse.Nodup
  apply List.nodup_reverse.mpr
  exact
    (bfsLoop_nodupInvariant (NodupInvariant.initial source) (Fintype.card V)).order_nodup

omit [DecidableEq V] in
private theorem bfsWork_le (successors : V → List V) (reverseOrder : List V)
    (hnodup : reverseOrder.Nodup) :
    bfsWork successors reverseOrder ≤
      Fintype.card V + entries successors := by
  classical
  unfold bfsWork entries
  apply Nat.add_le_add hnodup.length_le_card
  rw [← List.sum_toFinset (fun v => (successors v).length) hnodup]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The recorded time is exactly the work associated with the returned values. -/
theorem bfs_time_eq (successors : V → List V) (source : V) :
    (bfs successors source).time = bfsWork successors ⟪bfs successors source⟫ := by
  have haccount := bfsLoop_time_add_work successors (Fintype.card V) (initialState source)
  change
    (bfsLoop successors (Fintype.card V) (initialState source)).time =
      bfsWork successors
        (bfsLoop successors (Fintype.card V) (initialState source)).ret.reverseOrder.reverse
  rw [bfsWork_reverse]
  simpa [initialState, bfsWork] using haccount

/--
The traversal cost of breadth-first search is at most the number of values plus the total number
of successor-list entries.
-/
theorem bfs_time (successors : V → List V) (source : V) :
    (bfs successors source).time ≤
      Fintype.card V + entries successors := by
  rw [bfs_time_eq]
  exact bfsWork_le successors ⟪bfs successors source⟫ (bfs_nodup successors source)

end Finite


theorem discover_same_order (state : State V) (v : V) : 
    (discover state v).reverseOrder = state.reverseOrder := by 
  unfold discover 
  split_ifs <;> rfl 
  

-- Inspective neighbours costs time exactly equal to size of neighbours
theorem scan_time_eq_length (xs : List V) (state : State V) :
    (inspectNeighbors xs state).time = xs.length := by 
  induction xs generalizing state with 
  | nil =>
      simp only [inspectNeighbors, pure, TimeM.pure]
      rfl 
  | cons v vs ih =>
    simp only [inspectNeighbors, bind, TimeM.bind, tick]
    rw [ih, Nat.add_comm _ _ ]
    simp only [List.length_cons]

-- scanning the list of neighbours does not affect the list of dequeued nodes
theorem scan_same_order (xs : List V) (state : State V) :
    (inspectNeighbors xs state).ret.reverseOrder = state.reverseOrder := by
  induction xs generalizing state with
  | nil => rfl
  | cons v vs ih =>  
    simp only [inspectNeighbors, bind, TimeM.bind, ih]
    exact discover_same_order _ _  
     

/-- The total ticks accounted for by a dequeue-order: one per vertex dequeued, plus the
length of each of their successor lists. -/
abbrev cost (succ : V -> List V) (order : List V) : ℕ :=
  order.length + (order.map fun v => (succ v).length).sum

theorem bfsLoop_alt_cost (succ : V -> List V) (fuel : ℕ) (state : State V) :
    (bfsLoop_alt succ fuel state).time + cost succ state.reverseOrder =
      cost succ (bfsLoop_alt succ fuel state).ret.reverseOrder := sorry

-- NOTE: we do not use entries here, as succ might be disconnected.
-- by using final_list as the index set we actually get the edges explored.
theorem alt_time_eq_cost [Fintype V] (succ : V -> List V) (source : V) :
    let timeMonad := bfs_alt succ source 
    let final_list := timeMonad.ret
    timeMonad.time = cost succ final_list := sorry

-- the neighbours actually scanned are a sub-list of all successor-list entries in the input
theorem scan_cost_le_entries [Fintype V] (succ : V -> List V) (source : V) :
    let final_list := TimeM.ret (bfs_alt succ source)
    (final_list.map fun v => (succ v).length).sum ≤ entries succ := by
  intro final_list
  have hnodup : final_list.Nodup := sorry
  rw [← List.sum_toFinset (fun v => (succ v).length) hnodup]
  unfold entries
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

-- bfs_alt starting at `source` over structure `succ` returns a final list of visted nodes
-- we show that the length of this list is less than equal to the size of the cardinality of our type V.
theorem num_dqs_le_card [Fintype V] (succ: V -> List V) (source: V):
    (bfs_alt succ source).ret.length <= Fintype.card V 
    := by 
    sorry 

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
