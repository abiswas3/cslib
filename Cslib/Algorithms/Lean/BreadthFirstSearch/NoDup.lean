/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

module

public import Cslib.Algorithms.Lean.BreadthFirstSearch.BreadthFirstSearch
import all Init.Data.Queue

/-!
TODO: docs
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

namespace BFS

variable {V : Type*} [DecidableEq V]

/-- View a `Std.Queue`'s contents as a plain list (front to back). -/
def queueContents (queue : Std.Queue V) : List V :=
  queue.dList ++ queue.eList.reverse

omit [DecidableEq V] in
/-- Enqueuing places the new vertex at the back of the queue contents. -/
theorem queueContents_enqueue (queue : Std.Queue V) (v : V) :
    queueContents (Std.Queue.enqueue v queue) = queueContents queue ++ [v] := by
  simp only [queueContents, Std.Queue.enqueue, List.reverse_cons, List.append_assoc]

omit [DecidableEq V] in
/-- A successful dequeue removes exactly the first vertex from the queue contents. -/
theorem queueContents_eq_cons_of_dequeue? {queue remaining : Std.Queue V} {v : V}
    (hdequeue : queue.dequeue? = some (v, remaining)) :
    queueContents queue = v :: queueContents remaining := by
  rcases queue with ⟨eList, dList⟩
  cases dList with
  | nil =>
      cases hreverse : eList.reverse with
      | nil =>
          simp only [Std.Queue.dequeue?, hreverse] at hdequeue
          cases hdequeue
      | cons front rest =>
          simp only [Std.Queue.dequeue?, hreverse, Option.some.injEq, Prod.mk.injEq] at hdequeue
          rcases hdequeue with ⟨rfl, rfl⟩
          simp only [queueContents, hreverse, List.nil_append, List.reverse_nil,
            List.append_nil]
  | cons front rest =>
      simp only [Std.Queue.dequeue?, Option.some.injEq, Prod.mk.injEq] at hdequeue
      rcases hdequeue with ⟨rfl, rfl⟩
      simp only [queueContents, List.cons_append]

/-- At all points of bfs the conjuction of these 5 things is true
We prove this for the intial state. 
THen we assume this true in the induction hypothesis, and the induction step 
will require we prove this for the next step of BFS loop.
-/
structure DequeueInvariant (state : State V) : Prop where
  -- If v is in the queue, it will be in seen
  queue_seen : ∀ v, v ∈ queueContents state.queue → v ∈ state.seen
  -- If v is in the list of de-queued things, then it will be in seen
  order_seen : ∀ v, v ∈ state.reverseOrder → v ∈ state.seen
  -- if v is still in queue then it will not be in reverse order at that point 
  disjoint : ∀ v, v ∈ queueContents state.queue → v ∉ state.reverseOrder
  -- the contents of the queue are never duplicated
  queue_nodup : (queueContents state.queue).Nodup
  -- the state of reverse order is not duplicated.
  order_nodup : state.reverseOrder.Nodup

theorem DequeueInvariant.initial (source : V) :
    DequeueInvariant (initialState source) := by
  have queueContents_initial :
      queueContents (initialState source).queue = [source] := by
    simp only [queueContents, initialState]
    simp only [Std.Queue.enqueue]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  refine {
    queue_seen := ?_
    order_seen := ?_
    disjoint := ?_
    queue_nodup := ?_
    order_nodup := ?_
  }
  · intro v hv
    rw [queueContents_initial] at hv
    change v ∈ ({source} : Finset V)
    have h_v_eq_src : v = source := List.mem_singleton.mp hv 
    exact Finset.mem_singleton.mpr (h_v_eq_src)
  · intro v hv
    change v ∈ [] at hv -- this is not possible so i'll derive false
    by_contra _ -- change goal to false
    exact (List.not_mem_nil hv)
  · intro v _
    change v ∉ []
    exact List.not_mem_nil
  · rw [queueContents_initial]
    exact List.nodup_singleton source
  · change [].Nodup
    exact List.nodup_nil

variable {state : State V}

/-- Discovering one vertex preserves the dequeue invariant. -/
theorem DequeueInvariant.discover (h : DequeueInvariant state) (v : V) :
    DequeueInvariant (BFS.discover state v) := by
  unfold BFS.discover
  split_ifs with hvSeen
  · exact h
  · have hvNotQueue : v ∉ queueContents state.queue := by
      intro hvQueue
      exact hvSeen (h.queue_seen v hvQueue)
    have hvNotOrder : v ∉ state.reverseOrder := by
      intro hvOrder
      exact hvSeen (h.order_seen v hvOrder)
    refine {
      queue_seen := ?_
      order_seen := ?_
      disjoint := ?_
      queue_nodup := ?_
      order_nodup := ?_
    }
    · intro w hwQueue
      rw [queueContents_enqueue] at hwQueue
      apply Finset.mem_insert.mpr
      rcases List.mem_append.mp hwQueue with hwOld | hwNew
      · exact Or.inr (h.queue_seen w hwOld)
      · exact Or.inl (List.mem_singleton.mp hwNew)
    · intro w hwOrder
      exact Finset.mem_insert_of_mem (h.order_seen w hwOrder)
    · intro w hwQueue hwOrder
      rw [queueContents_enqueue] at hwQueue
      rcases List.mem_append.mp hwQueue with hwOld | hwNew
      · exact h.disjoint w hwOld hwOrder
      · have hwEq : w = v := List.mem_singleton.mp hwNew
        subst w
        exact hvNotOrder hwOrder
    · rw [queueContents_enqueue]
      apply List.nodup_append.mpr
      refine ⟨h.queue_nodup, List.nodup_singleton v, ?_⟩
      intro a ha b hb
      have hbEq : b = v := List.mem_singleton.mp hb
      subst b
      intro haEq
      subst a
      exact hvNotQueue ha
    · exact h.order_nodup

/-- Inspecting a list of neighbours preserves the dequeue invariant. -/
theorem DequeueInvariant.inspectNeighbors (h : DequeueInvariant state) (neighbors : List V) :
    DequeueInvariant (BFS.inspectNeighbors neighbors state).ret := by
  induction neighbors generalizing state with
  | nil =>
      simpa only [BFS.inspectNeighbors, pure, TimeM.pure] using h
  | cons v vs ih =>
      simp only [BFS.inspectNeighbors, bind, TimeM.bind, tick]
      exact ih (h.discover v)

/-- Moving the queue's front vertex into `reverseOrder` preserves the dequeue invariant. -/
theorem DequeueInvariant.dequeue (h : DequeueInvariant state) {v : V}
    {remaining : Std.Queue V} (hdequeue : state.queue.dequeue? = some (v, remaining)) :
    DequeueInvariant
      { state with queue := remaining, reverseOrder := v :: state.reverseOrder } := by
  have hcontents : queueContents state.queue = v :: queueContents remaining :=
    queueContents_eq_cons_of_dequeue? hdequeue
  have hvQueued : v ∈ queueContents state.queue := by
    rw [hcontents]
    exact List.mem_cons_self
  have hremainingNodup : (v :: queueContents remaining).Nodup := by
    rw [← hcontents]
    exact h.queue_nodup
  have hvNotRemaining : v ∉ queueContents remaining :=
    (List.nodup_cons.mp hremainingNodup).1
  have hvNotOrder : v ∉ state.reverseOrder := h.disjoint v hvQueued
  refine {
    queue_seen := ?_
    order_seen := ?_
    disjoint := ?_
    queue_nodup := ?_
    order_nodup := ?_
  }
  · intro w hwQueue
    apply h.queue_seen w
    rw [hcontents]
    exact List.mem_cons_of_mem v hwQueue
  · intro w hwOrder
    rcases List.mem_cons.mp hwOrder with hwEq | hwOld
    · subst w
      exact h.queue_seen v hvQueued
    · exact h.order_seen w hwOld
  · intro w hwQueue hwOrder
    rcases List.mem_cons.mp hwOrder with hwEq | hwOld
    · subst w
      exact hvNotRemaining hwQueue
    · apply h.disjoint w
      · rw [hcontents]
        exact List.mem_cons_of_mem v hwQueue
      · exact hwOld
  · exact (List.nodup_cons.mp hremainingNodup).2
  · exact List.nodup_cons.mpr ⟨hvNotOrder, h.order_nodup⟩

-- the state-generalized loop step: one call to bfsLoop_alt preserves the invariant
theorem bfsLoop_alt_dequeueInvariant (h : DequeueInvariant state) (succ : V -> List V)
    (fuel : ℕ) : DequeueInvariant (bfsLoop_alt succ fuel state).ret := by
  induction fuel generalizing state with
  | zero =>
      simpa only [bfsLoop_alt, pure, TimeM.pure] using h
  | succ fuel ih =>
      simp only [bfsLoop_alt]
      cases hdequeue : state.queue.dequeue? with
      | none =>
          simpa only [pure, TimeM.pure] using h
      | some pair =>
          rcases pair with ⟨v, remaining⟩
          simp only [tick, bind, TimeM.bind]
          apply ih
          exact (h.dequeue hdequeue).inspectNeighbors (succ v)

end BFS

end Cslib.Algorithms.Lean.TimeM
