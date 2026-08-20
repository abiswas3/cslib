import Mathlib.Data.Nat.Choose.Basic
-- Lecture 1 : Introduction To Monadic Proofs
-- We will prove that the sum of the fist `n` natural numbers is 
-- n(n-1)/2 but we will do this in a round about way that allows us 
-- specify algorithms


universe u v 
-- First define the Time monad
structure TimeM (β : Type u) (α : Type v) where
 data : α
 cost : β

def TimeM.pure [Zero β] (a : α) : TimeM β α :=
  {data := a, cost:= 0}

def TimeM.bind [Zero β] [Add β] (m : TimeM β α) (f : α -> TimeM β γ) : TimeM β γ :=
  {data := (f (m.data)).data, cost:= m.cost + (f (m.data)).cost }

def TimeM.tick (c : β) : TimeM β Unit :=
  {data := (), cost:= c}

abbrev Time := TimeM Nat 


def sum_of_n (n : Nat) (result : Nat) : Time Nat := 
  match n with 
  | 0 => TimeM.pure (result)
  | n + 1 => 
    if n % 2 == 0 then 
      TimeM.bind (TimeM.tick 1) (fun _ => (sum_of_n n (result + n)))
    else 
      sum_of_n n (result+n)

#eval sum_of_n 3 0


theorem h_arith {result n : Nat}
: result + n + n * (n - 1) / 2 = result + (n + 1) * (n + 1 - 1)/2 := by 
   rw [Nat.triangle_succ]
   omega 

theorem sum_of_n_spec (n result : Nat) :
    (sum_of_n n result).data = result + n*(n-1)/2 := by
    induction n generalizing result with 
    | zero => 
      unfold sum_of_n
      simp only [TimeM.pure, Nat.zero_mul, Nat.zero_div, Nat.add_zero] 
    | succ n ih => 
      by_cases h: n % 2 == 0
      · unfold sum_of_n 
        simp only [TimeM.tick, TimeM.bind]
        specialize ih (result + n)
        rw [ite_eq_left h]
        rw [ih]
        exact h_arith 
      · unfold sum_of_n
        simp only [TimeM.bind]
        specialize ih (result + n )
        rw [ite_eq_right h]
        rw [ih]
        exact h_arith

theorem equivalence (n: Nat): 
  (sum_of_n n 0).data = n*(n-1)/2 := by 
    rw [sum_of_n_spec n 0, Nat.zero_add]

theorem num_even_nats (n result : Nat) :
    (sum_of_n n result).cost <= (n/2+1):=  by 
  suffices  ha: (sum_of_n n result).cost <= (n+1)/2  by omega 
  induction n generalizing result with 
  | zero => 
    unfold sum_of_n
    simp only [TimeM.pure]
    omega 
  | succ n ih => 
    unfold sum_of_n
    by_cases h : n % 2 == 0 
    · rw [ite_eq_left h]
      simp only [TimeM.tick, TimeM.bind]
      specialize ih (result + n)
      simp only [beq_iff_eq] at h
      -- Sp far we have tp use the fact that n is even, so n+1 is odd and n+2 is even.
      -- Then in the calc block we will show as (n+1) is odd, 
      -- dividing by 2 and adding 1 = adding one and dividing by 2
      -- Here `h` proves that `n + 2` is also even. 
      have h_mod : (n + 1 + 1) % 2 = 0 := by rw [Nat.add_assoc, Nat.add_mod, h]      
      calc 1 + (sum_of_n n (result + n)).cost
          ≤ 1 + (n + 1) / 2 := Nat.add_le_add_left ih 1 
        _  = (n + 1) / 2 + 1 := by rw [Nat.add_comm] 
        _  = (n + 1 + 1) / 2 :=  by
          -- Since `n + 2` is divisible by two, its quotient is one larger.
          exact (Nat.succ_div_of_mod_eq_zero h_mod).symm 
    · rw [ite_eq_right h]
      specialize ih (result + n)
      omega 
