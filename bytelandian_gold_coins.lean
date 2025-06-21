import Std.Data.HashMap
open Std

-- Specification: Direct recursive solution for Bytelandian Gold Coins
def maxDollars_spec (n : Nat) : Nat :=
    if n ≤ 8 then
      -- Base case: for `n ≤ 8`, it's better to sell the coin directly.
      n
    else
      -- Recursive case: choose the maximum between selling the coin directly and exchanging it.
      max n (maxDollars_spec (n / 2) + maxDollars_spec (n / 3) + maxDollars_spec (n / 4))

-- Naive memoized solution (hard to prove correct)
def maxDollarsMemo (n : Nat) : Nat :=
  let rec helperMemo : Nat → HashMap Nat Nat → Nat × HashMap Nat Nat
  | n, memo =>
    match memo.get? n with
    | some v => (v, memo) -- already cached
    | none =>
      if n ≤ 8 then -- base case: sell coin directly
        let memo' := memo.insert n n
        (n, memo')
      else
        -- recursive: compute best exchange value, memoizing along the way
        let (v1, memo1) := helperMemo (n / 2) memo
        let (v2, memo2) := helperMemo (n / 3) memo1
        let (v3, memo3) := helperMemo (n / 4) memo2
        let best := max n (v1 + v2 + v3)
        let memo' := memo3.insert n best
        (best, memo')
  (helperMemo n (HashMap.emptyWithCapacity)).fst

-- Verified memoization using Σ-types

-- A cell stores a key-value pair with a proof that f(key) = value
def cell (f : α → β) := {c: α × β // f c.fst = c.snd}

-- PropMap: HashMap that stores cells with correctness proofs
abbrev PropMap [BEq α][Hashable α] [LawfulBEq α] (f : α → β) :=
  HashMap α (cell f)

-- Get function that returns value with correctness proof
def PropMap_get? [BEq α][Hashable α] [LawfulBEq α] (ft : α → β) (hm : PropMap ft) (a : α) : Option { b : β // ft a = b } :=
  match hf : hm.get? a with -- Attempt to get the value associated with `a` in the map.
  | none => none -- If not found, return `none`.
  | some x =>
    if heq : a == x.val.fst then -- Check if the key `a` matches `x.val.fst`.
      have : ft a = x.val.snd := by
        have hx := x.property -- Extract the proof that `ft x.val.fst = x.val.snd`.
        rw [beq_iff_eq] at heq -- Propositional equality from boolean equality
        rw [← heq] at hx -- Replace `x.val.fst` with `a` using `heq`.
        exact hx -- Conclude that `ft a = x.val.snd`.
      pure ⟨ x.val.snd, this ⟩ -- Return the value and proof as `some`.
    else
      none -- If the keys don't match (shouldn't happen), return `none`.

-- Insert function that requires a correctness proof
def PropMap_insert [BEq α][Hashable α] [LawfulBEq α] (ft : α → β) (hm : PropMap ft) (k : α) (v : β) (h : ft k = v) : PropMap ft :=
  let cell : { c : α × β // ft c.fst = c.snd } := ⟨(k, v), h⟩ -- Create the cell with proof.
  hm.insert k cell -- Insert the cell into the map at key `k`.

-- Verified memoized helper function
def helper (n : Nat) (memo : PropMap maxDollars_spec) :
  { v : Nat // maxDollars_spec n = v } × PropMap maxDollars_spec :=
  match PropMap_get? maxDollars_spec memo n with
  | some result =>
    -- If `n` is already in the memoization map, return the cached value and the memo.
    -- `result` has type `{ v : Nat // maxDollars_spec n = v }`.
    (result, memo)
  | none =>
    if h : n ≤ 8 then
      -- Base case: for `n ≤ 8`.
      let v := n
      have h_spec : maxDollars_spec n = v := by
        unfold maxDollars_spec
        rw [if_pos h]
      -- Prove that `maxDollars_spec n = n` using simplification.
      let memo' := PropMap_insert maxDollars_spec memo n v h_spec
      -- Insert `(n, v)` with proof into the memoization map.
      (⟨v, h_spec⟩, memo')
    else
      -- Recursive case: compute the values for `n / 2`, `n / 3`, and `n / 4`.
      let (r1, memo1) := helper (n / 2) memo
      let (r2, memo2) := helper (n / 3) memo1
      let (r3, memo3) := helper (n / 4) memo2
      -- `r1`, `r2`, `r3` are of type `{ v : Nat // maxDollars_spec (n / x) = v }`. Basically an induction hypothesis.
      -- `memo3` is the updated memoization map after all recursive calls.
      let exchangeSum := r1.val + r2.val + r3.val -- Sum the values obtained from recursion.
      let v := max n exchangeSum -- Decide whether to sell `n` directly or exchange it.
      -- **Construct the proof that `maxDollars_spec n = v`**
      have h_spec : maxDollars_spec n = v := by
        unfold maxDollars_spec -- Expand `maxDollars_spec n`.
        rw [if_neg h] -- Since `n > 8`, use the recursive case.
        rw [r1.property, r2.property, r3.property]
        -- Replace recursive calls with their computed values using the proofs from `r1`, `r2`, `r3`.
      let memo' := PropMap_insert maxDollars_spec memo3 n v h_spec
      -- Insert the computed value and its proof into the memoization map.
      (⟨v, h_spec⟩, memo') -- Return the computed value with proof and the updated memo.

-- Main verified function
def maxDollars (n : Nat) : Nat :=
  (helper n (HashMap.empty)).1.val

-- Correctness theorem (trivial proof!)
theorem maxDollars_spec_correct : ∀ n, maxDollars n = maxDollars_spec n := by
  intro n
  unfold maxDollars
  let ⟨v, h_spec⟩ := (helper n HashMap.empty).1
  exact h_spec.symm
