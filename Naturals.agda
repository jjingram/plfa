module plfa.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


-- The story of creation
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Operations on naturals are recursive functions
_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (succ (succ zero)) + (succ (succ (succ zero)))
  ≡⟨⟩    -- inductive case
    succ ((succ zero) + (succ (succ (succ zero))))
  ≡⟨⟩    -- inductive case
    succ (succ (zero + (succ (succ (succ zero)))))
  ≡⟨⟩    -- base case
    succ (succ (succ (succ (succ zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    succ (1 + 3)
  ≡⟨⟩
    succ (succ (0 + 3))
  ≡⟨⟩
    succ (succ 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

-- Exercise +-example
-- Compute 3 + 4, writing out your reasoning as a chain of equations.
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    succ (2 + 4)
  ≡⟨⟩
    succ (succ (1 + 4))
  ≡⟨⟩
    succ (succ (succ (0 + 4)))
  ≡⟨⟩
    succ (succ (succ 4))
  ≡⟨⟩
    7
  ∎

-- Multiplication
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- Exercise *-example
-- Compute 3 * 4, writing out your reasoning as a chain of equations.
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

-- Exercise _^_
-- Define exponentiation, which is given by the following equations.
--
-- n ^ 0        =  1
-- n ^ (1 + m)  =  n * (n ^ m)
--
-- Check that 3 ^ 4 is 81.
_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (succ m) = n * (n ^ m)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

-- Monus
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ (succ n) = zero
(succ m) ∸ (succ n) = m ∸ n

_ =
  begin
     3 ∸ 2
  ≡⟨⟩
     2 ∸ 1
  ≡⟨⟩
     1 ∸ 0
  ≡⟨⟩
     1
  ∎

_ =
  begin
     2 ∸ 3
  ≡⟨⟩
     1 ∸ 2
  ≡⟨⟩
     0 ∸ 1
  ≡⟨⟩
     0
  ∎

-- Exercise ∸-examples (recommended)
-- Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
_ =
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Precedence
infixl 6  _+_  _∸_
infixl 7  _*_
