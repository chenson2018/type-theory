module Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-suc; ≤-refl; +-mono-≤)
open import Data.Nat.Tactic.RingSolver

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc (b O) = b I
inc (b I) = (inc b) O
inc ⟨⟩ = ⟨⟩ I

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = (from b) + (from b)
from (b I) = (from b) + (from b) + 1

{-
  I would like to use the ring solver directly, but it seems to require free variables
  It would be nice to have a way for instance to pass (from b) that evaluates to a Nat
  This was helpful: https://gist.github.com/andrejbauer/358722620c26c09d6be218bcd95ee654
-}
  
+-succ-succ : ∀ (m n : ℕ) → suc m + suc n ≡ suc(m + n + 1)
+-succ-succ = solve-∀

+1-eq-suc : ∀ (m n : ℕ) → m + n + 1 ≡ suc(m + n)
+1-eq-suc = solve-∀

+1-eq-suc` : ∀ (n : ℕ) → n + 1 ≡ suc(n)
+1-eq-suc` = solve-∀

inc-eq-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-eq-suc ⟨⟩ = refl 
inc-eq-suc (b O) 
  rewrite 
    +1-eq-suc (from b) (from b) 
    = refl
inc-eq-suc (b I)
  rewrite 
      inc-eq-suc b 
    | +-succ-succ (from b) (from b) 
    = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl    
from-to (suc n) 
  rewrite 
      inc-eq-suc (to n) 
    | from-to n 
  = refl

data One : Bin → Set where
  b1 :
    One (⟨⟩ I)
  _I : ∀ {b : Bin}
    → One b 
    → One (b I)
  _O : ∀ {b : Bin}
    → One b 
    → One (b O)

one-inc : ∀{b : Bin} → One b → One (inc b)
one-inc b1 = b1 O
one-inc (x O) = x I
one-inc (x I) = (one-inc x) O

1-≤-one : ∀ {b : Bin} → One b → 1 ≤ (from b) 
1-≤-one b1 = ≤-refl {1} -- the same as s≤s z≤n
1-≤-one {b O} (x O) = +-mono-≤ (1-≤-one {b} x) (z≤n {from b})
1-≤-one {b I} (x I) = +-mono-≤ (z≤n {from b + from b}) (s≤s z≤n)

data Can : Bin → Set where
  c0 :
    Can (⟨⟩ O)
  cl : ∀{b : Bin}
    → One b
    → Can b

can-inc : ∀{b : Bin} → Can b → Can (inc b)
can-inc c0 = cl b1
can-inc (cl x) = cl (one-inc x) 

to-can : ∀(n : ℕ) → Can (to n)
to-can zero    = c0
to-can (suc n) = can-inc (to-can n)

to-suc : ∀(n : ℕ) → to(n + 1) ≡ inc(to n) 
to-suc zero = refl
to-suc (suc n) = 
  begin
    inc(to (n + 1)) ≡⟨ cong inc (cong to (+1-eq-suc` n)) ⟩
    inc(to (suc n)) ≡⟨⟩
    inc(inc (to n))
  ∎

-- this was miserable to figure out
-- sometimes I don't like when Agda automatically unwraps a definition

can-shift : ∀ {n : ℕ} → 1 ≤ n → to(n + n) ≡ (to n) O
can-shift {suc zero} x = refl
can-shift {suc (suc n)} x = 
  begin
  to(suc (suc n) + suc (suc n)) ≡⟨ {!   !} ⟩
  (to (suc (suc n)) O) 
  ∎

can-to-from : ∀{b : Bin} → Can b → to (from b) ≡ b
can-to-from c0 = refl
can-to-from (cl b1) = refl
can-to-from (cl {b O} (x O))
  rewrite 
      can-shift (1-≤-one x)
    | can-to-from (cl x)
    = refl
can-to-from (cl {b I} (x I))
  rewrite
      to-suc (from b + from b)
    | can-shift (1-≤-one x)
    | can-to-from (cl x)
    = refl 