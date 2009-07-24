module Permutation where


open import Data.Fin as Fin
import Data.Nat as Nat
open Nat using (ℕ; zero; suc)
open import Data.Function
import Relation.Nullary.Core as NulCore
open NulCore using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality

data Perm : ℕ → Set where
  ε    : Perm 0
  _◀_ : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)

{--
Note: the symbol ◀ is written as \T1.

The permutation #k ◀ σ is the permutation where #k is the first element
(the image of #0) and σ determines the order of the following.

As an example, #k ◀ id is
 0   1  ...   i   ...   k    (k+1)  ...  j    ...  N
 ↓   ↓        ↓         ↓      ↓         ↓         ↓
 k   0       i-1       k-1   (k+1)       j         N

as the following application function makes clear.
--}


bubblefrom : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
bubblefrom k m with Nat._≤?_ (toℕ k) (toℕ m)
...              | yes _  = suc     m 
...              | no  _  = inject₁ m


_§_ : {n : ℕ} → Perm n → Fin n → Fin n
ε        § ()
(k ◀ σ) § zero    = k
(k ◀ σ) § (suc n) = bubblefrom k (σ § n)


down :  {n : ℕ} → Fin (suc (suc n)) -> Fin (suc n)
down zero    = zero
down (suc x) = x

forget_at_ : {n : ℕ} → Perm (suc n) → Fin (suc n) → Perm n
forget_at_         (v ◀ σ) zero = σ
forget_at_ {zero}  (v ◀ ε) (suc ())
forget_at_ {suc m} (v ◀ σ) (suc k) = down v ◀ forget_at_ {m} σ k

_∙_ :  {n : ℕ} → Perm n → Perm n → Perm n
ε ∙ ε             = ε
σ₁ ∙ (k ◀ σ₂)  = (σ₁ § k) ◀ (forget σ₁ at k ∙ σ₂)

i : {n : ℕ} → Perm n
i {zero}  = ε
i {suc m} = zero ◀ i

putzero : {n : ℕ} → Fin (suc n) → Perm n → Perm (suc n)  
putzero zero     σ = zero ◀ σ
putzero (suc ()) ε
putzero (suc k) (v ◀ σ) = suc v ◀ putzero k σ

_* : {n : ℕ} → Perm n → Perm n
ε *        = ε
(v ◀ σ) * = putzero v (σ *) 



leibniz : ∀ {A B x y} (f : A → B) → x ≡ y → f x ≡ f y
leibniz f refl = refl

i-* : {n : ℕ} → (i {n}) * ≡ i {n}
i-* {zero } = refl
i-* {suc n} = leibniz (_◀_ zero) (i-* {n}) 


i_§ : {n : ℕ} {k : Fin n} → i § k ≡ k
i_§ {k = zero } = refl
i_§ {k = suc m} = leibniz (bubblefrom zero) i_§

--∙-§ : {n : ℕ} {σ₁ σ₂ : Perm n} {k : Fin n} → (σ₁ ∙ σ₂) § k ≡ σ₁ § (σ₂ § k)
--∙-§  {zero } {ε}  {ε}       {()} 
--∙-§  {suc n} {σ₁} {v ◀ σ₂} {zero } = ?
--∙-§  {suc n} {σ₁} {v ◀ σ₂} {suc k} = leibniz ? (∙-§ {n} {forget σ₁ at v} {σ₂} {k})

--∙-§  {suc n} {σ₁} {v ◀ σ₂} {k} = leibniz (?) (∙-§ {n} {forget σ₁ at v} {σ₂} {?})

--∙-assoc : {n : ℕ} {σ₁ σ₂ σ₃ : Perm n} → (σ₁ ∙ σ₂) ∙ σ₃ ≡ σ₁ ∙ (σ₂ ∙ σ₃)
--∙-assoc {zero } {ε} {ε} {ε} = refl
--∙-assoc {suc m} {σ₁} {σ₂} {v ◀ σ₃'} = leibniz (?) (∙-assoc {m} {forget σ₁ at (σ₂ § v)} {forget σ₂ at v} {σ})

--∙-lneutral : {n : ℕ} {σ : Perm n} → i ∙ σ ≡ σ
--∙-lneutral {zero } {ε}      = refl
--∙-lneutral {suc n} {v ◀ σ} = leibniz (?) (∙-lneutral {n} {σ})

∙-rneutral : {n : ℕ} {σ : Perm n} → σ ∙ i ≡ σ 
∙-rneutral {zero } {ε}      = refl
∙-rneutral {suc n} {v ◀ σ} = leibniz (_◀_ v) (∙-rneutral {n} {σ})



--∙-linv : {n : ℕ} {σ : Perm n} → σ * ∙ σ ≡ i
--∙-linv {zero } {ε}      = refl
--∙-linv {suc n} {v ◀ σ} = ? (∙-linv {n} {σ})

∙-rinv : {n : ℕ} {σ : Perm n} → σ ∙ σ * ≡ i
∙-rinv {zero } {ε}      = refl
∙-rinv {suc n} {v ◀ σ} = ? (∙-rinv {n} {σ})
