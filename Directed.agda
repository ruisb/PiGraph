------------------------------------------------------------------------
-- Directed Multigraphs multigraphs
------------------------------------------------------------------------

-- A representation of Undirected Graphs, based on the idea underlying Martin
-- Erwig's FGL. It is an extension of the std library Data.Graph.Acyclic.
-- Note that this representation does not aim to be efficient. 

module Directed where

import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _<′_)
import Data.Nat.Properties as Nat
import Data.Fin as Fin
open Fin using (Fin; Fin′; zero; suc; #_; toℕ) renaming (_ℕ-ℕ_ to _-_)
import Data.Fin.Props as FP
open FP using (_≟_)
import Data.Product as Prod
open Prod using (∃; _×_; _,_)
open import Data.Maybe
open import Data.Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)
import Data.List as List
open List using (List; []; [_]; _∷_; _∈_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Induction.Nat

open import Relation.Binary.EqReasoning
--not important, just for examples
import Data.Char

------------------------------------------------------------------------
-- A lemma

private

  lemma : ∀ n (i : Fin n) → n - suc i <′ n
  lemma zero    ()
  lemma (suc n) i  = Nat.≤⇒≤′ $ Nat.s≤s $ FP.nℕ-ℕi≤n n i

------------------------------------------------------------------------
-- Node contexts

-- record Context (Node Edge : Set) (n : ℕ) : Set where
--   field
--     label        : Node
--     predecessors : List (Edge × Fin n) 
--     successors   : List (Edge × Fin n)
--open Context public
-- context : ∀ {Node Edge n} →
--           Node → List (Edge × Fin n) → List (Edge × Fin n) → 
--           Context Node Edge n
-- context l pp ss = record { label = l; predecessors = pp; successors = ss }


data Context (Node Edge : Set) (n : ℕ) : Set where
   context : Node → List (Edge × Fin n) → List (Edge × Fin n) → Context Node Edge n

label : ∀ {Node Edge n} → Context Node Edge n → Node
label        (context l _ _) = l

predecessors : ∀ {Node Edge n} → Context Node Edge n → List (Edge × Fin n)
predecessors (context _ p _) = p

successors : ∀ {Node Edge n} → Context Node Edge n → List (Edge × Fin n)
successors   (context _ _ s) = s

-- Map for contexts.

cmap : ∀ {N₁ N₂ E₁ E₂ n} →
       (N₁ → N₂) → 
       (List (E₁ × Fin n) → List (E₂ × Fin n)) →
       (List (E₁ × Fin n) → List (E₂ × Fin n)) →
       Context N₁ E₁ n → Context N₂ E₂ n
cmap fn fp fs c = context (fn (label c)) (fp (predecessors c)) (fs (successors c))
 
------------------------------------------------------------------------
-- Graphs

infixr 3 _&_

-- The graphs are indexed on the number of nodes.

data Graph (Node Edge : Set) : ℕ → Set where
  ∅   : Graph Node Edge 0
  _&_ : ∀ {n} (c : Context Node Edge n) (g : Graph Node Edge n) →
        Graph Node Edge (suc n)



private

  open Data.Char
  open Data.Unit

  exampleDAG : Graph ℕ ℕ 5
  exampleDAG = context 0 [] [] &
               context 1 ((10 , # 1) ∷ (11 , # 1) ∷ []) [] &
               context 2 ((12 , # 0) ∷ []) [] &
               context 3 [] [] &
               context 4 [] [] &
               ∅

  example2 : Graph Char ⊤ 4
  example2 =   context 'd' [ (tt , # 2) ] [ (tt , # 0) ] -- #3
             & context 'c' [ (tt , # 1) ] []             -- #2
             & context 'b' [ (tt , # 0) ] []             -- #1
             & context 'a' [] []                         -- #0
             & ∅

------------------------------------------------------------------------
-- Higher-order functions

-- "Fold right".

foldr : ∀ {N E m} (T : ℕ → Set) →
        (∀ {n} → Context N E n → T n → T (suc n)) →
        T 0 →
        Graph N E m → T m
foldr T _∙_ x ∅       = x
foldr T _∙_ x (c & g) = c ∙ foldr T _∙_ x g

-- "Fold left".

foldl : ∀ {N E n} (T : ℕ → Set) →
        ((i : Fin n) → T (toℕ i) → Context N E (n - suc i) →
         T (suc (toℕ i))) →
        T 0 →
        Graph N E n → T n
foldl T f x ∅       = x
foldl T f x (c & g) =
  foldl (λ n → T (suc n)) (λ i → f (suc i)) (f zero x c) g

-- Maps over node contexts.

map : ∀ {N₁ N₂ E₁ E₂ n} →
      (∀ {n} → Context N₁ E₁ n → Context N₂ E₂ n) →
      Graph N₁ E₁ n → Graph N₂ E₂ n
map f = foldr _ (λ c g → f c & g) ∅

-- Maps over node labels.

nmap : ∀ {N₁ N₂ E n} → (N₁ → N₂) → Graph N₁ E n → Graph N₂ E n
nmap f = map (cmap f id id)

-- Maps over edge labels.

emap : ∀ {N E₁ E₂ n} → (E₁ → E₂) → Graph N E₁ n → Graph N E₂ n
emap f = map (cmap id (List.map (Prod.map f id)) (List.map (Prod.map f id)))

-- Zips two graphs with the same number of nodes. Note that one of the
-- graphs has a type which restricts it to be completely disconnected.

zipNodesWith : ∀ {N₁ N₂ N E n} → (N₁ → N₂ → N) →
          Graph N₁ ⊥ n → Graph N₂ E n → Graph N E n
zipNodesWith _∙_ ∅         ∅         = ∅
zipNodesWith _∙_ (c₁ & g₁) (c₂ & g₂) =
     context (label c₁ ∙ label c₂) (predecessors c₂) (successors c₂) & zipNodesWith _∙_ g₁ g₂

-- ------------------------------------------------------------------------
-- Specific graphs

-- A completeley disconnected graph.

disconnected : ∀ n → Graph ⊤ ⊥ n
disconnected zero    = ∅
disconnected (suc n) = context tt [] [] & disconnected n

-- A complete graph.

complete : ∀ n → Graph ⊤ ⊤ n
complete zero    = ∅
complete (suc n) = let allPrev =  (List.map (_,_ tt) $ Vec.toList (Vec.allFin n))
                   in  context tt allPrev allPrev &
                       complete n

-- ------------------------------------------------------------------------
-- -- Queries

-- -- The top-most context.

-- head : ∀ {N E n} → Graph N E (suc n) → Context N E n
-- head (c & g) = c

-- -- The remaining graph.

-- tail : ∀ {N E n} → Graph N E (suc n) → Graph N E n
-- tail (c & g) = g

-- -- Finds the context and remaining graph corresponding to a given node
-- -- index.

-- _[_] : ∀ {N E n} →
--        Graph N E n → (i : Fin n) → Graph N E (suc (n - suc i))
-- ∅       [ () ]
-- (c & g) [ zero ]  = c & g
-- (c & g) [ suc i ] = g [ i ]

_[_] :  ∀ {N E n} →
        Graph N E n → (i : Fin n) → Graph N E n 
∅ [ () ]
(c & g) [ zero  ] = ? 
(c & g) [ suc i ] = ? 


-- -- The nodes of the graph (node number relative to "topmost" node ×
-- -- node label).

-- nodes : ∀ {N E n} → Graph N E n → Vec (Fin n × N) n
-- nodes {N} = Vec.zip (Vec.allFin _) ∘
--             foldr (Vec N) (λ c ns → label c ∷ ns) []

-- private

--   test-nodes : nodes example ≡ (# 0 , 0) ∷ (# 1 , 1) ∷ (# 2 , 2) ∷
--                                (# 3 , 3) ∷ (# 4 , 4) ∷ []
--   test-nodes = refl

-- -- Topological sort. Gives a vector where earlier nodes are never
-- -- successors of later nodes.

-- topSort : ∀ {N E n} → Graph N E n → Vec (Fin n × N) n
-- topSort = nodes

-- -- The edges of the graph (predecessor × edge label × successor).
-- --
-- -- The predecessor is a node number relative to the "topmost" node in
-- -- the graph, and the successor is a node number relative to the
-- -- predecessor.

-- edges : ∀ {E N n} → Graph N E n → List (∃ λ i → E × Fin (n - suc i))
-- edges {E} {N} {n} =
--   foldl (λ _ → List (∃ λ i → E × Fin (n - suc i)))
--         (λ i es c → List._++_ es (List.map (_,_ i) (successors c)))
--         []

-- private

--   test-edges : edges example ≡ (# 1 , 10 , # 1) ∷ (# 1 , 11 , # 1) ∷
--                                (# 2 , 12 , # 0) ∷ []
--   test-edges = refl

-- -- The successors of a given node i (edge label × node number relative
-- -- to i).

-- sucs : ∀ {E N n} →
--        Graph N E n → (i : Fin n) → List (E × Fin (n - suc i))
-- sucs g i = successors $ head $ g [ i ]

-- private

--   test-sucs : sucs example (# 1) ≡ (10 , # 1) ∷ (11 , # 1) ∷ []
--   test-sucs = refl

-- -- The predecessors of a given node i (node number relative to i ×
-- -- edge label).

-- preds : ∀ {E N n} → Graph N E n → (i : Fin n) → List (Fin′ i × E)
-- preds g       zero    = []
-- preds (c & g) (suc i) =
--   List._++_ (List.gfilter (p i) $ successors c)
--             (List.map
-- (Prod.map suc id) $ preds g i)
--   where
--   p : ∀ {E n} (i : Fin n) → E × Fin n → Maybe (Fin′ (suc i) × E)
--   p i (e , j)  with i ≟ j
--   p i (e , .i) | yes refl = just (zero , e)
--   p i (e , j)  | no _     = nothing

-- private

--   test-preds : preds example (# 3) ≡
--                (# 1 , 10) ∷ (# 1 , 11) ∷ (# 2 , 12) ∷ []
--   test-preds = refl

-- ------------------------------------------------------------------------
-- -- Operations

-- -- Weakens a node label.

-- weaken : ∀ {n} {i : Fin n} → Fin (n - suc i) → Fin n
-- weaken {n} {i} j = Fin.inject≤ j (FP.nℕ-ℕi≤n n (suc i))

-- -- Labels each node with its node number.

-- number : ∀ {N E n} → Graph N E n → Graph (Fin n × N) E n
-- number {N} {E} =
--   foldr (λ n → Graph (Fin n × N) E n)
--         (λ c g → cmap (_,_ zero) id c & nmap (Prod.map suc id) g)
--         ∅

-- private

--   test-number : number example ≡
--                 (context (# 0 , 0) [] &
--                  context (# 1 , 1) ((10 , # 1) ∷ (11 , # 1) ∷ []) &
--                  context (# 2 , 2) ((12 , # 0) ∷ []) &
--                  context (# 3 , 3) [] &
--                  context (# 4 , 4) [] &
--                  ∅)
--   test-number = refl

-- -- Reverses all the edges in the graph.

-- reverse : ∀ {N E n} → Graph N E n → Graph N E n
-- reverse {N} {E} g =
--   foldl (Graph N E)
--         (λ i g' c →
--            context (label c)
--                    (List.map (Prod.swap ∘ Prod.map FP.reverse id) $
--                              preds g i)
--            & g')
--         ∅ g

-- private

--   test-reverse : reverse (reverse example) ≡ example
--   test-reverse = refl


context-swap : ∀ {N E n} → Context N E n -> Context N E n
context-swap ctx = context (label ctx) (successors ctx) (predecessors ctx)

reverse : ∀ {N E n} → Graph N E n → Graph N E n
reverse = map context-swap 

private

  test-reverse : reverse (reverse example2) ≡ example2
  test-reverse = refl
 
  leibniz : ∀ {A B x y} (f : A → B) → x ≡ y → f x ≡ f y
  leibniz f refl = refl

  leibniz2 : ∀  {A B C a b c d} (f : A → B → C) → (a ≡ b) → (c ≡ d) → f a c ≡ f b d
  leibniz2 f refl refl = refl

  context-swap-involutive : ∀ {N E n} (c : Context N E n) → context-swap (context-swap c) ≡ c
  context-swap-involutive (context l [] s)       = refl
  context-swap-involutive (context l (p ∷ ps) s) = leibniz (app-pred p) (context-swap-involutive (context l ps s))
     where app-pred : ∀ {N E n} → (E × Fin n) → Context N E n -> Context N E n
           app-pred p (context l ps s) = context l (p ∷ ps) s

  reverse-involutive : ∀ {N E n} (g : Graph N E n) → reverse (reverse g) ≡ g
  reverse-involutive ∅       = refl
  reverse-involutive (c & g) = leibniz2 _&_ (context-swap-involutive c) (reverse-involutive g)





-- ------------------------------------------------------------------------
-- -- Views

-- -- Expands the subgraph induced by a given node into a tree (thus
-- -- losing all sharing).

-- data Tree N E : Set where
--   node : (label : N) (successors : List (E × Tree N E)) → Tree N E

-- toTree : ∀ {N E n} → Graph N E n → Fin n → Tree N E
-- toTree {N} {E} g i = <-rec Pred expand _ (g [ i ])
--   where
--   Pred = λ n → Graph N E (suc n) → Tree N E

--   expand : (n : ℕ) → <-Rec Pred n → Pred n
--   expand n rec (c & g) =
--     node (label c)
--          (List.map
--             (Prod.map id (λ i → rec (n - suc i) (lemma n i) (g [ i ])))
--             (successors c))

-- -- Performs the toTree expansion once for each node.

-- toForest : ∀ {N E n} → Graph N E n → Vec (Tree N E) n
-- toForest g = Vec.map (toTree g) (Vec.allFin _)

-- private

--   test-toForest : toForest example ≡
--                     let n3 = node 3 [] in
--                     node 0 [] ∷
--                     node 1 ((10 , n3) ∷ (11 , n3) ∷ []) ∷
--                     node 2 ((12 , n3) ∷ []) ∷
--                     node 3 [] ∷
--                     node 4 [] ∷
--                     []
--   test-toForest = refl
