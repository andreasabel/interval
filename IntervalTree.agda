{-# OPTIONS --copatterns #-}

open import Size
open import Data.Bool

module IntervalTree
  (Interval : Set)
  (sub : Bool → Interval → Interval)
  where

-- Parameters:
-- Interval : An abstract type of intervals
-- sub      : Generation a subinterval (either left or right)

left  = sub false
right = sub true

-- Infinite interval trees

mutual

  data ITree {s : Size} (i : Interval) : Set where
    leaf : ITree i
    node : ITree' {s} (left i) → ITree' {s} (right i) → ITree i

  record ITree' {s : Size} (i : Interval) : Set where
    coinductive
    constructor delay
    field
      force : ∀{s' : Size< s} → ITree {s'} i
open ITree'

-- Full tree

mutual

  fullTree : (i : Interval) → ITree i
  fullTree i = node (fullTree' (left i)) (fullTree' (right i))

  fullTree' : (i : Interval) → ITree' i
  force (fullTree' i) = fullTree i

-- Equality of ITree

mutual

  data Eq {s : Size} : ∀{i} → ITree i → ITree i → Set where

    ~leaf : ∀{i} →
            Eq {s} {i} leaf leaf

    ~node : ∀{i}{l l' : ITree' (left i)}{r r' : ITree' (right i)} →

            Eq' {s} l l' → Eq' {s} r r' →
            Eq (node l r) (node l' r')

  record Eq' {s : Size} {i} (t t' : ITree' i) : Set where
    coinductive
    constructor ~delay
    field
      ~force : ∀{s' : Size< s} → Eq {s'} (force t) (force t')
open Eq'

mutual

  -- With sized types:

  -- ~refl : ∀{s i} (t : ITree i) → Eq {s} t t
  -- ~refl leaf       = ~leaf
  -- ~refl (node l r) = ~node (~refl' l) (~refl' r)

  -- ~refl' : ∀{s i} (t : ITree' i) → Eq' {s} t t
  -- ~force (~refl' t) = ~refl (force t)

  -- Without sized types:

  ~refl : ∀{i} (t : ITree i) → Eq t t
  ~refl leaf       = ~leaf
  ~refl (node l r) = ~node (~refl' l) (~refl' r)

  ~refl' : ∀{i} (t : ITree' i) → Eq' t t
  ~force (~refl' t) = ~refl (force t)

-- TODO:  ~sym , ~trans

-- Functions monotone in some predicate
-- E.g. P = "has no zero"

Mon : (Interval → Bool) → Set
Mon f = ∀ {i : Interval}{b : Bool} → T (f i) → T (f (sub b i))

record Fun : Set where
  field
    fun : Interval → Bool
    mon : Mon fun

module _ (fun : Interval → Bool) (mon : Mon fun) where

  -- Tree containing only intervals on which fun holds

  mutual

    funTree  : ∀{s} (i : Interval) → ITree {s} i
    funTree i = if fun i then node (funTree' (left i)) (funTree' (right i))
                else leaf

    funTree' : ∀{s} (i : Interval) → ITree' {s} i
    force (funTree' i) = funTree i

  mutual

    prune : ∀{s i} → ITree {s} i → ITree {s} i
    prune leaf               = leaf
    prune {i = i} (node l r) = if fun i then node (prune' l) (prune' r)
                               else leaf

    prune' : ∀{s i} → ITree' {s} i → ITree' {s} i
    force (prune' t) = prune (force t)

-- Theorem: prune . fullTree = funTree

  mutual
    thm : ∀{s} i → Eq {s} (prune (fullTree i)) (funTree i)
    thm i with fun i
    thm i | true  = ~node (thm' (left i)) (thm' (right i))
    thm i | false = ~leaf

    thm' : ∀{s} i → Eq' {s} (prune' (fullTree' i)) (funTree' i)
    ~force (thm' i) = thm i
