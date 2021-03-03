module EqualityMonadic where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Functor, Monad, id)

--
-- IsEquality
--

{-@ type IsReflexive r a R = x:a -> {_:r a | R x x} @-}
type IsReflexive r a = a -> r a

{-@ type IsSymmetric r a R = x:a -> y:a -> {_:r a | R x y} -> {_:r a | R y x} @-}
type IsSymmetric r a = a -> a -> r a -> r a

{-@ type IsTransitive r a R = x:a -> y:a -> z:a -> {_:r a | R x y} -> {_:r a | R y z} -> {_:r a | R x z} @-}
type IsTransitive r a = a -> a -> a -> r a -> r a -> r a

-- Data Class of equalities `e` over a type `a`.
{-@
data IsEquality e a = IsEquality
  { eq :: a -> a -> Bool,
    reflexive  :: IsReflexive e a {eq},
    symmetric  :: IsSymmetric e a {eq},
    transitive :: IsTransitive e a {eq}
  }
@-}
data IsEquality e a = IsEquality
  { eq :: a -> a -> Bool,
    reflexive :: IsReflexive e a,
    symmetric :: IsSymmetric e a,
    transitive :: IsTransitive e a
  }

--
-- Base Equality (proxy for the Eq typeclass)
--

data BaseEquality a = BaseEquality
  {eq_base :: a -> a -> Bool}

{-@ reflect baseEquality_Int @-}
baseEquality_Int :: BaseEquality Int
baseEquality_Int = BaseEquality {eq_base = (Prelude.==)}

--
-- SMT Equality
--

{-@ type SMTEqual a X Y = {_:SMTEquality a | X = Y} @-}

{-@
data SMTEquality :: * -> * where
  SMTE_inject :: x:a -> y:a -> {_:Proof | x = y} -> SMTEqual a {x} {y}
@-}
data SMTEquality :: * -> * where
  SMTE_inject :: a -> a -> Proof -> SMTEquality a

-- TODO: can't write out refinement types for IsReflexive, IsSymmetric, and
-- IsTransitive, since (==) requires Eq instance, and I don't have access to
-- Haskell's typeclasses.

{-@ reflect isReflexive_SMTEquality @-}
isReflexive_SMTEquality :: IsReflexive SMTEquality a
isReflexive_SMTEquality x = SMTE_inject x x ()

{-@ assume isEquality_SMTEquality :: IsEquality SMTEquality a @-}
isEquality_SMTEquality :: IsEquality SMTEquality a
isEquality_SMTEquality = undefined

--
-- Propositional Equality
--

-- Measure. Uninterpreted propositional equality.
{-@ measure eq_propositional :: a -> a -> Bool @-}

-- Data. Propositional equality axioms.
{-@
data PropositionalEquality :: * -> * where
    PE_inject :: x:a -> y:a -> {_:Proof | x = y} -> {_:PropositionalEquality a | eq_propositional x y}
  | PE_extend :: f:(a -> b) -> g:(a -> b) -> (x:a -> {_:PropositionalEquality b | eq_propositional (f x) (g x)}) -> {_:PropositionalEquality (a -> b) | eq_propositional f g}
  | PE_context :: x:a -> y:a -> {_:PropositionalEquality a | eq_propositional x y} -> ctx:(a -> b) -> {_:PropositionalEquality b | eq_propositional (ctx x) (ctx y)}
@-}
data PropositionalEquality :: * -> * where
  PE_inject :: a -> a -> Proof -> PropositionalEquality a
  PE_extend :: (a -> b) -> (a -> b) -> (a -> PropositionalEquality b) -> PropositionalEquality (a -> b)
  PE_context :: a -> a -> PropositionalEquality a -> (a -> b) -> PropositionalEquality b

--
-- Functor
--

-- -- Data Class. Functor.
-- {-@
-- data FunctorRaw (f :: * -> *) = FunctorRaw
--   { map :: forall a b. (a -> b) -> (f a -> f b) }
-- @-}

-- {-@
-- data Functor (f :: * -> *) = Functor
--   { map_id :: forall a . x:f a -> {map id = (\x: a -> a)} }
-- @-}

--
-- Monad
--

-- -- Data Class. MonadRaw provides the form of a monad but without checking monad
-- -- laws.
-- {-@
-- data MonadRaw (m :: * -> *) = MonadRaw
--   { iFunctor :: Functor m,
--     lift :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b
--   }
-- @-}
-- data MonadRaw (m :: * -> *) = MonadRaw
--   { lift :: forall a. a -> m a,
--     bind :: forall a b. m a -> (a -> m b) -> m b
--   }

--
-- Utilities
--

{-@ reflect id @-}
id :: forall a. a -> a
id x = x
