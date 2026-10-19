{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Polysemy.Labeled
-- Description : Polytropos-backed effect labelling for Polysemy
-- Copyright   : (c) 2026, Nadia Yvette Chambers
-- License     : BSD-3-Clause
-- Maintainer  : nadia.yvette.chambers@ik.me
-- Stability   : experimental
--
-- Effect labelling using type-level 'Symbol' tags and Polytropos '#label' syntax
-- ('OverloadedLabels' via 'Field').
--
-- In Polysemy, disambiguating multiple effects of the same type is typically achieved
-- with 'Polysemy.Tagged.Tagged'. 'Polysemy.Labeled' builds upon 'Tagged' by introducing
-- the @l ::: e@ type operator and ergonomic label-directed combinators ('sendLabeled',
-- 'runLabeledBy', 'askBy', 'localBy') that allow effect actions to be addressed
-- directly by '#label' without verbose type applications.
--
-- = Example
--
-- @
-- import Polysemy
-- import Polysemy.Labeled
-- import Polysemy.Reader
--
-- program
--   :: ( Member (\"db\" ::: Reader String) r
--      , Member (\"cache\" ::: Reader Int) r
--      )
--   => Sem r (String, Int)
-- program = do
--   dbUrl <- askBy #db
--   ttl   <- askBy #cache
--   pure (dbUrl, ttl)
--
-- runProgram :: IO (String, Int)
-- runProgram =
--   program
--     & runReaderBy #db \"postgres:\/\/localhost:5432\/prod\"
--     & runReaderBy #cache 3600
--     & runM
-- @
module Polysemy.Labeled
  ( -- * Label Type Operator
    type (:::)
  , Tagged(..)

    -- * Label Combinators
  , sendLabeled
  , runLabeledBy
  , labeledBy
  , tagBy
  , retagBy

    -- * Labeled Reader Combinators
  , runReaderBy
  , askBy
  , asksBy
  , localBy

    -- * Re-exports from Polytropos
  , Field(..)
  ) where

import GHC.TypeLits (Symbol)
import Polysemy
import Polysemy.Reader (Reader(..), runReader)
import Polysemy.Tagged (Tagged(..), retag, tag, tagged, untag)
import Polytropos.Core (Field(..))

-- | Infix type operator for labeling an effect @e@ with a 'Symbol' name @name@.
--
-- Defined as a type synonym for 'Tagged' @name e@.
--
-- @
-- type AppEffects =
--   '[ \"db\" ::: Reader DBConfig
--    , \"metrics\" ::: Reader MetricsHandle
--    , Embed IO
--    ]
-- @
type (:::) (name :: Symbol) (e :: Effect) = Tagged name e
infixr 6 :::

-- | Send an action to a labeled effect using '#label' syntax.
--
-- @
-- sendLabeled #logger (LogInfo \"Transaction started\")
-- @
sendLabeled
  :: forall l e r a
   . Member (l ::: e) r
  => Field l
  -> e (Sem r) a
  -> Sem r a
sendLabeled _ = send . Tagged @l
{-# INLINE sendLabeled #-}

-- | Run a labeled effect using a standard interpreter for the underlying effect @e@.
--
-- @
-- runLabeledBy #db (runReader dbConfig) action
-- @
runLabeledBy
  :: forall l e r a
   . Field l
  -> (Sem (e ': r) a -> Sem r a)
  -> Sem ((l ::: e) ': r) a
  -> Sem r a
runLabeledBy _ runner = runner . untag
{-# INLINE runLabeledBy #-}

-- | Tag an unlabelled computation with a label @l@.
--
-- Reinterprets @e@ as @l ::: e@.
labeledBy
  :: forall l e r a
   . Field l
  -> Sem (e ': r) a
  -> Sem ((l ::: e) ': r) a
labeledBy _ = tagged @l
{-# INLINE labeledBy #-}

-- | Access a labeled effect locally within a scoped subcomputation.
--
-- Analogous to 'tag' with a runtime '#label' witness.
tagBy
  :: forall l e r a
   . Member (l ::: e) r
  => Field l
  -> Sem (e ': r) a
  -> Sem r a
tagBy _ = tag @l
{-# INLINE tagBy #-}

-- | Retag an effect from label @l1@ to label @l2@.
retagBy
  :: forall l1 l2 e r a
   . Member (l2 ::: e) r
  => Field l1
  -> Field l2
  -> Sem ((l1 ::: e) ': r) a
  -> Sem r a
retagBy _ _ = retag @_ @l2
{-# INLINE retagBy #-}

--------------------------------------------------------------------------------
-- Labeled Reader Combinators
--------------------------------------------------------------------------------

-- | Run a labeled 'Reader' effect with a constant environment value.
--
-- @
-- runReaderBy #db \"localhost:5432\" action
-- @
runReaderBy
  :: forall l i r a
   . Field l
  -> i
  -> Sem ((l ::: Reader i) ': r) a
  -> Sem r a
runReaderBy l i = runLabeledBy l (runReader i)
{-# INLINE runReaderBy #-}

-- | Retrieve the environment of a labeled 'Reader' effect.
--
-- @
-- host <- askBy #db
-- @
askBy
  :: forall l i r
   . Member (l ::: Reader i) r
  => Field l
  -> Sem r i
askBy l = sendLabeled l Ask
{-# INLINE askBy #-}

-- | Retrieve a projection of the environment of a labeled 'Reader' effect.
--
-- @
-- port <- asksBy #db dbPort
-- @
asksBy
  :: forall l i j r
   . Member (l ::: Reader i) r
  => Field l
  -> (i -> j)
  -> Sem r j
asksBy l f = f <$> askBy l
{-# INLINE asksBy #-}

-- | Modify the environment of a labeled 'Reader' effect for the duration of a subcomputation.
--
-- @
-- localBy #db (\\cfg -> cfg { timeout = 5000 }) action
-- @
localBy
  :: forall l i r a
   . Member (l ::: Reader i) r
  => Field l
  -> (i -> i)
  -> Sem r a
  -> Sem r a
localBy l f m = sendLabeled l (Local f m)
{-# INLINE localBy #-}
