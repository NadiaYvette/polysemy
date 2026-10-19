{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Polysemy.ReaderSoup
-- Description : Composable multi-context Reader soup effect backed by Polytropos
-- Copyright   : (c) 2026, Nadia Yvette Chambers
-- License     : BSD-3-Clause
-- Maintainer  : nadia.yvette.chambers@ik.me
-- Stability   : experimental
--
-- A composable, extensible multi-context Reader soup effect for Polysemy.
--
-- In traditional Polysemy architectures, applications requiring multiple distinct
-- environments maintain separate 'Polysemy.Reader.Reader' effects in the effect
-- row. Each distinct 'Polysemy.Reader.Reader' requires its own interpretation layer,
-- causing multiple effect traversals and handler allocations.
--
-- 'ReaderSoup' packs any number of labeled environments into a single flat contiguous
-- 'Record' backed by Polytropos's 'Polytropos.Core.Rep'.
--
-- Key Properties:
--
-- * __O(1) Direct Indexing__: Retrieval via 'askSoup' resolves at compile time
--   to a direct literal slot offset synthesized by the Polytropos type-checker plugin.
-- * __O(K) Sub-Soup Slicing__: Computations requiring only a subset of contexts can use
--   'filtering' to narrow the active environment in $O(K)$ time via 'SubRow' evidence.
-- * __Interoperability__: Functions written for standard 'Polysemy.Reader.Reader' or
--   'Polysemy.Tagged.Tagged' effects can be executed within 'ReaderSoup' using
--   'withSoupLabel' or 'withSoupAsLabeled'.
--
-- = Example
--
-- @
-- import Polysemy
-- import Polysemy.ReaderSoup
--
-- type AppSoup =
--   '[ \"db\" ':= String
--    , \"port\" ':= Int
--    ]
--
-- myApp :: HasSoup AppSoup r => Sem r String
-- myApp = do
--   dbUrl <- askSoup #db
--   p     <- askSoup #port
--   pure (dbUrl ++ \":\" ++ show p)
-- @
module Polysemy.ReaderSoup
  ( -- * Effect
    ReaderSoup(..)
  , Soup

    -- * Context Resolution Class
  , HasSoup

    -- * Handlers
  , runReaderSoup
  , runSoup

    -- * Ambient Operations
  , askSoup
  , asksSoup
  , localSoup
  , askFullSoup

    -- * Disambiguated Operations
  , askSoupIn
  , asksSoupIn
  , localSoupIn
  , askFullSoupIn

    -- * Sub-Soup Slicing & Narrowing
  , filtering
  , filteringIn

    -- * Interoperability
  , withSoupLabel
  , withSoupLabelIn
  , withSoupAsLabeled
  , withSoupAsLabeledIn

    -- * Re-exports from Polytropos
  , LookupContext
  , Field(..)
  , FieldIndex
  , SubRow
  , Record
  , Pair(..)
  , (:::)
  ) where

import Data.Functor.Identity (Identity(..))
import Data.Kind (Type)
import Data.Primitive.SmallArray (indexSmallArray)
import GHC.TypeLits (Symbol)
import Unsafe.Coerce (unsafeCoerce)

import Polysemy
import Polysemy.Reader (Reader, runReader)
import Polysemy.Tagged (untag)

import Polytropos (Record, projectRecord, setField)
import Polytropos.Core
  ( Field(..), FieldIndex(..), Pair(..), Rep(..), RowRep(..)
  , SubRow
  )
import Polytropos.ReaderSoup (LookupContext)
import Polysemy.Labeled (type (:::))

-- | Fetch a field value from a 'Record' using its compile-time synthesized index.
getField :: forall n a r. FieldIndex n r a => Field n -> Record r -> a
getField _ (RowRep (Rep _ v)) =
  case indexSmallArray v (fieldIndex @_ @n @r @a) of
    Identity val -> unsafeCoerce val

-- | A multi-context Reader effect holding a flat contiguous 'Record'
-- of labeled contexts.
data ReaderSoup (ctxs :: [Pair Symbol Type]) (m :: Type -> Type) a where
  AskSoup     :: forall ctxs l c m. (c ~ LookupContext l ctxs, FieldIndex l ctxs c)
              => Field l
              -> ReaderSoup ctxs m c
  LocalSoup   :: forall ctxs l c m a. (c ~ LookupContext l ctxs, FieldIndex l ctxs c)
              => Field l
              -> (c -> c)
              -> m a
              -> ReaderSoup ctxs m a
  AskFullSoup :: forall ctxs m. ReaderSoup ctxs m (Record ctxs)

-- | Convenient alias for 'ReaderSoup'.
type Soup = ReaderSoup

-- | Functional dependency class that resolves the ambient context row @ctxs@
-- from the effect row @r@.
--
-- This enables calls such as @'askSoup' #db@ with zero manual type annotations.
class Member (ReaderSoup ctxs) r => HasSoup (ctxs :: [Pair Symbol Type]) (r :: EffectRow) | r -> ctxs
instance {-# OVERLAPPING #-} HasSoup ctxs (ReaderSoup ctxs ': r)
instance {-# OVERLAPPABLE #-} HasSoup ctxs r => HasSoup ctxs (e ': r)

-- | Run a 'ReaderSoup' effect by supplying the context 'Record'.
runReaderSoup :: forall ctxs r a. Record ctxs -> Sem (ReaderSoup ctxs ': r) a -> Sem r a
runReaderSoup rec = interpretH $ \case
  AskSoup fld -> pureT (getField fld rec)
  AskFullSoup -> pureT rec
  LocalSoup fld f m -> do
    mm <- runT m
    let !val  = getField fld rec
        !val' = f val
        !rec' = setField fld val' rec
    raise $ runReaderSoup rec' mm
{-# INLINE runReaderSoup #-}

-- | Alias for 'runReaderSoup'.
runSoup :: forall ctxs r a. Record ctxs -> Sem (Soup ctxs ': r) a -> Sem r a
runSoup = runReaderSoup
{-# INLINE runSoup #-}

--------------------------------------------------------------------------------
-- Ambient Operations (inferred context row via HasSoup)
--------------------------------------------------------------------------------

-- | Retrieve a specific context @c@ labeled @l@ from the ambient soup in $O(1)$ time.
--
-- @
-- dbUrl <- askSoup #db
-- @
askSoup
  :: forall l ctxs c r.
     ( HasSoup ctxs r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem r c
askSoup fld = send (AskSoup @ctxs @l fld)
{-# INLINE askSoup #-}

-- | Retrieve a projection of a context @c@ from the ambient soup.
--
-- @
-- port <- asksSoup #db dbPort
-- @
asksSoup
  :: forall l ctxs c a r.
     ( HasSoup ctxs r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> (c -> a)
  -> Sem r a
asksSoup fld f = f <$> askSoup fld
{-# INLINE asksSoup #-}

-- | Modify a specific context @c@ labeled @l@ in the soup for a scoped subcomputation.
--
-- @
-- localSoup #db (\\url -> url ++ \"?ssl=true\") action
-- @
localSoup
  :: forall l ctxs c r a.
     ( HasSoup ctxs r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> (c -> c)
  -> Sem r a
  -> Sem r a
localSoup fld f m = send (LocalSoup @ctxs @l fld f m)
{-# INLINE localSoup #-}

-- | Retrieve the entire ambient 'Record' environment.
askFullSoup :: forall ctxs r. HasSoup ctxs r => Sem r (Record ctxs)
askFullSoup = send (AskFullSoup @ctxs)
{-# INLINE askFullSoup #-}

--------------------------------------------------------------------------------
-- Disambiguated Operations (explicit context row via Member)
--------------------------------------------------------------------------------

-- | Retrieve a context from an explicitly specified 'ReaderSoup' row.
askSoupIn
  :: forall ctxs l c r.
     ( Member (ReaderSoup ctxs) r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem r c
askSoupIn fld = send (AskSoup @ctxs @l fld)
{-# INLINE askSoupIn #-}

-- | Retrieve a projection of a context from an explicitly specified 'ReaderSoup' row.
asksSoupIn
  :: forall ctxs l c a r.
     ( Member (ReaderSoup ctxs) r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> (c -> a)
  -> Sem r a
asksSoupIn fld f = f <$> askSoupIn @ctxs fld
{-# INLINE asksSoupIn #-}

-- | Locally modify a context in an explicitly specified 'ReaderSoup' row.
localSoupIn
  :: forall ctxs l c r a.
     ( Member (ReaderSoup ctxs) r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> (c -> c)
  -> Sem r a
  -> Sem r a
localSoupIn fld f m = send (LocalSoup @ctxs @l fld f m)
{-# INLINE localSoupIn #-}

-- | Retrieve the entire 'Record' environment from an explicitly specified 'ReaderSoup' row.
askFullSoupIn :: forall ctxs r. Member (ReaderSoup ctxs) r => Sem r (Record ctxs)
askFullSoupIn = send (AskFullSoup @ctxs)
{-# INLINE askFullSoupIn #-}

--------------------------------------------------------------------------------
-- Sub-Soup Slicing & Narrowing
--------------------------------------------------------------------------------

-- | Restrict the ambient soup to a sub-row @sub@ in $O(K)$ time via 'SubRow'.
--
-- Enables modular subroutines to request only the contexts they require.
filtering
  :: forall sub super r a.
     ( HasSoup super r
     , SubRow sub super
     )
  => Sem (ReaderSoup sub ': r) a
  -> Sem r a
filtering act = do
  superRec <- askFullSoup
  let !subRec = projectRecord superRec
  runReaderSoup subRec act
{-# INLINE filtering #-}

-- | Restrict an explicitly specified soup row @super@ to a sub-row @sub@.
filteringIn
  :: forall sub super r a.
     ( Member (ReaderSoup super) r
     , SubRow sub super
     )
  => Sem (ReaderSoup sub ': r) a
  -> Sem r a
filteringIn act = do
  superRec <- askFullSoupIn @super
  let !subRec = projectRecord superRec
  runReaderSoup subRec act
{-# INLINE filteringIn #-}

--------------------------------------------------------------------------------
-- Interoperability
--------------------------------------------------------------------------------

-- | Run an unlabelled 'Reader' @c@ action by dipping into context @l@ of the ambient soup.
withSoupLabel
  :: forall l ctxs c r a.
     ( HasSoup ctxs r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem (Reader c ': r) a
  -> Sem r a
withSoupLabel fld act = do
  val <- askSoup fld
  runReader val act
{-# INLINE withSoupLabel #-}

-- | Run an unlabelled 'Reader' @c@ action with an explicitly specified soup row @ctxs@.
withSoupLabelIn
  :: forall ctxs l c r a.
     ( Member (ReaderSoup ctxs) r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem (Reader c ': r) a
  -> Sem r a
withSoupLabelIn fld act = do
  val <- askSoupIn @ctxs fld
  runReader val act
{-# INLINE withSoupLabelIn #-}

-- | Run a labeled @l ::: Reader c@ action by dipping into context @l@ of the ambient soup.
withSoupAsLabeled
  :: forall l ctxs c r a.
     ( HasSoup ctxs r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem ((l ::: Reader c) ': r) a
  -> Sem r a
withSoupAsLabeled fld act = do
  val <- askSoup fld
  runReader val (untag act)
{-# INLINE withSoupAsLabeled #-}

-- | Run a labeled @l ::: Reader c@ action with an explicitly specified soup row @ctxs@.
withSoupAsLabeledIn
  :: forall ctxs l c r a.
     ( Member (ReaderSoup ctxs) r
     , c ~ LookupContext l ctxs
     , FieldIndex l ctxs c
     )
  => Field l
  -> Sem ((l ::: Reader c) ': r) a
  -> Sem r a
withSoupAsLabeledIn fld act = do
  val <- askSoupIn @ctxs fld
  runReader val (untag act)
{-# INLINE withSoupAsLabeledIn #-}
