{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module ReaderSoupSpec (spec) where

import Polysemy
import Polysemy.Labeled
import Polysemy.Reader (Reader, ask)
import Polysemy.ReaderSoup
import Polytropos (emptyRecord, insertField)
import Test.Hspec

type AppSoup =
  '[ "db" ':= String
   , "port" ':= Int
   , "debug" ':= Bool
   ]

type SubSoup =
  '[ "db" ':= String
   , "port" ':= Int
   ]

mkAppRecord :: String -> Int -> Bool -> Record AppSoup
mkAppRecord db p d =
  insertField #db db
    $ insertField #port p
    $ insertField #debug d
    $ emptyRecord

spec :: Spec
spec = describe "Polysemy.ReaderSoup and Polysemy.Labeled" $ do
  describe "ReaderSoup" $ do
    it "retrieves individual contexts via askSoup and asksSoup" $ do
      let env = mkAppRecord "postgres://localhost" 5432 True
          prog :: HasSoup AppSoup r => Sem r (String, Int, Bool, Int)
          prog = do
            db <- askSoup #db
            p  <- askSoup #port
            d  <- askSoup #debug
            l  <- asksSoup #db length
            pure (db, p, d, l)
          (db, p, d, l) = run . runReaderSoup env $ prog
      db `shouldBe` "postgres://localhost"
      p `shouldBe` 5432
      d `shouldBe` True
      l `shouldBe` 20

    it "supports localSoup scoped modification" $ do
      let env = mkAppRecord "postgres://localhost" 5432 True
          prog :: HasSoup AppSoup r => Sem r (Int, Int)
          prog = do
            orig <- askSoup #port
            modified <- localSoup #port (+ 1000) (askSoup #port)
            pure (orig, modified)
          (orig, modified) = run . runReaderSoup env $ prog
      orig `shouldBe` 5432
      modified `shouldBe` 6432

    it "narrows context rows via filtering with SubRow" $ do
      let env = mkAppRecord "postgres://localhost" 5432 True
          subProg :: HasSoup SubSoup r => Sem r String
          subProg = do
            db <- askSoup #db
            p  <- askSoup #port
            pure (db ++ ":" ++ show p)
          superProg :: HasSoup AppSoup r => Sem r String
          superProg = filtering @SubSoup subProg
          res = run . runReaderSoup env $ superProg
      res `shouldBe` "postgres://localhost:5432"

    it "interoperates with unlabelled Reader via withSoupLabel" $ do
      let env = mkAppRecord "postgres://localhost" 5432 True
          soupAction :: HasSoup AppSoup r => Sem r String
          soupAction = withSoupLabel #db ask
          res = run . runReaderSoup env $ soupAction
      res `shouldBe` "postgres://localhost"

    it "interoperates with labeled Reader via withSoupAsLabeled" $ do
      let env = mkAppRecord "postgres://localhost" 5432 True
          soupAction :: HasSoup AppSoup r => Sem r String
          soupAction = withSoupAsLabeled #db (askBy #db)
          res = run . runReaderSoup env $ soupAction
      res `shouldBe` "postgres://localhost"

  describe "Polysemy.Labeled" $ do
    it "runs multiple labeled readers with askBy, asksBy, and localBy" $ do
      let prog :: (Member ("db" ::: Reader String) r, Member ("port" ::: Reader Int) r) => Sem r (String, Int, Int)
          prog = do
            d <- askBy #db
            p <- askBy #port
            p' <- localBy #port (\(x :: Int) -> x * 2) (askBy #port)
            pure (d, p, p')
          (d, p, p') =
            run
              . runReaderBy #db "sqlite://test.db"
              . runReaderBy #port (8080 :: Int)
              $ prog
      d `shouldBe` "sqlite://test.db"
      p `shouldBe` 8080
      p' `shouldBe` 16160
