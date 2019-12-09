{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module ZebraPuzzle (Resident(..), Solution(..), solve) where

import Prelude hiding ((!!))

import Control.Applicative ((<|>))
import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.Bool (bool)
import Data.List (find, findIndex, tails, (\\))
import Data.Maybe
import Data.Stream.Infinite (Stream (..), (!!))
import qualified Data.Stream.Infinite as Infinite
import Optics

import Debug.Trace

data Resident = Englishman | Spaniard | Ukrainian | Norwegian | Japanese
  deriving (Eq, Show, Enum, Bounded)

data House = Red | Green | Ivory | Yellow | Blue
  deriving (Eq, Show, Enum, Bounded)

data Pet = Dog | Snails | Fox | Horse | Zebra
  deriving (Eq, Show, Enum, Bounded)

data Drink = Coffee | Tea | Milk | OrangeJuice | Water
  deriving (Eq, Show, Enum, Bounded)

data Cigarett = OldGold | Chesterfields | Kools | LuckyStrike | Parliaments
  deriving (Eq, Show, Enum, Bounded)

data Props =
  Props
  { _resident :: [Resident]
  , _house    :: [House]
  , _pet      :: [Pet]
  , _drink    :: [Drink]
  , _cigarett :: [Cigarett]
  }
  deriving (Eq, Show)

makeFieldLabelsWith classUnderscoreNoPrefixFields ''Props

type Fact = [Props]

format :: Fact -> String
format fact = unlines $ do
  p <- fact
  pure $ unwords $ (\l -> view l p) <$> [#resident % to show, #house % to show, #pet % to show, #drink % to show, #cigarett % to show]



data Solution =
  Solution
  { waterDrinker :: Resident
  , zebraOwner   :: Resident
  } deriving (Eq, Show)

solve :: Solution
solve = case (waterDrinker' &&& zebraOwner') fact of
  (Just [w], Just [z]) -> Solution w z
  _                    -> error "No solution"
  where
    fact :: Fact
    fact = fst $ (!! 0) $ Infinite.dropWhile (uncurry (/=)) $ conses $ Infinite.iterate step' fact1

    conses :: Stream a -> Stream (a, a)
    conses = Infinite.unfold (((!! 0) &&& (!! 1)) &&& Infinite.tail)

    step' fact = step $ trace (format fact) fact

    waterDrinker' = fmap _resident . find ((== pure Water) . _drink)
    zebraOwner' = fmap _resident . find ((== pure Zebra) . _pet)

step :: Fact -> Fact
step = sweep . fact15
     . sweep . fact14
     . sweep . fact13
     . sweep . fact12
     . sweep . fact11
     . sweep . fact10
     . sweep . fact9
     . sweep . fact8
     . sweep . fact7
     . sweep . fact6
     . sweep . fact5
     . sweep . fact4
     . sweep . fact3
     . sweep . fact2


fact1 :: Fact
fact1 = replicate 5 $
  Props
  [minBound .. maxBound]
  [minBound .. maxBound]
  [minBound .. maxBound]
  [minBound .. maxBound]
  [minBound .. maxBound]

exactly :: Eq a => Lens' Props [a] -> a -> Prism' Props Props
exactly l x = filtering $ \p -> p ^. l == pure x

excluding :: Eq a => Lens' Props [a] -> a -> Prism' Props Props
excluding l x = filtering $ \p -> x `notElem` p ^. l

single :: Prism' [a] [a]
single = filtering $ (1 ==) . length

multiple :: Prism' [a] [a]
multiple = filtering $ (1 <) . length

filtering :: (a -> Bool) -> Prism' a a
filtering p = prism id (bool Left Right =<< p)


unify :: (Eq a, Eq b) => Lens' Props [a] -> a -> Lens' Props [b] -> b -> Fact -> Fact
unify lx x ly y fact = fact
  & traversed % exactly lx x % ly .~ pure y
  & traversed % exactly ly y % lx .~ pure x
  & traversed % excluding lx x % ly %~ (\\ pure y)
  & traversed % excluding ly y % lx %~ (\\ pure x)

adject :: (Eq a, Eq b) => Lens' Props [a] -> a -> Lens' Props [b] -> b -> Fact -> Fact
adject lx x ly y = adject' ly y lx x . adject' lx x ly y

adject' :: (Eq a, Eq b) => Lens' Props [a] -> a -> Lens' Props [b] -> b -> Fact -> Fact
adject' lx x ly y fact = fromMaybe fact $ do
  i <- findIndex (^. lx % to (== pure x)) fact
  let l = i - 1 <$ fact ^? ix (i - 1) % ly % multiple % filtering (elem y)
  let r = i + 1 <$ fact ^? ix (i + 1) % ly % multiple % filtering (elem y)
  guard (isJust l /= isJust r)
  i' <- l <|> r
  pure $ fact & ix i' % ly .~ pure y

prepending :: [b] -> Lens' [a] [(b, a)]
prepending xs = lens (\s -> zip xs s) (\_ b -> snd <$> b)

appending :: [b] -> Lens' [a] [(a, b)]
appending xs = lens (\s -> zip s xs) (\_ b -> fst <$> b)

exactlyLeading :: (Eq a, Eq b) => a -> b -> Prism' (Maybe [a], [b]) (Maybe [a], [b])
exactlyLeading x y = filtering $ \(xs, ys) ->
  case xs of
    Nothing -> False
    Just xs' -> ((pure x == xs') && elem y ys) || (elem x xs' && (pure y == ys))

nonLeading :: (Eq a, Eq b) => a -> b -> Prism' (Maybe [a], [b]) (Maybe [a], [b])
nonLeading x y = filtering $ \(xs, ys) ->
  case xs of
    Nothing -> True
    Just xs' -> (elem x xs') /= (elem y ys)

exactlyTrailing :: (Eq a, Eq b) => a -> b -> Prism' ([a], Maybe [b]) ([a], Maybe [b])
exactlyTrailing x y = filtering $ \(xs, ys) ->
  case ys of
    Nothing -> False
    Just ys' -> ((pure x == xs) && elem y ys') || (elem x xs && (pure y == ys'))

nonTrailing :: (Eq a, Eq b) => a -> b -> Prism' ([a], Maybe [b]) ([a], Maybe [b])
nonTrailing x y = filtering $ \(xs, ys) ->
  case ys of
    Nothing -> True
    Just ys' -> (elem x xs) /= (elem y ys')

align :: (Eq a, Eq b) => Lens' Props [a] -> a -> Lens' Props [b] -> b -> Fact -> Fact
align lx x ly y = g . f
  where
    prepending' fact = prepending $ Nothing : (fact ^.. traversed % lx % to pure)
    appending' fact = appending $ tail (fact ^.. traversed % ly % to pure) <> [Nothing]

    f fact = fact
      & partsOf (traversed % ly)
      .~ ( (fact ^.. traversed % ly)
           & prepending' fact % traversed % nonLeading x y % _2 %~ (\\ pure y)
           & prepending' fact % traversed % exactlyLeading x y % _2 .~ pure y
         )

    g fact = fact
      & partsOf (traversed % lx)
      .~ ( (fact ^.. traversed % lx)
           & appending' fact % traversed % nonTrailing x y % _1 %~ (\\ pure x)
           & appending' fact % traversed % exactlyTrailing x y % _1 .~ pure x
         )


fact2 :: Fact -> Fact
fact2 = unify #resident Englishman #house Red

fact3 :: Fact -> Fact
fact3 = unify #resident Spaniard #pet Dog

fact4 :: Fact -> Fact
fact4 = unify #drink Coffee #house Green

fact5 :: Fact -> Fact
fact5 = unify #resident Ukrainian #drink Tea

fact6 :: Fact -> Fact
fact6 = align #house Ivory #house Green

fact7 :: Fact -> Fact
fact7 = unify #cigarett OldGold #pet Snails

fact8 :: Fact -> Fact
fact8 = unify #cigarett Kools #house Yellow

fact9 :: Fact -> Fact
fact9 = set (ix 2 % #drink) $ pure Milk

fact10 :: Fact -> Fact
fact10 = set (ix 0 % #resident) $ pure Norwegian

fact11 :: Fact -> Fact
fact11 = adject #cigarett Chesterfields #pet Fox

fact12 :: Fact -> Fact
fact12 = adject #cigarett Kools #pet Horse

fact13 :: Fact -> Fact
fact13 = unify #cigarett LuckyStrike #drink OrangeJuice

fact14 :: Fact -> Fact
fact14 = unify #resident Japanese #cigarett Parliaments

fact15 :: Fact -> Fact
fact15 = adject #resident Norwegian #house Blue

sweep :: Fact -> Fact
sweep =
  (\fact' -> fact' & traversed % #resident % multiple
             %~ (\\ fact' ^.. traversed % #resident % single % traversed)
  ) .
  (\fact' -> fact' & traversed % #house % multiple
             %~ (\\ fact' ^.. traversed % #house % single % traversed)
  ) .
  (\fact' -> fact' & traversed % #pet % multiple
             %~ (\\ fact' ^.. traversed % #pet % single % traversed)
  ) .
  (\fact' -> fact' & traversed % #drink % multiple
             %~ (\\ fact' ^.. traversed % #drink % single % traversed)
  ) .
  (\fact' -> fact' & traversed % #cigarett % multiple
             %~ (\\ fact' ^.. traversed % #cigarett % single % traversed)
  )
