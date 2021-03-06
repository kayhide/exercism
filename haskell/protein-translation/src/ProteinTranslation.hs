{-# LANGUAGE LambdaCase #-}
module ProteinTranslation(proteins) where

import Data.Bool (bool)
import Data.List (unfoldr)


proteins :: String -> Maybe [String]
proteins = fmap (fmap show . takeWhile (/= Stop)) . traverse parseProtein . chunksOf 3


data Protein
  = Methionine
  | Phenylalanine
  | Leucine
  | Serine
  | Tyrosine
  | Cysteine
  | Tryptophan
  | Stop
  deriving (Eq, Show)

parseProtein :: String -> Maybe Protein
parseProtein = \case
  "AUG" -> Just Methionine
  "UUU" -> Just Phenylalanine
  "UUC" -> Just Phenylalanine
  "UUA" -> Just Leucine
  "UUG" -> Just Leucine
  "UCU" -> Just Serine
  "UCC" -> Just Serine
  "UCA" -> Just Serine
  "UCG" -> Just Serine
  "UAU" -> Just Tyrosine
  "UAC" -> Just Tyrosine
  "UGU" -> Just Cysteine
  "UGC" -> Just Cysteine
  "UGG" -> Just Tryptophan
  "UAA" -> Just Stop
  "UAG" -> Just Stop
  "UGA" -> Just Stop
  _ -> Nothing


chunksOf :: Int -> [a] -> [[a]]
chunksOf n = unfoldr splitAt'
  where
    splitAt' :: [a] -> Maybe ([a], [a])
    splitAt' xs = case splitAt n xs of
      res@(xs', _) -> bool Nothing (Just res) $ length xs' == n
