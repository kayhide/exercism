module ResistorColors (Color(..), Resistor(..), label, ohms) where

import Control.Arrow ((***))

data Color =
    Black
  | Brown
  | Red
  | Orange
  | Yellow
  | Green
  | Blue
  | Violet
  | Grey
  | White
  deriving (Show, Enum, Bounded)

newtype Resistor = Resistor { bands :: (Color, Color, Color) }
  deriving Show

label :: Resistor -> String
label resistor =
  uncurry (<>) . (show *** (' ' :)) . last $ zip vs units

  where
  vs :: [Int]
  vs = 0 : (takeWhile (0 <) . iterate (`div` 1000) $ ohms resistor)

  units :: [String]
  units = (<> "ohms") <$> ["", "", "kilo", "mega", "giga", "tera"]


ohms :: Resistor -> Int
ohms = (*) <$> sig <*> ex


sig :: Resistor -> Int
sig (Resistor (x, y, _)) = fromEnum x * 10 + fromEnum y

ex :: Resistor -> Int
ex (Resistor (_, _, z)) = 10 ^ fromEnum z
