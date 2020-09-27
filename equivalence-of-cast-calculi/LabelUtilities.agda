module equivalence-of-cast-calculi.LabelUtilities (Label : Set) where

open import Data.Bool using (Bool; false; true; not)
open import Data.Product using (_×_; _,_)

Label×Polarity : Set
Label×Polarity = Label × Bool

make-label×polarity : Label → Label×Polarity
make-label×polarity l = l , true

negate-label×polarity : Label×Polarity → Label×Polarity
negate-label×polarity (l , b) = l , not b
