module LabelUtilities (Label : Set) where

open import Data.Bool using (Bool; false; true; not)
open import Data.Product using (_×_; _,_)

Label×Polarity : Set
Label×Polarity = Label × Bool

make-pos-label : Label → Label×Polarity
make-pos-label l = l , true

make-neg-label : Label → Label×Polarity
make-neg-label l = l , false

negate-label : Label×Polarity → Label×Polarity
negate-label (l , b) = l , not b
