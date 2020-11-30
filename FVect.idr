module FVect

import Data.Vect
import Data.Fin
import Data.Nat

%default total

||| A Fin-based Vect. Can be thought of as a Vect with both a length and
||| a maximum capacity. Operations like filtering can reduce the length
||| without affecting maximum capacity which provides proof that a Vect's
||| length has not increased over the course of a series of operations.
public export
data FVect : (capacity : Nat) -> (len : Fin (S capacity)) -> (elem : Type) -> Type where
  Nil : {capacity : Nat } -> FVect capacity FZ elem
  
  ||| Cons an element to the FVect, increasing its capacity.
  ||| See (:::) for an operator that conses an element without
  ||| increasing capacity.
  (::) : {capacity : Nat} 
      -> {len : Fin (S capacity)} 
      -> (x : elem) 
      -> (xs : FVect capacity len elem) 
      -> FVect (S capacity) (FS len) elem

%name FVect xs, ys, zs

||| Cons an element without increasing the capacity of the FVect.
||| You must make sure the capacity and length of the FVect being
||| consed onto are accessible in the context where you call this.
||| 
||| The function signature is a bit tricky because it needs to
||| ensure you are going from length of type Fin n to length of
||| type Fin n but calling Fin's FS constructor increments n.
||| To increment the value stored without weakening the bounds of
||| the Fin, we go from (weaken (Fin (S n))) to (FS (Fin (S n))).
|||
||| In other words, we go from a weaker input Fin to the succesor of a 
||| stronger bounded Fin.
public export
(:::) : {n : Nat} 
     -> {1 len' : Fin (S n)} 
     -> (v : elem) 
     -> FVect (S n) (weaken len') elem 
     -> FVect (S n) (FS len') elem
(:::) {n = n}     {len' = FZ}      v _ = [v]
(:::) {n = 0}     {len' = (FS l')} _ _ = absurd l'
(:::) {n = (S k)} {len' = (FS l')} v (x :: xs) = v :: (x ::: xs)

||| Create an empty FVect with the given capacity.
export
empty : (capacity : Nat) -> FVect capacity FZ elem
empty _ = []

||| Allow FVect to hold one more element. 
||| Do not change the elements currently in the FVect.
public export
addCapacity : FVect c l a -> (FVect (S c) (weaken l) a)
addCapacity [] = []
addCapacity (x :: xs) = x :: (addCapacity xs)

||| Allow FVect to hold n more elements. 
||| Do not change the elements currently in the FVect.
public export
addCapacityN : {0 capacity : Nat} 
            -> {0 l : Fin (S capacity)} 
            -> (n : Nat) 
            -> FVect capacity l a 
            -> (FVect (capacity + n) (weakenN n l) a)
addCapacityN n [] = Nil
addCapacityN n (x :: xs) = x :: (addCapacityN n xs)

||| Reduce the FVect's capacity to hold elements.
public export
removeCapacity : {n : Nat} 
              -> {1 len' : Fin (S n)} 
              -> FVect (S n) (weaken len') a 
              -> FVect n len' a
removeCapacity {n = n}     {len' = FZ}      [] = []
removeCapacity {n = 0}     {len' = (FS l')} (x :: xs) = absurd l'
removeCapacity {n = (S k)} {len' = (FS l')} (x :: xs) = x :: (removeCapacity xs)

||| Get a Fin (S n) with value n.
||| In other words, convert the Nat n into the smallest Fin
||| that can contain it.
export
minimalFin : (n : Nat) -> Fin (S n)
minimalFin 0 = FZ
minimalFin (S k) = FS $ minimalFin k

||| Get the length of the FVect.
||| Returns a Fin n where n is the capacity of the FVect.
export
length : {0 capacity : Nat} 
      -> {1 l : Fin (S capacity)} 
      -> FVect capacity l a 
      -> Fin (S capacity)
length _ = l

||| Get the capacity of the FVect.
export
capacity : {1 c: Nat} -> {0 l : Fin (S c)} -> FVect c l a -> Nat
capacity _ = c

||| Get the smallest FVect that can contain the given Vect.
export
fromVect : {l : Nat} -> Vect l a -> FVect l (minimalFin l) a
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

export
toVect : FVect c l elem -> Vect (finToNat l) elem
toVect [] = []
toVect (x :: xs) = x :: (toVect xs)

-- toList provided by Foldable/Data.List

||| All but the first element of the FVect.
||| This operation does not change capacity. This means you can
||| carry out this operation and retain proof that the new FVect
||| length is less than or equal to the original FVect (although
||| in this case the length is exactly one less than before the
||| call to tail).
public export
tail : FVect c (FS l) elem -> FVect c (weaken l) elem
tail (x :: xs) = addCapacity xs

public export 
head : FVect c (FS l) elem -> elem
head (x :: _) = x

public export
last : FVect c (FS l) elem -> elem
last [x] = x
last (x :: (y :: xs)) = last $ y :: xs

||| All but the last element of the FVect.
||| This operation does not change capacity. This means you can
||| carry out this operation and retain proof that the new FVect
||| length is less than or equal to the original FVect (although
||| in this case the length is exactly one less than before the
||| call to tail).
public export
init : FVect c (FS l) elem -> FVect c (weaken l) elem
init [_] = []
init (x :: (y :: xs)) = x :: (init $ y :: xs)

||| Remove all Nothings from the FVect.
||| This operation does not change capacity. That means you can
||| carry out this operation and retain proof that the new FVect
||| length is less than or equal to that of the original FVect.
export
catMaybes : {capacity : Nat} 
         -> {len : Fin (S capacity)} 
         -> FVect capacity len (Maybe elem) 
         -> (len' : Fin (S capacity) ** FVect capacity len' elem)
catMaybes {len = FZ} [] = (FZ ** [])
catMaybes {len = (FS k)} (Nothing  :: xs) = let (l' ** rest) = catMaybes xs in
                                              (weaken l' ** addCapacity rest)
catMaybes {len = (FS k)} ((Just x) :: xs) = let (l' ** rest) = catMaybes xs in
                                              (FS l' ** x :: rest)

||| Filter down to only elements matching the predicate.
||| This operation does not change capacity. That means you can
||| carry out this operation and retain proof that the new FVect
||| length is less than or equal to that of the original FVect.
export
filter : {capacity : Nat}
      -> {len : Fin (S capacity)}
      -> (elem -> Bool)
      -> FVect capacity len elem
      -> (len' : Fin (S capacity) ** FVect capacity len' elem)
filter p [] = (FZ ** [])
filter p (x :: xs) = let (l' ** rest) = filter p xs in
                         if p x
                            then (FS l' ** x :: rest)
                            else (weaken l' ** addCapacity rest)

--
-- Functor
--

Functor (FVect c l) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

--
-- Foldable
--

Foldable (FVect c l) where
  foldr _ acc [] = acc
  foldr f acc (x :: xs) = f x $ foldr f acc xs


