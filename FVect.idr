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
     -> {len' : Fin (S n)} 
     -> (v : elem) 
     -> FVect (S n) (weaken len') elem 
     -> FVect (S n) (FS len') elem
(:::) {n = 0} {len' = FZ}     v _ = [v]
(:::) {n = 0} {len' = (FS x)} _ _ = absurd x
(:::) {n = (S k)} {len' = FZ} v _ = [v]
(:::) {n = (S k)} {len' = (FS x)} v (y :: xs) = v :: (y ::: xs)

||| Create an empty FVect with the given capacity.
export
empty : (capacity : Nat) -> FVect capacity FZ elem
empty _ = []

||| Allow FVect to hold one more element. 
||| Do not change the elements currently in the FVect.
export
addCapacity : FVect c l a -> (FVect (S c) (weaken l) a)
addCapacity [] = []
addCapacity (x :: xs) = x :: (addCapacity xs)

||| Allow FVect to hold n more elements. 
||| Do not change the elements currently in the FVect.
export
addCapacityN : {0 capacity : Nat} 
            -> {0 l : Fin (S capacity)} 
            -> (n : Nat) 
            -> FVect capacity l a 
            -> (FVect (capacity + n) (weakenN n l) a)
addCapacityN n [] = Nil
addCapacityN n (x :: xs) = x :: (addCapacityN n xs)

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

||| Get a Fin (S n) with value n.
||| In other words, convert the Nat n into the smallest Fin
||| that can contain it.
export
minimalFin : (n : Nat) -> Fin (S n)
minimalFin 0 = FZ
minimalFin (S k) = FS $ minimalFin k

||| Get the smallest FVect that can contain the given Vect.
export
fromVect : {l : Nat} -> Vect l a -> FVect l (minimalFin l) a
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

--
-- TMP
--

test : String
test = let v : FVect _ _ Int = 1 :: (empty 3) in
             let v2 = 2 :: v in
               ?test_rhs
