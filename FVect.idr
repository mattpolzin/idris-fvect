module FVect

import Data.Fin

%default total

public export
data FVect : {maxLen : Nat} -> (len : Fin maxLen) -> (elem : Type) -> Type where
  Nil : FVect FZ elem
  (::) : (x : elem) -> (xs : FVect len elem) -> FVect (FS len) elem

%name FVect xs, ys, zs
