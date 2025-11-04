class Semigroup (α : Type) where
  op : α → α → α

infixl:70 " <> " => fun a b => Semigroup.op a b

class Monoid (α : Type) extends Semigroup α where
  neutral : α

class Group (α : Type) extends Monoid α where
  inv : α → α

class Abelian (α : Type) extends Group α where

open Semigroup Monoid Group Abelian

----

instance : Semigroup Int where
  op := Int.add

instance : Monoid Int where
  neutral := 0

instance : Group Int where
  inv a := Int.neg a

instance : Abelian Int where

----

instance : Semigroup (α → α) where
  op f g := f ∘ g

instance : Monoid (α → α) where
  neutral := id

----
