def last? : List α → Option α
  | [] => none
  | x :: [] => some x
  | _ :: xs => last? xs

def findFirst? (ls : List α) (f : α → Bool) : Option α
  := match ls with
    | [] => none
    | z :: zs => if f z then some z else findFirst? zs f

def findFirst?? (ls : List α) (f : α → Bool) : Option α
  := List.head? $ List.filter f ls

def zip : (List α) → (List β) → (List (α × β))
  | [], _ | _, [] => []
  | l::ls, d::ds => (l,d) :: zip ls ds

def zipWith : (List α) → (List β) → (α → β → η) → List η
  | [], _ | _, [] => λ_ => []
  | l::ls, d::ds => λf => (f l d) :: zipWith ls ds f

def take : Nat → List α → List α
  | 0, _ | _, [] => []
  | n+1, l::ls => l :: take n ls

def distribute : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | (a, .inl b) => .inl (a, b)
  | (a, .inr g) => .inr (a, g)

def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | ⟨a,b⟩ :: ls =>
    let ⟨as, bs⟩ := unzip ls
    ⟨a::as, b::bs⟩

def reverse : List α → List α :=
  let rec helper : List α → List α → List α
    | [], sf => sf
    | y::ys, sf => helper ys (y::sf)
  λxs => helper xs []

def main : IO Unit
  := do
    let stdin ← IO.getStdin
    IO.println "Name: "
    let name ← stdin.getLine.map String.trim
    IO.println s!"hello {name ++ "a"}"

#eval some (· * 4) <*> some 3

#check let s := Stream.mk (λx => x + 1); s.next?
#check [1,2].flatMap λx => [x+1]

def repeatn : Nat → IO Unit → List (IO Unit)
  | 0, _ => []
  | n+1, a => a :: repeatn n a

def sequence : List (IO Unit) → IO Unit
  | []    => pure ()
  | a::as => do a; sequence as

#eval sequence $ repeatn 3 (IO.print "aa")

inductive Positive where
  | one : Positive
  | succ : Positive → Positive
deriving Repr

def Positive.add : Positive → Positive → Positive
  | .one, b => .succ b
  | .succ a', b => .succ (add a' b)

instance : Add Positive where
  add := Positive.add

def Positive.toString : Positive → String
  | .one => "1"
  | .succ a => s!"{Positive.toString a}+1"

def Positive.toNat : Positive → Nat
  | .one => 1
  | succ a => 1 + Positive.toNat a

instance : ToString Positive where
  toString := toString ∘ Positive.toNat

def Positive.mul : Positive → Positive → Positive
  | .one, a => a
  | .succ a, b => b + a.mul b

instance : Mul Positive where
  mul := Positive.mul

def Positive.ofNatMinus : Nat → Positive
  | 0 => .one
  | n+1 => .succ $ ofNatMinus n

instance : OfNat Positive (n + 1) where
  ofNat := Positive.ofNatMinus n

#eval ToString.toString $ (2 : Positive) * 4

def Positive.compare : Positive → Positive → Ordering
  | .one, .one => Ordering.eq
  | .one, .succ _ => Ordering.lt
  | .succ _, .one => Ordering.lt
  | .succ a, .succ b => a.compare b

def Positive.lt (a : Positive) (b : Positive) : Prop
  := (· == Ordering.lt) $ Positive.compare a b

instance : Ord Positive where
  compare := Positive.compare

instance : LT Positive where
  lt := Positive.lt

deriving instance BEq, Hashable for Positive

---------

structure Pos where
  succ ::
  pred : Nat

#check Pos.succ 9

def Pos.add : Pos → Pos → Pos
  | a, b => succ $ a.pred + b.pred + 1

def Pos.mul : Pos → Pos → Pos
  | a, b => succ $ (a.pred + 1) * (b.pred + 1) - 1

instance : Mul Pos where
  mul := Pos.mul

instance : Add Pos where
  add := Pos.add

instance : ToString Pos where
  toString a := toString $ a.pred + 1

instance : OfNat Pos (n + 1) where
  ofNat := Pos.succ n

------------------

inductive Even where
  | zero : Even
  | plus2 : Even → Even

def Even.double : Nat → Even
  | 0 => .zero
  | n+1 => .plus2 (Even.double n)

def Even.toNat : Even → Nat
  | .zero => 0
  | .plus2 a => 2 + Even.toNat a

def Even.add : Even → Even → Even
  | .zero, b => b
  | .plus2 a, b => .plus2 (Even.add a b)

def Even.mul : Even → Even → Even
  | .zero, _    => .zero
  | .plus2 a, b => (b.add b).add (Even.mul a b)

def Even.toString : Even → String
  := ToString.toString ∘ Even.toNat

instance : Add Even where
  add := Even.add

instance : Mul Even where
  mul := Even.mul

instance : OfNat Even Nat.zero where
  ofNat := .zero

instance [OfNat Even n] : OfNat Even (n+2) where
  ofNat := .plus2 (OfNat.ofNat n)

def List.mysum [Add α] [OfNat α 0] : List α → α
  | []    => (0 : α)
  | x::xs => x + xs.sum

--------

class Op (α : Type) (β : Type) (γ : outParam Type) where
  op : α → β → γ

instance [Add α] : Op α α α where
  op := Add.add

instance i2 : Op Pos Nat Nat where
  op a b := a.pred + b + 1

instance i3 : Op Pos Nat Pos where
  op a b := OfNat.ofNat $ a.pred + b + 1

instance i4 : Op Nat Pos Nat where
  op a b := a + b.pred + 1

#check (i3.op 1 2)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul | ⟨x,y⟩, a => ⟨x*a, y*a⟩

#eval (⟨1,2⟩ : PPoint Nat) * 9

structure NonEmpty (α : Type) where
  head : α
  tail : List α
deriving Repr

def NonEmpty.get? : NonEmpty α → Nat → Option α
  | l, 0 => some l.head
  | xs, n => xs.tail[n]?

def NonEmpty.get (xs : NonEmpty α) (n : Nat) (ok : xs.tail.length ≥ n) : α
  := match xs, n with
  | l, 0    => l.head
  | xs, n+1 => xs.tail[n]

def NonEmpty.append (xs : NonEmpty α) (ys : NonEmpty α) : NonEmpty α
  := match xs with
    | ⟨h, ls⟩ => ⟨h, ls ++ ys.head :: ys.tail⟩

instance : GetElem (NonEmpty α) Nat α (λc i => c.tail.length ≥ i)
  where
  getElem := NonEmpty.get

#check {head := 1, tail := [0,1] : NonEmpty Nat}[2]

class RevElem (list : Type)
              (index : Type)
              (out : outParam Type)
              (inBounds? : outParam (list → index → Prop))
  where
  revGet : (l : list) → (ix : index) → inBounds? l ix → out

instance listRevElem : RevElem
                       (List α)
                       Nat
                       α
                       (λl ix => l.length > ix)
  where
  revGet l ix _ := l[l.length - ix - 1]

macro a:term "(]" b:term "[)" : term => `(RevElem.revGet $a $b (by simp))

#eval [1,2,4,5](]1[) -- 4
#eval [1,2,4,5](]0[) -- 5

#print List.head!

instance : Append (NonEmpty α) where
  append a b := a.append b

#eval (⟨1, [1,2,3]⟩ ++ ⟨2,[3,7]⟩ : NonEmpty Nat)

def NonEmpty.map :  (α → β) →  NonEmpty α →NonEmpty β
  | f, ⟨h, t⟩ => ⟨f h, f <$> t⟩

instance : Functor NonEmpty where
  map := NonEmpty.map

instance : HAppend (List α) (NonEmpty α) (NonEmpty α) where
  hAppend l ne := match l with
    | [] => ne
    | x::xs => ⟨x, xs ++ ne.head :: ne.tail⟩

inductive BinT (α : Type) where
  | leaf : α → BinT α
  | node : α → BinT α → BinT α → BinT α
deriving Repr

def BinT.map  (f : α → β) : BinT α → BinT β
  | .leaf a => .leaf (f a)
  | .node a l r => .node (f a) (l.map f) (r.map f)

instance : Functor BinT where
  map := BinT.map

instance {α : Type} : Functor (λx => α → x) where
  map f g := f ∘ g

structure Id' (α : Type) where
  id'::
  get : α
deriving Repr

open Id' (id')

instance : Functor Id' where
  map f i := ⟨f i.get⟩

#eval Nat.succ <$> id' 4

structure Const (α : Type) (β : Type) where
  cns ::
  get : α
deriving Repr
open Const

instance : Functor (Const α) where
  map _ g := cns g.get

#eval get $ not <$> not <$> (xor false) <$> (cns 2)

#check Option.join (some $ some 0)

#eval [1,2].isPerm [1,2,3]
#check Array.foldl

#print Monad
