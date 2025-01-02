
---[universe levels]------------------------

#check 3      -- term level
#check Nat    -- type level
#check Type 0 -- type 1 level
#check Type 1 -- type 2 level

#check List   -- Type n -> Type n ; list works on every universe level
#check Prod   -- Type n -> Type v -> Type (max n v) ; also works on every type level

#check List Nat  -- Type (list of numbers)
#check List Type -- Type 1 (list of types)

#check Prod Nat String -- Type (tuple nat x string)
#check Prod Type Type -- Type (tuple type x type)

---[definitions]------------------------
/-
"def" defines a function
-/

-- func that returns a constant value
def hello := "world"

-- standard function definition
def test (x : Nat) (y : Bool) : Nat
  := x + addup
where
  addup := if y then 2 else 1

-- function composition
def comp (a b c : Type) (f : b -> c) (g : a -> b) (x : a)
  := f (g x)

-- partial application
/-
haskell equivalent

comp1 :: ToString a => a -> Bool
comp1 = comp (not . null) (show)
-/
def comp1 [ToString a] (x : a) : Bool
  := comp a String Bool (fun x => x.length > 3) toString x

#eval comp1 3 -- false
#eval comp1 3000 -- true

-- recursive factorial
def factorial : Nat -> Nat
  | 0      => 1
  | Nat.succ n => (Nat.succ n) * factorial n

open Nat
-- no Nat. needed
def factorial2 : Nat -> Nat
  | 0      => 1
  | succ n => (succ n) * factorial n

def F.{u} (a : Type u) : Type u
  := Prod a a

--[structures]------------------

structure Point where
  x : Float
  y : Float
deriving Repr

def a : Point := Point.mk 1 2

def norm (p : Point) : Float
  := match p with
  | {x, y} => Float.sqrt (x^2 + y^2)

def projectX (p : Point) : Point
  := {p with x := 0}

#check ({x := 1, y := 2} : Point)
#eval a.x
#eval norm a

--[inductive]------------------

inductive N where
  | z         : N
  | s (n : N) : N

def isZero : N -> Bool
  | N.z => true
  | _   => false

def isEven : N -> Bool
  | N.z => true
  | N.s k => !isEven k

def add : N -> N -> N
:= fun x y =>
  match x with
  | N.z   => y
  | N.s k => N.s (add k y)

infixl:55 "+.+" => add

open N
#eval isEven z
#eval isEven (s z)
#eval isEven (s (s z))
#eval isEven (s (s z)+.+(s z))
