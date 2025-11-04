-- Option
inductive Maybe (α : Type) where
  | just : α → Maybe α
  | nothing : Maybe α
deriving Repr

def Maybe.map (f : α → β) : Maybe α → Maybe β
  | just a => just $ f a
  | nothing => nothing

instance : Functor Maybe where
  map := Maybe.map

def Maybe.seq : (Maybe (α → β)) → (Unit → Maybe α) → Maybe β
  | nothing, _ => nothing
  | just f, g => f <$> g ()

def Maybe.pure : α → Maybe α := Maybe.just

instance : Applicative Maybe where
  seq := Maybe.seq
  pure := Maybe.pure

def Maybe.bind : (Maybe α) → (α → Maybe β) → Maybe β
  | just x, f => f x
  | nothing, _ => nothing

instance : Monad Maybe where
  pure := Maybe.pure
  bind := Maybe.bind

-- Except

inductive Exception (ε : Type) (α : Type) where
  | ok : α → Exception ε α
  | error : ε → Exception ε α
deriving Repr

def Exception.map (f : α → β) : Exception ε α → Exception ε β
  | ok a => ok $ f a
  | error e => error e

instance : Functor (Exception γ) where
  map := Exception.map

def Exception.seq : (Exception ε (α → β)) → (Unit → Exception ε α) → Exception ε β
  | error e, _ => error e
  | ok f, ex => f <$> ex ()

def Exception.pure : α → Exception ε α := .ok

instance : Applicative (Exception ε) where
  pure := Exception.pure
  seq := Exception.seq

def Exception.bind : (Exception ε α) → (α → Exception ε β) → Exception ε β
  | ok f, g => g f
  | error e, _ => error e

instance : Monad (Exception γ) where
  pure := Exception.pure
  bind := Exception.bind

--State

structure State (γ : Type) (α : Type) where
  runState : γ → (γ × α)

def State.map (f : (α → β)) : State γ α → State γ β
  | s => .mk λg =>
          let (g1, s1) := s.runState g
          (g1, f s1)

instance : Functor (State γ) where
  map := State.map

def State.seq : (State γ (α → β)) → (Unit → State γ α) → State γ β
  | sf, sx => .mk λg =>
              let (g1, f) := sf.runState g
              let (g2, x) := (sx ()).runState g1
              (g2, f x)

def State.pure (a : α) : State γ α := ⟨(·, a)⟩

instance : Applicative (State γ) where
  seq := State.seq
  pure := State.pure

def State.bind : (State γ α) → (α → State γ β) → State γ β
  | sx, fs => .mk λg =>
              let (g1, a) := sx.runState g
              (fs a).runState g1

def State.get : State γ γ := ⟨λg => (g,g)⟩

def State.modify (f : γ → γ) : State γ Unit
  := .mk λg => (f g, ())

instance : Monad (State γ) where
  pure := State.pure
  bind := State.bind

-- Writer

structure Writer (χ : Type) (α : Type) where
  log : List χ
  val : α
deriving Repr

def Writer.map (f : α → β) : Writer χ α → Writer χ β
  | ⟨l, v⟩ => ⟨l, f v⟩

instance : Functor (Writer χ) where
  map := Writer.map

def Writer.seq : (Writer χ (α → β)) → (Unit → Writer χ α) → Writer χ β
  | ⟨l1, v1⟩, ll => let ⟨l2, v2⟩ := ll (); ⟨l1 ++ l2, v1 v2⟩

def Writer.pure (a : α) : Writer χ α := ⟨[], a⟩

instance : Applicative (Writer χ) where
  pure := Writer.pure
  seq := Writer.seq

def Writer.bind : (Writer χ α) → (α → Writer χ β) → Writer χ β
  | ⟨l, v⟩, f =>
    let ⟨l1, v2⟩ := f v
    ⟨l ++ l1, v2⟩

def Writer.tell (c : χ) : (Writer χ Unit) := ⟨[c],()⟩

instance : Monad (Writer γ) where
  pure := Writer.pure
  bind := Writer.bind

-- Reader

structure Reader (γ : Type) (α : Type) where
  runReader : γ → α

def Reader.map : (α → β) → Reader γ α → Reader γ β
  | f, r => .mk λg => f $ r.runReader g

instance : Functor (Reader γ) where
  map := Reader.map

def Reader.seq : Reader γ (α → β) → (Unit → Reader γ α) → Reader γ β
  | rf, rx => .mk λg =>
              let f := rf.runReader g
              let x := (rx ()).runReader g
              f x

def Reader.pure : α -> Reader γ α := λa => .mk (λ_ => a)

instance : Applicative (Reader γ) where
  pure := Reader.pure
  seq := Reader.seq

def Reader.bind : Reader γ α → (α → Reader γ β) → Reader γ β
  | rx, rf => .mk λg =>
              let x := rx.runReader g
              (rf x).runReader g

---------------------------------

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x::xs => do
            let x1 ← f x
            let x1s ← mapM f xs
            pure $ x1::x1s

inductive BinT (α : Type) where
  | leaf : α → BinT α
  | node : α → BinT α → BinT α → BinT α
deriving Repr

def BinT.mapM [Monad m] (f : α → m β) : BinT α → m (BinT β)
  | leaf a => BinT.leaf <$> f a
  | node a l r => do
                  let a' ← f a
                  let l' ← BinT.mapM f l
                  let r' ← BinT.mapM f r
                  pure $ .node a' l' r'

open Maybe
#eval (just $ (· * 1)) <*> just 1

#check Option

-------------

section Expressions

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op
deriving Repr, BEq

inductive Arith where
  | plus
  | minus
  | times
  | div
deriving Repr, BEq
open Expr
open Arith

def Arith.apply [Monad m] (divEff : Int → Int → m Int) : Arith → Int → Int → m Int
  | div,   a, b => divEff a b
  | plus,  a, b => pure $ a + b
  | minus, a, b => pure $ a - b
  | times, a, b => pure $ a * b

def Expr.eval [Monad m] (divEff : Int → Int → m Int) : Expr Arith → m Int
  | const a => pure a
  | prim op a b => do
                    let mut a' ← eval divEff a
                    let b' ← eval divEff b
                    Arith.apply divEff op a' b'

def divOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then none
    else pure (x / y)

def divExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

#eval eval divOption $ prim div (const 3) (const 1)
#eval eval divExcept $ prim div (const 3) (const 0)

end Expressions

section ManyMonad
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

open Many

def Many.pure (a : α) : Many α := more a (λ() => none)

def Many.append : Many α → Many α → Many α
    | Many.none, y => y
    | Many.more x xs, y => Many.more x (λu => append (xs u) y)

instance : Append (Many α) where
  append := Many.append

def Many.fromList : List α → Many α
  | [] => .none
  | x::xs => .more x (λ() => Many.fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ | _, Many.none => []
  | n+1, Many.more x xs => x::Many.take n (xs ())

def Many.takeAll : Many α → List α
  | .none => []
  | .more x xs => x :: Many.takeAll (xs ())

instance [ToString α] : ToString (Many α) where
  toString x := toString $ takeAll x

def Many.map (f : α → β) : Many α → Many β
  | .none => .none
  | .more x xs => .more (f x) (λu => Many.map f (xs u))

def Many.seq : (Many (α → β)) → (Unit → Many α) → Many β
  | .none, _ => .none
  | .more f fs, xs => Many.map f (xs ()) ++ Many.seq (fs ()) xs

def Many.bind : Many α → (α → Many β) → Many β
  | .none, _ => .none
  | .more x xs, f => f x ++ Many.bind (xs ()) f

instance : Functor Many where
  map := Many.map

instance : Applicative Many where
  seq := Many.seq
  pure := Many.pure

instance : Monad Many where
  bind := Many.bind
  pure := Many.pure

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] => if goal == 0 then Many.pure [] else .none
  | x::xs =>
    if x > goal
    then
      (addsTo goal xs)
    else do
      (.cons x <$> addsTo (goal - x) xs) ++ (addsTo goal xs)

#eval takeAll $ addsTo 10 [1,2,3,5]

end ManyMonad

def cartesianProduct (a : Many α) (b : Many β) : Many (α × β)
  := do
    let as ← a
    let bs ← b
    return (as, bs)

macro "!" x:term "!" : term => `(Many.fromList $x)

#eval IO.print $ cartesianProduct ![1,2]! ![5,6]!

--

structure Stack (α : Type) where
  stack : List α
deriving Repr

abbrev StackOP α β := StateT (Stack α) (Except String) β

def Stack.length : StackOP α Nat
  := do
    let s ← get
    pure s.stack.length

def Stack.push (a : α) : StackOP α Unit
  := modify λs => {s with stack := a::s.stack}

def Stack.pop : StackOP α α
  := do
    let s ← get
    match s.stack with
    | []    => throw "Empty stack on pop"
    | x::xs => set {s with stack := xs}
               pure x

def Stack.op (f : α → α → α) : StackOP α Unit
  := do
    let s ← get
    match s.stack with
    | [] | _::[] => throw "Empty stack on binary operations"
    | x::y::xs => set $ {s with stack := f x y :: xs}

def Stack.foldAux (f : α → α → α) (init : α) (s : Stack α) : α
  := s.stack.foldl f init

def Stack.fold (f : α → α → α) (init : α) : StackOP α Unit
  := do
    let s ← get
    let res := Stack.foldAux f init s
    set $ Stack.mk [res]

#check List.foldl

open Stack
def test : StackOP Float Unit := do
  push 1
  push 4
  _ ← op Float.add
  op Float.div

#eval test.run (Stack.mk [2])
