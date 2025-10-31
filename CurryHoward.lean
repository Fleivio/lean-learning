variable (p q r : Prop)

/-
∧ ≡ × ≡ Prod ≡ Tuple
∨ ≡ ⊕ ≡ Sum  ≡ Either
→ ≡ → ≡ Func ≡ →
↔ ≡ (←, →)
¬ ≡ (→ Empty) ≡ (→ False)

-/

def My.swap : α × β → β × α
  | ⟨a, b⟩ => ⟨b, a⟩

example : p ∧ q ↔ q ∧ p :=
  let flip : ∀ {α β : Prop}, α ∧ β → β ∧ α := λ⟨α, β⟩ => ⟨β, α⟩
  ⟨flip, flip⟩

---------------------------------

def My.swapEither : α ⊕ β → β ⊕ α
  | .inl a => .inr a
  | .inr b => .inl b

example : p ∨ q ↔ q ∨ p :=
  let flip : ∀ {α β : Prop},
      α ∨ β → β ∨ α :=
      λ
      | .inl a => .inr a
      | .inr a => .inl a
  ⟨flip, flip⟩

--------------------------------

def My.assoc : α × (β × ζ) → (α × β) × ζ
  | (a, (b, z)) => ((a, b), z)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨
    λ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩,
    λ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩
  ⟩

-------------------------------

def My.assocEither : α ⊕ (β ⊕ ζ) → (α ⊕ β) ⊕ ζ
  | .inl a => .inl (.inl a)
  | .inr (.inl b) => .inl (.inr b)
  | .inr (.inr z) => .inr z

def My.assocEitherRev : (α ⊕ β) ⊕ ζ → α ⊕ (β ⊕ ζ)
  | .inl (.inl a) => .inl a
  | .inl (.inr b) => .inr (.inl b)
  | .inr z => .inr (.inr z)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
    λ
    | .inl (.inl a) => .inl a
    | .inl (.inr b) => .inr (.inl b)
    | .inr z => .inr (.inr z),
    λ
    | .inl a => .inl (.inl a)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr z) => .inr z
  ⟩

-------------------------------

def My.dist : α × (β ⊕ ζ) → (α × β) ⊕ (α × ζ)
  | ⟨a, .inl b⟩ => .inl ⟨a, b⟩
  | ⟨a, .inr z⟩ => .inr ⟨a, z⟩

def My.distRev : (α × β) ⊕ (α × ζ) → α × (β ⊕ ζ)
  | .inl ⟨a, b⟩ => ⟨a, .inl b⟩
  | .inr ⟨a, z⟩ => ⟨a, .inr z⟩

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨
    λ
    | ⟨a, .inl b⟩ => .inl ⟨a, b⟩
    | ⟨a, .inr z⟩ => .inr ⟨a, z⟩,
    λ
    | .inl ⟨a, b⟩ => ⟨a, .inl b⟩
    | .inr ⟨a, z⟩ => ⟨a, .inr z⟩
  ⟩

--------------------------------

def My.distEither : α ⊕ (β × ζ) → (α ⊕ β) × (α ⊕ ζ)
  | .inl a     => ⟨.inl a, .inl a⟩
  | .inr ⟨b,z⟩ => ⟨.inr b, .inr z⟩

def My.distEitherRev :  (α ⊕ β) × (α ⊕ ζ) → α ⊕ (β × ζ)
  | ⟨.inl a, _⟩ | ⟨_, .inl a⟩ => .inl a
  | ⟨.inr b, .inr z⟩          => .inr ⟨b, z⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    λ
    | .inl p => ⟨.inl p, .inl p⟩
    | .inr ⟨q, r⟩ => ⟨.inr q, .inr r⟩,
    λ
    | ⟨.inl p, _⟩ | ⟨_, .inl p⟩ => .inl p
    | ⟨.inr q, .inr r⟩ => .inr ⟨q, r⟩
  ⟩

--------------------------------

def My.uncurry : (α → β → ζ) → (α × β) → ζ :=
  λf ⟨a, b⟩ => f a b

def My.curry : ((α × β) → ζ) → α → β → ζ :=
  λf a b => f ⟨a, b⟩

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    λf ⟨hp, hq⟩ => f hp hq,
    λf hp hq => f ⟨hp, hq⟩
  ⟩

----------------------------------

def My.uncurriedEither {α β ζ: Type u} : (α → ζ) × (β → ζ) → ((α ⊕ β) → ζ) :=
  λ⟨h, g⟩ => λ
              | .inl x => h x
              | .inr x => g x

def My.uncurriedEitherRev {α β ζ: Type u} : ((α ⊕ β) → ζ) → (α → ζ) × (β → ζ) :=
  λf => ⟨λa => f (.inl a), λb => f (.inr b)⟩

theorem genDeMorgan : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    λf => ⟨λhp => f $ .inl hp, λhq => f $ .inr hq⟩,
    λ⟨g, h⟩ => λ
               | .inl a => g a
               | .inr a => h a
  ⟩

--------------------------------------

def My.deMorgan : ((α ⊕ β) → Empty) → ((α → Empty) × (β → Empty)) := My.uncurriedEitherRev

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := @genDeMorgan p q False

--------------------------------------

def My.revDeMorgan : ((α → Empty) ⊕ (β → Empty)) → ((α × β) → Empty) :=
  λab ⟨a, b⟩ => match ab with
    | .inl f => f a
    | .inr f => f b

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λnpq ⟨hp, hq⟩ => match npq with
    | .inl f => f hp
    | .inr f => f hq

-------------------------------------

def My.a1 : (α × (α → Empty)) → Empty
  | ⟨a, f⟩ => f a

example : ¬(p ∧ ¬p)
  | ⟨hp, hnp⟩ => hnp hp

-------------------------------------

def My.a2 {α β: Type u} : (α × (β → Empty)) → ((α → β) → Empty)
  | ⟨a, f⟩, g => f $ g a

example : p ∧ ¬q → ¬(p → q)
  | ⟨hp, hnq⟩, f => hnq (f hp)

-------------------------------------

def My.a3 : (α → Empty) → α → β
  | f, a => Empty.elim (f a)

example : ¬p → (p → q)
  | hnp, hp => absurd hp hnp

-------------------------------------

def My.a4 {α β: Type u} : ((α → Empty) ⊕ β) → α → β
  | .inl f, a => (f a).elim
  | .inr b, _ => b

example : (¬p ∨ q) → (p → q) :=
  λnpq p => match npq with
            | .inl np => absurd p np
            | .inr q => q

-------------------------------------

example : p ∨ False ↔ p :=
  ⟨
    λ
    | .inl p => p
    | .inr ff => @False.elim p ff,
    .inl
  ⟩

-------------------------------------

example : p ∧ False ↔ False :=
  ⟨
    λ⟨_, ff⟩ => ff,
    λff => ⟨False.elim ff, ff⟩
  ⟩

-------------------------------------

def My.a7 : (α → β) → (β → Empty) → (α → Empty)
  | f, g => g ∘ f

example : (p → q) → (¬q → ¬p) :=
  λf nq p => nq (f p)

-----------------------------------

section Cl -- lógica clássica (não há equivalentes em funções usuais)

open Classical -- import mentiras
variable (p q r : Prop)

example : p ∨ ¬p := em p

example : ¬¬p → p :=
  λnnp => match em p with
    | .inl pp => pp
    | .inr np => absurd np nnp

example : ¬¬p → p
  | nnp => byCases
          (λpp => pp)
          (λnp => absurd np nnp)

example : ¬¬p → p
  | nnp => byContradiction (fun np : ¬p => nnp np)

---

example : (p → q ∨ r) → ((p → q) ∨ (p → r))
  | f =>
    match em p with
    | .inl hp => match f hp with
                | .inl hq => .inl λ_ => hq
                | .inr hr => .inr λ_ => hr
    | .inr hnp => .inl λp => absurd p hnp

---

example : ¬(p ∧ q) → ¬p ∨ ¬q
  | npq =>
    match em p, em q with
    | .inr hnp, _       => .inl hnp
    | .inl _, .inr hnq => .inr hnq
    | .inl hp, .inl hq  => False.elim $ npq ⟨hp, hq⟩

---

example : ¬(p → q) → p ∧ ¬q
  | npq =>
    match em p with
      | .inr hnp => False.elim $ npq (λp => absurd p hnp)
      | .inl hp  => ⟨hp, λhq => npq (λ_ => hq)⟩

---

example : (p → q) → (¬p ∨ q)
  | pq =>
    match em p with
      | .inr hnp => .inl hnp
      | .inl hp  => .inr $ pq hp

---

example : (¬q → ¬p) → (p → q)
  | nqnp, hp =>
    match em q with
      | .inr hnq => absurd hp $ nqnp hnq
      | .inl hq  => hq

---

example : (((p → q) → p) → p)
  := match em p with
    | .inl hp  => λ_ => hp
    | .inr hnp => λf => f (λhp => absurd hp hnp)

end Cl
