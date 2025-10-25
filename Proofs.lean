variable (p q r : Prop)

def My.swap : α × β → β × α
  | ⟨a, b⟩ => ⟨b, a⟩

example : p ∧ q ↔ q ∧ p :=
  let flip : ∀ {α β : Prop},
      α ∧ β → β ∧ α := λ
  ⟨α, β⟩ => ⟨β, α⟩
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
    λ ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩,
    λ ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩
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
  λ f ⟨a, b⟩ => f a b

def My.curry : ((α × β) → ζ) → α → β → ζ :=
  λ f a b => f ⟨a, b⟩

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    λ f ⟨hp, hq⟩ => f hp hq,
    λ f hp hq => f ⟨hp, hq⟩
  ⟩

----------------------------------

def My.uncurriedEither {α β ζ: Type u} : (α → ζ) × (β → ζ) → ((α ⊕ β) → ζ) :=
  λ ⟨h, g⟩ => λ
              | .inl x => h x
              | .inr x => g x

def My.uncurriedEitherRev {α β ζ: Type u} : ((α ⊕ β) → ζ) → (α → ζ) × (β → ζ) :=
  λ f => ⟨λ a => f (.inl a), λ b => f (.inr b)⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    λ f => ⟨λ hp => f $ .inl hp, λ hq => f $ .inr hq⟩,
    λ ⟨g, h⟩ => λ
                | .inl a => g a
                | .inr a => h a
  ⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
