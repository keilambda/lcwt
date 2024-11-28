module STLC where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.List using (List; _∷_; []; [_]; _++_; filter)
open import Data.String using (String; _≟_; _==_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level using (zero)
open import Relation.Nullary using (¬?; ⌊_⌋)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _▻_)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_; _∉?_)

-- 1.1.1: The set of untyped λ-terms
V : Set
V = String

data Λ : Set where
  `_   : V → Λ
  ƛ_⇒_ : V → Λ → Λ
  _·_  : Λ → Λ → Λ

-- 1.1.2: Notation
infix  9 `_
infixl 7 _·_
infixr 5 ƛ_⇒_

private
  variable
    L M N P Q R : Λ
    x y z u v w : V

-- 1.1.3:
-- i: Free variables
FV : Λ → List V
FV (` x)     = [ x ]
FV (ƛ x ⇒ P) = filter (λ y → ¬? (x ≟ y)) (FV P)
FV (P · Q)   = FV P ++ FV Q

-- ii: Closed; Combinator
Closed : Λ → Set
Closed M = FV M ≡ []

-- 1.1.4: Equality
-- congruence
`-cong : x ≡ y → ` x ≡ ` y
`-cong = cong `_

ƛ-cong : x ≡ y → M ≡ N → ƛ x ⇒ M ≡ ƛ y ⇒ N
ƛ-cong = cong₂ ƛ_⇒_

ƛ-cong-binder : x ≡ y → ƛ x ⇒ M ≡ ƛ y ⇒ M
ƛ-cong-binder h = ƛ-cong h refl

ƛ-cong-body : M ≡ N → ƛ x ⇒ M ≡ ƛ x ⇒ N
ƛ-cong-body = ƛ-cong refl

·-cong : M ≡ N → P ≡ Q → M · P ≡ N · Q
·-cong = cong₂ _·_

·-cong-left : M ≡ N → M · L ≡ N · L
·-cong-left h = ·-cong h refl

·-cong-right : M ≡ N → L · M ≡ L · N
·-cong-right = ·-cong refl

-- injectivity
`-inj : ` x ≡ ` y → x ≡ y
`-inj refl = refl

ƛ-inj : ƛ x ⇒ M ≡ ƛ y ⇒ N → x ≡ y × M ≡ N
ƛ-inj refl = refl , refl

ƛ-inj-binder : ƛ x ⇒ M ≡ ƛ y ⇒ N → x ≡ y
ƛ-inj-binder h = proj₁ (ƛ-inj h)

ƛ-inj-body : ƛ x ⇒ M ≡ ƛ y ⇒ N → M ≡ N
ƛ-inj-body h = proj₂ (ƛ-inj h)

·-inj : M · P ≡ N · Q → M ≡ N × P ≡ Q
·-inj refl = refl , refl

·-inj-left : M · L ≡ N · L → M ≡ N
·-inj-left h = proj₁ (·-inj h)

·-inj-right : L · M ≡ L · N → M ≡ N
·-inj-right h = proj₂ (·-inj h)

-- 1.1.5: β-reduction and η-reduction
-- substitution
_[_:=_] : Λ → V → Λ → Λ
(` y)     [ x := N ] = if x == y then N else ` y
(ƛ y ⇒ M) [ x := N ] = if (x == y) ∨ ⌊ y ∈? FV N ⌋ then ƛ y ⇒ M else ƛ y ⇒ M [ x := N ]
(M · L)   [ x := N ] = M [ x := N ] · L [ x := N ]

infix 9 _[_:=_]

-- β-rule
β⟶_ : Λ → Λ
β⟶ ((ƛ x ⇒ M) · N) = M [ x := N ]
β⟶ (` x)           = ` x
β⟶ (ƛ x ⇒ M)       = ƛ x ⇒ β⟶ M
β⟶ (M · N)         = β⟶ M · β⟶ N

-- η-rule
η⟶_ : Λ → Λ
η⟶ (ƛ x ⇒ M · ` y) = if (x == y) ∧ ⌊ x ∉? FV M ⌋ then M else ƛ x ⇒ M · ` y
η⟶ (` x)           = ` x
η⟶ (ƛ x ⇒ M)       = ƛ x ⇒ η⟶ M
η⟶ (M · N)         = η⟶ M · η⟶ N

data _⟶β_ : Rel Λ zero where
  β-ƛ :
    -----------------------------
    (ƛ x ⇒ M) · N ⟶β M [ x := N ]

  β-appr :
    M ⟶β N
    ----------------
    → L · M ⟶β L · N

  β-appl :
    M ⟶β N
    ----------------
    → M · L ⟶β N · L

  β-abs :
    M ⟶β N
    --------------------
    → ƛ x ⇒ M ⟶β ƛ x ⇒ N

infix 4 _⟶β_

_↠β_ : Rel Λ zero
_↠β_ = Star _⟶β_

⟶β→↠β : M ⟶β N → M ↠β N
⟶β→↠β = ε ▻_

data _≡β_ : Rel Λ zero where
  ⟶β→≡β : M ⟶β N → M ≡β N
  ≡β-refl : M ≡β M
  ≡β-sym : M ≡β N → N ≡β M
  ≡β-trans : L ≡β M → M ≡β N → L ≡β N

↠β→≡β : M ↠β N → M ≡β N
↠β→≡β ε         = ≡β-refl
↠β→≡β (ml ◅ ln) = ≡β-trans (⟶β→≡β ml) (↠β→≡β ln)

module Combinators where
  I = ƛ "x" ⇒ ` "x"
  K = ƛ "x" ⇒ ƛ "y" ⇒ ` "x"
  S = ƛ "x" ⇒ ƛ "y" ⇒ ƛ "z" ⇒ ` "x" · ` "z" · (` "y" · ` "z")

  Ω = (ƛ "x" ⇒ ` "x" · ` "x") · (ƛ "x" ⇒ ` "x" · ` "x")
  Y = ƛ "f" ⇒ (ƛ "x" ⇒ ` "f" · (` "x" · ` "x")) · (ƛ "x" ⇒ ` "f" · (` "x" · ` "x"))

-- 1.1.11: Type atom and simple types
𝔸 : Set
𝔸 = String

data 𝕋 : Set where
  ``_  : 𝔸 → 𝕋
  _⟶_ : 𝕋 → 𝕋 → 𝕋

infix  9 ``_
infixr 5 _⟶_

private
  variable
    α β γ σ τ ρ : 𝔸
    A B C D : 𝕋

``-inj : `` α ≡ `` β → α ≡ β
``-inj refl = refl

⟶-inj : A ⟶ B ≡ C ⟶ D → A ≡ C × B ≡ D
⟶-inj refl = refl , refl

``≢⟶ : `` α ≢ A ⟶ B
``≢⟶ ()

_𝕋==_ : 𝕋 → 𝕋 → Bool
(`` x) 𝕋== (`` y)   = x == y
(x ⟶ y) 𝕋== (p ⟶ q) = x 𝕋== p ∧ y 𝕋== q
_ 𝕋== _             = false

-- 1.1.13: Type substitution
_[_:=_]ᵀ : 𝕋 → 𝔸 → 𝕋 → 𝕋
(`` x)  [ α := C ]ᵀ = if x == α then C else `` x
(A ⟶ B) [ α := C ]ᵀ = A [ α := C ]ᵀ ⟶ B [ α := C ]ᵀ

infix 9 _[_:=_]ᵀ

-- 1.1.14: Type assignment
Ctx : Set
Ctx = List (V × 𝕋)

-- The system λ→ à la Curry
data _⊢_∶_ : Ctx → Λ → 𝕋 → Set where
  ⊢`_ : ∀ {Γ x A}
    → (x , A) ∈ Γ
    -------------
    → Γ ⊢ ` x ∶ A

  ⊢_⟶_ : ∀ {Γ A B}
    → Γ ⊢ M ∶ (A ⟶ B)
    -----------------
    → Γ ⊢ N ∶ A
    ---------------
    → Γ ⊢ M · N ∶ B

  ⊢ƛ_ : ∀ {Γ x M A B}
    → ((x , A) ∷ Γ) ⊢ M ∶ B
    -----------------------
    → Γ ⊢ ƛ x ⇒ M ∶ (A ⟶ B)

infix  9 ⊢`_
infixl 7 ⊢_⟶_
infixr 5 ⊢ƛ_

-- 1.1.15
dom : Ctx → List V
dom [] = []
dom ((d , _) ∷ xs) = d ∷ dom xs

⊢_∶_ : Λ → 𝕋 → Set
⊢ M ∶ A = [] ⊢ M ∶ A

-- 1.1.16
module TypeAssignmentExamples where
  open import Relation.Nullary.Negation.Core using (¬_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open Combinators

  x-ty : [ ("x" , `` "A") ] ⊢ (` "x") ∶ (`` "A")
  x-ty = ⊢` here refl

  x-nty : ¬ (⊢ (` "x") ∶ (`` "A"))
  x-nty (⊢` ())

  I-ty : ⊢ I ∶ (`` "A" ⟶ `` "A")
  I-ty = ⊢ƛ (⊢` here refl)

  K-ty : ⊢ K ∶ (`` "A" ⟶ `` "B" ⟶ `` "A")
  K-ty = ⊢ƛ (⊢ƛ (⊢` there (here refl)))

  S-ty : ⊢ S ∶ ((`` "A" ⟶ `` "B" ⟶ `` "C") ⟶ (`` "A" ⟶ `` "B") ⟶ `` "A" ⟶ `` "C")
  S-ty = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ ⊢ ⊢` there (there (here refl)) ⟶ (⊢` here refl) ⟶ (⊢ ⊢` there (here refl) ⟶ (⊢` (here refl))))))
