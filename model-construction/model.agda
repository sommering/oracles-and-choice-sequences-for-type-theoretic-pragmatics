module model where

open import Agda.Primitive

data _==_ {i} {A : Set i} (M : A) : A → Set i where
  refl : M == M

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

record LogicalFramework : Set₁ where
  field
    signature : Set
    term : signature → Set
    _≼_ : signature → signature → Set
    id : ∀ {Ψ} → Ψ ≼ Ψ
    trans : ∀ {Ψ Ψ′ Ψ′′} → Ψ ≼ Ψ′ → Ψ′ ≼ Ψ′′ → Ψ ≼ Ψ′′
    _↿_ : ∀ {Ψ Ψ′} → term Ψ → Ψ ≼ Ψ′ → term Ψ′
    id-law : ∀ {Ψ} (M : term Ψ) → (M ↿ id) == M
    --trans-law : ∀ {Ψ Ψ′ Ψ′′ α β} → {!!} == {!!}

𝔓_ : Set → Set₁
𝔓_ A = A → Set

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor ⟨_,_⟩
  field
    π₁ : A
    π₂ : B π₁

∫_ : ∀ {i} {A : Set i} → (A → Set i) → Set i
∫ F = Σ _ F

module _ (LF : LogicalFramework) where
  module LF = LogicalFramework LF

  record World : Set₁ where
    constructor ⟨_,_,_⟩
    field
      Ψ : LF.signature          -- a signature in the logical framework
      𝒯 : 𝔓 LF.term Ψ          -- the collection of terms which we have recognized as types
      𝒦 : ∫ 𝒯 → 𝔓 LF.term Ψ   -- for each known type, the collection of effected constructions

  record _≼_ (u : World) (v : World) : Set where
    constructor ⟨_,_,_⟩
    private module u = World u; module v = World v; open LF
    field
      Ψ : u.Ψ LF.≼ v.Ψ
      𝒯 : ∀ {A} → u.𝒯 A → v.𝒯 (A ↿ Ψ)
      𝒦 : ∀ {A} 𝒯A M → u.𝒦 ⟨ A , 𝒯A ⟩ M → v.𝒦 ⟨ A ↿ Ψ , 𝒯 𝒯A ⟩ (M ↿ Ψ)

  reflexivity : (u : World) → u ≼ u
  reflexivity ⟨ Ψ , 𝒯 , 𝒦 ⟩ = ⟨ id , 𝒯-id , 𝒦-id ⟩
    where
      open LF

      𝒯-id : {A : term Ψ} → 𝒯 A → 𝒯 (A ↿ id)
      𝒯-id {A} 𝒯A rewrite id-law A = 𝒯A

      𝒦-id : {A : term Ψ} (𝒯A : 𝒯 A) (M : term Ψ) → 𝒦 ⟨ A , 𝒯A ⟩ M → 𝒦 ⟨ A ↿ id , 𝒯-id 𝒯A ⟩ (M ↿ id)
      𝒦-id {A} 𝒯A M 𝒦M rewrite id-law M | id-law A = 𝒦M

  transitivity : (u v w : World) → u ≼ v → v ≼ w → u ≼ w
  transitivity u v w α β = ⟨ Ψ-trans , 𝒯-trans , {!!} ⟩
    where
      open LF ; module u = World u ; module v = World v ; module w = World w
      module α = _≼_ α; module β = _≼_ β

      Ψ-trans : u.Ψ LF.≼ w.Ψ
      Ψ-trans = trans α.Ψ β.Ψ

      𝒯-trans : {A : term u.Ψ} → u.𝒯 A → w.𝒯 (A ↿ Ψ-trans)
      𝒯-trans {A} 𝒯A = {!!}


  𝒟 : World → Set
  𝒟 ⟨ Ψ , 𝒯 , 𝒦 ⟩ = LF.term Ψ

  Judgment : (i : Level) → Set (lsuc i)
  Judgment i = World → Set i

  _⊩_ : ∀ {i} → World → Judgment i → Set i
  w ⊩ J = J w

  _⇒_ : ∀ {i j} → Judgment i → Judgment j → Judgment (lsuc lzero ⊔ i ⊔ j)
  (J₁ ⇒ J₂) w = ∀ (u : World) → w ≼ u → u ⊩ J₁ → u ⊩ J₂

