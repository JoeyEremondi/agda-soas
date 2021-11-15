
open import SOAS.Metatheory.Syntax

-- Second-order equational logic library
module SOAS.Metatheory.SecondOrder.Preorder {T : Set} (Syn : Syntax {T}) where

open import SOAS.Common
open import SOAS.Families.Core {T}
open import SOAS.Context
open import SOAS.Variable

open import SOAS.Metatheory.FreeMonoid Syn

open import SOAS.Metatheory.SecondOrder.Metasubstitution Syn
open import SOAS.Metatheory.SecondOrder.Unit Syn

open import SOAS.ContextMaps.CategoryOfRenamings {T}
open import SOAS.Families.Build

open import SOAS.Metatheory Syn
open Syntax Syn
open Theory

private
  variable
    α β γ : T
    Γ Δ Π : Ctx
    𝔐 𝔑 : MCtx

-- Equational reasoning system extended from an axiom relation on terms
module PreOrderLogic (_▹_⊢_≼ₐ_ : ∀ 𝔐 Γ {α} → (𝔐 ▷ 𝕋) α Γ → (𝔐 ▷ 𝕋) α Γ → Set) where
  -- Equality between terms: smallest equivalence relation closed under the axioms
  -- and parametrised metasubstitution
  data _▹_⊢_≼_ : (𝔐 : MCtx){α : T}(Γ : Ctx) → (𝔐 ▷ 𝕋) α Γ → (𝔐 ▷ 𝕋) α Γ → Set₁ where
    ax  : {t s : (𝔐 ▷ 𝕋) α Γ} → 𝔐 ▹ Γ ⊢ t ≼ₐ s →  𝔐 ▹ Γ ⊢ t ≼ s
    eq  : {t s : (𝔐 ▷ 𝕋) α Γ} → t ≡ s → 𝔐 ▹ Γ ⊢ t ≼ s
    tr  : {t s u : (𝔐 ▷ 𝕋) α Γ} → 𝔐 ▹ Γ ⊢ t ≼ s → 𝔐 ▹ Γ ⊢ s ≼ u → 𝔐 ▹ Γ ⊢ t ≼ u
    □ms : {t s : (𝔐 ▷ 𝕋) α Γ}
        → 𝔐 ▹ Γ ⊢ t ≼ s
        → (ρ : Γ ↝ Δ)
        → (ζ ξ : MSub Δ 𝔐 𝔑)
        → (∀{τ Π}(𝔪 : Π ⊩ τ ∈ 𝔐) → 𝔑 ▹ (Π ∔ Δ) ⊢ (ix≀ ζ 𝔪) ≼ (ix≀ ξ 𝔪))
        → 𝔑 ▹ Δ ⊢ (□msub≀ t ρ ζ) ≼ (□msub≀ s ρ ξ)

  -- Reflexivity of ≼ lifted from refl
  rf : {t : (𝔐 ▷ 𝕋) α Γ} → 𝔐 ▹ Γ ⊢ t ≼ t
  rf = eq refl

  infix 1 _▹_⊢_≼_

  -- Helpers for equational reasoning
  module ≼-Reasoning where

    _≼⟨_⟩_ : (t : (𝔐 ▷ 𝕋) α Γ) {s u : (𝔐 ▷ 𝕋) α Γ}
           → 𝔐 ▹ Γ ⊢ t ≼ s
           → 𝔐 ▹ Γ ⊢ s ≼ u
           → 𝔐 ▹ Γ ⊢ t ≼ u
    t ≼⟨ t≼s ⟩ s≼u = tr {t = t} t≼s s≼u

    _≡⟨_⟩_ : (t : (𝔐 ▷ 𝕋) α Γ){s : (𝔐 ▷ 𝕋) α Γ} {u : (𝔐 ▷ 𝕋) α Γ}
           → t ≡ s
           → 𝔐 ▹ Γ ⊢ s ≼ u
           → 𝔐 ▹ Γ ⊢ t ≼ u
    t ≡⟨ t≡s ⟩ s≼u = t ≼⟨ eq t≡s ⟩ s≼u

    _≡⟨⟩_ : (t : (𝔐 ▷ 𝕋) α Γ) {s : (𝔐 ▷ 𝕋) α Γ}
           → 𝔐 ▹ Γ ⊢ t ≼ s
           → 𝔐 ▹ Γ ⊢ t ≼ s
    t ≡⟨⟩ t≼s = t ≡⟨ refl ⟩ t≼s

    begin_ : {t s : (𝔐 ▷ 𝕋) α Γ} → 𝔐 ▹ Γ ⊢ t ≼ s → 𝔐 ▹ Γ ⊢ t ≼ s
    begin t≼s = t≼s

    _∎ : (t : (𝔐 ▷ 𝕋) α Γ) → 𝔐 ▹ Γ ⊢ t ≼ t
    t ∎ = rf

    infix  1 begin_
    infixr 2 _≼⟨_⟩_
    infixr 2 _≡⟨_⟩_
    infixr 2 _≡⟨⟩_
    infix  3 _∎

  -- Rewrite two sides of ≼ with ≡
  rw : {t t′ s s′ : (𝔐 ▷ 𝕋) α Γ}
     → t ≡ t′ → s ≡ s′ → 𝔐 ▹ Γ ⊢ t ≼ s → 𝔐 ▹ Γ ⊢ t′ ≼ s′
  rw {t = t}{t′}{s}{s′} t≡t′ s≡s′ t≼s =
    begin t′ ≡⟨ sym t≡t′ ⟩ t ≼⟨ t≼s ⟩ s ≡⟨ s≡s′ ⟩ s′ ∎
      where open ≼-Reasoning

  -- Closure under base metasubstitution
  ms : {t s : (𝔐 ▷ 𝕋) α Γ}
     → 𝔐 ▹ Γ ⊢ t ≼ s
     → (ζ ξ : MSub Γ 𝔐 𝔑)
     → (∀{τ Π}(𝔪 : Π ⊩ τ ∈ 𝔐) → 𝔑 ▹ (Π ∔ Γ) ⊢ (ix≀ ζ 𝔪) ≼ (ix≀ ξ 𝔪))
     → 𝔑 ▹ Γ ⊢ msub≀ t ζ ≼ msub≀ s ξ
  ms {t = t}{s} t≼s ζ ξ ζ≼ξ = rw (□msub-id t (ix≀ ζ)) (□msub-id s (ix≀ ξ)) (□ms t≼s id ζ ξ ζ≼ξ)

  -- Metasubstitution of same mapping applied to two equivalent terms
  ms-eq : {t s : (𝔐 ▷ 𝕋) α Γ}
     → 𝔐 ▹ Γ ⊢ t ≼ s
     → (ζ : MSub Γ 𝔐 𝔑)
     → 𝔑 ▹ Γ ⊢ msub≀ t ζ ≼ msub≀ s ζ
  ms-eq {t = t}{s} t≼s ζ = ms t≼s ζ ζ (λ 𝔪 → rf)

  -- Closure under renaming
  ren≼ : {t s : (𝔐 ▷ 𝕋) α Γ}
         → 𝔐 ▹ Γ ⊢ t ≼ s
         → (ρ : Γ ↝ Δ)
         → 𝔐 ▹ Δ ⊢ 𝕣𝕖𝕟 ∥ 𝔐 ∥ t ρ ≼ 𝕣𝕖𝕟 ∥ 𝔐 ∥ s ρ
  ren≼ {𝔐}{α}{Γ}{Δ}{t = t}{s} t≼s ρ =
    begin
        (𝕣𝕖𝕟 ∥ 𝔐 ∥ t ρ)
    ≡⟨ sym (□msub-runit t ρ) ⟩
        □msub t ρ ms-unit
    ≡⟨ sym (cong (□msub t ρ) (iext (dext (id≀≈ms-unit Δ)))) ⟩
        □msub≀ t ρ (id≀ Δ)
    ≼⟨ □ms t≼s ρ (id≀ Δ) (id≀ Δ) (λ 𝔪 → rf) ⟩
        □msub≀ s ρ (id≀ Δ)
    ≡⟨ cong (□msub s ρ) (iext (dext (id≀≈ms-unit Δ))) ⟩
        □msub s ρ ms-unit
    ≡⟨ □msub-runit s ρ ⟩
        (𝕣𝕖𝕟 ∥ 𝔐 ∥ s ρ)
    ∎ where open ≼-Reasoning

  -- Lemma to apply equality to terms attached to the end of a metasubstitution
  ▹-eq : {Π′ : Ctx}{s u : (𝔑 ▷ 𝕋) β (Π′ ∔ Γ)}
       → 𝔑 ▹ (Π′ ∔ Γ) ⊢ s ≼ u → (ζ ξ : MSub Γ 𝔐 𝔑)
       → (∀{τ Π}(𝔪 : Π ⊩ τ ∈ 𝔐) → 𝔑 ▹ (Π ∔ Γ) ⊢ (ix≀ ζ 𝔪) ≼ (ix≀ ξ 𝔪))
       → (𝔪 : Π ⊩ α ∈ (𝔐 ⁅ Π′ ⊩ₙ β ⁆))
       → 𝔑 ▹ Π ∔ Γ ⊢ ix≀ (ζ ▹ s) 𝔪 ≼ ix≀ (ξ ▹ u) 𝔪
  ▹-eq e ◦ ◦ ζ≼ξ ↓ = e
  ▹-eq e (x ◃ ζ) (y ◃ ξ) ζ≼ξ ↓ = ζ≼ξ ↓
  ▹-eq e (x ◃ ζ) (y ◃ ξ) ζ≼ξ (↑ 𝔪) = ▹-eq e ζ ξ (λ 𝔫 → ζ≼ξ (↑ 𝔫)) 𝔪

  -- Congruence: metasubstitution of equivalent terms into a term extended with
  -- a new metavariable
  cong≼ : (t : (𝔐 ⁅ Π ⊩ₙ β ⁆ ▷ 𝕋) α Γ)
      → {s u : (𝔐 ▷ 𝕋) β (Π ∔ Γ)}
      → 𝔐 ▹ (Π ∔ Γ) ⊢ s ≼ u
      → 𝔐 ▹ Γ ⊢ instₑ t s ≼ instₑ t u
  cong≼ t {s} {u} s≼u = ms rf (id≀ _ ▹ s) (id≀ _ ▹ u) (▹-eq s≼u (id≀ _) (id≀ _) λ _ → rf)

  -- Double congruence
  cong₂≼ : {Π₁ Π₂ : Ctx}{β₁ β₂ : T}
        (t : ((𝔐 ⁅ Π₁ ⊩ₙ β₁ ⁆) ⁅ Π₂ ⊩ₙ β₂ ⁆ ▷ 𝕋) α Γ)
      → {s₁ u₁ : (𝔐 ▷ 𝕋) β₁ (Π₁ ∔ Γ)}
      → {s₂ u₂ : (𝔐 ▷ 𝕋) β₂ (Π₂ ∔ Γ)}
      → 𝔐 ▹ (Π₁ ∔ Γ) ⊢ s₁ ≼ u₁
      → 𝔐 ▹ (Π₂ ∔ Γ) ⊢ s₂ ≼ u₂
      → 𝔐 ▹ Γ ⊢ instₑ₂ t s₁ s₂ ≼ instₑ₂ t u₁ u₂
  cong₂≼ t {s₁}{u₁}{s₂}{u₂} s≼u₁ s≼u₂ =
    ms rf ((id≀ _ ▹ s₁) ▹ s₂) ((id≀ _ ▹ u₁) ▹ u₂)
    (▹-eq s≼u₂ (id≀ _ ▹ s₁) (id≀ _ ▹ u₁) (▹-eq s≼u₁ (id≀ _) (id≀ _) (λ - → rf)))

  -- Syntactic sugar
  cong[_]inside_ : {s u : (𝔐 ▷ 𝕋) β (Π ∔ Γ)}
      → 𝔐 ▹ (Π ∔ Γ) ⊢ s ≼ u
      → (t : (𝔐 ⁅ Π ⊩ₙ β ⁆ ▷ 𝕋) α Γ)
      → 𝔐 ▹ Γ ⊢ instₑ t s ≼ instₑ t u
  cong[ s≼u ]inside t = cong≼ t s≼u
  infix 05 cong[_]inside_
  cong₂[_][_]inside_ : {Π₁ Π₂ : Ctx}{β₁ β₂ : T}
      → {s₁ u₁ : (𝔐 ▷ 𝕋) β₁ (Π₁ ∔ Γ)}
      → {s₂ u₂ : (𝔐 ▷ 𝕋) β₂ (Π₂ ∔ Γ)}
      → 𝔐 ▹ (Π₁ ∔ Γ) ⊢ s₁ ≼ u₁
      → 𝔐 ▹ (Π₂ ∔ Γ) ⊢ s₂ ≼ u₂
      → (t : ((𝔐 ⁅ Π₁ ⊩ₙ β₁ ⁆) ⁅ Π₂ ⊩ₙ β₂ ⁆ ▷ 𝕋) α Γ)
      → 𝔐 ▹ Γ ⊢ instₑ₂ t s₁ s₂ ≼ instₑ₂ t u₁ u₂
  cong₂[ s≼u₁ ][ s≼u₂ ]inside t = cong₂≼ t s≼u₁ s≼u₂
  infix 05 cong₂[_][_]inside_

  -- Linear metasubstitution
  ○ms : {t s : (𝔐 ▷ 𝕋) α Γ}
     → 𝔐 ▹ Γ ⊢ t ≼ s
     → (ζ ξ : MSub Δ 𝔐 𝔑)
     → (∀{τ Π}(𝔪 : Π ⊩ τ ∈ 𝔐) → 𝔑 ▹ (Π ∔ Δ) ⊢ (ix≀ ζ 𝔪) ≼ (ix≀ ξ 𝔪))
     → 𝔑 ▹ Γ ∔ Δ ⊢ ○msub≀ t ζ ≼ ○msub≀ s ξ
  ○ms {Γ = Γ}{𝔑 = 𝔑}{t = t}{s} t≼s ζ ξ ζ≼ξ = □ms t≼s (inl Γ) (inr≀ Γ ζ) (inr≀ Γ ξ) (λ {τ}{Π} 𝔪 → begin
        ix≀ (inr≀ Γ ζ) 𝔪
    ≡⟨ ix-inr≀ ζ 𝔪 ⟩
        (𝕣𝕖𝕟 ∥ 𝔑 ∥ (ix≀ ζ 𝔪) (Π ∔∣ inr Γ))
    ≼⟨ ren≼ (ζ≼ξ 𝔪) (Π ∔∣ inr Γ) ⟩
        (𝕣𝕖𝕟 ∥ 𝔑 ∥ (ix≀ ξ 𝔪) (Π ∔∣ inr Γ))
    ≡⟨ sym (ix-inr≀ ξ 𝔪) ⟩
        ix≀ (inr≀ Γ ξ) 𝔪
    ∎) where open ≼-Reasoning

  -- Linear metasubstitution of same mapping applied to two equivalent terms
  ○ms-eq : {t s : (𝔐 ▷ 𝕋) α Π}
     → 𝔐 ▹ Π ⊢ t ≼ s
     → (ζ : MSub Γ 𝔐 𝔑)
     → 𝔑 ▹ Π ∔ Γ ⊢ ○msub≀ t ζ ≼ ○msub≀ s ζ
  ○ms-eq {t = t}{s} t≼s ζ = ○ms t≼s ζ ζ (λ 𝔪 → rf)

  -- Application of an axiom as a rewrite rule, and syntactic sugar
  ax≼ : {t s : (𝔐 ▷ 𝕋) α Π}
      → 𝔐 ▹ Π ⊢ t ≼ₐ s → (ζ : MSub Γ 𝔐 𝔑)
      → 𝔑 ▹ Π ∔ Γ ⊢ ○msub≀ t ζ ≼ ○msub≀ s ζ
  ax≼ a ζ = ○ms-eq (ax a) ζ

  ax_with《_ : {t s : (𝔐 ▷ 𝕋) α Π}
      → 𝔐 ▹ Π ⊢ t ≼ₐ s → (ζ : MSub Γ 𝔐 𝔑)
      → 𝔑 ▹ Π ∔ Γ ⊢ ○msub≀ t ζ ≼ ○msub≀ s ζ
  ax_with《_ = ax≼

  infix 15 ax_with《_

  -- Application of an equivalence as a rewrite rule, and syntactic sugar
  thm_with《_ : {t s : (𝔐 ▷ 𝕋) α Π}
     → 𝔐 ▹ Π ⊢ t ≼ s
     → (ζ : MSub Γ 𝔐 𝔑)
     → 𝔑 ▹ Π ∔ Γ ⊢ ○msub≀ t ζ ≼ ○msub≀ s ζ
  thm_with《_ = ○ms-eq
  infix 15 thm_with《_

  -- Application of theorem with no metavariables
  thm : {t s : (⁅⁆ ▷ 𝕋) α Π}
      → ⁅⁆ ▹ Π ⊢ t ≼ s
      → 𝔐 ▹ Π ∔ Γ ⊢ ○msub≀ t ◦ ≼ ○msub≀ s ◦
  thm e = thm e with《 ◦
