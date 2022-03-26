module modal where

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Bool

open import Agda.Builtin.String

data ty : Set where 
    𝕌 : ty
    □ : ty → ty
    _⇒_ _&_ : ty → ty → ty

data tm : Set where 
    var : String → tm 
    _●_ _,_ : tm → tm → tm
    π₁ π₂ : tm → tm
    ƛ_∷_∙_ : String → ty → tm → tm 
    u : tm
    -- adding box modality
    box : tm → tm
    letbox_≣_inn_ : String → tm → tm → tm

data _value : tm → Set where 
    ƛV : ∀ {x T t} → (ƛ x ∷ T ∙ t) value
    &V : ∀{t1 t2} → t1 value → t2 value → (t1 , t2) value
    uV : u value
    boxV : ∀{t} → (box t) value
 
_=ₛ_ : String → String → Bool 
_=ₛ_ = primStringEquality

[_/_]_ : tm → String → tm → tm
[ s / x ] t@(var y) = if (x =ₛ y) then s else t
[ s / x ] (t ● t') = ([ s / x ] t) ● ([ s / x ] t')
[ s / x ] (π₁ t') = π₁ ([ s / x ] t')
[ s / x ] (π₂ t') = π₂ ([ s / x ] t')
[ s / x ] (t , t') = [ s / x ] t , [ s / x ] t'
[ s / x ] t@(ƛ y ∷ T ∙ t') = if (x =ₛ y) then t else (ƛ x ∷ T ∙ [ s / x ] t')
[ s / x ] u = u
-- adding box modality
[ s / x ] t@(box d) = t
[ s / x ] (letbox d ≣ x₁ inn d₁) = {!   !}

data _⟶_ : tm → tm → Set where
    st-ƛ : ∀{A N M x} → M value → ((ƛ x ∷ A ∙ N) ● M) ⟶ ([ M / x ] N)
    st-&₁ : ∀{M N} → M value → N value → (π₁(M , N)) ⟶ M 
    st-&₂ : ∀{M N} → M value → N value → (π₂(M , N)) ⟶ N
    st-&c₁ : ∀{M M' N} → (M ⟶ M') → (M , N) ⟶ (M' , N) 
    st-&c₂ : ∀{M N N'} → M value → (N ⟶ N') → (M , N) ⟶ (M , N')
    st-π₁c : ∀{M M'} → M ⟶ M' → (π₁ M) ⟶ (π₁ M')
    st-π₂c : ∀{M M'} → M ⟶ M' → (π₂ M) ⟶ (π₂ M')
    st-●c₁ : ∀{M M' N} → M ⟶ M' → (M ● N) ⟶ (M' ● N)
    st-●c₂ : ∀{M N N'} → M value → N ⟶ N' → (M ● N) ⟶ (M ● N')

    st-lbc : ∀{u M N M'} → M ⟶ M' → (letbox u ≣ M inn N) ⟶ (letbox u ≣ M' inn N)
    st-lbd : ∀{u M N} → (letbox u ≣ (box M) inn N) ⟶ ([ M / u ]  N)

data multi {X : Set}(R : X → X → Set) : X → X → Set where
    mrefl : ∀{x : X} → multi R x x 
    mstep : ∀ { x y z : X} → R x y → multi R y z → multi R x z

_~>*_ : tm → tm → Set 
t ~>* t' = multi _⟶_ t t'

_ : ((ƛ "x"  ∷ 𝕌 ∙ var "x") ● π₁ (u , u)) ~>* u
_ = mstep (st-●c₂ ƛV (st-&₁ uV uV)) 
    (mstep (st-ƛ uV) 
     mrefl)


module kripke where 




{-


data type : Set where
    Unit Nat : type
    box : type → type
    _⇒_ _&_ : type -> type -> type    
     
data Id (A : Set): Set where 
    id : A → Id A

⦅_⦆ : type → Set
⦅ Unit ⦆ = ⊤
⦅ Nat ⦆ = ℕ
⦅ box t ⦆ = Id ⦅ t ⦆
⦅ n ⇒ m ⦆ = ⦅ n ⦆ → ⦅ m ⦆
⦅ s & t ⦆ = ⦅ s ⦆ × ⦅ t ⦆


data term : type → Set where
    ∧I : ∀{t s} → term t → term s → term (t & s)
    ⊤I : term Unit 
    λI : ∀ {dom ran} → ( ⦅ dom ⦆ → term ran) → term (dom ⇒ ran)
    const : ⦅ Nat ⦆ → term Nat
    □ : ∀{t} → term t → term t


_ : term Nat → term (box (Nat ⇒ Nat))
_ = λ { (const x) → {! λI ? !}
      ; (□ x) → {!   !}}



data Value : {t : type} → term t →  Set where 
    imp : ∀{t : type} → (M : term t) →  



module Phoas (var : type -> Set) where
     data exp : type -> Set where
          Var : ∀ {t : type} → (var t → exp t )
          _∧_ : ∀ {s t : type} → exp s → exp t → exp (s & t)
          --_●_ : ∀ {dom ran} → exp (dom ⇒ ran) → exp dom → exp ran
          ƛ : ∀ {dom ran} → (var dom → exp ran) → exp (dom ⇒ ran)     

module Ex1 where
     -- interpret the types into Agda types
    open Phoas Value
    
    _ : exp (Unit & Nat) 
    _ = Var tt ∧ Var 4

-}