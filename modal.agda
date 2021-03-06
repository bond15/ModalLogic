module modal where

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Bool

open import Agda.Builtin.String

data ty : Set where 
    š : ty
    ā” : ty ā ty
    _ā_ _&_ : ty ā ty ā ty

data tm : Set where 
    var : String ā tm 
    _ā_ _,_ : tm ā tm ā tm
    Ļā Ļā : tm ā tm
    Ę_ā·_ā_ : String ā ty ā tm ā tm 
    u : tm
    -- adding box modality
    box : tm ā tm
    letbox_ā£_inn_ : String ā tm ā tm ā tm

data _value : tm ā Set where 
    ĘV : ā {x T t} ā (Ę x ā· T ā t) value
    &V : ā{t1 t2} ā t1 value ā t2 value ā (t1 , t2) value
    uV : u value
    boxV : ā{t} ā (box t) value
 
_=ā_ : String ā String ā Bool 
_=ā_ = primStringEquality

[_/_]_ : tm ā String ā tm ā tm
[ s / x ] t@(var y) = if (x =ā y) then s else t
[ s / x ] (t ā t') = ([ s / x ] t) ā ([ s / x ] t')
[ s / x ] (Ļā t') = Ļā ([ s / x ] t')
[ s / x ] (Ļā t') = Ļā ([ s / x ] t')
[ s / x ] (t , t') = [ s / x ] t , [ s / x ] t'
[ s / x ] t@(Ę y ā· T ā t') = if (x =ā y) then t else (Ę x ā· T ā [ s / x ] t')
[ s / x ] u = u
-- adding box modality
[ s / x ] t@(box d) = t
[ s / x ] (letbox d ā£ xā inn dā) = {!   !}

data _ā¶_ : tm ā tm ā Set where
    st-Ę : ā{A N M x} ā M value ā ((Ę x ā· A ā N) ā M) ā¶ ([ M / x ] N)
    st-&ā : ā{M N} ā M value ā N value ā (Ļā(M , N)) ā¶ M 
    st-&ā : ā{M N}Ā ā M value ā N value ā (Ļā(M , N)) ā¶ N
    st-&cā : ā{M M' N} ā (M ā¶ M') ā (M , N) ā¶ (M' , N) 
    st-&cā : ā{M N N'} ā M value ā (N ā¶ N') ā (M , N) ā¶ (M , N')
    st-Ļāc : ā{M M'} ā M ā¶ M' ā (Ļā M) ā¶ (Ļā M')
    st-Ļāc : ā{M M'} ā M ā¶ M' ā (Ļā M) ā¶ (Ļā M')
    st-ācā : ā{M M' N} ā M ā¶ M' ā (M ā N) ā¶ (M' ā N)
    st-ācā : ā{M N N'} ā M value ā N ā¶ N' ā (M ā N) ā¶ (M ā N')

    st-lbc : ā{u M N M'} ā M ā¶ M' ā (letbox u ā£ M inn N) ā¶ (letbox u ā£ M' inn N)
    st-lbd : ā{u M N} ā (letbox u ā£ (box M) inn N) ā¶ ([ M / u ]  N)

data multi {X : Set}(R : X ā X ā Set) : X ā X ā Set where
    mrefl : ā{x : X} ā multi R x x 
    mstep : ā { x y z : X} ā R x y ā multi R y z ā multi R x z

_~>*_ : tm ā tm ā Set 
t ~>* t' = multi _ā¶_ t t'

_ : ((Ę "x"  ā· š ā var "x") ā Ļā (u , u)) ~>* u
_ = mstep (st-ācā ĘV (st-&ā uV uV)) 
    (mstep (st-Ę uV) 
     mrefl)


module kripke where 




{-


data type : Set where
    Unit Nat : type
    box : type ā type
    _ā_ _&_ : type -> type -> type    
     
data Id (A : Set): Set where 
    id : A ā Id A

ā¦_ā¦ : type ā Set
ā¦ Unit ā¦ = ā¤
ā¦ Nat ā¦ = ā
ā¦ box t ā¦ = Id ā¦ t ā¦
ā¦ n ā m ā¦ = ā¦ n ā¦ ā ā¦ m ā¦
ā¦ s & t ā¦ = ā¦ s ā¦ Ć ā¦ t ā¦


data term : type ā Set where
    ā§I : ā{t s} ā term t ā term s ā term (t & s)
    ā¤I : term Unit 
    Ī»I : ā {dom ran} ā ( ā¦ dom ā¦ ā term ran) ā term (dom ā ran)
    const : ā¦ Nat ā¦ ā term Nat
    ā” : ā{t} ā term t ā term t


_ : term Nat ā term (box (Nat ā Nat))
_ = Ī» { (const x) ā {! Ī»I ? !}
      ; (ā” x) ā {!   !}}



data Value : {t : type} ā term t ā  Set where 
    imp : ā{t : type} ā (M : term t) ā  



module Phoas (var : type -> Set) where
     data exp : type -> Set where
          Var : ā {t : type} ā (var t ā exp t )
          _ā§_ : ā {s t : type} ā exp s ā exp t ā exp (s & t)
          --_ā_ : ā {dom ran} ā exp (dom ā ran) ā exp dom ā exp ran
          Ę : ā {dom ran} ā (var dom ā exp ran) ā exp (dom ā ran)     

module Ex1 where
     -- interpret the types into Agda types
    open Phoas Value
    
    _ : exp (Unit & Nat) 
    _ = Var tt ā§ Var 4

-}