open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary

open import Function

-- Fin defined as a refinement type.
record BFin (u : ℕ) : Set where
  constructor _bounded_
  field
    v : ℕ
    .v<u : v < u

open BFin

-- An eliminator for the irrelevant bottom type.
⊥-elim-irr : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim-irr ()

-- Some BFin properties and actions.
bfin-to-< : ∀ {n}{x : BFin n} → v x < n
bfin-to-< {n}{x bounded x<n} with x <? n
... | yes p = p
... | no ¬p = ⊥-elim-irr (¬p x<n)

bfin-projv : ∀ {n}{x y : BFin n} → x ≡ y → v x ≡ v y
bfin-projv refl = refl

bfin-cong : ∀ {n}{x y : BFin n} → v x ≡ v y → x ≡ y
bfin-cong refl = refl

bfin-pedantic-cong : ∀ {u x y} → x ≡ y → .(x<u : x < u) → .(y<u : y < u) → x bounded x<u ≡ y bounded y<u
bfin-pedantic-cong refl x<u y<u = refl

bfin-id : ∀ {n} → (i : BFin n) → let (_ bounded i<n) = i in v i bounded i<n ≡ i 
bfin-id (i bounded _) = refl

bfin-subst : ∀ {m}{i : BFin m}{n}{m≡n : m ≡ n}
           → BFin.v (subst BFin m≡n i) ≡ BFin.v i
bfin-subst {i = i bounded i<m}{n}{refl} = refl

_≟b_ : ∀ {n} → Decidable (_≡_ {A = BFin n})
(x bounded _) ≟b (y bounded _) with x ≟ y
... | yes refl = yes refl
... | no ¬p = no λ fx≡fy → contradiction (bfin-projv fx≡fy) ¬p

bsuc : ∀ {n} → BFin n → BFin (suc n)
bsuc (i bounded i<n) = suc i bounded s≤s i<n

blookup : ∀ {a}{n}{X : Set a} → Vec X n → BFin n → X
blookup {n = suc n} (x ∷ xs) (zero bounded v<u) = x
blookup {n = suc n} (x ∷ xs) (suc i bounded v<u) = blookup xs (i bounded ≤-pred v<u)

btabulate : ∀ {a}{n}{X : Set a} → (BFin n → X) → Vec X n
btabulate {n = zero} f = []
btabulate {n = suc n} f = (f (0 bounded 0<1+n)) ∷ btabulate (f ∘ bsuc)

btabulate∘blookup : ∀ {a}{n}{X : Set a}{v : Vec X n} → btabulate (blookup v) ≡ v
btabulate∘blookup {n = zero} {v = []} = refl
btabulate∘blookup {n = suc n} {v = x ∷ v₁} = cong₂ _∷_ refl btabulate∘blookup

blookup∘btabulate : ∀ {a}{n}{X : Set a}{f : BFin n → X} → ∀ i → blookup (btabulate f) i ≡ f i
blookup∘btabulate {n = suc n} (zero bounded i<n) = refl
blookup∘btabulate {n = suc n} (suc i bounded i<n) = blookup∘btabulate {n = n} (i bounded ≤-pred i<n)

--magic-bfin : ∀ {a}{X : Set a} → BFin 0 → X
--magic-bfin ()

¬BFin0 : ∀ {a}{X : Set a} (i : BFin 0) → X
¬BFin0 (i bounded ())

-- Some further facts about BFin.
-- Similarly to Fin:
--   binect increases the bound;
--   braise increases the bound and the element
binject : ∀ {m n} → BFin m → BFin (m + n)
binject (x bounded x<m) = x bounded ≤-trans x<m (m≤m+n _ _)

braise : ∀ {m n} → BFin m → BFin (n + m)
braise {m}{n} (x bounded x<m) = (n + x) bounded +-monoʳ-< n x<m


x≥y⇒[1+x]-y≡1+[x-y] : ∀ {x y} → x ≥ y → suc x ∸ y ≡ suc (x ∸ y)
x≥y⇒[1+x]-y≡1+[x-y] {x} {zero} x≥y = refl
x≥y⇒[1+x]-y≡1+[x-y] {suc x} {suc y} (s≤s x≥y) = x≥y⇒[1+x]-y≡1+[x-y] x≥y

breduce : ∀ {m n} → (i : BFin (m + n)) → (v i ≥ m) → BFin n
breduce {m}{n} (x bounded x<m+n) x≥m = (x ∸ m) bounded (subst₂ _≤_ (x≥y⇒[1+x]-y≡1+[x-y] x≥m)
                                                                   (m+n∸m≡n m n)
                                                                   $ ∸-monoˡ-≤ m x<m+n)

binject≤ : ∀ {m n} → BFin m → .(m ≤ n) → BFin n
binject≤ (x bounded x<m) m≤n = x bounded ≤-trans x<m m≤n

breduce< : ∀ {m n} → (i : BFin m) → .(v i < n) → BFin n
breduce< (i bounded _) pf = i bounded pf


binject≤-thm : ∀ {m n}{i j}.{m≤n : m ≤ n} → v i ≡ v j → binject≤ i m≤n ≡ j
binject≤-thm refl = refl

breduce<-thm : ∀ {m n}{i : BFin m}.{vi<n} → BFin.v (breduce< {n = n} i vi<n) ≡ BFin.v i
breduce<-thm {i = i bounded i<m}{i<n} with breduce< (i bounded i<m) i<n
... | q = refl
