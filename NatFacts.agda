open import Data.Nat
open import Data.Nat.DivMod 
open import Data.Nat.Properties
open import Data.Nat.Divisibility

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary

open import Data.Empty
open import Data.Sum

a*b≢0⇒a≢0 : ∀ {a b} → a * b ≢ 0 → a ≢ 0
a*b≢0⇒a≢0 {zero}    {b} 0≢0 0≡0 = 0≢0 0≡0
a*b≢0⇒a≢0 {(suc a)} {b} _       = λ ()

a*b≢0⇒b≢0 : ∀ {a b} → a * b ≢ 0 → b ≢ 0
a*b≢0⇒b≢0 {a} {b} rewrite (*-comm a b) = a*b≢0⇒a≢0

-- A basic fact about division that is not yet in the stdlib.
/-mono-x : ∀ {a b c} → a < b * c → (c≢0 : False (c ≟ 0))
         → (a / c) {≢0 = c≢0} < b
/-mono-x {a}{b}{c} a<b*c c≢0 with <-cmp ((a / c) {≢0 = c≢0}) b
/-mono-x {a} {b} {c} a<b*c c≢0 | tri< l< _ _ = l<
/-mono-x {a} {b} {c} a<b*c c≢0 | tri≈ _ l≡ _ = let
     a<a/c*c = subst (a <_) (cong₂ _*_ (sym l≡) refl) a<b*c
     a/c*c≤a = m/n*n≤m a c {≢0 = c≢0}
     a<a = ≤-trans a<a/c*c a/c*c≤a
   in contradiction a<a (n≮n a)
/-mono-x {a} {b} {suc c} a<b*c c≢0 | tri> _ _ l> = let
     b*c<a/c*c = *-monoˡ-< c l>
     a/c*c≤a = m/n*n≤m a (suc c) {≢0 = c≢0}
     b*c≤a = ≤-trans b*c<a/c*c a/c*c≤a
     a<a = <-trans a<b*c b*c≤a
   in contradiction a<a (n≮n a)


n≢0⇒m%n<n : ∀ {m n} → (pf : n ≢ 0) → (m % n) {≢0 = fromWitnessFalse pf} < n
n≢0⇒m%n<n {n = zero} pf = contradiction refl pf
n≢0⇒m%n<n {m}{n = suc n} pf = m%n<n m n

divmod-thm : ∀ {a b m n}
           → (n≢0 : n ≢ 0)
           → a ≡ (m % n) {≢0 = fromWitnessFalse n≢0}
           → b ≡ (m / n) {≢0 = fromWitnessFalse n≢0} * n
             → m ≡ a + b
divmod-thm {n = zero} n≢0 _ _ = contradiction refl n≢0
divmod-thm {m = m}{n = suc n} n≢0 refl refl = m≡m%n+[m/n]*n m n

s<z⇒⊥ : ∀ {x} → x < 0 → ⊥
s<z⇒⊥ {x} = λ ()

sx≮1 : ∀ {x} → suc x < 1 → ⊥
sx≮1 {x} (s≤s ())

ssx≮2 : ∀ {x} → suc (suc x) < 2 → ⊥
ssx≮2 (s≤s (s≤s ()))

a<b⇒a-m<b-m : ∀ {a b  m} → a < b → a ≥ m → a ∸ m < b ∸ m
a<b⇒a-m<b-m {zero} {suc b} {zero} a<b a≥m = a<b
a<b⇒a-m<b-m {suc a} {suc b} {zero} a<b a≥m = a<b
a<b⇒a-m<b-m {suc a} {suc b} {suc m} a<b a≥m = a<b⇒a-m<b-m (≤-pred a<b) (≤-pred a≥m)

a<b⇒a≡c⇒c<b : ∀ {a b c} → a < b → a ≡ c → c < b
a<b⇒a≡c⇒c<b a<b refl = a<b

b≡0+c≡a⇒b+c≡a : ∀ {a b c} → b ≡ 0 → c ≡ a → b + c ≡ a
b≡0+c≡a⇒b+c≡a refl refl = refl

m≡m+x⇒0≡x : ∀ {m x} → m ≡ m + x → 0 ≡ x
m≡m+x⇒0≡x {m}{x} m≡m+x = +-cancelˡ-≡ m (trans (+-identityʳ m) m≡m+x)

a*b≡0⇒b≢0⇒a≡0 : ∀ {a b} → a * b ≡ 0 → b ≢ 0 → a ≡ 0
a*b≡0⇒b≢0⇒a≡0 {a}{b} a*b≡0 b≢0 with (m*n≡0⇒m≡0∨n≡0 a a*b≡0)
a*b≡0⇒b≢0⇒a≡0 {a} {b} a*b≡0 b≢0 | inj₁ x = x
a*b≡0⇒b≢0⇒a≡0 {a} {b} a*b≡0 b≢0 | inj₂ y = contradiction y b≢0

-- m≤n⇒m%n≡m
m<n⇒m/n≡0 : ∀ {m n} → (m<n : m < n) → ∀ {≢0} → (m / n) {≢0} ≡ 0
m<n⇒m/n≡0 {m} {n@(suc n-1)} m<n = let
                      m%n≡m = m≤n⇒m%n≡m (≤-pred m<n)
                      m≡m%n+m/n*n = (m≡m%n+[m/n]*n m n-1)
                      m≡m+m/n*n = trans m≡m%n+m/n*n (cong₂ _+_ m%n≡m refl)
                      m/n*n≡0 = sym (m≡m+x⇒0≡x m≡m+m/n*n)
                      m/n≡0 = a*b≡0⇒b≢0⇒a≡0 {a = m / n} {b = n} m/n*n≡0 (m<n⇒n≢0 m<n) 
                    in m/n≡0 

a<c⇒c|b⇒[a+b]%c≡a : ∀ {a b c} → a < c → (c ∣ b) → ∀ {≢0} → ((a + b) % c) {≢0} ≡ a
a<c⇒c|b⇒[a+b]%c≡a {a} {b} {c@(suc c-1)} a<c c|b = trans (%-remove-+ʳ a c|b) (m≤n⇒m%n≡m (≤-pred a<c))
