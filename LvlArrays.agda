{-# OPTIONS --rewriting --inversion-max-depth=100  #-}
open import Data.Nat
open import Data.Nat.DivMod 
open import Data.Nat.Properties

open import Data.Product
open import Data.Sum
open import Function using (_$_ ; _∘_ ; case_of_)
open import Data.Vec hiding (sum)
open import Data.Vec.Properties
open import Data.Unit hiding (_≟_; _≤_)

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary

open import Data.Empty
open import Data.Nat.Divisibility

open import Data.Nat.Solver
open +-*-Solver

open import BFin
open import NatFacts

{-# BUILTIN REWRITE _≡_ #-}

open BFin.BFin

{-# REWRITE btabulate∘blookup #-}
{-# REWRITE blookup∘btabulate #-}

-- A type for the linearised index.
infixr 5 _∷_
data FlatIx : (d : ℕ) → (s : Vec ℕ d) → Set where
  []   : FlatIx 0 []
  _∷_ : ∀ {d s x} → BFin x → (ix : FlatIx d s) → FlatIx (suc d) (x ∷ s)

-- Operations and properties on FlatIx
ix-lookup : ∀ {d s} → FlatIx d s → (i : BFin d) → BFin (blookup s i)
ix-lookup [] ()
ix-lookup (x ∷ ix) (zero bounded _) = x
ix-lookup (x ∷ ix) (suc i bounded _) = ix-lookup ix (i bounded _)

ix-tabulate : ∀ {d s} → ((i : BFin d) → BFin (blookup s i)) → FlatIx d s
ix-tabulate {s = []} f = []
ix-tabulate {d = suc d}{s = x ∷ s} f = f (0 bounded s≤s z≤n) ∷ ix-tabulate (f ∘ bsuc)

ix-lookup∘ix-tabulate : ∀ {d s}{f : (i : BFin d) → BFin (blookup s i)}{i}
                      → ix-lookup {s = s} (ix-tabulate f) i ≡ f i
ix-lookup∘ix-tabulate {s = x ∷ s} {i = 0 bounded _} = refl
ix-lookup∘ix-tabulate {s = x ∷ s} {i = suc i bounded _} = ix-lookup∘ix-tabulate {s = s} 

flat-ix-zero : ∀ (x : FlatIx zero []) → x ≡ []
flat-ix-zero [] = refl

ix-tabulate∘ix-lookup : ∀ {n}{s : Vec _ n}{iv}
                      → ix-tabulate {s = s} (ix-lookup iv) ≡ iv
ix-tabulate∘ix-lookup {zero} {[]}{iv} rewrite (flat-ix-zero iv) = refl
ix-tabulate∘ix-lookup {suc n}{x ∷ s}{i ∷ iv} = cong₂ _∷_ refl ix-tabulate∘ix-lookup 

-- Note that keeping those as rewrites rules simplify a number of proofs.
{-# REWRITE ix-lookup∘ix-tabulate #-}
{-# REWRITE ix-tabulate∘ix-lookup #-}

bfin-lookup : ∀ {n}{s}{x y : FlatIx n s}{iv}
            → x ≡ y
            → BFin.v (ix-lookup x iv) ≡ BFin.v (ix-lookup y iv)
bfin-lookup refl = refl


flat-prod : ∀ {n} → Vec ℕ n → ℕ
flat-prod = foldr _ _*_ 1

-- The type of shape of arrays of level `l`
ShType : (l : ℕ) → Set

-- The type of indices into arrays of level `l`
IxType : (l : ℕ) → ShType l → Set

-- Representaiton for an array of level `l`.
-- Note that we don't talk about the properties of
-- the representation, and when it is adequate.  So,
-- this can be done later.
ReprAr : ∀ l (X : Set) → Set

-- Representation of indices into arrays of level `l`
record Ix (l : ℕ) (s : ShType l) : Set where
  -- In this particular case, additionally to the index
  -- representation we carry the type argument carries the
  -- shape of the index space where this index is coming from.
  -- We need this to distinguish the indices from diffrent index
  -- spaces that have the same representation.
  constructor ix
  field
    flat-ix : IxType l s

-- The main type for leveled arrays.
data Ar {a} (l : ℕ) (X : Set a) (s : ShType l) : Set a where
  imap : (Ix l s → X) → Ar l X s


prod : ∀ {l} → ShType l → ℕ

-- Note here that representation types of Shape and the
-- Array itself don't have to match.  It is convenient
-- when they do, but for more complex array types this
-- is not the case.
ShType zero    = ⊤
ShType (suc l) = ReprAr l ℕ
                 --Σ (ReprSh l) λ s → Vec ℕ (prod s) 

ReprAr l X = Σ (ShType l) λ s → Vec X (prod {l = l} s)

-- In principle, we can say that this type on its own is
-- a type of array indices.  In this case however, we won't
-- be able to distinguish between indices into different
-- shapes.  E.g. index ⟨2⟩ can index arrays Ar 1 X 5
-- Ar 2 X [5], etc.  This can be both a bug and a feature.
IxType zero tt = ⊤
IxType (suc l) (s , vec) = FlatIx (prod s) vec


prod {zero}  sh = 1
prod {suc l} (s , vec) = flat-prod vec

unimap : ∀ {a}{X : Set a}{l s} → Ar l X s → _
unimap (imap a) = a


-- Offset to linearised index.
o-i : ∀ {n} → (sh : Vec ℕ n)
    → FlatIx 1 (flat-prod sh ∷ [])
    → FlatIx n sh
o-i [] iv = []
o-i (s ∷ sh) iv with flat-prod (s ∷ sh) ≟ 0
o-i (s ∷ sh) (x ∷ []) | yes p rewrite p = ¬BFin0 x
o-i (s ∷ sh) (off ∷ []) | no ¬p = let
                                         o bounded o<s*sh = off
                                         tl = flat-prod sh
                                         tl≢0 = fromWitnessFalse (a*b≢0⇒b≢0 {a = s} ¬p)
                                         x = (o / tl) {≢0 = tl≢0}
                                    in (x bounded /-mono-x o<s*sh tl≢0)
                                       ∷ o-i sh (((o % tl) {≢0 = tl≢0} bounded n≢0⇒m%n<n (a*b≢0⇒b≢0 {a = s} ¬p)) ∷ [])

-- Some instance magic, move it some place that is more appropriate.
instance
  auto≥ : ∀ {m n : ℕ} → {{_ : True (m ≥? n)}} → m ≥ n
  auto≥ {m} {n} {{c}} = toWitness c


module test-oi where
  test-oi₁ : o-i (10 ∷ 5 ∷ []) (40 bounded auto≥ ∷ []) ≡ (8 bounded _) ∷ (0 bounded _) ∷ []
  test-oi₁ = refl

-- Offset to index, but on the Ix type.
off→idx : ∀ {l}
        → (sh : ShType l)
        → BFin (prod sh)
        → Ix l sh
off→idx {zero} tt i = ix tt
off→idx {suc l} (sh , v) i = ix (o-i v (i ∷ []))

-- Convert array type into its representaion type.
repr : ∀ {X l s} → Ar l X s → ReprAr l X
repr {l = zero} {s} (imap x) = tt , x (ix tt) ∷ []
repr {l = suc l} {s} (imap x) = s , btabulate λ i → x (off→idx s i)

-- [x , y] < [a , b] ⇒ rowmaj [x , y] < a*b ⇒ x*b+y < a*b  
rm-thm : ∀ {a b} → (x : BFin a) → (b ≢ 0) → (y : BFin b) → (BFin (a * b)) -- Σ (BFin (a * b)) λ t → v t ≡ v y + v x * b
rm-thm {a} {zero}  x pf y = contradiction (refl {x = 0}) pf
rm-thm {zero} {suc b} () pf y 
rm-thm {suc a} {suc b} (x bounded x<a) pf (y bounded y<b) =
  ((y + x * suc b) bounded (+-mono-≤ (y<b) $ *-monoˡ-≤ (suc b) (≤-pred x<a))) -- , refl

v-rm-thm : ∀ {a b x y b≢0} → (BFin.v (rm-thm {a = a} {b = b} x b≢0 y)) ≡ (v y) + (v x) * b
v-rm-thm {suc a} {suc b} {x} {y} {≢0} = refl

Πs≡0⇒Fin0 : ∀ {n} → (s : Vec ℕ n)
          → (FlatIx n s) → (flat-prod s ≡ 0)
          → BFin 0
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 with  m*n≡0⇒m≡0∨n≡0 x Πxs≡0
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 | inj₁ x≡0 rewrite x≡0 = i
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 | inj₂ Πs≡0 = Πs≡0⇒Fin0 s iv Πs≡0


-- Linearised index to offset.
i-o : ∀ {n} → (s : Vec ℕ n)
    → (iv : FlatIx n s)
    → FlatIx 1 (flat-prod s ∷ [])
i-o [] iv = (0 bounded auto≥) ∷ iv
i-o (s ∷ sh) (i ∷ iv) with flat-prod (s ∷ sh) ≟ 0
i-o (s ∷ sh) (i ∷ iv) | yes p rewrite p = ¬BFin0 $ Πs≡0⇒Fin0 (s ∷ sh) (i ∷ iv) p
i-o (s ∷ sh) (i ∷ iv) | no ¬p = (rm-thm i (a*b≢0⇒b≢0 {a = s} ¬p) (ix-lookup (i-o sh iv) (0 bounded auto≥))) ∷ []


-- Full index to offset.
idx→off : ∀ {l} → (sh : ShType l) → Ix l sh → BFin (prod sh)
idx→off {zero} sh iv = 0 bounded auto≥
idx→off {suc l} (s , v) (ix flat-ix) = ix-lookup (i-o v flat-ix) (0 bounded auto≥)


BFin1≡0 : ∀ (i : BFin 1) → i ≡ (0 bounded auto≥)
BFin1≡0 (0 bounded _) = refl
BFin1≡0 (suc x bounded 1+x<1) = ⊥-elim-irr (sx≮1 1+x<1)


-- Index-to offset and offset-to-index are reverses of each other.
io-oi : ∀ {n}{x : Vec _ n}{i : BFin (flat-prod x)}
      → i-o x (o-i x (i ∷ [])) ≡ i ∷ []
io-oi {zero} {[]}{i} = cong₂ _∷_ (sym $ BFin1≡0 i) refl
io-oi {suc n} {x ∷ x₁}{i} with flat-prod (x ∷ x₁) ≟ 0
... | yes p = ⊥-elim $ ¬BFin0 (subst BFin p i)
... | no ¬p with flat-prod (x ∷ x₁) ≟ 0
io-oi {suc n} {x ∷ x₁} {i} | no ¬p | yes q = contradiction q ¬p
io-oi {suc n} {x ∷ x₁} {i} | no ¬p | no ¬q
     -- Now we just have to use the fact that i = i%x₁ + i/x₁*x₁
     -- Hopefully, this is easy enough.
   = cong (_∷ []) (bfin-cong (trans (v-rm-thm {a = x}
                                               {b = flat-prod x₁}
                                               {b≢0 = a*b≢0⇒b≢0 {a = x} ¬q})
                                     (sym $ divmod-thm {a = v (ix-lookup (i-o x₁ (o-i x₁ _)) (0 bounded _))}
                                                       (a*b≢0⇒b≢0 {a = x} ¬p)
                                                       -- this is where the recursive call to the theorem happens.
                                                       (trans (cong (λ x → v (ix-lookup x (0 bounded auto≥)))
                                                              (io-oi {x = x₁})) refl)
                                                       refl)))

shape-repr : ∀ {l X} → ReprAr l X → ShType l
shape-repr {zero} _ = tt
shape-repr {suc l} (s , v) = s

-- Convert from array representation to the array type.
unrepr : ∀ {l X} → (ra : ReprAr l X) → Ar l X (shape-repr ra)
unrepr {zero}  (_ , x ∷ []) = imap λ _ → x
unrepr {suc l} (s , v)       = imap λ iv → blookup v (idx→off _ iv)

-- The essence of the reshape operation.
reix : ∀ {l l₁ s s₁} → Ix l s → (prod s ≡ prod s₁) → Ix l₁ s₁
reix iv pf = let ox = idx→off _ iv in off→idx _ $ subst BFin pf ox

-- Reshape operation.
reshape : ∀ {a}{X : Set a}{l l₁ s s₁} → Ar l X s → prod s ≡ prod s₁ → Ar l₁ X s₁
reshape (imap a) pf = imap λ iv → a $ reix iv (sym pf)


sum : ∀ {l s} → Ar l ℕ s → ℕ
sum {l} a = let s , v = repr a in Data.Vec.sum v


-- The version of the avgpool that uses level-3 arrays, but without
-- the generalised nesting.
module explicit-avgpool where
  lem-mn : ∀ m n →  m * 2 * (n * 2 * 1) ≡ m * (n * 2 + (n * 2 + 0))
  lem-mn = solve 2 (λ m n → m :* con 2 :* (n :* con 2 :* con 1)
                         := m :* (n :* con 2 :+ (n :* con 2 :+ con 0))) refl


  avgpool-reshape : ∀ {m n}
                  → Ar 2 ℕ ((tt , 2 ∷ []) , m * 2 ∷ n * 2 ∷ [])
                  → Ar 3 ℕ (((tt , 2 ∷ []) , 2 ∷ 2 ∷ []) , m ∷ 2 ∷
                                                             n ∷ 2 ∷ [])
  avgpool-reshape {m} {n} a = reshape a (lem-mn m n)


  split-col : ∀ {m n n₁} → Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n + n₁ ∷ [])
                         → Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n ∷ [])
                         × Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n₁ ∷ [])
  split-col {m} {n} {n₁} (imap a) = (imap λ { (ix (i ∷ j ∷ [])) → a (ix (i ∷ binject j ∷ [])) }) ,    --inject+ _ j
                                   imap λ { (ix (i ∷ j ∷ [])) → a (ix (i ∷ braise j ∷ [])) } -- raise _ j

  merge-col : ∀ {m n n₁}
            → Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n ∷ [])
            → Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n₁ ∷ [])
            → Ar 2 ℕ ((tt , (2 ∷ [])) , m ∷ n + n₁ ∷ [])
  merge-col {m} {n} {n₁} (imap a) (imap b) = imap foo
    where
      foo : _
      foo (ix (i ∷ j ∷ [])) with (v j <? n)
      ... | yes p = a (ix (i ∷ (v j) bounded p ∷ []))
      ... | no ¬p = b (ix (i ∷ breduce j (≮⇒≥ ¬p) ∷ [])) -- reduce≥ j (≮⇒≥ ¬p)


  shape : ∀ {a}{X : Set a}{l s} → Ar l X s → ShType l
  shape {s = s} _ = s

  nest-col : ∀ {m n}
           → (a : Ar 3 ℕ (((tt , (2 ∷ [])) , (2 ∷ 2 ∷ [])) , (m ∷ 2 ∷ n ∷ 2 ∷ [])))
           → let so , si = split-col {n = 1} (unrepr $ shape a)
             in Ar 3 (Ar 3 ℕ (repr si)) (repr so)
  nest-col {m} {n} (imap a) = imap λ { (ix (i ∷ j ∷ [])) → imap λ { (ix (k ∷ l ∷ [])) → a (ix (i ∷ k ∷ j ∷ l ∷ []))}}


  avgpool : ∀ {m n}
          → Ar 2 ℕ ((tt , 2 ∷ []) , m * 2 ∷ n * 2 ∷ [])
          → Ar 2 ℕ ((tt , 2 ∷ []) , m ∷ n ∷ [])
  avgpool {m} {n} a = let
       a' = nest-col $ avgpool-reshape {m = m} {n = n} a
       r = imap λ iv → sum (unimap a' iv)
     in reshape r refl


-- RanedT means that we want to select an axis of the shape
-- across which we are going to "cut" the shape.
RankedT : ∀ {l : ℕ} → ShType l → Set
                -- Level-0 arrays can be arbitrarily nested:
                -- Ar 0 ℕ tt -> Ar 0 (Ar 0 ℕ tt) tt -> Ar 0 (Ar 0 (Ar 0 ...)) tt
                -- XXX maybe Fin 1 is better?
RankedT {0} _ = ⊤
                      -- Level-1 arrays can be nested in two ways:
                      -- [1,2,3] -> [[1,2,3]] or [[1],[2],[3]]
RankedT {1} (s , v) = BFin (1 + prod s)
                                      -- Finally, arrays of level 2+ can be nested by
                                      -- choosing an axis across which we "cut" and
                                      -- where do we cut.  This gives us arbitrary
                                      -- hypercube slicing.
RankedT {suc (suc l)} ((s , v) , _) = Σ (BFin (prod s)) λ i → BFin (1 + blookup v i)
                                      --Σ (Ix _ s) λ iv →
                                      --  Fin (1 + (lookup v $ idx→off s iv))


-- Update an element in the vector at the position given by BFin.
modvec : ∀ {a}{n}{A : Set a} → BFin n → A → Vec A n → Vec A n
modvec {n = suc n} (zero  bounded i<u) y (x ∷ xs) = y ∷ xs
modvec {n = suc n} (suc i bounded i<u) y (x ∷ xs) = x ∷ modvec (i bounded ≤-pred i<u) y xs


blookup∘modvec₁ : ∀ {a}{n}{A : Set a}
               → (i j : BFin n) → i ≡ j → (xs : _) → (y : A)
               → blookup (modvec i y xs) j ≡ y
blookup∘modvec₁ {n = suc n} (zero bounded v<u₁) .(0 bounded _) refl (_ ∷ _) y = refl
blookup∘modvec₁ {n = suc n} (suc v₁ bounded v<u₁) .(suc v₁ bounded _) refl (_ ∷ xs) y = blookup∘modvec₁ _ _ refl xs y 

bfin-proj≢ : ∀ {n}{x y : BFin n} → x ≢ y → v x ≢ v y
bfin-proj≢ {x = v₁ bounded v<u₁} {v₂ bounded v<u₂} x≢y refl = contradiction refl x≢y

bfin-suc-≢ : ∀ {n}{i j}.{i<n : _ < suc n}.{j<n : _ < suc n}
     → (suc i bounded i<n) ≢ (suc j bounded j<n)
     → (i bounded ≤-pred i<n) ≢ (j bounded ≤-pred j<n)
bfin-suc-≢ x≢y i≡j = contradiction (cong suc (bfin-projv i≡j)) (bfin-proj≢ x≢y)


bfin-≢ : ∀ {n}{x y}.{x<n : x < n}.{y<n : y < n}
       → x ≢ y → x bounded x<n ≢ y bounded y<n
bfin-≢ x≢y fx≡fy = contradiction (bfin-projv fx≡fy) x≢y

blookup∘modvec₂ : ∀ {a}{n}{A : Set a}
               → (i j : BFin n) → i ≢ j → (xs : _) → (y : A)
               → blookup (modvec i y xs) j ≡ blookup xs j
blookup∘modvec₂ {n = suc n} (zero bounded v<u₁) (zero bounded v<u₂) i≢j xs y = contradiction refl i≢j
blookup∘modvec₂ {n = suc n} (zero bounded v<u₁) (suc v₂ bounded v<u₂) i≢j (x ∷ xs) y = refl
blookup∘modvec₂ {n = suc n} (suc v₁ bounded v<u₁) (zero bounded v<u₂) i≢j (x ∷ xs) y = refl
blookup∘modvec₂ {n = suc n} (suc i bounded v<u₁) (suc j bounded v<u₂) i≢j (x ∷ xs) y
  = blookup∘modvec₂ _ _ (bfin-suc-≢ {i<n = v<u₁} i≢j) xs y

-- These two functions construct the left shape of ranked cut
left-to-full-hlp : ∀ {l} {ss : ShType l} {vs : Vec ℕ (prod ss)}
                      {iv}{n : BFin (1 + (blookup vs iv))}
                 → Ix _ (ss , modvec iv (BFin.v n) vs)
                 → (i : BFin (prod ss)) → BFin (blookup vs i)
left-to-full-hlp {vs = vs}{iv = i bounded i<u} {n = nn bounded nn<u}
                 (ix il) (j bounded j<u) with i ≟ j
                 -- if this is the shape element index that we made a cut
                 -- over, it can be used as is as the upper bounds agree, i.e.
                 -- we have x < nn ∧ nn < (1 + vs[i]), but we need to show that
                 -- x < vs[i]
... | yes refl = let
                   il[j] = (ix-lookup il (j bounded i<u))
                   x = subst BFin (blookup∘modvec₁ _ _ refl vs _) il[j]
                 in binject≤ x (≤-pred nn<u)
... | no ¬p = -- if is is not the index we made a cut over, then the shape
              -- elements stayed the same
              let
                il[j] = (ix-lookup il (j bounded j<u))
                x = subst BFin (blookup∘modvec₂ _ _ (bfin-≢ ¬p) vs _) il[j]
              in x

left-to-full : ∀ {l}{ss : ShType l}{vs iv}{n : BFin (1 + (blookup vs iv))}
             → Ix _ (ss , modvec iv (BFin.v n) vs) → Ix _ (ss , vs)
left-to-full {n = n} ii = ix $ ix-tabulate (left-to-full-hlp {n = n} ii)


ux<m-n⇒vn+vx<m : ∀ {m n}{x : BFin (m ∸ n)} → n + BFin.v x < m
ux<m-n⇒vn+vx<m {m}{n}{x = x bounded x<m-n} with m ∸ n ≟ 0
... | yes p = ⊥-elim-irr (s<z⇒⊥ (subst (x <_) p x<m-n))
... | no ¬p = subst (n + x <_) (m+[n∸m]≡n {m = n} (<⇒≤ $ m∸n≢0⇒n<m ¬p)) (+-monoʳ-< n (recompute (_ <? _) x<m-n))


-- These two functions construct the right shape of ranked cut
right-to-full-hlp : ∀ {l} {ss : ShType l} {vs : Vec ℕ (prod ss)}
                     {iv}{n : BFin (1 + (blookup vs iv))}
                 → Ix _ (ss , modvec iv (blookup vs iv ∸ BFin.v n) vs)
                 → (i : BFin (prod ss)) → BFin (blookup vs i)
right-to-full-hlp {vs = vs}{iv = i bounded i<u}{n} (ix ir) (j bounded j<u) with i ≟ j
... | yes refl = let
                   ir[j] = ix-lookup ir (j bounded i<u)
                   x = subst BFin (blookup∘modvec₁ _ _ refl vs _) ir[j]
                   -- we have: x < (vs[i] - n) ∧ n < (1 + vs[i]), we pick
                   -- the n+x element from the original shape and we need to
                   -- show that n+x < vs[i]
                 in (BFin.v n + BFin.v x) bounded ux<m-n⇒vn+vx<m {n = BFin.v n} {x = x}
... | no ¬p = -- if i is not the index we made a cut over, the shape
              -- elements are exactly the same
              let
                 ir[j] = (ix-lookup ir (j bounded j<u))
                 x = subst BFin (blookup∘modvec₂ _ _ (bfin-≢ ¬p) vs _) ir[j]
              in x



right-to-full : ∀ {l}{ss : ShType l}{vs iv}{n : BFin (1 + (blookup vs iv))}
              → Ix _ (ss , modvec iv (blookup vs iv ∸ BFin.v n) vs) → Ix _ (ss , vs)
right-to-full {n = n} ii = ix $ ix-tabulate (right-to-full-hlp {n = n} ii)


ix-tabulate-ext-funs : ∀ {n s}{f g : (j : BFin n) → BFin (blookup s j)}
                     → (∀ j → f j ≡ g j) → ix-tabulate {s = s} f ≡ ix-tabulate g
ix-tabulate-ext-funs {zero} {[]} fpf = refl
ix-tabulate-ext-funs {suc n} {x ∷ s} fpf = cong₂ _∷_ (fpf (0 bounded _)) (ix-tabulate-ext-funs $ fpf ∘ bsuc)



thm-io-ixtab : ∀ {n}{x : Vec ℕ n}{f i}
             → (∀ j → f j ≡ ix-lookup (o-i x (i ∷ [])) j)
             → i-o x (ix-tabulate f) ≡ i ∷ []
thm-io-ixtab {n}{x}{i = i} fpf rewrite (ix-tabulate-ext-funs {s = x} fpf)
                                     | (io-oi {x = x} {i = i})
                                     = refl

ix-lookup-io-thm1 : ∀ {n}{x : Vec ℕ n}{y}{i} → i-o x y ≡ i ∷ [] → ix-lookup (i-o x y) (0 bounded auto≥) ≡ i
ix-lookup-io-thm1 pf rewrite pf = refl



ranked-cut : ∀ {l : ℕ} → (s : ShType l) → RankedT s → ShType l × ShType l
ranked-cut {zero} tt tt = tt , tt
ranked-cut {suc zero} (tt , x ∷ []) (0 bounded i<u) = (tt , x ∷ []) , (tt , 1 ∷ [])
ranked-cut {suc zero} (tt , x ∷ []) (1 bounded i<u) = (tt , 1 ∷ []) , (tt , x ∷ [])
ranked-cut {suc zero} (tt , x ∷ []) (suc (suc v₁) bounded i<u) = ⊥-elim-irr (ssx≮2 i<u)
ranked-cut {suc (suc l)} s@((ss , vs) , v) ri@(iv , n) = let
     shsh-l = modvec iv (BFin.v n) vs
     shsh-r = modvec iv (blookup vs iv ∸ BFin.v n) vs
   in   ((ss , shsh-l)
         , btabulate λ i → blookup v $ idx→off (ss , vs) $ left-to-full {n = n} $ off→idx (ss , shsh-l) i)
      , ((ss , shsh-r)
         , btabulate λ i → blookup v $ idx→off (ss , vs) $ right-to-full {n = n} $ off→idx (ss , shsh-r) i)


lkup-left : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
             → let
                 (sl , _) , s₂ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
             (p : (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → Σ _ (λ t → t ≡ (o-i sv (i ∷ [])))
             → (j : BFin (prod ss))
             → BFin (blookup (modvec iv (BFin.v n) sv) j)
lkup-left {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n} p (ii , refl) i@(vi bounded i<u) with BFin.v iv ≟ BFin.v i
... | yes refl = let
                  tv bounded tv<sv[j] = (ix-lookup ii i)
                  q = breduce< (tv bounded tv<sv[j]) p
               in subst BFin (sym $ blookup∘modvec₁ iv iv refl _ _) q

... | no ¬p = subst BFin (sym $ blookup∘modvec₂ _ _ (bfin-≢ {x<n = iv<u} {y<n = i<u} $ ¬p) sv _) (ix-lookup ii i)


lkup-right : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
             → let
                 _ , _ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
             (¬p : ¬ (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → Σ _ (λ t → t ≡ (o-i sv (i ∷ [])))
             → (j : BFin (prod ss))
             → BFin (blookup (modvec iv (blookup sv iv ∸ BFin.v n) sv) j)
lkup-right {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n} ¬p (ii , p') i@(vi bounded i<u) with BFin.v iv ≟ BFin.v i
... | yes refl =
                let
                  t bounded t<sv[i] = (ix-lookup ii i)
                  q = (t ∸ BFin.v n) bounded a<b⇒a-m<b-m {m = BFin.v n} t<sv[i]
                                                         (≮⇒≥ λ x → ¬p (subst (_< BFin.v n) (cong (λ y → BFin.v (ix-lookup y iv)) p' ) x))
                in subst BFin (sym $ blookup∘modvec₁ iv i refl sv (blookup sv iv ∸ BFin.v n)) q
... | no ¬pp = subst BFin (sym $ blookup∘modvec₂ _ _ (bfin-≢ {x<n = iv<u} {y<n = i<u} $ ¬pp) sv _) (ix-lookup ii i)


lkup-left-thm-1 : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
          → let
                 (sl , _) , s₂ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
                 (ni bounded ni<n) = n
                 (s[i] bounded s[i]<ps) = ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv
            in
            (p : s[i] < ni)
          → (j : _)
          → (iv≡jv : BFin.v iv ≡ BFin.v j)
          → BFin.v (lkup-left {s = s}{ri = ri} p (o-i sv (i ∷ []) , refl) j)
            ≡ BFin.v (ix-lookup (o-i sv (i ∷ [])) j)
lkup-left-thm-1 {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n}{i} p j refl with BFin.v iv ≟ BFin.v j
... | yes refl  =  trans (bfin-subst {i = (breduce< (ix-lookup (o-i sv (i ∷ [])) (viv bounded _)) _)}
                                     {m≡n = (sym (blookup∘modvec₁ (viv bounded _) (viv bounded _) refl sv (BFin.v n)))})
                         (breduce<-thm {n = BFin.v n}
                                       {i = ix-lookup (o-i sv (i ∷ [])) (viv bounded _)}
                                       {vi<n = p})

... | no ¬p = contradiction refl ¬p



lkup-left-thm-2 : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
          → let
                 (sl , _) , s₂ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
                 viv bounded iv<u = iv
            in
            (p : (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
          → (j : _)
          → (iv≢j : BFin.v iv ≢ BFin.v j)
          → let _ bounded j<u = j in
            BFin.v (lkup-left {s = s}{ri = ri} p (o-i sv (i ∷ []) , refl) j)
            ≡ (BFin.v $ subst BFin (sym $ blookup∘modvec₂ _ _ (bfin-≢ {x<n = iv<u} {y<n = j<u} $ iv≢j) sv (BFin.v n))
                                   (ix-lookup (o-i sv (i ∷ [])) j))
lkup-left-thm-2 {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n}{i} p j iv≢j with BFin.v iv ≟ BFin.v j
... | yes pp = contradiction pp iv≢j
... | no ¬pp = trans (bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) j)}
                                 {m≡n = (sym (blookup∘modvec₂ iv j (bfin-≢ ¬pp) sv (BFin.v n)))})
                     (sym $ bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) j)}
                                       {m≡n = (sym (blookup∘modvec₂ iv j
                                                      (λ fx≡fy → ⊥-elim (iv≢j (bfin-projv fx≡fy))) sv (BFin.v n)))})

lkup-right-thm1 : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
             → let
                 _ , _ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
             (¬p : ¬ (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → (j : BFin (prod ss))
             → (iv≡j : BFin.v iv ≡ BFin.v j)
             → BFin.v (lkup-right {s = s}{ri = ri} ¬p (o-i sv (i ∷ []) , refl) j)
               ≡ BFin.v (ix-lookup (o-i sv (i ∷ [])) iv) ∸ BFin.v n
lkup-right-thm1 {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n}{i} ¬p j refl with BFin.v iv ≟ BFin.v j
... | yes refl = bfin-subst {m≡n = sym $ blookup∘modvec₁ iv iv refl sv (blookup sv iv ∸ BFin.v n )}
... | no ¬pp   = contradiction refl ¬pp

lkup-right-thm2 : ∀ {l}{s : ShType (suc (suc l))}{ri}{i}
             → let
                 _ , _ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
             (¬p : ¬ (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → (j : BFin (prod ss))
             → (iv≢j : BFin.v iv ≢ BFin.v j)
             → BFin.v (lkup-right {s = s}{ri = ri} ¬p (o-i sv (i ∷ []) , refl) j)
               ≡ let
                   _ bounded iv<u = iv
                   _ bounded j<u = j
                 in BFin.v $ subst BFin (sym $ blookup∘modvec₂ _ _ (bfin-≢ {x<n = iv<u} {y<n = j<u} $ iv≢j)
                                                                   sv (blookup sv iv ∸ BFin.v n)) (ix-lookup (o-i sv (i ∷ [])) j)
lkup-right-thm2 {s = ((ss , sv) , v)} {ri = iv@(viv bounded iv<u) , n}{i} ¬p j iv≢j with BFin.v iv ≟ BFin.v j
... | yes pp = contradiction pp iv≢j
... | no ¬pp = trans (bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) j)}
                                 {m≡n = (sym (blookup∘modvec₂ iv j (bfin-≢ ¬pp) sv (blookup sv (viv bounded _) ∸ BFin.v n)))})
                     (sym $ bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) j)}
                                       {m≡n = (sym (blookup∘modvec₂ iv j
                                                      (λ fx≡fy → ⊥-elim (iv≢j (bfin-projv fx≡fy))) sv (blookup sv (viv bounded _) ∸ BFin.v n)))})

-- These two functions map indeces of the cut-shape into the indices of the original shape.
full-to-left : ∀ {l}{s : ShType (suc (suc l))}{ri}
             → let
                 (sl , _) , s₂ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
               (i : BFin (prod (proj₁ s)))
             → (p : (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → BFin (prod sl)
full-to-left {l}{s@((ss , sv) , v)} {ri@(iv@(viv bounded iv<u) , n)} i p = let
            ((lss , lsv) , lv) , _ = ranked-cut s ri
            ix ii = off→idx (ss , sv) i
            p' : ii ≡ (o-i sv (i ∷ []))
            p' = refl
            ii' = ix-tabulate (lkup-left {s = s} {ri = ri} p (ii , p'))
          in idx→off (lss , lsv) (ix ii')


full-to-right : ∀ {l}{s : ShType (suc (suc l))}{ri}
             → let
                 _ , (sr , _) = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
               (i : BFin (prod (proj₁ s)))
             → (¬p : ¬ (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → BFin (prod sr)
full-to-right {l}{s@((ss , sv) , v)} {ri@(iv@(viv bounded iv<u) , n)} i ¬p = let
            _ , ((rss , rsv) , rv) = ranked-cut s ri
            ix ii = off→idx (ss , sv) i
            p' : ii ≡ (o-i sv (i ∷ []))
            p' = refl
            ii' = ix-tabulate (lkup-right {s = s} {ri = ri} ¬p (ii , p'))
          in idx→off (rss , rsv) (ix ii')



blookup-1 : ∀ {a}{X : Set a}{x : X}{i} → blookup (x ∷ []) i ≡ x
blookup-1 {i = zero bounded i<u} = refl
blookup-1 {i = suc i bounded i<u} = ⊥-elim-irr (sx≮1 i<u)

ixl-io<sh : ∀ {n}{s : Vec _ n}{i iv}
          → BFin.v (ix-lookup (i-o s iv) i) < flat-prod s
ixl-io<sh {n}{s}{i}{iv} =
  let
    ixl = (ix-lookup (i-o s iv) i)
    ixl<u = bfin-to-< {x = ixl}
  in subst₂ _<_ refl (blookup-1 {i = i}) ixl<u


ixl-mods : ∀ {n}{s}{sh : Vec _ n}{i : BFin s}{iv : FlatIx _ sh}
         → (¬p : flat-prod (s ∷ sh) ≢ 0)
         → (v (rm-thm i (a*b≢0⇒b≢0 {a = s} ¬p) (ix-lookup (i-o sh iv) (0 bounded auto≥))) % flat-prod sh)
           {≢0 = fromWitnessFalse $ a*b≢0⇒b≢0 {a = s} ¬p}
           ≡ v (ix-lookup (i-o sh iv) (0 bounded auto≥))
ixl-mods {n}{s}{sh}{i}{iv} ¬p = trans (cong (_% flat-prod sh)
                                       (v-rm-thm {x = i}
                                                 {y = (ix-lookup (i-o sh iv) (0 bounded _))}
                                                 {b≢0 = a*b≢0⇒b≢0 {a = s} ¬p}))
                                 (a<c⇒c|b⇒[a+b]%c≡a (ixl-io<sh {i = (0 bounded _)}{iv = iv})
                                                     (n∣m*n (v i) {n = flat-prod sh})
                                                     {≢0 = fromWitnessFalse $ a*b≢0⇒b≢0 {a = s} ¬p})

ixl-oi-io : ∀ {n}{sv : Vec _ n}{i} → o-i sv (ix-lookup (i-o sv i) (0 bounded auto≥) ∷ []) ≡ i
ixl-oi-io {zero} {[]} {[]} = refl
ixl-oi-io {suc n} {s ∷ sh} {i ∷ iv} with flat-prod (s ∷ sh) ≟ 0
... | yes p = ¬BFin0 $ Πs≡0⇒Fin0 (s ∷ sh) (i ∷ iv) p
... | no ¬p = cong₂ _∷_
                   (bfin-cong (trans (cong (λ x → (x / flat-prod sh){≢0 = fromWitnessFalse $ a*b≢0⇒b≢0 {a = s} ¬p})
                                     (v-rm-thm {x = i}
                                               {y = (ix-lookup (i-o sh iv) (0 bounded _))}
                                               {b≢0 = a*b≢0⇒b≢0 {a = s} ¬p}))
                                     -- XXX this can be written in a nicer way.
                                     (trans (+-distrib-/-∣ʳ {m = v (ix-lookup (i-o sh iv) (0 bounded _))}
                                                            _
                                                            (n∣m*n (v i) {n = flat-prod sh}))
                                            (b≡0+c≡a⇒b+c≡a (m<n⇒m/n≡0 (ixl-io<sh {i = (0 bounded _)}{iv = iv}))
                                                           (m*n/n≡m (v i)
                                                           (flat-prod sh)))   )))
                   (trans (cong (λ x → o-i sh (x ∷ [])) $ bfin-cong $ ixl-mods {s = s}{sh = sh}{i = i}{iv = iv} ¬p)
                          ixl-oi-io)

lf∘fl : ∀ {l}{s : ShType (suc (suc l))}{ri}
             → let
                 (sl , _) , s₂ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
               (i : BFin (prod (proj₁ s)))
             → (p : (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → (j : BFin (prod ss))
             → (left-to-full-hlp {ss = ss} {n = n}
                (ix
                 (o-i (modvec iv (BFin.v n) sv)
                  (ix-lookup
                   (i-o (modvec iv (BFin.v n) sv)
                    (ix-tabulate (lkup-left {s = s} {ri = ri} p (o-i sv (i ∷ []) , refl))))
                   (0 bounded auto≥)
                   ∷ [])))) j ≡ ix-lookup (o-i sv (i ∷ [])) j
lf∘fl {s = s@((ss , sv) , v)} {ri@(iv@(viv bounded iv<u) , (nn bounded n<u))} i p (j bounded j<u) with viv ≟ j
... | yes refl = binject≤-thm
                   {i = (subst BFin (blookup∘modvec₁ iv iv refl sv nn)
                                    (ix-lookup
                                     (o-i (modvec iv nn sv)
                                      (ix-lookup
                                       (i-o (modvec iv nn sv)
                                        (ix-tabulate (lkup-left {s = s} p (o-i sv (i ∷ []) , refl))))
                                       (0 bounded auto≥)
                                       ∷ []))
                                     iv))}
                   {m≤n = ≤-pred n<u}
                   (trans (bfin-subst {m≡n = (blookup∘modvec₁ iv iv refl sv nn) })
                          let
                            oiio = ixl-oi-io {sv = (modvec iv nn sv)}
                                            {i = (ix-tabulate (lkup-left {s = s}{ri = ri} p
                                                                 (o-i sv (i ∷ []) , refl)))}
                            oiio≡foo = cong (λ x → BFin.v (ix-lookup x iv)) oiio
                          in trans oiio≡foo (lkup-left-thm-1 {s = s} {ri = ri} p iv refl))
... | no ¬pp = bfin-cong (trans (bfin-subst {i = _}{m≡n = (blookup∘modvec₂ iv (j bounded _) (bfin-≢ ¬pp) sv nn)})
                                let
                                  oiio = ixl-oi-io {sv = (modvec iv nn sv)}
                                                  {i = (ix-tabulate (lkup-left {s = s}{ri = ri} p
                                                                    (o-i sv (i ∷ []) , refl)))}
                                  oiio≡foo = cong (λ x → BFin.v (ix-lookup x (j bounded j<u))) oiio
                                in trans oiio≡foo
                                         (trans (lkup-left-thm-2 {s = s} {ri = ri} p (j bounded j<u) ¬pp)
                                                (bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) (j bounded _))}
                                                            {m≡n = (sym $
                                                            blookup∘modvec₂ (viv bounded _) (j bounded _) (bfin-≢ $ ¬pp) sv nn)}) ))



rf∘fr : ∀ {l}{s : ShType (suc (suc l))}{ri}
             → let
                 _ , _ = ranked-cut s ri
                 ((ss , sv) , v) = s
                 (iv , n) = ri
               in
               (i : BFin (prod (proj₁ s)))
             → (¬p : ¬ (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (proj₁ s) i) iv) < BFin.v n)
             → (j : BFin (prod ss))
             → (right-to-full-hlp {ss = ss} {n = n}
                                  (ix
                                   (o-i
                                    (modvec iv (blookup sv iv ∸ BFin.v n) sv)
                                    (ix-lookup
                                     (i-o
                                      (modvec iv (blookup sv iv ∸ BFin.v n) sv)
                                      (ix-tabulate (lkup-right {s = s} {ri = ri} ¬p (o-i sv (i ∷ []) , refl))))
                                     (0 bounded auto≥)
                                     ∷ [])))) j ≡ ix-lookup (o-i sv (i ∷ [])) j
rf∘fr {s = s@((ss , sv) , v)} {ri@(iv@(viv bounded iv<u) , (nn bounded n<u))} i ¬p (j bounded j<u) with viv ≟ j
... | yes refl = bfin-cong (trans (cong (nn +_)
                                        (trans (bfin-subst {m≡n = (blookup∘modvec₁ iv iv refl sv (blookup sv iv ∸ nn )) })
                                               let
                                                 oiio = ixl-oi-io {sv = (modvec iv (blookup sv iv ∸ nn) sv)}
                                                                 {i = (ix-tabulate (lkup-right {s = s}{ri = ri} ¬p
                                                                                      (o-i sv (i ∷ []) , refl)))}
                                                 oiio≡foo = cong (λ x → BFin.v (ix-lookup x iv)) oiio
                                               in trans oiio≡foo
                                                        (lkup-right-thm1 {s = s} {ri = ri} ¬p (j bounded j<u) refl)))
                                  (m+[n∸m]≡n {m = nn} (≮⇒≥ ¬p)))

... | no ¬pp = bfin-cong (trans
                           (bfin-subst {i = _}{m≡n = (blookup∘modvec₂ iv (j bounded _) (bfin-≢ ¬pp) sv (blookup sv (viv bounded _) ∸ nn))})
                           let
                             oiio = ixl-oi-io {sv = modvec iv (blookup sv iv ∸ nn) sv}
                                             {i = (ix-tabulate (lkup-right {s = s}{ri = ri} ¬p
                                                               (o-i sv (i ∷ []) , refl)))}
                             oiio≡foo = cong (λ x → BFin.v (ix-lookup x (j bounded j<u))) oiio
                           in trans oiio≡foo
                                    (trans (lkup-right-thm2 {s = s} {ri = ri} ¬p (j bounded j<u) ¬pp)
                                           (bfin-subst {i = (ix-lookup (o-i sv (i ∷ [])) (j bounded _))}
                                                       {m≡n = sym $ blookup∘modvec₂ (viv bounded _) (j bounded _)
                                                                                    (bfin-≢ $ ¬pp) sv (blookup sv (viv bounded _) ∸ nn)    })))


_ri++_ : ∀ {l}{s : ShType l}{ri} → let s₁ , s₂ = ranked-cut s ri in Ix _ s₁ → Ix _ s₂ → Ix _ s
_ri++_ {zero} {s} {ri} il ir = ix tt
_ri++_ {suc zero} {tt , x ∷ []} {0 bounded _} il ir = il
_ri++_ {suc zero} {tt , x ∷ []} {1 bounded _} il ir = ir
_ri++_ {suc zero} {tt , x ∷ []} {suc (suc i) bounded i<u} il ir = ⊥-elim-irr (ssx≮2 i<u)
_ri++_ {suc (suc l)} {s@((ss , sv) , v)} {ri@(iv@(viv bounded iv<u) , n)} (ix il) (ix ir) = ix $ ix-tabulate merge-ixs
  where
    merge-ixs : _
    merge-ixs i with (BFin.v $ ix-lookup (Ix.flat-ix $ off→idx (ss , sv) i) iv) <? BFin.v n
    ... | yes p = let
                    x = ix-lookup il (full-to-left {s = s} {ri = ri} i p)
                  in subst BFin (cong (blookup v)
                                      (ix-lookup-io-thm1
                                         {n = prod ss}
                                         {x = sv}
                                         (thm-io-ixtab {n = prod ss} {x = sv}
                                                       {f = left-to-full-hlp {ss = ss} {n = n}
                                                            (ix
                                                             (o-i (modvec iv (BFin.v n) sv)
                                                              (ix-lookup
                                                               (i-o (modvec iv (BFin.v n) sv)
                                                                (ix-tabulate (lkup-left {s = s}{ri = ri} p (o-i sv (i ∷ []) , refl))))
                                                               (0 bounded _) ∷ [])))}
                                                       {i = i}
                                                       (lf∘fl {s = s} {ri = ri} i p))))
                                 x


    ... | no ¬p = let
                    x = ix-lookup ir (full-to-right {s = s} {ri = ri} i ¬p)
                  in subst BFin (cong (blookup v)
                                      (ix-lookup-io-thm1
                                         {n = prod ss}
                                         {x = sv}
                                         (thm-io-ixtab
                                            {n = prod ss}
                                            {x = sv}
                                            {f = right-to-full-hlp {ss = ss} {n = n}
                                                                   (ix
                                                                    (o-i
                                                                     (modvec (viv bounded _) (blookup sv (viv bounded _) ∸ BFin.v n) sv)
                                                                     (ix-lookup
                                                                      (i-o
                                                                       (modvec (viv bounded _) (blookup sv (viv bounded _) ∸ BFin.v n) sv)
                                                                       (ix-tabulate (lkup-right {s = s} {ri = ri} ¬p (o-i sv (i ∷ []) , refl))))
                                                                      (0 bounded _)
                                                                      ∷ [])))}
                                            {i = i}
                                            (rf∘fr {s = s} {ri = ri} i ¬p))))
                                x


nest : ∀ {a}{X : Set a}{l s} → Ar l X s → (ri : RankedT s) →
       let s₁ , s₂ = ranked-cut s ri in
       Ar l (Ar l X s₂) s₁
nest (imap a) ri = imap λ ov → imap λ iv → a $ ov ri++ iv

--- This is about embedding arrays of multiple levels.

subst-vec : ∀ {n m}{eq : n ≡ m} → (v : Vec ℕ n)  → flat-prod v ≡ (flat-prod $ (subst (Vec ℕ) eq v))
subst-vec {n}{m}{refl} v = refl

sh-embed : ∀ {l} → (s : ShType l) → Σ (ShType (1 + l)) λ s₁ → prod s ≡ prod s₁
sh-embed {zero} tt = (tt , (1 ∷ [])) , refl
sh-embed {suc l} (s , v) = let
     s' , s≡s' = sh-embed s
   in ((s' , subst (Vec _) s≡s' v)) , subst-vec {eq = s≡s'} v


embed : ∀ {a}{X : Set a}{l s}
      → Ar l X s
      → let s' , _ = sh-embed s in
        Ar (1 + l) X s'
embed {l = l}{s = s} a = let s' , eq = sh-embed s in reshape a eq 


module _ where
  a : Ar 1 ℕ (_ , 5 ∷ [])
  a = imap λ iv → let ix fiv = iv in v $ ix-lookup fiv (0 bounded auto≥)

  test₁ : embed a ≡ imap λ iv → (v $ ix-lookup (i-o _ (Ix.flat-ix iv)) (0 bounded auto≥)) / 1
  test₁ = refl



iota : ∀ {l} → (s : ShType l) → Ar l (Ix _ s) s
iota s = imap Function.id

idx→arr : ∀ {l}{s : ShType (1 + l)}
        → Ix _ s
        → let (ss , v) = s in Ar l ℕ ss
idx→arr {l} {ss , v} (ix iv) = imap λ jv → BFin.v $ ix-lookup iv (idx→off _ jv)

shape : ∀ {a}{X : Set a}{l s} → Ar l X s → ShType l
shape {s = s} _ = s


-- dim is morally (shape ∘ shape), but we cannot write it like this
dim : ∀ {a}{X : Set a}{l s} → Ar l X s → ShType (l ∸ 1)
dim {l = zero} {s} _ = tt
dim {l = suc l} {ss , _} _ = ss


-- average pooling with ranked-cut

s≡s' : ∀ m n →  m * 2 * (n * 2 * 1) ≡ m * (n * 2 + (n * 2 + 0))
s≡s' = solve 2 (λ m n → m :* con 2 :* (n :* con 2 :* con 1)
                     := m :* (n :* con 2 :+ (n :* con 2 :+ con 0))) refl

avgp : ∀ {m n}
     → Ar 2 ℕ ((tt , 2 ∷ []) , m * 2 ∷ n * 2 ∷ [])
     → Ar 2 ℕ ((tt , 2 ∷ []) , m ∷ n ∷ [])
avgp {m}{n} a = let
  s₁ : ShType 3
  s₁ = ((_ , 2 ∷ []) , 2 ∷ 2 ∷ [])
      ,  m ∷ 2 ∷ n ∷ 2 ∷ []
  a₁ = reshape {s₁ = s₁} a (s≡s' m n)
  aₙ = nest a₁ ((1 bounded auto≥) , (1 bounded auto≥))
  r₃ = imap λ iv → sum $ unimap aₙ iv
  in reshape r₃ refl

po-eq : ∀ {l s} → (iv jv : Ix l s) → Set
po-eq {zero}  iv jv = iv ≡ jv
po-eq {suc l} (ix iv) (ix jv) = ∀ i → ix-lookup iv i ≡ ix-lookup jv i

fix-eq : ∀ {n}{s} (iv jv : FlatIx n s)  → (∀ i → ix-lookup iv i ≡ ix-lookup jv i) → iv ≡ jv
fix-eq {zero} {[]} [] [] eq = refl
fix-eq {suc n} {x ∷ s} (i ∷ iv) (j ∷ jv) eq = cong₂ _∷_ (eq (0 bounded auto≥)) (fix-eq iv jv (eq ∘ bsuc))

ix-eq : ∀ {l}{s : ShType l} iv jv → po-eq {s = s} iv jv → iv ≡ jv
ix-eq {zero} {s} iv jv refl = refl
ix-eq {suc l} {ss , sv} (ix iv) (ix jv) poeq = cong ix (fix-eq iv jv poeq)

sel-eq : ∀ {a}{X : Set a}{l s}
       → (a : Ar l X s)
       → (iv jv : Ix l s)
       → po-eq {l = l} iv jv
       → unimap a iv ≡ unimap a jv
sel-eq {l = zero} {s} a iv jv refl = refl
sel-eq {l = suc l} {s} a iv jv eq rewrite (ix-eq iv jv eq) = refl

