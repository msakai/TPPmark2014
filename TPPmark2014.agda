{-
TPPmark2014 problem.

See <http://imi.kyushu-u.ac.jp/lasm/tpp2014/tppmark2014-2.pdf> for details.

Checked with and Agda-2.4.2 and agda-stdlib-0.8.1.
-}
module TPPmark2014 where

open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Sum
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import Induction.Nat
open ≡-Reasoning

-- ---------------------------------------------------------------------------

distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distribˡ-*-+ m n o =
  begin
    m * (n + o)
  ≡⟨  *-comm m (n + o) ⟩
    (n + o) * m
  ≡⟨  distribʳ-*-+ m n o ⟩
    n * m + o * m
  ≡⟨  cong (λ x → x + o * m) (*-comm n m) ⟩
    m * n + o * m
  ≡⟨  cong (λ x → m * n + x) (*-comm o m) ⟩
    m * n + m * o
  ∎

*-left-identity : ∀ n → 1 * n ≡ n
*-left-identity n = +-right-identity n

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n = trans (*-comm n 1) (*-left-identity n)

mod-dist-+ : ∀ (a b : ℕ) → (a + b) mod 3 ≡ (toℕ (a mod 3) + toℕ (b mod 3)) mod 3
mod-dist-+ a b = {!!}

mod-dist-* : ∀ (a b : ℕ) → (a * b) mod 3 ≡ (toℕ (a mod 3) * toℕ (b mod 3)) mod 3
mod-dist-* a b = {!!}

_^2 : ℕ → ℕ
_^2 n = n * n

-- ---------------------------------------------------------------------------

-- (i) For any a ∈ N, (a^2 mod 3) = 0 or (a^2 mod 3) = 1.
prop1 : ∀ (a : ℕ) → (a ^2) mod 3 ≡ Fin.zero ⊎ (a ^2) mod 3 ≡ Fin.suc (Fin.zero)
prop1 a rewrite mod-dist-* a a with a mod 3
... | Fin.zero = inj₁ refl
... | (Fin.suc Fin.zero) = inj₂ refl
... | (Fin.suc (Fin.suc Fin.zero)) = inj₂ refl
... | (Fin.suc (Fin.suc (Fin.suc ())))

-- ---------------------------------------------------------------------------

lem5 : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2))
    → (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3 ≡ Fin.zero
lem5 a b c P = begin
    (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3
      ≡⟨ sym (mod-dist-+ (a ^2) (b ^2)) ⟩
    ((a ^2) + (b ^2)) mod 3
      ≡⟨ cong (λ (n : ℕ) → n mod 3) P ⟩
    (3 * (c ^2)) mod 3
      ≡⟨ mod-dist-* 3 (c ^2) ⟩
    Fin.zero
      ∎

lem6 : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2))
    → (a ^2) mod 3 ≡ Fin.zero
lem6 a b c P with prop1 a
... | inj₁ p = p
... | inj₂ p with prop1 b
...     | inj₁ q = ⊥-elim (1≢0 1≡0)
            where
              1≢0 : ¬ Fin.suc Fin.zero ≡ Fin.zero {2}
              1≢0 ()

              1≡0 : Fin.suc Fin.zero ≡ Fin.zero {2}
              1≡0 =
                begin
                  Fin.suc Fin.zero
                ≡⟨ refl ⟩
                  (toℕ (Fin.suc (Fin.zero {1})) + toℕ (Fin.zero {2})) mod 3
                ≡⟨ cong (λ x → (toℕ x + toℕ (Fin.zero {2})) mod 3) (sym p) ⟩
                  (toℕ ((a ^2) mod 3) + toℕ (Fin.zero {2})) mod 3
                ≡⟨ cong (λ x → (toℕ ((a ^2) mod 3) + toℕ x) mod 3) (sym q) ⟩
                  (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3
                ≡⟨ lem5 a b c P ⟩
                  Fin.zero
                ∎
...     | inj₂ q = ⊥-elim (2≢0 2≡0)
            where
              2≢0 : ¬ Fin.suc (Fin.suc Fin.zero) ≡ Fin.zero {2}
              2≢0 ()

              2≡0 : Fin.suc (Fin.suc Fin.zero) ≡ Fin.zero {2}
              2≡0 =
                begin
                  Fin.suc (Fin.suc (Fin.zero {0}))
                ≡⟨ refl ⟩
                  (toℕ (Fin.suc (Fin.zero {1})) + toℕ (Fin.suc (Fin.zero {1}))) mod 3
                ≡⟨ cong (λ x → (toℕ x + toℕ (Fin.suc (Fin.zero {1}))) mod 3) (sym p) ⟩
                  (toℕ ((a ^2) mod 3) + toℕ (Fin.suc (Fin.zero {1}))) mod 3
                ≡⟨ cong (λ x → (toℕ ((a ^2) mod 3) + toℕ x) mod 3) (sym q) ⟩
                  (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3
                ≡⟨ lem5 a b c P ⟩
                  Fin.zero
                ∎

rem0→∣ : ∀ {a} → (a mod 3 ≡ Fin.zero) → (3 ∣ a)
rem0→∣ {a} P = divides (a div 3) $ begin
      a
    ≡⟨ DivMod.property (a divMod 3) ⟩
      toℕ (a mod 3) + (a div 3) * 3
    ≡⟨ cong (λ x → toℕ x + (a div 3) * 3) P ⟩
      toℕ (Fin.zero {2}) + (a div 3) * 3
    ≡⟨ refl ⟩
      (a div 3) * 3
    ∎

3∣*-split : ∀ (a b : ℕ) → (3 ∣ a * b) → (3 ∣ a) ⊎ (3 ∣ b)
3∣*-split a b P = {!!}

3∣^2→3∣ : ∀ {a} → (3 ∣ a ^2) → (3 ∣ a)
3∣^2→3∣ {a} P with 3∣*-split a a P
... | inj₁ p = p
... | inj₂ p = p

-- (ii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then (3 | a), (3 | b) and (3 | c).
prop2a : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → (3 ∣ a)
prop2a a b c a^2+b^2≡3c^2 = 3∣^2→3∣ 3∣a^2
  where
    lem : (a ^2) mod 3 ≡ Fin.zero
    lem = lem6 a b c a^2+b^2≡3c^2

    3∣a^2 : 3 ∣ a ^2
    3∣a^2 = rem0→∣ lem

prop2b : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → (3 ∣ b)
prop2b a b c a^2+b^2≡3c^2 = prop2a b a c b^2+a^2≡3*c^2
  where
    b^2+a^2≡3*c^2 : (b ^2 + a ^2 ≡ 3 * (c ^2))
    b^2+a^2≡3*c^2 = begin
        b ^2 + a ^2
      ≡⟨ +-comm (b ^2) (a ^2) ⟩
        a ^2 + b ^2
      ≡⟨ a^2+b^2≡3c^2 ⟩
        3 * (c ^2)
      ∎

3∣→9∣^2 : ∀ {a} → (3 ∣ a) → (9 ∣ a ^2)
3∣→9∣^2 {a} (divides q P) = divides (q * q) $ begin
    a ^2
  ≡⟨ cong (λ x → x ^2) P ⟩
    (q * 3) ^2
  ≡⟨ refl ⟩
    (q * 3) * (q * 3)
  ≡⟨ refl ⟩
    (q * 3) * (q * 3)
  ≡⟨ sym (*-assoc (q * 3) q 3) ⟩
    ((q * 3) * q) * 3
  ≡⟨ cong (λ x → x * 3) (*-assoc q 3 q) ⟩
    (q * (3 * q)) * 3
  ≡⟨ cong (λ x → (q * x) * 3) (*-comm 3 q) ⟩
    (q * (q * 3)) * 3
  ≡⟨ cong (λ x → x * 3) (sym (*-assoc q q 3)) ⟩
    ((q * q) * 3) * 3
  ≡⟨ *-assoc (q * q) 3 3 ⟩
    (q * q) * (3 * 3)
  ≡⟨ refl ⟩
    q * q * 9
  ∎

prop2c : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → (3 ∣ c)
prop2c a b c P = 3∣^2→3∣ 3∣c^2
  where
    9∣a^2 : 9 ∣ a ^2
    9∣a^2 = 3∣→9∣^2 (prop2a a b c P)

    9∣b^2 : 9 ∣ b ^2
    9∣b^2 = 3∣→9∣^2 (prop2b a b c P)

    9∣a^2+b^2 : 9 ∣ a ^2 + b ^2
    9∣a^2+b^2 = ∣-+ 9∣a^2 9∣b^2

    9∣3*c^2 : 9 ∣ 3 * (c ^2)
    9∣3*c^2 = subst (λ x → 9 ∣ x) P 9∣a^2+b^2

    3∣c^2 : 3 ∣ (c ^2)
    3∣c^2 = /-cong 2 9∣3*c^2

-- ---------------------------------------------------------------------------

lem1 : ∀ {a} → (3∣a : 3 ∣ a) → ¬ a ≡ 0 → quotient 3∣a < a
lem1 {a} (divides q a≡q*3) a≢0 = {!!}

lem2 : ∀ {a} → (3∣a : 3 ∣ a) → (quotient 3∣a ≡ 0) → a ≡ 0
lem2 {a} (divides q a≡q*3) q≡0 = begin
    a
  ≡⟨ a≡q*3 ⟩
    q * 3
  ≡⟨ cong (λ x → x * 3) q≡0 ⟩
    0 * 3
  ≡⟨ refl ⟩
    0
  ∎

lem3 : ∀ {a} → (3∣a : 3 ∣ a) → ¬ a ≡ 0 → ¬ (quotient 3∣a ≡ 0)
lem3 {a} 3∣a a≢0 q∣a≡0 = a≢0 (lem2 3∣a q∣a≡0)

lem4 : ∀ (a b c : ℕ) → ((3 * a) ^2 + (3 * b) ^2 ≡ 3 * (3 * c) ^2) → a ^2 + b ^2 ≡ 3 * (c ^2)
lem4 a b c P = {!!}

lem : ∀ (a b c : ℕ) → (a * 3) ^2 + (b * 3) ^2 ≡ 3 * (c * 3) ^2 → a ^2 + b ^2 ≡ 3 * (c ^2)
lem a b c P = cancel-*-right (a ^2 + b ^2) (3 * (c ^2)) Q
  where
    Q : (a ^2 + b ^2) * 9 ≡ (3 * (c ^2)) * 9
    Q = begin
          (a ^2 + b ^2) * 9
        ≡⟨ distribʳ-*-+ 9 (a ^2) (b ^2) ⟩
          (a ^2 * 9 + b ^2 * 9)
        ≡⟨ {!!} ⟩
          (a * 3) ^2 + (b * 3) ^2
        ≡⟨ P ⟩
          3 * (c * 3) ^2
        ≡⟨ refl ⟩
          3 * ((c * 3) * (c * 3))
        ≡⟨ {!!} ⟩
          (3 * (c ^2)) * 9
        ∎

s<s*3 : ∀ m → suc m < suc m * 3
s<s*3 m = subst (λ x → 1 + m < x) (*-comm (2 + n) (1 + m)) P
  where
    n = 1

    2+m≤2+m : 2 + m ≤ 2 + m
    2+m≤2+m = ≤′⇒≤ ≤′-refl

    2+m≤2+m+m+n+nm : 2 + m ≤ (2 + m) + (m + (n + n * m))
    2+m≤2+m+m+n+nm = m≤m+n (2 + m) (m + (n + n * m))
    
    1+m<2+m+m+n+nm : 1 + m < (2 + m) + (m + (n + n * m))
    1+m<2+m+m+n+nm = 2+m≤2+m+m+n+nm
  
    2+m+m+n+nm≡ssn*sm : (2 + m) + (m + (n + n * m)) ≡ (2 + n) * (1 + m)
    2+m+m+n+nm≡ssn*sm = sym $
      begin
        (2 + n) * (1 + m)
      ≡⟨ distribʳ-*-+ (1 + m) 2 n ⟩
        2 * (1 + m) + n * (1 + m)
      ≡⟨ cong (λ x → x + n * (1 + m)) (distribˡ-*-+ 2 1 m) ⟩
        (2 + 2 * m) + n * (1 + m)
      ≡⟨ cong (λ x → 2 + 2 * m + x) (distribˡ-*-+ n 1 m) ⟩
        (2 + 2 * m) + (n * 1 + n * m)
      ≡⟨ refl ⟩
        (2 + (m + (m + 0))) + (n * 1 + n * m)
      ≡⟨ cong (λ x → 2 + (m + x) + (n * 1 + n * m)) (+-right-identity m) ⟩
        (2 + (m + m)) + (n * 1 + n * m)
      ≡⟨  cong (λ x → 2 + (m + m) + (x + n * m)) (*-right-identity n) ⟩
        (2 + (m + m)) + (n + n * m)
      ≡⟨  cong (λ x → x + (n + n * m)) (sym (+-assoc 2 m m)) ⟩
        ((2 + m) + m) + (n + n * m)
      ≡⟨  +-assoc (2 + m) m (n + n * m) ⟩
        (2 + m) + (m + (n + n * m))
      ∎

    P : 1 + m < (2 + n) * (1 + m)
    P = subst (λ x → 1 + m < x) 2+m+m+n+nm≡ssn*sm 1+m<2+m+m+n+nm

3∣sn→q<sn : ∀ n → (3∣sn : 3 ∣ suc n) → quotient 3∣sn < suc n
3∣sn→q<sn n (divides zero ())
3∣sn→q<sn n (divides (suc m) sn≡sm*3) = subst (λ x → suc m < x) (sym sn≡sm*3) P
  where
    P : suc m < suc m * 3
    P = s<s*3 m

prop3a-step
  : ∀ a
  → (∀ a' → (a' <′ a) → ∀ b' c' → (a' ^2 + b' ^2 ≡ 3 * (c' ^2)) → a' ≡ 0)
  → ∀ b c → (a ^2 + b ^2 ≡ 3 * (c ^2)) → a ≡ 0
prop3a-step zero rec b c P = refl
prop3a-step (suc n) rec b c P = trans a≡a'*3 a'*3≡0
  where
    a : ℕ
    a = suc n
    3∣a : 3 ∣ a
    3∣a = prop2a a b c P
    3∣b : 3 ∣ b
    3∣b = prop2b a b c P
    3∣c : 3 ∣ c
    3∣c = prop2c a b c P
    a' : ℕ
    a' = quotient 3∣a
    b' : ℕ
    b' = quotient 3∣b
    c' : ℕ
    c' = quotient 3∣b
    Q : a' ^2 + b' ^2 ≡ 3 * (c' ^2)
    Q = {!!}
    a'<a : a' < a
    a'<a = 3∣sn→q<sn n 3∣a
    a'≡0 : a' ≡ 0
    a'≡0 = rec a' (≤⇒≤′ a'<a) b' c' Q
    a'*3≡0 : a' * 3 ≡ 0
    a'*3≡0 = cong (λ x → x * 3) a'≡0
    a≡a'*3 : a ≡ a' * 3
    a≡a'*3 = {!!}

-- (iii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then a = b = c = 0.
prop3a : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → a ≡ 0
prop3a a = <-rec (λ n → ∀ b c → (n ^2 + b ^2 ≡ 3 * (c ^2)) → n ≡ 0) prop3a-step a

prop3b : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → b ≡ 0
prop3b a b c a^2+b^2≡3c^2 = prop3a b a c b^2+a^2≡3*c^2
  where
    b^2+a^2≡3*c^2 : (b ^2 + a ^2 ≡ 3 * (c ^2))
    b^2+a^2≡3*c^2 = begin
        b ^2 + a ^2
      ≡⟨ +-comm (b ^2) (a ^2) ⟩
        a ^2 + b ^2
      ≡⟨ a^2+b^2≡3c^2 ⟩
        3 * (c ^2)
      ∎

prop3c : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → c ≡ 0
prop3c a b c P = {!!}
