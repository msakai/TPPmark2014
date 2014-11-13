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

quot≡0⇒3∣ : ∀ {a} → (a mod 3 ≡ Fin.zero) → (3 ∣ a)
quot≡0⇒3∣ {a} P = divides (a div 3) $ begin
      a
    ≡⟨ DivMod.property (a divMod 3) ⟩
      toℕ (a mod 3) + (a div 3) * 3
    ≡⟨ cong (λ x → toℕ x + (a div 3) * 3) P ⟩
      toℕ (Fin.zero {2}) + (a div 3) * 3
    ≡⟨ refl ⟩
      (a div 3) * 3
    ∎

-- TODO: 3が素数であることを利用して証明したいが、面倒なので a mod 3 と b mod 3 による場合分けで力技で証明する方針で
3∣*-split : ∀ (a b : ℕ) → (3 ∣ a * b) → (3 ∣ a) ⊎ (3 ∣ b)
3∣*-split a b (divides q a*b≡q*3) = {!!}
  where
    P : (toℕ (a mod 3) * toℕ (b mod 3)) mod 3 ≡ Fin.zero
    P = begin
          (toℕ (a mod 3) * toℕ (b mod 3)) mod 3
        ≡⟨ sym (mod-dist-* a b) ⟩
          (a * b) mod 3
        ≡⟨ cong (λ x → x mod 3) a*b≡q*3 ⟩
          (q * 3) mod 3
        ≡⟨ cong (λ x → x mod 3) (*-comm q 3) ⟩
          (3 * q) mod 3
        ≡⟨ mod-dist-* 3 q ⟩
          Fin.zero
        ∎

3∣^2⇒3∣ : ∀ {a} → (3 ∣ a ^2) → (3 ∣ a)
3∣^2⇒3∣ {a} P with 3∣*-split a a P
... | inj₁ p = p
... | inj₂ p = p

3∣⇒9∣^2 : ∀ {a} → (3 ∣ a) → (9 ∣ a ^2)
3∣⇒9∣^2 {a} (divides q P) = divides (q * q) $ begin
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

3∣sn⇒quot<sn : ∀ n → (3∣sn : 3 ∣ suc n) → quotient 3∣sn < suc n
3∣sn⇒quot<sn n (divides zero ())
3∣sn⇒quot<sn n (divides (suc m) sn≡sm*3) = subst (λ x → suc m < x) (sym sn≡sm*3) P
  where
    P : suc m < suc m * 3
    P = s<s*3 m

-- ---------------------------------------------------------------------------
-- (i) For any a ∈ N, (a^2 mod 3) = 0 or (a^2 mod 3) = 1.

prop1 : ∀ (a : ℕ) → (a ^2) mod 3 ≡ Fin.zero ⊎ (a ^2) mod 3 ≡ Fin.suc (Fin.zero)
prop1 a rewrite mod-dist-* a a with a mod 3
... | Fin.zero = inj₁ refl
... | (Fin.suc Fin.zero) = inj₂ refl
... | (Fin.suc (Fin.suc Fin.zero)) = inj₂ refl
... | (Fin.suc (Fin.suc (Fin.suc ())))

-- ---------------------------------------------------------------------------

lem1 : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2))
    → (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3 ≡ Fin.zero
lem1 a b c P = begin
    (toℕ ((a ^2) mod 3) + toℕ ((b ^2) mod 3)) mod 3
      ≡⟨ sym (mod-dist-+ (a ^2) (b ^2)) ⟩
    ((a ^2) + (b ^2)) mod 3
      ≡⟨ cong (λ (n : ℕ) → n mod 3) P ⟩
    (3 * (c ^2)) mod 3
      ≡⟨ mod-dist-* 3 (c ^2) ⟩
    Fin.zero
      ∎

lem2 : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2))
    → (a ^2) mod 3 ≡ Fin.zero
lem2 a b c P with prop1 a
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
                ≡⟨ lem1 a b c P ⟩
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
                ≡⟨ lem1 a b c P ⟩
                  Fin.zero
                ∎

-- (ii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then (3 | a), (3 | b) and (3 | c).
prop2a : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → (3 ∣ a)
prop2a a b c a^2+b^2≡3c^2 = 3∣^2⇒3∣ 3∣a^2
  where
    lem : (a ^2) mod 3 ≡ Fin.zero
    lem = lem2 a b c a^2+b^2≡3c^2

    3∣a^2 : 3 ∣ a ^2
    3∣a^2 = quot≡0⇒3∣ lem

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

prop2c : ∀ (a b c : ℕ) → (a ^2 + b ^2 ≡ 3 * (c ^2)) → (3 ∣ c)
prop2c a b c P = 3∣^2⇒3∣ 3∣c^2
  where
    9∣a^2 : 9 ∣ a ^2
    9∣a^2 = 3∣⇒9∣^2 (prop2a a b c P)

    9∣b^2 : 9 ∣ b ^2
    9∣b^2 = 3∣⇒9∣^2 (prop2b a b c P)

    9∣a^2+b^2 : 9 ∣ a ^2 + b ^2
    9∣a^2+b^2 = ∣-+ 9∣a^2 9∣b^2

    9∣3*c^2 : 9 ∣ 3 * (c ^2)
    9∣3*c^2 = subst (λ x → 9 ∣ x) P 9∣a^2+b^2

    3∣c^2 : 3 ∣ (c ^2)
    3∣c^2 = /-cong 2 9∣3*c^2

-- ---------------------------------------------------------------------------
-- (iii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then a = b = c = 0.

lem3 : ∀ (a b c : ℕ) → (a * 3) ^2 + (b * 3) ^2 ≡ 3 * (c * 3) ^2 → a ^2 + b ^2 ≡ 3 * (c ^2)
lem3 a b c P = cancel-*-right (a ^2 + b ^2) (3 * (c ^2)) Q
  where
    f : ∀ m n → (m * n) ^2 ≡ m ^2 * n ^2
    f m n = 
      begin
        (m * n) ^2
      ≡⟨ refl ⟩
        (m * n) * (m * n)
      ≡⟨ *-assoc m n (m * n) ⟩
        m * (n * (m * n))
      ≡⟨ cong (λ x → m * x) (*-comm n (m * n)) ⟩
        m * ((m * n) * n)
      ≡⟨ cong (λ x → m * x) (*-assoc m n n) ⟩
        m * (m * (n * n))
      ≡⟨ sym (*-assoc m m (n * n)) ⟩
        (m * m) * (n * n)
      ≡⟨ refl ⟩
        m ^2 * n ^2
      ∎

    Q : (a ^2 + b ^2) * 3 ^2 ≡ (3 * (c ^2)) * 3 ^2
    Q = begin
          (a ^2 + b ^2) * 3 ^2
        ≡⟨ distribʳ-*-+ (3 ^2) (a ^2) (b ^2) ⟩
          a ^2 * 3 ^2 + b ^2 * 3 ^2
        ≡⟨ cong (λ x → x + b ^2 * 3 ^2) (sym (f a 3)) ⟩
          (a * 3) ^2 + b ^2 * 3 ^2
        ≡⟨ cong (λ x → (a * 3) ^2 + x) (sym (f b 3)) ⟩
          (a * 3) ^2 + (b * 3) ^2
        ≡⟨ P ⟩
          3 * (c * 3) ^2
        ≡⟨ cong (λ x → 3 * x) (f c 3) ⟩
          3 * (c ^2 * 3 ^2)
        ≡⟨ sym (*-assoc 3 (c ^2) (3 ^2)) ⟩
          (3 * c ^2) * 3 ^2
        ∎

prop3a-step
  : ∀ a
  → (∀ a' → (a' <′ a) → ∀ b' c' → (a' ^2 + b' ^2 ≡ 3 * (c' ^2)) → a' ≡ 0)
  → ∀ b c → (a ^2 + b ^2 ≡ 3 * (c ^2)) → a ≡ 0
prop3a-step zero rec b c P = refl
prop3a-step (suc n) rec b c P = body
  where
    a : ℕ
    a = suc n

    body : a ≡ 0
    body with (prop2a a b c P) | (prop2b a b c P) | (prop2c a b c P)
    ... | divides a' a≡a'*3 | divides b' b≡b'*3 | divides c' c≡c'*3 =
        begin
          a
        ≡⟨ a≡a'*3 ⟩
          a' * 3
        ≡⟨ cong (λ x → x * 3) a'≡0 ⟩
          0 * 3
        ≡⟨ refl ⟩
          0
        ∎
      where
        a'≡0 : a' ≡ 0
        a'≡0 = rec a' (≤⇒≤′ a'<a) b' c' P3
          where
            P2 : (a' * 3) ^2 + (b' * 3) ^2 ≡ 3 * ((c' * 3) ^2)
            P2 rewrite (sym a≡a'*3) | (sym b≡b'*3) | (sym c≡c'*3) = P
            P3 : a' ^2 + b' ^2 ≡ 3 * (c' ^2)
            P3 = lem3 a' b' c' P2
            a'<a : a' < a
            a'<a = 3∣sn⇒quot<sn n (divides a' a≡a'*3)

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
