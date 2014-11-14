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

mod-dist-+ : ∀ a b → (a + b) mod 3 ≡ (toℕ (a mod 3) + toℕ (b mod 3)) mod 3
mod-dist-+ a b = {!!}

mod-dist-* : ∀ a b → (a * b) mod 3 ≡ (toℕ (a mod 3) * toℕ (b mod 3)) mod 3
mod-dist-* a b = {!!}

_² : ℕ → ℕ
_² n = n * n

distrib-²-* : ∀ m n → (m * n) ² ≡ m ² * n ²
distrib-²-* m n =
  begin
    (m * n) ²
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
    m ² * n ²
  ∎

rem≡0⇒∣ : ∀ {a n} → (a mod (suc n) ≡ Fin.zero) → (suc n ∣ a)
rem≡0⇒∣ {a} {n} P = divides (a div m) $ begin
      a
    ≡⟨ DivMod.property (a divMod m) ⟩
      toℕ (a mod m) + (a div m) * m
    ≡⟨ cong (λ x → toℕ x + (a div m) * m) P ⟩
      toℕ (Fin.zero {n}) + (a div m) * m
    ≡⟨ refl ⟩
      (a div m) * m
    ∎
  where
    m = suc n

-- TODO: 3が素数であることを利用して証明したいが、面倒なので a mod 3 と b mod 3 による場合分けで力技で証明する方針で
3∣*-split : ∀ a b → (3 ∣ a * b) → (3 ∣ a) ⊎ (3 ∣ b)
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

3∣²⇒3∣ : ∀ {a} → (3 ∣ a ²) → (3 ∣ a)
3∣²⇒3∣ {a} P with 3∣*-split a a P
... | inj₁ p = p
... | inj₂ p = p

*∣* : ∀ {a₁ n₁ a₂ n₂} → (suc n₁ ∣ a₁) → (suc n₂ ∣ a₂) → (suc n₁ * suc n₂ ∣ a₁ * a₂)
*∣* {a₁} {n₁} {a₂} {n₂} (divides q₁ a₁≡q₁*m₁) (divides q₂ a₂≡q₂*m₂) = divides (q₁ * q₂) $ begin
      a₁ * a₂
    ≡⟨ cong (λ x → x * a₂) a₁≡q₁*m₁ ⟩
      (q₁ * m₁) * a₂
    ≡⟨ cong (λ x → (q₁ * m₁) * x) a₂≡q₂*m₂ ⟩
      (q₁ * m₁) * (q₂ * m₂)
    ≡⟨ sym (*-assoc (q₁ * m₁) q₂ m₂) ⟩
      ((q₁ * m₁) * q₂) * m₂
    ≡⟨ cong (λ x → x * m₂) (*-assoc q₁ m₁ q₂) ⟩
      (q₁ * (m₁ * q₂)) * m₂
    ≡⟨ cong (λ x → (q₁ * x) * m₂) (*-comm m₁ q₂) ⟩
      (q₁ * (q₂ * m₁)) * m₂
    ≡⟨ cong (λ x → x * m₂) (sym (*-assoc q₁ q₂ m₁)) ⟩
      ((q₁ * q₂) * m₁) * m₂
    ≡⟨ *-assoc (q₁ * q₂) m₁ m₂ ⟩
      (q₁ * q₂) * (m₁ * m₂)
    ∎
  where
    m₁ = suc n₁
    m₂ = suc n₂

∣⇒²∣² : ∀ {a n} → (suc n ∣ a) → ((suc n) ² ∣ a ²)
∣⇒²∣² {a} {n} 1+n∣a = *∣* 1+n∣a 1+n∣a

s<s*ss : ∀ m n → suc m < suc m * suc (suc n)
s<s*ss m n = subst (λ x → 1 + m < x) (*-comm (2 + n) (1 + m)) P
  where
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

3∣sn⇒quot<sn : ∀ {n} → (3∣sn : 3 ∣ suc n) → (quotient 3∣sn < suc n)
3∣sn⇒quot<sn {n} (divides zero ())
3∣sn⇒quot<sn {n} (divides (suc m) sn≡sm*3) = subst (λ x → suc m < x) (sym sn≡sm*3) P
  where
    P : suc m < suc m * 3
    P = s<s*ss m 1

-- ---------------------------------------------------------------------------
-- (i) For any a ∈ N, (a^2 mod 3) = 0 or (a^2 mod 3) = 1.

prop1 : ∀ a → (a ² mod 3 ≡ Fin.zero) ⊎ (a ² mod 3 ≡ Fin.suc (Fin.zero))
prop1 a rewrite mod-dist-* a a with a mod 3
... | Fin.zero = inj₁ refl
... | (Fin.suc Fin.zero) = inj₂ refl
... | (Fin.suc (Fin.suc Fin.zero)) = inj₂ refl
... | (Fin.suc (Fin.suc (Fin.suc ())))

-- ---------------------------------------------------------------------------

private
  lem1 : ∀ a b c → a ² + b ² ≡ 3 * c ²
      → (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3 ≡ Fin.zero
  lem1 a b c P = begin
      (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
        ≡⟨ sym (mod-dist-+ (a ²) (b ²)) ⟩
      (a ² + b ²) mod 3
        ≡⟨ cong (λ x → x mod 3) P ⟩
      (3 * c ²) mod 3
        ≡⟨ mod-dist-* 3 (c ²) ⟩
      Fin.zero
        ∎
  
  lem2 : ∀ a b c → a ² + b ² ≡ 3 * c ² → a ² mod 3 ≡ Fin.zero
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
                    (toℕ (a ² mod 3) + toℕ (Fin.zero {2})) mod 3
                  ≡⟨ cong (λ x → (toℕ (a ² mod 3) + toℕ x) mod 3) (sym q) ⟩
                    (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
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
                    (toℕ (a ² mod 3) + toℕ (Fin.suc (Fin.zero {1}))) mod 3
                  ≡⟨ cong (λ x → (toℕ (a ² mod 3) + toℕ x) mod 3) (sym q) ⟩
                    (toℕ (a ² mod 3) + toℕ (b ² mod 3)) mod 3
                  ≡⟨ lem1 a b c P ⟩
                    Fin.zero
                  ∎

-- (ii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then (3 | a), (3 | b) and (3 | c).
prop2a : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ a)
prop2a a b c a²+b²≡3c² = 3∣²⇒3∣ 3∣a²
  where
    lem : a ² mod 3 ≡ Fin.zero
    lem = lem2 a b c a²+b²≡3c²

    3∣a² : 3 ∣ a ²
    3∣a² = rem≡0⇒∣ lem

prop2b : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ b)
prop2b a b c a²+b²≡3c² = prop2a b a c b²+a²≡3*c²
  where
    b²+a²≡3*c² : (b ² + a ² ≡ 3 * c ²)
    b²+a²≡3*c² = begin
        b ² + a ²
      ≡⟨ +-comm (b ²) (a ²) ⟩
        a ² + b ²
      ≡⟨ a²+b²≡3c² ⟩
        3 * c ²
      ∎

prop2c : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → (3 ∣ c)
prop2c a b c P = 3∣²⇒3∣ 3∣c²
  where
    9∣a² : 9 ∣ a ²
    9∣a² = ∣⇒²∣² (prop2a a b c P)

    9∣b² : 9 ∣ b ²
    9∣b² = ∣⇒²∣² (prop2b a b c P)

    9∣a²+b² : 9 ∣ a ² + b ²
    9∣a²+b² = ∣-+ 9∣a² 9∣b²

    9∣3*c² : 9 ∣ 3 * c ²
    9∣3*c² = subst (λ x → 9 ∣ x) P 9∣a²+b²

    3∣c² : 3 ∣ c ²
    3∣c² = /-cong 2 9∣3*c²

-- ---------------------------------------------------------------------------
-- (iii) Let a ∈ N, b ∈ N and c ∈ N. If a^2 + b^2 = 3c^2 then a = b = c = 0.

private
  lem3 : ∀ a b c → (a * 3) ² + (b * 3) ² ≡ 3 * (c * 3) ² → a ² + b ² ≡ 3 * c ²
  lem3 a b c P = cancel-*-right (a ² + b ²) (3 * c ²) Q
    where  
      Q : (a ² + b ²) * 3 ² ≡ (3 * c ²) * 3 ²
      Q = begin
            (a ² + b ²) * 3 ²
          ≡⟨ distribʳ-*-+ (3 ²) (a ²) (b ²) ⟩
            a ² * 3 ² + b ² * 3 ²
          ≡⟨ cong (λ x → x + b ² * 3 ²) (sym (distrib-²-* a 3)) ⟩
            (a * 3) ² + b ² * 3 ²
          ≡⟨ cong (λ x → (a * 3) ² + x) (sym (distrib-²-* b 3)) ⟩
            (a * 3) ² + (b * 3) ²
          ≡⟨ P ⟩
            3 * (c * 3) ²
          ≡⟨ cong (λ x → 3 * x) (distrib-²-* c 3) ⟩
            3 * (c ² * 3 ²)
          ≡⟨ sym (*-assoc 3 (c ²) (3 ²)) ⟩
            (3 * c ²) * 3 ²
          ∎

prop3a-step
  : ∀ a
  → (∀ a' → (a' <′ a) → ∀ b' c' → (a' ² + b' ² ≡ 3 * c' ²) → a' ≡ 0)
  → ∀ b c → (a ² + b ² ≡ 3 * c ²) → a ≡ 0
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
            P2 : (a' * 3) ² + (b' * 3) ² ≡ 3 * (c' * 3) ²
            P2 rewrite (sym a≡a'*3) | (sym b≡b'*3) | (sym c≡c'*3) = P
            P3 : a' ² + b' ² ≡ 3 * c' ²
            P3 = lem3 a' b' c' P2
            a'<a : a' < a
            a'<a = 3∣sn⇒quot<sn (divides a' a≡a'*3)

prop3a : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → a ≡ 0
prop3a a = <-rec (λ n → ∀ b c → (n ² + b ² ≡ 3 * c ²) → n ≡ 0) prop3a-step a

prop3b : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → b ≡ 0
prop3b a b c a²+b²≡3c² = prop3a b a c b²+a²≡3*c²
  where
    b²+a²≡3*c² : b ² + a ² ≡ 3 * c ²
    b²+a²≡3*c² = begin
        b ² + a ²
      ≡⟨ +-comm (b ²) (a ²) ⟩
        a ² + b ²
      ≡⟨ a²+b²≡3c² ⟩
        3 * c ²
      ∎

prop3c-step
  : ∀ c
  → (∀ c' → (c' <′ c) → ∀ a' b' → (a' ² + b' ² ≡ 3 * c' ²) → c' ≡ 0)
  → ∀ a b → (a ² + b ² ≡ 3 * c ²) → c ≡ 0
prop3c-step zero rec a b P = refl
prop3c-step (suc n) rec a b P = body
  where
    c : ℕ
    c = suc n

    body : c ≡ 0
    body with (prop2a a b c P) | (prop2b a b c P) | (prop2c a b c P)
    ... | divides a' a≡a'*3 | divides b' b≡b'*3 | divides c' c≡c'*3 =
        begin
          c
        ≡⟨ c≡c'*3 ⟩
          c' * 3
        ≡⟨ cong (λ x → x * 3) c'≡0 ⟩
          0 * 3
        ≡⟨ refl ⟩
          0
        ∎
      where
        c'≡0 : c' ≡ 0
        c'≡0 = rec c' (≤⇒≤′ c'<c) a' b' P3
          where
            P2 : (a' * 3) ² + (b' * 3) ² ≡ 3 * (c' * 3) ²
            P2 rewrite (sym a≡a'*3) | (sym b≡b'*3) | (sym c≡c'*3) = P
            P3 : a' ² + b' ² ≡ 3 * c' ²
            P3 = lem3 a' b' c' P2
            c'<c : c' < c
            c'<c = 3∣sn⇒quot<sn (divides c' c≡c'*3)

prop3c : ∀ a b c → (a ² + b ² ≡ 3 * c ²) → c ≡ 0
prop3c a b c = <-rec (λ n → ∀ a₁ b₁ → a₁ ² + b₁ ² ≡ 3 * n ² → n ≡ 0) prop3c-step c a b
