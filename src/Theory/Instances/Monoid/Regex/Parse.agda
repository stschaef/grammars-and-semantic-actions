{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX regex source text, elaborated to an `RE`.

   This is the bootstrap and it is *not* verified: an ordinary recursive
   descent in the metalanguage, run at elaboration time on a literal, so
   what reaches the theory is a regex value like any other.  Nothing
   downstream depends on the parser being right -- if it builds the wrong
   `RE`, the wrong language is decided, correctly.

   Nullability is not known until the parse finishes, so the result is
   `Σ Nullability RE`.  On a literal Agda normalises that away.

   A malformed pattern is a *type* error at the use site, because
   `IsJust nothing` is `⊥`. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Regex.Parse where

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _∸_)
import Agda.Builtin.Nat as AN
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Maybe as M
import Agda.Builtin.Char as AC
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Regex.Unicode public

-- A regex whose nullability is only known once it is built

RE? : Type ℓ-zero
RE? = Σ[ n ∈ Nullability ] RE n

private
  infixr 20 _⊗?_
  infixr 19 _⊕?_

  _⊗?_ : RE? → RE? → RE?
  (n , r) ⊗? (n' , r') = n ·ν n' , r ⊗r r'

  _⊕?_ : RE? → RE? → RE?
  (n , r) ⊕? (n' , r') = n +ν n' , r ⊕r r'

  ε? : RE?
  ε? = nullable , εr

  sat? : (UChar → Bool) → RE?
  sat? P = notNullable , satr P

  opt? : RE? → RE?
  opt? (n , r) = nullable , εr ⊕r r

  -- The repetition operators need a body that consumes.  `(a?)*` is the
  -- pathological case every engine special-cases; here the type rules it
  -- out, so the parser rejects it rather than looping.
  star? plus? : RE? → M.Maybe RE?
  star? (notNullable , r) = M.just (nullable , r *r)
  star? (nullable , _) = M.nothing
  plus? (notNullable , r) = M.just (notNullable , r +r)
  plus? (nullable , _) = M.nothing

  rep? : ℕ → ℕ → RE? → M.Maybe RE?
  rep? n extra (notNullable , r) = M.just (zerob n , betweenr n extra r)
  rep? n extra (nullable , _) = M.nothing

private
  Src : Type ℓ-zero
  Src = List AC.Char

  Par : Type ℓ-zero → Type ℓ-zero
  Par A = Src → M.Maybe (A × Src)

  infixl 1 _>>=?_
  _>>=?_ : {A B : Type ℓ-zero} → M.Maybe A → (A → M.Maybe B) → M.Maybe B
  M.nothing >>=? f = M.nothing
  M.just a >>=? f = f a

  eq : AC.Char → AC.Char → Bool
  eq = AC.primCharEquality

  elem : AC.Char → List AC.Char → Bool
  elem c [] = false
  elem c (d ∷ ds) = eq c d or elem c ds

  special : List AC.Char
  special = '|' ∷ '*' ∷ '+' ∷ '?' ∷ '(' ∷ ')' ∷ '[' ∷ ']'
          ∷ '{' ∷ '}' ∷ '.' ∷ '\\' ∷ []

  lit : AC.Char → Par Unit
  lit c [] = M.nothing
  lit c (d ∷ cs) with eq c d
  ... | true = M.just (tt , cs)
  ... | false = M.nothing

  digitVal : AC.Char → M.Maybe ℕ
  digitVal c = indexOf ('0' ∷ '1' ∷ '2' ∷ '3' ∷ '4'
                      ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷ []) 0
    where
    indexOf : List AC.Char → ℕ → M.Maybe ℕ
    indexOf [] _ = M.nothing
    indexOf (d ∷ ds) v with eq c d
    ... | true = M.just v
    ... | false = indexOf ds (suc v)

  number : Src → M.Maybe (ℕ × Src)
  number cs = readDigits cs 0 false
    where
    readDigits : Src → ℕ → Bool → M.Maybe (ℕ × Src)
    readDigits [] acc true = M.just (acc , [])
    readDigits [] acc false = M.nothing
    readDigits (c ∷ cs) acc seen with digitVal c
    ... | M.just d = readDigits cs (AN._+_ (AN._*_ acc 10) d) true
    ... | M.nothing with seen
    ...   | true = M.just (acc , c ∷ cs)
    ...   | false = M.nothing

private
  escaped : AC.Char → M.Maybe RE?
  escaped 'd' = M.just (sat? isDigit)
  escaped 'D' = M.just (sat? λ c → not (isDigit c))
  escaped 'w' = M.just (sat? isWord)
  escaped 'W' = M.just (sat? λ c → not (isWord c))
  escaped 's' = M.just (sat? isSpace)
  escaped 'S' = M.just (sat? λ c → not (isSpace c))
  escaped 'n' = M.just (notNullable , charr '\n')
  escaped 't' = M.just (notNullable , charr '\t')
  escaped c with elem c special
  ... | true = M.just (notNullable , charr c)
  ... | false = M.nothing

  namedClass : List AC.Char → M.Maybe (UChar → Bool)
  namedClass cs = firstMatchingClass
    where
    same : List AC.Char → List AC.Char → Bool
    same [] [] = true
    same (x ∷ xs) (y ∷ ys) = eq x y and same xs ys
    same _ _ = false

    try : AS.String → (UChar → Bool) → M.Maybe (UChar → Bool)
        → M.Maybe (UChar → Bool)
    try nm P alt with same cs (AS.primStringToList nm)
    ... | true = M.just P
    ... | false = alt

    firstMatchingClass : M.Maybe (UChar → Bool)
    firstMatchingClass =
      try "alpha" isAlpha (try "digit" isDigit (try "alnum" isAlnum
      (try "upper" isUpper (try "lower" isLower (try "space" isSpace
      (try "blank" isBlank (try "punct" isPunct (try "cntrl" isCntrl
      (try "print" isPrint (try "graph" isGraph
      (try "xdigit" isXDigit M.nothing)))))))))))

private
  -- `[:name:]` -- the leading `[` is already consumed
  posixName : Par (UChar → Bool)
  posixName (':' ∷ cs) = readName cs []
    where
    readName : Src → List AC.Char → M.Maybe ((UChar → Bool) × Src)
    readName [] acc = M.nothing
    readName (':' ∷ ']' ∷ rest) acc =
      namedClass acc >>=? λ P → M.just (P , rest)
    readName (c ∷ rest) acc = readName rest (acc ++ (c ∷ []))
  posixName _ = M.nothing

  items : ℕ → Par (List Item)
  items zero _ = M.nothing
  items (suc f) (']' ∷ cs) = M.just ([] , cs)
  items (suc f) ('[' ∷ cs) with posixName cs
  ... | M.just (P , rest) =
        items f rest >>=? λ r → M.just (classI P ∷ r .fst , r .snd)
  ... | M.nothing =
        items f cs >>=? λ r → M.just (chI '[' ∷ r .fst , r .snd)
  items (suc f) (lo ∷ '-' ∷ hi ∷ cs) with eq hi ']'
  ... | true = items f ('-' ∷ hi ∷ cs) >>=? λ r →
                 M.just (chI lo ∷ r .fst , r .snd)
  ... | false = items f cs >>=? λ r → M.just (rangeI lo hi ∷ r .fst , r .snd)
  items (suc f) (c ∷ cs) = items f cs >>=? λ r → M.just (chI c ∷ r .fst , r .snd)
  items (suc f) [] = M.nothing

  bracket : ℕ → Par RE?
  bracket f ('^' ∷ cs) =
    items f cs >>=? λ r → M.just ((notNullable , bracketNotr (r .fst)) , r .snd)
  bracket f cs =
    items f cs >>=? λ r → M.just ((notNullable , bracketr (r .fst)) , r .snd)

-- The grammar proper.  `alt ::= cat ('|' cat)*`, `cat ::= piece*`,
-- `piece ::= atom postfix*`.

private
  alt cat piece atom : ℕ → Par RE?

  alt zero _ = M.nothing
  alt (suc f) cs = cat f cs >>=? λ r → more f (r .fst) (r .snd)
    where
    more : ℕ → RE? → Par RE?
    more zero acc cs' = M.just (acc , cs')
    more (suc g) acc ('|' ∷ cs') =
      cat g cs' >>=? λ r → more g (acc ⊕? r .fst) (r .snd)
    more (suc g) acc cs' = M.just (acc , cs')

  cat zero _ = M.nothing
  cat (suc f) cs = concatPieces f ε? cs
    where
    concatPieces : ℕ → RE? → Par RE?
    concatPieces zero acc cs' = M.just (acc , cs')
    concatPieces (suc g) acc [] = M.just (acc , [])
    concatPieces (suc g) acc ('|' ∷ cs') = M.just (acc , '|' ∷ cs')
    concatPieces (suc g) acc (')' ∷ cs') = M.just (acc , ')' ∷ cs')
    concatPieces (suc g) acc cs' =
      piece g cs' >>=? λ r → concatPieces g (acc ⊗? r .fst) (r .snd)

  piece zero _ = M.nothing
  piece (suc f) cs = atom f cs >>=? λ r → post f (r .fst) (r .snd)
    where
    post : ℕ → RE? → Par RE?
    bound : ℕ → RE? → ℕ → Par RE?
    close : ℕ → RE? → ℕ → ℕ → Par RE?

    post zero acc cs' = M.just (acc , cs')
    post (suc g) acc ('*' ∷ cs') = star? acc >>=? λ r → post g r cs'
    post (suc g) acc ('+' ∷ cs') = plus? acc >>=? λ r → post g r cs'
    post (suc g) acc ('?' ∷ cs') = post g (opt? acc) cs'
    post (suc g) acc ('{' ∷ cs') =
      number cs' >>=? λ r → bound g acc (r .fst) (r .snd)
    post (suc g) acc cs' = M.just (acc , cs')

    -- `{n}` or `{n,m}`
    bound g acc n ('}' ∷ cs') = rep? n 0 acc >>=? λ r → post g r cs'
    bound g acc n (',' ∷ cs') =
      number cs' >>=? λ r → close g acc n (r .fst) (r .snd)
    bound _ _ _ _ = M.nothing

    close g acc n m ('}' ∷ cs') = rep? n (m ∸ n) acc >>=? λ r → post g r cs'
    close _ _ _ _ _ = M.nothing

  atom zero _ = M.nothing
  atom (suc f) ('(' ∷ cs) =
    alt f cs >>=? λ r → lit ')' (r .snd) >>=? λ q → M.just (r .fst , q .snd)
  atom (suc f) ('[' ∷ cs) = bracket f cs
  atom (suc f) ('.' ∷ cs) = M.just ((notNullable , dotr) , cs)
  atom (suc f) ('\\' ∷ c ∷ cs) = escaped c >>=? λ r → M.just (r , cs)
  atom (suc f) (c ∷ cs) with elem c special
  ... | true = M.nothing
  ... | false = M.just ((notNullable , charr c) , cs)
  atom (suc f) [] = M.nothing

parseRE : AS.String → M.Maybe RE?
parseRE s = parseAll (AS.primStringToList s)
  where
  parseAll : Src → M.Maybe RE?
  parseAll cs =
    alt (suc (suc (AN._*_ (length cs) 4))) cs >>=? λ r → done (r .snd) (r .fst)
    where
    done : Src → RE? → M.Maybe RE?
    done [] r = M.just r
    done (_ ∷ _) _ = M.nothing

IsJust : {ℓ : Level} {A : Type ℓ} → M.Maybe A → Type ℓ-zero
IsJust (M.just _) = Unit
IsJust M.nothing = Empty.⊥

-- `⟨| "[a-z]+" |⟩` -- a malformed pattern is a type error here, because
-- `IsJust nothing` is uninhabited and `Unit` is solved by eta.
⟨|_|⟩ : (s : AS.String) → {_ : IsJust (parseRE s)} → RE?
⟨|_|⟩ s {p} = get (parseRE s) p
  where
  get : (m : M.Maybe RE?) → IsJust m → RE?
  get (M.just r) _ = r

∥_∥ : (s : AS.String) → {_ : IsJust (parseRE s)} → Nullability
∥_∥ s {p} = ⟨|_|⟩ s {p} .fst

reOf : (s : AS.String) → {p : IsJust (parseRE s)} → RE (∥_∥ s {p})
reOf s {p} = ⟨|_|⟩ s {p} .snd
