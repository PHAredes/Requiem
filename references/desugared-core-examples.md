# Surface-Lowered Core Examples

## Nat

### Surface

```requiem
(data Nat: Type
  ((zero Nat)
   (succ (forall (n: Nat). Nat))))

(def sum: (forall (n: Nat). (forall (m: Nat). Nat))
  (match m:
    (case zero: n)
    (case (succ m'): (succ (sum n m')))))
```

### Lowered Core Shape

```lisp
(data (Ann Nat Type)
  ((zero Nat)
   (succ (Pi (Ann n Nat) Nat))))

(def (Ann sum (Pi (Ann n Nat) (Pi (Ann m Nat) Nat)))
  (Nat-elim
    (Lam (Ann _ Nat) Nat)
    n
    (Lam (Ann m' Nat) (Lam (Ann ih Nat)
      (succ ih)))
    m))
```

## Bool

### Surface

```requiem
(data Bool: Type
  ((true Bool)
   (false Bool)))

(def not: (forall (b: Bool). Bool)
  (match b:
    (case true: false)
    (case false: true)))
```

### Lowered Core Shape

```lisp
(data (Ann Bool Type)
  ((true Bool)
   (false Bool)))

(def (Ann not (Pi (Ann b Bool) Bool))
  (Lam (Ann b Bool)
    (Bool-elim
      (Lam (Ann _ Bool) Bool)
      false
      true
      b)))
```

## Note

These examples capture the intended eliminator-based encoding for pattern matching.
The current frontend still lowers `match` into clause forms, and elaboration consumes those clauses.
