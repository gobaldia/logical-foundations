# Logical Foundations

## Basics

### Definición de tipos
Los tipos se definen como sigue:

#### Días de la semana
```coq
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
```

#### Booleanos
```coq
Inductive bool : Type :=
  | true : bool
  | false : bool.
```

#### Naturales
```coq
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
```

### Definición de funciones

#### Funciones no recursivas
Las funciones no recursivas se definen utilizando la palabra reservada `Definition`.

La siguiente función retorna el día siguiente al que se recibe por parámetro.

```coq
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
```

La negación, conjunción y disyunción booleana se definen como sigue:
```coq
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
```

```coq
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
```

```coq
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```

#### Funciones recursivas
Las funciones recursivas se definen utilizando la palabra reservada `Fixpoint`.

La siguiente funcion decide si un natural es par:
```coq
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
```

La suma, multiplicación y resta de naturales se podrían definir como sigue:
```coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
```

```coq
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.
```

```coq
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
```

### Pruebas por simplificación
A continuación se muestran ejemplos de pruebas por simplificación.

```coq
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
```

```coq
Theorem plus_1_l : ∀ n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
```

```coq
Theorem mult_0_l : ∀ n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
```

### Pruebas por rewriting
Para demostrar teoremas más complejos Coq provee la táctica `Rewrite`. Lo que hace es reemplazar el contenido de un _goal_ por una expresión equivalente que se encuentre en las _hipótesis_. En el ejemplo siguiente puede verse ésto:

```coq
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite → H.
  reflexivity. Qed.
```