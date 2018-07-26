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
```
Inductive bool : Type :=
  | true : bool
  | false : bool.
```

#### Naturales
```
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
```

### Definición de funciones

#### Funciones no recursivas
Las funciones no recursivas se definen utilizando la palabra reservada `Definition`.

La siguiente función retorna el día siguiente al que se recibe por parámetro.

```
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
```
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```

#### Funciones recursivas
Las funciones recursivas se definen utilizando la palabra reservada `Fixpoint`.

La siguiente funcion decide si un natural es par:
```
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
```