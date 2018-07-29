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
  | S : nat -> nat.
```

### Definición de funciones

#### Funciones no recursivas
Las funciones no recursivas se definen utilizando la palabra reservada `Definition`.

La siguiente función retorna el día siguiente al que se recibe por parámetro.

```coq
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
```

La negación, conjunción y disyunción booleana se definen como sigue:
```coq
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
```

```coq
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
```

```coq
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
```

#### Funciones recursivas
Las funciones recursivas se definen utilizando la palabra reservada `Fixpoint`.

La siguiente funcion decide si un natural es par:
```coq
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
```

La suma, multiplicación y resta de naturales se podrían definir como sigue:
```coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
```

```coq
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
```

```coq
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
```

### Pruebas por simplificación
A continuación se muestran ejemplos de pruebas por simplificación.

```coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
```

```coq
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
```

```coq
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
```

### Pruebas por rewriting
Para demostrar teoremas más complejos Coq provee la táctica `rewrite`. Lo que hace es reemplazar el contenido de un _goal_ por una expresión equivalente que se encuentre en las _hipótesis_. En el ejemplo siguiente puede verse ésto:

```coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.
```

### Pruebas por casos
Cuando tenemos que hacer casos en las pruebas debemos utilizar la táctica `destruct`.

Por ejemplo, si quisiéramos probar que `1` es distinto de `0`, deberíamos hacer casos en `n`, contemplando cuando `n=0` y cuando `n=S n'`, tal cual se muestra en el siguiente fragmento de código.
```coq
Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.
```

## Induction
Coq provee la táctica `induction` para realizar demostraciones por inducción.

Para demostrar que `n = n+0` es necesario recurrir a inducción, tal como se muestra a continuación.

```coq
Theorem plus_n_O : ∀ n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
```

## Lists
Las listas se definen en Coq como un tipo inductivo, de forma similar a como se hace en Haskell. Es decir, una lista podría ser o bien la lista vacía o bien el par formado por un elemento y una lista.

El tipo particular lista de naturales se define como sigue:

```coq
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat → natlist → natlist.
```

Una lista se define, por ejemplo, como `Definition mylist := cons 1 (cons 2 (cons 3 nil)).`.

A continuación se definen, a modo de ejemplo, algunas de las funciones ya conocidas de otros cursos, como son `lenght`, `append`, `head` y `tail`.

```coq
Fixpoint length (l : natlist) : nat :=
	match l with
	| nil => 0
	| x :: xs => 1 + length (xs)
	end.
```

```coq
Fixpoint append (l1 l2 : natlist) : natlist :=
	match l1 with
	| nil => l2
	| x :: xs => x :: (append xs l2)
	end.
```

```coq
Fixpoint head (l : natlist) : nat :=
	match l with
	| nil => default
	| x :: xs => x
	end.
```

```coq
Fixpoint tail (l : natlist) : natlist :=
	match l with
	| nil => nil
	| x :: xs => xs
	end.
```

### Inducción en listas
El esquema de demostraciones por inducción sobre listas de naturales es el siguiente:

1) Demostramos el caso base, es decir la validez de la proposición para la lista vacía (`nil`).
2) Suponiendo cierta la proposición para una lista `l`, demostramos su validez cuando `l` es `cons n l'`.

### Options
Para evitar devolver valores por defecto cuando la función que implementamos no tiene qué devolver, podemos utilizar los `options`.

Siguiendo este enfoque podemos definir el tipo `natoption`, tal como se puede ver a continuación.

```coq
Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.
```

Si ahora quisiéramos implementar una función que devuelva el enésimo elemento de una lista, deberíamos hacer algo así:
```coq
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' ⇒ match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.
```

## Poly

### Listas polimórficas

En el capítulo [Lists](#lists) se mostró cómo crear listas de un tipo específico (el ejemplo concreto fue de naturales). Por lo general, nos va a interesar poder definir listas "genéricas", es decir listas que puedan ser de cualquier tipo. Es aquí que entra en juego el tema del polimorfismo. El tipo lista polimórfica se define como sigue:

```coq
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
```

Podemos ver a `list` como una _función_ que va de `Type` en `Type`. Para algún tipo `X`, el tipo `list X` es un conjunto inductivamente definido de listas cuyos elementos son de tipo `X`.

El parámetro `X` funciona como un parámetro de los constructores `nil` y `cons`, es decir `nil` y `cons` son constructores polimórficos. A modo de ejemplo, `nil nat` va a construir una lista de naturales vacía. Por su parte, si tipeamos `cons nat 3 (nil nat)` obtendremos una lista de naturales que solamente contendrá al elemento `3`.

Las funciones definidas anteriormente para listas de naturales (`lenght`, `append`, `head` y `tail`) pueden ser definidas para listas polimórficas como sigue:

```coq
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
```

```coq
Fixpoint append {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (append xs l2)
  end.
```

```coq
Fixpoint head {X : Type} (l : list X) : X :=
  match l with
  | nil => default
  | cons x xs => x
  end.
```

```coq
Fixpoint tail {X : Type} (l : list X) : (list X) :=
  match l with
  | nil => nil
  | cons x xs => cons xs
  end.
```

### Options polimórficos
El `option` polimórfico se define como sigue:

```coq
Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.
```

### Funciones como datos
#### Funciones de orden superior
Son funciones que pueden recibir o devolver funciones.

Un ejemplo de función de orden superior es `filter`, debido a que recibe como parámetro una función (el _predicado_ para el cual deben valer los valores que se retornan). La forma de definirla en Coq es la siguiente:

```coq
Fixpoint filter {X:Type} (test: X→bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.
```

#### Funciones anónimas
Las funciones anónimas son aquellas que no reciben un nombre, es decir que se definen dentro de una función y viven dentro de dicha función. Un ejemplo podría ser si queremos _filtrar_ todos las sublistas de largo 1, sin necesidad de definir la función `lenght_1`. En ese caso, nos quedaría algo así:

```coq
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
```

Por su parte, la siguiente función retorna una función. Lo que hace es recibir un valor `x` y retornar una función que devuelve ese valor `x`.

```coq
Definition constfun {X: Type} (x: X) : nat→X :=
  fun (k:nat) => x.
```

## Tactics

### Apply
La táctica `apply` se usa en casos donde el _goal_ a ser demostrado es exactamente igual a algunas de las hipótesis del contexto o a algo ya demostrado. Lo que se hace con `apply` se podría también hacer con `rewrite`.

### Apply ... With ...
La táctica `apply ... with ...` es una variación de `apply` que implica un cambio de variable.

### Inversion
Para aprovechar el hecho de que los constructores de un tipo inductivo son _inyectivos_ y disjuntos entre sí, Coq provee la táctica `inversion`. Si `H` es una hipótesis, al escribir `inversion H` Coq va a generar todas las ecuaciones que pueda inferir de `H` como hipótesis adicionales, reemplazado las variables en el _goal_ a medida que avanza.

Un ejemplo de uso de _inversion_ es el siguiente:
```coq
Theorem S_injective : ∀ (n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.
```