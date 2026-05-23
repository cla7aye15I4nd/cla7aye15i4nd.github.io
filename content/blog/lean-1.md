---
date: 2026-01-14
tags: [math, lean]
---

# Learn Lean (A Language for Mathematical Proofs) from a Programmer's Perspective


> [!NOTE] Why I learn Lean?
> Briefly, I have broad interest in many areas of mathematics and computer science. However, due to limited time and energy, I can only choose a few areas to focus on. I have taken too much time exploring computer science topics. Recently, I noticed that Terence Tao said that AI can help non-professionals do research in mathematics. This motivated me to learn Lean, which is a language for writing mathematical proofs that can be checked by a computer. It is also a cross between programming and mathematics, which should be a good starting point for me.

> [!IMPORTANT] Prerequisites
> I already have some knowledge of mathematics, such as basic [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms). I also very like Combinatorial Mathematics, which can motivated me to learn lean.

## High Level Overview

The overall idea of using a programming language to write mathematical proofs is based on type.
In OOP languages, you can define classes (different types) and corresponding instances, some language may have generic types, for example, in C++ you can define a template class. In math, we have proposition and corresponding proofs. In Lean, proposition is a type, and proof is an instance of that type. So in Lean, you can define a proposition as a type, and then write a proof as an instance of that type. 

However, a big differece between type system of Lean and other languages is that Lean has dependent types, which means that the type of a proposition can depend on the value of a term. For example, you can define a type `Vector n` which represents a vector of length `n`, where `n` is a natural number. This allows you to write more expressive propositions and proofs.

## Starting Lean

After understanding its high level idea, let me use a example to show how Lean works. I want to use Lean to prove that $0 + n = n$. We can first see how we proof it in math.

### Mathematical Proof

> [!NOTE] Peano Axioms (Addition Definition)
> $$
> \begin{align*}
> \text{1. }& a + 0 = a \\
> \text{2. }& a + \text{succ}(b) = \text{succ}(a + b)
> \end{align*}
> $$

We can use induction to prove this proposition. First, we need to prove the base case, which is when $n = 0$. In this case, we have $0 + 0 = 0$, which is true.

Next, we need to prove the inductive step, which is when $n = \text{succ}(k)$, where $\text{succ}(k)$ is the successor of $k$. In this case, we have:
$$
0 + \text{succ}(k) = \text{succ}(0 + k)
$$
By the inductive hypothesis, we have $0 + k = k$, so we can substitute this into the equation:
$$
0 + \text{succ}(k) = \text{succ}(k)
$$
Finally, we have proved that $0 + n = n$ for all natural numbers $n$.

## Raw Lean Code
```lean4
theorem zero_add_raw (n : Nat) : 0 + n = n :=
  @Nat.rec.{0}
    (fun (k : Nat) => 0 + k = k)              -- Motive P(k)
    (@Eq.refl.{1} Nat 0)                      -- Base case: P(0)
    (fun (m : Nat) (ih : 0 + m = m) =>        -- Inductive step: P(m) -> P(m+1)
      @Eq.rec.{0, 1}
        Nat
        (0 + m)                               -- Source 'a'
        (fun (x : Nat) (_ : 0 + m = x) =>     -- Motive for Eq.rec
          0 + @Nat.succ m = @Nat.succ x)
        (@Eq.refl.{1} Nat (0 + @Nat.succ m))       -- Starting term (Type matches Motive at 'a')
        m                                     -- Target 'b'
        ih                                    -- Proof of 'a = b'
    )
    n
```

I call it as raw lean code because real Lean user do not write such code like this. They will use more friendly syntax sugar provided by Lean, but I think this version can better show the underlying mechanism of Lean.

#### Axioms Used
Let's explain some key elements in this code:
- `Nat`: This is the type of natural numbers in Lean.
- `@Nat.rec.{0}`, `@Eq.refl.{1}`, and `@Eq.rec.{0, 1}`: These are some predefined functions. They are axioms in mathematics.
  - `Nat.rec` is the principle of [mathematical induction](https://en.wikipedia.org/wiki/Mathematical_induction) for natural numbers.
  - `Eq.refl` is the reflexivity of equality (ie. for any term `a`, `a = a`).
  - `Eq.rec` is the principle of substituting equals for equals (ie. if `a = b`, then we can replace `a` with `b` in any proposition).

#### Function Signatures

The type signature of `zero_add_raw` is:
```
    ∀ (n : Nat), 0 + n = n
```
Here is very hard to understand part if you are not familiar with dependent types. At here, we must notice that a type can contain logic. In common programming languages, a type is just a label for a set of values, for example, `Dict[int, str]` is a type for dictionaries with integer keys and string values. 

A signature of a function usually be like:
```
    (ReturnType) FunctionName(ParamType1 Param1, ParamType2 Param2, ...
``` 

It defines the input and output types of a function. However, in Lean, the type of a function can depend on the value of its parameters. 

To understand function in Lean, I prefer to take it in this way, `zero_add_raw` is not a function but just a elements with type: `∀ (n : Nat), 0 + n = n`, the code under the theorem is trying to construct an instance of this type from existing axioms.

### Constructing the Proof

#### Step 1: Nat.rec.{0}
Now, let's see the type of `Nat.rec.{0}` is:
```
∀ {motive : Nat → Prop}, motive Nat.zero → (∀ (n : Nat), motive n → motive n.succ) → ∀ (t : Nat), motive t
```
It have four parameters:
1. `motive`: This is a function that takes a natural number and returns a proposition.
2. `motive Nat.zero`: This is the base case of the induction, which is a proof of the proposition for `0`.
3. `∀ (n : Nat), motive n → motive n.succ`: This is the inductive step, which is a function that takes a natural number `n` and a proof of the proposition for `n`, and returns a proof of the proposition for `n.succ`.
4. `∀ (t : Nat), motive t`: This is the conclusion of the induction, which is a proof of the proposition for any natural number `t`.

We can understand the first and the last parameters first because they are most simple.

**For the first parameter**, we have:
```lean4
(fun (k : Nat) => 0 + k = k)
```
This is a function that takes a natural number `k` and returns the proposition `0 + k = k`. This is our motive for the induction.

**For the last parameter**, we have:
```lean4
n
```
This is the natural number `n` that we want to prove the proposition for.

#### Step 2: Base Case
Next, we can understand the second parameter, which is the base case of the induction. We have:
```lean4
(@Eq.refl.{1} Nat 0)
```
This is a proof of the proposition for `0`. The type of `Eq.refl.{1}` is:
```
∀ {α : Type u} (a : α), a = a
```
It takes a type `α` and a term `a` of type `α`, and returns a proof that `a = a`. In our case, we have `α` as `Nat` and `a` as `0`, so it returns a proof that `0 = 0`, which is our base case.

#### Step 3: Inductive Step
This is the most complex part. The type of the third parameter is:
```
∀ (n : Nat), motive n → motive n.succ
```
and the code is:
```lean4
(fun (m : Nat) (ih : 0 + m = m) =>        -- Inductive step: P(m) -> P(m+1)
    @Eq.rec.{0, 1}
        Nat
        (0 + m)                               -- Source 'a'
        (fun (x : Nat) (_ : 0 + m = x) =>     -- Motive for Eq.rec
            0 + @Nat.succ m = @Nat.succ x)
        (@Eq.refl.{1} Nat (0 + @Nat.succ m))       -- Starting term (Type matches Motive at 'a')
        m                                     -- Target 'b'
        ih                                    -- Proof of 'a = b'
)
```
We can find that it is a function that takes a natural number `m` and a proof `ih` of the proposition for `m`, and returns a proof of the proposition for `m.succ`. 

The type of `Eq.rec.{0, 1}` is:
```
∀ {α : Type} {a : α} {motive : (a_1 : α) → a = a_1 → Prop}, 
    motive a (Eq.refl a : a = a) → ∀ {a_1 : α} (t : a = a_1), motive a_1 t
```

It have 6 parameters, which is very crazy. Let's understand them by write this parts mathematically.

> Within the context of $~\mathbb{N} \rightarrow$ **Arg 1: Type**
> 
> Since I have a proof that $0 + \text{succ}(m) = \text{succ}(0 + m) \rightarrow$ **Arg 4: Base Evidence**
>
> And I know that $0 + m = m$ **Arg 6: Equality Proof**,
>
> I can use the template $0 + \text{succ}(m) = \text{succ}(x) \rightarrow$ **Arg 3: Motive**
>
> to swap $(0 + m) \rightarrow$ **Arg 2: Source**
> 
> inside my goal
> 
> with $m \rightarrow$ **Arg 5: Target**
> 
> to conclude that $0 + \text{succ}(m) = \text{succ}(m)$.

From above, we can understand why the simple step in original mathematical proof is so complex here. Now, we can check that what the each parameter is in our code:
1. `Nat`: This is the type of natural numbers in Lean. (Arg 1)
2. `0 + m`: This is the source term `a`. (Arg 2)
3. `(fun (x : Nat) (_ : 0 + m = x) => 0 + @Nat.succ m = @Nat.succ x)`: This is the motive for `Eq.rec`. (Arg 3)
4. `(@Eq.refl.{1} Nat (0 + @Nat.succ m))`: This is the starting term, which is a proof of the proposition for `0 + succ(m)`. (Arg 4)
5. `m`: This is the target term `b`. (Arg 5)
6. `ih`: This is the proof of `a = b`, which is `0 + m = m`. (Arg 6)

## Simplified Lean Code

If Lean ask user to write code in above section, the lean will be too complex to use. So Lean provide some syntax sugar to make it easier to write code. The simplified version of above code is:

### Universe Levels Omitted
 
In the original code, we use .{0} and .{1} to specify the universe levels of types. However, in most cases, Lean can infer the universe levels automatically, so we can omit them. The code becomes:

> [!NOTE] Universe Levels
> Here I introduce a concept called universe levels. If you do not want know what it is, you can assume it is something like template parameters in C++. If we use .{0}, it means we explicitly specify the type.


```lean4
theorem zero_add_v1 (n : Nat) : 0 + n = n :=
  @Nat.rec
    (fun (k : Nat) => 0 + k = k)              -- Motive P(k)
    (@Eq.refl Nat 0)                      -- Base case: P(0)
    (fun (m : Nat) (ih : 0 + m = m) =>        -- Inductive step: P(m) -> P(m+1)
      @Eq.rec
        Nat
        (0 + m)                               -- Source 'a'
        (fun (x : Nat) (_ : 0 + m = x) =>     -- Motive for Eq.rec
          0 + @Nat.succ m = @Nat.succ x)
        (@Eq.refl Nat (0 + @Nat.succ m))       -- Starting term (Type matches Motive at 'a')
        m                                     -- Target 'b'
        ih                                    -- Proof of 'a = b'
    )
    n
```

### Implicit Arguments
Recall the type signatures of `Nat.rec`, `Eq.refl`, and `Eq.rec`, we can find that they have some implicit arguments, for example, the signature of `Eq.refl` is:
```
∀ {α : Type u} (a : α), a = a
```
The implicit argument is `α`, which is wrapped in `{}`. Lean can infer the value of implicit arguments automatically, so we can omit them when calling the function. The `@` symbol is used to indicate that we are calling a function with implicit arguments. After removing the `@` symbols and use implicit arguments in the code.
```lean4

theorem zero_add_v2 (n : Nat) : 0 + n = n :=
  Nat.rec
    (Eq.refl 0)                               -- Base case: P(0)
    (fun (m : Nat) (ih : 0 + m = m) =>        -- Inductive step: P(m) -> P(m+1)
      Eq.rec
        (motive := fun (x : Nat) (_ : 0 + m = x) =>
          0 + Nat.succ m = Nat.succ x)
        (Eq.refl (0 + Nat.succ m))            -- Starting term
        ih                                    -- Proof of 'a = b'
    )
    n
```
We need add `motive :=` to specify the motive for `Nat.rec` and `Eq.rec`, because Lean cannot infer them automatically in this case.

### Definition Equality
We may find many steps in last version code is very very trivial, for example, the base case `0 + 0 = 0` is true by definition of addition. So Lean provide a sugar called `rfl`, which can prove any proposition that is true by definition. We can use `rfl` to replace some trivial steps in last version code. The final version code is:
```lean4
theorem zero_add_v3 (n : Nat) : 0 + n = n :=
  Nat.rec
    rfl
    (fun (m : Nat) (ih : 0 + m = m) =>        -- Inductive step: P(m) -> P(m+1)
      Eq.rec
        (motive := fun (x : Nat) (_ : 0 + m = x) =>
          0 + Nat.succ m = Nat.succ x)
        rfl
        ih                                    -- Proof of 'a = b'
    )
    n
```

### `congrArg` for `Eq.rec`
In last version code, we use `Eq.rec` to do substitution. However, Lean provide a more friendly function called `congrArg`, which can be used to prove that if `a = b`, then `f(a) = f(b)` for any function `f`. The use of `congrArg` will be like:
```lean4
congrArg f h
```
where `f` is a function and `h` is a proof of `a = b`. After using `congrArg`, the code becomes:
```lean4
theorem zero_add_v4 (n : Nat) : 0 + n = n :=
  Nat.rec
    rfl
    (fun (m : Nat) (ih : 0 + m = m) =>
      congrArg Nat.succ ih
    )
    n
```
or even shorter:
```lean4
theorem zero_add (n : Nat) : 0 + n = n :=
    Nat.rec
        rfl
        (fun _ ih => congrArg Nat.succ ih)
        n
```

### Pattern Matching for Recursion
Lean also provide pattern matching for recursion, which can make the code more readable. The code becomes:
```lean4
theorem zero_add_v5 : (n : Nat) → 0 + n = n
  | 0 => rfl
  | Nat.succ m => congrArg Nat.succ (zero_add_v5 m)
```
We should notice that in this version we use a recursive function to define the proof. We can not use original `(fun _ ih => congrArg Nat.succ ih)` style because we need to call the function itself in the inductive step, otherwise we can not caoture the inductive hypothesis (`ih`).

## Tactic Mode
Lean also provide a tactic mode. How to understand tactic mode? The original mode is called term mode, the code will be like real programming code. However, in tactic mode, we can write code like we do in mathematical proof, which is much friendlier for mathematicians.

If Term Mode is like writing a nested functional expression, Tactic Mode is like using an interactive debugger or a REPL. You see the state of your variables and your "Goal" (the type you are trying to inhabit) at every step.

### The "Mind Map" from Term to Tactic

When you move from Term Mode to Tactic Mode, your mental model shifts from Construction to Transformation:

| Concept | Term Mode (Construction) | Tactic Mode (Transformation) |
| :--- | :--- | :--- |
| **Induction** | `Nat.rec` or Pattern Matching | `induction n with d hd` |
| **Substitution** | `Eq.rec` or `congrArg` | `rw [hd]` (rewrite) |
| **Definition** | `rfl` | `simp` or `rfl` |
| **Function App** | `f x` | `apply f` |


### Final Tactic Code

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [add_succ]  -- 0 + succ(n) = succ(0 + n)
    rw [ih]        -- succ(0 + n) = succ(n)
```

I think most part of the code are meet intuition except the `rw`, I believe it is because of the `InfoView` panel is not here.

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
```

When you just have this part of code, the info view will show
```
n: Nat
ih: 0 + n = n
⊢ 0 + (n + 1) = n + 1
```
when you put the cursor on `rw [add_succ]`, it means you want to rewrite the goal using the theorem `add_succ`, which is replace `0 + succ(n)` with `succ(0 + n)`. After you apply this step, the info view will show
```
n : Nat
ih : 0 + n = n
⊢ (0 + n).succ = n + 1
```
Than when you put the cursor on `rw [ih]`, it means you want to rewrite the goal using the inductive hypothesis `ih`, which is replace `0 + n` with `n`. After you apply this step, the info view will show
```
n : Nat
ih : 0 + n = n
⊢ n.succ = n + 1
```
Now, the goal is true by definition of addition.

> [!WARNING]
> I have a little question here, why we do not use another rfl to finish the proof? I think it is because Lean can not infer that `n.succ = n + 1` by definition of addition here. 

For reference, I put the original mathematical proof here again, you will find the tactic code is very similar to it.

> [!NOTE]
> Next, we need to prove the inductive step, which is when $n = \text{succ}(k)$, where $\text{succ}(k)$ is the successor of $k$. In this case, we have:
> $$
> 0 + \text{succ}(k) = \text{succ}(0 + k)
> $$
> By the inductive hypothesis, we have $0 + k = k$, so we can substitute this into the equation:
> $$
> 0 + \text{succ}(k) = \text{succ}(k)
> $$
> Finally, we have proved that $0 + n = n$ for all natural numbers $n$.