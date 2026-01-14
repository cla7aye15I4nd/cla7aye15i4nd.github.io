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

After understanding its high level idea, let me use a example to show how Lean works. I want to use Lean to prove that $0 + n = n + 0$. We can first see how we proof it in math.

### Mathematical Proof

> [!NOTE] Peano Axioms (Addition Definition)
> $$
> \begin{align*}
> \text{1. }& a + 0 = a \\
> \text{2. }& a + \text{succ}(b) = \text{succ}(a + b)
> \end{align*}
> $$

We can use induction to prove this proposition. First, we need to prove the base case, which is when $n = 0$. In this case, we have $0 + 0 = 0 + 0$, which is true.

Next, we need to prove the inductive step, which is when $n = \text{succ}(k)$, where $\text{succ}(k)$ is the successor of $k$. In this case, we have:
$$
0 + \text{succ}(k) = \text{succ}(0 + k)
$$
By the inductive hypothesis, we have $0 + k = k + 0$, so we can substitute this into the equation:
$$
0 + \text{succ}(k) = \text{succ}(k + 0)
$$
Finally, we need to prove that $\text{succ}(k + 0) = \text{succ}(k)$, which is true by the definition of addition.  

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
    motive a → ∀ {a_1 : α} (t : a = a_1), motive a_1 t
```
The parameters are:
1. `α`: This is the type of the terms we are working with.
2. `a`: This is the source term.
3. `motive`: This is a function that takes a term `a_1` of type `α` and a proof that `a = a_1`, and returns a proposition.
4. `motive a`: This is a proof of the proposition for the source term `a`.
5. `∀ {a_1 : α} (t : a = a_1)`: This is a function that takes a target term `a_1` of type `α` and a proof that `a = a_1`, and returns a proof of the proposition for the target term `a_1`.
6. `motive a_1 t`: This is the conclusion of the induction, which is a proof of the proposition for the target term `a_1`.

