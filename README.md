
# **System‑F‑Ω (F Omega) Type Checker**
*A higher‑kinded polymorphic type checker with traits, variants, and recursive types*

---

## 🧩 Overview

**System‑F‑Ω** (pronounced *F‑Omega*) is an experimental **type inference and checking engine** that implements higher‑kinded polymorphism, trait constraints, recursive algebraic types, and structural typing — designed for advanced research, interpreters, and language runtime experiments.

It extends **System F** (the polymorphic lambda calculus) with:
- Type abstractions and applications (`Λα::* . e`, `e [τ]`)
- Higher‑kinded types (λ‑types)
- Type‑level functions and application
- First‑class record, variant, and tuple types
- Recursive types (`μt. τ`)
- Trait constraints and dictionary passing (Haskell‑style typeclasses)
- Kind inference and unification
- Nominal *and* structural type reasoning

The implementation is written in **TypeScript**, fully strongly typed, and modular — each feature neatly isolated in `./src/typechecker.ts`.


## 📖 Glossary

Before diving into the examples, here are a few key terms you’ll encounter when working with the `system‑f‑omega` type checker.

They come from the theory of typed λ‑calculi, but you don’t need an academic background to follow them.

| Concept | Description |
|:--|:--|
| **Lambda (λ)** | A notation for **functions**. In code, `λx:Int. x + 1` means “a function that takes `x` of type `Int` and returns `x + 1`.” The library constructs them with `lamTerm(argName, argType, body)`. |
| **Type Lambda (Λ)** | A function **over types**, not values. For example `Λa::* . λx:a. x` defines a function that works for *any* type `a`. Created using `tylamTerm()`. |
| **Application** | Applying a function to an argument. At the term level: `(f x)` applies `f` to `x`. At the type level: `(F Int)` applies a type constructor `F` to a type. Represented by `appTerm` or `appType`. |
| **Polymorphism** | The ability for functions or types to work *generically* over many types. In System‑F this is expressed with universal quantification `∀a::* . …` implemented via type lambdas and applications. Example: the polymorphic identity function `Λa. λx:a. x`. |
| **Kinds** | The “types of types.” Just as values have types, types themselves have *kinds*. The base kind `*` (pronounced “star”) means “a concrete type.” A higher‑kind, like `* → *`, means “a type that takes one type argument.” |
| **Higher‑Kinded Type** | A type operator that consumes or produces other types. Example: `λt::* . t → t` has kind `* → *`. These let you define structures like `Option`, `List`, or `Functor`. |
| **Normalization** | The process of simplifying or evaluating type‑level expressions until they are in canonical form. For instance, normalizing `(λt. t → t) Int` yields `Int → Int`. The function `normalizeType()` performs this step internally. |
| **Instantiation** | Substituting a specific type for a type variable when applying a polymorphic function. Example: applying `Λa. a → a` to `Int` gives `Int → Int`. Implemented with `tyapp_term` and supported by `instantiate()`. |
| **Recursive Type (μ)** | A type defined in terms of itself, such as lists or trees. Written `μList.<Nil:(), Cons:(Int, List)>`, created with `muType()`. These model self‑referential data structures. |
| **Trait / Typeclass** | A constraint that associates a type with a collection of required methods. Similar to interfaces or Haskell’s typeclasses, defined with `trait_def` and implemented via *dictionaries* of method terms. |
| **Subtyping** | A relation where one type can safely stand in for another (e.g., bottom type `⊥` is a subtype of any type). The checker uses `subsumes()` and `unifyTypes()` to reason about subtype relations. |
| **Context (Γ)** | The current *environment* of assumptions during type checking — it contains variable bindings (`x : τ`), type declarations, trait definitions, and enum definitions. In your code this is the `Context` type. |
| **Constraint** | A condition the checker generates that must hold for typing to succeed (for example, two types must unify, or a type must have kind `*`). The solver eventually resolves or reports unsatisfied constraints. |
| **Substitution** | A mapping from type variables to concrete types, used to gradually refine unknowns during unification (`?0 ↦ Int`). Represented by `Map<string, Type>` in your code. |
| **Meta‑Variable (MetaVar)** | A temporary placeholder type variable (like `?0`, `?1`) created during inference to stand in for an unknown type until constraints solve it. Introduced with `freshMetaVar()`. |
| **Unification** | The algorithmic process of finding a substitution that makes two types structurally equal. If unification succeeds, the types are considered compatible; otherwise it raises a `TypingError`. Implemented in `unifyTypes()`. |
| **Occurs Check** | A safeguard inside unification that prevents defining a variable in terms of itself (e.g., `a = a → a` would be infinite). Your typechecker implements this in `occursCheck()`. |
| **Bottom Type (⊥ / never)** | A type that represents “no value can exist.” It is a subtype of all types. In your code this is `{ never: null }`. |
| **Normalization (revisited)** | Specifically, *type‑level β‑reduction*, meaning that when a type function (λ‑type) is applied to an argument, its body is simplified by substituting the argument in place of the parameter. |

---

## 🥸 Created and Vibe Coded by A.I. using Claude

A very large portion of this type checker implementation was "vibe coded" by
Claude along with tests. That means there might be bugs! That's why there's over
5000 lines of code for tests in the `./test/` folder. Please feel free to
file issues with the type checker to help make this software more usable for
everyone.

Additionally, a majority of the documentation was A.I. generated by ChatGPT and
any help improving the examples or docs would be greatly appreciated! 

---

## ⚙️ Project Structure

```
system-f-omega/
│
├── src/
│   ├── eval.ts            # Functions to evaluate and interpret terms
│   ├── index.ts           # Entry point / simple REPL integration
│   ├── typechecker.ts     # Core type inference & checking logic
│   └── types.ts           # AST and type system definitions
│
├── examples/
│   ├── polymorphic.ts     # Λ-expressions and forall examples
│   ├── traits.ts          # Trait (typeclass) and dict usage
│   ├── enums.ts           # ADTs and pattern matching
│   ├── recursion.ts       # μ-types and fold/unfold usage
│   └── tuples.ts          # Heterogeneous tuples
│
├── biome.json
├── bunfig.toml
├── package.json
├── README.md
└── tsconfig.md
```

---

## 🧰 Installation

You can use it as a library or (in the future) as a command-line repl tool.

Please note that there is no CLI actually implemented yet, so it's largely
not functional yet.

### Clone and build

```bash
git clone https://github.com/yourname/system-f-omega.git
cd system-f-omega
bun install
bun run build
```

### Run the REPL or examples

This is not working yet, but it will be implemented at some point.

```bash
# after installation
bunx system-f-omega 
# or
bun repl
```

---

## ✍️ **Examples and Guided Walkthrough**

This section provides hands‑on examples that demonstrate how to experiment with the  
`system‑f‑omega` type checker using the exported term and type constructors.

Each example builds intuition for a different part of the System F‑Ω language:  
polymorphism, kinds, algebraic data types, recursion, and traits.

You can run any example from a Node/TypeScript environment just by copy‑pasting it into a script and calling `inferType()` at the end.

---

### Simple Function — The Polymorphic **Identity**

In System F, the fundamental building block is *parametric polymorphism*:  
a single function that works uniformly for any type.

Here we define the **identity function**, parameterised over the type variable `a`.

```ts
const id = tylamTerm("a", starKind,          // Λa::* .
  lamTerm("x", varType("a"),                 // λx:a.
    varTerm("x")                             //   x
  )
);
```

This creates a **type lambda** followed by a **term lambda**:

- First, at the **type level**, we abstract over a type parameter `a` of kind `*`.
- Then, at the **term level**, we take a value `x` of type `a` and return it unchanged.

**Inferred type:**

```
Λa::* . (a → a)
```

That is, a function polymorphic in `a`.

If we now *instantiate* the polymorphic type by applying it to a concrete type (e.g. `Int`), we obtain:

```ts
inferType([], tyapp_term(id, conType("Int")));
// ⇒ Int → Int
```

The same term now represents the *identity function specialized to integers*.

---

### Higher‑Kinded Example — Type Operators and **Functor Shapes**

System F‑Ω generalizes polymorphism by allowing **types that take types as arguments**.  
These are higher‑kinded type functions.

Below, we define a simple λ‑abstraction at the type level:

```ts
// λt::* . (t → t)
const functorLike = lamType("t", starKind,
  arrowType(varType("t"), varType("t"))
);
```

This type operator maps any concrete type `t` to the function type `t → t`.

```ts
showType(functorLike);
// ⇒ λt::* . (t → t)
```

When we **apply** it to a specific argument at the kind `*`, normalization substitutes and reduces:

```ts
normalizeType(appType(functorLike, conType("Int")));
// ⇒ Int → Int
```

This example illustrates how F‑Omega can model *generic type constructors* such as `Functor`, `Option`, or parametric functions — all of which are *functions at the type level.*

---

### Algebraic Data Types — Defining an **Enum**

A key extension supported by the checker is **nominal variants** (like Haskell or ML enums).  
Let’s describe an `Option<a>` type, which can either hold a value (`Some a`) or nothing (`None`):

```ts
const OptionEnum = {
  enum: {
    name: "Option",
    kind: arrow_kind(starKind, starKind),  // * → *
    params: ["a"],
    variants: [
      ["Some", varType("a")],
      ["None", unitType],
    ],
  },
};
```

When you add this definition to your context, the type checker can reason about values of that enum:

```ts
const some42 = injectTerm(
  "Some",
  conTerm("42", conType("Int")),
  appType(conType("Option"), conType("Int"))
);
```

Here, `<Some = 42> as Option<Int>` constructs a variant carrying an integer.

**Typing judgment:**

```
Γ ⊢ <Some = 42> as Option<Int> : Option<Int>
```

Later, pattern‑matching expressions (`matchTerm`) will use the same variant information for exhaustiveness checking.

---

### Recursive Algebraic Data Types — Building a **List<Int>**

Recursive types (`μ‑types`) allow defining self‑referential structures such as linked lists.

```ts
const ListType = muType("List",
  variantType([
    ["Nil", unitType],
    ["Cons", tupleType([conType("Int"), varType("List")])],
  ]),
);
```

This means  
`μList.< Nil: (), Cons: (Int, List) >`

Each value of type `List` is either an empty list or a pair of an integer and another list.

Creating the base case (`Nil`) and folding it into the recursive type:

```ts
foldTerm(ListType, injectTerm("Nil", unitValue, ListType));
```

This *folds* a concrete structure into its recursive wrapper, producing a well‑typed `List<Int>` value.

Normalizing produces:

```
μList.<Nil: (), Cons: (Int, List)>
```

From here you can construct non‑empty lists, unfold them, and perform recursive pattern matches.

---

### Trait Example — Implementing **Eq**

Typeclasses (called *traits* here) describe behavior shared across types.  
They operate much like Haskell’s `Eq`, `Show`, or `Ord`.

Let’s define a minimal `Eq` trait, representing equality testing.

```ts
const EqTrait = {
  trait_def: {
    name: "Eq",
    type_param: "Self",
    kind: arrow_kind(starKind, starKind),           // * → *
    methods: [
      ["eq", arrowType(varType("Self"),
               arrowType(varType("Self"), conType("Bool")))],
    ],
  },
};
```

This defines a generic interface requiring an `eq` method.

Now we supply a **dictionary implementation** for integers:

```ts
const EqIntDict = dictTerm("Eq", conType("Int"), [
  ["eq", lamTerm("x", conType("Int"),
    lamTerm("y", conType("Int"), conTerm("true", conType("Bool"))),
  )],
]);
```

Finally, we register both the trait and its integer instance in the typing context:

```ts
const ctx: Context = [
  { trait_def: EqTrait.trait_def },
  { trait_impl: { trait: "Eq", type: conType("Int"), dict: EqIntDict } },
];
```

Verifying that this instance satisfies the trait:

```ts
checkTraitImplementation(ctx, "Eq", conType("Int"));
// ✅ OK
```

Now any function constrained by `Eq<Int>` can retrieve the corresponding dictionary automatically.

---

## 🧩 **Core API Reference**

| Function | Description |
|:--|:--|
| `inferType(ctx, term)` | Infers the type of a term given a context |
| `checkType(ctx, term, expectedType)` | Bidirectional checking against an expected type |
| `normalizeType(type)` | Normalizes λ/applications and expands type aliases |
| `instantiate(type)` | Instantiates `∀` polymorphic type variables |
| `checkTraitImplementation(ctx, trait, type)` | Resolves trait dictionary for a concrete type |
| `unifyTypes(t1, t2)` | Attempts unification, returning constraints |
| `subsumes(ctx, general, specific)` | Subtyping and bottom‑type checks |
| `showType(type)` | Displays a type in human‑readable format |
| `checkKind(ctx, type)` | Infers or validates the kind of a type |
| `patternBindings(p)` | Extracts variable bindings from patterns |
| `checkExhaustive(patterns, type, ctx)` | Ensures match patterns cover all cases |

These functions form the backbone of the `system-f-omega` type checker.  
Each utility corresponds to a distinct part of the formal typing or kinding rules in the underlying calculus.

---

### **`inferType(ctx, term): Result<TypingError, Type>`**

Infers (synthesizes) the type of a term from the context.  
It is the core *type inference judgment* \(Γ ⊢ e : τ\).

- **Arguments:**
  - `ctx`: the typing context, including bound variables, trait definitions, and enum declarations.
  - `term`: an abstract syntax tree (AST) representing a System‑FΩ expression.

- **Returns:** The inferred type of the term, or a `TypingError` if type checking fails.

- **Usage:**
```ts
inferType(ctx, lamTerm("x", conType("Int"), varTerm("x")));
// => ok({ arrow: { from: Int, to: Int } })
```

---

### **`checkType(ctx, term, expectedType): Result<TypingError, { type: Type; subst: Substitution }>`**

Performs *bidirectional* type checking, verifying that a given term has an expected type.

This is the complementary relation \(Γ ⊢ e ⇐ τ\), used when the expected type is known — for instance, in function arguments or annotated lambdas.

- **Automatically handles** subtyping, polymorphic instantiation (`∀` and bounded `∀`), trait constraints, and structural matches on records or variants.
- **Used internally** by `inferTypeWithMode`, applications, and polymorphic functions.

- **Usage:**
```ts
checkType(ctx, lamTerm("x", conType("Int"), varTerm("x")), arrowType(conType("Int"), conType("Int")));
// => ok({ type: (Int → Int), subst: Map(…) })
```

---

### **`normalizeType(type, ctx?): Type`**

Performs **type‑level β‑reduction** and **normalization**, simplifying type expressions by expanding:
- Type‑level applications (`(λt. t → t) Int → Int → Int`)
- Recursive types (`μList. …`)
- Enum (nominal) definitions into structural variants.

It ensures all types are in *normal form* for unification and equality checks.

- **Example:**
```ts
normalizeType(appType(lamType("t", starKind, arrowType(varType("t"), varType("t"))), conType("Int")));
// => (Int → Int)
```

---

### **`instantiate(type, fresh?): Type`**

Removes outer `∀`‑quantifiers by replacing bound variables with **fresh meta‑type variables** (`?N`).  
This transforms polymorphic types into monomorphic *instances* ready for checking or unification.

- **Example:**
```ts
instantiate(forallType("a", starKind, arrowType(varType("a"), varType("a"))));
// => (?0 → ?0)
```

- Useful when applying polymorphic functions to concrete arguments.

---

### **`checkTraitImplementation(ctx, trait, type): Result<TypingError, Term>`**

Finds or constructs a **dictionary term** that provides evidence for a given trait constraint.  
Implements logic similar to Haskell’s instance resolution.

- Checks the context for existing `trait_impl` bindings or polymorphic trait definitions.
- Normalizes and instantiates candidate implementations.
- Unifies `instance type` with the target `type`.

- **Example:**
```ts
checkTraitImplementation(ctx, "Eq", conType("Int"));
// => ok(dictTerm("Eq", Int, …))
```

---

### **`unifyTypes(left, right, worklist, subst, ctx?): Result<TypingError, null>`**

Attempts to unify two types, producing assignments for meta‑variables and generating constraint equations.

- Supports structural unification for functions, tuples, records, variants, and recursive types.
- Treats the bottom type (`⊥`) as a universal subtype.
- Returns errors for mismatched kinds or incompatible structures.

- **Example:**
```ts
const subst = new Map<string, Type>();
unifyTypes(varType("?0"), conType("Int"), [], subst);
// subst => Map("?0" → Int)
```

---

### **`subsumes(ctx, general, specific, worklist, subst): Result<TypingError, null>`**

Performs **subtyping** and **type containment** checking — ensuring that a more specific type can be assigned where a general type is expected.

- Handles:
  - Bottom subtype rule (⊥ <: τ)
  - Forall instantiation (∀α. τ <: σ)
  - Structural subsumption (width subtyping for records and variants)

- **Example:**
```ts
subsumes(ctx, arrowType(conType("Int"), conType("Bool")), arrowType(neverType, conType("Bool")), [], new Map());
// ok(null) since ⊥ <: Int
```

---

### **`showType(type): string`**

Pretty‑prints a type in readable mathematical notation.

Used for:
- Error messages,
- REPL output,
- Logging or debugging type inference results.

Supports all System‑FΩ constructs (`∀`, `λ`, `μ`, records, variants, traits, etc.).

- **Example:**
```ts
showType(forallType("a", starKind, arrowType(varType("a"), varType("a"))));
// => "∀a::*.(a → a)"
```

---

### **`checkKind(ctx, type): Result<TypingError, Kind>`**

Infers or validates the **kind** of a type (the “type of types”).

Kinds ensure that type operators are used correctly — for instance `Option` has kind `* → *`, while `Int` has kind `*`.

- **Example:**
```ts
checkKind(ctx, lamType("t", starKind, arrowType(varType("t"), varType("t"))));
// => ok({ arrow: { from: *, to: * } })
```

---

### **`patternBindings(pattern): [string, Type][]`**

Extracts variable bindings introduced by a pattern (from `match` or `let` constructs).  
The returned bindings form a partial context extension for pattern bodies.

- **Example:**
```ts
patternBindings(
  recordPattern([["x", varPattern("y")], ["z", wildcardPattern()]])
);
// => [["y", { var: "$unknown" }]]
```

---

### **`checkExhaustive(patterns, type, ctx): Result<TypingError, null>`**

Ensures that a set of pattern clauses cover **all possible cases** for a given variant or enum type.

- Detects missing or extra cases.
- Handles both nominal (`enum`) and structural (`variant`) types.
- Returns a `TypingError` with `missing_case` if a label is not covered.

- **Example:**
```ts
checkExhaustive(
  [variantPattern("Some", varPattern("x"))],
  appType(conType("Option"), conType("Int")),
  ctx
);
// => err({ missing_case: { label: "None" } })
```

---

These functions represent the **public API surface** of **System‑F‑Ω**:  
They let you build, analyze, and type‑check complex programs embedded within the calculus — from basic function types to full trait‑constrained polymorphism.

**Typical workflow:**
1. Build term ASTs using constructors (`lamTerm`, `tylamTerm`, `injectTerm`, etc.).
2. Call `inferType()` to infer or `checkType()` to check.
3. Use `normalizeType()` and `showType()` for final, readable results.
4. Inspect `TypingError` results for diagnostics.

---

## 📖 Theoretical Background

System‑F‑Ω extends System‑F with **higher kinds (kind polymorphism)** and **type‑level computation**:

- Types are first‑class entities.
- Type operators (λ, app) allow constructing functions over types.
- Recursive types `μt. τ` enable modeling ADTs.
- Trait bounds capture interface‑like constraints akin to Haskell’s `typeclass` dictionaries.
- The normalization rules collapse β‑redexes at both term and type levels.

### Kind Inference Rules

```
Γ ⊢ τ : *
Γ ⊢ σ : * → *
───────────────────────────────
Γ ⊢ σ τ : *
```

### Type Inference Rule Example

(Lambda)
```
Γ, x:τ₁ ⊢ e : τ₂
─────────────────────────────
Γ ⊢ (λx:τ₁.e) : τ₁ → τ₂
```

(Type Abstraction)
```
Γ, α::κ ⊢ e : τ
─────────────────────────────
Γ ⊢ Λα::κ.e : ∀α::κ. τ
```

---

## 🧗 Goals & Future Work

✅ Current features

- System‑F core  
- Type and term abstraction/application  
- Higher‑kinded kinds and unification  
- Records, variants, tuples, recursive algebraic types  
- Trait / typeclass constraint solving  
- Kind inference and constraint solver 
- Basic Type printing and formatting
- Compilation to WasmGC from Zig or Grain (1.0 milestone)

🚧 Planned & Ongoing Improvements

- 🧩 Generalized type inference (HM(X)-style) → existing bidirectional inference extended with let-generalization
- ⚙️ Type-level evaluation optimization → caching / partial eval in normalizeType
- 🧠 Meta-variable generalization → promote solved metas at let-bindings
- 💬 Interactive REPL integration → use existing show* functions dynamically in CLI
- 🧱 Coercion derivation → explicit coercions for structural subtyping

---

## 🧪 Typical Development Loop

1. Define context bindings (traits, enums, or base types).
2. Build your term AST via constructors (`lamTerm`, `appTerm`, etc.).
3. Run `inferType(context, term)` or `checkType(...)`.
4. Inspect normalized type with `showType(type)`.
5. Add new type constructors to extend System‑F‑Ω.

---

## 🧾 License

MIT © 2025 — Developed by Josh  
Use freely for research, teaching, and experimental compilers.
