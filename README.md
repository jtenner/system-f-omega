# **System-F-Ω Type Checker**
*A higher-kinded polymorphic type system with traits, variants, and recursive types*

**System-F-Ω** is an experimental, strongly typed type inference and checking engine for exploring advanced type systems. It brings together concepts from functional programming, type theory, and compiler design into a single, extensible library.

Whether you're a type theory enthusiast implementing λ-calculi, a compiler developer exploring polymorphism and traits, or a beginner curious about how type inference works behind the scenes, this project provides both the theory and practical code to experiment with.

## 🎯 **What is System-F-Ω?**

System-F-Ω extends the classic **System-F** (polymorphic λ-calculus) with:

- **Higher-kinded types** (types that take types as arguments, like `List<t>` or `Option<a, b>`)
- **Traits/Typeclasses** (interfaces with dictionary-passing resolution, similar to Haskell)
- **Algebraic data types** (enums/variants with nominal + structural support)
- **Recursive types** (`μ`-types for lists, trees, etc.)
- **Structural typing** (record/tuple patterns with width subsumption)
- **Bidirectional type checking** (combines inference and checking for robust results)

The system uses a **stateful context** (`TypeCheckerState`) for all operations, managing environments, meta-variables, and solutions. This makes it suitable for building full compilers or just experimenting with type system ideas.

### 🎓 **Key Concepts (Beginner-Friendly)**

If you're new to advanced type systems, here's a quick glossary:

| Term | What It Means | Example |
|------|---------------|---------|
| **Kind** | The "type of a type" | `*` (concrete type) or `* → *` (type constructor like `List`) |
| **Polymorphism** | One function works for *any* type | `λx:a. x` has type `∀a. a → a` |
| **Type Lambda (Λ)** | A function *over types* | `Λα::*. α → α` (works for any type `α`) |
| **Higher-Kinded** | Types that take other types | `List` has kind `* → *` (takes one type parameter) |
| **Trait** | An interface defining methods | `Eq<Self>` requires `fn eq(self, other: Self) -> Bool` |
| **Dictionary** | "Proof" that a type implements a trait | A record of method implementations |
| **Unification** | Making two types "match" by solving unknowns | `?0 = Int`, so `?0 → Bool = Int → Bool` |
| **Normalization** | Simplifying complex types | `(λt.t→t) Int` → `Int → Int` |
| **Recursive Type** | A type defined in terms of itself | `μList. <Nil:() \| Cons:(Int, List)>` |

## 🛠️ **Installation**

```bash
# Clone and install
git clone https://github.com/yourusername/system-f-omega.git
cd system-f-omega
bun install  # or npm install

# Build
bun run build
```

**Usage**: This is a library, not a CLI. Import functions into your TypeScript/JavaScript project:

```ts
// Using Bun or ES modules
import { inferType, TypeCheckerState, showType } from "./src/typechecker.js";
```

## 🚀 **Quick Start**

### **1. Create a Context**

All type checking happens in a `TypeCheckerState`, which holds your bindings (variables, types, traits) and inference state:

```ts
import { 
  state, 
  termBinding, 
  conType, 
  arrowType, 
  TypeCheckerState,
  showContext 
} from "./src/typechecker.js";

// Basic context: bind "x" to type "Int -> Int"
const ctx: TypeCheckerState = state([
  termBinding("id", arrowType(conType("Int"), conType("Int")))
]);

console.log(showContext(ctx.ctx));
/* Output:
Term: id = (Int → Int)
*/
```

### **2. Build Terms (AST)**

Terms are constructed using *constructors* that mirror the syntax tree:

```ts
import { 
  lamTerm, 
  varTerm, 
  appTerm,
  inferType,
  showType
} from "./src/typechecker.js";

// λx:Int. x + 1 (simplified)
const identity = lamTerm("x", conType("Int"), 
  varTerm("x")
);

const app = appTerm(varTerm("id"), identity);

// Type check!
const result = inferType(ctx, identity);
console.log(showType(result.ok)); 
// Output: (Int → Int)
```

### **3. Inference & Checking**

- **Infer** the type of a term: `inferType(state, term)`
- **Check** against an expected type: `checkType(state, term, expectedType)`
- **Normalize** complex types: `normalizeType(state, type)`

```ts
// Check if our identity has the right type
const checkResult = checkType(ctx, identity, arrowType(conType("Int"), conType("Int")));
if ("ok" in checkResult) {
  console.log("✓ Type checks:", showType(checkResult.ok.type));
}
```

### **4. Pretty Printing**

```ts
import { showType, showTerm, showContext } from "./src/typechecker.js";

console.log(showTerm(identity)); 
// λx:Int.x

console.log(showType(result.ok)); 
// (Int → Int)

console.log(showContext(ctx.ctx)); 
// Term: id = (Int → Int)
```

## 📚 **Core Examples**

These show progressive complexity, from basic functions to full polymorphic traits.

### **Example 1: Polymorphic Identity (System-F Basics)**

The classic polymorphic identity function `id` works for *any* type:

```ts
import { tylamTerm, lamTerm, varTerm, varType, forallType, starKind, arrowType } from "./src/typechecker.js";

const idPoly = tylamTerm("a", starKind,           // Λa::*
  lamTerm("x", varType("a"),                      // λx:a.
    varTerm("x")                                  //   x
  )
);

// Inferred type: ∀a::*. (a → a)
console.log("Identity type:", showType(inferType(state(), idPoly).ok));

// Apply to concrete type: id [Int]
const idInt = tyappTerm(idPoly, conType("Int"));
console.log("Specialized:", showType(inferType(state(), idInt).ok)); 
// (Int → Int)
```

### **Example 2: Higher-Kinded Types (Type Operators)**

Define a type constructor `Box` that wraps any type:

```ts
import { lamType, appType, normalizeType } from "./src/typechecker.js";

const Box = lamType("t", starKind,                 // λt::*. 
  recordType([["value", varType("t")]])            // { value: t }

);

// Box<Int> normalizes to { value: Int }
const boxedInt = normalizeType(state(), appType(Box, conType("Int")));
console.log("Boxed Int:", showType(boxedInt));
```

### **Example 3: Enums & Pattern Matching**

Define a nominal enum `Result` and pattern match on it:

```ts
import { 
  enumDefBinding, 
  appType, 
  injectTerm, 
  conTerm,
  matchTerm,
  varPattern,
  wildcardPattern,
  inferType,
  showType 
} from "./src/typechecker.js";

const resultEnum = enumDefBinding("Result", { arrow: { from: starKind, to: starKind } }, ["E"], [
  ["Ok", varType("E")],
  ["Err", conType("String")]
]);

const ctx = state([resultEnum]);

// <Ok = 42> as Result<Int>
const okValue = injectTerm("Ok", conTerm("42", conType("Int")), 
  appType(conType("Result"), conType("Int"))
);

// Pattern match
const matcher = matchTerm(okValue, [
  [varPattern("x"), varTerm("x")],      // Ok(x) => x
  [wildcardPattern(), conTerm("error", conType("String"))] // Err(_) => "error"
]);

console.log("Match type:", showType(inferType(ctx, matcher).ok));
```

### **Example 4: Recursive Types (Lists)**

Define and use a recursive `List` type:

```ts
import { muType, variantType, tupleType, foldTerm, injectTerm, unitValue } from "./src/typechecker.js";

const List = muType("List",                       // μList.
  variantType([
    ["Nil", unitType],                            // Nil: ()
    ["Cons", tupleType([conType("Int"), varType("List")])] // Cons: (Int, List)
  ])
);

// Empty list: fold <Nil=()> as List
const emptyList = foldTerm(List, injectTerm("Nil", unitValue, List));
console.log("Empty list type:", showType(inferType(state(), emptyList).ok));
```

### **Example 5: Traits & Dictionaries**

Define an `Eq` trait and implement it for `Int`:

```ts
import { 
  traitDefBinding, 
  dictTerm, 
  lamTerm, 
  traitImplBinding,
  checkTraitImplementation,
  showType
} from "./src/typechecker.js";

const EqTrait = traitDefBinding("Eq", "Self", { arrow: { from: starKind, to: starKind } }, [
  ["eq", arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool")))]
]);

const eqIntImpl = dictTerm("Eq", conType("Int"), [
  ["eq", lamTerm("x", conType("Int"), 
    lamTerm("y", conType("Int"), 
      conTerm("true", conType("Bool"))))]    // Simplified equality
]);

const ctx = state([
  EqTrait,
  traitImplBinding("Eq", conType("Int"), eqIntImpl)
]);

// Get the dictionary for Eq<Int>
const dict = checkTraitImplementation(ctx, "Eq", conType("Int"));
console.log("Eq<Int> dictionary:", showType(inferType(ctx, dict.ok).ok));
```

### **Example 6: Type Aliases**

Create shortcuts for complex types:

```ts
import { typeAliasBinding, normalizeType } from "./src/typechecker.js";

const PairAlias = typeAliasBinding("Pair", ["A", "B"], [starKind, starKind], 
  tupleType([varType("A"), varType("B")])
);

const ctx = state([PairAlias]);

// Pair<Int, String> expands to (Int, String)
const pairType = normalizeType(ctx, appType(appType(conType("Pair"), conType("Int")), conType("String")));
console.log("Pair type:", showType(pairType));  // (Int, String)
```

## 🔧 **Core API Reference**

The library revolves around a **stateful context** (`TypeCheckerState`) passed to all major functions.

### **Creating State**

```ts
import { state, TypeCheckerState } from "./src/typechecker.js";

// Empty state
const emptyState: TypeCheckerState = state([]);

// With bindings
const ctx: TypeCheckerState = state([termBinding("x", conType("Int"))]);
```

### **Essential Functions**

| Function | Description | Signature |
|----------|-------------|-----------|
| **`inferType(state, term)`** | Infers the type of a term | `Result<TypingError, Type>` |
| **`checkType(state, term, expected)`** | Checks term against expected type | `Result<TypingError, {type: Type, subst: Map}>` |
| **`normalizeType(state, ty)`** | β-reduces & expands types | `Type` |
| **`unifyTypes(state, t1, t2, worklist, subst)`** | Unifies two types (mutates substitution) | `Result<TypingError, null>` |
| **`subsumes(state, general, specific, ...)`** | Checks subtyping | `Result<TypingError, null>` |
| **`checkKind(state, ty)`** | Infers/validates type kind | `Result<TypingError, Kind>` |
| **`checkTraitImplementation(state, trait, ty)`** | Resolves trait dictionary | `Result<TypingError, Term>` |
| **`freshMetaVar(state)`** | Creates fresh type variable (`?N`) | `MetaType` |
| **`showType(ty)`**, **`showTerm(t)`**, **`showContext(bindings)`** | Pretty printing | `string` |

### **Term Constructors** (Building ASTs)

```ts
import { 
  // Basics
  varTerm, lamTerm, appTerm, conTerm,
  // Polymorphism
  tylamTerm, tyappTerm,
  // Data structures
  recordTerm, injectTerm, matchTerm, tupleTerm,
  // Recursion
  foldTerm, unfoldTerm,
  // Traits
  dictTerm, traitLamTerm, traitAppTerm, traitMethodTerm,
  // Control
  letTerm
} from "./src/typechecker.js";

// Examples:
const lambda = lamTerm("x", conType("Int"), varTerm("x"));
const poly = tylamTerm("a", starKind, lambda);
const application = appTerm(varTerm("f"), varTerm("x"));
const recordVal = recordTerm([["x", conTerm("1", conType("Int"))]]);
const variant = injectTerm("Some", conTerm("42", conType("Int")), 
  appType(conType("Option"), conType("Int")));
```

### **Type Constructors**

```ts
import { 
  // Basics
  varType, arrowType, conType,
  // Polymorphism
  forallType, lamType, appType,
  // Data
  recordType, variantType, tupleType, muType,
  // Traits  
  boundedForallType,
  // Kinds
  starKind, arrowKind
} from "./src/typechecker.js";

const intToBool = arrowType(conType("Int"), conType("Bool"));
const polyFun = forallType("a", starKind, arrowType(varType("a"), varType("a")));
const listTy = muType("L", variantType([
  ["Nil", tupleType([])],
  ["Cons", tupleType([conType("Int"), varType("L")])]
]));
```

### **Bindings** (Context Entries)

```ts
import { 
  termBinding, typeBinding,
  traitDefBinding, traitImplBinding, dictBinding,
  enumDefBinding, typeAliasBinding
} from "./src/typechecker.js";

const bindings = [
  // Variable binding
  termBinding("x", conType("Int")),
  
  // Type variable (kind)
  typeBinding("Alpha", starKind),
  
  // Type alias
  typeAliasBinding("Result", ["T"], [starKind], 
    appType(conType("Option"), varType("T"))),
    
  // Enum definition
  enumDefBinding("Color", starKind, [], [
    ["Red", unitType], ["Blue", unitType]
  ]),
  
  // Trait definition
  traitDefBinding("Show", "T", starKind, [
    ["show", arrowType(varType("T"), conType("String"))]
  ]),
  
  // Trait implementation (dictionary)
  traitImplBinding("Show", conType("Int"), 
    dictTerm("Show", conType("Int"), [
      ["show", lamTerm("n", conType("Int"), conTerm("n.toString", conType("String")))]
    ]))
];
```

### **Pattern Matching**

```ts
import { 
  varPattern, wildcardPattern, 
  recordPattern, variantPattern, tuplePattern
} from "./src/typechecker.js";

const patterns = [
  varPattern("x"),                    // binds whole value to x
  wildcardPattern(),                  // matches anything, no binding
  recordPattern([["first", varPattern("a")], ["rest", wildcardPattern()]]),
  variantPattern("Cons", tuplePattern([varPattern("hd"), varPattern("tl")])),
];
```

### **Error Handling**

All functions return `Result<TypingError, T>`, where errors are structured:

```ts
type TypingError = 
  | { unbound: string }                    // Undefined variable/type
  | { type_mismatch: { expected: Type, actual: Type } }
  | { kind_mismatch: { expected: Kind, actual: Kind } }
  | { not_a_function: Type }               // Applied non-function
  | { missing_trait_impl: { trait: string, type: Type } }
  | { cyclic: string }                     // Infinite type
  | { missing_case: { label: string } }    // Incomplete pattern match
  | { invalid_variant_label: { variant: Type, label: string } }
  | { missing_field: { record: Type, label: string } }
  | { not_a_variant: Type }
  | { not_a_record: Type }
  | { wrong_number_of_dicts: { expected: number, actual: number } };
  // ... more
```

## 🧪 **Testing & Examples**

The `examples/` folder contains self-contained files:

```bash
# Run individual examples
bun run examples/polymorphic.ts
bun run examples/traits.ts
bun run examples/enums.ts
bun run examples/recursion.ts
```

The `tests/` folder has ~5000+ lines of unit tests covering:

- Unification edge cases
- Higher-kinded polymorphism
- Trait resolution
- Recursive type normalization
- Pattern matching exhaustiveness
- Kind inference

Run tests with:
```bash
bun test
```

## 🎓 **For Type Theory Enthusiasts**

### **Formal Judgment Forms**

**Kinding** (types well-formed under Γ):
```
Γ ⊢ τ : κ
```

**Subtyping**:
```
Γ ⊢ τ₁ <: τ₂
```

**Type Inference** (synthesis):
```
Γ ⊢ e ⇒ τ
```

**Type Checking** (analysis):
```
Γ ⊢ e ⇐ τ
```

**Unification** (constraint solving):
```
Γ; σ ⊢ τ₁ = τ₂
```

### **Key Implementation Decisions**

1. **Stateful Meta-Variables**: All inference uses `MetaEnv` with `freshMetaVar()` for unknowns
2. **Bidirectional Architecture**: `inferType` uses synthesis; `checkType` handles checking
3. **Worklist Constraint Solver**: Defers unification decisions via `solveConstraints()`
4. **Nominal + Structural**: Enums are nominal, but records/variants support structural subtyping
5. **Dictionary Passing**: Traits resolved via explicit dictionaries, no implicit parameters

### **Research Connections**

- **System F<:** The polymorphic core (Girard/Reynolds)
- **Fω**: Higher-kinded extension (Harper/Stone)
- **MLF**: Let-polymorphism (not yet: future work)
- **Haskell Typeclasses**: Dictionary-passing model
- **Rust Traits**: Similar bound resolution, without orphan rules

## 🔮 **Roadmap & Planned Features**

### **v0.2.0 (Next)**
- [ ] Let-polymorphism (HM-style generalization)
- [ ] Type class instances with supertraits
- [ ] Associated types in traits
- [ ] Better error messages with source locations

### **v1.0.0 (Milestone)**
- [ ] WASM compilation target
- [ ] Full λF (dependent types lite)
- [ ] Effect system integration
- [ ] Incremental type checking

### **Long-term**
- Dependent types (Π-types)
- Linear types
- Effect rows
- Pattern synonyms
- Template Haskell-style metaprogramming

## 🤝 **Contributing**

1. Fork & clone
2. `bun install`
3. Add tests in `tests/`
4. Run `bun test --watch`
5. Submit PRs!

**Good first issues**:
- More examples (especially traits + HKTs)
- Better pretty-printer (handle all edge cases)
- Documentation for advanced unification rules

## 📄 **License**

MIT © 2025 Joshua Tenner. See [MIT LICENSE](./LICENSE).

**Vibe-coded** with assistance from Claude AI. Extensive tests ensure correctness, but type systems are complex — bug reports welcome! 🐛

---

*Special thanks to literally everyone who helped me understand this complicated world of type theory.*
