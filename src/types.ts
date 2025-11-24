/**
 * A single *trait bound* used in bounded polymorphism.
 *
 * **What it represents**
 * A `TraitConstraint` expresses that a type must implement a specific trait.
 * For example, in `∀Self where Eq<Self>. Self → Self`, the constraint is
 * `Eq<Self>`.
 *
 * **Why it's useful**
 * Trait constraints allow the type checker to:
 * - Require certain capabilities (equality, ordering, functor behavior, etc.)
 * - Resolve dictionaries during trait applications
 * - Type‑check trait‑lambda abstractions that depend on evidence
 *
 * **Used by**
 * - {@link BoundedForallType}
 * - {@link traitLamTerm}
 * - {@link checkTraitConstraints}
 *
 * **Examples**
 *
 * Basic constraint:
 * ```ts
 * import { varType } from "system-f-omega";
 *
 * const c: TraitConstraint = {
 *   trait: "Eq",
 *   type: varType("Self"),
 * };
 * // Represents: Eq<Self>
 * ```
 *
 * Multiple constraints:
 * ```ts
 * import { conType } from "system-f-omega";
 *
 * const constraints: TraitConstraint[] = [
 *   { trait: "Eq", type: conType("Int") },
 *   { trait: "Show", type: conType("Int") },
 * ];
 * ```
 *
 * In a bounded polymorphic signature:
 * ```ts
 * import { boundedForallType, varType, starKind } from "system-f-omega";
 *
 * const c = { trait: "Eq", type: varType("T") };
 * const ty = boundedForallType("T", starKind, [c], varType("T"));
 * // ∀T::* where Eq<T>. T
 * ```
 */
export type TraitConstraint = {
  trait: string;
  type: Type;
};

/**
 * A universally quantified type with *trait constraints*.
 *
 * **What it represents**
 * `BoundedForallType` describes polymorphic types that require trait
 * constraints on their type parameter.
 * Example form:
 * `∀Self::*. Eq<Self>. Self → Self`
 *
 * This is similar to Haskell’s `forall a. (Eq a) => ...`.
 *
 * **Why it's useful**
 * Bounded polymorphism allows:
 * - Constraining generic functions to types with required capabilities
 * - Type‑checking trait‑lambda terms (see {@link traitLamTerm})
 * - Automatic dictionary resolution when instantiating polymorphic values
 *   (see {@link instantiateWithTraits})
 *
 * **Related**
 * - {@link TraitConstraint}
 * - {@link Kind}
 * - {@link instantiateWithTraits}
 * - {@link traitLamTerm}
 *
 * **Structure**
 * - `var`: the bound type variable (e.g. `"Self"`)
 * - `kind`: its kind (usually `*`)
 * - `constraints`: trait requirements such as `Eq<Self>`
 * - `body`: the underlying polymorphic type
 *
 * **Examples**
 *
 * A simple constrained identity type:
 * ```ts
 * import { boundedForallType, varType, starKind } from "system-f-omega";
 *
 * const eqSelf = boundedForallType(
 *   "Self",
 *   starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   varType("Self")
 * );
 * // Represents: ∀Self::* where Eq<Self>. Self
 * ```
 *
 * Multiple constraints:
 * ```ts
 * import { boundedForallType, varType, starKind, conType } from "system-f-omega";
 *
 * const constraints = [
 *   { trait: "Eq", type: varType("T") },
 *   { trait: "Show", type: varType("T") }
 * ];
 *
 * const ty = boundedForallType("T", starKind, constraints, conType("Int"));
 * // ∀T::* where Eq<T>, Show<T>. Int
 * ```
 *
 * Building a trait‑generic function:
 * ```ts
 * import { boundedForallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const comparable = boundedForallType(
 *   "A",
 *   starKind,
 *   [{ trait: "Ord", type: varType("A") }],
 *   arrowType(varType("A"), varType("A"))
 * );
 * // ∀A::* where Ord<A>. A → A
 * ```
 */
export type BoundedForallType = {
  bounded_forall: {
    var: string;
    kind: Kind;
    constraints: TraitConstraint[];
    body: Type;
  };
};

/**
 * The base kind `*` used for ordinary, fully‑applied types.
 *
 * **What it represents**
 * `StarKind` is the simplest kind in the kind system.
 * It marks types that represent actual runtime values:
 * - `Int :: *`
 * - `Bool :: *`
 * - `List<Int> :: *`
 *
 * In contrast, higher‑kinded types (like `List :: * → *`) use
 * {@link ArrowKind}.
 *
 * **Why it's useful**
 * The type checker must know *what kind of thing a type constructor is*.
 * `StarKind` lets the system distinguish:
 * - data types (`*`)
 * - type constructors (`* → *`)
 * - more complex kinds (`(* → *) → *`)
 *
 * It also appears in:
 * - type declarations (see {@link addType})
 * - polymorphic type binders (see {@link forallType})
 * - bounded polymorphism (see {@link BoundedForallType})
 *
 * **Examples**
 *
 * Declaring a type as a concrete data type:
 * ```ts
 * import { addType, starKind, freshState } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;   // Int :: *
 * ```
 *
 * Using `*` in a polymorphic function:
 * ```ts
 * import { forallType, varType, arrowType, starKind } from "system-f-omega";
 *
 * const id = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * // ∀A::*. A → A
 * ```
 *
 * Checking that a concrete type has kind `*`:
 * ```ts
 * import { checkKind, conType, starKind, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const kind = checkKind(state, conType("Int"));  // → *
 * ```
 *
 * @see {@link ArrowKind} for higher‑kinded types
 * @see {@link Kind} union of all kinds
 * @see {@link addType} binds a name to a kind
 */
export type StarKind = { star: null };

/**
 * A function‑kind of the form `κ₁ → κ₂`, representing type constructors.
 *
 * **What it represents**
 * `ArrowKind` describes kinds of *type‑level functions*—constructors that take
 * types as input and produce new types.
 *
 * Examples:
 * - `List :: * → *`
 * - `Either :: * → * → *` (internally `* → (* → *)`)
 * - `Functor :: (* → *) → *`
 *
 * In other words, if `StarKind` (`*`) classifies values, `ArrowKind` classifies
 * *type constructors* of one or more arguments.
 *
 * **Why it's useful**
 * Higher‑kinded types are essential for:
 * - generic containers (`List<T>`)
 * - type‑level functions (e.g., `λF::(*→*). ...`)
 * - traits over constructors (e.g., `Functor<F>` requires `F :: * → *`)
 *
 * The type checker uses `ArrowKind` when validating:
 * - type declarations added via {@link addType}
 * - type applications in {@link checkAppKind}
 * - polymorphic type lambdas in {@link lamType}
 *
 * **Examples**
 *
 * Declaring a unary type constructor:
 * ```ts
 * import { addType, arrowKind, starKind, freshState } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * // List :: * → *
 * ```
 *
 * Declaring a binary constructor (Either<A, B>):
 * ```ts
 * import { arrowKind, starKind } from "system-f-omega";
 *
 * // * → (* → *)
 * const eitherKind = arrowKind(starKind, arrowKind(starKind, starKind));
 * ```
 *
 * Using arrow kinds in a type lambda:
 * ```ts
 * import { lamType, arrowKind, starKind, varType, showType } from "system-f-omega";
 *
 * const tlam = lamType("F", arrowKind(starKind, starKind), varType("F"));
 * // λF::(* → *). F
 * ```
 *
 * @see {@link Kind} union of StarKind and ArrowKind
 * @see {@link starKind} for the base kind
 * @see {@link checkAppKind} validates applications using ArrowKind
 * @see {@link addType} binds constructors with their kinds
 */
export type ArrowKind = { arrow: { from: Kind; to: Kind } };

/**
 * The full set of kinds supported by the type system.
 *
 * **What it represents**
 * `Kind` describes the “type of a type.”
 * It indicates how many type arguments a type constructor expects.
 *
 * The system has only two fundamental kinds:
 *
 * - {@link StarKind} — `*`
 *   Represents concrete, fully‑applied types like `Int`, `Bool`,
 *   or `List<Int>`.
 *
 * - {@link ArrowKind} — `κ₁ → κ₂`
 *   Represents type constructors such as `List :: * → *`,
 *   `Either :: * → (* → *)`, or other higher‑kinded abstractions.
 *
 * **Why it's useful**
 * Kinds prevent mis‑application of type constructors.
 * For example, it is illegal to write `Int<Int>` because `Int` has kind `*`,
 * not `* → *`.
 *
 * The type checker uses `Kind` in:
 * - {@link checkKind} — Infers and validates the kind of a type
 * - {@link checkAppKind} — Ensures type application is well‑formed
 * - {@link addType} — Declares the kind of a new type constructor
 * - {@link arrowKind} and {@link starKind} — Constructors for kinds
 *
 * **Examples**
 *
 * A concrete type has kind `*`:
 * ```ts
 * import { checkKind, conType, starKind, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * checkKind(state, conType("Int")).ok;  // -> *
 * ```
 *
 * A list type constructor has kind `* → *`:
 * ```ts
 * import { addType, arrowKind, starKind, freshState } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * ```
 *
 * Higher‑kinded constructor (`Either :: * → * → *`):
 * ```ts
 * import { arrowKind, starKind } from "system-f-omega";
 *
 * const eitherKind =
 *   arrowKind(starKind, arrowKind(starKind, starKind));  // * → (* → *)
 * ```
 *
 * @see {@link StarKind} Base kind
 * @see {@link ArrowKind} Higher‑kinded constructors
 * @see {@link checkKind} Kind inference/checking
 * @see {@link arrowKind} Helper to build function kinds
 */
export type Kind =
  | StarKind // * (base kind for proper types)
  | ArrowKind; // κ₁ → κ₂

/**
 * A pattern that binds the entire matched value to a variable.
 *
 * **What it represents**
 * `VarPattern` matches **anything** and gives it a name.
 * For example, in `match x { y => ... }`, the pattern `{ var: "y" }`
 * means “bind the whole scrutinee to `y`”.
 *
 * It is the pattern‑level equivalent of a function parameter binding.
 *
 * **Why it's useful**
 * Variable patterns are fundamental for:
 * - Extracting values in `match` expressions
 * - Binding names inside nested patterns
 * - Acting as an “open” pattern that matches all inputs (like a wildcard)
 *
 * The type checker:
 * - Assigns the scrutinee’s type to the binding
 * - Extends the context with the new variable (see {@link checkPattern})
 *
 * **Related**
 * - {@link wildcardPattern} — matches anything but binds nothing
 * - {@link Pattern} — union of all supported pattern forms
 * - {@link checkPattern} — validates the pattern and extracts bindings
 *
 * **Examples**
 *
 * Basic variable pattern:
 * ```ts
 * import { varPattern, showPattern } from "system-f-omega";
 *
 * console.log(showPattern(varPattern("x")));  // "x"
 * ```
 *
 * Using a var pattern in a match:
 * ```ts
 * import { matchTerm, varPattern, varTerm } from "system-f-omega";
 *
 * const match = matchTerm({ var: "xs" }, [
 *   [varPattern("x"), varTerm("x")]
 * ]);
 * // Matches anything and returns x
 * ```
 *
 * Type‑checking a var pattern:
 * ```ts
 * import { checkPattern, freshState, varPattern, conType, addType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const res = checkPattern(state, varPattern("n"), conType("Int"));
 * // Binds: n : Int
 * ```
 */
export type VarPattern = { var: string };

/**
 * A pattern that matches any value without binding it.
 *
 * **What it represents**
 * `WildcardPattern` corresponds to the `_` pattern in a `match` expression.
 * It accepts every possible input but does **not** introduce a variable
 * into the context.
 *
 * Useful when:
 * - A branch should ignore its value
 * - Only pattern structure matters, not the payload
 * - You want an “always matches” fallback case
 *
 * **Why it's useful**
 * Wildcards make pattern matching:
 * - **Exhaustive**: one wildcard case covers all remaining possibilities
 * - **Simple**: no unnecessary variable bindings
 * - **Safe**: avoids unused‑variable warnings or errors
 *
 * The type checker treats wildcard patterns specially:
 * - They always succeed in {@link checkPattern}
 * - They produce *no bindings*
 * - A single wildcard makes {@link checkExhaustive} succeed immediately
 *
 * **Related**
 * - {@link VarPattern} — like `_`, but binds the value
 * - {@link Pattern} — union of all pattern types
 * - {@link checkPattern} — validates patterns
 *
 * **Examples**
 *
 * Matching anything:
 * ```ts
 * import { wildcardPattern, showPattern } from "system-f-omega";
 *
 * console.log(showPattern(wildcardPattern()));  // "_"
 * ```
 *
 * Using `_` as a fallback case:
 * ```ts
 * import { matchTerm, wildcardPattern, conTerm, conType } from "system-f-omega";
 *
 * const match = matchTerm(
 *   conTerm("42", conType("Int")),
 *   [[wildcardPattern(), conTerm("0", conType("Int"))]]
 * );
 * // Always returns 0
 * ```
 *
 * Checking a wildcard pattern:
 * ```ts
 * import { checkPattern, wildcardPattern, conType, addType, freshState, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const res = checkPattern(state, wildcardPattern(), conType("Bool"));
 * console.log(res.ok.length);  // 0 (no bindings)
 * ```
 */
export type WildcardPattern = { wildcard: null };

/**
 * A pattern that matches a **specific constructor or literal value**.
 *
 * **What it represents**
 * `ConPattern` corresponds to patterns like:
 * - `true`
 * - `None`
 * - `SomeConstructor`
 *
 * It matches **only** that exact constructor name, and never binds variables.
 *
 * Each constructor includes:
 * - `name`: the literal or enum/variant constructor
 * - `type`: the expected type of that constructor (used for type checking)
 *
 * **Why it's useful**
 * Constructor patterns enable:
 * - Exact matching in `match` expressions
 *   (e.g. `match xs { None => ... | Some(x) => ... }`)
 * - Enumerated datatype pattern matching
 * - Safer control flow by verifying that a constructor belongs to the
 *   expected enum or type
 *
 * The type checker:
 * - Ensures the constructor’s type is assignable to the scrutinee’s type
 *   (via {@link checkPattern})
 * - Rejects mismatches early and precisely
 *
 * **Related**
 * - {@link VariantPattern} — constructor + payload (e.g. `Some(x)`)
 * - {@link Pattern} — all supported pattern types
 * - {@link checkPattern} — validates constructor compatibility
 *
 * **Examples**
 *
 * Matching a literal boolean:
 * ```ts
 * import { conPattern, conType, showPattern } from "system-f-omega";
 *
 * const pat = conPattern("true", conType("Bool"));
 * console.log(showPattern(pat));  // "true"
 * ```
 *
 * Matching a unit constructor from an enum:
 * ```ts
 * import { conPattern, conType } from "system-f-omega";
 *
 * const pat = conPattern("None", conType("Option<Int>"));
 * // Matches only the "None" case
 * ```
 *
 * Type‑checking a constructor pattern:
 * ```ts
 * import { checkPattern, freshState, addType, conPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const res = checkPattern(state, conPattern("true", conType("Bool")), conType("Bool"));
 * console.log(res.ok.length);  // 0 (no bindings)
 * ```
 */
export type ConPattern = { con: { name: string; type: Type } };

/**
 * A pattern that matches **record values field‑by‑field**.
 *
 * **What it represents**
 * `RecordPattern` corresponds to patterns like:
 *
 * ```ts
 * { x: px, y: py }
 * ```
 *
 * Each field is a pair `[label, subpattern]`.
 * A `RecordPattern` recursively matches the structure of a record value and
 * extracts any bindings found inside nested patterns.
 *
 * **Why it's useful**
 * Record patterns allow:
 * - Destructuring of structured data directly in `match` expressions
 * - Binding individual fields by name
 * - Flexible shape checking through **structural typing**
 *
 * The type checker:
 * - Ensures all required fields exist in the scrutinee's type
 *   (via {@link checkRecordPattern})
 * - Recursively checks each field's pattern
 * - Merges all variable bindings found in subpatterns
 *
 * **Related**
 * - {@link Pattern} — union of all pattern kinds
 * - {@link checkPattern} — main pattern‑checking dispatcher
 * - {@link RecordType} — type counterpart for records
 *
 * **Examples**
 *
 * Basic record destructuring:
 * ```ts
 * import { recordPattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", varPattern("b")],
 * ]);
 *
 * console.log(showPattern(pat));  // "{x: a, y: b}"
 * ```
 *
 * Nested patterns:
 * ```ts
 * import { recordPattern, tuplePattern, varPattern } from "system-f-omega";
 *
 * const pat = recordPattern([
 *   ["point", tuplePattern([varPattern("x"), varPattern("y")])]
 * ]);
 * // Matches { point = (x, y) }
 * ```
 *
 * Type‑checking a record pattern:
 * ```ts
 * import {
 *   checkPattern, freshState, addType,
 *   recordPattern, varPattern, recordType, conType, starKind
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["x", varPattern("n")]]);
 * const ty = recordType([["x", conType("Int")]]);
 *
 * const res = checkPattern(state, pat, ty);
 * // Binds: n : Int
 * console.log(res.ok.length);  // 1
 * ```
 */
export type RecordPattern = { record: [string, Pattern][] };

/**
 * A pattern that matches a **specific variant/constructor** of a sum type.
 *
 * **What it represents**
 * `VariantPattern` corresponds to patterns like:
 *
 * ```ts
 * Some(x)
 * Left(v)
 * Cons(hd, tl)
 * ```
 *
 * A variant pattern has:
 * - `label`: the constructor name (e.g. `"Some"`)
 * - `pattern`: the payload pattern for that constructor (recursive)
 *
 * It matches *only* values built using that variant and then recursively
 * checks the inner pattern.
 *
 * **Why it's useful**
 * Variant patterns enable:
 * - Pattern matching on enums / algebraic data types
 *   (e.g. `Option`, `Either`, `List`, custom enums)
 * - Destructuring inside recursive types (e.g. lists or trees)
 * - Precise case analysis in `match` expressions
 *
 * The type checker:
 * - Verifies the label belongs to the scrutinee’s variant/enum type
 *   (via {@link checkPattern})
 * - Determines the type associated with that label (nominal or structural)
 * - Recursively checks the payload pattern against that field type
 *
 * **Related**
 * - {@link ConPattern} — constructor with no payload (`None`, `true`, etc.)
 * - {@link Pattern} — union of all supported pattern types
 * - {@link checkPattern} — validates variant patterns
 * - {@link VariantType} — structural variant type
 *
 * **Examples**
 *
 * Matching an `Option<Int>`:
 * ```ts
 * import { variantPattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = variantPattern("Some", varPattern("x"));
 * console.log(showPattern(pat));  // "Some(x)"
 * ```
 *
 * Matching a recursive list constructor:
 * ```ts
 * import { variantPattern, tuplePattern, varPattern } from "system-f-omega";
 *
 * const consPat = variantPattern(
 *   "Cons",
 *   tuplePattern([varPattern("hd"), varPattern("tl")])
 * );
 * // Matches Cons(hd, tl)
 * ```
 *
 * Type‑checking a variant pattern:
 * ```ts
 * import {
 *   freshState, addType, addEnum, checkPattern,
 *   variantPattern, varPattern, appType, conType, starKind
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const pat = variantPattern("Some", varPattern("x"));
 * const ty  = appType(conType("Option"), conType("Int"));
 *
 * const res = checkPattern(state, pat, ty);
 * console.log(res.ok.length);  // 1 (binds x : Int)
 * ```
 */
export type VariantPattern = { variant: { label: string; pattern: Pattern } };

/**
 * A pattern that matches a **tuple value** position‑by‑position.
 *
 * **What it represents**
 * `TuplePattern` corresponds to patterns like:
 *
 * ```ts
 * (x, y)
 * ()
 * (hd, (a, b))
 * ```
 *
 * Each element inside the tuple is its own nested pattern.
 * Tuple patterns match only **tuple types of the same arity**.
 *
 * **Why it's useful**
 * Tuple patterns allow:
 * - Destructuring of multi‑value tuples within `match` expressions
 * - Binding individual components by position
 * - Nested structural pattern matching (tuples inside tuples, inside variants, etc.)
 *
 * The type checker:
 * - Ensures the scrutinee’s type is a tuple of the same length
 *   (via {@link checkTuplePattern})
 * - Recursively checks each element’s pattern
 * - Collects all variable bindings from element patterns
 *
 * **Related**
 * - {@link Pattern} — union of all pattern forms
 * - {@link checkPattern} — main pattern‑checking dispatcher
 * - {@link TupleType} — type-level tuple
 *
 * **Examples**
 *
 * Simple tuple destructuring:
 * ```ts
 * import { tuplePattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = tuplePattern([varPattern("x"), varPattern("y")]);
 * console.log(showPattern(pat));  // "(x, y)"
 * ```
 *
 * Nested tuple pattern:
 * ```ts
 * import { tuplePattern, varPattern } from "system-f-omega";
 *
 * const pat = tuplePattern([
 *   varPattern("a"),
 *   tuplePattern([varPattern("b"), varPattern("c")])
 * ]);
 * // Matches (a, (b, c))
 * ```
 *
 * Type‑checking against a tuple type:
 * ```ts
 * import {
 *   checkPattern, freshState, addType,
 *   tuplePattern, varPattern, tupleType, conType, starKind
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = tuplePattern([varPattern("n")]);
 * const ty  = tupleType([conType("Int")]);
 *
 * const res = checkPattern(state, pat, ty);
 * console.log(res.ok.length);  // 1 (binds n : Int)
 * ```
 */
export type TuplePattern = { tuple: Pattern[] };

/**
 * A union of all supported pattern forms used in `match` expressions.
 *
 * **What it represents**
 * `Pattern` is the root type for every kind of pattern the type checker
 * understands. Patterns describe *shapes* of data and may bind variables.
 *
 * Supported forms:
 * - {@link VarPattern} — variable binding (`x`)
 * - {@link WildcardPattern} — match anything (`_`)
 * - {@link ConPattern} — match a specific constructor or literal (`true`, `None`)
 * - {@link RecordPattern} — match records by field (`{ x: p1, y: p2 }`)
 * - {@link VariantPattern} — match enum / ADT constructors (`Some(p)`, `Cons(p)`)
 * - {@link TuplePattern} — match tuple elements (`(p1, p2, ...)`)
 *
 * **Why it's useful**
 * Patterns power the `match` construct, enabling:
 * - Structural decomposition of values
 * - Binding local variables inside pattern cases
 * - Exhaustiveness checking (via {@link checkExhaustive})
 * - Rich destructuring of tuples, records, and variants
 *
 * The type checker:
 * - Validates patterns against an expected type via {@link checkPattern}
 * - Extracts variable bindings for each case
 * - Ensures all cases collectively cover all possibilities
 *
 * **Related**
 * - {@link checkPattern} — checks a single pattern
 * - {@link inferMatchType} — checks all patterns within a match expression
 * - {@link computeFreePatterns} — extracts free names for imports/renaming
 *
 * **Examples**
 *
 * Matching with multiple pattern forms:
 * ```ts
 * import {
 *   matchTerm, varPattern, wildcardPattern, conPattern,
 *   variantPattern, tuplePattern, recordPattern, conTerm, conType
 * } from "system-f-omega";
 *
 * // match value {
 * //   None        => 0
 * //   Some(x)     => x
 * //   _           => -1
 * // }
 * const match = matchTerm(
 *   conTerm("opt", conType("Option<Int>")),
 *   [
 *     [conPattern("None", conType("Unit")), conTerm("0", conType("Int"))],
 *     [variantPattern("Some", varPattern("x")), varPattern("x")],
 *     [wildcardPattern(), conTerm("-1", conType("Int"))],
 *   ]
 * );
 * ```
 *
 * Nested patterns:
 * ```ts
 * import { recordPattern, tuplePattern, varPattern } from "system-f-omega";
 *
 * // Matches a record { point = (x, y) }
 * const pat = recordPattern([
 *   ["point", tuplePattern([varPattern("x"), varPattern("y")])]
 * ]);
 * ```
 *
 * Exhaustive matching with multiple patterns:
 * ```ts
 * import { checkExhaustive, variantPattern, varPattern, conType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * const patterns = [
 *   variantPattern("None", varPattern("_")),
 *   variantPattern("Some", varPattern("x"))
 * ];
 *
 * const res = checkExhaustive(
 *   { ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } },
 *   patterns,
 *   conType("Option<Int>")
 * );
 * console.log("ok" in res);  // true
 * ```
 */
export type Pattern =
  | VarPattern // x - bind variable
  | WildcardPattern // _ - match anything
  | ConPattern // literal constant
  | RecordPattern // { l1: p1, l2: p2 }
  | VariantPattern // Label(pattern)
  | TuplePattern; // #(...patterns)

/**
 * A type variable, written as `a`, `T`, `Self`, etc.
 *
 * **What it represents**
 * `VarType` is the simplest type form: a named type variable.
 * It can represent:
 * - A **polymorphic parameter** (`∀a. a → a`)
 * - A **generic type argument** (`List<a>`)
 * - A **trait‑bound self type** (`Eq<Self>`)
 *
 * Type variables may be:
 * - **Bound** (introduced by `∀`, `λ`, or `μ`)
 * - **Free** (unconstrained until unification assigns them)
 *
 * **Why it's useful**
 * `VarType` is essential for:
 * - Polymorphism (generic functions, traits, HKTs)
 * - Type inference (variables unify with other types)
 * - Representing unknown or placeholder types
 *
 * The type checker:
 * - Resolves bound variables inside quantifiers
 * - Unifies free variables during inference (via {@link unifyVariable})
 * - Looks up kinds for variables using {@link checkVarKind}
 *
 * **Related**
 * - {@link forallType} — binds a type variable
 * - {@link lamType} — binds a variable in a type lambda
 * - {@link unifyVariable} — unifies `VarType` with concrete types
 * - {@link substituteType} — replaces occurrences of a type variable
 *
 * **Examples**
 *
 * Using a type variable in a polymorphic function:
 * ```ts
 * import { forallType, arrowType, varType, starKind, showType } from "system-f-omega";
 *
 * const id = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * console.log(showType(id));  // "∀A::*. (A → A)"
 * ```
 *
 * Appearing inside a type application:
 * ```ts
 * import { appType, conType, varType, showType } from "system-f-omega";
 *
 * const listA = appType(conType("List"), varType("A"));
 * console.log(showType(listA));  // "List<A>"
 * ```
 *
 * Type inference where a variable gets unified:
 * ```ts
 * import { freshState, unifyTypes, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * unifyTypes(state, varType("X"), conType("Int"), [], subst);
 * console.log(subst.get("X"));  // { con: "Int" }
 * ```
 */
export type VarType = { var: string };

/**
 * A function type of the form `τ₁ → τ₂`.
 *
 * **What it represents**
 * `ArrowType` is the core type constructor for functions.
 * It describes a value that takes an input of type `from` and returns a value of
 * type `to`, just like function arrows in most typed languages.
 *
 * Examples:
 * - `Int → Bool`
 * - `(A → B) → List<A>`
 * - `Self → Int` inside a trait
 *
 * **Why it's useful**
 * Function types are essential to:
 * - Typing lambda expressions (`λx:τ. body`)
 * - Checking applications (`f x`), via {@link inferAppType}
 * - Encoding method signatures in traits
 * - Structural unification during type inference (via {@link unifyArrowTypes})
 *
 * The type checker:
 * - Validates both sides have kind `*` using {@link checkArrowKind}
 * - Unifies arrows structurally (domain and codomain)
 * - Supports bottom-domain subtyping, where `⊥ → τ` is a subtype of any
 *   function returning `τ`
 *
 * **Related**
 * - {@link lamTerm} — term-level λ whose type is an ArrowType
 * - {@link unifyArrowTypes} — structural arrow unification
 * - {@link checkArrowKind} — ensures function types are well‑kinded
 * - {@link inferLamType} — infers arrow types from lambdas
 *
 * **Examples**
 *
 * A simple function type:
 * ```ts
 * import { arrowType, conType, showType } from "system-f-omega";
 *
 * const fn = arrowType(conType("Int"), conType("Bool"));
 * console.log(showType(fn));  // "(Int → Bool)"
 * ```
 *
 * Nested function types:
 * ```ts
 * import { arrowType, varType, showType } from "system-f-omega";
 *
 * const f = arrowType(
 *   arrowType(varType("A"), varType("B")),
 *   varType("C")
 * );
 * console.log(showType(f));  // "((A → B) → C)"
 * ```
 *
 * Using ArrowType in a lambda:
 * ```ts
 * import { lamTerm, arrowType, conType, varTerm, inferType, freshState, addType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const inferred = inferType(state, id);
 * console.log(showType(inferred.ok));  // "(Int → Int)"
 * ```
 */
export type ArrowType = { arrow: { from: Type; to: Type } };

/**
 * A universally‑quantified polymorphic type `∀α::κ. τ`.
 *
 * **What it represents**
 * `ForallType` is the type‑level form of a polymorphic function.
 * It binds a type variable (`var`) of a given kind (`kind`) inside a body type
 * (`body`).
 *
 * Example:
 * ```
 * ∀A::*. A → A
 * ```
 *
 * This is equivalent to a generic function in many languages:
 * - Haskell: `forall a. a -> a`
 * - TypeScript: `<A>(x: A) => A`
 *
 * **Why it's useful**
 * Universal quantification enables:
 * - Generic functions that work for *any* type
 * - Polymorphic higher‑order functions
 * - Type‑level abstraction that can later be instantiated with concrete types
 *
 * The type checker uses `ForallType` in:
 * - {@link inferTylamType} — inferring the type of a `Λα::κ. term`
 * - {@link inferTyappType} — applying a type argument to a polymorphic value
 * - {@link instantiateType} — freshening quantified variables into meta‑vars
 * - {@link subsumes} — polymorphic subtyping via Skolemization
 *
 * **Structure**
 * - `var`: name of the type variable (`"A"`, `"Self"`, `"F"`)
 * - `kind`: its kind (`*`, `* → *`, etc.)
 * - `body`: the type in which the variable may appear
 *
 * **Examples**
 *
 * A basic polymorphic identity type:
 * ```ts
 * import { forallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * const idTy = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * console.log(showType(idTy));  // "∀A::*. (A → A)"
 * ```
 *
 * A higher‑kinded polymorphic type:
 * ```ts
 * import { forallType, lamType, varType, arrowKind, starKind, showType } from "system-f-omega";
 *
 * const polyFunctor = forallType(
 *   "F",
 *   arrowKind(starKind, starKind),   // F :: * → *
 *   varType("F")
 * );
 * console.log(showType(polyFunctor));  // "∀F::(* → *). F"
 * ```
 *
 * Instantiating a polymorphic type:
 * ```ts
 * import { instantiateType, freshState, forallType, varType, arrowType, conType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const poly = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * const inst = instantiateType(state, poly);   // fresh ?0
 *
 * // (?0 → ?0)
 * ```
 *
 * @see {@link tylamTerm} Term-level abstraction
 * @see {@link tyappTerm} Type application
 * @see {@link instantiateType} Skolemizes polymorphic types
 * @see {@link checkForallKind} Validates forall kinds
 * @see {@link Kind} Kinds for type variables
 */
export type ForallType = { forall: { var: string; kind: Kind; body: Type } };

/**
 * A type‑level application `F A`, applying a type constructor to an argument.
 *
 * **What it represents**
 * `AppType` is how the type checker represents *higher‑kinded type application*.
 * It corresponds to writing:
 *
 * - `List<Int>` → `appType(List, Int)`
 * - `Either<Int, Bool>` → `appType(appType(Either, Int), Bool)`
 *
 * Internally, type applications are **left‑associative**:
 * ```
 * F A B  ≡  ((F A) B)
 * ```
 *
 * **Why it's useful**
 * Type application is essential for:
 * - Using higher‑kinded types (`List :: * → *`)
 * - Applying type constructors with multiple parameters
 * - Normalization (beta‑reduction of type lambdas)
 * - Enum expansion (parameterized variants)
 *
 * The type checker uses `AppType` in:
 * - {@link checkAppKind} — ensures `func` has a function kind
 * - {@link normalizeType} — beta‑reduces `(λα. body) arg`
 * - {@link getSpineArgs} and {@link getSpineHead} — deconstructing nested apps
 * - {@link unifyAppTypes} — unifying type applications
 *
 * **Examples**
 *
 * A simple HKT application:
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log(showType(listInt));  // "List<Int>"
 * ```
 *
 * A multi‑argument constructor (`Either`):
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const either = appType(
 *   appType(conType("Either"), conType("Int")),
 *   conType("Bool")
 * );
 * console.log(showType(either));  // "Either<Int, Bool>"
 * ```
 *
 * Beta‑reducing a type lambda:
 * ```ts
 * import { lamType, appType, varType, conType, starKind, normalizeType, freshState, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const id = lamType("T", starKind, varType("T"));
 *
 * const applied = appType(id, conType("Int"));
 * console.log(showType(normalizeType(state, applied)));  // "Int"
 * ```
 *
 * @see {@link checkAppKind} Validates kind correctness of applications
 * @see {@link normalizeType} Performs beta‑reduction
 * @see {@link getSpineArgs} Extracts argument list
 * @see {@link getSpineHead} Extracts base constructor
 * @see {@link unifyAppTypes} Unification rule for applications
 */
export type AppType = { app: { func: Type; arg: Type } };

/**
 * A type‑level lambda `λα::κ. body`, used to define **higher‑kinded type functions**.
 *
 * **What it represents**
 * `LamType` is the type‑level analogue of a lambda expression.
 * It abstracts over a type variable (`var`) of a given kind (`kind`) inside a
 * type (`body`).
 *
 * Example:
 * ```
 * λT::*. T → T
 * ```
 *
 * This is how the system represents **type constructors** that take arguments,
 * such as functors, monads, or type‑level functions produced during enum
 * normalization.
 *
 * **Why it's useful**
 * Type‑level lambdas are essential for:
 * - Expressing higher‑kinded constructors (`(* → *) → *`)
 * - Beta‑reducing type functions in {@link normalizeType}
 * - Representing parameterized enum expansions
 *   (recursive enums often normalize into λ‑wrapped bodies)
 * - Supporting type application with {@link AppType}
 *
 * They behave exactly like lambdas at the term level, but operate *on types*:
 * - `lamType(...)` introduces a type variable binding
 * - `appType(...)` applies it
 * - `normalizeType(...)` performs β‑reduction
 *
 * **Related**
 * - {@link AppType} — type‑level application
 * - {@link normalizeType} — reduces `(λt. body) arg`
 * - {@link forallType} — quantifies over a type parameter instead of abstracting
 * - {@link arrowKind} — kinds for type functions
 *
 * **Examples**
 *
 * A simple type‑level identity function:
 * ```ts
 * import { lamType, varType, starKind, showType } from "system-f-omega";
 *
 * const idTy = lamType("T", starKind, varType("T"));
 * console.log(showType(idTy));  // "λT::*. T"
 * ```
 *
 * Applying a type lambda:
 * ```ts
 * import { lamType, appType, conType, starKind, normalizeType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const id = lamType("T", starKind, { var: "T" });
 * const applied = appType(id, conType("Int"));
 *
 * console.log(showType(normalizeType(state, applied)));  // "Int"
 * ```
 *
 * A higher‑kinded constructor:
 * ```ts
 * import { lamType, arrowKind, starKind, varType, showType } from "system-f-omega";
 *
 * // λF::(* → *). F<Int>
 * const applyToInt = lamType("F", arrowKind(starKind, starKind),
 *   appType(varType("F"), conType("Int"))
 * );
 *
 * console.log(showType(applyToInt));  // "λF::(* → *). F<Int>"
 * ```
 */
export type LamType = { lam: { var: string; kind: Kind; body: Type } };

/**
 * A concrete (named) type constructor such as `Int`, `Bool`, `List`, or `Either`.
 *
 * **What it represents**
 * `ConType` is the simplest type form representing:
 * - **Primitive types** (`Int`, `Bool`, `String`)
 * - **User‑defined types** added via {@link addType}
 * - **Enum/ADT constructors** declared via {@link addEnum}
 * - **Type aliases** that normalize to constructors
 *
 * A `con` may be:
 * - a fully concrete type (`Int`)
 * - a type constructor waiting for arguments (`List :: * → *`)
 * - part of a multi‑argument constructor (`Either :: * → * → *`)
 *
 * **Why it's useful**
 * Concrete type names serve as the “heads” of type applications and are crucial
 * for:
 * - Kind checking (handled by {@link checkConKind})
 * - Nominal type matching (e.g., enum resolution)
 * - Unification of type applications (e.g. `Either<Int, Bool>`)
 * - Normalization and enum expansion
 *
 * ConTypes often appear inside:
 * - {@link AppType} (e.g. `appType(conType("List"), Int)`)
 * - {@link VariantType} (enum variants referencing constructors)
 * - {@link TraitConstraint} (e.g. `Eq<Int>`)
 *
 * **Examples**
 *
 * A simple concrete type:
 * ```ts
 * import { conType, showType } from "system-f-omega";
 *
 * const t = conType("Int");
 * console.log(showType(t));  // "Int"
 * ```
 *
 * Using a constructor as the head of a type application:
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log(showType(listInt));  // "List<Int>"
 * ```
 *
 * Declaring a new type in the context:
 * ```ts
 * import { addType, conType, starKind, freshState } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Unit", starKind).ok;
 *
 * const unit = conType("Unit");
 * ```
 *
 * @see {@link checkConKind} Validates a constructor’s kind
 * @see {@link appType} Applies type constructors
 * @see {@link normalizeType} Expands enums and aliases
 * @see {@link addType} Declares a new concrete type
 */
export type ConType = { con: string };

/**
 * A structural **record type** of the form `{ label₁: τ₁, label₂: τ₂, ... }`.
 *
 * **What it represents**
 * `RecordType` describes an object with named fields and their associated types.
 * Examples:
 * ```
 * { x: Int, y: Bool }
 * { name: String, age: Int }
 * ```
 *
 * Record types have **structural width subtyping**:
 * - `{ x: Int }` is a subtype of `{ x: Int, y: Bool }`
 *   (extra fields are allowed on the wider type)
 *
 * **Why it's useful**
 * Records model everyday structured data.
 * The type checker uses `RecordType` to support:
 * - Typed records (`recordTerm`)
 * - Field projection (`projectTerm`)
 * - Pattern matching via {@link RecordPattern}
 * - Width‑subtyping in unification (a flexible and powerful feature)
 *
 * **The type checker ensures**
 * - All fields have kind `*` (via {@link checkRecordKind})
 * - Field labels match for direct unification
 * - Width‑subtyping works correctly in {@link unifyRecordTypes}
 *
 * **Related**
 * - {@link recordTerm} — term‑level record construction
 * - {@link RecordPattern} — destructuring pattern
 * - {@link projectTerm} — record field access
 * - {@link unifyRecordTypes} — structural unification rule
 *
 * **Examples**
 *
 * Creating a simple record type:
 * ```ts
 * import { recordType, conType, showType } from "system-f-omega";
 *
 * const person = recordType([
 *   ["name", conType("String")],
 *   ["age",  conType("Int")]
 * ]);
 *
 * console.log(showType(person));  // "{name: String, age: Int}"
 * ```
 *
 * Inferring a record type from a term:
 * ```ts
 * import { recordTerm, conTerm, conType, inferType, addType, freshState, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const term = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const ty   = inferType(state, term);
 * console.log(showType(ty.ok));  // "{x: Int}"
 * ```
 *
 * Width‑subtyping example:
 * ```ts
 * import { recordType, conType, isAssignableTo, freshState } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const narrow = recordType([["x", conType("Int")]]);
 * const wide   = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 *
 * console.log(isAssignableTo(state, narrow, wide));  // true
 * ```
 */
export type RecordType = { record: [string, Type][] };

/**
 * A structural **variant (sum) type** of the form:
 * ```
 * < Label₁: τ₁ | Label₂: τ₂ | ... >
 * ```
 *
 * **What it represents**
 * `VariantType` describes tagged unions, also known as:
 * - algebraic sum types
 * - discriminated unions
 * - enum variants with payloads
 *
 * Each case is a pair `[label, type]`, where `type` is the payload type the
 * constructor carries.
 *
 * Example:
 * ```
 * <Left: Int | Right: Bool>
 * ```
 *
 * **Why it's useful**
 * Variants enable rich data modeling:
 * - Optional values (`<None: () | Some: A>`)
 * - Either types (`<Left: L | Right: R>`)
 * - Recursive enums like lists and trees (often using {@link MuType})
 *
 * The type checker uses `VariantType` for:
 * - Structural variant matching in {@link checkPattern}
 * - Type inference for variant injections via {@link inferInjectType}
 * - Exhaustiveness checking with {@link checkExhaustive}
 * - Structural unification in {@link unifyVariants}
 *
 * **How it differs from enums**
 * - Enums (added via {@link addEnum}) are **nominal** and may expand into a
 *   `VariantType` during normalization.
 * - `VariantType` is **structural** and can be written directly.
 *
 * **Related**
 * - {@link injectTerm} — term‑level variant construction
 * - {@link VariantPattern} — pattern for matching a specific case
 * - {@link normalizeType} — expands enums into structural variants
 * - {@link unifyVariants} — unification logic for matching labels and payloads
 *
 * **Examples**
 *
 * Defining a simple Either‑like variant:
 * ```ts
 * import { variantType, conType, showType } from "system-f-omega";
 *
 * const either = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 * console.log(showType(either));  // "<Left: Int | Right: Bool>"
 * ```
 *
 * Matching against a structural variant:
 * ```ts
 * import { variantPattern, varPattern, checkPattern } from "system-f-omega";
 * import { variantType, conType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = variantType([["Some", conType("Int")]]);
 *
 * const pat = variantPattern("Some", varPattern("x"));
 * const res = checkPattern(state, pat, ty);
 * console.log(res.ok.length);  // 1 (binds x: Int)
 * ```
 *
 * Structural variant with multiple fields:
 * ```ts
 * import { variantType, tupleType, conType, showType } from "system-f-omega";
 *
 * const cons = variantType([
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("Int"), conType("List<Int>")])]
 * ]);
 *
 * console.log(showType(cons));  // "<Nil: () | Cons: (Int, List<Int>)>"
 * ```
 */
export type VariantType = { variant: [string, Type][] };

/**
 * A recursive type of the form `μX. body`, representing an **equi‑recursive**
 * fixed point.
 *
 * **What it represents**
 * `MuType` encodes recursive data structures such as:
 * - linked lists
 * - trees
 * - infinite or self‑referential types
 *
 * A `MuType` introduces a type variable (`var`) that the `body` may reference.
 * Conceptually:
 * ```
 * μX. (Int, X)      // a list-like structure
 * μNode. <Leaf: Int | Branch: (Node, Node)>
 * ```
 *
 * The system treats `μ` types **equi‑recursively**, meaning:
 * ```
 * μX. τ  ≡  τ[μX. τ / X]
 * ```
 * so folding and unfolding are not separate runtime constructs but type‑level
 * equivalences driven by the type checker.
 *
 * **Why it's useful**
 * Recursive types are essential for:
 * - Enum expansion (e.g., recursive enums normalized via {@link normalizeType})
 * - Representing ADTs like `List<T>` or `Tree<T>`
 * - Supporting fold/unfold constructs (`foldTerm`, `unfoldTerm`)
 * - Allowing recursive pattern matching on structural variants
 *
 * The type checker uses `MuType` when:
 * - Typechecking `fold`/`unfold` via {@link inferFoldType} and {@link inferUnfoldType}
 * - Preventing infinite cycles in unification (see {@link unifyMuTypes})
 * - Normalizing recursive definitions
 *
 * **Related**
 * - {@link foldTerm} — packs a value into a μ-type
 * - {@link unfoldTerm} — unwraps one layer of a μ-type
 * - {@link unifyMuTypes} — unification rule for recursive types
 * - {@link substituteType} — used to unfold a μ-body
 *
 * **Examples**
 *
 * A simple recursive list type:
 * ```ts
 * import { muType, tupleType, conType, varType, showType } from "system-f-omega";
 *
 * const listInt = muType("L",
 *   tupleType([conType("Int"), varType("L")])
 * );
 * console.log(showType(listInt));  // "μL.(Int, L)"
 * ```
 *
 * A recursive binary tree:
 * ```ts
 * import { muType, variantType, tupleType, conType, varType, showType } from "system-f-omega";
 *
 * const tree = muType("Node",
 *   variantType([
 *     ["Leaf", conType("Int")],
 *     ["Branch", tupleType([varType("Node"), varType("Node")])]
 *   ])
 * );
 * console.log(showType(tree));
 * // "μNode.<Leaf: Int | Branch: (Node, Node)>"
 * ```
 *
 * Unfolding one layer during type checking:
 * ```ts
 * import { unfoldTerm, foldTerm, muType, tupleType, conType, varType, inferType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const listTy = muType("L", tupleType([conType("Int"), varType("L")]));
 *
 * const folded = foldTerm(listTy, { tuple: [conType("1"), { var: "rest" }] });
 * const unfolded = unfoldTerm(folded);
 *
 * console.log(showType(inferType(state, unfolded).ok));
 * // "(Int, μL.(Int, L))"
 * ```
 */
export type MuType = { mu: { var: string; body: Type } };

/**
 * A tuple (product) type of the form `(τ₁, τ₂, …)` or `()` for the empty tuple.
 *
 * **What it represents**
 * `TupleType` describes ordered, fixed‑length collections of values.
 *
 * Examples:
 * - `(Int, Bool)` — a pair
 * - `(A, B, C)` — a triple
 * - `()` — the unit type (zero‑arity tuple)
 *
 * Tuples differ from records because:
 * - **Fields are positional**, not named
 * - **Arity must match exactly** (no width‑subtyping)
 *
 * **Why it's useful**
 * Tuple types are fundamental for:
 * - Representing multi‑value results
 * - Encoding multi‑field enum payloads (e.g. `Cons: (A, List<A>)`)
 * - Pattern matching with {@link TuplePattern}
 * - Projection via {@link tupleProjectTerm}
 *
 * The type checker ensures:
 * - All element types have kind `*` (via {@link checkTupleKind})
 * - Tuple arity matches exactly during unification
 *
 * **Related**
 * - {@link tupleTerm} — term‑level tuple construction
 * - {@link TuplePattern} — pattern for destructuring tuples
 * - {@link tupleProjectTerm} — positional field access
 * - {@link unifyTupleTypes} — unifies tuples element‑wise
 *
 * **Examples**
 *
 * Defining a pair type:
 * ```ts
 * import { tupleType, conType, showType } from "system-f-omega";
 *
 * const pair = tupleType([conType("Int"), conType("Bool")]);
 * console.log(showType(pair));  // "(Int, Bool)"
 * ```
 *
 * Using the unit tuple type:
 * ```ts
 * import { tupleType, showType } from "system-f-omega";
 *
 * const unit = tupleType([]);
 * console.log(showType(unit));  // "()"
 * ```
 *
 * Inferring a tuple type:
 * ```ts
 * import {
 *   tupleTerm, conTerm, conType, inferType,
 *   addType, freshState, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const term = tupleTerm([conTerm("1", conType("Int"))]);
 * const ty = inferType(state, term);
 * console.log(showType(ty.ok));  // "(Int)"
 * ```
 */
export type TupleType = { tuple: Type[] };

/**
 * The **bottom type** `⊥`, representing a type with **no possible values**.
 *
 * **What it represents**
 * `NeverType` is the uninhabited type—there are *no* runtime values of this
 * type. It corresponds to:
 * - Haskell’s `Void`
 * - TypeScript’s `never`
 * - Scala’s `Nothing`
 *
 * In this system, `⊥` arises naturally from:
 * - Empty variants (`variantType([])` normalizes to `⊥`)
 * - Impossible branches in pattern matching
 * - Failed or cyclic type normalization
 *
 * **Why it's useful**
 * The bottom type supports powerful type inference behaviors:
 *
 * - **Subtyping rule:**
 *   `⊥ <: τ` for *all* types `τ`
 *   (an unreachable value can pretend to be anything)
 *
 * - **Unification behavior:**
 *   - `⊥ ~ τ` succeeds when `τ :: *`
 *   - `τ ~ ⊥` only succeeds when `τ` itself is also `⊥`
 *
 * - **Pattern typing:**
 *   A pattern matching on `⊥` need not bind anything—its scrutinee is
 *   unreachable.
 *
 * - **Normalization fallback:**
 *   Cycles or empty variants collapse to `⊥`, preventing infinite loops.
 *
 * **Used in**
 * - {@link isBottom} — bottom detection after normalization
 * - {@link unifyTypes} — asymmetric unification with `⊥`
 * - {@link subsumes} — bottom is always a subtype
 * - {@link inferFoldType} and {@link inferUnfoldType} — recursive enums
 *
 * **Examples**
 *
 * Direct bottom type:
 * ```ts
 * import { neverType, showType } from "system-f-omega";
 *
 * console.log(showType(neverType));  // "⊥"
 * ```
 *
 * Empty structural variant becomes bottom:
 * ```ts
 * import { normalizeType, variantType, freshState, isBottom } from "system-f-omega";
 *
 * const state = freshState();
 * const empty = variantType([]);
 *
 * console.log(isBottom(state, normalizeType(state, empty)));  // true
 * ```
 *
 * Subtyping example:
 * ```ts
 * import { isAssignableTo, neverType, conType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(isAssignableTo(state, neverType, conType("Int")));  // true
 * ```
 */
export type NeverType = { never: null };

/**
 * An existential **meta‑type variable** such as `?0`, `?1`, … used during
 * type inference.
 *
 * **What it represents**
 * `MetaType` stands for an **unknown type** that the type checker will fill in
 * later during unification.
 * It is the type‑level equivalent of a placeholder:
 *
 * - When inferring the type of `λx. x`, the argument type may initially be `?0`
 * - When applying a polymorphic function, `∀A. A → A`, instantiation
 *   produces a fresh meta‑var like `?1`
 *
 * Meta‑variables may unify with:
 * - Concrete types (e.g. `?0 := Int`)
 * - Other type variables (e.g. `?1 := A`)
 * - More complex types (e.g. `?2 := List<?0>`)
 *
 * **Why it's useful**
 * Meta‑types enable:
 * - Hindley–Milner‑style inference
 * - Constraint solving and gradual refinement of unknown types
 * - Instantiation of polymorphic (`forall`) types
 * - Flexible, incremental unification across large expressions
 *
 * The type checker uses them in:
 * - {@link freshMetaVar} — create a fresh `?N`
 * - {@link solveMetaVar} — bind `?N := τ` if no occurs‑check violation
 * - {@link unifyTypes} — flex‑rigid unification rules
 * - {@link applySubstitution} — substitute solved meta‑variables
 *
 * **Related**
 * - {@link VarType} — user‑written type variables
 * - {@link instantiateType} — replaces `∀`‑bound types with new meta‑variables
 * - {@link getUnboundMetas} — detects remaining unsolved meta‑vars
 *
 * **Examples**
 *
 * Creating a fresh meta‑variable during inference:
 * ```ts
 * import { freshState, freshMetaVar, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const m = freshMetaVar(state.meta, starKind);
 * console.log(m.evar);  // "?0"
 * ```
 *
 * Solving a meta‑var during unification:
 * ```ts
 * import { solveMetaVar, freshState, freshMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const m = freshMetaVar(state.meta);
 *
 * solveMetaVar(state, m.evar, conType("Int"));
 * console.log(state.meta.solutions.get(m.evar));  // { con: "Int" }
 * ```
 *
 * Applying substitution:
 * ```ts
 * import { applySubstitution, freshState, freshMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const m = freshMetaVar(state.meta);
 *
 * const subst = new Map([[m.evar, conType("Int")]]);
 * const resolved = applySubstitution(state, subst, m);
 * console.log(resolved.con);  // "Int"
 * ```
 */
export type MetaType = { evar: string };

/**
 * The full set of types supported by the System F‑omega–style type system.
 *
 * **What it represents**
 * `Type` is a *tagged union* of all possible type forms.
 * Every type in the language—primitive, polymorphic, recursive, structural,
 * inferred, or constructed—is represented using one of these variants.
 *
 * The language supports:
 *
 * | Constructor            | Meaning                                             |
 * |------------------------|-----------------------------------------------------|
 * | {@link MetaType}       | Existential meta‑variables (`?N`) for inference     |
 * | {@link VarType}        | Named type variables (`A`, `Self`, `F`)             |
 * | {@link ArrowType}      | Function types (`τ₁ → τ₂`)                           |
 * | {@link ForallType}     | Universal polymorphism (`∀α::κ. τ`)                 |
 * | {@link AppType}        | Type application (`F τ`)                             |
 * | {@link BoundedForallType} | Trait‑bounded polymorphism (`∀α where C. τ`)     |
 * | {@link LamType}        | Type‑level lambda (`λα::κ. τ`)                       |
 * | {@link ConType}        | Concrete type constructors (`Int`, `List`, …)        |
 * | {@link RecordType}     | Structural record types (`{ x: Int, y: Bool }`)     |
 * | {@link VariantType}    | Structural sum types (`<Some: A | None: ()>`)       |
 * | {@link MuType}         | Recursive types (`μα. τ`)                            |
 * | {@link TupleType}      | Tuple/product types (`(τ₁, τ₂, …)`)                  |
 * | {@link NeverType}      | Bottom type (`⊥`)                                    |
 *
 * **Why it's useful**
 * This union is the *entire vocabulary of the typechecker*.
 * Every operation in the system—type inference, subtyping, normalization,
 * unification, pattern checking—relies on analyzing one of these `Type`
 * variants.
 *
 * `Type` enables:
 * - Higher‑kinded polymorphism (System F‑omega)
 * - Trait constraints (similar to typeclasses)
 * - Structural records and variants
 * - Recursive algebraic data types
 * - Meta‑variable–driven type inference
 * - Beta‑reduction of type‑level lambdas
 * - Normalization of enums and type aliases
 *
 * All major typechecker components dispatch on this union, including:
 * - {@link inferType}
 * - {@link checkType}
 * - {@link normalizeType}
 * - {@link unifyTypes}
 * - {@link checkKind}
 *
 * **Examples**
 *
 * A simple function type:
 * ```ts
 * import { arrowType, conType, showType } from "system-f-omega";
 *
 * const fn = arrowType(conType("Int"), conType("Bool"));
 * console.log(showType(fn));  // "(Int → Bool)"
 * ```
 *
 * A polymorphic type:
 * ```ts
 * import { forallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * const poly = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * console.log(showType(poly));  // "∀A::*. (A → A)"
 * ```
 *
 * A recursive list type:
 * ```ts
 * import { muType, tupleType, varType, conType, showType } from "system-f-omega";
 *
 * const list = muType("L", tupleType([conType("Int"), varType("L")]));
 * console.log(showType(list));  // "μL.(Int, L)"
 * ```
 *
 * A structural variant type:
 * ```ts
 * import { variantType, conType, showType } from "system-f-omega";
 *
 * const opt = variantType([
 *   ["None", { tuple: [] }],
 *   ["Some", conType("Int")]
 * ]);
 *
 * console.log(showType(opt));  // "<None: ⊥ | Some: Int>"
 * ```
 *
 * @see {@link Kind} — kinds for type constructors
 * @see {@link inferType} — synthesizes a Type
 * @see {@link checkType} — checks a Type
 * @see {@link unifyTypes} — unification engine
 * @see {@link normalizeType} — fully normalizes a Type
 */
export type Type =
  | MetaType // meta type variable
  | VarType // type variable α
  | ArrowType // τ₁ → τ₂
  | ForallType // ∀α::κ.τ
  | AppType // type application F τ
  | BoundedForallType // trait type
  | LamType // λα::κ.τ
  | ConType // type constant (Int, Bool, etc.)
  | RecordType // {l₁:τ₁, l₂:τ₂, ...}
  | VariantType // <l₁:τ₁ | l₂:τ₂ | ...>
  | MuType // μα.τ - recursive type  List<t> -> { Cons(t, List<t>), Nil }
  | TupleType // tuples
  | NeverType; // bottom type (⊥)

/**
 * A term variable reference, written simply as `x` in expressions.
 *
 * **What it represents**
 * `VarTerm` is the AST node for *using* a variable that is bound in the current
 * term context. It is the term‑level counterpart to {@link VarType}.
 *
 * Examples of term variables:
 * - `x` inside `λx:Int. x`
 * - `f` in an application `f a`
 * - `eqDict` when calling a trait method `eqDict.eq`
 *
 * `VarTerm` itself contains only the variable name; the type is obtained by
 * looking it up in the typing context.
 *
 * **Why it's useful**
 * Variables are fundamental in any lambda calculus or typed language:
 * - Referencing function parameters
 * - Using values introduced by `let` bindings
 * - Accessing trait dictionaries via context lookup
 * - Carrying placeholders when evaluating or matching terms
 *
 * During type inference:
 * - {@link inferVarType} looks up the name in the typing context (`Γ`)
 * - It may resolve to a normal type (`Int`), a dictionary type
 *   (`Dict<Eq, Int>`), or a type expected by the current branch
 *
 * **Related**
 * - {@link inferVarType} — looks up a variable’s type in the context
 * - {@link lamTerm} — introduces a new bound term variable
 * - {@link letTerm} — binds a value to a name in local scope
 * - {@link traitMethodTerm} — uses a dict variable to access methods
 *
 * **Examples**
 *
 * A simple variable reference:
 * ```ts
 * import { varTerm, showTerm } from "system-f-omega";
 *
 * console.log(showTerm(varTerm("x")));  // "x"
 * ```
 *
 * Looking up a variable’s type:
 * ```ts
 * import { freshState, addType, addTerm, varTerm, conTerm, conType, starKind, inferType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "n", conTerm("42", conType("Int"))).ok;
 *
 * const t = inferType(state, varTerm("n"));
 * console.log(t.ok.con);  // "Int"
 * ```
 *
 * Using a variable inside a lambda:
 * ```ts
 * import { lamTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log(showTerm(id));  // "λx:Int.x"
 * ```
 */
export type VarTerm = { var: string };
/**
 * A lambda abstraction `λarg:τ. body`, representing a typed function value.
 *
 * **What it represents**
 * `LamTerm` is the term‑level function constructor of the language.
 * It introduces:
 * - a **term variable** (`arg`)
 * - annotated with a **parameter type** (`type`)
 * - and a **body** that may reference that variable
 *
 * Conceptually:
 * ```
 * λx : Int. x + 1
 * λself : List<Int>. fold(self)
 * ```
 *
 * **Why it's useful**
 * Lambdas define functions—the core computational building block of the
 * language. They are central to:
 * - Function definition and higher‑order programming
 * - Type inference (domain/codomain checking via {@link inferLamType})
 * - Trait methods (method bodies are lambdas)
 * - Polymorphic and trait‑bounded functions inside `Λ` and `∀`
 *
 * The type checker:
 * - Verifies the annotated parameter type is well‑kinded
 * - Extends the context with `arg : type`
 * - Recursively type‑checks the body
 * - Produces an {@link ArrowType} (`type → bodyType`)
 *
 * **Related**
 * - {@link VarTerm} — variables used inside the lambda body
 * - {@link inferLamType} — inference rule for lambdas
 * - {@link arrowType} — constructs the resulting function type
 * - {@link appTerm} — applies a lambda to an argument
 *
 * **Examples**
 *
 * A simple identity function:
 * ```ts
 * import { lamTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log(showTerm(id));  // "λx:Int.x"
 * ```
 *
 * Inferring the type of a lambda:
 * ```ts
 * import {
 *   freshState, addType, inferType,
 *   lamTerm, varTerm, conType, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const ty = inferType(state, id);
 * console.log(showType(ty.ok));  // "(Int → Int)"
 * ```
 *
 * Lambda with a complex body:
 * ```ts
 * import { lamTerm, appTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const twice = lamTerm("f", conType("(Int → Int)"),
 *   lamTerm("x", conType("Int"),
 *     appTerm(varTerm("f"), appTerm(varTerm("f"), varTerm("x")))
 *   )
 * );
 * ```
 */
export type LamTerm = { lam: { arg: string; type: Type; body: Term } };

/**
 * A function application `(callee arg)`.
 *
 * **What it represents**
 * `AppTerm` applies a function term to an argument term.
 * It corresponds directly to writing:
 *
 * ```
 * f x
 * (λx. x) 42
 * add (mul 2 3) 5
 * ```
 *
 * The `callee` must eventually have a function type (`τ₁ → τ₂`), possibly after:
 * - type instantiation (`forall`)
 * - trait‑bounded instantiation (`bounded_forall`)
 * - normalization of type‑level lambdas
 *
 * **Why it's useful**
 * Application is the *core computation step* of the lambda calculus.
 * It is essential for:
 * - Calling user‑defined and anonymous functions
 * - Using values produced by `lamTerm`, `tylamTerm`, or `traitLamTerm`
 * - Interacting with dictionaries in trait method calls
 * - Performing higher‑order functional programming
 *
 * The type checker:
 * - Infers the callee type with {@link inferAppType}
 * - Ensures the argument matches the expected parameter type
 * - Produces the result type of the function
 * - Handles polymorphism, type lambdas, and trait constraints automatically
 *
 * **Related**
 * - {@link lamTerm} — introduces functions to be applied
 * - {@link inferAppType} — main application typing rule
 * - {@link tyappTerm} — type‑level application
 * - {@link traitAppTerm} — trait dictionary‑passing application
 *
 * **Examples**
 *
 * Applying a simple function:
 * ```ts
 * import { lamTerm, appTerm, varTerm, conType, conTerm, inferType, addType, freshState, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const call = appTerm(id, conTerm("42", conType("Int")));
 *
 * console.log(showType(inferType(state, call).ok));  // "Int"
 * ```
 *
 * Higher‑order application:
 * ```ts
 * import { lamTerm, appTerm, varTerm, conType, starKind, freshState, addType, inferType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const applyTwice = lamTerm("f", conType("(Int → Int)"),
 *   lamTerm("x", conType("Int"),
 *     appTerm(varTerm("f"), appTerm(varTerm("f"), varTerm("x")))
 *   )
 * );
 *
 * const inc = lamTerm("n", conType("Int"), varTerm("n")); // pretend increment
 * const call = appTerm(applyTwice, inc);
 * ```
 *
 * Using `AppTerm` inside a match or let:
 * ```ts
 * import { appTerm, varTerm } from "system-f-omega";
 *
 * const expr = appTerm(varTerm("f"), varTerm("y"));
 * ```
 */
export type AppTerm = { app: { callee: Term; arg: Term } };

/**
 * A **type-level lambda abstraction** `Λα::κ. body`, introducing a polymorphic
 * type parameter.
 *
 * **What it represents**
 * `TyLamTerm` is the term‑level construct for *explicit* type abstraction.
 * It corresponds to writing:
 *
 * ```
 * ΛA::*. e
 * ```
 *
 * At runtime, nothing happens—this is purely a type‑level construct that enables
 * parametric polymorphism.
 * At typechecking time, it produces a {@link ForallType}.
 *
 * Example (polymorphic identity):
 * ```
 * ΛA::*. λx:A. x
 * ```
 *
 * **Why it's useful**
 * Type lambdas allow you to define **explicitly polymorphic functions**, similar
 * to System F or GHC's `forall`/`/\` syntax. This gives:
 *
 * - First‑class polymorphism
 * - Control over type abstraction boundaries
 * - The ability to pass polymorphic functions as values
 *
 * The type checker:
 * - Extends the type context with the new type variable (`var :: kind`)
 * - Infers the type of the body
 * - Wraps the result into a {@link ForallType}
 *
 * **Related**
 * - {@link tyappTerm} — applies a type argument to a `TyLamTerm`
 * - {@link inferTylamType} — inference rule for type lambdas
 * - {@link ForallType} — type of a `TyLamTerm`
 * - {@link Kind} — kinds classify type parameters
 *
 * **Examples**
 *
 * A simple polymorphic identity function:
 * ```ts
 * import {
 *   tylamTerm, lamTerm, varTerm, varType,
 *   starKind, inferType, freshState, addType, showType
 * } from "system-f-omega";
 *
 * const state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = tylamTerm("A", starKind,
 *   lamTerm("x", varType("A"), varTerm("x"))
 * );
 *
 * console.log(showType(inferType(state, id).ok));
 * // "∀A::*. (A → A)"
 * ```
 *
 * Creating a polymorphic constant function:
 * ```ts
 * import { tylamTerm, lamTerm, varTerm, varType, starKind } from "system-f-omega";
 *
 * const constFn = tylamTerm("A", starKind,
 *   tylamTerm("B", starKind,
 *     lamTerm("x", varType("A"),
 *       lamTerm("y", varType("B"), varTerm("x"))
 *     )
 *   )
 * );
 * // ΛA::*. ΛB::*. λx:A. λy:B. x
 * ```
 *
 * Applying a type lambda:
 * ```ts
 * import { tylamTerm, tyappTerm, varTerm, lamTerm, varType, starKind, conType, inferType, freshState, addType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const poly = tylamTerm("T", starKind, lamTerm("x", varType("T"), varTerm("x")));
 * const inst = tyappTerm(poly, conType("Bool"));
 *
 * console.log(showType(inferType(state, inst).ok));  // "(Bool → Bool)"
 * ```
 */
export type TyLamTerm = { tylam: { var: string; kind: Kind; body: Term } };

/**
 * A **type application** `term [T]`, applying a polymorphic term to a type.
 *
 * **What it represents**
 * `TyAppTerm` is the term‑level construct for instantiating a polymorphic
 * function with a concrete type argument.
 * It corresponds to writing:
 *
 * ```
 * (ΛA::*. e) [Int]
 * ```
 *
 * This is how explicitly polymorphic functions (introduced via
 * {@link TyLamTerm}) are specialized to concrete types during evaluation.
 *
 * **Why it's useful**
 * Type application enables:
 * - Explicit instantiation of `∀`‑polymorphic terms
 * - More predictable type inference (important in System F)
 * - Passing polymorphic functions as first‑class values
 * - Controlling instantiation order in higher‑rank polymorphism
 *
 * The type checker:
 * - Ensures the callee has a polymorphic type (`∀α::κ. τ`)
 * - Verifies that the provided type has the correct kind
 * - Substitutes the type argument into the body of the forall
 * (via {@link inferTyappType})
 *
 * **Related**
 * - {@link TyLamTerm} — introduces type parameters
 * - {@link inferTyappType} — typing rule for type application
 * - {@link forallType} — the type of a polymorphic value
 * - {@link AppTerm} — term‑level function application
 *
 * **Examples**
 *
 * Applying a polymorphic identity function:
 * ```ts
 * import {
 *   tylamTerm, lamTerm, varTerm, varType, starKind,
 *   tyappTerm, conType, inferType, freshState, addType, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const polyId =
 *   tylamTerm("A", starKind, lamTerm("x", varType("A"), varTerm("x")));
 *
 * const inst = tyappTerm(polyId, conType("Int"));
 * console.log(showType(inferType(state, inst).ok));  // "(Int → Int)"
 * ```
 *
 * Higher‑rank instantiation:
 * ```ts
 * import { tyappTerm, conType } from "system-f-omega";
 *
 * const poly = { var: "polyId" };   // assume polyId :: ∀A::*. A → A
 * const inst = tyappTerm(poly, conType("Bool"));
 * // polyId[Bool]
 * ```
 *
 * Using type application in a nested term:
 * ```ts
 * import { appTerm, tyappTerm, varTerm, conType } from "system-f-omega";
 *
 * // f [Int] x
 * const expr = appTerm(tyappTerm(varTerm("f"), conType("Int")), varTerm("x"));
 * ```
 */
export type TyAppTerm = { tyapp: { term: Term; type: Type } };

/**
 * A typed constant or literal value, such as `"42" : Int` or `"true" : Bool`.
 *
 * **What it represents**
 * `ConTerm` is the AST node for **literal values** and **nullary constructors**.
 * It pairs:
 * - `name` — the literal or constructor name
 * - `type` — its explicitly annotated type
 *
 * Examples:
 * - `42 : Int`
 * - `true : Bool`
 * - `None : Option<T>`
 *
 * **Why it's useful**
 * Constants provide:
 * - Base values for computation
 * - Tagged enum constructors (e.g., `"None"` or `"Nil"`)
 * - Known types during inference (no lookup required)
 *
 * The type checker:
 * - Simply returns the annotated type (via {@link inferType})
 * - Validates kind correctness through {@link checkType} and constructor usage
 *
 * **Related**
 * - {@link AppTerm} — applying functions to constants
 * - {@link ConPattern} — pattern‑matching on specific constructors
 * - {@link injectTerm} — variant constructors with payloads
 *
 * **Examples**
 *
 * A basic integer literal:
 * ```ts
 * import { conTerm, conType, inferType, freshState, addType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const lit = conTerm("42", conType("Int"));
 * console.log(inferType(state, lit).ok.con);  // "Int"
 * ```
 *
 * A boolean literal:
 * ```ts
 * import { conTerm, conType } from "system-f-omega";
 *
 * const t = conTerm("true", conType("Bool"));
 * ```
 *
 * Using a constant in a record:
 * ```ts
 * import { recordTerm, conTerm, conType } from "system-f-omega";
 *
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))]
 * ]);
 * ```
 */
export type ConTerm = { con: { name: string; type: Type } };

/**
 * A `let` binding: `let name = value in body`.
 *
 * **What it represents**
 * `LetTerm` introduces a **local variable** bound to a value.
 * It corresponds to the common functional‑language construct:
 *
 * ```
 * let x = e1 in e2
 * ```
 *
 * This expression:
 * 1. Evaluates or typechecks `value`
 * 2. Extends the context with `name : type(value)`
 * 3. Typechecks `body` under the extended context
 * 4. Produces the type of `body`
 *
 * Let‑bindings are **non‑recursive**: the `value` cannot refer to `name`.
 *
 * **Why it's useful**
 * Local bindings improve expressiveness:
 * - Introduce intermediate values
 * - Improve clarity by naming subexpressions
 * - Support step‑by‑step type inference
 *
 * The type checker:
 * - Infers the type of `value` via {@link inferType}
 * - Extends the context with `name : inferredType`
 * - Typechecks the body in that extended environment (via {@link inferLetType})
 *
 * **Related**
 * - {@link inferLetType} — inference rule for let‑bindings
 * - {@link varTerm} — referencing a let‑bound variable
 * - {@link lamTerm} — function abstraction, another binder
 *
 * **Examples**
 *
 * Simple let‑binding:
 * ```ts
 * import {
 *   letTerm, conTerm, conType, varTerm,
 *   inferType, addType, starKind, freshState, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const expr = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * console.log(showType(inferType(state, expr).ok));  // "Int"
 * ```
 *
 * Let‑binding inside an expression:
 * ```ts
 * import {
 *   letTerm, lamTerm, varTerm, conType, appTerm,
 *   inferType, addType, freshState, starKind
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * // let f = λx:Int. x in f 5
 * const f = lamTerm("x", conType("Int"), varTerm("x"));
 * const expr = letTerm("f", f, appTerm(varTerm("f"), conTerm("5", conType("Int"))));
 *
 * console.log(inferType(state, expr).ok.con);  // "Int"
 * ```
 *
 * Nested let‑bindings:
 * ```ts
 * import { letTerm, conTerm, varTerm, conType } from "system-f-omega";
 *
 * const nested =
 *   letTerm("x", conTerm("1", conType("Int")),
 *     letTerm("y", conTerm("2", conType("Int")),
 *       varTerm("x")
 *     )
 *   );
 * ```
 */
export type LetTerm = { let: { name: string; value: Term; body: Term } };

/**
 * A record value `{ label = value, ... }` with named fields.
 *
 * **What it represents**
 * `RecordTerm` corresponds to constructing a record at the term level:
 *
 * ```
 * { x = 1, y = true }
 * { point = (x, y) }
 * ```
 *
 * Each field is a pair `[label, term]`.
 * The order of fields does not matter—record types are **structural**.
 *
 * **Why it's useful**
 * Records allow you to build structured data with named fields.
 * They work well for:
 * - Configuration objects
 * - Named arguments
 * - Data structures (points, vectors, AST nodes)
 *
 * The type checker:
 * - Infers each field’s type individually (via {@link inferRecordType})
 * - Constructs a {@link RecordType} with field names and inferred types
 * - Supports field projection (see {@link ProjectTerm})
 *
 * **Related**
 * - {@link recordType} — type-level representation of records
 * - {@link inferRecordType} — inference rule for record terms
 * - {@link projectTerm} — accessing a record’s field
 * - {@link RecordPattern} — pattern matching on record fields
 *
 * **Examples**
 *
 * A simple record value:
 * ```ts
 * import { recordTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 *
 * console.log(showTerm(rec));  // "{x = 1, y = true}"
 * ```
 *
 * Inferring the type of a record:
 * ```ts
 * import {
 *   recordTerm, conTerm, conType,
 *   addType, freshState, inferType, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 *
 * console.log(showType(inferType(state, rec).ok));
 * // "{x: Int, y: Bool}"
 * ```
 *
 * Nested record fields:
 * ```ts
 * import { recordTerm, tupleTerm, varTerm } from "system-f-omega";
 *
 * const term = recordTerm([
 *   ["point", tupleTerm([varTerm("x"), varTerm("y")])]
 * ]);
 * // { point = (x, y) }
 * ```
 */
export type RecordTerm = { record: [string, Term][] };

/**
 * A record field projection `record.label`.
 *
 * **What it represents**
 * `ProjectTerm` extracts a field from a record value, exactly like:
 *
 * ```
 * { x = 1, y = true }.x   // result: 1
 * p.y
 * user.name
 * ```
 *
 * The term stores:
 * - `record` — the record expression being accessed
 * - `label` — the field name to retrieve
 *
 * **Why it's useful**
 * Field projection is essential for working with structured data.
 * It enables:
 * - Accessing fields in records
 * - Retrieving components of nested data structures
 * - Using records as lightweight structs or objects
 *
 * The type checker:
 * - Infers the type of `record` (via {@link inferProjectType})
 * - Ensures it is a {@link RecordType}
 * - Looks up the requested field
 * - Returns the corresponding field type
 *
 * Projection fails with:
 * - `not_a_record` if the scrutinee is not a record type
 * - `missing_field` if the record lacks the given label
 *
 * **Related**
 * - {@link recordTerm} — builds record values
 * - {@link RecordType} — type form for records
 * - {@link inferProjectType} — typing rule for projections
 * - {@link RecordPattern} — destructuring counterpart in patterns
 *
 * **Examples**
 *
 * Basic projection:
 * ```ts
 * import {
 *   recordTerm, conTerm, conType, projectTerm,
 *   freshState, addType, inferType, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 *
 * console.log(showType(inferType(state, proj).ok));  // "Int"
 * ```
 *
 * Nested projection:
 * ```ts
 * import { recordTerm, tupleTerm, projectTerm, varTerm } from "system-f-omega";
 *
 * const rec = recordTerm([
 *   ["pair", tupleTerm([varTerm("a"), varTerm("b")])]
 * ]);
 *
 * const field = projectTerm(rec, "pair");
 * // Accesses the tuple stored under "pair"
 * ```
 *
 * Projection failure case:
 * ```ts
 * import { projectTerm, varTerm, inferType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const bad = projectTerm(varTerm("x"), "y");
 * const res = inferType(state, bad);
 *
 * console.log(showError(res.err));  // "Unbound identifier: x" or "Not a record type: ..."
 * ```
 */
export type ProjectTerm = { project: { record: Term; label: string } };

/**
 * A **variant injection** `<label = value> as VariantType`, constructing a value
 * of a sum type (like `Some(42)` or `Left("err")`).
 *
 * **What it represents**
 * `InjectTerm` builds a tagged union value.
 * It corresponds to writing:
 *
 * ```
 * <Some = 42> as Option<Int>
 * <Left = "err"> as Either<String, Int>
 * ```
 *
 * The node stores:
 * - `label` — the constructor name (e.g. `"Some"`, `"Left"`)
 * - `value` — the payload term
 * - `variant_type` — the expected type of the variant (nominal or structural)
 *
 * The type checker uses this to determine which case of the variant is being
 * constructed and ensures the payload type matches the constructor's field type.
 *
 * **Why it's useful**
 * Variant injection is central for:
 * - Creating values of algebraic data types (ADTs)
 * - Working with enums defined via {@link addEnum}
 * - Constructing structural variants defined via {@link VariantType}
 * - Building recursive types (lists, trees) using {@link MuType}
 *
 * The type checker:
 * - Handles both **nominal enums** and **structural variants**
 * - Looks up the constructor label inside the variant definition
 * - Ensures the payload term matches the case’s field type
 *   (via {@link inferInjectType})
 * - Produces the variant’s overall type
 *
 * **Related**
 * - {@link VariantType} — structural variant form
 * - {@link addEnum} — introduces nominal variant constructors
 * - {@link inferInjectType} — inference rule for injection
 * - {@link VariantPattern} — pattern‑matching counterpart
 *
 * **Examples**
 *
 * Injecting into a nominal enum:
 * ```ts
 * import {
 *   injectTerm, conTerm, conType, appType,
 *   addEnum, addType, freshState, starKind,
 *   inferType, showType
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const term = injectTerm("Some", conTerm("42", conType("Int")),
 *   appType(conType("Option"), conType("Int"))
 * );
 *
 * console.log(showType(inferType(state, term).ok));  // "Option<Int>"
 * ```
 *
 * Injecting into a structural variant:
 * ```ts
 * import { injectTerm, variantType, conTerm, conType, inferType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const variantTy = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 *
 * const inj = injectTerm("Left", conTerm("1", conType("Int")), variantTy);
 * console.log(inferType(state, inj).ok.variant);
 * // [["Left", Int], ["Right", Bool]]
 * ```
 *
 * Injecting a unit case (zero‑payload constructor):
 * ```ts
 * import { injectTerm, unitValue, appType, conType } from "system-f-omega";
 *
 * const none = injectTerm("None", unitValue, appType(conType("Option"), conType("Bool")));
 * ```
 */
export type InjectTerm = {
  inject: { label: string; value: Term; variant_type: Type };
};

/**
 * A pattern match expression:
 *
 * ```
 * match scrutinee {
 *   pattern₁ => body₁
 *   pattern₂ => body₂
 *   ...
 * }
 * ```
 *
 * **What it represents**
 * `MatchTerm` performs **destructuring** based on the structure of a value.
 * Each case consists of:
 * - a **pattern** (record, variant, tuple, variable, etc.)
 * - a **body** evaluated when that pattern matches
 *
 * Example:
 * ```
 * match xs {
 *   None      => 0
 *   Some(x)   => x
 * }
 * ```
 *
 * **Why it's useful**
 * Pattern matching is one of the most expressive features of typed functional
 * languages. It enables:
 * - Deconstructing structured data (tuples, records, variants)
 * - Binding variables inside patterns
 * - Exhaustiveness checking to ensure all cases are covered
 * - Writing concise, declarative control flow
 *
 * The type checker:
 * - Infers the type of the scrutinee
 * - Checks each pattern against its type using {@link checkPattern}
 * - Infers the type of each body under the extended context
 * - Ensures all branches produce compatible result types
 *   (via {@link inferMatchType})
 * - Ensures the match is **exhaustive** using {@link checkExhaustive}
 *
 * **Related**
 * - {@link Pattern} — all supported pattern forms
 * - {@link checkPattern} — validates each pattern
 * - {@link inferMatchType} — core match typing rule
 * - {@link checkExhaustive} — exhaustiveness analysis
 * - {@link VariantPattern}, {@link RecordPattern}, {@link TuplePattern}
 *
 * **Examples**
 *
 * Matching a simple variant:
 * ```ts
 * import {
 *   matchTerm, variantPattern, varPattern, conTerm, conType,
 *   addEnum, addType, freshState, inferType, appType, starKind, showType
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 *
 * const match = matchTerm(scrut, [
 *   [variantPattern("None", varPattern("_")), conTerm("0", conType("Int"))],
 *   [variantPattern("Some", varPattern("x")), varTerm("x")]
 * ]);
 *
 * console.log(showType(inferType(state, match).ok));  // "Int"
 * ```
 *
 * Using record patterns:
 * ```ts
 * import { matchTerm, recordPattern, varPattern, recordTerm, conTerm, conType } from "system-f-omega";
 *
 * const scrut = recordTerm([["x", conTerm("1", conType("Int"))]]);
 *
 * const match = matchTerm(scrut, [
 *   [recordPattern([["x", varPattern("n")]]), varTerm("n")]
 * ]);
 * ```
 *
 * Tuple pattern match:
 * ```ts
 * import { matchTerm, tuplePattern, varPattern, tupleTerm, conTerm, conType } from "system-f-omega";
 *
 * const match = matchTerm(
 *   tupleTerm([conTerm("1", conType("Int")), conTerm("2", conType("Int"))]),
 *   [[tuplePattern([varPattern("a"), varPattern("b")]), varTerm("a")]]
 * );
 * ```
 */
export type MatchTerm = {
  match: { scrutinee: Term; cases: [Pattern, Term][] };
};

/**
 * A **fold** operation `fold[μX. body](term)` used to *pack* a value into a
 * recursive `μ` type.
 *
 * **What it represents**
 * `FoldTerm` wraps a term into a recursive type defined by {@link MuType}.
 * It corresponds to the constructor:
 *
 * ```
 * fold[μX. τ](e)
 * ```
 *
 * The idea is:
 * - The annotation `type` *must be* a `μ` type: `μX. τ`
 * - The inner `term` must have the *unfolded* type: `τ[μX. τ / X]`
 *
 * Example:
 * ```
 * fold[List<Int>](Cons(1, Nil))
 * ```
 *
 * **Why it's useful**
 * Folding is essential when working with **recursive algebraic data types**:
 * - Lists, trees, nested variants, etc.
 * - Recursive enums created via {@link addEnum}
 *
 * In this type system, `μ` is **equi‑recursive**, but explicit `fold` and
 * `unfold` terms help guide and check recursive structure.
 *
 * The type checker:
 * - Ensures `type` is a valid `μ` type
 * - Unfolds it using {@link substituteType}
 * - Checks the inner term against the unfolded type
 *   (via {@link inferFoldType})
 * - Returns the annotated `μ` type
 *
 * **Related**
 * - {@link MuType} — the recursive type form
 * - {@link unfoldTerm} — inverse operation
 * - {@link inferFoldType} — typing rule for `fold`
 * - {@link substituteType} — used to compute the unfolded body
 *
 * **Examples**
 *
 * Folding a simple list node:
 * ```ts
 * import {
 *   muType, tupleType, conType, foldTerm,
 *   inferType, freshState, addType, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", { star: null }).ok;
 *
 * // μL.(Int, L)
 * const listTy = muType("L", tupleType([conType("Int"), { var: "L" }]));
 *
 * // fold[List](1, tail)
 * const node = foldTerm(listTy, {
 *   tuple: [conTerm("1", conType("Int")), { var: "tail" }]
 * });
 *
 * console.log(showType(inferType(state, node).ok));  // "μL.(Int, L)"
 * ```
 *
 * Folding a Nil constructor (unit case in a recursive enum):
 * ```ts
 * import { foldTerm, unitValue } from "system-f-omega";
 *
 * const nilFolded = foldTerm(listTy, unitValue);
 * ```
 *
 * Using fold inside a pattern‑built recursive structure:
 * ```ts
 * import { foldTerm, injectTerm, appType, conType } from "system-f-omega";
 *
 * // fold[List<Int>](<Nil=()> as List<Int>)
 * const nil = foldTerm(
 *   appType(conType("List"), conType("Int")),
 *   injectTerm("Nil", { tuple: [] }, appType(conType("List"), conType("Int")))
 * );
 * ```
 */
export type FoldTerm = { fold: { type: Type; term: Term } };

/**
 * An **unfold** operation `unfold(term)` used to *unwrap* one layer of a
 * recursive `μ` type.
 *
 * **What it represents**
 * `UnfoldTerm` performs the inverse of {@link FoldTerm}.
 * Given a term whose type is a recursive type:
 *
 * ```
 * μX. body
 * ```
 *
 * `unfold(term)` produces a value of the unfolded type:
 *
 * ```
 * body[μX. body / X]
 * ```
 *
 * Conceptually:
 * - `fold` packs a value into a recursive type
 * - `unfold` unpacks one recursive layer
 *
 * Example:
 * ```
 * unfold(fold[List](Cons(1, xs)))  =>  (1, xs)
 * ```
 *
 * **Why it's useful**
 * Unfolding is essential for:
 * - Pattern matching on recursive variants
 * - Accessing the internal structure of `μ`‑types
 * - Implementing recursive algorithms on lists or trees
 * - Normalizing nested recursive enums
 *
 * The type checker:
 * - Infers the type of `term`
 * - Ensures it is of the form `μX. body`
 * - Substitutes the recursive type into `body`
 *   (via {@link substituteType})
 * - Produces the unfolded result type (via {@link inferUnfoldType})
 *
 * **Related**
 * - {@link FoldTerm} — the inverse (packing)
 * - {@link MuType} — recursive type form
 * - {@link inferUnfoldType} — typing rule for unfolding
 * - {@link substituteType} — used for recursive expansion
 *
 * **Examples**
 *
 * Unfolding a list node:
 * ```ts
 * import {
 *   muType, tupleType, conType, varTerm,
 *   foldTerm, unfoldTerm, inferType,
 *   addType, freshState, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * // μL.(Int, L)
 * const listTy = muType("L", tupleType([conType("Int"), { var: "L" }]));
 *
 * const folded = foldTerm(listTy, {
 *   tuple: [conTerm("1", conType("Int")), varTerm("rest")]
 * });
 *
 * const unfolded = unfoldTerm(folded);
 * console.log(showType(inferType(state, unfolded).ok));
 * // "(Int, μL.(Int, L))"
 * ```
 *
 * Unfolding a Nil branch:
 * ```ts
 * import { unfoldTerm, injectTerm, appType, conType, unitValue } from "system-f-omega";
 *
 * const nil = injectTerm("Nil", unitValue, appType(conType("List"), conType("Int")));
 * const unfoldedNil = unfoldTerm(nil);  // Works once wrapped in fold/list context
 * ```
 *
 * Using unfold inside recursion:
 * ```ts
 * const dec = unfoldTerm(varTerm("node"));
 * // Typically used in match expressions to inspect recursive structures
 * ```
 */
export type UnfoldTerm = { unfold: Term };

/**
 * A tuple value `(e₁, e₂, …)` or `()` for the empty/Unit tuple.
 *
 * **What it represents**
 * `TupleTerm` constructs a runtime tuple with ordered fields.
 * Examples:
 * - `(1, true)`
 * - `(x, (y, z))`
 * - `()` — the **unit value**, the only inhabitant of the unit type
 *
 * Each element is itself a full `Term`, allowing nested tuples and
 * higher‑order structures.
 *
 * **Why it's useful**
 * Tuples provide:
 * - Lightweight product types without labels
 * - Multi‑value return patterns
 * - Payloads for variant constructors (e.g. `Cons(hd, tl)`)
 * - Structured matching via {@link TuplePattern}
 *
 * The type checker:
 * - Infers each element’s type independently via {@link inferTupleType}
 * - Produces a {@link TupleType} of the same arity
 * - Enforces exact arity during projection or pattern matching
 *
 * **Related**
 * - {@link TupleType} — type-level representation of tuples
 * - {@link tupleProjectTerm} — positional projection `tup.i`
 * - {@link TuplePattern} — pattern for destructuring tuple values
 * - {@link inferTupleType} — typing rule for tuple terms
 *
 * **Examples**
 *
 * A simple tuple value:
 * ```ts
 * import { tupleTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const pair = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 *
 * console.log(showTerm(pair));  // "(1, true)"
 * ```
 *
 * Inferring the type of a tuple:
 * ```ts
 * import {
 *   tupleTerm, conTerm, conType,
 *   addType, freshState, starKind,
 *   inferType, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const term = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 *
 * console.log(showType(inferType(state, term).ok));  // "(Int, Bool)"
 * ```
 *
 * A nested tuple:
 * ```ts
 * import { tupleTerm, varTerm } from "system-f-omega";
 *
 * const nested = tupleTerm([
 *   varTerm("x"),
 *   tupleTerm([varTerm("y"), varTerm("z")])
 * ]);
 * // (x, (y, z))
 * ```
 */
export type TupleTerm = { tuple: Term[] };

/**
 * A tuple projection `tuple.index`, extracting the *n*-th element from a tuple.
 *
 * **What it represents**
 * `TupleProjectTerm` accesses a specific position inside a tuple value, similar
 * to:
 *
 * ```
 * (a, b, c).0   // => a
 * (x, y).1      // => y
 * ```
 *
 * The node stores:
 * - `tuple` — the tuple expression being projected
 * - `index` — a zero-based index (`0` = first element)
 *
 * **Why it's useful**
 * Tuple projection allows:
 * - Extracting components of tuple values
 * - Working with multi‑return functions encoded as tuples
 * - Decomposing constructor payloads (e.g. list nodes `(hd, tl)`)
 * - Lightweight product operations without named fields
 *
 * The type checker:
 * - Infers the type of the tuple expression
 * - Normalizes it to a {@link TupleType}
 * - Ensures the index is within bounds
 * - Returns the type of the selected tuple element
 *   (via {@link inferTupleProjectType})
 *
 * Errors include:
 * - `not_a_tuple` if the scrutinee is not a tuple type
 * - `tuple_index_out_of_bounds` if `index` is invalid
 *
 * **Related**
 * - {@link TupleTerm} — constructs tuple values
 * - {@link TupleType} — type of tuple expressions
 * - {@link inferTupleProjectType} — typing rule for projections
 * - {@link tuplePattern} — pattern matching counterpart
 *
 * **Examples**
 *
 * Basic projection:
 * ```ts
 * import {
 *   tupleTerm, conTerm, conType,
 *   tupleProjectTerm, inferType,
 *   freshState, addType, starKind, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tup = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 *
 * const proj = tupleProjectTerm(tup, 0);
 * console.log(showType(inferType(state, proj).ok));  // "Int"
 * ```
 *
 * Out‑of‑bounds projection:
 * ```ts
 * import { tupleProjectTerm, tupleTerm, conTerm, conType, inferType, freshState, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int"))]);
 * const bad = tupleProjectTerm(tup, 1);
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Tuple index out of bounds: Tuple: (Int,) Index: 1"
 * ```
 *
 * Nested projection:
 * ```ts
 * import { tupleProjectTerm, tupleTerm, varTerm } from "system-f-omega";
 *
 * const proj = tupleProjectTerm(
 *   tupleTerm([varTerm("a"), tupleTerm([varTerm("b"), varTerm("c")])]),
 *   1
 * );
 * // projects the nested tuple (b, c)
 * ```
 */
export type TupleProjectTerm = {
  tuple_project: { tuple: Term; index: number };
};

/**
 * A **trait dictionary** value:
 *
 * ```
 * dict Trait<Type> { method1 = impl1, method2 = impl2, ... }
 * ```
 *
 * **What it represents**
 * `DictTerm` packages concrete implementations of a trait’s methods for a
 * specific type.
 * Dictionaries are how the system **passes trait evidence** during type
 * checking—similar to *typeclass dictionaries* in Haskell.
 *
 * Example:
 * ```
 * dict Eq<Int> {
 *   eq = λx:Int. λy:Int. ...
 * }
 * ```
 *
 * A dictionary contains:
 * - `trait`: the trait name (`"Eq"`, `"Ord"`, `"Show"`, etc.)
 * - `type`: the type the trait is implemented for (`Int`, `List<A>`, …)
 * - `methods`: the concrete implementations of the trait’s required methods
 *
 * **Why it's useful**
 * Dictionaries allow traits to be:
 * - **Resolved dynamically** at type‑checking time
 * - **Passed implicitly or explicitly** via {@link TraitAppTerm}
 * - **Stored, referenced, and used** just like ordinary values
 *
 * The type checker uses dictionaries to:
 * - Validate method implementations (via {@link inferDictType})
 * - Supply evidence for trait‑bounded polymorphism (via {@link checkTraitConstraints})
 * - Support method projection (`d.eq`) via {@link traitMethodTerm}
 *
 * **Related**
 * - {@link traitImplBinding} — stores a dictionary as a trait implementation
 * - {@link inferDictType} — validates the dictionary against the trait definition
 * - {@link traitMethodTerm} — accesses dictionary methods
 * - {@link TraitConstraint} — constraints requiring a dictionary
 *
 * **Examples**
 *
 * A simple Eq<Int> dictionary:
 * ```ts
 * import {
 *   dictTerm, lamTerm, varTerm, conTerm, conType
 * } from "system-f-omega";
 *
 * const eqIntDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"),
 *            lamTerm("y", conType("Int"),
 *              conTerm("true", conType("Bool"))
 *            )
 *   )]
 * ]);
 *
 * // dict Eq<Int> { eq = λx:Int. λy:Int. true }
 * ```
 *
 * Using the dictionary as evidence for trait application:
 * ```ts
 * import { traitAppTerm, conType } from "system-f-omega";
 *
 * const app = traitAppTerm({ var: "f" }, conType("Int"), [eqIntDict]);
 * ```
 *
 * Validating a dictionary:
 * ```ts
 * import {
 *   inferDictType, freshState, addTraitDef, conType,
 *   arrowType, varType, starKind
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), arrowType(varType("A"), conType("Bool")))]
 * ]).ok;
 *
 * inferDictType(state, eqIntDict);  // ok
 * ```
 */
export type DictTerm = {
  dict: {
    trait: string;
    type: Type;
    methods: [string, Term][]; // method implementations
  };
};

/**
 * A **trait method access** `dict.method`, extracting a method implementation
 * from a trait dictionary.
 *
 * **What it represents**
 * `TraitMethodTerm` is how the language *calls* a trait method using explicit
 * dictionary evidence.
 *
 * Example:
 * ```
 * eqDict.eq     // lookup the 'eq' method inside an Eq<T> dictionary
 * showDict.show // access a Show<T> method
 * ```
 *
 * The node stores:
 * - `dict`: a term producing a dictionary (either a variable or a `DictTerm`)
 * - `method`: the method name to project (e.g. `"eq"`, `"map"`)
 *
 * **Why it's useful**
 * Trait method projection is the essential mechanism behind:
 * - **Dictionary‑passing** trait implementations
 * - Resolving trait methods after constraint solving
 * - Calling trait operations explicitly when needed
 *
 * During type checking:
 * - The type of `dict` must be a dictionary for some trait `T` applied to a type `A`
 * - The method name must exist in the trait definition (via {@link inferTraitMethodType})
 * - The returned type is the method's type with the trait’s type parameter substituted
 *
 * **Related**
 * - {@link DictTerm} — dictionary providing the methods
 * - {@link inferTraitMethodType} — typing rule for method projection
 * - {@link traitImplBinding} — stores named dictionaries in the context
 * - {@link TraitConstraint} — requires dictionaries during instantiation
 *
 * **Examples**
 *
 * Accessing a method from a dictionary variable:
 * ```ts
 * import {
 *   traitMethodTerm, varTerm, inferType,
 *   freshState, addType, addTraitDef, addDict,
 *   dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(conType("A"), arrowType(conType("A"), conType("Bool")))]
 * ]).ok;
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"),
 *            lamTerm("y", conType("Int"),
 *              conTerm("true", conType("Bool"))
 *            ))]
 * ]);
 *
 * state = addDict(state, "eqInt", eqDict).ok;
 *
 * const method = traitMethodTerm(varTerm("eqInt"), "eq");
 * console.log(showType(inferType(state, method).ok));
 * // "(Int → (Int → Bool))"
 * ```
 *
 * Accessing a method from a concrete dictionary literal:
 * ```ts
 * import { traitMethodTerm, dictTerm, conType } from "system-f-omega";
 *
 * const d = dictTerm("Show", conType("Int"), [
 *   ["show", { var: "impl" }]
 * ]);
 *
 * const showMethod = traitMethodTerm(d, "show");
 * // Accesses the 'show' method stored in the dictionary
 * ```
 *
 * Using a projected method in an application:
 * ```ts
 * import { appTerm, traitMethodTerm, varTerm } from "system-f-omega";
 *
 * const cmp = appTerm(traitMethodTerm(varTerm("eqInt"), "eq"), varTerm("x"));
 * ```
 */
export type TraitMethodTerm = {
  trait_method: {
    dict: Term; // dictionary/evidence
    method: string;
  };
};

/**
 * A **trait lambda**:
 *
 * ```
 * ΛtypeVar::kind where constraints. body
 * ```
 *
 * introducing both:
 * - a **type parameter** (like a polymorphic lambda), and
 * - a **dictionary variable** providing evidence for required traits.
 *
 * **What it represents**
 * `TraitLamTerm` is the term‑level constructor for *bounded polymorphism*
 * (System F + typeclasses).
 *
 * It corresponds to writing something like:
 *
 * ```
 * ΛSelf::* where Eq<Self>. λd:Eq<Self>. body
 * ```
 *
 * but with dictionaries passed implicitly by the type system.
 *
 * A trait lambda binds:
 * - `type_var` — the polymorphic type parameter (`"Self"` in Eq<Self>)
 * - `kind` — the parameter kind (`*` or higher‑kinded)
 * - `constraints` — trait bounds (e.g. `Eq<Self>`, `Functor<F>`)
 * - `trait_var` — the **dictionary variable** giving access to the trait methods
 * - `body` — a term that uses both `type_var` and `trait_var`
 *
 * **Why it's useful**
 * Trait lambdas express *generic functions that require trait implementations*.
 *
 * They are crucial for:
 * - Writing trait‑polymorphic functions
 * - Encoding Haskell‑style typeclass methods
 * - Allowing implicit dictionary resolution in applications
 * - Representing bounded polymorphism in System‑F‑omega
 *
 * During type checking:
 * - The context is extended with `type_var :: kind`
 * - A dictionary binding `trait_var : Dict<trait, type_var>` is added
 * - The body is type‑checked under these assumptions (via {@link inferTraitLamType})
 * - The overall result is a {@link BoundedForallType}
 *
 * **Related**
 * - {@link TraitAppTerm} — applies a trait lambda to a type + dictionaries
 * - {@link BoundedForallType} — the type produced by a trait lambda
 * - {@link checkTraitConstraints} — resolves trait evidence for instantiation
 * - {@link traitMethodTerm} — accesses methods via the dictionary variable
 * - {@link DictBinding} — binds the trait_var in context
 *
 * **Examples**
 *
 * A simple trait‑polymorphic function:
 * ```ts
 * import {
 *   traitLamTerm, varType, arrowType, starKind, showTerm
 * } from "system-f-omega";
 *
 * const eqLam = traitLamTerm(
 *   "d",               // dictionary variable
 *   "Eq",              // trait
 *   "Self",            // type variable
 *   starKind,          // Self :: *
 *   [{ trait: "Eq", type: varType("Self") }], // Eq<Self>
 *   arrowType(varType("Self"), varType("Self"))
 * );
 *
 * console.log(showTerm(eqLam));
 * // "ΛSelf::* where Eq<Self>. (Self → Self)"
 * ```
 *
 * Using the trait variable inside the body:
 * ```ts
 * import { traitLamTerm, traitMethodTerm, varType, starKind } from "system-f-omega";
 *
 * // ΛSelf where Eq<Self>. d.eq
 * const t = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   traitMethodTerm({ var: "d" }, "eq")
 * );
 * ```
 *
 * Inferring the type:
 * ```ts
 * import {
 *   freshState, addType, addTraitDef, inferType,
 *   traitLamTerm, varType, arrowType, conType, starKind
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(
 *   state, "Eq", "A", starKind,
 *   [["eq", arrowType(varType("A"), conType("Bool"))]]
 * ).ok;
 *
 * const lam = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   arrowType(varType("Self"), conType("Int"))
 * );
 *
 * console.log(showType(inferType(state, lam).ok));
 * // "∀Self::* where Eq<Self>. (Self → Int)"
 * ```
 */
export type TraitLamTerm = {
  trait_lam: {
    trait_var: string; // dict variable name
    trait: string;
    type_var: string;
    kind: Kind;
    constraints: TraitConstraint[];
    body: Term;
  };
};

/**
 * A **trait application**:
 *
 * ```
 * term [Type] with dicts
 * ```
 *
 * applying a trait‑polymorphic function to:
 * - a **type argument**, and
 * - a list of **dictionary arguments** that satisfy its trait constraints.
 *
 * **What it represents**
 * `TraitAppTerm` is how *bounded polymorphism* is instantiated.
 * A function defined with a {@link TraitLamTerm}:
 *
 * ```
 * ΛSelf::* where Eq<Self>. body
 * ```
 *
 * is applied with:
 *
 * ```
 * f [Int] with { eqIntDict }
 * ```
 *
 * The type checker ensures:
 * - `term` has a {@link BoundedForallType}
 * - The provided type argument has the correct kind
 * - The dictionaries in `dicts` satisfy the trait constraints
 *
 * **Why it's useful**
 * Trait application is the key mechanism for:
 * - Passing trait evidence (dictionaries) required by a trait‑lambda
 * - Instantiating typeclass‑like functions with concrete types
 * - Supporting implicit/explicit dictionary‑passing semantics
 * - Enabling Haskell‑style bounded polymorphism in a System‑F‑omega setting
 *
 * **How it works during type checking**
 * Using {@link inferTraitAppType}, the system:
 * 1. Infers the type of `term`
 * 2. Ensures it is a bounded forall (`∀Self where C. τ`)
 * 3. Checks the provided type matches the binder kind
 * 4. Substitutes the type into the constraints
 * 5. Checks each constraint is satisfied by the corresponding dictionary
 * 6. Substitutes the type argument into the body and returns the result type
 *
 * **Related**
 * - {@link TraitLamTerm} — introduces bounded polymorphism
 * - {@link BoundedForallType} — the type of trait‑lambda expressions
 * - {@link checkTraitConstraints} — resolves required dictionaries
 * - {@link inferTraitAppType} — main typing rule for trait application
 * - {@link instantiateWithTraits} — auto-instantiation helper
 *
 * **Examples**
 *
 * Applying a single‑constraint trait lambda:
 * ```ts
 * import {
 *   traitLamTerm, traitAppTerm, dictTerm, conType,
 *   varType, arrowType, starKind, inferType, addTraitDef,
 *   addType, traitImplBinding, freshState, lamTerm, conTerm, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * // Eq<Self> trait definition
 * state = addTraitDef(
 *   state, "Eq", "A", starKind,
 *   [["eq", arrowType(varType("A"), conType("Bool"))]]
 * ).ok;
 *
 * // Dictionary: Eq<Int>
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"),
 *            conTerm("true", conType("Bool")))]
 * ]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * // Trait lambda: ΛSelf where Eq<Self>. Self → Int
 * const lam = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   arrowType(varType("Self"), conType("Int"))
 * );
 *
 * // Apply: lam[Int] with eqDict
 * const app = traitAppTerm(lam, conType("Int"), [eqDict]);
 * console.log(showType(inferType(state, app).ok));  // "Int"
 * ```
 *
 * Multiple constraints:
 * ```ts
 * const app = traitAppTerm(
 *   lam,                      // trait-lambda term
 *   conType("Int"),           // type argument
 *   [eqDict, showDict]        // evidence for each constraint
 * );
 * ```
 *
 * Error case: wrong number of dictionaries:
 * ```ts
 * import { traitAppTerm, traitLamTerm, conType, varType, starKind, inferType } from "system-f-omega";
 *
 * const lam = traitLamTerm("d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   { var: "body" }
 * );
 *
 * const bad = traitAppTerm(lam, conType("Int"), []);
 * // Missing dict -> inferType will return wrong_number_of_dicts
 * ```
 */
export type TraitAppTerm = {
  trait_app: {
    term: Term;
    type: Type;
    dicts: Term[]; // evidence for each constraint
  };
};

/**
 * The full set of **term-level expressions** supported by the language.
 *
 * **What it represents**
 * `Term` is a *tagged union* of all syntactic constructs in the language’s
 * lambda calculus.
 * Every expression you can evaluate or typecheck—functions, applications,
 * pattern matches, variants, records, dictionaries—appears as one of these
 * variants.
 *
 * The language supports:
 *
 * | Term Form                | Example                  | Description                             |
 * |--------------------------|--------------------------|-----------------------------------------|
 * | {@link VarTerm}          | `x`                      | Variable reference                      |
 * | {@link LamTerm}          | `λx:τ. e`                | Function abstraction                    |
 * | {@link AppTerm}          | `e₁ e₂`                  | Function application                    |
 * | {@link TyLamTerm}        | `ΛA::κ. e`               | Type abstraction                        |
 * | {@link TyAppTerm}        | `e [T]`                  | Type application                        |
 * | {@link TraitLamTerm}     | `ΛSelf where C. e`       | Trait‑bounded abstraction               |
 * | {@link TraitAppTerm}     | `e[T] with dicts`        | Trait‑bounded application               |
 * | {@link TraitMethodTerm}  | `dict.m`                 | Access trait method                     |
 * | {@link DictTerm}         | `dict T { m = e }`       | Trait dictionary                        |
 * | {@link RecordTerm}       | `{ x = e }`              | Record value                            |
 * | {@link ProjectTerm}      | `e.x`                    | Record projection                       |
 * | {@link TupleTerm}        | `(e₁, e₂)`               | Tuple value                             |
 * | {@link TupleProjectTerm} | `e.i`                    | Tuple index access                      |
 * | {@link InjectTerm}       | `<Label=e> as T`         | Variant injection                       |
 * | {@link MatchTerm}        | `match e { ... }`        | Pattern matching                        |
 * | {@link FoldTerm}         | `fold[T](e)`             | Pack into μ‑type                        |
 * | {@link UnfoldTerm}       | `unfold(e)`              | Unpack from μ‑type                      |
 * | {@link ConTerm}          | `42 : Int`               | Literal/constructor                     |
 *
 * **Why it's useful**
 * This union defines the **entire surface language**.
 * The typechecker recursively processes these nodes to:
 * - infer types ({@link inferType})
 * - check types ({@link checkType})
 * - resolve trait evidence ({@link checkTraitConstraints})
 * - normalize recursive structures
 * - support pattern matching and exhaustiveness checking
 *
 * Every major component of the compiler interprets or transforms this `Term`
 * structure.
 *
 * **Related**
 * - {@link inferType} — synthesizes a type for a term
 * - {@link checkType} — validates a term against an expected type
 * - {@link normalizeType} — expands type-level constructs used inside terms
 * - {@link Pattern} — used in {@link MatchTerm}
 *
 * **Examples**
 *
 * A simple function and application:
 * ```ts
 * import { lamTerm, varTerm, conTerm, conType, appTerm, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));  // λx:Int. x
 * const call = appTerm(id, conTerm("42", conType("Int")));
 *
 * console.log(showTerm(call));  // "(λx:Int.x 42)"
 * ```
 *
 * A polymorphic function (System F):
 * ```ts
 * import { tylamTerm, tyappTerm, varTerm, varType, lamTerm, conTerm, conType, starKind } from "system-f-omega";
 *
 * const poly = tylamTerm("A", starKind, lamTerm("x", varType("A"), varTerm("x")));
 * const inst = tyappTerm(poly, conType("Bool"));
 * ```
 *
 * Pattern matching on a variant:
 * ```ts
 * import { matchTerm, variantPattern, varPattern, conTerm, conType } from "system-f-omega";
 *
 * const m = matchTerm(
 *   conTerm("Some(3)", conType("Option<Int>")),
 *   [[variantPattern("Some", varPattern("x")), varTerm("x")]]
 * );
 * ```
 */
export type Term =
  | AppTerm // e₁ e₂
  | ConTerm // constants with their types
  | DictTerm // trait dict
  | FoldTerm // fold: τ[μα.τ/α] → μα.τ
  | InjectTerm // <l=e> as T
  | LamTerm // λx:τ.e
  | LetTerm
  | MatchTerm // match e { l₁(x₁) => e₁ | l₂(x₂) => e₂ }
  | ProjectTerm // e.l
  | RecordTerm // {l₁=e₁, l₂=e₂, ...}
  | TraitAppTerm // trat application
  | TraitLamTerm // trait lambda
  | TraitMethodTerm // trait method
  | TupleProjectTerm // tuple[0]
  | TupleTerm // tuple: #(l₁, l₂, ...)
  | TyAppTerm // e [τ]
  | TyLamTerm // Λα::κ.e
  | UnfoldTerm // unfold: μα.τ → τ[μα.τ/α]
  | VarTerm; // variable x

/**
 * A term binding in the typing context: `name : type`.
 *
 * **What it represents**
 * `TermBinding` stores the association between a **term variable** and its
 * inferred or declared **type** inside the typing context (`Γ`).
 *
 * Every time a new variable is introduced—by a lambda, a let‑binding, or global
 * definitions—its name and type are added to the context as a `TermBinding`.
 *
 * Conceptually:
 * ```
 * Γ = { x : Int,  f : Bool → Int,  eqInt : Dict<Eq, Int>, ... }
 * ```
 *
 * **Why it's useful**
 * The typechecker relies on bindings to:
 * - Look up the type of a variable when encountering a {@link VarTerm}
 * - Track the environment while typechecking lambdas ({@link LamTerm})
 * - Extend scope for let‑bindings ({@link LetTerm})
 * - Store dictionary values for trait resolution
 *
 * Without `TermBinding`, the typechecker would have no way to know what each
 * variable refers to.
 *
 * **Where it appears**
 * - Inside the typing context: `TypeCheckerState.ctx`
 * - Produced by {@link termBinding}
 * - Added to the context by {@link addTerm}, {@link inferLamType}, and
 *   {@link checkPattern}
 *
 * **Related**
 * - {@link VarTerm} — term variables that rely on term bindings
 * - {@link addTerm} — adds a new binding after inferring its type
 * - {@link termBinding} — constructor for this binding
 * - {@link TypeBinding} — analogous binding for types
 *
 * **Examples**
 *
 * Creating a binding manually:
 * ```ts
 * import { termBinding, conType } from "system-f-omega";
 *
 * const bind = termBinding("x", conType("Int"));
 * // Represents: x : Int
 * ```
 *
 * Adding a binding via `addTerm`:
 * ```ts
 * import {
 *   freshState, addType, addTerm, conTerm, conType, starKind, showContext
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * state = addTerm(state, "n", conTerm("42", conType("Int"))).ok;
 * console.log(showContext(state.ctx));
 * // "Term: n = Int"
 * ```
 *
 * Binding introduced by a lambda:
 * ```ts
 * import { lamTerm, varTerm, conType, inferType, freshState, addType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * // During typechecking, ctx is extended with x : Int (a TermBinding)
 * ```
 */
export type TermBinding = { term: { name: string; type: Type } };

/**
 * A binding in the typing context that assigns a **kind** to a type constructor:
 *
 * ```
 * name :: kind
 * ```
 *
 * **What it represents**
 * `TypeBinding` records the kind of a type constructor or type variable in the
 * typing context (`Γ`).
 *
 * Examples:
 * - `Int :: *`
 * - `List :: * → *`
 * - `F :: * → (* → *)`
 *
 * This binding is used whenever the typechecker needs to look up the kind of a
 * type constructor.
 *
 * **Why it's useful**
 * Kinds classify types, just like types classify values.
 * Type bindings allow the typechecker to:
 * - Verify correct usage of type constructors (`List<Int>` vs `Int<Int>`)
 * - Infer kinds during type application (via {@link checkAppKind})
 * - Expand type aliases and enum definitions
 * - Bind type parameters inside {@link ForallType}, {@link LamType}, and
 *   {@link BoundedForallType}
 *
 * Without `TypeBinding`, the system would not know how
 * many type arguments a constructor expects.
 *
 * **Where it appears**
 * - Inside the typing context: `TypeCheckerState.ctx`
 * - Created by {@link typeBinding}
 * - Added via {@link addType}, {@link addTypeAlias}, {@link addEnum}
 *
 * **Related**
 * - {@link Kind} — the classification of type constructors
 * - {@link addType} — registers a new type constructor in the context
 * - {@link checkKind} — uses type bindings during kind inference
 * - {@link TypeAliasBinding} — binds type aliases instead of constructors
 *
 * **Examples**
 *
 * Declaring a primitive type:
 * ```ts
 * import { typeBinding, starKind } from "system-f-omega";
 *
 * const bind = typeBinding("Int", starKind);
 * // Represents: Int :: *
 * ```
 *
 * Adding a type to the context:
 * ```ts
 * import { addType, freshState, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * console.log(showContext(state.ctx));
 * // "Type: Bool = *"
 * ```
 *
 * Declaring a higher‑kinded constructor:
 * ```ts
 * import { typeBinding, arrowKind, starKind } from "system-f-omega";
 *
 * const listBind = typeBinding("List", arrowKind(starKind, starKind));
 * // List :: * → *
 * ```
 */
export type TypeBinding = { type: { name: string; kind: Kind } };

/**
 * A binding that defines a **parametric type alias**:
 *
 * ```
 * type Alias<A₁::K₁, A₂::K₂, ...> = Body
 * ```
 *
 * **What it represents**
 * `TypeAliasBinding` describes a named alias for a type expression, possibly
 * parameterized by type variables and their kinds.
 *
 * Examples:
 * - `type Id<A> = A`
 * - `type Pair<A, B> = (A, B)`
 * - `type Reader<R, A> = R → A`
 *
 * A type alias expands *purely at compile time*—it does **not** introduce a new
 * nominal type, but simply rewrites to its body during normalization.
 *
 * **Why it's useful**
 * Type aliases provide:
 * - Readable names for complex type expressions
 * - Lightweight type‑level abstraction
 * - Parameterized type definitions without creating new nominal types
 *
 * The type checker uses alias bindings to:
 * - Expand aliases during {@link normalizeType}
 * - Determine kind information for aliased constructors
 * - Validate alias bodies against their parameter kinds (via {@link addTypeAlias})
 *
 * **Structure**
 * - `name`: alias name (e.g. `"Id"`)
 * - `params`: type parameter names (e.g. `["A"]`)
 * - `kinds`: kinds of type parameters (e.g. `[ * ]`)
 * - `body`: the type expression that defines the alias
 *
 * **Related**
 * - {@link addTypeAlias} — creates and validates an alias binding
 * - {@link normalizeType} — expands aliases during type normalization
 * - {@link Kind} — kinds of alias parameters
 * - {@link TypeBinding} — binding for actual type constructors
 *
 * **Examples**
 *
 * Simple identity alias:
 * ```ts
 * import { typeAliasBinding, varType, starKind } from "system-f-omega";
 *
 * const idAlias = typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * // type Id<A> = A
 * ```
 *
 * Multi‑parameter alias:
 * ```ts
 * import { typeAliasBinding, tupleType, varType, starKind } from "system-f-omega";
 *
 * const pair = typeAliasBinding(
 *   "Pair",
 *   ["A", "B"],
 *   [starKind, starKind],
 *   tupleType([varType("A"), varType("B")])
 * );
 * // type Pair<A, B> = (A, B)
 * ```
 *
 * Expansion during normalization:
 * ```ts
 * import {
 *   addTypeAlias, normalizeType, appType, conType,
 *   freshState, starKind, varType, showType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const t = appType(conType("Id"), conType("Int"));
 * console.log(showType(normalizeType(state, t)));  // "Int"
 * ```
 */
export type TypeAliasBinding = {
  type_alias: { name: string; params: string[]; kinds: Kind[]; body: Type };
};

/**
 * A **trait definition**, describing an interface that types can implement.
 *
 * ```
 * trait Trait<TypeParam :: Kind> {
 *   method1 : Type
 *   method2 : Type
 *   ...
 * }
 * ```
 *
 * **What it represents**
 * `TraitDef` declares:
 * - the **trait name** (`"Eq"`, `"Ord"`, `"Show"`, …)
 * - its **type parameter** (`"Self"`, `"A"`, `"F"`, …)
 * - the **kind** of that type parameter (`*`, `* → *`, etc.)
 * - the list of **method signatures** associated with the trait
 *
 * Example:
 * ```
 * trait Eq<Self :: *> {
 *   eq : Self → Self → Bool
 * }
 * ```
 *
 * **Why it's useful**
 * Traits give the language *typeclasses*: reusable interfaces that types can
 * implement.
 *
 * A `TraitDef` enables:
 * - Method lookup for trait methods (via {@link inferTraitMethodType})
 * - Validation of trait dictionaries (via {@link inferDictType})
 * - Trait‑bounded polymorphism (`∀Self where Eq<Self>. …`)
 * - Trait application (via {@link TraitAppTerm})
 *
 * It is the foundation of the dictionary‑passing mechanism used to resolve
 * constraints like `Eq<Int>` or `Functor<List>`.
 *
 * **The typechecker uses trait definitions to:**
 * - Verify that dictionaries implement all required methods
 * - Resolve trait constraints during bounded quantification
 * - Provide method signatures for `dict.method` projections
 *
 * **Related**
 * - {@link TraitImplBinding} — declares that a type implements a trait
 * - {@link DictTerm} — concrete dictionary implementing a trait
 * - {@link TraitLamTerm} — introduces trait‑bounded polymorphism
 * - {@link checkTraitConstraints} — resolves implementations
 *
 * **Examples**
 *
 * Defining a simple trait:
 * ```ts
 * import { TraitDef, starKind, arrowType, varType } from "system-f-omega";
 *
 * const eqDef: TraitDef = {
 *   name: "Eq",
 *   type_param: "Self",
 *   kind: starKind,
 *   methods: [
 *     ["eq", arrowType(varType("Self"), arrowType(varType("Self"), { con: "Bool" }))]
 *   ]
 * };
 * ```
 *
 * Adding the trait to a typing context:
 * ```ts
 * import { addTraitDef, freshState, starKind, arrowType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), arrowType(varType("A"), { con: "Bool" }))]
 * ]).ok;
 * ```
 *
 * A higher‑kinded trait:
 * ```ts
 * import { arrowKind, starKind } from "system-f-omega";
 *
 * const functorDef: TraitDef = {
 *   name: "Functor",
 *   type_param: "F",
 *   kind: arrowKind(starKind, starKind), // F :: * → *
 *   methods: [
 *     ["map", { arrow: { from: { var: "F" }, to: { var: "F" } } }]
 *   ]
 * };
 * ```
 */
export type TraitDef = {
  name: string;
  type_param: string; // e.g., "Self"
  kind: Kind;
  methods: [string, Type][]; // method name -> method type
};

/**
 * A context binding that stores a **trait definition** (`trait_def: TraitDef`).
 *
 * **What it represents**
 * `TraitDefBinding` is how the typing context (`Γ`) remembers that a trait
 * exists and what its methods and type parameter are.
 *
 * When a trait is declared with {@link addTraitDef}, the resulting
 * `TraitDefBinding` is inserted into the context so that other parts of the
 * typechecker can reference:
 *
 * - the trait’s name
 * - its type parameter and kind
 * - all of its method signatures
 *
 * **Why it's useful**
 * Trait definitions must be available globally so the typechecker can:
 *
 * - Validate dictionaries against the trait’s method list
 *   (via {@link inferDictType})
 * - Resolve trait method access (`dict.method`)
 *   (via {@link inferTraitMethodType})
 * - Check trait constraints inside bounded polymorphism
 *   (via {@link checkTraitConstraints})
 * - Instantiate trait‑polymorphic functions
 *   (via {@link TraitLamTerm} and {@link TraitAppTerm})
 *
 * Without this binding, traits would be unknown to the system and
 * dictionary‑passing would be impossible.
 *
 * **Related**
 * - {@link TraitDef} — the structure stored inside this binding
 * - {@link addTraitDef} — creates and inserts a `TraitDefBinding` into context
 * - {@link traitImplBinding} — stores implementations of traits
 * - {@link DictTerm} — dictionary values used to satisfy trait requirements
 *
 * **Examples**
 *
 * Creating a trait definition binding manually:
 * ```ts
 * import { traitDefBinding, TraitDef, starKind, arrowType, varType } from "system-f-omega";
 *
 * const eqDef: TraitDef = {
 *   name: "Eq",
 *   type_param: "A",
 *   kind: starKind,
 *   methods: [["eq", arrowType(varType("A"), { con: "Bool" })]]
 * };
 *
 * const binding = traitDefBinding("Eq", "A", starKind, eqDef.methods);
 * console.log(binding.trait_def.name);  // "Eq"
 * ```
 *
 * How the binding appears inside the typing context:
 * ```ts
 * import { addTraitDef, freshState, starKind, arrowType, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), { con: "Bool" })]
 * ]).ok;
 *
 * console.log(showContext(state.ctx));
 * // Trait: Eq = TraitDef (Eq A = * ...
 * ```
 */
export type TraitDefBinding = {
  trait_def: TraitDef;
};

/**
 * A context binding that registers a **trait implementation**:
 *
 * ```
 * impl Trait for Type = dictTerm(...)
 * ```
 *
 * **What it represents**
 * `TraitImplBinding` pairs:
 * - a **trait name** (`"Eq"`)
 * - a **type** that implements the trait (`Int`, `List<A>`, …)
 * - a **dictionary term** providing the actual method implementations
 *
 * This is the *canonical form* of a typeclass instance in the dictionary‑passing
 * translation used by the typechecker.
 *
 * Example conceptual form:
 * ```
 * impl Eq<Int> {
 *   eq = λx:Int. λy:Int. x == y
 * }
 * ```
 *
 * **Why it's useful**
 * Trait implementations supply **evidence** that a type supports a trait.
 * They allow the typechecker to:
 *
 * - Resolve trait constraints (`Eq<Int>`, `Show<List<A>>`, …)
 * - Materialize dictionary values when needed (via {@link checkTraitImplementation})
 * - Support bounded polymorphism inside {@link TraitLamTerm} and {@link TraitAppTerm}
 * - Validate method implementations against trait signatures (via {@link inferDictType})
 *
 * Without trait implementation bindings, trait‑bounded polymorphism could not be checked.
 *
 * **Where it is used**
 * - Stored in the typing context (`TypeCheckerState.ctx`)
 * - Retrieved during constraint solving in {@link checkTraitConstraints}
 * - Used when projecting trait methods in {@link traitMethodTerm}
 *
 * **Related**
 * - {@link TraitDefBinding} — stores the trait interface
 * - {@link DictTerm} — dictionary providing concrete method definitions
 * - {@link checkTraitImplementation} — resolves trait evidence
 * - {@link traitImplBinding} — constructor for this binding
 *
 * **Examples**
 *
 * Creating a binding for `Eq<Int>`:
 * ```ts
 * import {
 *   traitImplBinding, dictTerm, conType,
 *   lamTerm, varTerm, conTerm
 * } from "system-f-omega";
 *
 * const eqIntDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"),
 *            lamTerm("y", conType("Int"),
 *              conTerm("true", conType("Bool"))
 *            ))]
 * ]);
 *
 * const impl = traitImplBinding("Eq", conType("Int"), eqIntDict);
 * // Represents: impl Eq for Int = dict Eq<Int> { eq = ... }
 * ```
 *
 * Adding it to the context:
 * ```ts
 * import { freshState } from "system-f-omega";
 *
 * let state = freshState();
 * state.ctx.push(impl);
 * ```
 *
 * Resolving a trait requirement:
 * ```ts
 * import { checkTraitImplementation, conType, showTerm } from "system-f-omega";
 *
 * const result = checkTraitImplementation(state, "Eq", conType("Int"));
 * console.log("resolved:", showTerm(result.ok));   // prints dictionary term
 * ```
 */
export type TraitImplBinding = {
  trait_impl: {
    trait: string;
    type: Type;
    dict: Term; // dictionary term
  };
};

/**
 * A binding that introduces a **dictionary variable** into the typing context.
 *
 * **What it represents**
 * `DictBinding` stores:
 * - a **name** for the dictionary variable (`"d"`, `"eqInt"`, …)
 * - the **trait** it provides evidence for (`"Eq"`, `"Functor"`)
 * - the **type** the trait applies to (e.g. `Int`, `List<A>`)
 *
 * Unlike {@link TraitImplBinding}, which stores *global* implementations,
 * `DictBinding` represents **local evidence** available inside a term.
 *
 * This occurs inside:
 * - trait lambdas (`ΛSelf where Eq<Self>. body`)
 * - trait method projections (`d.eq`)
 * - explicit dictionary passing (`term [T] with {dicts}`)
 *
 * Conceptually:
 * ```
 * d : Dict<Eq, Int>
 * ```
 *
 * **Why it's useful**
 * Dictionary bindings make trait‑bounded polymorphism *work locally*:
 *
 * - Provide trait evidence to pattern bodies
 * - Enable method lookup (`d.eq`) inside {@link TraitMethodTerm}
 * - Bind dictionaries introduced by {@link TraitLamTerm}
 * - Track dictionary variables in recursive or nested contexts
 *
 * They act exactly like term bindings (`name : type`) but specifically for
 * dictionaries.
 *
 * **Where it appears**
 * - Inserted into the context during {@link inferTraitLamType}
 * - Added explicitly via {@link addDict}
 * - Looked up by {@link inferTraitMethodType}
 *
 * **Related**
 * - {@link DictTerm} — actual trait dictionary values
 * - {@link TraitLamTerm} — introduces dictionary variables
 * - {@link TraitMethodTerm} — uses dictionary bindings to access methods
 * - {@link TraitConstraint} — conditions requiring dictionary evidence
 *
 * **Examples**
 *
 * Manually creating a dictionary binding:
 * ```ts
 * import { dictBinding, conType } from "system-f-omega";
 *
 * const bind = dictBinding("eqInt", "Eq", conType("Int"));
 * // Represents: eqInt : Dict<Eq, Int>
 * ```
 *
 * Adding a dictionary binding to a context:
 * ```ts
 * import { freshState, addType, addTraitDef, addDict,
 *          dictTerm, conType, starKind, lamTerm, varTerm, conTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, []).ok;
 *
 * const eqDict = dictTerm("Eq", conType("Int"), []);
 * state = addDict(state, "eqInt", eqDict).ok;
 *
 * // Now eqInt is available in the typing context
 * ```
 *
 * Inside a trait lambda:
 * ```ts
 * import { traitLamTerm, starKind, varType } from "system-f-omega";
 *
 * // ΛSelf where Eq<Self>. body
 * // Automatically adds:
 * //    type var Self
 * //    dict var d : Dict<Eq, Self>
 * const lam = traitLamTerm("d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   { var: "body" }
 * );
 * ```
 */
export type DictBinding = {
  dict: {
    name: string; // dictionary variable
    trait: string;
    type: Type;
  };
};

/**
 * A **nominal enum (algebraic data type) definition** such as:
 *
 * ```
 * enum Option<T :: *> {
 *   None : ()
 *   Some : T
 * }
 * ```
 *
 * **What it represents**
 * `EnumDef` defines a named algebraic data type with:
 * - a **name** (`"Option"`, `"Either"`, `"List"`)
 * - a **kind** describing its type constructor arity
 *   (e.g. `* → *` for `Option`, `* → * → *` for `Either`)
 * - **type parameters**, each with a kind
 * - a list of **variants** (constructors), each with an associated field type
 * - a `recursive` flag indicating whether the type refers to itself
 *
 * Variants contain **field schemes**, which may reference the enum’s type
 * parameters. Their payloads are instantiated when the enum is applied to
 * concrete type arguments.
 *
 * **Why it's useful**
 * Nominal enums allow the language to define:
 * - Option types (`None | Some<T>`)
 * - Sum types (`Left<L> | Right<R>`)
 * - Recursive structures (lists, trees, ASTs)
 *
 * The typechecker uses `EnumDef` to:
 * - Validate constructors when typechecking {@link InjectTerm}
 * - Normalize enum applications into structural {@link VariantType} via
 *   {@link normalizeType}
 * - Support pattern matching with {@link VariantPattern}
 * - Check constructor label validity in {@link checkPattern}
 * - Handle recursive enums by introducing {@link MuType}
 *
 * **Related**
 * - {@link FieldScheme} — the variant payload types
 * - {@link enumDefBinding} — context binding for enums
 * - {@link addEnum} — registers an enum definition
 * - {@link VariantType} — structural variant form produced by normalization
 * - {@link MuType} — used for recursive enums
 *
 * **Examples**
 *
 * A non‑recursive enum:
 * ```ts
 * import { EnumDef, starKind, arrowKind, conType, tupleType } from "system-f-omega";
 *
 * const optionDef: EnumDef = {
 *   name: "Option",
 *   kind: arrowKind(starKind, starKind),  // * → *
 *   params: ["T"],
 *   variants: [
 *     ["None", tupleType([])],  // ()
 *     ["Some", conType("T")]    // T
 *   ],
 *   recursive: false
 * };
 * ```
 *
 * A binary type constructor (`Either<L, R>`):
 * ```ts
 * import { arrowKind, starKind, conType } from "system-f-omega";
 *
 * const eitherDef: EnumDef = {
 *   name: "Either",
 *   kind: arrowKind(starKind, arrowKind(starKind, starKind)), // * → (* → *)
 *   params: ["L", "R"],
 *   variants: [
 *     ["Left",  conType("L")],
 *     ["Right", conType("R")]
 *   ],
 *   recursive: false
 * };
 * ```
 *
 * A recursive list definition:
 * ```ts
 * import { tupleType, conType, varType, appType } from "system-f-omega";
 *
 * const listDef: EnumDef = {
 *   name: "List",
 *   kind: arrowKind(starKind, starKind), // * → *
 *   params: ["T"],
 *   variants: [
 *     ["Nil",  tupleType([])],
 *     ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 *   ],
 *   recursive: true   // important!
 * };
 * ```
 *
 * **Normalization example**
 * When applying `List<Int>`, normalization produces:
 * ```
 * μX. <Nil: () | Cons: (Int, X)>
 * ```
 * using {@link normalizeType}.
 */
export type EnumDef = {
  name: string; // e.g., "Either"
  kind: Kind; // e.g., * → * → * (for two params)
  params: string[]; // param var names, e.g., ["t", "u"]
  variants: [string, FieldScheme][]; // variant label → field scheme (with param vars unbound)
  recursive: boolean;
};

/**
 * A **field scheme** inside an enum (ADT) variant — simply a `Type` with
 * unbound type parameters.
 *
 * **What it represents**
 * `FieldScheme` describes the *payload type* of a variant **before**
 * substituting the enum’s type parameters.
 * It is used inside {@link EnumDef.variants}.
 *
 * For example, in:
 * ```
 * enum Option<T> {
 *   None : ()
 *   Some : T
 * }
 * ```
 * the field schemes are:
 * - `()` for `None`
 * - `T`  for `Some`
 *
 * These schemes may include type parameters that will be instantiated when the
 * enum is applied to concrete arguments:
 * ```
 * Option<Int>.Some → Int
 * ```
 *
 * **Why it's useful**
 * Field schemes allow enum definitions to:
 * - be **parametric** (using unbound vars like `T`, `A`, `E`)
 * - support **normalization** into {@link VariantType} via {@link normalizeType}
 * - participate in recursive definitions (`List<T>` has `Cons : (T, List<T>)`)
 *
 * The typechecker uses them in:
 * - {@link addEnum} — validating that each scheme has kind `*`
 * - {@link inferInjectType} — matching constructor payloads
 * - {@link normalizeType} — substituting params with actual type arguments
 *
 * **Examples**
 *
 * A simple payload:
 * ```ts
 * import { varType } from "system-f-omega";
 *
 * const someField: FieldScheme = varType("T");  // T
 * ```
 *
 * A tuple payload for a `Cons` constructor:
 * ```ts
 * import { tupleType, varType, appType, conType } from "system-f-omega";
 *
 * const consField: FieldScheme = tupleType([
 *   varType("T"),                     // head
 *   appType(conType("List"), varType("T"))  // tail
 * ]);
 * ```
 *
 * Unit payload:
 * ```ts
 * import { tupleType } from "system-f-omega";
 *
 * const noneField: FieldScheme = tupleType([]);  // ()
 * ```
 */
export type FieldScheme = Type; // e.g., { var: "t" } for Left, unit for None

/**
 * A context binding that stores a **nominal enum (ADT) definition**.
 *
 * **What it represents**
 * `EnumDefBinding` inserts an {@link EnumDef} into the typing context (`Γ`).
 * This lets the typechecker recognize:
 * - the name of the enum (`"Option"`, `"Either"`, `"List"`, …)
 * - its kind (e.g. `* → *`)
 * - its type parameters
 * - its constructors and their field schemes
 * - whether it is recursive
 *
 * Once in the context, this information is used to:
 * - Expand enum types into structural variants (via {@link normalizeType})
 * - Validate constructor labels during pattern matching (via {@link checkPattern})
 * - Typecheck variant injections (via {@link inferInjectType})
 *
 * **Why it's useful**
 * Nominal ADTs are foundational for sum types, optionals, result types,
 * recursive lists, trees, etc.
 * This binding gives the typechecker everything it needs to:
 *
 * - perform nominal → structural conversion
 * - check constructor names
 * - substitute enum parameters with actual types
 * - ensure correct usage of recursive enums
 *
 * Without `EnumDefBinding`, enums would not exist beyond parsing.
 *
 * **Related**
 * - {@link EnumDef} — the definition stored in the binding
 * - {@link addEnum} — creates and inserts an enum binding into context
 * - {@link normalizeType} — expands enum applications into {@link VariantType} or {@link MuType}
 * - {@link inferInjectType} — uses enum metadata to typecheck injections
 * - {@link VariantPattern} — depends on valid enum constructors
 *
 * **Examples**
 *
 * Creating a binding manually:
 * ```ts
 * import {
 *   enumDefBinding, tupleType, conType, arrowKind, starKind
 * } from "system-f-omega";
 *
 * const optionBinding = enumDefBinding(
 *   "Option",
 *   arrowKind(starKind, starKind),
 *   ["T"],
 *   [
 *     ["None", tupleType([])],
 *     ["Some", conType("T")]
 *   ],
 *   false
 * );
 *
 * console.log(optionBinding.enum.name);    // "Option"
 * console.log(optionBinding.enum.variants); // [["None", ()], ["Some", T]]
 * ```
 *
 * After `addEnum`, the binding appears in the context:
 * ```ts
 * import { freshState, addType, addEnum, starKind, tupleType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 *
 * console.log(showContext(state.ctx));
 * // Enum: Color = { name: "Color", kind: *, params: [], ... }
 * ```
 */
export type EnumDefBinding = { enum: EnumDef };

/**
 * A single entry in the typing context `Γ`, representing any kind of
 * environment binding used during type checking.
 *
 * **What it represents**
 * `Binding` is a *tagged union* of all possible things that can appear in the
 * context (`TypeCheckerState.ctx`).
 *
 * Each variant introduces a name (or trait/type) and the information the
 * typechecker needs to look it up.
 *
 * The context can contain:
 *
 * | Binding Variant         | Meaning                                   |
 * |-------------------------|-------------------------------------------|
 * | {@link TermBinding}     | Term variable binding (`x : τ`)           |
 * | {@link TypeBinding}     | Type constructor or type variable (`A :: κ`) |
 * | {@link TraitDefBinding} | Trait/interface definition                |
 * | {@link TraitImplBinding}| Registered implementation of a trait for a type |
 * | {@link DictBinding}     | Local dictionary variable (`d : Dict<T, τ>`) |
 * | {@link EnumDefBinding}  | Named enum (ADT) definition               |
 * | {@link TypeAliasBinding}| Parametric type alias                      |
 *
 * These bindings together define the knowledge the typechecker has about:
 * - term variables in scope
 * - available type constructors and aliases
 * - traits and their methods
 * - trait implementations
 * - dictionary evidence for bounded polymorphism
 * - enum constructors
 *
 * **Why it's useful**
 * The typing context `Γ` is the backbone of the entire typechecker.
 * Every operation — variable lookup, kind checking, trait resolution,
 * enum expansion, alias expansion — depends on the bindings stored here.
 *
 * The context is extended in:
 * - {@link inferLamType} — adds argument bindings
 * - {@link inferLetType} — adds local let‑bindings
 * - {@link addType}, {@link addEnum}, {@link addTraitDef} — global declarations
 * - {@link traitLamTerm} — adds a type variable + dictionary binding
 * - {@link addDict} and {@link addTraitImpl} — add dictionary or impl evidence
 *
 * **Related**
 * - {@link TypeCheckerState} — contains the context and meta‑env
 * - {@link bindingName} — extracts a display name from a binding
 * - {@link renameBinding} — used for imports and name rewriting
 * - {@link bindingDependencies} — used by the module importer
 *
 * **Examples**
 *
 * Building a context with different bindings:
 * ```ts
 * import {
 *   termBinding, typeBinding, traitDefBinding, enumDefBinding,
 *   conType, starKind, arrowType, varType
 * } from "system-f-omega";
 *
 * const ctx: Binding[] = [
 *   termBinding("x", conType("Int")),                // x : Int
 *   typeBinding("Int", starKind),                    // Int :: *
 *
 *   traitDefBinding("Eq", "A", starKind, [
 *     ["eq", arrowType(varType("A"), varType("Bool"))]
 *   ]),                                              // trait Eq<A>
 *
 *   enumDefBinding("Option", starKind, ["T"], [
 *     ["None", { tuple: [] }],
 *     ["Some", varType("T")]
 *   ], false)                                        // enum Option<T>
 * ];
 * ```
 *
 * Looking up bindings inside `inferVarType`:
 * ```ts
 * import { inferVarType, varTerm } from "system-f-omega";
 *
 * inferVarType({ ctx, meta: ... }, varTerm("x"));  // retrieves Int
 * ```
 *
 * Adding a binding to context:
 * ```ts
 * import { freshState, addTerm, varTerm, conTerm, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTerm(state, "y", conTerm("42", conType("Int"))).ok;
 * // ctx now contains a TermBinding for y : Int
 * ```
 */
export type Binding =
  | TermBinding // x : τ
  | TypeBinding // α :: κ
  | TraitDefBinding // trait definition
  | TraitImplBinding // trait impl
  | DictBinding // dict binding
  | EnumDefBinding // enums
  | TypeAliasBinding; // Type Alias

/**
 * The **typing context** `Γ`: an ordered list of bindings used during type
 * inference and checking.
 *
 * **What it represents**
 * `Context` is the environment that tracks:
 * - term variables and their types (`x : Int`)
 * - type constructors and their kinds (`List :: * → *`)
 * - trait definitions (e.g., `trait Eq<A> { ... }`)
 * - trait implementations (e.g., `impl Eq<Int>`)
 * - dictionary variables (`d : Dict<Eq, Int>`)
 * - enum (ADT) definitions
 * - type aliases
 *
 * In other words, it contains **everything the typechecker knows** at any point.
 *
 * The order of bindings matters:
 * - later bindings shadow earlier ones
 * - inner scopes extend the context (e.g., lambda parameters, let‑bindings)
 *
 * **Why it's useful**
 * The context is essential for:
 * - Looking up variable types ({@link inferVarType})
 * - Looking up type constructors when checking kinds ({@link checkKind})
 * - Resolving trait definitions for method lookup ({@link inferTraitMethodType})
 * - Finding trait implementations for typeclass‑like constraints ({@link checkTraitConstraints})
 * - Expanding enums and aliases during type normalization ({@link normalizeType})
 *
 * The context evolves as the program is typechecked:
 * - Lambdas push a new variable binding
 * - Let‑bindings add temporary bindings
 * - Trait lambdas add type and dictionary bindings
 * - Module imports insert multiple bindings at once
 *
 * **Related**
 * - {@link Binding} — variants stored inside the context
 * - {@link TypeCheckerState} — wraps the context with meta‑variable state
 * - {@link addType}, {@link addTerm}, {@link addEnum}, {@link addTraitDef} — extend the context
 * - {@link renameBinding} — used for module import renaming
 *
 * **Examples**
 *
 * An initially empty context:
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(showContext(state.ctx));  // ""
 * ```
 *
 * Adding basic bindings:
 * ```ts
 * import {
 *   addType, addTerm, conTerm, conType,
 *   freshState, starKind, showContext
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;                 // TypeBinding
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;  // TermBinding
 *
 * console.log(showContext(state.ctx));
 * // Type: Int = *
 * // Term: x = Int
 * ```
 *
 * Extending the context during lambda typing:
 * ```ts
 * import { lamTerm, varTerm, conType, inferType, freshState, addType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 *
 * // inferLamType internally extends ctx with: x : Int
 * console.log(inferType(state, id).ok);
 * ```
 */
export type Context = Binding[];

/**
 * The **meta‑variable environment**, storing the state used for type inference.
 *
 * Meta‑variables (`?0`, `?1`, …) represent *unknown types* that are gradually
 * solved during unification. `MetaEnv` tracks:
 *
 * - **solutions** — mappings from meta‑variables to concrete types
 *   (`?0 := Int`, `?1 := List<?2>`, etc.)
 * - **kinds** — the kind assigned to each meta‑variable (`?0 :: *`, `?3 :: * → *`)
 * - **counter** — the next available index for generating fresh meta‑variables
 *
 * **What it represents**
 * This environment is the engine behind Hindley–Milner style inference:
 *
 * - When you instantiate a polymorphic type, you create fresh meta‑vars
 *   (via {@link freshMetaVar}).
 * - As the typechecker collects constraints, meta‑vars unify with
 *   concrete types ({@link unifyTypes}).
 * - Once solved, the solution is stored in `solutions`.
 * - Kind information ensures higher‑kinded types unify correctly.
 *
 * **Why it's useful**
 * Without a meta‑environment, the typechecker could not:
 * - Track unknown types during inference
 * - Solve unification constraints incrementally
 * - Support polymorphism (`∀`) and type lambdas (`λ`)
 * - Enforce kind‑correct inference for higher‑kinded types
 * - Detect cyclic types (`a ~ a → Int`)
 *
 * MetaEnv effectively powers:
 * - bidirectional typechecking
 * - subsumption & bounded polymorphism
 * - type‑level beta‑reduction
 * - structual & nominal unification
 *
 * **Related**
 * - {@link freshMetaVar} — creates new meta‑vars in this environment
 * - {@link solveMetaVar} — records a solution with occurs‑check
 * - {@link applySubstitution} — resolves meta‑vars during normalization
 * - {@link unifyTypes} — main engine that produces meta‑var constraints
 * - {@link getUnboundMetas} — collects unsolved meta‑vars
 *
 * **Examples**
 *
 * Creating a fresh meta‑variable:
 * ```ts
 * import { freshState, freshMetaVar, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const mv = freshMetaVar(state.meta, starKind);
 *
 * console.log(mv.evar);                  // "?0"
 * console.log(state.meta.kinds.get("?0")); // "*"
 * ```
 *
 * Solving a meta‑var:
 * ```ts
 * import { freshState, freshMetaVar, solveMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const mv = freshMetaVar(state.meta);
 *
 * solveMetaVar(state, mv.evar, conType("Int"));
 * console.log(state.meta.solutions.get(mv.evar));  // { con: "Int" }
 * ```
 *
 * Following meta‑var substitutions:
 * ```ts
 * import { applySubstitution, freshState, freshMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const mv = freshMetaVar(state.meta);
 *
 * const subst = new Map([[mv.evar, conType("Int")]]);
 * console.log(applySubstitution(state, subst, mv));  // Int
 * ```
 */
export type MetaEnv = {
  solutions: Map<string, Type>; // evar -> Type
  kinds: Map<string, Kind>; // evar -> Kind
  counter: number;
};

/**
 * The full mutable **typechecking state**, containing:
 *
 * - `ctx` — the typing context (`Γ`), a list of bindings
 * - `meta` — the meta‑variable environment for type inference
 *
 * This is threaded through every inference and checking function.
 *
 * **What it represents**
 * `TypeCheckerState` is the *entire knowledge state* of the typechecker at any
 * given point.
 *
 * It contains:
 * - **Context (`ctx`)**:
 *   term variables, type constructors, traits, dictionaries, enums, aliases
 *   (see {@link Context}, {@link Binding})
 *
 * - **Meta‑environment (`meta`)**:
 *   existential type variables, their kinds, and their solved values
 *   (see {@link MetaEnv})
 *
 * Every type‑checking call uses this structure to:
 * - look up variable types
 * - resolve trait implementations
 * - remember type constructors and aliases
 * - track type inference state
 * - generate fresh meta‑variables
 * - unify constraints and record solutions
 *
 * **Why it's useful**
 * `TypeCheckerState` enables:
 * - **Incremental type inference** with meta‑vars
 * - **Scoped typing** for lambdas, lets, and patterns
 * - **Global declarations** (types, traits, enums, aliases)
 * - **Dictionary‑passing** for trait constraints
 * - **Normalization** using context information (enums, aliases)
 *
 * Nearly every function in the typechecker accepts and returns (or mutates)
 * a `TypeCheckerState`.
 *
 * **Related**
 * - {@link MetaEnv} — tracks meta‑variable inference state
 * - {@link Context} — tracks term/type/trait/dict/enum/alias bindings
 * - {@link inferType} — core inference engine
 * - {@link checkType} — bidirectional checking
 * - {@link normalizeType} — relies heavily on context lookups
 * - {@link addType}, {@link addEnum}, {@link addTraitDef}, {@link addDict} — extend the state
 *
 * **Examples**
 *
 * Creating a fresh, empty checker state:
 * ```ts
 * import { freshState } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(state.ctx.length);    // 0
 * console.log(state.meta.counter);  // 0
 * ```
 *
 * Adding types and terms:
 * ```ts
 * import {
 *   freshState, addType, addTerm,
 *   conTerm, conType, starKind, showContext
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * console.log(showContext(state.ctx));
 * // "Type: Int = *"
 * // "Term: x = Int"
 * ```
 *
 * Using state during inference:
 * ```ts
 * import { inferType, varTerm, showType } from "system-f-omega";
 *
 * const t = inferType(state, varTerm("x"));
 * console.log(showType(t.ok));  // "Int"
 * ```
 */
export type TypeCheckerState = {
  meta: MetaEnv;
  ctx: Context;
};

/**
 * Optional **renaming rules** used when importing another module’s bindings.
 *
 * During `importModule`, these aliases let users rename:
 * - trait names
 * - type constructors
 * - term variables
 * - record/variant labels
 *
 * This prevents name collisions and allows controlled, explicit renaming during
 * module merging.
 *
 * **What it represents**
 * `ImportAliases` is a collection of maps, one for each category of importable
 * names:
 *
 * - `traits` — rename trait definitions (`Eq → PartialEq`)
 * - `types` — rename type constructors (`Int32 → Int`)
 * - `terms` — rename term variables (`add → plus`)
 * - `labels` — rename record fields or variant labels (`x → xCoord`, `Left → L`)
 *
 * These maps are applied by {@link importModule} via {@link renameBinding},
 * {@link renameType}, {@link renameTerm}, and {@link renamePattern}.
 *
 * All fields are optional; an empty alias map means no renaming for that
 * category.
 *
 * **Why it's useful**
 * Import aliases allow:
 * - **Avoiding name clashes** between modules
 * - **Re‑exporting** bindings under new names
 * - **Localizing naming conventions** (e.g., renaming all labels for a record)
 * - **Controlling visibility and conflicts** when combining multiple libraries
 *
 * Without them, module imports would easily produce accidental collisions.
 *
 * **Related**
 * - {@link importModule} — uses aliases during module merging
 * - {@link renameBinding} — renames individual context bindings
 * - {@link renameType} — renames constructors, labels, type variables
 * - {@link renameTerm} — renames term-level identifiers
 *
 * **Examples**
 *
 * Renaming types and traits:
 * ```ts
 * import { ImportAliases } from "system-f-omega";
 *
 * const aliases: ImportAliases = {
 *   types:  { Int32: "Int" },
 *   traits: { Eq: "PartialEq" }
 * };
 * ```
 *
 * Renaming term variables:
 * ```ts
 * const aliases: ImportAliases = {
 *   terms: { add: "plus", mul: "times" }
 * };
 * ```
 *
 * Renaming labels in records and variants:
 * ```ts
 * const aliases: ImportAliases = {
 *   labels: { x: "xCoord", Left: "L" }
 * };
 * ```
 *
 * Full example used during module import:
 * ```ts
 * import { importModule, freshState } from "system-f-omega";
 *
 * const result = importModule({
 *   from: moduleA,
 *   into: freshState(),
 *   roots: ["Int32", "Eq"],
 *   aliases: {
 *     types:  { Int32: "Int" },
 *     traits: { Eq: "PartialEq" },
 *     labels: { Left: "L", Right: "R" }
 *   }
 * });
 * ```
 */
export type ImportAliases = {
  traits?: Record<string, string>;
  types?: Record<string, string>;
  terms?: Record<string, string>;
  labels?: Record<string, string>;
};

/**
 * Creates a brand‑new **typechecker state** with an empty meta‑environment
 * and optional initial context.
 *
 * **What it represents**
 * `freshState()` initializes the full state required by the typechecker:
 *
 * - `ctx` — the typing context (`Γ`), containing term/type/trait/enum bindings
 * - `meta` — the meta‑variable environment, used for type inference
 *
 * A fresh state has:
 * - no bindings
 * - no solved meta‑variables
 * - meta‑variable counter starting at `0`
 *
 * This is the starting point for interactive REPL sessions, module checking,
 * and unit tests.
 *
 * **Why it's useful**
 * `freshState` gives the typechecker a clean environment in which:
 * - new types or traits can be declared (`addType`, `addTraitDef`)
 * - new terms can be added (`addTerm`, `addDict`)
 * - inference can begin with no leftover meta‑vars or constraints
 *
 * It ensures that inference is **pure**, **repeatable**, and **scoped**, making
 * it safe to run many independent checks.
 *
 * **Related**
 * - {@link TypeCheckerState} — structure returned by this function
 * - {@link Context} — the initial (optional) context
 * - {@link MetaEnv} — meta‑variable state initialized here
 * - {@link inferType} — uses this state for type inference
 *
 * **Examples**
 *
 * Creating a fresh, empty state:
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 *
 * console.log(showContext(state.ctx));  // ""
 * console.log(state.meta.counter);      // 0
 * ```
 *
 * Creating a state with initial bindings:
 * ```ts
 * import { freshState, typeBinding, starKind, showContext } from "system-f-omega";
 *
 * const initial = [typeBinding("Int", starKind)];
 * const state = freshState(initial);
 *
 * console.log(showContext(state.ctx));
 * // "Type: Int = *"
 * ```
 *
 * Using the state for type inference:
 * ```ts
 * import { freshState, addType, inferType, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = inferType(state, conTerm("42", conType("Int")));
 * console.log(result.ok);  // "Int"
 * ```
 */
export const freshState = (ctx: Context = []): TypeCheckerState =>
  ({
    ctx,
    meta: {
      solutions: new Map(),
      kinds: new Map(),
      counter: 0,
    },
  }) satisfies TypeCheckerState;

/**
 * An error raised when a **type name** is not found in the typing context.
 *
 * **What it represents**
 * `UnboundTypeError` indicates that the typechecker encountered a type variable
 * or constructor that has **no corresponding binding** in the context (`Γ`).
 *
 * This happens when:
 * - A type variable is used outside its binding scope
 *   (e.g., referring to `A` with no surrounding `∀A` or `λA`)
 * - A type constructor has not been added via {@link addType} or {@link addEnum}
 * - A type alias refers to a missing name
 * - A pattern or trait constraint mentions a non‑existent type
 *
 * Example situations:
 * ```
 * x : MissingType       // MissingType is unbound
 * ∀A. B → A             // B is unbound
 * foo : List<Z>         // Z is unbound if not declared
 * ```
 *
 * **Why it's useful**
 * This error helps catch:
 * - misspelled type names
 * - missing imports
 * - invalid references to type parameters
 * - incomplete module environments
 *
 * It is one of the earliest and clearest signals that the type environment
 * is underspecified.
 *
 * **Where it is produced**
 * - {@link checkKind} — when resolving type constructors or variables
 * - {@link checkConKind} — when looking up constructors
 * - {@link checkVarKind} — when encountering unbound type variables
 * - {@link substituteType} — during normalization if expansions refer to missing types
 *
 * **Related**
 * - {@link TypeBinding} — how type constructors are added to the context
 * - {@link addType} — registers a type name
 * - {@link addEnum} — registers an enum name
 * - {@link showError} — pretty-prints this error
 *
 * **Examples**
 *
 * Unbound type variable:
 * ```ts
 * import { checkKind, varType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const res = checkKind(state, varType("A"));
 *
 * console.log(showError(res.err));  // "Unbound identifier: A"
 * ```
 *
 * Unbound constructor:
 * ```ts
 * import { checkKind, conType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const res = checkKind(state, conType("Foo"));
 *
 * console.log(showError(res.err));  // "Unbound identifier: Foo"
 * ```
 */
export type UnboundTypeError = { unbound: string };

/**
 * An error raised when a type has the **wrong kind**.
 *
 * **What it represents**
 * A `KindMismatchTypeError` occurs when the typechecker expected a type of one
 * kind (e.g. `*`) but instead found a type of a different kind (e.g. `* → *`).
 *
 * This typically happens when:
 * - Applying a type constructor to the wrong number of arguments
 *   (`Int<Int>` → `Int :: *`, but application expects `* → *`)
 * - Using a higher‑kinded type where a concrete type is required
 *   (`List :: * → *` used where `*` is expected)
 * - Incorrect kinds for type parameters in `∀`, `λ`, or type aliases
 * - Variant or record fields that must have kind `*` but don’t
 *
 * Example of a mismatch:
 * ```
 * expected: *
 * actual:   * → *
 * ```
 *
 * **Why it's useful**
 * This error enforces **kind safety**, ensuring:
 * - Type constructors are applied correctly
 * - Higher‑kinded types are used only where valid
 * - Polymorphic functions respect declared kinds
 * - Enum and alias definitions have well‑formed kinds
 *
 * **Where it is produced**
 * - {@link checkKind} — main kind inference/checking entrypoint
 * - {@link checkAppKind} — when applying a higher‑kinded type
 * - {@link checkForallKind}, {@link checkLamKind} — binder kind checking
 * - {@link checkRecordKind}, {@link checkVariantKind} — ensuring fields are `*`
 *
 * **Related**
 * - {@link Kind} — the kind system (`*`, `κ₁ → κ₂`)
 * - {@link StarKind} — the base kind
 * - {@link ArrowKind} — kind-level functions
 * - {@link showError} — pretty printing of this error
 *
 * **Examples**
 *
 * Wrong arity in type application:
 * ```ts
 * import { checkKind, appType, conType, starKind, arrowKind, freshState, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;  // * → *
 *
 * const bad = appType(appType(conType("List"), conType("Int")), conType("Bool"));
 * const res = checkKind(state, bad);
 *
 * console.log(showError(res.err));
 * // Kind mismatch:
 * //   Expected: *
 * //   Actual:   (* → *)
 * ```
 *
 * Field kind mismatch:
 * ```ts
 * import { recordType, arrowKind, starKind, checkKind, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const bad = recordType([["f", arrowKind(starKind, starKind)]]);
 *
 * console.log(showError(checkKind(state, bad).err));
 * // Kind mismatch: expected *, got (* → *)
 * ```
 */
export type KindMismatchTypeError = {
  kind_mismatch: { expected: Kind; actual: Kind };
};

/**
 * An error raised when two types are **incompatible** during unification or
 * checking.
 *
 * **What it represents**
 * A `TypeMismatchTypeError` occurs when the typechecker expects a value of one
 * type but encounters a different, incompatible type.
 *
 * This happens in situations such as:
 * - Applying a function to an argument of the wrong type
 *   (`(Int → Bool)` applied to a `String`)
 * - Unifying record/tuple shapes that don’t match
 * - Trying to use a variant constructor in the wrong enum
 * - Checking a lambda body against an expected return type that doesn't match
 * - Attempting to unify distinct constructors (`Int` vs `Bool`)
 *
 * Example:
 * ```
 * expected: Int
 * actual:   Bool
 * ```
 *
 * **Why it's useful**
 * This error pinpoints the moment where two types diverge, making it easier to
 * diagnose:
 * - incorrect function arguments
 * - bad pattern matches
 * - wrong dictionary method signatures
 * - mismatched record or tuple structures
 * - failed subsumption during bounded polymorphism
 *
 * It is the most common error in the typechecker and one of the most important
 * for debugging.
 *
 * **Where it is produced**
 * - {@link unifyTypes} — structural unification failure
 * - {@link checkType} — expected vs inferred mismatch
 * - {@link checkPattern} — pattern vs type mismatch
 * - {@link inferInjectType} — wrong variant payload
 * - {@link subsumes} — failed subtype check
 *
 * **Related**
 * - {@link showError} — pretty‑prints this error
 * - {@link KindMismatchTypeError} — similar error for kinds
 * - {@link unifyArrowTypes}, {@link unifyRecordTypes}, etc. — structural rules that may fail
 *
 * **Examples**
 *
 * Mismatched function argument:
 * ```ts
 * import {
 *   freshState, addType, inferType,
 *   lamTerm, varTerm, conTerm, conType,
 *   appTerm, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const bad = appTerm(id, conTerm("true", conType("Bool")));
 *
 * console.log(showError(inferType(state, bad).err));
 * // Type mismatch:
 * //   Expected: Int
 * //   Actual:   Bool
 * ```
 *
 * Record mismatch:
 * ```ts
 * import {
 *   recordPattern, varPattern, recordType, conType,
 *   checkPattern, freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["y", varPattern("n")]]);
 * const ty  = recordType([["x", conType("Int")]]);
 *
 * console.log(showError(checkPattern(state, pat, ty).err));
 * // Missing field 'y' in record: {x: Int}
 * ```
 */
export type TypeMismatchTypeError = {
  type_mismatch: { expected: Type; actual: Type };
};

/**
 * An error raised when attempting to **apply a non-function value**.
 *
 * **What it represents**
 * `NotAFunctionTypeError` occurs when the typechecker encounters an
 * application `e₁ e₂` but the inferred type of `e₁` is **not a function type**
 * (`τ₁ → τ₂`), or not a polymorphic type that can reduce to one.
 *
 * Examples of invalid applications:
 * - `42 x` — `42 : Int` is not a function
 * - `{x = 1} y` — records are not callable
 * - `<Left=1> y` — variants are not functions
 * - `List y` — type constructors cannot be applied as terms
 *
 * The error payload contains the exact **non-function type** that was used as
 * the callee.
 *
 * **Why it's useful**
 * This error catches common mistakes such as:
 * - Forgetting parentheses around lambdas
 * - Misusing constructors or values in function position
 * - Applying polymorphic values without instantiation
 * - Treating non-callable data (records, variants) as functions
 *
 * It provides a clear message showing *which* type was incorrectly used in
 * function position.
 *
 * **Where it is produced**
 * - {@link inferAppType} — when checking the callee of an application
 * - During normalization when the callee does not reduce to a function type
 *
 * **Related**
 * - {@link ArrowType} — the only valid function type form
 * - {@link inferAppType} — main inference rule for applications
 * - {@link showError} — handles formatting of this error
 *
 * **Examples**
 *
 * Applying a literal (invalid):
 * ```ts
 * import {
 *   appTerm, conTerm, conType,
 *   inferType, freshState, addType,
 *   starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const bad = appTerm(conTerm("42", conType("Int")), { var: "x" });
 * console.log(showError(inferType(state, bad).err));
 * // "Not a function: Int"
 * ```
 *
 * Applying a record (invalid):
 * ```ts
 * import { recordTerm, appTerm, varTerm, inferType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const rec = recordTerm([["x", varTerm("v")]]);
 * const invalid = appTerm(rec, varTerm("y"));
 *
 * console.log(showError(inferType(state, invalid).err));
 * // "Not a function: {x: τ}"
 * ```
 *
 * Applying a variant (invalid):
 * ```ts
 * import { injectTerm, conTerm, conType, appTerm, freshState, inferType, showError } from "system-f-omega";
 * import { variantType } from "system-f-omega";
 *
 * const state = freshState();
 * const left = injectTerm("Left", conTerm("1", conType("Int")),
 *   variantType([["Left", conType("Int")]])
 * );
 *
 * console.log(showError(inferType(state, appTerm(left, conTerm("0", conType("Int")))).err));
 * // "Not a function: <Left: Int>"
 * ```
 */
export type NotAFunctionTypeError = { not_a_function: Type };

/**
 * An error raised when attempting to **apply a non–type‑function** at the
 * type level.
 *
 * **What it represents**
 * `NotATypeFunctionTypeError` occurs when the typechecker encounters a type
 * application:
 *
 * ```
 * F<T>
 * ```
 *
 * but the type `F` does **not** have a function kind (`κ₁ → κ₂`).
 *
 * Examples that trigger this error:
 * - `Int<Bool>` — `Int :: *`, but application requires `* → *`
 * - `A<B>` where `A` is a plain type parameter (`A :: *`)
 * - Applying a non-HKT record or variant type
 *
 * The payload contains the invalid type used in function position.
 *
 * **Why it's useful**
 * This error enforces **kind correctness** in higher‑kinded type applications:
 * - Prevents applying ordinary types as if they were generics
 * - Catches misuse of polymorphic constructors
 * - Helps debug type alias and enum expansions
 *
 * It is the type‑level analogue of {@link NotAFunctionTypeError}.
 *
 * **Where it is produced**
 * - {@link checkAppKind} — main checker for type applications
 * - {@link checkKind} — when encountering unexpected kinds
 * - During normalization if a type lambda does not have function kind
 *
 * **Related**
 * - {@link ArrowKind} — only types with arrow kinds can be applied
 * - {@link AppType} — type‑level application node
 * - {@link KindMismatchTypeError} — related kind error
 * - {@link showError} — formats this error for users
 *
 * **Examples**
 *
 * Applying a primitive type (invalid):
 * ```ts
 * import {
 *   checkKind, appType, conType, starKind, freshState, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const bad = appType(conType("Int"), conType("Bool"));
 * console.log(showError(checkKind(state, bad).err));
 * // "Not a type-level function: Int"
 * ```
 *
 * Applying a type variable incorrectly:
 * ```ts
 * import { checkKind, appType, varType, conType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const bad = appType(varType("A"), conType("Int"));  // A :: * (not a function)
 *
 * console.log(showError(checkKind(state, bad).err));
 * // "Not a type-level function: A"
 * ```
 *
 * Applying a record or variant type:
 * ```ts
 * import { appType, recordType, conType, checkKind, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const recTy = recordType([["x", conType("Int")]]);
 *
 * console.log(showError(checkKind(state, appType(recTy, conType("Int"))).err));
 * // "Not a type-level function: {x: Int}"
 * ```
 */
export type NotATypeFunctionTypeError = { not_a_type_function: Type };

/**
 * An error raised when the typechecker detects a **cyclic (infinite) type**.
 *
 * **What it represents**
 * `CyclicTypeError` occurs when unification or substitution produces a type
 * where a type variable (or meta‑variable) would have to contain *itself*.
 *
 * Classic example of an invalid cyclic type:
 * ```
 * a = a → Int
 * ```
 *
 * or for meta‑variables:
 * ```
 * ?0 = (?0 → Bool)
 * ```
 *
 * This cannot be solved because it would require an *infinitely large type*.
 *
 * The error stores the name of the variable causing the cycle (`"a"` or `"?0"`).
 *
 * **Why it's useful**
 * Detecting cyclic types is essential for:
 * - Ensuring type inference terminates
 * - Preventing infinite unification loops
 * - Ensuring well‑formed recursive types only come from explicit μ‑types
 * - Rejecting illegal recursive uses of type variables
 *
 * This error indicates a *logical contradiction* in the type program.
 *
 * **Where it is produced**
 * - {@link occursCheck} — when checking rigid type variables
 * - {@link occursCheckEvar} — when checking meta‑variables (`?N`)
 * - {@link solveMetaVar} — rejects binding a meta‑var to a type that contains it
 * - {@link unifyTypes} — rejects degenerate forms like `μX.X` or self-referential arrows
 *
 * **Related**
 * - {@link MuType} — the **only** legal way to express recursive types
 * - {@link unifyTypes} — where cycles are most commonly encountered
 * - {@link showError} — formats this error for the user
 *
 * **Examples**
 *
 * Cyclic type from a variable:
 * ```ts
 * import { occursCheck, arrowType, varType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), varType("Int"));  // a → Int
 * console.log(occursCheck("a", ty));  // true → cyclic
 * ```
 *
 * Cyclic meta‑variable:
 * ```ts
 * import { freshState, freshMetaVar, occursCheckEvar, arrowType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const mv = freshMetaVar(state.meta);
 *
 * const ty = arrowType({ evar: mv.evar }, varType("Int"));  // ?0 → Int
 * console.log(occursCheckEvar(state.meta, mv.evar, ty));  // true
 * ```
 *
 * Infinite type rejected during unification:
 * ```ts
 * import { unifyTypes, freshState, varType, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * const result = unifyTypes(state, varType("a"), arrowType(varType("a"), varType("Int")), [], new Map());
 *
 * // result.err = { cyclic: "a" }
 * ```
 */
export type CyclicTypeError = { cyclic: string };

/**
 * An error raised when a value is used **as if it were a record**, but its type
 * is not a record type.
 *
 * **What it represents**
 * `NotARecordTypeError` occurs when the typechecker encounters:
 *
 * - A record projection:
 *   ```
 *   e.x
 *   ```
 *   but `e` does **not** have a record type `{ x : τ }`.
 *
 * - A record pattern:
 *   ```
 *   match e { {x: p} => ... }
 *   ```
 *   but `e` is not a record.
 *
 * The error payload contains the **actual type** that caused the failure.
 *
 * **Examples of invalid usage**
 * - `42.x` — `42 : Int` is not a record
 * - `<Left=1>.x` — variants are not records
 * - `(1, 2).x` — tuples are not records
 * - Using `{x: p}` to match a type that isn’t `{x: τ}`
 *
 * **Why it's useful**
 * This error helps catch:
 * - Misspelled labels
 * - Incorrect destructuring patterns
 * - Using projection on non‑record data
 * - Mixing up tuple and record syntax
 *
 * It points directly to the value/type that was incorrectly used in a record
 * context.
 *
 * **Where it is produced**
 * - {@link inferProjectType} — when projecting `record.label`
 * - {@link checkRecordPattern} — when destructuring a record pattern
 * - {@link checkPattern} — catches record‑pattern mismatch
 *
 * **Related**
 * - {@link RecordType} — valid record types `{ l: τ }`
 * - {@link recordTerm} — constructing record values
 * - {@link projectTerm} — record projection syntax
 * - {@link MissingFieldTypeError} — similar error when record exists but label doesn’t
 *
 * **Examples**
 *
 * Projecting a non-record:
 * ```ts
 * import {
 *   projectTerm, conTerm, conType, inferType,
 *   freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const t = projectTerm(conTerm("42", conType("Int")), "x");
 * console.log(showError(inferType(state, t).err));
 * // "Not a record type: Int"
 * ```
 *
 * Record pattern on a non-record:
 * ```ts
 * import {
 *   checkPattern, recordPattern, varPattern,
 *   conType, addType, freshState, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = recordPattern([["x", varPattern("a")]]);
 * const res = checkPattern(state, pat, conType("Bool"));
 *
 * console.log(showError(res.err));
 * // "Not a record type: Bool"
 * ```
 */
export type NotARecordTypeError = { not_a_record: Type };

/**
 * An error raised when projecting or pattern‑matching a record **missing a
 * required field**.
 *
 * **What it represents**
 * `MissingFieldTypeError` occurs when the typechecker expects a record with a
 * field `label`, but the inferred record type does not contain that field.
 *
 * This can happen when:
 * - Accessing a field:
 *   ```
 *   e.x
 *   ```
 *   but `e` has no field named `"x"`.
 *
 * - Matching a record pattern:
 *   ```
 *   match e { { x: p } => ... }
 *   ```
 *   but the scrutinee’s type does not contain field `"x"`.
 *
 * The error stores:
 * - `record` — the actual record type encountered
 * - `label` — the field that was expected but missing
 *
 * **Why it's useful**
 * This error points out:
 * - Typos in record field names
 * - Mismatches between expected and actual record shapes
 * - Incorrect destructuring patterns
 * - Misuse of record projection syntax
 *
 * It’s more precise than {@link NotARecordTypeError}, because it means
 * “this *is* a record, but the field you asked for does not exist.”
 *
 * **Where it is produced**
 * - {@link inferProjectType} — accessing a missing record field
 * - {@link checkRecordPattern} — pattern contains unknown field
 * - {@link checkPattern} — structural mismatch inside patterns
 *
 * **Related**
 * - {@link RecordType} — structural record types
 * - {@link projectTerm} — record field access
 * - {@link recordPattern} — destructuring patterns
 * - {@link showError} — pretty‑prints this error
 *
 * **Examples**
 *
 * Projecting a missing field:
 * ```ts
 * import {
 *   recordTerm, conTerm, conType, projectTerm,
 *   inferType, addType, freshState, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const bad = projectTerm(rec, "y");
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Missing field 'y' in record: {x: Int}"
 * ```
 *
 * Record pattern with an unknown field:
 * ```ts
 * import {
 *   checkPattern, recordPattern, varPattern,
 *   recordType, conType, freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = recordPattern([["z", varPattern("a")]]);
 * const ty = recordType([["x", conType("Bool")]]);
 *
 * console.log(showError(checkPattern(state, pat, ty).err));
 * // "Missing field 'z' in record: {x: Bool}"
 * ```
 */
export type MissingFieldTypeError = {
  missing_field: { record: Type; label: string };
};

/**
 * An error raised when a value is used **as if it were a variant (sum) type**,
 * but its actual type is *not* a variant or enum.
 *
 * **What it represents**
 * `NotAVariantTypeError` occurs when the typechecker expects a variant type:
 *
 * - In a **variant injection**:
 *   ```
 *   <Some = value> as T
 *   ```
 *   but `T` does not normalize to a variant type (structural or enum).
 *
 * - In a **variant pattern**:
 *   ```
 *   Some(x) => ...
 *   ```
 *   but the scrutinee's type is not a variant.
 *
 * The error stores the **invalid type** that was incorrectly used as a variant.
 *
 * **Examples of invalid usage**
 * - Injecting into a non‑variant type:
 *   ```
 *   <Left = 1> as Int
 *   ```
 *
 * - Pattern matching a non‑variant:
 *   ```
 *   match (1, 2) { Left(x) => ... }
 *   ```
 *
 * - Using `Some(x)` on a type that is neither:
 *   - a nominal enum (`Option<T>`)
 *   - nor a structural variant (`<Some: T | None: ()>`)
 *
 * **Why it's useful**
 * This error helps catch:
 * - Typos in variant labels
 * - Incorrect assumptions about a type’s structure
 * - Misuse of pattern matching or injections
 * - Misapplied enum constructors
 *
 * It provides a clear message about which type was expected to be a variant.
 *
 * **Where it is produced**
 * - {@link inferInjectType} — invalid variant injection
 * - {@link checkPattern} — variant pattern applied to non‑variant type
 * - {@link checkExhaustive} — scrutinee is not a variant/enum
 *
 * **Related**
 * - {@link VariantType} — structural variant type
 * - {@link EnumDefBinding} — nominal variant definition
 * - {@link InvalidVariantTypeError} — label exists in enum, but wrong label used
 * - {@link showError} — formats this error for users
 *
 * **Examples**
 *
 * Injecting into a non‑variant:
 * ```ts
 * import {
 *   injectTerm, conTerm, conType,
 *   inferType, freshState, addType,
 *   starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const bad = injectTerm("Left", conTerm("42", conType("Int")), conType("Int"));
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Not a variant type: Int"
 * ```
 *
 * Variant pattern on wrong type:
 * ```ts
 * import {
 *   checkPattern, variantPattern, varPattern,
 *   recordType, conType, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const pat = variantPattern("Some", varPattern("x"));
 * const ty  = recordType([["x", conType("Int")]]);
 *
 * console.log(showError(checkPattern(state, pat, ty).err));
 * // "Not a variant type: {x: Int}"
 * ```
 */
export type NotAVariantTypeError = { not_a_variant: Type };

/**
 * An error raised when a **variant label does not exist** in the expected
 * variant or enum type.
 *
 * **What it represents**
 * `InvalidVariantTypeError` occurs when the typechecker encounters:
 *
 * - A **variant pattern**:
 *   ```
 *   Some(x)
 *   ```
 *   but the scrutinee’s type has no `Some` constructor.
 *
 * - A **variant injection**:
 *   ```
 *   <Bad = value> as Option<Int>
 *   ```
 *   but `"Bad"` is not one of the constructors in `Option`.
 *
 * The error reports:
 * - `variant` — the *actual* variant type being matched or constructed
 * - `label` — the invalid constructor name
 *
 * This is different from {@link NotAVariantTypeError}:
 * here the type *is* a variant, but **the label is wrong**.
 *
 * **Why it's useful**
 * This error helps catch:
 * - Typos in constructor names
 * - Using the wrong constructor for a given enum
 * - Misaligned structural variant definitions
 * - Incorrect assumptions about an enum’s shape
 *
 * It provides precise diagnostic feedback about which label is not valid.
 *
 * **Where it is produced**
 * - {@link checkPattern} — when matching a label not present in the variant
 * - {@link inferInjectType} — when injecting with an unknown constructor
 * - {@link checkExhaustive} — when patterns use extraneous labels
 *
 * **Related**
 * - {@link VariantType} — structural variant representation
 * - {@link EnumDefBinding} — nominal enum metadata
 * - {@link NotAVariantTypeError} — when the type isn’t a variant at all
 * - {@link MissingCaseTypeError} — when patterns fail to cover required labels
 *
 * **Examples**
 *
 * Wrong label in a pattern:
 * ```ts
 * import {
 *   freshState, addEnum, checkPattern,
 *   variantPattern, varPattern, conType,
 *   starKind, showError
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const pat = variantPattern("Bad", varPattern("x"));
 * const ty  = conType("Option<Int>");
 *
 * console.log(showError(checkPattern(state, pat, ty).err));
 * // "Invalid variant label 'Bad' for: Option<Int>"
 * ```
 *
 * Wrong label in an injection:
 * ```ts
 * import {
 *   injectTerm, conTerm, conType, appType,
 *   freshState, addEnum, starKind, showError, inferType
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 *
 * // Invalid variant: Green
 * const bad = injectTerm("Green", conTerm("0", conType("Int")), conType("Color"));
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Invalid variant label 'Green' for: Color"
 * ```
 */
export type InvalidVariantTypeError = {
  invalid_variant_label: { variant: Type; label: string };
};

/**
 * An error raised when a `match` expression is **not exhaustive**—i.e., at
 * least one variant case is missing.
 *
 * **What it represents**
 * `MissingCaseTypeError` occurs when the typechecker determines that some
 * constructor of a variant or enum **is not handled** in a `match` expression.
 *
 * Example:
 * ```
 * enum Option<T> { None, Some(T) }
 *
 * match opt {
 *   None => 0
 * }
 * ```
 *
 * This fails because `Some(_)` is missing.
 *
 * The error stores:
 * - `label` — the **first missing constructor name**, chosen deterministically
 *
 * **Why it's useful**
 * Exhaustiveness checking ensures:
 * - You handle **every possible shape** of your data
 * - No runtime pattern‑match failures
 * - Better safety, similar to Rust/Haskell warning/error levels
 *
 * This error is crucial for preventing incomplete pattern matches over:
 * - Enums ({@link EnumDef})
 * - Structural variants ({@link VariantType})
 * - Recursive variants ({@link MuType})
 *
 * **Where it is produced**
 * - {@link checkExhaustive} — the dedicated exhaustiveness checker
 * - {@link inferMatchType} — after inferring branch types
 *
 * **Related**
 * - {@link ExtraCaseTypeError} — reports *extra* or unreachable cases
 * - {@link InvalidVariantTypeError} — wrong variant label
 * - {@link VariantPattern} — patterns involved in variant matching
 *
 * **Examples**
 *
 * Missing a case in a nominal enum:
 * ```ts
 * import {
 *   freshState, addEnum, checkExhaustive,
 *   variantPattern, varPattern, conType, starKind, showError
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red",  tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 *
 * const patterns = [
 *   variantPattern("Red", varPattern("_"))
 * ];
 *
 * const res = checkExhaustive(state, patterns, conType("Color"));
 * console.log(showError(res.err));
 * // "Non-exhaustive match: missing case 'Blue'"
 * ```
 *
 * Structural variant example:
 * ```ts
 * import {
 *   variantType, checkExhaustive,
 *   variantPattern, varPattern, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = variantType([
 *   ["Left",  { con: "Int" }],
 *   ["Right", { con: "Bool" }]
 * ]);
 *
 * const patterns = [
 *   variantPattern("Left", varPattern("x"))
 * ];
 *
 * console.log(showError(checkExhaustive(state, patterns, ty).err));
 * // "Non-exhaustive match: missing case 'Right'"
 * ```
 */
export type MissingCaseTypeError = { missing_case: { label: string } };

/**
 * An error raised when a `match` expression includes a **case that can never
 * occur**, i.e., a pattern whose label is *not part of the variant type* being
 * matched.
 *
 * **What it represents**
 * `ExtraCaseTypeError` occurs when pattern matching introduces an **extra or
 * unreachable constructor**, such as:
 *
 * ```
 * match opt {
 *   None => 0
 *   Some(x) => x
 *   Bad(y)  => y    // 'Bad' does not exist in Option<T>
 * }
 * ```
 *
 * The error stores:
 * - `label` — the extra/unreachable constructor used in the match
 *
 * This is the complement of {@link MissingCaseTypeError}, which reports missing
 * cases. `ExtraCaseTypeError` reports *invalid* cases.
 *
 * **Why it's useful**
 * This error helps catch:
 * - Typos in pattern labels
 * - Patterns intended for the wrong enum
 * - Structural variants re‑used in the wrong context
 * - Copy‑paste errors in pattern matches
 *
 * Ensuring no extra cases also helps maintain **pattern match hygiene**, keeping
 * matches predictable and well‑typed.
 *
 * **Where it is produced**
 * - {@link checkExhaustive} — detects unreachable/labeled patterns not present
 *   in the variant or enum
 * - {@link checkPattern} — when matching a constructor that does not exist for
 *   a structural variant
 *
 * **Related**
 * - {@link MissingCaseTypeError} — missing cases (under-coverage)
 * - {@link InvalidVariantTypeError} — label is invalid for injection or pattern
 * - {@link VariantPattern} — pattern form that triggers this error
 * - {@link showError} — formats this error nicely for users
 *
 * **Examples**
 *
 * Extra case in an enum match:
 * ```ts
 * import {
 *   freshState, addEnum, checkExhaustive,
 *   variantPattern, varPattern, conType, starKind, showError
 * } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red",  tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 *
 * const patterns = [
 *   variantPattern("Red", varPattern("x")),
 *   variantPattern("Green", varPattern("y"))  // extra (invalid)
 * ];
 *
 * console.log(showError(checkExhaustive(state, patterns, conType("Color")).err));
 * // "Unreachable case in match: 'Green'"
 * ```
 *
 * Extra label in structural variant matching:
 * ```ts
 * import {
 *   variantType, checkExhaustive, variantPattern,
 *   varPattern, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = variantType([
 *   ["Left",  { con: "Int" }],
 *   ["Right", { con: "Bool" }]
 * ]);
 *
 * const badPatterns = [
 *   variantPattern("Left", varPattern("x")),
 *   variantPattern("Up", varPattern("y")) // invalid label
 * ];
 *
 * console.log(showError(checkExhaustive(state, badPatterns, ty).err));
 * // "Unreachable case in match: 'Up'"
 * ```
 */
export type ExtraCaseTypeError = { extra_case: { label: string } };

/**
 * An error raised when a value is used **as if it were a tuple**, but its type
 * is *not* a tuple type.
 *
 * **What it represents**
 * `NotATupleTypeError` occurs when the typechecker expects a tuple:
 *
 * - In a **tuple projection**:
 *   ```
 *   e.0
 *   ```
 *   but `e` does *not* have a tuple type.
 *
 * - In a **tuple pattern**:
 *   ```
 *   match e { (x, y) => ... }
 *   ```
 *   but `e` is not a tuple.
 *
 * The error payload contains the **actual type** that was incorrectly treated
 * as a tuple.
 *
 * **Examples of invalid usage**
 * - `42.0` — `42 : Int` is not a tuple
 * - `{x = 1}.0` — records are not tuples
 * - `<Left=1>.0` — variants are not tuples
 * - Using `(x, y)` to match a non‑tuple value
 *
 * **Why it's useful**
 * This error catches:
 * - Misuse of tuple syntax
 * - Confusion between tuples and records
 * - Incorrect destructuring in patterns
 * - Accidental attempts to project non‑tuple values
 *
 * It provides a clear diagnostic with the actual offending type.
 *
 * **Where it is produced**
 * - {@link inferTupleProjectType} — tuple index projection
 * - {@link checkTuplePattern} — destructuring pattern `(p₁, p₂, …)`
 * - {@link checkPattern} — general pattern context
 *
 * **Related**
 * - {@link TupleType} — valid tuple types `(τ₁, τ₂, …)`
 * - {@link tupleTerm} — constructing tuple values
 * - {@link tuplePattern} — destructuring tuple patterns
 * - {@link TupleIndexOutofBoundsTypeError} — when it *is* a tuple but index is invalid
 *
 * **Examples**
 *
 * Projecting a non‑tuple:
 * ```ts
 * import {
 *   projectTerm, conTerm, conType,
 *   tupleProjectTerm, inferType,
 *   freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const bad = tupleProjectTerm(conTerm("42", conType("Int")), 0);
 * console.log(showError(inferType(state, bad).err));
 * // "Not a tuple type: Int"
 * ```
 *
 * Tuple pattern on a non‑tuple:
 * ```ts
 * import {
 *   checkPattern, tuplePattern, varPattern,
 *   recordType, conType, freshState, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 *
 * const pat = tuplePattern([varPattern("a"), varPattern("b")]);
 * const ty  = recordType([["x", conType("Int")]]);
 *
 * console.log(showError(checkPattern(state, pat, ty).err));
 * // "Not a tuple type: {x: Int}"
 * ```
 */
export type NotATupleTypeError = { not_a_tuple: Type };

/**
 * An error raised when projecting a tuple index that is **out of bounds**.
 *
 * **What it represents**
 * `TupleIndexOutofBoundsTypeError` occurs when the typechecker encounters a
 * tuple projection:
 *
 * ```
 * e.i
 * ```
 *
 * but the index `i` is not valid for the tuple’s arity.
 *
 * Examples:
 * - `(1, 2).3`     → tuple has length 2, but index 3 was requested
 * - `().0`         → the unit tuple has length 0
 * - `(x).1`        → a single‑element tuple has only index 0
 *
 * The error includes:
 * - `tuple` — the actual tuple type found
 * - `index` — the invalid index used
 *
 * **Why it's useful**
 * This error helps identify:
 * - Typos in tuple indexing
 * - Incorrect assumptions about tuple size
 * - Mismatches between pattern shape and actual data
 *
 * It is raised *only when the callee is a tuple*, so it is distinct from
 * {@link NotATupleTypeError}.
 *
 * **Where it is produced**
 * - {@link inferTupleProjectType} — primary checker for tuple projections
 * - {@link checkTuplePattern} — when matching tuple patterns with incorrect arity
 *
 * **Related**
 * - {@link TupleType} — structural representation of tuple types
 * - {@link tupleProjectTerm} — AST node for tuple indexing
 * - {@link NotATupleTypeError} — when the scrutinee is not a tuple at all
 *
 * **Examples**
 *
 * Projecting an out‑of‑bounds index:
 * ```ts
 * import {
 *   tupleTerm, conTerm, conType,
 *   tupleProjectTerm, inferType,
 *   freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int"))]); // (1,)
 *
 * const bad = tupleProjectTerm(tup, 1); // index 1 out of range
 * console.log(showError(inferType(state, bad).err));
 * // "Tuple index out of bounds:
 * //    Tuple: (Int)
 * //    Index: 1"
 * ```
 *
 * Indexing unit:
 * ```ts
 * import { tupleProjectTerm, tupleTerm, inferType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const unit = tupleTerm([]);  // ()
 *
 * console.log(showError(inferType(state, tupleProjectTerm(unit, 0)).err));
 * // "Tuple index out of bounds"
 * ```
 *
 * Tuple pattern mismatch example:
 * ```ts
 * import {
 *   checkPattern, tuplePattern, varPattern,
 *   tupleType, conType, addType, freshState, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = tuplePattern([varPattern("x"), varPattern("y")]); // (x, y)
 * const ty  = tupleType([conType("Int")]);                     // (Int)
 *
 * // During checking, index 1 is out-of-bounds
 * console.log(showError(checkPattern(state, pat, ty).err));
 * ```
 */
export type TupleIndexOutofBoundsTypeError = {
  tuple_index_out_of_bounds: { tuple: Type; index: number };
};

/**
 * An error raised when the typechecker cannot find a **trait implementation**
 * for a required trait–type combination.
 *
 * **What it represents**
 * `MissingTraitImplError` means the system was asked to resolve a trait
 * constraint:
 *
 * ```
 * Trait<T>
 * ```
 *
 * but no dictionary exists in the context (`Γ`) that implements the trait for
 * that type.
 *
 * For example:
 * - `Eq<String>` with no `impl Eq for String`
 * - `Functor<F>` with no matching implementation for the constructor `F`
 *
 * The error includes:
 * - `trait` — the missing trait name (`"Eq"`, `"Ord"`, `"Functor"`, …)
 * - `type` — the type for which no implementation exists
 *
 * **Why it's useful**
 * This error pinpoints missing or incorrect trait implementations. It helps
 * detect:
 * - missing `impl` blocks
 * - incorrect types inside trait dictionaries
 * - forgetting to register the implementation with {@link addTraitImpl}
 * - mismatches between expected and actual trait instances
 *
 * It is essential for:
 * - trait‑bounded polymorphism (`∀Self where Eq<Self>. …`)
 * - dictionary‑passing resolution
 * - verifying completeness of trait instances
 *
 * **Where it is produced**
 * - {@link checkTraitConstraints} — when resolving trait bounds
 * - {@link checkTraitImplementation} — when resolving a single constraint
 * - {@link inferTraitAppType} — when applying a trait‑lambda to a type
 *
 * **Related**
 * - {@link TraitImplBinding} — stores trait implementations
 * - {@link checkTraitConstraints} — batch resolution
 * - {@link TraitConstraint} — required constraints
 * - {@link showError} — formats this error for user display
 *
 * **Examples**
 *
 * Missing trait implementation for a concrete type:
 * ```ts
 * import {
 *   freshState, addType, addTraitDef, checkTraitImplementation,
 *   conType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", starKind).ok;
 *
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", { con: "Bool" }]
 * ]).ok;
 *
 * const res = checkTraitImplementation(state, "Eq", conType("String"));
 * console.log(showError(res.err));
 * // "Missing trait implementation:
 * //    Trait: Eq
 * //    Type:  String"
 * ```
 *
 * Missing implementation inside trait constraints:
 * ```ts
 * import {
 *   checkTraitConstraints, conType, freshState
 * } from "system-f-omega";
 *
 * const state = freshState();  // no impls
 *
 * const constraints = [{ trait: "Show", type: conType("Int") }];
 * console.log(checkTraitConstraints(state, constraints).err);
 * // { missing_trait_impl: { trait: "Show", type: Int } }
 * ```
 */
export type MissingTraitImplError = {
  missing_trait_impl: { trait: string; type: Type };
};

/**
 * An error raised when a trait dictionary is **missing a required method**, or
 * when code attempts to access a method that the trait does not define.
 *
 * **What it represents**
 * `MissingMethodError` indicates a mismatch between:
 *
 * - a trait’s **declared method list** (in {@link TraitDef}), and
 * - the methods provided by a dictionary ({@link DictTerm}) or accessed through
 *   a {@link TraitMethodTerm}.
 *
 * This can happen when:
 * - A dictionary omits one of the trait’s required methods
 * - A trait method projection (`dict.m`) refers to a method not in the trait
 * - A trait definition changes but existing dictionaries weren’t updated
 *
 * The error stores:
 * - `trait` — the trait name (`"Eq"`, `"Ord"`, `"Show"`, …)
 * - `method` — the method name that was missing
 *
 * **Why it's useful**
 * This error ensures trait implementations are **complete** and consistent:
 * - Prevents partially implemented typeclasses
 * - Ensures dictionary‑passing works correctly
 * - Avoids runtime failures due to missing evidence
 *
 * In effect, this enforces typeclass‑like *interface completeness*.
 *
 * **Where it is produced**
 * - {@link inferDictType} — when validating a dictionary against a trait def
 * - {@link inferTraitMethodType} — when projecting a method from a dictionary
 * - {@link checkTraitConstraints} — validating evidence for trait‑bounded polymorphism
 *
 * **Related**
 * - {@link TraitDef} — source of required method signatures
 * - {@link DictTerm} — dictionary providing method implementations
 * - {@link TraitMethodTerm} — projects dictionary methods
 * - {@link TraitImplBinding} — stored trait implementations
 *
 * **Examples**
 *
 * Dictionary missing a required method:
 * ```ts
 * import {
 *   freshState, addType, addTraitDef,
 *   dictTerm, inferType, conType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", conType("Bool")],
 *   ["lt", conType("Bool")]
 * ]).ok;
 *
 * const incomplete = dictTerm("Eq", conType("Int"), [
 *   ["eq", conType("Bool")]  // missing "lt"
 * ]);
 *
 * console.log(showError(inferType(state, incomplete).err));
 * // "Missing method 'lt' in trait 'Eq'"
 * ```
 *
 * Accessing a method not in the trait:
 * ```ts
 * import {
 *   freshState, addType, addTraitDef, traitMethodTerm,
 *   dictTerm, conType, starKind, showError, inferType
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", conType("Bool")]
 * ]).ok;
 *
 * const d = dictTerm("Eq", conType("Int"), [["eq", conType("Bool")]]);
 *
 * const bad = traitMethodTerm(d, "lt");  // 'lt' not in Eq
 * console.log(showError(inferType(state, bad).err));
 * // "Missing method 'lt' in trait 'Eq'"
 * ```
 */
export type MissingMethodError = {
  missing_method: { trait: string; method: string };
};

/**
 * An error raised when a **trait application supplies the wrong number of
 * dictionaries** compared to the trait constraints required by a
 * {@link BoundedForallType}.
 *
 * **What it represents**
 * Trait‑polymorphic functions (introduced via {@link TraitLamTerm}) may require
 * one or more trait constraints:
 *
 * ```
 * ΛSelf where Eq<Self>, Show<Self>. body
 * ```
 *
 * Instantiating such a function requires providing **one dictionary per
 * constraint**, in the correct order:
 *
 * ```
 * f[Int] with { eqIntDict, showIntDict }
 * ```
 *
 * `WrongNumberOfDictsError` occurs when:
 * - *Too few* dictionaries are provided
 * - *Too many* dictionaries are provided
 *
 * The error reports:
 * - `expected` — how many dictionaries the trait lambda needs
 * - `actual` — how many were supplied
 *
 * **Why it's useful**
 * This error ensures that:
 * - All required trait evidence is provided
 * - No extraneous evidence is passed
 * - Trait‑bounded polymorphism behaves like typeclass application
 *
 * It prevents confusing runtime behavior by enforcing exact dictionary arity.
 *
 * **Where it is produced**
 * - {@link inferTraitAppType} — the main checker for trait application
 * - Possibly surfaced through {@link checkTraitConstraints}
 *
 * **Related**
 * - {@link TraitAppTerm} — application with dictionary arguments
 * - {@link TraitLamTerm} — introduces trait constraints
 * - {@link TraitConstraint} — describes each required dictionary
 * - {@link MissingTraitImplError} — used when a required dictionary is missing or unresolved
 *
 * **Examples**
 *
 * Too few dictionaries:
 * ```ts
 * import {
 *   traitLamTerm, traitAppTerm, varType, conType,
 *   starKind, inferType, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const lam = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   { var: "body" }
 * );
 *
 * const bad = traitAppTerm(lam, conType("Int"), []);  // missing 1 dictionary
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Wrong number of dictionaries provided:
 * //    Expected: 1
 * //    Actual:   0"
 * ```
 *
 * Too many dictionaries:
 * ```ts
 * import {
 *   traitAppTerm, traitLamTerm, varType, conType,
 *   starKind, dictTerm, inferType, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const lam = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [],  // no constraints
 *   { var: "body" }
 * );
 *
 * const extraDict = dictTerm("Eq", conType("Int"), []);
 * const bad = traitAppTerm(lam, conType("Int"), [extraDict]);  // provided 1, expected 0
 *
 * console.log(showError(inferType(state, bad).err));
 * // "Wrong number of dictionaries provided:
 * //    Expected: 0
 * //    Actual:   1"
 * ```
 */
export type WrongNumberOfDictsError = {
  wrong_number_of_dicts: { expected: number; actual: number };
};

/**
 * An error raised when a type binding or declaration receives a **kind that the
 * typechecker did not expect**.
 *
 * **What it represents**
 * `UnexpectedKindError` indicates that a type, constructor, or parameter was
 * assigned a kind that violates the expected definition or context rules.
 *
 * This typically occurs when:
 * - A type is declared with a kind that doesn't match expected usage
 *   (e.g., giving `Int` the kind `* → *` instead of `*`)
 * - A type alias or enum provides a kind inconsistent with its parameters
 * - A type definition is reused with an incompatible kind in a different module
 * - A module import renames a type but kind mismatches appear afterward
 *
 * The error reports:
 * - `name` — the binding that received the wrong kind
 * - `kind` — the unexpected kind that was encountered
 *
 * **Why it's useful**
 * This error helps catch:
 * - Incorrect HKT declarations
 * - Mistakes in enum or alias parameterization
 * - Mismatched kinds across modules during import
 * - Conceptual misuse of type constructors
 *
 * It acts as a safeguard ensuring that type constructors behave consistently
 * across the entire program.
 *
 * **Where it is produced**
 * Although rare, this error may surface in:
 * - {@link addType} — when a declared kind contradicts expected usage
 * - {@link addEnum} — inconsistencies in enum parameter kinds
 * - {@link addTypeAlias} — kind mismatch in type alias declarations
 * - {@link importModule} — when imported types conflict in kind
 *
 * **Related**
 * - {@link Kind} — describes allowed kinds (`*` and `κ₁ → κ₂`)
 * - {@link KindMismatchTypeError} — for mismatch between *two* kinds
 * - {@link TypeBinding} — associates names with kinds
 * - {@link checkKind} — computes and validates kind information
 *
 * **Examples**
 *
 * Declaring a primitive with the wrong kind:
 * ```ts
 * import { addType, arrowKind, starKind, freshState, showError } from "system-f-omega";
 *
 * let state = freshState();
 *
 * // Suppose Int is expected to be :: *
 * const res = addType(state, "Int", arrowKind(starKind, starKind));  // invalid
 *
 * console.log(showError(res.err));
 * // "Unexpected kind assigned to 'Int': (* → *)"
 * ```
 *
 * Incorrect enum parameterization:
 * ```ts
 * import { addEnum, starKind, tupleType, showError, freshState } from "system-f-omega";
 *
 * let state = freshState();
 *
 * // Wrong kinds for parameters in enum definition
 * const res = addEnum(state, "Bad", ["A"], [tupleType([])], [["Case", tupleType([])]]);
 *
 * console.log(showError(res.err));  // Unexpected kind assigned in enum definition
 * ```
 *
 * Importing a conflicting type binding:
 * ```ts
 * import { importModule, starKind, arrowKind, addType, freshState } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "List", arrowKind(starKind, starKind)).ok; // List :: * → *
 *
 * let into = freshState();
 * into = addType(into, "List", starKind).ok; // Incorrect :: *
 *
 * const res = importModule({ from, into, roots: ["List"] });
 * console.log("unexpected_kind" in res.err);  // true
 * ```
 */
export type UnexpectedKindError = {
  unexpected_kind: { name: string; kind: Kind };
};

/**
 * An error raised when the module importer detects a **cyclic dependency
 * between bindings**, such as:
 *
 * ```
 * A depends on B
 * B depends on C
 * C depends on A    // cycle!
 * ```
 *
 * **What it represents**
 * `CircularImportError` is produced when {@link importModule} or
 * {@link collectDependencies} discovers that importing certain bindings would
 * create a recursive loop in the dependency graph.
 *
 * The error includes:
 * - `name` — the binding where the cycle was detected
 * - `cycle` — the sequence of names forming the cycle (e.g. `["A", "B", "A"]`)
 *
 * Cycles may occur in:
 * - Type aliases referencing each other
 * - Enums referencing aliases which refer back to the enum
 * - Traits referencing types that reference the trait
 * - Deep import graphs across modules
 *
 * **Why it's useful**
 * This error prevents:
 * - infinite recursive type or alias expansion
 * - invalid recursive module structures
 * - nonsensical or non‑terminating renaming during import
 *
 * It ensures imported code is **well‑formed, acyclic**, and safe to normalize.
 *
 * **Where it is produced**
 * - {@link collectDependencies} — DFS traversal detects cycles
 * - {@link importModule} — reports cycles before renaming and merging
 *
 * **Related**
 * - {@link DuplicateBindingError} — name conflicts during import
 * - {@link importModule} — full module importer
 * - {@link bindingDependencies} — computes per‑binding dependencies
 *
 * **Examples**
 *
 * Direct cycle:
 * ```ts
 * import { freshState, collectDependencies, addTypeAlias,
 *          typeAliasBinding, conType, showError } from "system-f-omega";
 *
 * let state = freshState();
 *
 * // A -> B -> A
 * state.ctx.push(typeAliasBinding("A", [], [], conType("B")));
 * state.ctx.push(typeAliasBinding("B", [], [], conType("A")));
 *
 * const res = collectDependencies(state, ["A"]);
 * console.log(showError(res.err));
 * // Circular import detected involving 'A': Cycle: A → B → A
 * ```
 *
 * Cycle through intermediate bindings:
 * ```ts
 * import { freshState, collectDependencies, typeAliasBinding, conType, showError } from "system-f-omega";
 *
 * let state = freshState();
 *
 * state.ctx.push(typeAliasBinding("X", [], [], conType("Y")));
 * state.ctx.push(typeAliasBinding("Y", [], [], conType("Z")));
 * state.ctx.push(typeAliasBinding("Z", [], [], conType("X"))); // closes the loop
 *
 * console.log(showError(collectDependencies(state, ["X"]).err));
 * // Cycle: X → Y → Z → X
 * ```
 *
 * During module import:
 * ```ts
 * import { importModule, freshState, showError } from "system-f-omega";
 *
 * const from = freshState();   // assume contains a cycle
 * const into = freshState();
 *
 * const result = importModule({ from, into, roots: ["A"] });
 * console.log(showError(result.err));  // circular import error
 * ```
 */
export type CircularImportError = {
  circular_import: { name: string; cycle: string[] };
};

/**
 * An error raised when attempting to add a **binding with a name that already
 * exists** in the typing context (`Γ`), without permission to override it.
 *
 * **What it represents**
 * `DuplicateBindingError` is produced when the typechecker encounters a
 * redefinition of:
 * - a term variable (`x`)
 * - a type constructor (`Int`)
 * - a trait (`Eq`)
 * - a dictionary variable (`eqInt`)
 * - an enum or type alias
 *
 * The error includes:
 * - `name` — the conflicting identifier
 * - `existing` — the binding currently in the context
 * - `incoming` — the new binding that attempted to overwrite it
 *
 * Example:
 * ```
 * Int :: *
 * Int :: *
 *         ↑ duplicate!
 * ```
 *
 * **Why it's useful**
 * This error prevents:
 * - accidental shadowing of important definitions
 * - clashes between modules during {@link importModule}
 * - inconsistencies between type constructors
 * - silently overwriting dictionaries or implementations
 *
 * It ensures that the global context remains well‑formed and deterministic.
 *
 * **When it occurs**
 * - {@link addType} — type already exists
 * - {@link addTerm} — term name already used
 * - {@link addTraitDef} — trait redefined
 * - {@link addEnum} — enum name reused
 * - {@link addTypeAlias} — alias name collides
 * - {@link importModule} — merging modules without `allowOverrides`
 *
 * **Related**
 * - {@link bindingName} — extracts the name used for duplicate checking
 * - {@link renameBinding} — avoids conflicts during module import
 * - {@link CircularImportError} — similar import‑time structural error
 * - {@link showError} — formats duplicate binding errors nicely
 *
 * **Examples**
 *
 * Duplicating a type binding:
 * ```ts
 * import {
 *   freshState, addType, starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = addType(state, "Int", starKind);  // duplicate
 * console.log(showError(result.err));
 * // Duplicate binding for 'Int':
 * //   Existing: Type: Int = *
 * //   Incoming: Type: Int = *
 * ```
 *
 * Duplicating a term binding:
 * ```ts
 * import {
 *   freshState, addType, addTerm, conTerm, conType,
 *   starKind, showError
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * const result = addTerm(state, "x", conTerm("7", conType("Int")));  // duplicate
 * console.log(showError(result.err));
 * ```
 *
 * Duplicate binding during module import:
 * ```ts
 * import { freshState, addType, importModule, starKind, showError } from "system-f-omega";
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 *
 * const result = importModule({ from, into, roots: ["Int"] });
 * console.log(showError(result.err));  // duplicate binding error
 * ```
 */
export type DuplicateBindingError = {
  duplicate_binding: {
    name: string;
    existing: Binding;
    incoming: Binding;
  };
};

/**
 * A tagged union of **all possible typechecking errors** produced by the
 * typechecker.
 *
 * **What it represents**
 * `TypingError` collects every error that can arise during:
 * - type inference (`inferType`)
 * - type checking (`checkType`)
 * - kind checking (`checkKind`)
 - pattern matching (`checkPattern`, `checkExhaustive`)
 * - trait resolution (`checkTraitImplementation`, `checkTraitConstraints`)
 * - module importing (`importModule`)
 * - type unification (`unifyTypes`)
 *
 * Each error variant provides precise information about what went wrong.
 *
 * **Categories of errors**
 *
 * **Lookup / Missing definitions**
 * - {@link UnboundTypeError} — missing type or variable  
 * - {@link MissingTraitImplError} — missing trait instance  
 * - {@link MissingMethodError} — missing required trait method  
 * - {@link MissingFieldTypeError} — missing record field  
 * - {@link MissingCaseTypeError} — missing match case  
 *
 * **Kind errors**
 * - {@link KindMismatchTypeError} — kind mismatch  
 * - {@link UnexpectedKindError} — invalid or unexpected kind  
 * - {@link NotATypeFunctionTypeError} — type application on a non‑function kind  
 *
 * **Type errors**
 * - {@link TypeMismatchTypeError} — incompatible types  
 * - {@link CyclicTypeError} — infinite/cyclic type detected  
 * - {@link WrongNumberOfDictsError} — mismatched dictionary evidence arity  
 *
 * **Data shape errors**
 * - {@link NotARecordTypeError} — used as record but isn’t  
 * - {@link NotATupleTypeError} — used as tuple but isn’t  
 * - {@link TupleIndexOutofBoundsTypeError} — invalid tuple projection  
 * - {@link NotAVariantTypeError} — used as variant but isn’t  
 * - {@link InvalidVariantTypeError} — invalid variant label  
 * - {@link ExtraCaseTypeError} — extraneous match case not present in data  
 *
 * **Function errors**
 * - {@link NotAFunctionTypeError} — applying non‑function value  
 *
 * **Module/import errors**
 * - {@link CircularImportError} — dependency cycle during module import  
 * - {@link DuplicateBindingError} — conflicting name in context  
 *
 * **Why it’s useful**
 * Collecting all errors under a single type allows:
 * - clean and uniform error handling through `Result<TypingError, T>`  
 * - pattern matching on error kinds  
 * - user‑friendly formatting via {@link showError}  
 * - IDE tooling and REPLs to surface precise diagnostics  
 *
 * **Where it is used**
 * - All high‑level APIs return `Result<TypingError, T>`  
 * - {@link inferType}, {@link checkType}, {@link solveConstraints}  
 * - {@link importModule}  
 * - {@link showError} understands every variant  
 *
 * **Example**
 * ```ts
 * import {
 *   freshState, inferType, varTerm,
 *   showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const res = inferType(state, varTerm("missing"));
 *
 * if ("err" in res) {
 *   console.log(showError(res.err));  // "Unbound identifier: missing"
 * }
 * ```
 *
 * @see {@link showError} for pretty‑printing all errors
 * @see {@link inferType} and {@link checkType} which produce these errors
 */
export type TypingError =
  | CircularImportError
  | CyclicTypeError
  | DuplicateBindingError
  | ExtraCaseTypeError
  | InvalidVariantTypeError
  | KindMismatchTypeError
  | MissingCaseTypeError
  | MissingFieldTypeError
  | MissingMethodError
  | MissingTraitImplError
  | NotAFunctionTypeError
  | NotARecordTypeError
  | NotATupleTypeError
  | NotATypeFunctionTypeError
  | NotAVariantTypeError
  | TupleIndexOutofBoundsTypeError
  | TypeMismatchTypeError
  | UnboundTypeError
  | UnexpectedKindError
  | WrongNumberOfDictsError;

/**
 * A **type equality constraint** of the form `left = right`, used by the
 * constraint‑based unification engine.
 *
 * **What it represents**
 * `TypeEqConstraint` is an instruction telling the solver:
 *
 * > “These two types must be equal. Unify them.”
 *
 * It is the fundamental building block of type inference under a worklist
 * algorithm.
 *
 * Whenever the typechecker needs to enforce that two types match (e.g.
 * function argument matching, subsumption, pattern checking), it generates
 * a `type_eq` constraint and pushes it into the solver’s worklist.
 *
 * **Why it's useful**
 * TypeEq constraints allow:
 * - Incremental, ordered unification
 * - Collecting many equality checks before solving
 * - Supporting higher‑kinded unification
 * - Delaying constraints until enough information is learned
 * - Explicit control over meta‑variable solving
 *
 * They allow complex typing rules to remain simple: rules only generate
 * constraints; the solver performs the unification.
 *
 * **Where it is used**
 * - {@link unifyTypes} — consumes type equality constraints
 * - {@link solveConstraints} — processes the entire worklist
 * - {@link subsumes} — adds constraints for subtyping
 * - {@link checkPattern} — generates constraints when matching patterns
 * - {@link checkType} — produces equality constraints for expected types
 *
 * **Related**
 * - {@link KindEqConstraint} — the analogous constraint for kinds
 * - {@link HasTypeConstraint} — deferred type checking
 * - {@link HasKindConstraint} — deferred kind checking
 * - {@link processConstraint} — dispatches constraint solving
 *
 * **Examples**
 *
 * Creating a simple type‑equality constraint:
 * ```ts
 * import { typeEq, varType, conType } from "system-f-omega";
 *
 * const eq = typeEq(varType("A"), conType("Int"));
 * // { type_eq: { left: A, right: Int } }
 * ```
 *
 * Solving a single constraint:
 * ```ts
 * import {
 *   freshState, solveConstraints,
 *   typeEq, varType, conType
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq(varType("a"), conType("Int"))];
 * const subst = new Map();
 *
 * const result = solveConstraints(state, worklist, subst);
 * console.log(subst.get("a"));  // { con: "Int" }
 * ```
 *
 * Constraints generated during type inference:
 * ```ts
 * import {
 *   freshState, unifyTypes,
 *   arrowType, varType, conType
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const worklist = [];
 *
 * unifyTypes(
 *   state,
 *   arrowType(varType("A"), varType("B")),
 *   arrowType(conType("Int"), conType("Bool")),
 *   worklist,
 *   subst
 * );
 *
 * // worklist now contains:
 * //  A = Int
 * //  B = Bool
 * ```
 */
export type TypeEqConstraint = { type_eq: { left: Type; right: Type } };

/**
 * A **kind equality constraint** of the form `left = right`, used during
 * higher‑kinded type checking.
 *
 * **What it represents**
 * `KindEqConstraint` tells the solver:
 *
 * > “These two kinds must be equal—unify them.”
 *
 * This is the kind‑level analogue of {@link TypeEqConstraint}.
 * It is generated when:
 * - Applying a higher‑kinded type (`F<T>`)
 * - Instantiating polymorphic types with kinded type parameters
 * - Checking lambda kinds in {@link LamType}
 * - Ensuring record/variant fields have kind `*`
 *
 * **Why it's useful**
 * Kind equality constraints enable:
 * - Proper checking of type‑level functions (`* → *`, `(* → *) → *`, etc.)
 * - Ensuring type constructors are applied correctly
 * - Supporting System F‑omega’s higher‑kinded polymorphism
 * - Clean separation between *generating constraints* and *solving them*
 *
 * They allow kind checking to be deferred until enough meta‑kind information is
 * known.
 *
 * **Where it is used**
 * - {@link checkAppKind} — verifies constructor application kinds
 * - {@link solveConstraints} — processes kind equality constraints
 * - {@link unifyKinds} — performs structural kind unification
 * - {@link HasKindConstraint} — may produce kind equality constraints indirectly
 *
 * **Related**
 * - {@link TypeEqConstraint} — type‑level equality constraint
 * - {@link HasKindConstraint} — deferred kind check constraint
 * - {@link kindsEqual} — structural kind equality
 * - {@link showError} — formats kind errors
 *
 * **Examples**
 *
 * A simple kind‑equality constraint:
 * ```ts
 * import { kindEq, starKind } from "system-f-omega";
 *
 * const c = kindEq(starKind, starKind);
 * // { kind_eq: { left: *, right: * } }
 * ```
 *
 * Solving kind constraints:
 * ```ts
 * import { freshState, solveConstraints, kindEq, starKind, arrowKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [
 *   kindEq(arrowKind(starKind, starKind), arrowKind(starKind, starKind))
 * ];
 *
 * console.log("ok" in solveConstraints(state, worklist));  // true
 * ```
 *
 * Detecting kind mismatch:
 * ```ts
 * import { freshState, solveConstraints, kindEq, starKind, arrowKind, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const bad = [kindEq(starKind, arrowKind(starKind, starKind))];
 *
 * console.log(showError(solveConstraints(state, bad).err));
 * // "Kind mismatch: Expected: *  Actual: (* → *)"
 * ```
 */
export type KindEqConstraint = { kind_eq: { left: Kind; right: Kind } };

/**
 * A **deferred kind-checking constraint** of the form:
 *
 * ```
 * Γ ⊢ ty : kind
 * ```
 *
 * meaning “check that type `ty` has kind `kind`, using the stored
 * `TypeCheckerState`.”
 *
 * **What it represents**
 * `HasKindConstraint` is added to the solver’s worklist when the typechecker
 * needs to **delay a kind check** until more information is known—usually
 * because:
 *
 * - Meta‑variables (`?N`) must first be solved
 * - Type-level normalization may reveal new structure
 * - Higher‑kinded unification depends on constraints processed earlier
 *
 * The constraint stores:
 * - `ty` — the type whose kind must be checked
 * - `kind` — the expected kind
 * - `state` — a snapshot of the typechecker state to use for kind checking
 *
 * When processed, the solver:
 * 1. Runs `checkKind(state, ty)`
 * 2. Generates a {@link KindEqConstraint} equating the inferred and expected kind
 *
 * **Why it's useful**
 * Deferred kind checking enables:
 * - Correct higher‑kinded type inference
 * - Avoiding premature errors when meta‑vars are not yet solved
 * - Smooth interaction between unification, normalization, and kind inference
 *
 * Without deferred constraints, many valid programs involving type‑level lambdas,
 * polymorphism, or trait‑bounded types would fail too early.
 *
 * **Where it is used**
 * - Automatically introduced by certain typing rules that rely on kind
 *   information not yet available
 * - Processed by {@link processConstraint} and {@link solveConstraints}
 * - Used in type-level normalization paths that need delayed kind validation
 *
 * **Related**
 * - {@link KindEqConstraint} — constraint generated after a deferred check
 * - {@link TypeEqConstraint} — analogous mechanism for type equality
 * - {@link checkKind} — performs actual kind inference
 * - {@link processConstraint} — executes deferred kind checking
 *
 * **Examples**
 *
 * Deferring a kind check:
 * ```ts
 * import {
 *   hasKind, lamType, varType, starKind,
 *   freshState, solveConstraints, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * // λX::*. X   has kind * → *
 * const ty = lamType("X", starKind, varType("X"));
 *
 * const worklist = [
 *   hasKind(ty, starKind, state)  // Expect kind *, but actual is * → *
 * ];
 *
 * const result = solveConstraints(state, worklist);
 * console.log(showError(result.err));
 * // "Kind mismatch: Expected: * Actual: (* → *)"
 * ```
 *
 * A valid deferred check:
 * ```ts
 * import { hasKind, conType, starKind, freshState, solveConstraints } from "system-f-omega";
 *
 * const state = freshState();
 * const w = [hasKind(conType("Int"), starKind, state)];
 *
 * console.log("ok" in solveConstraints(state, w));  // true
 * ```
 */
export type HasKindConstraint = {
  has_kind: { ty: Type; kind: Kind; state: TypeCheckerState };
};

/**
 * A **deferred type-checking constraint** of the form:
 *
 * ```
 * Γ ⊢ term : ty
 * ```
 *
 * meaning “infer the type of `term` later, and unify it with the expected
 * type `ty`.”
 *
 * **What it represents**
 * `HasTypeConstraint` is added to the solver’s worklist when the typechecker
 * wants to **delay the type inference or checking** of a subterm.
 *
 * This is typically necessary when:
 * - Unification has not yet solved enough meta‑variables
 * - Let‑expressions or trait methods rely on types discovered later
 * - Polymorphic or trait‑bounded expressions require staged resolution
 * - Complex expressions produce constraints that must be solved before checking a subterm
 *
 * When processed, the solver:
 * 1. Runs `inferType(state, term)`
 * 2. Produces a {@link TypeEqConstraint} equating the inferred type with `ty`
 *
 * **Why it's useful**
 * Deferred type checking enables:
 * - Constraint‑based typing (worklist‑driven inference)
 * - Handling forward references and staged type reconstruction
 * - Allowing type inference to proceed even when some information is missing
 * - Let‑polymorphism and trait checking without premature failure
 *
 * Without this mechanism, many programs would fail early simply because the
 * typechecker had not yet solved enough constraints to infer nested types.
 *
 * **Where it is used**
 * - Pattern checking and record/variant matching
 * - Dictionary validation in {@link inferDictType}
 * - Trait‑bounded polymorphism and trait applications
 * - Inference paths that rely on staged resolution
 *
 * **Related**
 * - {@link TypeEqConstraint} — produced after deferring the check
 * - {@link HasKindConstraint} — analogous mechanism for deferred kind checking
 * - {@link processConstraint} — executes deferred inference
 * - {@link inferType} — used to infer the type of the deferred term
 *
 * **Examples**
 *
 * Deferred typecheck for a lambda value:
 * ```ts
 * import {
 *   hasType, lamTerm, varTerm, conType,
 *   arrowType, freshState, solveConstraints, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const term = lamTerm("x", conType("Int"), varTerm("x"));
 *
 * const worklist = [
 *   hasType(term, arrowType(conType("Int"), conType("Int")), state)
 * ];
 *
 * console.log("ok" in solveConstraints(state, worklist));  // true
 * ```
 *
 * Using deferred typing for trait dictionary validation:
 * ```ts
 * import {
 *   hasType, dictTerm, conType, freshState, solveConstraints
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const dict = dictTerm("Eq", conType("Int"), [["eq", { var: "impl" }]]);
 *
 * const w = [hasType(dict, conType("Bool"), state)];  // obviously wrong
 *
 * console.log("err" in solveConstraints(state, w));  // true
 * ```
 */
export type HasTypeConstraint = {
  has_type: { term: Term; ty: Type; state: TypeCheckerState };
};

/**
 * A **worklist constraint** used by the typechecker’s unification engine.
 *
 * This union covers all kinds of constraints that may appear in the solver:
 *
 * 1. **Type equality** — {@link TypeEqConstraint}
 *    Ensures two types must be equal (`τ₁ = τ₂`).
 *
 * 2. **Kind equality** — {@link KindEqConstraint}
 *    Ensures two kinds match (`κ₁ = κ₂`).
 *
 * 3. **Deferred kind checking** — {@link HasKindConstraint}
 *    Postpones checking `Γ ⊢ τ : κ` until more information is known.
 *
 * 4. **Deferred type checking** — {@link HasTypeConstraint}
 *    Postpones checking `Γ ⊢ e : τ` until constraints solve enough meta‑vars.
 *
 * **What it represents**
 * `Constraint` is the atomic unit of the **worklist‑based solver** in the
 * typechecker.
 *
 * Constraint generation happens during type inference whenever the typechecker
 * wants to *require* something but not necessarily solve it immediately.
 *
 * The solver (`solveConstraints`) repeatedly processes these constraints until
 * no constraints remain or an error occurs.
 *
 * **Why it's useful**
 * Constraints allow the typechecker to:
 * - Defer decisions until enough information is available
 * - Perform unification incrementally
 * - Support higher‑kinded polymorphism
 * - Cleanly separate constraint generation from solving
 * - Simultaneously solve many dependent equations
 *
 * This makes the typechecker more expressive and more predictable.
 *
 * **Where it is used**
 * - {@link unifyTypes} → pushes {@link TypeEqConstraint}
 * - {@link checkAppKind} → pushes {@link KindEqConstraint}
 * - {@link inferDictType} → often pushes {@link HasTypeConstraint}
 * - {@link solveConstraints} and {@link processConstraint} → consume constraints
 *
 * **Related**
 * - {@link TypeEqConstraint} — type equality
 * - {@link KindEqConstraint} — kind equality
 * - {@link HasKindConstraint} — deferred kind checking
 * - {@link HasTypeConstraint} — deferred type checking
 * - {@link solveConstraints} — solver worklist engine
 *
 * **Examples**
 *
 * Building a worklist manually:
 * ```ts
 * import {
 *   typeEq, kindEq, hasKind, hasType,
 *   starKind, conType, varType, freshState
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const constraints: Constraint[] = [
 *   typeEq(varType("A"), conType("Int")),
 *   kindEq(starKind, starKind),
 *   hasKind(conType("Bool"), starKind, state),
 *   hasType({ var: "x" }, conType("String"), state)
 * ];
 * ```
 *
 * Solving constraints:
 * ```ts
 * import { solveConstraints } from "system-f-omega";
 *
 * const subst = new Map();
 * const result = solveConstraints(state, constraints, subst);
 * // If successful, `subst` now contains inferred meta-type solutions.
 * ```
 */
export type Constraint =
  | TypeEqConstraint
  | KindEqConstraint
  | HasKindConstraint
  | HasTypeConstraint;

/**
 * Runtime values for term evaluation (experimental).
 *
 * **Purpose**: **Big-step/small-step evaluator** representation:
 * - **Closures**: `vlam` (call-by-value), `vthunk` (call-by-name).
 * - **Data**: Records/variants/tuples/folds (structural).
 * - **Traits**: `vdict` (method table).
 * - **Apps**: `vapp` (unevaluated, reduce callee first).
 * Used in `eval` (not fully implemented, experimental).
 * Mirrors `Term` structure (deconstruct via pattern matching).
 *
 * **Evaluation**:
 * - Closures capture `env: Environment`.
 * - `vdict.methods: Map` for trait dispatch.
 * - Reduce `vapp` → apply `vlam/vthunk`.

 * @typedef {Union} Value
 * @type {vvar} `vvar "x"` - Variable (lookup env)
 * @type {vlam} Closure (param, body, captured env)
 * @type {vapp} Application (reduce callee → arg)
 * @type {vrecord} `{x:v, y:v}` - Record fields
 * @type {vvariant} `vvariant "L" v` - Tagged payload
 * @type {vtuple} `[v1, v2]` - Tuple elements
 * @type {vfold} Folded recursive value
 * @type {vdict} `{trait, type, methods: Map}` - Trait evidence
 * @type {vthunk} `{term, env}` - Lazy thunk (call-by-name)

 * @example Construction (core values)
 * ```ts
 * import type { Value, Environment } from "system-f-omega";
 *
 * const env: Environment = new Map();
 *
 * // Closures
 * const closure: Value = {
 *   vlam: { param: "x", body: { var: "x" }, env }
 * };
 *
 * // Data
 * const rec: Value = { vrecord: { x: { vvar: "self" }, y: { vvar: "1" } } };
 * const varnt: Value = { vvariant: { label: "Left", value: { vvar: "42" } } };
 * const tup: Value = { vtuple: [{ vvar: "true" }, { vvar: "()" }] };
 *
 * // Traits
 * const dict: Value = {
 *   vdict: {
 *     trait: "Eq",
 *     type: { con: "Int" },
 *     methods: new Map([["eq", { vlam: { param: "x", body: { var: "x" }, env } }]])
 *   }
 * };
 * ```

 * @example Lazy thunk (call-by-name)
 * ```ts
 * import type { Value } from "system-f-omega";
 *
 * const thunk: Value = {
 *   vthunk: { term: { lam: { arg: "x", type: { con: "Int" }, body: { var: "x" } } }, env: new Map() }
 * };
 * ```

 * @see {@link Environment} Captured bindings
 * @see {@link EvalResult} Evaluation result
 * @see {@link EvalConfig} Eval options (strict/lazy)
 * @see {@link Term} Source terms (experimental eval)
 */
export type Value =
  | { vvar: string }
  | { vlam: { param: string; body: Term; env: Environment } }
  | { vapp: { func: Value; arg: Value } }
  | { vrecord: Record<string, Value> }
  | { vvariant: { label: string; value: Value } }
  | { vtuple: Value[] }
  | { vfold: { type: Type; value: Value } }
  | { vdict: { trait: string; type: Type; methods: Map<string, Value> } }
  | { vthunk: { term: Term; env: Environment } };

/**
 * The **runtime environment** used by the experimental evaluator,
 * mapping term variables to their evaluated **Values**.
 *
 * ```
 * Environment = Map<variableName, Value>
 * ```
 *
 * **What it represents**
 * During evaluation (big‑step or small‑step), an `Environment` stores:
 * - **closure bindings** for lambda abstractions
 *   (when a lambda is evaluated, it captures the environment in which it was defined)
 * - **thunk bindings** for call‑by-name or lazy evaluation
 *   (unevaluated terms paired with the environment needed to evaluate them)
 * - **local variable bindings** introduced by `let`, pattern matches, or
 *   lambda application
 *
 * This enables lexical scoping, proper closure semantics, and lazy evaluation.
 *
 * **Why it's useful**
 * The environment:
 * - Keeps track of free variables inside closures
 * - Ensures correct variable lookup during evaluation
 * - Supports thunk evaluation for lazy semantics
 * - Allows the evaluator to behave like a real-world interpreter
 *   (e.g., Haskell’s or Scheme’s evaluation strategies)
 *
 * Without an environment, closures would not capture context, and evaluation
 * would not be able to resolve variable references.
 *
 * **Where it is used**
 * - {@link Value.vlam} — closures store the environment they were defined in
 * - {@link Value.vthunk} — lazy thunks store an environment for deferred eval
 * - The evaluation engine (`eval` / `reduce`) carries an environment around
 *
 * **Related**
 * - {@link Value} — the value-level runtime representation
 * - {@link VarTerm} — evaluated by looking up values in the environment
 * - {@link vlam} and {@link vthunk} variants of `Value`
 *
 * **Examples**
 *
 * Creating an empty environment:
 * ```ts
 * let env: Environment = new Map();
 * ```
 *
 * Storing a value in the environment:
 * ```ts
 * import { vvar, vlam } from "system-f-omega";  // Example shapes
 *
 * const env: Environment = new Map();
 * env.set("x", { vvar: "42" });  // pretend evaluated literal
 * ```
 *
 * Closure capturing an environment:
 * ```ts
 * import { vlam, varTerm } from "system-f-omega";
 *
 * const env: Environment = new Map([["y", { vvar: "7" }]]);
 *
 * const closure = {
 *   vlam: {
 *     param: "x",
 *     body: varTerm("y"),  // references captured y
 *     env                     // closure captures env
 *   }
 * };
 * ```
 *
 * Thunk with an environment:
 * ```ts
 * const thunk = {
 *   vthunk: {
 *     term: { var: "x" },
 *     env: new Map([["x", { vvar: "100" }]])
 *   }
 * };
 * ```
 */
export type Environment = Map<string, Value>;

/**
 * The result of evaluating a term: either a **runtime value** or a **string
 * error message**.
 *
 * ```
 * EvalResult = { ok: Value } | { err: string }
 * ```
 *
 * **What it represents**
 * `EvalResult` is a specialization of the generic {@link Result} type used by
 * the *experimental* evaluator.
 *
 * It captures the outcome of evaluating a term:
 * - `ok: Value` → evaluation succeeded and produced a runtime value
 * - `err: string` → evaluation failed with a human-readable error message
 *
 * This keeps the evaluator simple and separate from the typing system:
 * runtime errors use plain strings rather than {@link TypingError}.
 *
 * **Why it's useful**
 * `EvalResult` provides:
 * - A simple, type-safe way to distinguish success from failure
 * - Clear error reporting for evaluation-specific problems
 * - Support for different evaluation strategies (strict vs lazy)
 *
 * Evaluation may fail due to:
 * - Unbound variables at runtime
 * - Invalid applications
 * - Unsupported constructs in the current evaluator stage
 * - Step limit exceeded (depending on config)
 *
 * **Where it is used**
 * - Returned by `eval` or `evaluate` functions
 * - Produced by stepping functions in small-step evaluation
 * - Interacts with {@link Environment} and {@link Value} during evaluation
 *
 * **Related**
 * - {@link Value} — the runtime representation of evaluated expressions
 * - {@link Environment} — variable bindings during evaluation
 * - {@link Result} — the generic success/error wrapper
 * - {@link EvalConfig} — evaluation strategy + step limits
 *
 * **Examples**
 *
 * Successful evaluation:
 * ```ts
 * import { vvar } from "system-f-omega";  // pretend Value shape
 *
 * const result: EvalResult = { ok: { vvar: "42" } };
 * // evaluation produced the value 42
 * ```
 *
 * Runtime error:
 * ```ts
 * const result: EvalResult = { err: "Unbound variable 'x'" };
 * ```
 *
 * Handling evaluation results:
 * ```ts
 * function run(result: EvalResult) {
 *   if ("ok" in result) {
 *     console.log("Value:", result.ok);
 *   } else {
 *     console.error("Runtime error:", result.err);
 *   }
 * }
 * ```
 */
export type EvalResult = Result<string, Value>; // Using string for error messages

/**
 * Configuration options for the **experimental evaluator**, controlling how
 * terms are reduced and how infinite loops are prevented.
 *
 * **What it represents**
 * `EvalConfig` specifies:
 * - **Evaluation strategy**
 *   - `strict: true` → call‑by‑value
 *   - `strict: false` → call‑by‑name (lazy, via thunks)
 * - **Step limit** (`maxSteps`) to avoid non‑termination
 *
 * These settings allow you to experiment with different operational semantics
 * without changing the evaluator implementation.
 *
 * **Why it's useful**
 * Evaluation strategy dramatically affects program behavior:
 *
 * 1. **Call‑by‑value (strict)**
 *    - Arguments are evaluated *before* a function call
 *    - Simpler reasoning, predictable performance
 *    - Matches languages like JavaScript, OCaml, and ML
 *
 * 2. **Call‑by‑name (lazy)**
 *    - Arguments are wrapped as thunks and evaluated only if needed
 *    - Enables non‑strict semantics
 *    - Matches lazy languages like Haskell
 *    - Useful for testing the correctness of your closure/thunk model
 *
 * The `maxSteps` limit ensures the evaluator:
 * - halts on infinite recursion
 * - avoids runaway computations
 * - behaves safely in REPL or debugging environments
 *
 * **Where it is used**
 * - By the evaluator function (`eval`, `step`, or equivalent)
 * - Interacts with {@link Environment} and {@link Value}
 * - Governs how closures and thunks are reduced
 *
 * **Related**
 * - {@link Value.vthunk} — used when `strict: false` (lazy mode)
 * - {@link Value.vlam} — closures depend on the evaluation environment
 * - {@link EvalResult} — evaluation outcome
 *
 * **Examples**
 *
 * Strict evaluation:
 * ```ts
 * const config: EvalConfig = {
 *   strict: true,
 *   maxSteps: 1000
 * };
 * // Arguments are evaluated immediately (call‑by‑value)
 * ```
 *
 * Lazy evaluation using thunks:
 * ```ts
 * const config: EvalConfig = {
 *   strict: false,
 *   maxSteps: 2000
 * };
 * // Arguments are evaluated on demand (call‑by‑name)
 * ```
 *
 * Step-limited evaluation:
 * ```ts
 * const config: EvalConfig = {
 *   strict: true,
 *   maxSteps: 10
 * };
 * // Prevents infinite loops by stopping after 10 reduction steps
 * ```
 */
export type EvalConfig = {
  strict: boolean; // true for call-by-value, false for call-by-name
  maxSteps: number; // for preventing infinite loops
};

/**
 * A generic **tagged result type** used throughout the typechecker and
 * evaluator to represent either:
 *
 * - a **successful** result: `{ ok: value }`
 * - an **error** result: `{ err: errorValue }`
 *
 * ```
 * Result<TErr, TOk> = { ok: TOk } | { err: TErr }
 * ```
 *
 * **What it represents**
 * `Result` is a lightweight alternative to exceptions.
 * It makes success and failure explicit in the type system, enabling safe,
 * predictable error handling without throwing.
 *
 * This is used across:
 * - type inference
 * - kind checking
 * - unification
 * - module importing
 * - evaluator runtime errors
 *
 * **Why it's useful**
 * `Result` allows:
 * - *composable* typechecking and evaluation functions
 * - precise handling of domain-specific errors (e.g., {@link TypingError})
 * - clean propagation of failures without intermediate try/catch
 * - safe pattern matching in user code or higher-level utilities
 *
 * TypeScript understands unions like `{ ok: ... } | { err: ... }`, enabling good
 * editor support:
 *
 * ```
 * if ("ok" in result) {
 *   // success case
 * } else {
 *   // error case
 * }
 * ```
 *
 * **Where it is used**
 * - Most typechecker APIs return `Result<TypingError, Type>`
 * - Evaluator returns `Result<string, Value>` as {@link EvalResult}
 * - Add/lookup operations return `Result<TypingError, State>`
 *
 * **Related**
 * - {@link TypingError} — common error type for the typechecker
 * - {@link EvalResult} — runtime evaluation result type
 * - {@link ok} / {@link err} — helper constructors for success/failure
 *
 * **Examples**
 *
 * Successful result:
 * ```ts
 * import type { Result } from "system-f-omega";
 *
 * const r: Result<string, number> = { ok: 42 };
 * ```
 *
 * Error result:
 * ```ts
 * const r: Result<string, number> = { err: "Something went wrong" };
 * ```
 *
 * Handling a result:
 * ```ts
 * function handle<T>(res: Result<string, T>) {
 *   if ("ok" in res) {
 *     console.log("Success:", res.ok);
 *   } else {
 *     console.error("Error:", res.err);
 *   }
 * }
 * ```
 */
export type Result<TErr, TOk> = { ok: TOk } | { err: TErr };

/**
 * A collection of **free names** discovered inside a `Type`—used primarily for
 * dependency analysis, renaming, and module imports.
 *
 * **What it represents**
 * `FreeTypeNames` gathers all identifiers that appear *unbound* inside a type:
 *
 * - `typeVars` — free type variables (`"A"`, `"T"`, `"Self"`)
 * - `typeCons` — referenced type constructors (`"Int"`, `"List"`)
 * - `traits` — trait names referenced inside bounded foralls (`Eq`, `Show`)
 * - `labels` — record/variant labels (`"x"`, `"Left"`, `"Some"`)
 *
 * These sets are generated by {@link computeFreeTypes} and are used to
 * understand how a type depends on other parts of the program.
 *
 * **Why it's useful**
 * Collecting free names is essential for:
 *
 * - **Module imports** — determining which definitions must be carried over
 * - **Renaming** — applying consistent renames via {@link renameType}
 * - **Cycle detection** — ensuring type aliases and enums don't form loops
 * - **Dependency analysis** — discovering which types reference which others
 *
 * The typechecker uses this information extensively during
 * {@link collectDependencies}, {@link importModule}, and renaming passes.
 *
 * **Where it is used**
 * - {@link computeFreeTypes} — builds this data structure
 * - {@link importModule} — determines what needs to be imported
 * - {@link bindingDependencies} — detects dependencies between bindings
 * - {@link renameType} — renames labels, constructors, and vars
 *
 * **Related**
 * - {@link FreeTermNames} — collects free names from full terms
 * - {@link FreePatternNames} — collects free names from patterns
 * - {@link Type} — the input structure analyzed
 *
 * **Examples**
 *
 * Free names of a type application:
 * ```ts
 * import { computeFreeTypes, appType, conType, varType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = appType(conType("List"), varType("A"));
 *
 * const free = computeFreeTypes(state, ty);
 *
 * console.log([...free.typeVars]); // ["A"]
 * console.log([...free.typeCons]); // ["List"]
 * ```
 *
 * Free names inside a variant type:
 * ```ts
 * import { computeFreeTypes, variantType, conType } from "system-f-omega";
 *
 * const ty = variantType([
 *   ["Left",  conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 *
 * const free = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, ty);
 *
 * console.log([...free.labels]);   // ["Left", "Right"]
 * console.log([...free.typeCons]); // ["Int", "Bool"]
 * ```
 *
 * Trait‑bounded polymorphism:
 * ```ts
 * import { computeFreeTypes, boundedForallType, varType, starKind } from "system-f-omega";
 *
 * const ty = boundedForallType("A", starKind, [{ trait: "Eq", type: varType("A") }], varType("A"));
 *
 * const free = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, ty);
 *
 * console.log([...free.traits]);   // ["Eq"]
 * console.log([...free.typeVars]); // ["A"]
 * ```
 */
export type FreeTypeNames = {
  typeVars: Set<string>;
  typeCons: Set<string>;
  traits: Set<string>;
  labels: Set<string>; // variant or record labels
};

/**
 * A collection of **free names** extracted from a pattern.
 * This is used for renaming, dependency analysis, and module imports.
 *
 * **What it represents**
 * `FreePatternNames` gathers all identifiers that appear inside a pattern:
 *
 * - `vars` — variable names bound by the pattern (`x`, `hd`, `y`)
 * - `constructors` — constructors used in constant/variant patterns (`None`, `true`, `Zero`)
 * - `labels` — record labels or variant tags (`x`, `Left`, `Some`)
 *
 * These are collected by {@link computeFreePatterns}.
 *
 * **Why it's useful**
 * Free pattern names are essential for:
 *
 * - **Module import renaming** — mapping labels, constructors, and var names
 * - **Dependency analysis** — determining which enums or constructors are used
 * - **Pattern‑scoped renaming** — used by {@link renamePattern}
 * - **Matching dependencies** — extracting labels for {@link checkExhaustive}
 *
 * Unlike types or terms, patterns do *not* distinguish bound vs free variables
 * for renaming—they are all collected to ensure safe and complete renaming.
 *
 * **Where it is used**
 * - {@link computeFreePatterns} — the producer of this structure
 * - {@link importModule} — detects dependencies across modules
 * - {@link renamePattern} — applies renaming maps
 * - {@link computeFreeTerms} — uses this when scanning match terms
 *
 * **Related**
 * - {@link FreeTypeNames} — free names that appear in types
 * - {@link FreeTermNames} — free names from terms
 * - {@link Pattern} — includes variables, constructors, labels
 *
 * **Examples**
 *
 * Extracting names from a simple pattern:
 * ```ts
 * import { computeFreePatterns, varPattern } from "system-f-omega";
 *
 * const pat = varPattern("x");
 * const free = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, pat);
 *
 * console.log([...free.vars]);  // ["x"]
 * console.log([...free.labels]); // []
 * console.log([...free.constructors]); // []
 * ```
 *
 * Pattern with constructors and labels:
 * ```ts
 * import {
 *   computeFreePatterns, recordPattern,
 *   variantPattern, varPattern
 * } from "system-f-omega";
 *
 * const pat = recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", variantPattern("Cons", varPattern("hd"))]
 * ]);
 *
 * const free = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, pat);
 *
 * console.log([...free.vars]);          // ["a", "hd"]
 * console.log([...free.labels]);        // ["x", "y", "Cons"]
 * console.log([...free.constructors]);  // []
 * ```
 *
 * Constructor pattern:
 * ```ts
 * import { computeFreePatterns, conPattern, conType } from "system-f-omega";
 *
 * const pat = conPattern("None", conType("Unit"));
 * const free = computeFreePatterns({ ctx: [], meta: { ... } }, pat);
 *
 * console.log([...free.constructors]); // ["None"]
 * ```
 */
export type FreePatternNames = {
  vars: Set<string>;
  constructors: Set<string>;
  labels: Set<string>;
};

/**
 * A collection of **free names** discovered inside a `Term`, including names
 * from embedded **types** and **patterns**.
 *
 * Extracted by {@link computeFreeTerms}, this structure summarizes all
 * identifiers referenced anywhere within a term.
 *
 * **What it represents**
 * `FreeTermNames` contains seven categories of free names:
 *
 * - `terms` — free term variables (`x`, `f`, `xs`)
 * - `constructors` — literal or variant constructor names in terms (`"42"`, `"Some"`, `"Nil"`)
 * - `traits` — traits referenced inside type annotations or dictionary usage (`Eq`, `Ord`)
 * - `dicts` — dictionary variable names used in trait method calls (`d`, `eqInt`)
 * - `labels` — record field names and variant labels (`x`, `head`, `Left`)
 * - `typeVars` — type variables appearing in embedded types (`A`, `T`, `Self`)
 * - `typeCons` — type constructors appearing in embedded types (`Int`, `List`, `Option`)
 *
 * **Why it's useful**
 * Collecting free names across an entire term enables:
 *
 * - **Module dependency analysis**
 *   Determining which types, traits, or terms must be imported.
 *
 * - **Safe renaming during imports**
 *   Used by {@link renameTerm} to avoid shadowing or collisions.
 *
 * - **Enum/trait dependency tracking**
 *   Helps {@link importModule} find all nested references.
 *
 * - **Pattern‑aware free name detection**
 *   Through integration with {@link computeFreePatterns}.
 *
 * It’s the most comprehensive “name collector,” combining data from:
 * - term syntax,
 * - embedded types,
 * - embedded patterns,
 * - and dictionary usages.
 *
 * **Where it is used**
 * - {@link computeFreeTerms} — main producer
 * - {@link computeFreeTypes} — collects embedded type names
 * - {@link computeFreePatterns} — collects names inside match patterns
 * - {@link importModule} — gathers dependency roots
 * - {@link renameTerm} — renames all free occurrences
 *
 * **Related**
 * - {@link FreeTypeNames}
 * - {@link FreePatternNames}
 * - {@link Term}
 * - {@link Pattern}
 *
 * **Examples**
 *
 * Free names in a simple application:
 * ```ts
 * import { computeFreeTerms, appTerm, varTerm } from "system-f-omega";
 *
 * const term = appTerm(varTerm("f"), varTerm("x"));
 * const free = computeFreeTerms({ ctx: [], meta: ... }, term);
 *
 * console.log([...free.terms]); // ["f", "x"]
 * ```
 *
 * Free names inside a record + constructor:
 * ```ts
 * import { computeFreeTerms, recordTerm, conTerm, conType } from "system-f-omega";
 *
 * const term = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("Some", conType("Option<Int>"))]
 * ]);
 *
 * const free = computeFreeTerms(..., term);
 *
 * console.log([...free.labels]);        // ["x", "y"]
 * console.log([...free.constructors]);  // ["1", "Some"]
 * console.log([...free.typeCons]);      // ["Int", "Option"]
 * ```
 *
 * Free names in a match expression:
 * ```ts
 * import {
 *   computeFreeTerms,
 *   matchTerm, variantPattern, varPattern,
 *   conTerm, conType
 * } from "system-f-omega";
 *
 * const term = matchTerm(
 *   { var: "rec" },
 *   [[ variantPattern("Cons", varPattern("hd")), varTerm("hd") ]]
 * );
 *
 * const free = computeFreeTerms(..., term);
 *
 * console.log([...free.terms]);         // ["rec", "hd"]
 * console.log([...free.labels]);        // ["Cons"]
 * console.log([...free.typeCons]);      // (depends on scrutinee type)
 * ```
 */
export type FreeTermNames = {
  terms: Set<string>;
  constructors: Set<string>;
  traits: Set<string>;
  dicts: Set<string>;
  labels: Set<string>;
  typeVars: Set<string>;
  typeCons: Set<string>;
};

/**
 * A **queue of constraints** to be processed by the unification solver.
 *
 * ```
 * Worklist = Constraint[]
 * ```
 *
 * **What it represents**
 * A `Worklist` is an ordered list of constraints (see {@link Constraint})
 * generated during type inference and kind checking.
 *
 * Each constraint describes something the solver must eventually enforce:
 * - a type equality (`τ₁ = τ₂`)
 * - a kind equality (`κ₁ = κ₂`)
 * - a deferred type check (`Γ ⊢ e : τ`)
 * - a deferred kind check (`Γ ⊢ τ : κ`)
 *
 * The solver (`solveConstraints`) repeatedly removes constraints from this list
 * and attempts to resolve them, often adding *new* constraints as it learns more
 * about types and kinds.
 *
 * **Why it's useful**
 * The worklist enables:
 * - Incremental, ordered constraint solving
 * - Deferred checking when meta‑variables are unresolved
 * - A clean separation between **generating constraints** and **solving them**
 * - Support for higher‑kinded polymorphism and trait‑bounded polymorphism
 *
 * It is the backbone of constraint‑based type inference.
 *
 * **Where it is used**
 * - Populated by:
 *   - {@link unifyTypes}
 *   - {@link checkType}
 *   - {@link subsumes}
 *   - {@link inferDictType}
 *   - {@link checkKind}
 * - Consumed by:
 *   - {@link solveConstraints}
 *   - {@link processConstraint}
 *
 * **Related**
 * - {@link Constraint} — the union of possible worklist items
 * - {@link solveConstraints} — processes the worklist
 * - {@link processConstraint} — processes a single constraint
 * - {@link Substitution} — solver output
 *
 * **Examples**
 *
 * A simple worklist with a type equality:
 * ```ts
 * import { typeEq, varType, conType } from "system-f-omega";
 *
 * const wl: Worklist = [
 *   typeEq(varType("A"), conType("Int"))
 * ];
 * ```
 *
 * Worklist built by unification:
 * ```ts
 * import {
 *   unifyTypes, arrowType, varType, conType,
 *   freshState
 * } from "system-f-omega";
 *
 * let state = freshState();
 * const wl: Worklist = [];
 * const subst = new Map();
 *
 * unifyTypes(
 *   state,
 *   arrowType(varType("X"), varType("Y")),
 *   arrowType(conType("Int"), conType("Bool")),
 *   wl,
 *   subst
 * );
 *
 * console.log(wl.length);  // 2 constraints: X=Int, Y=Bool
 * ```
 *
 * Solving a complete worklist:
 * ```ts
 * import { solveConstraints } from "system-f-omega";
 *
 * const result = solveConstraints(state, wl, subst);
 * console.log("ok" in result);  // true if all constraints solved successfully
 * ```
 */
export type Worklist = Constraint[];

/**
 * A mapping from **type variables or meta‑variables** to their inferred
 * **substituted types**.
 *
 * ```
 * Substitution = Map<string, Type>
 * ```
 *
 * **What it represents**
 * A `Substitution` describes the partial or complete results of unification.
 *
 * Keys are:
 * - meta‑variables (`"?0"`, `"?1"`, …) created via {@link freshMetaVar}
 * - rigid type variables (`"A"`, `"Self"`) in certain unification contexts
 *
 * Values are:
 * - the fully or partially solved types associated with those variables
 *   (`Int`, `List<?1>`, `A → A`, etc.)
 *
 * Example substitutions:
 * ```
 * ?0 → Int
 * ?1 → List<?2>
 * A  → Bool
 * ```
 *
 * **Why it's useful**
 * Substitutions are essential for:
 * - Representing the evolving results of unification
 * - Replacing unknown types with concrete ones during inference
 * - Propagating solutions across the entire AST
 * - Combining local and global inference results
 *
 * They are returned by:
 * - {@link solveConstraints}
 * - {@link unifyTypes}
 * - {@link checkType} (as part of its result)
 *
 * And consumed by:
 * - {@link applySubstitution}
 * - {@link mergeSubsts}
 * - {@link normalizeType}
 *
 * **Where it is used**
 * - Every unification and constraint solver step updates a substitution
 * - The typechecker threads substitutions to apply solved types to terms, types,
 *   trait constraints, and recursive structures
 *
 * **Related**
 * - {@link applySubstitution} — applies a substitution to a type
 * - {@link MetaEnv} — global store of solved meta‑vars
 * - {@link unifyTypes} — generates new substitution entries
 * - {@link mergeSubsts} — combines local and global substitutions
 *
 * **Examples**
 *
 * A simple substitution:
 * ```ts
 * import { Substitution } from "system-f-omega";
 *
 * const subst: Substitution = new Map([
 *   ["?0", { con: "Int" }]
 * ]);
 * ```
 *
 * Unification producing a substitution:
 * ```ts
 * import {
 *   unifyTypes, varType, conType,
 *   freshState
 * } from "system-f-omega";
 *
 * let state = freshState();
 * const subst = new Map();
 * const worklist = [];
 *
 * unifyTypes(state, varType("A"), conType("Bool"), worklist, subst);
 * solveConstraints(state, worklist, subst);
 *
 * console.log(subst.get("A"));  // { con: "Bool" }
 * ```
 *
 * Applying a substitution:
 * ```ts
 * import {
 *   applySubstitution, varType,
 *   conType, freshState
 * } from "system-f-omega";
 *
 * const subst: Substitution = new Map([["A", conType("Int")]]);
 *
 * console.log(
 *   applySubstitution(freshState(), subst, varType("A"))
 * );
 * // → Int
 * ```
 */
export type Substitution = Map<string, Type>;

/**
 * Constructs a **successful** {@link Result} value:
 *
 * ```
 * ok(value)  →  { ok: value }
 * ```
 *
 * **What it represents**
 * `ok` is a tiny helper used throughout the typechecker and evaluator to
 * produce the “success” branch of a {@link Result}.
 * This avoids manually writing `{ ok: ... }` and keeps APIs consistent.
 *
 * It pairs naturally with {@link err}, the constructor for error results.
 *
 * **Why it's useful**
 * `ok` helps ensure:
 * - uniform creation of success results
 * - clearer code in inference functions
 * - fewer mistakes when assembling `Result` values
 *
 * It is used everywhere results need to be returned, including:
 * - type inference (`inferType`)
 * - type checking (`checkType`)
 * - constraint solving (`solveConstraints`)
 * - trait resolution (`checkTraitImplementation`)
 * - module importing (`importModule`)
 * - evaluation (`EvalResult`)
 *
 * **Related**
 * - {@link Result} — the union type returned by many APIs
 * - {@link err} — constructor for failure cases
 * - {@link showError} — pretty-prints error results
 *
 * **Examples**
 *
 * Creating a successful result:
 * ```ts
 * import { ok } from "system-f-omega";
 *
 * const r = ok(42);
 * // { ok: 42 }
 * ```
 *
 * Using `ok` inside a type inference rule:
 * ```ts
 * import { ok } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * function inferLiteral() {
 *   return ok(conType("Int"));
 * }
 * ```
 *
 * Pattern matching on a `Result`:
 * ```ts
 * import { ok } from "system-f-omega";
 *
 * const r = ok("hello");
 *
 * if ("ok" in r) {
 *   console.log("Success:", r.ok);
 * }
 * ```
 */
export const ok = <T>(val: T) => ({ ok: val });

/**
 * Constructs an **error** {@link Result} value:
 *
 * ```
 * err(value)  →  { err: value }
 * ```
 *
 * **What it represents**
 * `err` is the counterpart to {@link ok}.
 * It wraps an error payload in the `{ err: ... }` form used throughout the
 * typechecker and evaluator.
 *
 * The error payload can be:
 * - a {@link TypingError} (for typechecking)
 * - a `string` (for the evaluator)
 * - any user-defined error type
 *
 * **Why it's useful**
 * This helper ensures:
 * - consistent construction of error results
 * - cleaner code in functions that may fail
 * - fewer mistakes when wrapping error payloads
 *
 * Many core APIs return `Result<TErr, TOk>` values, including:
 * - {@link inferType}
 * - {@link checkType}
 * - {@link solveConstraints}
 * - {@link checkTraitImplementation}
 * - {@link importModule}
 * - evaluator functions (`EvalResult`)
 *
 * `err` makes these error returns lightweight and readable.
 *
 * **Related**
 * - {@link ok} — constructor for success cases
 * - {@link Result} — the result type used by all major APIs
 * - {@link showError} — pretty-prints type errors
 *
 * **Examples**
 *
 * Creating an error result:
 * ```ts
 * import { err } from "system-f-omega";
 *
 * const r = err("Something went wrong");
 * // { err: "Something went wrong" }
 * ```
 *
 * Using `err` in a typechecking function:
 * ```ts
 * import { err } from "system-f-omega";
 *
 * function lookup(name) {
 *   return err({ unbound: name });  // UnboundTypeError
 * }
 * ```
 *
 * Handling a result:
 * ```ts
 * function handle(result) {
 *   if ("err" in result) {
 *     console.error("Error:", result.err);
 *   }
 * }
 * ```
 */
export const err = <T>(val: T) => ({ err: val });

/**
 * Pretty‑prints the current typing **context** (`Γ`) as a multi‑line string.
 *
 * **What it represents**
 * `showContext` converts each {@link Binding} in the context into a readable
 * line using {@link showBinding}, and joins them with newlines.
 *
 * This is especially useful for:
 * - debugging type inference
 * - inspecting the environment in a REPL
 * - showing the result of module imports
 * - logging intermediate typechecker state
 *
 * **Why it's useful**
 * The typing context may contain many different kinds of bindings:
 * - term bindings (`x : Int`)
 * - type constructors (`List :: * → *`)
 * - trait definitions
 * - trait implementations
 * - dictionary bindings
 * - enums and type aliases
 *
 * `showContext` provides a simple, human‑readable summary of all of them.
 *
 * **Related**
 * - {@link Context} — the list of bindings being printed
 * - {@link Binding} — union of all binding types
 * - {@link showBinding} — pretty‑prints each individual binding
 *
 * **Examples**
 *
 * Empty context:
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * console.log(showContext(freshState().ctx));
 * // ""
 * ```
 *
 * After adding some bindings:
 * ```ts
 * import {
 *   freshState, addType, addTerm,
 *   conTerm, conType, starKind, showContext
 * } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * console.log(showContext(state.ctx));
 * // Type: Int = *
 * // Term: x = Int
 * ```
 *
 * With traits and enums:
 * ```ts
 * import { showContext } from "system-f-omega";
 *
 * console.log(showContext(state.ctx));
 * // Prints each binding on its own line
 * ```
 */
export const showContext = (context: Context) =>
  context.map((t) => showBinding(t)).join("\n");

/**
 * Extracts the **argument types** from a left‑associated type application spine.
 *
 * **What it represents**
 * Many type constructors—especially HKTs—are applied in *spine form*:
 *
 * ```
 * Either<Int, Bool>
 *    ≡ appType(appType(Either, Int), Bool)
 *
 * List<Int>
 *    ≡ appType(List, Int)
 * ```
 *
 * `getSpineArgs` walks through nested `AppType` nodes and collects all argument
 * types in **left‑to‑right order**.
 *
 * Given:
 * ```
 * appType(appType(F, A), B)
 * ```
 *
 * it returns:
 * ```
 * [A, B]
 * ```
 *
 * **Why it's useful**
 * Extracting the “spine” of a type is essential for:
 * - **Nominal unification**
 *   Matching parameterized types like `Either<Int, Bool>` vs `Either<a, b>`
 *   (via {@link unifyTypes})
 *
 * - **Enum/ADT expansion**
 *   When normalizing `Option<T>` or `List<T>` via {@link normalizeType}
 *
 * - **Pretty‑printing**
 *   Used by {@link showType} to display `F<A, B, C>` nicely
 *
 * - **Pattern/type inspection utilities**
 *
 * In short, anything that needs to know “what arguments were given to this type
 * constructor” uses this helper.
 *
 * **Related**
 * - {@link getSpineHead} — extracts the root constructor (e.g. `Either`)
 * - {@link AppType} — representation of type application
 * - {@link normalizeType} — uses spines to expand enums/aliases
 * - {@link unifyTypes} — uses spines for structural unification
 *
 * **Examples**
 *
 * Extracting arguments from a nested application:
 * ```ts
 * import { getSpineArgs, appType, conType } from "system-f-omega";
 *
 * const ty = appType(
 *   appType(conType("Either"), conType("Int")),
 *   conType("Bool")
 * );
 *
 * console.log(getSpineArgs(ty));  // [Int, Bool]
 * ```
 *
 * Single argument:
 * ```ts
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log(getSpineArgs(listInt));  // [Int]
 * ```
 *
 * Non‑application types:
 * ```ts
 * import { getSpineArgs, conType } from "system-f-omega";
 *
 * console.log(getSpineArgs(conType("Int")));  // []
 * ```
 */
export function getSpineArgs(ty: Type): Type[] {
  const args: Type[] = [];
  let current = ty;
  while ("app" in current) {
    args.unshift(current.app.arg);
    current = current.app.func;
  }
  return args;
}

/**
 * Pretty‑prints a single {@link Binding} from the typing context (`Γ`).
 *
 * **What it represents**
 * `showBinding` converts any kind of binding—term, type, trait, dictionary,
 * enum, or type alias—into a human‑readable string.
 *
 * This function is the core printer used by {@link showContext} to display
 * multi‑line, debugging‑friendly summaries of the entire context.
 *
 * Each binding form is printed as:
 *
 * - **TermBinding**
 *   ```
 *   Term: x = Int
 *   ```
 *
 * - **TypeBinding**
 *   ```
 *   Type: List = (* → *)
 *   ```
 *
 * - **TraitDefBinding**
 *   ```
 *   Trait: Eq = TraitDef (Eq A = *
 *     eq : (A → Bool))
 *   ```
 *
 * - **TraitImplBinding**
 *   ```
 *   Impl: Eq = dict Eq<Int> {...} : Int
 *   ```
 *
 * - **DictBinding**
 *   ```
 *   Dict: eqInt = Trait Eq : Int
 *   ```
 *
 * - **TypeAliasBinding**
 *   ```
 *   Type Alias: Id<A::*> = A
 *   ```
 *
 * **Why it's useful**
 * Human‑readable printing of bindings is important for:
 * - REPLs and debugging
 * - Understanding typechecker output
 * - Inspecting module imports and renamings
 * - Showing what is currently in `Γ`
 *
 * `showBinding` provides a unified, consistent formatting for all binding types.
 *
 * **Where it is used**
 * - {@link showContext} — iterates through all bindings
 * - Debugging utilities
 * - Test outputs and error messages
 *
 * **Related**
 * - {@link Binding} — the union type handled by this function
 * - {@link showType} — prints embedded types
 * - {@link showKind} — prints kinds (`*`, `(* → *)`, ...)
 * - {@link showTraitDef} — prints trait method signatures
 *
 * **Examples**
 *
 * Displaying a term binding:
 * ```ts
 * import { termBinding, conType, showBinding } from "system-f-omega";
 *
 * const bind = termBinding("x", conType("Int"));
 * console.log(showBinding(bind));  // "Term: x = Int"
 * ```
 *
 * Printing a trait definition:
 * ```ts
 * import { traitDefBinding, starKind, arrowType, varType, showBinding } from "system-f-omega";
 *
 * const eqDef = traitDefBinding("Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))]
 * ]);
 *
 * console.log(showBinding(eqDef));
 * // "Trait: Eq = TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * Type alias binding printout:
 * ```ts
 * import { typeAliasBinding, varType, starKind, showBinding } from "system-f-omega";
 *
 * const alias = typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * console.log(showBinding(alias));
 * // "Type Alias: Id<A::*> = A"
 * ```
 */
export const showBinding = (bind: Binding) => {
  if ("term" in bind)
    return `Term: ${bind.term.name} = ${showType(bind.term.type)}`;
  if ("type" in bind)
    return `Type: ${bind.type.name} = ${showKind(bind.type.kind)}`;
  if ("trait_def" in bind)
    return `Trait: ${bind.trait_def.name} = ${showTraitDef(bind.trait_def)}`;
  if ("trait_impl" in bind)
    return `Impl: ${bind.trait_impl.trait} = ${showTerm(bind.trait_impl.dict)}: ${showType(bind.trait_impl.type)}`;
  if ("dict" in bind)
    return `Dict: ${bind.dict.name} = Trait ${bind.dict.trait} : ${showType(bind.dict.type)}`;
  if ("type_alias" in bind) {
    const params = bind.type_alias.params
      .map((p, i) => `${p}::${showKind(bind.type_alias.kinds[i]!)}`)
      .join(", ");
    return `Type Alias: ${bind.type_alias.name}<${params}> = ${showType(bind.type_alias.body)}`;
  }
};

/**
 * Converts a {@link TypingError} into a **human‑readable error message**.
 *
 * **What it represents**
 * `showError` is the central pretty‑printer for all typechecker errors.
 * It pattern‑matches on every variant of {@link TypingError} and produces a
 * descriptive, multiline string suitable for:
 *
 * - REPL output
 * - debugging
 * - error reporting
 * - IDE diagnostics
 *
 * Each error kind (unbound names, kind mismatches, type mismatches, invalid
 * variants, missing dictionaries, etc.) is formatted in a clear and consistent
 * style that’s readable by beginners and experts alike.
 *
 * **Why it's useful**
 * Errors–especially in a formal type system—can be cryptic.
 * `showError` transforms low‑level error objects into meaningful messages.
 *
 * This function:
 * - Ensures every error variant has a consistent format
 * - Helps users understand *why* inference failed
 * - Improves debugging of pattern matches, trait resolution, and HKT usage
 * - Bridges the gap between internal error structures and user‑facing feedback
 *
 * **Where it is used**
 * - In top‑level APIs (REPL, CLI, editor integrations)
 * - Inside `unwrap` to produce clear exception messages
 * - Anywhere a `TypingError` is printed
 *
 * **Related**
 * - {@link TypingError} — the union of all typechecker error variants
 * - {@link showType} — used to embed types in error messages
 * - {@link showKind} — embeds kinds
 * - {@link showBinding} — embeds duplicate binding info
 * - {@link unwrap} — throws errors using `showError`
 *
 * **Examples**
 *
 * Unbound identifier:
 * ```ts
 * import { showError } from "system-f-omega";
 *
 * console.log(showError({ unbound: "X" }));
 * // "Unbound identifier: X"
 * ```
 *
 * Type mismatch:
 * ```ts
 * import { showError, conType, arrowType } from "system-f-omega";
 *
 * console.log(showError({
 *   type_mismatch: {
 *     expected: arrowType(conType("Int"), conType("Int")),
 *     actual: conType("Bool")
 *   }
 * }));
 * // Type mismatch:
 * //   Expected: (Int → Int)
 * //   Actual:   Bool
 * ```
 *
 * Invalid variant label:
 * ```ts
 * import { showError, conType } from "system-f-omega";
 *
 * console.log(showError({
 *   invalid_variant_label: {
 *     label: "Bad",
 *     variant: conType("Option")
 *   }
 * }));
 * // Invalid variant label 'Bad' for:
 * //   Option
 * ```
 *
 * Duplicate binding:
 * ```ts
 * console.log(showError({
 *   duplicate_binding: {
 *     name: "Int",
 *     existing: typeBinding("Int", starKind),
 *     incoming: typeBinding("Int", starKind)
 *   }
 * }));
 * // Duplicate binding for 'Int':
 * //   Existing: Type: Int = *
 * //   Incoming: Type: Int = *
 * ```
 */
export function showError(err: TypingError): string {
  if ("unbound" in err) return `Unbound identifier: ${err.unbound}`;

  if ("kind_mismatch" in err)
    return `Kind mismatch:\n  Expected: ${showKind(err.kind_mismatch.expected)}\n  Actual:   ${showKind(err.kind_mismatch.actual)}`;

  if ("type_mismatch" in err)
    return `Type mismatch:\n  Expected: ${showType(err.type_mismatch.expected)}\n  Actual:   ${showType(err.type_mismatch.actual)}`;

  if ("not_a_function" in err)
    return `Not a function:\n  ${showType(err.not_a_function)}`;

  if ("not_a_type_function" in err)
    return `Not a type-level function:\n  ${showType(err.not_a_type_function)}`;

  if ("cyclic" in err) return `Cyclic type detected involving: ${err.cyclic}`;

  if ("not_a_record" in err)
    return `Not a record type:\n  ${showType(err.not_a_record)}`;

  if ("missing_field" in err)
    return `Missing field '${err.missing_field.label}' in record:\n  ${showType(err.missing_field.record)}`;

  if ("not_a_variant" in err)
    return `Not a variant type:\n  ${showType(err.not_a_variant)}`;

  if ("invalid_variant_label" in err)
    return `Invalid variant label '${err.invalid_variant_label.label}' for:\n  ${showType(err.invalid_variant_label.variant)}`;

  if ("missing_case" in err)
    return `Non-exhaustive match: missing case '${err.missing_case.label}'`;

  if ("extra_case" in err)
    return `Unreachable case in match: '${err.extra_case.label}'`;

  if ("not_a_tuple" in err)
    return `Not a tuple type:\n  ${showType(err.not_a_tuple)}`;

  if ("tuple_index_out_of_bounds" in err) {
    const { tuple, index } = err.tuple_index_out_of_bounds;
    return `Tuple index out of bounds:\n  Tuple: ${showType(tuple)}\n  Index: ${index}`;
  }

  if ("missing_trait_impl" in err) {
    const { trait, type } = err.missing_trait_impl;
    return `Missing trait implementation:\n  Trait: ${trait}\n  Type:  ${showType(type)}`;
  }

  if ("missing_method" in err) {
    const { trait, method } = err.missing_method;
    return `Missing method '${method}' in trait '${trait}'`;
  }

  if ("wrong_number_of_dicts" in err) {
    const { expected, actual } = err.wrong_number_of_dicts;
    return `Wrong number of dictionaries provided:\n  Expected: ${expected}\n  Actual:   ${actual}`;
  }

  if ("unexpected_kind" in err) {
    const { name, kind } = err.unexpected_kind;
    return `Unexpected kind assigned to '${name}': ${showKind(kind)}`;
  }

  if ("duplicate_binding" in err) {
    const { name, existing, incoming } = err.duplicate_binding;
    return (
      `Duplicate binding for '${name}':\n` +
      `  Existing: ${showBinding(existing)}\n` +
      `  Incoming: ${showBinding(incoming)}`
    );
  }

  if ("circular_import" in err) {
    const { name, cycle } = err.circular_import;
    return (
      `Circular import detected involving '${name}':\n` +
      `  Cycle: ${cycle.join(" → ")}`
    );
  }

  return "Unknown type error";
}

/**
 * Extracts the successful value from a {@link Result}, or throws a JavaScript
 * `Error` containing a friendly, formatted message using {@link showError}.
 *
 * ```
 * unwrap({ ok: value })          → value
 * unwrap({ err: typingError })   → throws Error("Failed: <formatted error>")
 * ```
 *
 * **What it represents**
 * `unwrap` is a convenience helper for tests, REPLs, and one‑off scripts where
 * you want:
 * - the *successful value* directly
 * - and are comfortable throwing an exception on error
 *
 * It is particularly useful when you are certain the computation should succeed
 * (e.g., inside tests) or when you want concise code without manual error
 * handling.
 *
 * **Why it's useful**
 * `unwrap`:
 * - Removes boilerplate `"ok" in result` checks
 * - Provides *descriptive exceptions* thanks to {@link showError}
 * - Helps when debugging failing inference
 * - Makes test code expressive and readable
 *
 * **Important**
 * This function **throws**, so it should not be used in production code unless
 * failure is intended to abort evaluation.
 *
 * **Where it is used**
 * - Testing type inference (`inferType`, `checkType`, etc.)
 * - Debugging constraint solving
 * - REPL commands to display immediate feedback
 *
 * **Related**
 * - {@link Result} — the wrapped success/error type
 * - {@link showError} — turns a {@link TypingError} into a human‑readable string
 * - {@link ok} / {@link err} — constructors for Result values
 *
 * **Examples**
 *
 * Successful unwrap:
 * ```ts
 * import { unwrap, ok } from "system-f-omega";
 *
 * const r = ok(42);
 * console.log(unwrap(r));  // 42
 * ```
 *
 * Unwrapping a failure (throws):
 * ```ts
 * import { unwrap, err } from "system-f-omega";
 *
 * try {
 *   unwrap(err({ unbound: "MissingType" }), "Typecheck failed");
 * } catch (e) {
 *   console.log(e.message);
 *   // "Typecheck failed: Unbound identifier: MissingType"
 * }
 * ```
 *
 * Using unwrap inside a type inference test:
 * ```ts
 * import { freshState, inferType, unwrap, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const result = inferType(state, { var: "x" });
 *
 * // If result is err, unwrap throws with a formatted message.
 * console.log(showType(unwrap(result)));
 * ```
 */
export const unwrap = <TOk = unknown>(
  result: Result<TypingError, TOk>,
  msg: string = "Failed",
): TOk => {
  if ("ok" in result) return result.ok;
  throw new Error(`${msg}: ${showError(result.err)}`);
};

/**
 * Pretty‑prints a {@link Kind} into a human‑readable string representation.
 *
 * **What it represents**
 * `showKind` converts the internal `Kind` structure (either:
 * - `StarKind` — representing `*`
 * - `ArrowKind` — representing `κ₁ → κ₂`
 *
 * into conventional kind notation used throughout type theory and in languages
 * like Haskell, OCaml, and PureScript.
 *
 * Examples of printed kinds:
 * - `*`
 * - `(* → *)`
 * - `(* → (* → *))`
 *
 * **Why it's useful**
 * Pretty‑printed kinds appear in:
 * - error messages ({@link KindMismatchTypeError}, {@link UnexpectedKindError})
 * - type displays involving `∀` or `Λ` binders ({@link showType})
 * - debug information when printing contexts (`showBinding`)
 * - developer‑facing output in REPL or logs
 *
 * Without readable kind printing, understanding higher‑kind errors would be much
 * more difficult.
 *
 * **How it works**
 * - If the kind is `*`, print `"*"`.
 * - If it is an arrow kind (`κ₁ → κ₂`), recursively print both sides wrapped
 *   in parentheses for clarity.
 *
 * **Related**
 * - {@link Kind} — the full kind system
 * - {@link StarKind} — base kind
 * - {@link ArrowKind} — kind-level function
 * - {@link showType} — pretty-prints types, embedding kinds for polymorphism
 *
 * **Examples**
 *
 * Printing simple and complex kinds:
 * ```ts
 * import { showKind, starKind, arrowKind } from "system-f-omega";
 *
 * console.log(showKind(starKind));                           // "*"
 * console.log(showKind(arrowKind(starKind, starKind)));      // "(* → *)"
 * console.log(showKind(arrowKind(starKind,
 *   arrowKind(starKind, starKind)
 * )));                                                       // "(* → (* → *))"
 * ```
 *
 * Kind inside a type printer:
 * ```ts
 * import { forallType, starKind, varType, showType } from "system-f-omega";
 *
 * const ty = forallType("A", starKind, varType("A"));
 * console.log(showType(ty));   // "∀A::*. A"
 * // showKind is used internally for the ":: *"
 * ```
 */
export function showKind(k: Kind): string {
  if ("star" in k) return "*";
  if ("arrow" in k)
    return `(${showKind(k.arrow.from)} → ${showKind(k.arrow.to)})`;
  return "unknown";
}

/**
 * Pretty‑prints a {@link Type} into a human‑readable string representation.
 *
 * **What it represents**
 * `showType` renders every kind of type in the language, including:
 * - simple types (`Int`, `Bool`)
 * - applications (`List<Int>`, `Either<A, B>`)
 * - function types (`A → B`)
 * - polymorphic types (`∀A::*. A → A`)
 * - trait‑bounded polymorphism (`∀Self::* where Eq<Self>. Self → Int`)
 * - type‑level lambdas (`λt::*. body`)
 * - records, variants, tuples
 * - recursive types (`μX. body`)
 * - meta‑variables (`?0`, `?1`)
 *
 * It is the primary way the language displays types to the user—in errors,
 * REPL output, logs, and debugging tools.
 *
 * **Why it's useful**
 * Pretty‑printed types appear everywhere:
 * - type errors (`showError`)
 * - inferred types (`inferType`)
 * - context printing (`showBinding`)
 * - variant and record displays
 *
 * A type system this rich would be nearly impossible to debug without a clear,
 * well‑structured type printer.
 *
 * **Printing rules**
 *
 * `showType` formats types using familiar, conventional notation:
 *
 * | Form                  | Printed As                                   |
 * |-----------------------|-----------------------------------------------|
 * | `VarType`            | `A`                                           |
 * | `ConType`            | `Int`, `List`, etc.                           |
 * | `AppType` (nominal)  | `List<Int>` / `Either<Int, Bool>`             |
 * | `AppType` (lambda)   | `(F A)`                                       |
 * | `ArrowType`          | `(A → B)`                                     |
 * | `ForallType`         | `∀A::*. body`                                 |
 * | `BoundedForallType`  | `∀A::*. where Eq<A>. body`                    |
 * | `LamType`            | `λA::*. body`                                 |
 * | `RecordType`         | `{ x: Int, y: Bool }`                         |
 * | `VariantType`        | `<Left: Int | Right: Bool>`                   |
 * | `TupleType`          | `(A, B, C)` or `()`                           |
 * | `MuType`             | `μX. body`                                    |
 * | `NeverType`          | `⊥`                                           |
 * | `MetaType`           | `?0`, `?1`                                    |
 *
 * Nominal type applications use **angle brackets**:
 * ```
 * Either<Int, Bool>
 * ```
 * while applied lambdas use **parenthesized application form**:
 * ```
 * (F A)
 * ```
 * detected via {@link getSpineArgs}.
 *
 * **Where it is used**
 * - {@link showError} — embedding types in error messages
 * - {@link showBinding} — printing context entries
 * - REPL inference output
 * - Debug logs
 *
 * **Related**
 * - {@link showKind} — prints kinds
 * - {@link getSpineArgs} — extracts application arguments
 * - {@link Type} — type AST representation
 *
 * **Examples**
 *
 * Nominal type application:
 * ```ts
 * import { showType, appType, conType } from "system-f-omega";
 *
 * const t = appType(conType("List"), conType("Int"));
 * console.log(showType(t));   // "List<Int>"
 * ```
 *
 * Function type:
 * ```ts
 * console.log(showType({
 *   arrow: { from: conType("Int"), to: conType("Bool") }
 * }));
 * // "(Int → Bool)"
 * ```
 *
 * Polymorphic type:
 * ```ts
 * import { forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const poly = forallType("A", starKind,
 *   arrowType(varType("A"), varType("A"))
 * );
 * console.log(showType(poly));  // "∀A::*. (A → A)"
 * ```
 *
 * Structural variant:
 * ```ts
 * import { variantType, conType } from "system-f-omega";
 *
 * const v = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 *
 * console.log(showType(v));  // "<Left: Int | Right: Bool>"
 * ```
 */
export function showType(t: Type): string {
  if ("app" in t && "con" in t.app.func) {
    const con = t.app.func.con;
    const args = getSpineArgs(t); // Helper from below
    return `${con}${args.length > 0 ? `<${args.map(showType).join(", ")}>` : ""}`; // Either<I32, Bool>
  }
  if ("var" in t) return t.var;
  if ("arrow" in t)
    return `(${showType(t.arrow.from)} → ${showType(t.arrow.to)})`;
  if ("never" in t) return "⊥";
  if ("forall" in t)
    return `∀${t.forall.var}::${showKind(t.forall.kind)}.${showType(t.forall.body)}`;
  if ("app" in t) return `(${showType(t.app.func)} ${showType(t.app.arg)})`;
  if ("lam" in t)
    return `λ${t.lam.var}::${showKind(t.lam.kind)}.${showType(t.lam.body)}`;
  if ("con" in t) return t.con;
  if ("record" in t) {
    const fields = t.record
      .map(([label, type]) => `${label}: ${showType(type)}`)
      .join(", ");
    return `{${fields}}`;
  }
  if ("variant" in t) {
    const cases = t.variant
      .map(([label, type]) => `${label}: ${showType(type)}`)
      .join(" | ");
    return `<${cases}>`;
  }
  if ("mu" in t) return `μ${t.mu.var}.${showType(t.mu.body)}`;

  if ("tuple" in t) {
    const elements = t.tuple.map(showType).join(", ");
    return `(${elements})`;
  }
  if ("bounded_forall" in t) {
    const constraints = t.bounded_forall.constraints
      .map((c) => `${c.trait}<${showType(c.type)}>`)
      .join(", ");
    return `∀${t.bounded_forall.var}::${showKind(t.bounded_forall.kind)} where ${constraints}.${showType(t.bounded_forall.body)}`;
  }
  if ("evar" in t) return `?${t.evar}`;
  return "unknown";
}

/**
 * Pretty‑prints a {@link Term} into a human‑readable string.
 *
 * **What it represents**
 * `showTerm` converts the internal term AST into a readable expression using
 * familiar functional‑language syntax:
 *
 * - Variables: `x`
 * - Lambdas: `λx:τ. body`
 * - Applications: `(f x)`
 * - Type lambdas: `ΛA::*. e`
 * - Type applications: `f [Int]`
 * - Records: `{ x = 1, y = true }`
 * - Projections: `e.x`
 * - Variants: `<Some=42> as Option<Int>`
 * - Pattern matches: `match e { Some(x) => ... | None => ... }`
 * - Trait lambdas: `ΛSelf::* where Eq<Self>. body`
 * - Trait apps: `f[Int] with dicts {d1, d2}`
 * - Dictionaries: `dict Eq<Int> { eq = ... }`
 * - Trait methods: `d.eq`
 * - Folds / unfolds: `fold[μX. ...](term)`, `unfold(term)`
 * - Tuples: `(e1, e2, ...)`
 * - Tuple projection: `tup.0`
 *
 * It is the *term‑level counterpart* to {@link showType}.
 *
 * **Why it's useful**
 * Pretty‑printed terms appear in:
 * - REPL output
 * - debugging logs
 * - error messages (e.g., in {@link showError})
 * - teaching or visualizing the structure of complex expressions
 *
 * Without this printer, debugging the raw AST would be far more difficult.
 *
 * **How it prints terms**
 * `showTerm` follows a series of formatting rules:
 * - Lambda: `λx:τ. body`
 * - Application: parentheses ensure left associativity
 * - Type lambda: `ΛA::κ. body`
 * - Type application: `term [type]`
 * - Trait lambda / app: printed with constraint lists
 * - Pattern match: `match scrutinee { pat1 => e1 | pat2 => e2 }`
 * - Variant injection: `<Label=value> as Type`
 * - Fold/unfold: explicit runtime forms for recursive types
 *
 * **Related**
 * - {@link showType} — for printing embedded types
 * - {@link showPattern} — for printing match case patterns
 * - {@link Term} — the full AST this printer handles
 * - {@link showBinding} — prints bindings containing terms
 *
 * **Examples**
 *
 * Lambda and application:
 * ```ts
 * import { lamTerm, varTerm, conType, appTerm, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const call = appTerm(id, varTerm("y"));
 *
 * console.log(showTerm(id));   // "λx:Int.x"
 * console.log(showTerm(call)); // "(λx:Int.x y)"
 * ```
 *
 * Type-level constructs:
 * ```ts
 * import { tylamTerm, tyappTerm, varTerm, conType, starKind, showTerm } from "system-f-omega";
 *
 * const poly = tylamTerm("A", starKind, varTerm("x"));
 * console.log(showTerm(poly));  // "ΛA::*. x"
 *
 * const inst = tyappTerm(poly, conType("Int"));
 * console.log(showTerm(inst));  // "ΛA::*. x [Int]"
 * ```
 *
 * Pattern match:
 * ```ts
 * import {
 *   matchTerm, variantPattern, varPattern,
 *   conTerm, conType, showTerm
 * } from "system-f-omega";
 *
 * const m = matchTerm(
 *   conTerm("opt", conType("Option<Int>")),
 *   [
 *     [variantPattern("Some", varPattern("x")), varTerm("x")],
 *     [variantPattern("None", varPattern("_")), conTerm("0", conType("Int"))],
 *   ]
 * );
 *
 * console.log(showTerm(m));
 * // match opt { Some(x) => x | None(_) => 0 }
 * ```
 *
 * Record and projection:
 * ```ts
 * import { recordTerm, conTerm, conType, projectTerm, showTerm } from "system-f-omega";
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * console.log(showTerm(rec));                  // "{x = 1}"
 * console.log(showTerm(projectTerm(rec, "x"))); // "{x = 1}.x"
 * ```
 */
export function showTerm(t: Term): string {
  if ("var" in t) return t.var;
  if ("lam" in t)
    return `λ${t.lam.arg}:${showType(t.lam.type)}.${showTerm(t.lam.body)}`;
  if ("app" in t) return `(${showTerm(t.app.callee)} ${showTerm(t.app.arg)})`;
  if ("tylam" in t)
    return `Λ${t.tylam.var}::${showKind(t.tylam.kind)}.${showTerm(t.tylam.body)}`;
  if ("tyapp" in t)
    return `${showTerm(t.tyapp.term)} [${showType(t.tyapp.type)}]`;
  if ("con" in t) return t.con.name;
  if ("let" in t)
    return `let ${t.let.name} = ${showTerm(t.let.value)} in ${showTerm(t.let.body)}`;

  if ("record" in t) {
    const fields = t.record
      .map(([label, term]) => `${label} = ${showTerm(term)}`)
      .join(", ");
    return `{${fields}}`;
  }
  if ("trait_lam" in t) {
    const constraints = t.trait_lam.constraints
      .map((c) => `${c.trait}<${showType(c.type)}>`)
      .join(", ");
    return `Λ${t.trait_lam.type_var}::${showKind(t.trait_lam.kind)} where ${constraints}. ${showTerm(t.trait_lam.body)}`;
  }

  if ("trait_app" in t) {
    const dicts = t.trait_app.dicts.map(showTerm).join(", ");
    return `${showTerm(t.trait_app.term)} [${showType(t.trait_app.type)}] with dicts {${dicts}}`;
  }

  if ("dict" in t) {
    const methods = t.dict.methods
      .map(([name, impl]) => `${name} = ${showTerm(impl)}`)
      .join(", ");
    return `dict ${t.dict.trait}<${showType(t.dict.type)}> { ${methods} }`;
  }

  if ("trait_method" in t) {
    return `${showTerm(t.trait_method.dict)}.${t.trait_method.method}`;
  }
  if ("project" in t) return `${showTerm(t.project.record)}.${t.project.label}`;
  if ("inject" in t)
    return `<${t.inject.label}=${showTerm(t.inject.value)}> as ${showType(t.inject.variant_type)}`;
  if ("match" in t) {
    const cases = t.match.cases
      .map(([pattern, body]) => `${showPattern(pattern)} => ${showTerm(body)}`)
      .join(" | ");
    return `match ${showTerm(t.match.scrutinee)} { ${cases} }`;
  }
  if ("fold" in t) {
    return `fold[${showType(t.fold.type)}](${showTerm(t.fold.term)})`;
  }
  if ("unfold" in t) {
    return `unfold(${showTerm(t.unfold)})`;
  }
  if ("tuple" in t) {
    const elements = t.tuple.map(showTerm).join(", ");
    return `(${elements})`;
  }
  if ("tuple_project" in t) {
    return `${showTerm(t.tuple_project.tuple)}.${t.tuple_project.index}`;
  }
  return "unknown";
}

/**
 * Pretty‑prints a {@link Pattern} into a human‑readable string representation.
 *
 * **What it represents**
 * `showPattern` converts the internal pattern AST into conventional pattern
 * matching syntax used in functional languages:
 *
 * - Variable pattern: `x`
 * - Wildcard: `_`
 * - Constructor / literal: `None`, `true`, `"42"`
 * - Record pattern: `{ x: p1, y: p2 }`
 * - Variant pattern: `Some(x)`
 * - Tuple pattern: `(p1, p2, p3)`
 *
 * This is the pattern‑level counterpart of {@link showTerm} and {@link showType}.
 *
 * **Why it's useful**
 * Human‑readable patterns appear in:
 * - Error messages (especially match failures)
 * - REPL displays of pattern structures
 * - Debugging tools that show typed pattern trees
 * - Pretty‑printing match expressions in {@link showTerm}
 *
 * Without readable patterns, `match` expressions would be extremely difficult to
 * understand during debugging and error reporting.
 *
 * **How it prints each pattern**
 * - `VarPattern`: prints the variable name
 *   → `x`
 *
 * - `WildcardPattern`: always prints `_`
 *
 * - `ConPattern`: prints the constructor/tag name
 *
 * - `RecordPattern`: prints record fields in `{label: pat}` format
 *
 * - `VariantPattern`: prints `Label(pat)`
 *   Example: `Some(x)`
 *
 * - `TuplePattern`: prints `(p1, p2, ...)`
 *
 * **Related**
 * - {@link Pattern} — pattern AST forms
 * - {@link showTerm} — prints patterns inside match branches
 * - {@link showType} — for printing types that patterns correspond to
 *
 * **Examples**
 *
 * Variable and wildcard:
 * ```ts
 * import { showPattern, varPattern, wildcardPattern } from "system-f-omega";
 *
 * console.log(showPattern(varPattern("x"))); // "x"
 * console.log(showPattern(wildcardPattern())); // "_"
 * ```
 *
 * Constructor and variant pattern:
 * ```ts
 * import { showPattern, conPattern, variantPattern, varPattern, conType } from "system-f-omega";
 *
 * console.log(showPattern(conPattern("None", conType("Unit"))));     // "None"
 * console.log(showPattern(variantPattern("Some", varPattern("x")))); // "Some(x)"
 * ```
 *
 * Record and tuple patterns:
 * ```ts
 * import { showPattern, recordPattern, tuplePattern, varPattern } from "system-f-omega";
 *
 * console.log(showPattern(recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", varPattern("b")]
 * ]))); // "{x: a, y: b}"
 *
 * console.log(showPattern(tuplePattern([
 *   varPattern("a"),
 *   varPattern("b")
 * ]))); // "(a, b)"
 * ```
 */
export function showPattern(p: Pattern): string {
  if ("var" in p) return p.var;
  if ("wildcard" in p) return "_";
  if ("con" in p) return p.con.name;
  if ("record" in p) {
    const fields = p.record
      .map(([label, pat]) => `${label}: ${showPattern(pat)}`)
      .join(", ");
    return `{${fields}}`;
  }
  if ("variant" in p) {
    return `${p.variant.label}(${showPattern(p.variant.pattern)})`;
  }
  if ("tuple" in p) {
    const elements = p.tuple.map(showPattern).join(", ");
    return `(${elements})`;
  }
  return "unknown";
}

/**
 * Pretty‑prints a {@link TraitDef} into a human‑readable, multi‑line format.
 *
 * **What it represents**
 * `showTraitDef` displays the structure of a trait definition, including:
 * - the trait name
 * - its type parameter and kind
 * - each method and its type signature
 *
 * Output format:
 * ```
 * TraitDef (Eq A = *
 *   eq : (A → Bool)
 * )
 * ```
 *
 * This mirrors how traits are printed in context listings (via {@link showBinding})
 * and error messages.
 *
 * **Why it's useful**
 * Pretty‑printing trait definitions is important for:
 * - diagnostic messages in the REPL or CLI
 * - debugging mismatched method signatures
 * - showing trait bindings in {@link showContext}
 * - validating dictionary implementations
 *
 * `showTraitDef` provides a consistent, readable representation for learners and
 * experts alike.
 *
 * **Formatting rules**
 * - `TraitDef (name typeParam = kind`
 * - Each method printed on its own line:
 *   `  methodName : methodType`
 * - Closed with a final `)` for grouping
 *
 * **Related**
 * - {@link TraitDef} — the trait metadata structure
 * - {@link showBinding} — prints the full binding for traits
 * - {@link showType} — used to render method signatures
 * - {@link showKind} — used for printing the parameter kind
 *
 * **Examples**
 *
 * Basic trait:
 * ```ts
 * import { showTraitDef, starKind, arrowType, varType } from "system-f-omega";
 *
 * const eq = {
 *   name: "Eq",
 *   type_param: "A",
 *   kind: starKind,
 *   methods: [
 *     ["eq", arrowType(varType("A"), arrowType(varType("A"), { con: "Bool" }))]
 *   ]
 * };
 *
 * console.log(showTraitDef(eq));
 * // TraitDef (Eq A = *
 * //   eq : (A → (A → Bool))
 * // )
 * ```
 *
 * Higher‑kinded trait:
 * ```ts
 * import { showTraitDef, arrowKind, starKind, varType } from "system-f-omega";
 *
 * const functor = {
 *   name: "Functor",
 *   type_param: "F",
 *   kind: arrowKind(starKind, starKind),
 *   methods: [
 *     ["map", varType("MapType")]  // pretend type for example
 *   ]
 * };
 *
 * console.log(showTraitDef(functor));
 * ```
 */
export const showTraitDef = (t: TraitDef) => {
  return `TraitDef (${t.name} ${t.type_param} = ${showKind(t.kind)}\n${t.methods.map((y) => `  ${y[0]} : ${showType(y[1])}`).join("\n")})`;
};
