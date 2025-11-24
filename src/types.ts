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
 * Tuple index out-of-bounds error (invalid projection index).
 *
 * **Purpose**: Bounds check failure:
 * - **Inference** (`inferTupleProjectType`): `index < 0` or `≥ tuple.length`.
 * Reports tuple type + index (post-normalization).
 *
 * @typedef {Object} TupleIndexOutofBoundsTypeError
 * @property {Object} tuple_index_out_of_bounds
 * @property {Type} tuple_index_out_of_bounds.tuple - Tuple type
 * @property {number} tuple_index_out_of_bounds.index - Invalid index
 *
 * @example Construction
 * ```ts
 * import { TupleIndexOutofBoundsTypeError, tupleType, conType } from "system-f-omega";
 *
 * const err: TupleIndexOutofBoundsTypeError = {
 *   tuple_index_out_of_bounds: { tuple: tupleType([conType("Int")]), index: 1 }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Projection out-of-bounds
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, tupleProjectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup1 = tupleTerm([conTerm("1", conType("Int"))]);  // Length 1
 * const proj1 = tupleProjectTerm(tup1, 1);  // Index 1 ≥ 1
 * const result = inferType(state, proj1);
 * console.log("error:", showError(result.err));  // "Tuple index out of bounds: Tuple: (Int,), Index: 1"
 * ```
 *
 * @see {@link inferTupleProjectType} Producer
 * @see {@link tupleProjectTerm} Usage
 * @see {@link showError} "Tuple index out of bounds: Tuple: τ, Index: n"
 */
export type TupleIndexOutofBoundsTypeError = {
  tuple_index_out_of_bounds: { tuple: Type; index: number };
};

/**
 * Missing trait impl error (no dictionary for trait+type).
 *
 * **Purpose**: Resolution failure:
 * - **Exact**: No `trait_impl` with `typesEqual(type)`.
 * - **Poly**: No instantiable impl (unify fail).
 * From `checkTraitImplementation` (single), `checkTraitConstraints` (multi).
 *
 * @typedef {Object} MissingTraitImplError
 * @property {Object} missing_trait_impl
 * @property {string} missing_trait_impl.trait - Missing trait (`"Eq"`)
 * @property {Type} missing_trait_impl.type - Target type (`String`)
 *
 * @example Construction
 * ```ts
 * import { MissingTraitImplError, conType } from "system-f-omega";
 *
 * const err: MissingTraitImplError = {
 *   missing_trait_impl: { trait: "Eq", type: conType("String") }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example No impl (exact)
 * ```ts
 * import { freshState, addType, addTraitDef, checkTraitImplementation, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")]]).ok;  // Def only
 *
 * const result = checkTraitImplementation(state, "Eq", conType("String"));
 * console.log("error:", showError(result.err));  // "Missing trait implementation: Trait: Eq Type: String"
 * ```
 *
 * @example Poly impl mismatch
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, checkTraitImplementation, forallType, appType, starKind, showError } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")]]).ok;
 * const polyDict = dictTerm("Eq", forallType("a", starKind, varType("a")), []);  // Poly impl
 * state.ctx.push(traitImplBinding("Eq", appType(conType("List"), conType("Int")), polyDict));  // List<Int>
 *
 * const result = checkTraitImplementation(state, "Eq", conType("String"));  // No String
 * console.log("no impl:", showError(result.err));  // "Missing trait implementation: Trait: Eq Type: String"
 * ```
 *
 * @see {@link checkTraitImplementation} Single producer
 * @see {@link checkTraitConstraints} Multi producer
 * @see {@link traitImplBinding} Stores impls
 * @see {@link showError} "Missing trait implementation: Trait: T Type: τ"
 */
export type MissingTraitImplError = {
  missing_trait_impl: { trait: string; type: Type };
};

/**
 * Missing method error (dict lacks required trait method).
 *
 * **Purpose**: Dict validation failures:
 * - **inferDictType**: Provided methods miss required from trait_def.
 * - **inferTraitMethodType**: Method absent in dict/trait_def.
 * Reports trait + method (no type, sig from trait_def).
 *
 * @typedef {Object} MissingMethodError
 * @property {Object} missing_method
 * @property {string} missing_method.trait - Trait name
 * @property {string} missing_method.method - Missing method
 *
 * @example Construction
 * ```ts
 * import { MissingMethodError } from "system-f-omega";
 *
 * const err: MissingMethodError = {
 *   missing_method: { trait: "Eq", method: "lt" }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Dict missing method
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, dictTerm, conType, starKind, arrowType, varType, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))],
 *   ["lt", arrowType(varType("A"), varType("Bool"))]
 * ]).ok;
 *
 * const incompleteDict = dictTerm("Eq", conType("Int"), [["eq", conType("Int")]]);  // Missing lt
 * const result = inferType(state, incompleteDict);
 * console.log("error:", showError(result.err));  // "Missing method 'lt' in trait 'Eq'"
 * ```
 *
 * @example Trait method (missing in dict)
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, inferType, traitMethodTerm, varTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")], ["lt", conType("Bool")]]).ok;
 * const noLtDict = dictTerm("Eq", conType("Int"), [["eq", conType("Int")]]);
 * state = addDict(state, "eqInt", noLtDict).ok;
 *
 * const ltMethod = traitMethodTerm(varTerm("eqInt"), "lt");
 * const result = inferType(state, ltMethod);
 * console.log("missing method:", showError(result.err));  // "Missing method 'lt' in trait 'Eq'"
 * ```
 *
 * @see {@link inferDictType} Dict validation
 * @see {@link inferTraitMethodType} Method lookup
 * @see {@link showError} "Missing method 'm' in trait 'T'"
 */
export type MissingMethodError = {
  missing_method: { trait: string; method: string };
};

/**
 * Wrong number of dictionaries error (trait app mismatch).
 *
 * **Purpose**: TraitAppTerm dicts != constraints:
 * - **inferTraitAppTerm**: Checks `dicts.length == constraints.length` pre-resolution.
 * Reports expected (constraints) vs actual (provided).
 *
 * @typedef {Object} WrongNumberOfDictsError
 * @property {Object} wrong_number_of_dicts
 * @property {number} wrong_number_of_dicts.expected - Required dicts
 * @property {number} wrong_number_of_dicts.actual - Provided dicts
 *
 * @example Construction
 * ```ts
 * import { WrongNumberOfDictsError } from "system-f-omega";
 *
 * const err: WrongNumberOfDictsError = {
 *   wrong_number_of_dicts: { expected: 1, actual: 0 }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Trait app (missing dict)
 * ```ts
 * import { freshState, inferType, traitAppTerm, traitLamTerm, conType, starKind, varType, showError } from "system-f-omega";
 *
 * let state = freshState();
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], conType("Int"));
 * const badApp = traitAppTerm(traitLam, conType("Int"), []);  // 0 dicts, needs 1
 * const result = inferType(state, badApp);
 * console.log("error:", showError(result.err));  // "Wrong number of dictionaries provided: Expected: 1 Actual: 0"
 * ```
 *
 * @example Trait app (extra dicts)
 * ```ts
 * import { freshState, inferType, traitAppTerm, traitLamTerm, conType, starKind, varType, dictTerm, showError } from "system-f-omega";
 *
 * let state = freshState();
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [], conType("Int"));  // 0 constraints
 * const eqDict = dictTerm("Eq", conType("Int"), []);
 * const badApp = traitAppTerm(traitLam, conType("Int"), [eqDict]);  // 1 dict, needs 0
 * const result = inferType(state, badApp);
 * console.log("extra dicts:", showError(result.err));  // "Wrong number of dictionaries provided: Expected: 0 Actual: 1"
 * ```
 *
 * @see {@link inferTraitAppType} Producer
 * @see {@link traitAppTerm} Usage
 * @see {@link showError} "Wrong number of dictionaries provided: Expected: n Actual: m"
 */
export type WrongNumberOfDictsError = {
  wrong_number_of_dicts: { expected: number; actual: number };
};

/**
 * Unexpected kind assigned to binding error.
 *
 * **Purpose**: Binding kind mismatch in context:
 * - **addType/TraitDef**: Assigned kind unexpected (ctx validation).
 * - **Param kinds**: Mismatch during alias/enum/trait param binding.
 * Reports name + kind (pre-binding).
 *
 * @typedef {Object} UnexpectedKindError
 * @property {Object} unexpected_kind
 * @property {string} unexpected_kind.name - Binding name
 * @property {Kind} unexpected_kind.kind - Unexpected kind
 *
 * @example Construction
 * ```ts
 * import { UnexpectedKindError, starKind, arrowKind } from "system-f-omega";
 *
 * const err: UnexpectedKindError = {
 *   unexpected_kind: { name: "List", kind: arrowKind(starKind, starKind) }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Hypothetical binder mismatch
 * ```ts
 * // Assume addType validates against expected (e.g., primitive * only)
 * import { freshState, addType, starKind, arrowKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * // If primitive expected * but arrow given
 * const result = addType(state, "Int", arrowKind(starKind, starKind));  // Hypothetical strict
 * console.log("unexpected:", showError(result.err));  // "Unexpected kind assigned to 'Int': (* → *)"
 * ```
 *
 * @see {@link addType} Potential producer
 * @see {@link showError} "Unexpected kind assigned to 'name': κ"
 */
export type UnexpectedKindError = {
  unexpected_kind: { name: string; kind: Kind };
};

/**
 * Circular import error (cyclic dependencies).
 *
 * **Purpose**: Module import cycle detection:
 * - **collectDependencies** DFS: `A → B → ... → A`.
 * Reports cycle start + path (`visiting` stack).
 * From `importModule` → prevents infinite deps.
 *
 * @typedef {Object} CircularImportError
 * @property {Object} circular_import
 * @property {string} circular_import.name - Cycle trigger name
 * @property {string[]} circular_import.cycle - Cycle path `["A", "B", "A"]`
 *
 * @example Construction
 * ```ts
 * import { CircularImportError } from "system-f-omega";
 *
 * const err: CircularImportError = {
 *   circular_import: { name: "A", cycle: ["A", "AliasA", "A"] }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Cycle in deps (alias self-ref)
 * ```ts
 * import { freshState, addType, collectDependencies, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "A", { star: null }).ok;
 * // Hypothetical self-ref alias: A → AliasA → A
 * state.ctx.push({ type_alias: { name: "AliasA", params: [], kinds: [], body: { con: "A" } } });
 *
 * const result = collectDependencies(state, ["A"]);
 * console.log("cycle:", showError(result.err));  // "Circular import detected involving 'A': Cycle: A → AliasA → A"
 * ```
 *
 * @example importModule propagation
 * ```ts
 * import { freshState, importModule, showError } from "system-f-omega";
 *
 * let from = freshState();  // Assume cyclic deps
 * let into = freshState();
 * const result = importModule({ from, into, roots: ["A"] });
 * console.log("import cycle:", "circular_import" in result.err);  // true
 * ```
 *
 * @see {@link collectDependencies} DFS producer
 * @see {@link importModule} Module importer
 * @see {@link showError} "Circular import detected involving 'name': Cycle: A → B → ..."
 */
export type CircularImportError = {
  circular_import: { name: string; cycle: string[] };
};

/**
 * Duplicate binding error (name conflict in context).
 *
 * **Purpose**: Prevents overwriting in `add*`/`importModule`:
 * - **add***: Duplicate name (`addType("Int")` twice).
 * - **importModule**: Root deps conflict (unless `allowOverrides=true`).
 * Reports **name + both bindings** (existing/incoming) for diagnosis.
 *
 * @typedef {Object} DuplicateBindingError
 * @property {Object} duplicate_binding
 * @property {string} duplicate_binding.name - Conflicting name
 * @property {Binding} duplicate_binding.existing - Current binding
 * @property {Binding} duplicate_binding.incoming - New binding
 *
 * @example Construction
 * ```ts
 * import { DuplicateBindingError, typeBinding, starKind } from "system-f-omega";
 *
 * const err: DuplicateBindingError = {
 *   duplicate_binding: {
 *     name: "Int",
 *     existing: typeBinding("Int", starKind),
 *     incoming: typeBinding("Int", starKind)
 *   }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example addType duplicate
 * ```ts
 * import { freshState, addType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const result = addType(state, "Int", starKind);  // Duplicate
 * console.log("error:", showError(result.err));
 * // "Duplicate binding for 'Int':
 * //   Existing: Type: Int = *
 * //   Incoming: Type: Int = *"
 * ```
 *
 * @example importModule root conflict
 * ```ts
 * import { freshState, addType, importModule, starKind, showError } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;  // Conflicts
 *
 * const result = importModule({ from, into, roots: ["Int"] });
 * console.log("import conflict:", showError(result.err));
 * // "Duplicate binding for 'Int':
 * //   Existing: Type: Int = *
 * //   Incoming: Type: Int = *"
 * ```
 *
 * @example Override (allowOverrides)
 * ```ts
 * import { freshState, addType, importModule, starKind } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;
 *
 * const result = importModule({
 *   from, into, roots: ["Int"],
 *   allowOverrides: true  // Overrides existing
 * });
 * console.log("overridden:", "ok" in result);  // true
 * ```
 *
 * @see {@link addBinding} Primary producer
 * @see {@link addType/Term/TraitDef/Impl/Dict/Enum/Alias} add* callers
 * @see {@link importModule} Import conflicts
 * @see {@link showError} "Duplicate binding for 'name': Existing: ... Incoming: ..."
 */
export type DuplicateBindingError = {
  duplicate_binding: {
    name: string;
    existing: Binding;
    incoming: Binding;
  };
};

/**
 * Type checking errors from bidirectional inference/analysis.
 *
 * **Purpose**: **Precise diagnostics** for all failures:
 * - **Lookup**: Unbound vars/cons, missing impls/methods/fields/cases.
 * - **Formation**: Kind mismatches (HKT apps, binders, data fields).
 * - **Unification**: Type mismatches, cycles (occurs check).
 * - **Data**: Wrong constructors (not_a_*), index bounds, exhaustiveness.
 * - **Traits**: Wrong dict count, missing evidence.
 * - **Modules**: Cycles, duplicates.
 * Returned in `Result<TypingError, T>` from all APIs (`inferType`, `checkType`, `add*`, `importModule`).
 * Pretty-printed via `showError`.
 *
 * **Error hierarchy**:
 * | Category | Errors | Common triggers |
 * |----------|--------|-----------------|
 * | **Lookup** | `UnboundTypeError`, `Missing*Error` | Missing bindings/impls/methods/fields/cases |
 * | **Kinds** | `KindMismatchTypeError`, `UnexpectedKindError`, `NotATypeFunctionTypeError` | HKT apps, binders, data fields |
 * | **Types** | `TypeMismatchTypeError`, `CyclicTypeError` | Unification/subsumption failures |
 * | **Data** | `NotA*TypeError`, `TupleIndexOutofBoundsTypeError`, `ExtraCaseTypeError` | Wrong constructors, bounds, over-coverage |
 * | **Traits** | `MissingTraitImplError`, `MissingMethodError`, `WrongNumberOfDictsError` | Resolution, dict validation |
 * | **Modules** | `CircularImportError`, `DuplicateBindingError` | Import cycles/conflicts |
 *
 * @typedef {Union} TypingError
 * @type {UnboundTypeError} Missing type var/constructor
 * @type {KindMismatchTypeError} Wrong kind (HKT app, binder body)
 * @type {TypeMismatchTypeError} Incompatible types (unify/subsumes)
 * @type {NotAFunctionTypeError} App on non-function
 * @type {NotATypeFunctionTypeError} Type app on non-HKT
 * @type {CyclicTypeError} Infinite type (occurs check)
 * @type {NotARecordTypeError} Record op on non-record
 * @type {MissingFieldTypeError} Absent record field
 * @type {NotAVariantTypeError} Variant op on non-variant
 * @type {InvalidVariantTypeError} Wrong variant label
 * @type {MissingCaseTypeError} Non-exhaustive match
 * @type {ExtraCaseTypeError} Unreachable match case
 * @type {NotATupleTypeError} Tuple op on non-tuple
 * @type {TupleIndexOutofBoundsTypeError} Invalid tuple index
 * @type {MissingTraitImplError} No dict for trait+type
 * @type {MissingMethodError} Absent trait method
 * @type {WrongNumberOfDictsError} Trait app dict count mismatch
 * @type {UnexpectedKindError} Binding kind mismatch
 * @type {CircularImportError} Module cycle
 * @type {DuplicateBindingError} Name conflict
 *
 * @example Construction (major categories)
 * ```ts
 * import {
 *   UnboundTypeError, KindMismatchTypeError, TypeMismatchTypeError,
 *   MissingTraitImplError, CyclicTypeError, DuplicateBindingError,
 *   starKind, conType
 * } from "system-f-omega";
 * import { typeBinding } from "system-f-omega";
 *
 * // Lookup
 * const unbound: UnboundTypeError = { unbound: "Missing" };
 *
 * // Kinds
 * const kindMismatch: KindMismatchTypeError = {
 *   kind_mismatch: { expected: starKind, actual: { arrow: { from: starKind, to: starKind } } }
 * };
 *
 * // Types
 * const typeMismatch: TypeMismatchTypeError = {
 *   type_mismatch: { expected: conType("Int"), actual: conType("Bool") }
 * };
 *
 * // Traits
 * const missingImpl: MissingTraitImplError = { missing_trait_impl: { trait: "Eq", type: conType("String") } };
 *
 * // Cycles
 * const cyclic: CyclicTypeError = { cyclic: "a" };
 *
 * // Modules
 * const duplicate: DuplicateBindingError = {
 *   duplicate_binding: { name: "Int", existing: typeBinding("Int", starKind), incoming: typeBinding("Int", starKind) }
 * };
 * ```
 *
 * @example Real inference failures
 * ```ts
 * import { freshState, addType, inferType, checkType, lamTerm, appTerm, varTerm, conTerm, projectTerm, matchTerm, variantPattern, varPattern, recordTerm, conType, starKind, arrowType, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * // Type mismatch (app arg)
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const badApp = appTerm(id, conTerm("true", conType("Bool")));
 * console.log("app err:", showError(inferType(state, badApp).err));
 *
 * // Not a record (project)
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * console.log("project err:", showError(inferType(state, projectTerm(conTerm("42", conType("Int")), "x")).err));
 *
 * // Missing impl (assume traits)
 * ```
 *
 * @example showError output
 * ```ts
 * import { freshState, inferType, showError } from "system-f-omega";
 * import { lamTerm, varTerm, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const badLam = lamTerm("x", conType("Bool"), varTerm("x"));  // Assume Bool missing
 * console.log(showError(inferType(state, badLam).err));  // Formatted error
 * ```
 *
 * @see {@link inferType} Synthesis errors
 * @see {@link checkType} Checking errors
 * @see {@link checkKind} Kind errors
 * @see {@link checkPattern} Pattern errors
 * @see {@link checkExhaustive} Match errors
 * @see {@link importModule} Binding/module errors
 * @see {@link showError} Pretty-printer
 * @see {@link Result} Error container
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
 * Type equality constraint `left = right` (unification equation).
 *
 * **Purpose**: **Core unification primitive**:
 * - Added during inference/checking: app args, subsumption, patterns.
 * - Processed by `solveConstraints` → `processConstraint` → `unifyTypes`.
 * - Triggers normalization, flex-rigid binding, structural recursion.
 * Drives entire type inference via worklist.
 *
 * @typedef {Object} TypeEqConstraint
 * @property {Object} type_eq
 * @property {Type} type_eq.left - Left type
 * @property {Type} type_eq.right - Right type
 *
 * @example Construction (typeEq helper)
 * ```ts
 * import { typeEq, varType, conType } from "system-f-omega";
 *
 * const constraint: TypeEqConstraint = typeEq(varType("a"), conType("Int"));
 * console.log(JSON.stringify(constraint));
 * ```
 *
 * @example Worklist solving
 * ```ts
 * import { freshState, solveConstraints, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq(varType("a"), conType("Int"))];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("a := Int:", subst.has("a"));  // true
 * ```
 *
 * @example Real inference (app arg unify)
 * ```ts
 * import { freshState, addType, inferType, lamTerm, appTerm, varTerm, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const app = appTerm(id, conTerm("42", conType("Int")));
 * // inferAppType adds typeEq(?0, Int) internally
 * const result = inferType(state, app);
 * console.log("solved via constraints");
 * ```
 *
 * @see {@link typeEq} Constructor
 * @see {@link solveConstraints} Worklist solver
 * @see {@link unifyTypes} Processor
 * @see {@link Constraint} Worklist item
 */
export type TypeEqConstraint = { type_eq: { left: Type; right: Type } };

/**
 * Kind equality constraint `left = right` (kind unification).
 *
 * **Purpose**: **HKT kind matching**:
 * - Added by `checkAppKind`: `func :: κ₁ → κ₂`, `arg :: κ₁`.
 * - Processed by `solveConstraints` → `unifyKinds` (structural).
 * Less common than types (triggers on HKT apps like `List<Int>`).
 *
 * @typedef {Object} KindEqConstraint
 * @property {Object} kind_eq
 * @property {Kind} kind_eq.left - Left kind
 * @property {Kind} kind_eq.right - Right kind
 *
 * @example Construction (kindEq helper)
 * ```ts
 * import { kindEq, starKind, arrowKind } from "system-f-omega";
 *
 * const constraint: KindEqConstraint = kindEq(starKind, arrowKind(starKind, starKind));
 * console.log(JSON.stringify(constraint));
 * ```
 *
 * @example Worklist solving (success)
 * ```ts
 * import { freshState, solveConstraints, kindEq, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [kindEq(starKind, starKind)];
 * const result = solveConstraints(state, worklist);
 * console.log("equal:", "ok" in result);  // true
 * ```
 *
 * @example Worklist failure (mismatch)
 * ```ts
 * import { freshState, solveConstraints, kindEq, starKind, arrowKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [kindEq(starKind, arrowKind(starKind, starKind))];
 * const result = solveConstraints(state, worklist);
 * console.log("mismatch:", "kind_mismatch" in result.err);  // true
 * ```
 *
 * @example Real HKT app (kindEq added)
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, arrowKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * state = addType(state, "Int", starKind).ok;
 *
 * // checkAppKind adds kindEq(starKind, starKind) internally
 * const result = checkKind(state, appType(conType("List"), conType("Int")));
 * console.log("HKT kind OK");
 * ```
 *
 * @see {@link kindEq} Constructor
 * @see {@link solveConstraints} Worklist solver
 * @see {@link unifyKinds} Processor
 * @see {@link checkAppKind} HKT trigger
 * @see {@link Constraint} Worklist item
 */
export type KindEqConstraint = { kind_eq: { left: Kind; right: Kind } };

/**
 * Has-kind constraint `Γ ⊢ ty : kind` (deferred well-formedness).
 *
 * **Purpose**: **Defer type kinding** to solver:
 * - Added when kind needed but ctx/metas incomplete (unification, alias bodies).
 * - Solver: `checkKind(state, ty)` → add `kindEq(result, kind)`.
 * Avoids premature errors during constraint propagation.
 *
 * @typedef {Object} HasKindConstraint
 * @property {Object} has_kind
 * @property {Type} has_kind.ty - Type to kind-check
 * @property {Kind} has_kind.kind - Expected kind
 * @property {TypeCheckerState} has_kind.state - Checker state (ctx/meta snapshot)
 *
 * @example Construction (hasKind helper)
 * ```ts
 * import { hasKind, lamType, starKind } from "system-f-omega";
 * import { freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const constraint = hasKind(lamType("X", starKind, { var: "X" }), starKind, state);
 * console.log(JSON.stringify(constraint));
 * ```
 *
 * @example Worklist deferral
 * ```ts
 * import { freshState, solveConstraints, hasKind, lamType, starKind, arrowKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [hasKind(lamType("X", starKind, { var: "X" }), starKind, state)];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("defers → kindEq(*, *→*):", "kind_mismatch" in result.err);  // true (mismatch)
 * ```
 *
 * @see {@link hasKind} Constructor
 * @see {@link solveConstraints} Processor
 * @see {@link checkKind} Triggered check
 */
export type HasKindConstraint = {
  has_kind: { ty: Type; kind: Kind; state: TypeCheckerState };
};

/**
 * Has-type constraint `Γ ⊢ term : ty` (deferred subterm typing).
 *
 * **Purpose**: **Defer inference/checking** of subterms:
 * - Added in bidirectional when ctx incomplete (lets, trait methods, dicts).
 * - Solver: `inferType(state, term)` → add `typeEq(result, ty)`.
 * Enables constraint-based flow (no blocking inference).
 *
 * @typedef {Object} HasTypeConstraint
 * @property {Object} has_type
 * @property {Term} has_type.term - Term to type
 * @property {Type} has_type.ty - Expected type
 * @property {TypeCheckerState} has_type.state - Checker state (ctx/meta snapshot)
 *
 * @example Construction (hasType helper)
 * ```ts
 * import { hasType, lamTerm, arrowType } from "system-f-omega";
 * import { freshState, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const constraint = hasType(lamTerm("x", conType("Int"), { var: "x" }), arrowType(conType("Int"), conType("Int")), state);
 * console.log(JSON.stringify(constraint));
 * ```
 *
 * @example Worklist deferral
 * ```ts
 * import { freshState, solveConstraints, hasType, lamTerm, arrowType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [hasType(lamTerm("x", conType("Int"), { var: "x" }), arrowType(conType("Int"), conType("Bool")), state)];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("defers → typeEq");
 * ```
 *
 * @see {@link hasType} Constructor
 * @see {@link solveConstraints} Processor
 * @see {@link inferType} Triggered inference
 */
export type HasTypeConstraint = {
  has_type: { term: Term; ty: Type; state: TypeCheckerState };
};

/**
 * Constraints for worklist-based unification/solving.
 *
 * **Purpose**: **Deferred solving** via `solveConstraints(worklist, subst)`:
 * - **Atomic**: `type_eq`/`kind_eq` → immediate unify.
 * - **Deferred**: `has_kind`/`has_type` → trigger inference/check → add eqs.
 * Processed by `processConstraint` loop until fixed-point.
 * Enables **non-blocking inference**: generate → solve → propagate.

 * | Variant | Trigger | Processor |
 * |---------|---------|-----------|
 * | `TypeEqConstraint` | App args, subsumption | `unifyTypes` (flex-rigid/structural) |
 * | `KindEqConstraint` | HKT apps | `unifyKinds` (structural) |
 * | `HasKindConstraint` | Well-formedness needed | `checkKind` → `kindEq` |
 * | `HasTypeConstraint` | Subterm typing | `inferType` → `typeEq` |

 * @typedef {Union} Constraint
 * @type {TypeEqConstraint} `left = right` - Type unification
 * @type {KindEqConstraint} `left = right` - Kind unification
 * @type {HasKindConstraint} `Γ ⊢ ty : kind` - Deferred kinding
 * @type {HasTypeConstraint} `Γ ⊢ term : ty` - Deferred typing

 * @example Construction (helpers)
 * ```ts
 * import { typeEq, kindEq, hasKind, hasType } from "system-f-omega";
 * import { freshState, varType, conType, lamTerm, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 *
 * // Atomic
 * const typeC = typeEq(varType("a"), conType("Int"));
 * const kindC = kindEq({ star: null }, { star: null });
 *
 * // Deferred
 * const kindC2 = hasKind(varType("a"), { star: null }, state);
 * const typeC2 = hasType(lamTerm("x", conType("Int"), { var: "x" }), arrowType(conType("Int"), conType("Int")), state);
 * ```

 * @example Worklist solving
 * ```ts
 * import { freshState, solveConstraints, typeEq, kindEq, hasKind } from "system-f-omega";
 * import { varType, conType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [
 *   typeEq(varType("a"), conType("Int")),  // Solves a=Int
 *   kindEq(starKind, starKind),            // Trivial
 *   hasKind(varType("a"), starKind, state) // Defers → kindEq
 * ];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("solved:", "ok" in result && subst.has("a"));  // true
 * ```

 * @example Real inference (internal constraints)
 * ```ts
 * import { freshState, addType, inferType, lamTerm, appTerm, varTerm, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const app = appTerm(id, conTerm("42", conType("Int")));
 * // inferAppType/checkType generate type_eq(?0, Int) internally
 * const result = inferType(state, app);
 * console.log("constraints solved implicitly");
 * ```

 * @see {@link solveConstraints} Worklist solver
 * @see {@link processConstraint} Dispatcher
 * @see {@link typeEq/kindEq/hasKind/hasType} Constructors
 * @see {@link unifyTypes} TypeEq processor
 * @see {@link inferType/checkKind} Has* triggers
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
 * Closure/thunk environment (var → value mapping).
 *
 * **Purpose**: **Captured bindings** for evaluation:
 * - **Closures** (`vlam`): `env` at lambda creation.
 * - **Thunks** (`vthunk`): Lazy env for call-by-name.
 * - **Lookup**: `vvar "x"` → `env.get("x")`.
 * Used in big-step eval (experimental).
 *
 * @typedef {Map<string, Value>} Environment
 *
 * @example Construction
 * ```ts
 * import type { Environment, Value } from "system-f-omega";
 *
 * const env: Environment = new Map([
 *   ["x", { vvar: "self" } as Value],
 *   ["id", { vlam: { param: "y", body: { var: "y" }, env: new Map() } } as Value]
 * ]);
 * ```
 *
 * @example Closure capture
 * ```ts
 * import type { Environment, Value } from "system-f-omega";
 *
 * const outerEnv: Environment = new Map([["f", { vvar: "add" } as Value]]);
 * const closure: Value = {
 *   vlam: {
 *     param: "x",
 *     body: { var: "x" },
 *     env: outerEnv  // Captures outer
 *   }
 * };
 * ```
 *
 * @see {@link Value.vlam/vthunk} Uses env
 * @see {@link EvalResult} Eval output
 */
export type Environment = Map<string, Value>;

/**
 * Evaluation result: success value or string error (experimental).
 *
 * **Purpose**: **Big-step eval** output:
 * - **Success**: Reduced `Value` (closures/data).
 * - **Errors**: Simple strings (`"unbound x"`, `"non-exhaustive"`, `"max steps"`).
 * From `eval(term, env?, config?)` (CBV/CBN, steps).
 * Uses untagged `Result<string, Value>` (string errs).
 *
 * @typedef {Result<string, Value>} EvalResult
 *
 * @example Success (Value)
 * ```ts
 * import type { EvalResult, Value } from "system-f-omega";
 *
 * const success: EvalResult = { ok: { vvar: "42" } as Value };
 * ```
 *
 * @example Error (string)
 * ```ts
 * import type { EvalResult } from "system-f-omega";
 *
 * const err: EvalResult = { err: "Unbound variable 'x'" };
 * ```
 *
 * @see {@link Result} Untagged union
 * @see {@link Value} Success type
 * @see {@link EvalConfig} Eval options
 * @see {@link Environment} Eval env
 */
export type EvalResult = Result<string, Value>; // Using string for error messages

/**
 * Evaluation configuration (experimental).
 *
 * **Purpose**: Controls **reduction strategy** + safety:
 * - **strict**: Call-by-value (reduce args first) vs call-by-name (lazy thunks).
 * - **maxSteps**: Loop prevention (divergence guard).
 * Passed to `eval(term, env?, config?)`.
 *
 * @typedef {Object} EvalConfig
 * @property {boolean} strict - `true`: CBV (reduce `vapp.arg`), `false`: CBN (`vthunk`)
 * @property {number} maxSteps - Step limit (defaults `∞` or large)
 *
 * @example CBV (strict=true)
 * ```ts
 * import type { EvalConfig } from "system-f-omega";
 *
 * const cbv: EvalConfig = { strict: true, maxSteps: 1000 };
 * // Reduces args eagerly
 * ```
 *
 * @example CBN (strict=false)
 * ```ts
 * import type { EvalConfig } from "system-f-omega";
 *
 * const cbn: EvalConfig = { strict: false, maxSteps: 1000 };
 * // Lazy args (thunks)
 * ```
 *
 * @see {@link EvalResult} Output
 * @see {@link Value.vthunk} Lazy values
 */
export type EvalConfig = {
  strict: boolean; // true for call-by-value, false for call-by-name
  maxSteps: number; // for preventing infinite loops
};

/**
 * Generic success/error result (tagged union).
 *
 * **Purpose**: **Error monad** for all APIs:
 * - **ok**: Success value.
 * - **err**: Error payload.
 * Ubiquitous: `inferType: Result<TypingError, Type>`, `eval: Result<string, Value>`, `add*: Result<TypingError, State>`.
 * Processed via `"ok" in res ? res.ok : handle(res.err)` or `showError(err)`.
 *
 * @typedef {Union} Result<TErr, TOk>
 * @template TErr Error type (`TypingError`, `string`)
 * @template TOk Success type (`Type`, `Value`, `State`)
 * @property {TOk} ok - Success value
 * @property {TErr} err - Error payload
 *
 * @example Success (Type)
 * ```ts
 * import type { Result } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const okRes: Result<string, Type> = { ok: conType("Int") };
 * ```
 *
 * @example Error (TypingError)
 * ```ts
 * import type { Result, TypingError } from "system-f-omega";
 *
 * const errRes: Result<TypingError, Type> = {
 *   err: { unbound: "Missing" } as TypingError
 * };
 * ```
 *
 * @example Usage (inferType)
 * ```ts
 * import { freshState, inferType } from "system-f-omega";
 * import type { Result } from "system-f-omega";
 *
 * const state = freshState();
 * const res: Result<any, any> = inferType(state, { var: "x" });
 * if ("ok" in res) {
 *   console.log("Type:", res.ok);
 * } else {
 *   console.log("Error:", res.err);
 * }
 * ```
 *
 * @see {@link TypingError} Common TErr
 * @see {@link EvalResult} Eval specialization (`Result<string, Value>`)
 * @see {@link ok/err} Helpers
 * @see {@link showError} Error display
 */
export type Result<TErr, TOk> = { ok: TOk } | { err: TErr };

/**
 * Free type names in `Type` (binder-respecting dependency analysis).
 *
 * **Purpose**: Collects **free identifiers** for modules/imports:
 * - Skips bound vars (`∀α.τ` → no `α`).
 * - Used in `collectDependencies`, `renameType`, cycle detection.
 * From `computeFreeTypes(type)`.
 *
 * @typedef {Object} FreeTypeNames
 * @property {Set<string>} typeVars - Free vars (`"a"`, `"Self"`)
 * @property {Set<string>} typeCons - Constructors (`"Int"`, `"List"`)
 * @property {Set<string>} traits - Trait names (`"Eq"`)
 * @property {Set<string>} labels - Record/variant labels (`"x"`, `"Left"`)
 *
 * @example Computation
 * ```ts
 * import { computeFreeTypes, arrowType, appType, conType, varType } from "system-f-omega";
 *
 * const ty = arrowType(
 *   appType(conType("List"), varType("a")),
 *   { variant: [["Left", varType("a")]] }
 * );
 * const free = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, ty);
 * console.log("vars:", Array.from(free.typeVars));  // ["a"]
 * console.log("cons:", Array.from(free.typeCons));  // ["List"]
 * console.log("labels:", Array.from(free.labels));  // ["Left"]
 * ```
 *
 * @see {@link computeFreeTypes} Producer
 * @see {@link importModule} Deps/renaming
 */
export type FreeTypeNames = {
  typeVars: Set<string>;
  typeCons: Set<string>;
  traits: Set<string>;
  labels: Set<string>; // variant or record labels
};

/**
 * Free pattern names in `Pattern` (no binders, all vars free).
 *
 * **Purpose**: Pattern dependencies for imports/renaming.
 * Collects vars/cons/labels (patterns bind vars).
 * From `computeFreePatterns(pattern)`.
 *
 * @typedef {Object} FreePatternNames
 * @property {Set<string>} vars - Pattern vars (`"x"`)
 * @property {Set<string>} constructors - Con patterns (`"None"`)
 * @property {Set<string>} labels - Record/variant labels (`"Cons"`)
 *
 * @example Computation
 * ```ts
 * import { computeFreePatterns, recordPattern, variantPattern, varPattern, conPattern } from "system-f-omega";
 *
 * const pat = recordPattern([
 *   ["head", variantPattern("Cons", varPattern("hd"))],
 *   ["tail", conPattern("Nil", { con: "Unit" })]
 * ]);
 * const free = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, pat);
 * console.log("vars:", Array.from(free.vars));     // ["hd"]
 * console.log("cons:", Array.from(free.constructors)); // ["Nil"]
 * console.log("labels:", Array.from(free.labels)); // ["head", "Cons", "tail"]
 * ```
 *
 * @see {@link computeFreePatterns} Producer
 * @see {@link importModule} Renaming
 */
export type FreePatternNames = {
  vars: Set<string>;
  constructors: Set<string>;
  labels: Set<string>;
};

/**
 * Free term names in `Term` (binder-respecting + embedded types/patterns).
 *
 * **Purpose**: Full term dependencies (terms + types + patterns).
 * Used for module analysis (`collectDependencies`).
 * From `computeFreeTerms(term)` (recurses types/patterns).
 *
 * @typedef {Object} FreeTermNames
 * @property {Set<string>} terms - Term vars (`"x"`)
 * @property {Set<string>} constructors - ConTerms (`"42"`)
 * @property {Set<string>} traits - Trait names (`"Eq"`)
 * @property {Set<string>} dicts - Dict vars (`"eqInt"`)
 * @property {Set<string>} labels - Record/method/variant labels
 * @property {Set<string>} typeVars - Embedded type vars
 * @property {Set<string>} typeCons - Embedded type cons
 *
 * @example Computation
 * ```ts
 * import { computeFreeTerms, lamTerm, appTerm, varTerm, recordTerm } from "system-f-omega";
 *
 * const term = lamTerm("x", { con: "Int" }, appTerm(varTerm("f"), recordTerm([["y", varTerm("z")]])));
 * const free = computeFreeTerms({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, term);
 * console.log("terms:", Array.from(free.terms));  // ["f", "z"]
 * console.log("labels:", Array.from(free.labels)); // ["y"]
 * console.log("typeCons:", Array.from(free.typeCons)); // ["Int"]
 * ```
 *
 * @see {@link computeFreeTerms} Producer
 * @see {@link computeFreeTypes} Embedded types
 * @see {@link importModule} Deps/renaming
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
 * Constraint worklist (queue for iterative solving).
 *
 * **Purpose**: **Worklist algorithm** for unification:
 * - Filled by `unifyTypes`/`subsumes`/`infer/check` (generate eqs).
 * - Processed by `solveConstraints` → `processConstraint` until empty.
 * Mutated in-place (shift/pop).
 * Enables **fixed-point solving** (deferred has/eqs).
 *
 * @typedef {Array<Constraint>} Worklist
 *
 * @example Worklist filling (unify)
 * ```ts
 * import { freshState, unifyTypes, appType, conType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Worklist = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, appType(conType("List"), varType("a")), appType(conType("List"), conType("Int")), worklist, subst);
 * console.log("filled:", worklist.length > 0);  // true (typeEq("a", Int))
 * ```
 *
 * @example Solving loop
 * ```ts
 * import { freshState, solveConstraints, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Worklist = [typeEq(varType("a"), conType("Int"))];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("solved:", "ok" in result && subst.has("a"));  // true
 * ```
 *
 * @see {@link solveConstraints} Consumer
 * @see {@link Constraint} Items
 * @see {@link Substitution} Bindings
 */
export type Worklist = Constraint[];

/**
 * Type substitution `?N/α → τ` (local bindings).
 *
 * **Purpose**: **Unification solutions**:
 * - Local (scoped): From `solveConstraints` → merged to global `meta.solutions`.
 * - Applied by `applySubstitution` (resolve metas/vars).
 * - Shadowing: Local > global (`mergeSubsts`).
 * Keys: Meta-vars (`"?0"`) + type vars (`"a"`).
 *
 * @typedef {Map<string, Type>} Substitution
 *
 * @example Local solving
 * ```ts
 * import { freshState, solveConstraints, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq(varType("a"), conType("Int"))];
 * const subst: Substitution = new Map();
 * solveConstraints(state, worklist, subst);
 * console.log("a := Int:", subst.get("a")?.con === "Int");  // true
 * ```
 *
 * @example Merging (local shadows)
 * ```ts
 * import { mergeSubsts, varType, conType } from "system-f-omega";
 *
 * const global = new Map([["a", conType("Bool")]]);
 * const local = new Map([["a", conType("Int")], ["b", conType("String")]]);
 * const merged = mergeSubsts(local, global);
 * console.log("a:Int (local):", merged.get("a")?.con === "Int");  // true
 * ```
 *
 * @example Application
 * ```ts
 * import { freshState, applySubstitution, varType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst: Substitution = new Map([["a", conType("Int")]]);
 * const resolved = applySubstitution(state, subst, varType("a"));
 * console.log("resolved:", resolved.con === "Int");  // true
 * ```
 *
 * @see {@link solveConstraints} Producer
 * @see {@link mergeSubsts} Local+global
 * @see {@link applySubstitution} Consumer
 * @see {@link Worklist} Source
 */
export type Substitution = Map<string, Type>;

/**
 * Success result constructor for `Result<TErr, TOk>`.
 *
 * **Purpose**: Builds `{ok: val}` (tagged success).
 * Ubiquitous in APIs: `inferType.ok(Type)`, `addType.ok(State)`.
 *
 * @template T Success type (`Type`, `State`, `Value`)
 * @param {T} val - Success value
 * @returns `{ok: T}`
 *
 * @example Success (Type)
 * ```ts
 * import { ok } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const success = ok(conType("Int"));  // { ok: { con: "Int" } }
 * console.log("ok:", success.ok.con);  // "Int"
 * ```
 *
 * @example API usage (inferType)
 * ```ts
 * import { freshState, addType, inferType, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;  // Uses ok
 * const result = inferType(state, conTerm("42", conType("Int")));
 * if ("ok" in result) console.log("Type:", result.ok);  // Uses ok internally
 * ```
 *
 * @see {@link err} Failure counterpart
 * @see {@link Result} Tagged union
 */
export const ok = <T>(val: T) => ({ ok: val });

/**
 * Error result constructor for `Result<TErr, TOk>`.
 *
 * **Purpose**: Builds `{err: val}` (tagged failure).
 * Ubiquitous: `inferType.err(TypingError)`, `addType.err(DuplicateBindingError)`.
 *
 * @template T Error type (`TypingError`, `string`)
 * @param {T} val - Error payload
 * @returns `{err: T}`
 *
 * @example Error (TypingError)
 * ```ts
 * import { err, UnboundTypeError } from "system-f-omega";
 *
 * const unboundErr = err({ unbound: "Missing" } as UnboundTypeError);
 * console.log("err:", unboundErr.err.unbound);  // "Missing"
 * ```
 *
 * @example API usage (unbound)
 * ```ts
 * import { freshState, inferType, varTerm } from "system-f-omega";
 *
 * const state = freshState();
 * const result = inferType(state, varTerm("missing"));  // Uses err internally
 * if ("err" in result) console.log("Error:", result.err);  // { unbound: "missing" }
 * ```
 *
 * @see {@link ok} Success counterpart
 * @see {@link Result} Tagged union
 * @see {@link showError} Error display
 */
export const err = <T>(val: T) => ({ err: val });

/**
 * Pretty-prints context bindings (multi-line).
 *
 * **Purpose**: Debugs `TypeCheckerState.ctx`. Uses `showBinding`.
 *
 * @param context - Binding list
 * @returns Newline-joined strings
 *
 * @example Empty context
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(showContext(state.ctx));  // ""
 * ```
 *
 * @example Basic bindings
 * ```ts
 * import { freshState, addType, addTerm, showContext, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", { con: { name: "42", type: conType("Int") } }).ok;
 * console.log(showContext(state.ctx));
 * // "Type: Int = *\nTerm: x = Int"
 * ```
 *
 * @example Complex (trait/enum)
 * ```ts
 * import { freshState, addType, addEnum, addTraitDef, showContext, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }]]).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", { arrow: { from: { var: "A" }, to: { var: "Bool" } }}]]).ok;
 * console.log(showContext(state.ctx));
 * // Multi-line: Type, Enum, TraitDef...
 * ```
 *
 * @see {@link showBinding} Single binding
 * @see {@link freshState} Empty ctx
 */
export const showContext = (context: Context) =>
  context.map((t) => showBinding(t)).join("\n");

/**
 * Extracts spine arguments from left-associated applications.
 *
 * **Purpose**: Deconstructs nominal types: `Either<Int, Bool>` → `["Int", "Bool"]`.
 * Used in nominal unification, enum expansion, `showType`.
 *
 * @param ty - Possibly nested app type
 * @returns Argument array (left-to-right)
 *
 * @example Nested nominal app
 * ```ts
 * import { getSpineArgs, appType, conType } from "system-f-omega";
 *
 * const either = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("spine:", getSpineArgs(either));  // ["Int", "Bool"]
 * ```
 *
 * @example Single app
 * ```ts
 * import { getSpineArgs, appType, conType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log("single:", getSpineArgs(listInt));  // ["Int"]
 * ```
 *
 * @example Non-app
 * ```ts
 * import { getSpineArgs, conType, arrowType } from "system-f-omega";
 * import { conType as int } from "system-f-omega";
 *
 * console.log("con:", getSpineArgs(conType("Int")));       // []
 * console.log("arrow:", getSpineArgs(arrowType(conType("Int"), int("Bool"))));  // []
 * ```
 *
 * @internal Used by {@link unifyTypes}, {@link showType}
 * @see {@link getSpineHead} Head extractor
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
 * Pretty-prints single binding for context display.
 *
 * **Purpose**: Formats `Context` entries. Used by `showContext`.
 *
 * @param bind - Binding variant
 * @returns Formatted string
 *
 * @example Term binding
 * ```ts
 * import { showBinding } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const termBind = { term: { name: "x", type: conType("Int") } };
 * console.log(showBinding(termBind));  // "Term: x = Int"
 * ```
 *
 * @example Type binding
 * ```ts
 * import { showBinding, starKind } from "system-f-omega";
 *
 * const typeBind = { type: { name: "Int", kind: starKind } };
 * console.log(showBinding(typeBind));  // "Type: Int = *"
 * ```
 *
 * @example Trait def
 * ```ts
 * import { showBinding } from "system-f-omega";
 * import { starKind, arrowType, varType } from "system-f-omega";
 *
 * const traitBind = {
 *   trait_def: {
 *     name: "Eq",
 *     type_param: "A",
 *     kind: starKind,
 *     methods: [["eq", arrowType(varType("A"), varType("Bool"))]]
 *   }
 * };
 * console.log(showBinding(traitBind));  // "Trait: Eq = TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * @example Trait impl + dict + alias
 * ```ts
 * import { showBinding, conType } from "system-f-omega";
 *
 * const implBind = { trait_impl: { trait: "Eq", type: conType("Int"), dict: { var: "d" } } };
 * console.log(showBinding(implBind));  // "Impl: Eq = d: Int"
 *
 * const dictBind = { dict: { name: "eqInt", trait: "Eq", type: conType("Int") } };
 * console.log(showBinding(dictBind));  // "Dict: eqInt = Trait Eq : Int"
 *
 * const aliasBind = {
 *   type_alias: { name: "Id", params: ["A"], kinds: [starKind], body: conType("A") }
 * };
 * console.log(showBinding(aliasBind));  // "Type Alias: Id<A::*> = A"
 * ```
 *
 * @see {@link showContext} Multi-binding printer
 * @see {@link showType} Embedded types
 * @see {@link showTraitDef} Trait methods
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
 * Pretty-prints `TypingError` for user-facing diagnostics.
 *
 * **Purpose**: Human-readable errors with context (types/kinds shown).
 * Covers all variants: unbound, mismatch, missing impl/case/field, cyclic, etc.

 * @param err - Typing error
 * @returns Formatted string
 *
 * @example Unbound identifier
 * ```ts
 * import { freshState, inferType, varTerm, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = inferType(state, varTerm("missing"));
 * console.log(showError(result.err));  // "Unbound identifier: missing"
 * ```
 *
 * @example Type mismatch
 * ```ts
 * import { freshState, addType, inferType, conTerm, appTerm, lamTerm, varTerm, arrowType, conType, starKind, showError, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const badApp = appTerm(id, conTerm("true", conType("Bool")));
 * const result = inferType(state, badApp);
 * console.log(showError(result.err));
 * // "Type mismatch:
 * //   Expected: (Int → Int)
 * //   Actual:   Bool"
 * ```
 *
 * @example Missing trait impl
 * ```ts
 * import { freshState, addType, addTraitDef, checkTraitImplementation, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")]]).ok;
 *
 * const result = checkTraitImplementation(state, "Eq", conType("String"));
 * console.log(showError(result.err));  // "Missing trait implementation:\n  Trait: Eq\n  Type:  String"
 * ```
 *
 * @example Non-exhaustive match
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", { var: "Unit" }], ["Blue", { var: "Unit" }]]).ok;
 *
 * const patterns = [variantPattern("Red", varPattern("x"))];  // Missing Blue
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log(showError(result.err));  // "Non-exhaustive match: missing case 'Blue'"
 * ```
 *
 * @example Cyclic type
 * ```ts
 * import { freshState, unifyTypes, arrowType, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map<string, Type>();
 * const result = unifyTypes(state, varType("a"), arrowType(varType("a"), varType("Int")), [], subst);
 * console.log(showError(result.err));  // "Cyclic type detected involving: a"
 * ```
 *
 * @example Duplicate binding (import)
 * ```ts
 * import { freshState, addType, importModule, starKind, showError } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;
 *
 * const result = importModule({ from, into, roots: ["Int"] });
 * console.log(showError(result.err));
 * // "Duplicate binding for 'Int':\n  Existing: Type: Int = *\n  Incoming: Type: Int = *"
 * ```
 *
 * @see {@link inferType} Common caller
 * @see {@link checkType} Checking errors
 */
export function showError(err: TypingError): string {
  if ("unbound" in err) return `Unbound identifier: ${err.unbound}`;

  if ("kind_mismatch" in err) {
    return `Kind mismatch:\n  Expected: ${showKind(err.kind_mismatch.expected)}\n  Actual:   ${showKind(err.kind_mismatch.actual)}`;
  }

  if ("type_mismatch" in err) {
    return `Type mismatch:\n  Expected: ${showType(err.type_mismatch.expected)}\n  Actual:   ${showType(err.type_mismatch.actual)}`;
  }

  if ("not_a_function" in err) {
    return `Not a function:\n  ${showType(err.not_a_function)}`;
  }

  if ("not_a_type_function" in err) {
    return `Not a type-level function:\n  ${showType(err.not_a_type_function)}`;
  }

  if ("cyclic" in err) {
    return `Cyclic type detected involving: ${err.cyclic}`;
  }

  if ("not_a_record" in err) {
    return `Not a record type:\n  ${showType(err.not_a_record)}`;
  }

  if ("missing_field" in err) {
    return `Missing field '${err.missing_field.label}' in record:\n  ${showType(err.missing_field.record)}`;
  }

  if ("not_a_variant" in err) {
    return `Not a variant type:\n  ${showType(err.not_a_variant)}`;
  }

  if ("invalid_variant_label" in err) {
    return `Invalid variant label '${err.invalid_variant_label.label}' for:\n  ${showType(err.invalid_variant_label.variant)}`;
  }

  if ("missing_case" in err) {
    return `Non-exhaustive match: missing case '${err.missing_case.label}'`;
  }

  if ("extra_case" in err) {
    return `Unreachable case in match: '${err.extra_case.label}'`;
  }

  if ("not_a_tuple" in err) {
    return `Not a tuple type:\n  ${showType(err.not_a_tuple)}`;
  }

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
 * Extracts success with custom error message.
 *
 * **Purpose**: `unwrap` + formatted error:
 * - Uses `showError` for TypingError → user-friendly.
 *
 * @template TErr Error type
 * @template TOk Success type
 * @param {Result<TErr, TOk>} result - Result to unwrap
 * @param {string} [msg="Failed"] - Prefix message
 * @returns {TOk} Success value
 * @throws {Error} `${msg}: ${showError(err)}`
 *
 * @example
 * ```ts
 * import { expect, err, UnboundTypeError } from "system-f-omega";
 *
 * expect(err({ unbound: "x" } as UnboundTypeError), "Var lookup failed");
 * // Throws: "Var lookup failed: Unbound identifier: x"
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
 * Pretty-prints kinds for debugging and error messages.
 *
 * **Purpose**: Human-readable kind strings (parenthesized arrows).
 * Used in `showType` (`∀a::κ.τ`), `showTerm` (tylam kinds), kind errors.
 *
 * @param k - Kind to print
 * @returns String (e.g., `*`, `(* → *)`)
 *
 * @example Basic kinds
 * ```ts
 * import { showKind, starKind, arrowKind } from "system-f-omega";
 *
 * showKind(starKind);                           // "*"
 * showKind(arrowKind(starKind, starKind));      // "(* → *)"
 * ```
 *
 * @example Nested HKT
 * ```ts
 * import { showKind, starKind, arrowKind } from "system-f-omega";
 *
 * showKind(arrowKind(starKind, arrowKind(starKind, starKind)));
 * // "(* → ((* → *) → *))"
 * ```
 *
 * @see {@link showType} Uses for polymorphic binders
 * @see {@link showTerm} Tylam/trait-lam kinds
 */
export function showKind(k: Kind): string {
  if ("star" in k) return "*";
  if ("arrow" in k)
    return `(${showKind(k.arrow.from)} → ${showKind(k.arrow.to)})`;
  return "unknown";
}

/**
 * Pretty-prints types for debugging, REPL, and error messages.
 *
 * **Purpose**: Human-readable type strings with conventional notation:
 * - Nominal apps: `Either<I32, Bool>` (spine-aware).
 * - Functions: `(Int → Bool)` (parenthesized).
 * - Polymorphism: `∀a::*. a → a`, `λt::*. t → t`.
 * - Data: `{x: Int}`, `<Left: I32 | Right: Bool>`, `(Int, Bool)`.
 * - Special: `⊥` (never), `?0` (metas), `μX. ...` (recursion).
 *
 * Recursive. Primary output for `inferType`, errors, docs.
 *
 * @param t - Type to print
 * @returns Pretty-printed string
 *
 * @example Nominal type applications
 * ```ts
 * import { showType, appType, conType } from "system-f-omega";
 *
 * showType(appType(appType(conType("Either"), conType("Int")), conType("Bool")));
 * // "Either<Int, Bool>"
 * ```
 *
 * @example Polymorphic + higher-kinded
 * ```ts
 * import { showType, forallType, arrowType, lamType, starKind, arrowKind, varType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * showType(forallType("a", starKind, arrowType(varType("a"), varType("a"))));
 * // "∀a::*. (a → a)"
 *
 * showType(lamType("F", arrowKind(starKind, starKind), varType("F")));
 * // "λF::(* → *). F"
 * ```
 *
 * @example Data structures + recursion
 * ```ts
 * import { showType, recordType, variantType, muType, tupleType, boundedForallType } from "system-f-omega";
 * import { varType, starKind, conType } from "system-f-omega";
 *
 * showType(recordType([["x", conType("Int")], ["y", conType("Bool")]]));
 * // "{x: Int, y: Bool}"
 *
 * showType(variantType([["Left", conType("Int")], ["Right", conType("Bool")]]));
 * // "<Left: Int | Right: Bool>"
 *
 * showType(muType("L", varType("L")));  // "μL.L"
 *
 * showType(boundedForallType("a", starKind, [{ trait: "Eq", type: varType("a") }], varType("a")));
 * // "∀a::* where Eq<a>. a"
 * ```
 *
 * @see {@link showTerm} Term printer (uses this)
 * @see {@link showKind} Kind printer (embedded)
 * @see {@link showPattern} Pattern printer
 * @see {@link getSpineArgs} Nominal app spine
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
  if ("mu" in t) {
    return `μ${t.mu.var}.${showType(t.mu.body)}`;
  }
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
 * Pretty-prints terms for debugging, REPL, and error messages.
 *
 * **Purpose**: Human-readable term strings with conventional notation:
 * - Lambdas: `λx:τ.body`
 * - Apps: `(callee arg)` (parenthesized).
 * - Polymorphism: `Λα::κ.body`, `term [τ]`.
 * - Data: `{x = 1, y = true}`, `<Left=42> as Either<Int,Bool>`.
 * - Traits: `dict Eq<Int> { eq = λx:Int.λy:Int.true }`, `d.eq`.
 * - Control: `match xs { Nil => 0 | Cons(x,_) => x }`.
 *
 * Recursive. Embeds `showType`/`showKind`/`showPattern`. Primary output for inference results.
 *
 * @param t - Term to print
 * @returns Pretty-printed string
 *
 * @example Core lambda calculus
 * ```ts
 * import { showTerm, lamTerm, appTerm, varTerm, conType } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * showTerm(id);  // "λx:Int.x"
 *
 * const app = appTerm(varTerm("f"), varTerm("x"));
 * showTerm(app);  // "(f x)"
 * ```
 *
 * @example Data + patterns
 * ```ts
 * import { showTerm, recordTerm, injectTerm, matchTerm, tupleTerm } from "system-f-omega";
 * import { conTerm, conType, varTerm, showPattern, varPattern, wildcardPattern, variantPattern, tuplePattern } from "system-f-omega";
 *
 * showTerm(recordTerm([["x", conTerm("1", conType("Int"))]]));  // "{x = 1}"
 *
 * const inj = injectTerm("Left", conTerm("42", conType("Int")), conType("Either"));
 * showTerm(inj);  // "<Left=42> as Either"
 *
 * const match = matchTerm(varTerm("xs"), [
 *   [varPattern("x"), conTerm("0", conType("Int"))],
 *   [variantPattern("Cons", tuplePattern([varPattern("hd"), wildcardPattern()])), varTerm("hd")]
 * ]);
 * showTerm(match);  // "match xs { x => 0 | Cons((hd, _)) => hd }"
 * ```
 *
 * @example Traits + polymorphism
 * ```ts
 * import { showTerm, tylamTerm, tyappTerm, dictTerm, traitMethodTerm, starKind } from "system-f-omega";
 * import { lamTerm, varTerm, conType, conTerm, showType } from "system-f-omega";
 *
 * const polyId = tylamTerm("a", starKind, lamTerm("x", conType("Int"), varTerm("x")));
 * showTerm(polyId);  // "Λa::*. λx:Int.x"
 *
 * showTerm(tyappTerm(polyId, conType("Bool")));  // "Λa::*. λx:Int.x [Bool]"
 *
 * const dict = dictTerm("Eq", conType("Int"), [["eq", conTerm("eqInt", conType("Bool"))]]);
 * showTerm(dict);  // "dict Eq<Int> { eq = eqInt }"
 *
 * showTerm(traitMethodTerm(dict, "eq"));  // "dict Eq<Int> { eq = eqInt }.eq"
 * ```
 *
 * @see {@link showType} Embedded types
 * @see {@link showKind} Kind annotations
 * @see {@link showPattern} Match cases
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
 * Pretty-prints patterns for debugging and error messages.
 *
 * **Purpose**: Human-readable string for patterns in `match` expressions.
 * Recursive: handles nested records/variants/tuples.
 *
 * Used in: `showTerm(match)`, error reporting (`missing_case`).
 *
 * @param p - Pattern to print
 * @returns String representation (e.g., `{x: y}`, `Cons(_)`)
 *
 * @example Simple patterns
 * ```ts
 * import { showPattern, varPattern, wildcardPattern, conPattern } from "system-f-omega";
 *
 * showPattern(varPattern("x"));     // "x"
 * showPattern(wildcardPattern());   // "_"
 * showPattern(conPattern("None", {}));  // "None"
 * ```
 *
 * @example Nested structures
 * ```ts
 * import { showPattern, recordPattern, variantPattern, tuplePattern } from "system-f-omega";
 * import { varPattern, wildcardPattern } from "system-f-omega";
 *
 * showPattern(recordPattern([["x", varPattern("a")], ["y", wildcardPattern()]]));
 * // "{x: a, y: _}"
 *
 * showPattern(variantPattern("Cons", tuplePattern([varPattern("hd"), wildcardPattern()]))));
 * // "Cons((hd, _))"
 *
 * showPattern(tuplePattern([varPattern("1"), varPattern("2")]));  // "(1, 2)"
 * ```
 *
 * @see {@link showType} Type pretty-printer
 * @see {@link showTerm} Term pretty-printer (uses this)
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
 * Pretty-prints trait definition (multi-line methods).
 *
 * **Purpose**: Debugs `TraitDef` bindings. Used in `showBinding`.
 *
 * @param t - Trait definition
 * @returns Formatted string
 *
 * @example Basic trait
 * ```ts
 * import { showTraitDef } from "system-f-omega";
 * import { starKind, arrowType, varType } from "system-f-omega";
 *
 * const eqTrait = {
 *   name: "Eq",
 *   type_param: "A",
 *   kind: starKind,
 *   methods: [["eq", arrowType(varType("A"), varType("Bool"))]]
 * };
 * console.log(showTraitDef(eqTrait));
 * // "TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * @example Multi-method
 * ```ts
 * import { showTraitDef } from "system-f-omega";
 * import { starKind, arrowType, varType } from "system-f-omega";
 *
 * const ordTrait = {
 *   name: "Ord",
 *   type_param: "A",
 *   kind: starKind,
 *   methods: [
 *     ["eq", arrowType(varType("A"), varType("Bool"))],
 *     ["lt", arrowType(varType("A"), varType("Bool"))]
 *   ]
 * };
 * console.log(showTraitDef(ordTrait));
 * // "TraitDef (Ord A = *\n  eq : (A → Bool)\n  lt : (A → Bool))"
 * ```
 *
 * @example HKT trait
 * ```ts
 * import { showTraitDef, arrowKind, starKind } from "system-f-omega";
 * import { varType, arrowType } from "system-f-omega";
 *
 * const functorTrait = {
 *   name: "Functor",
 *   type_param: "F",
 *   kind: arrowKind(starKind, starKind),
 *   methods: [["map", arrowType(varType("F"), varType("F"))]]
 * };
 * console.log(showTraitDef(functorTrait));
 * // "TraitDef (Functor F = (* → *)\n  map : (F → F))"
 * ```
 *
 * @internal Used by {@link showBinding}
 * @see {@link showBinding} Context printer
 */
export const showTraitDef = (t: TraitDef) => {
  return `TraitDef (${t.name} ${t.type_param} = ${showKind(t.kind)}\n${t.methods.map((y) => `  ${y[0]} : ${showType(y[1])}`).join("\n")})`;
};
