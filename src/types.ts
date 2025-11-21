/**
 * Trait bound in bounded polymorphism: `trait<type>`.
 *
 * **Purpose**: Constraint in `∀{Eq<Self>}. Self → Self`.
 * Used in `boundedForallType`, `traitLamTerm`, `checkTraitConstraints`.
 *
 * @typedef {Object} TraitConstraint
 * @property {string} trait - Trait name (`"Eq"`, `"Functor"`)
 * @property {Type} type - Type param (`Self`, `List<Int>`)
 *
 * @example Basic constraint
 * ```ts
 * import { type TraitConstraint } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const eqSelf: TraitConstraint = { trait: "Eq", type: varType("Self") };
 * console.log("Eq<Self>");  // Eq<Self>
 * ```
 *
 * @example Bounded forall
 * ```ts
 * import { boundedForallType, starKind, varType } from "system-f-omega";
 * import type { TraitConstraint } from "system-f-omega";
 *
 * const constraint: TraitConstraint = { trait: "Eq", type: varType("Self") };
 * const bounded = boundedForallType("Self", starKind, [constraint], varType("Self"));
 * console.log("∀Self where Eq<Self>. Self");  // ∀Self::* where Eq<Self>. Self
 * ```
 *
 * @example Trait lambda
 * ```ts
 * import { traitLamTerm, starKind } from "system-f-omega";
 * import type { TraitConstraint } from "system-f-omega";
 *
 * const constraint: TraitConstraint = { trait: "Eq", type: { var: "Self" } };
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [constraint], { var: "body" });
 * console.log("ΛSelf where Eq<Self>. body");  // ΛSelf::* where Eq<Self>. body
 * ```
 *
 * @example Resolution
 * ```ts
 * import { checkTraitConstraints } from "system-f-omega";
 * import type { TraitConstraint } from "system-f-omega";
 * // Assume state + impls
 *
 * const constraints: TraitConstraint[] = [{ trait: "Eq", type: conType("Int") }];
 * const dicts = checkTraitConstraints(state, constraints);
 * console.log("dicts:", dicts.ok.length);  // 1
 * ```
 *
 * @see {@link boundedForallType} Usage
 * @see {@link traitLamTerm} Term usage
 * @see {@link checkTraitConstraints} Resolution
 */
export type TraitConstraint = {
  trait: string;
  type: Type;
};

/**
 * Bounded universal quantifier `∀var::kind where constraints. body`.
 *
 * **Purpose**: Trait-bounded polymorphism: `∀Self::*. Eq<Self>. Self → Self`.
 *
 * @typedef {Object} BoundedForallType
 * @property {Object} bounded_forall
 * @property {string} bounded_forall.var - Bound variable (`"Self"`)
 * @property {Kind} bounded_forall.kind - Variable kind (`*`)
 * @property {TraitConstraint[]} bounded_forall.constraints - Trait bounds
 * @property {Type} bounded_forall.body - Body type
 *
 * @example Construction
 * ```ts
 * import { boundedForallType, starKind, varType, showType } from "system-f-omega";
 *
 * const eqSelf = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], varType("Self"));
 * console.log(showType(eqSelf));  // "∀Self::* where Eq<Self>. Self"
 * ```
 *
 * @example Trait lambda inference
 * ```ts
 * import { freshState, inferType, traitLamTerm, boundedForallType, starKind, varType, arrowType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Self")));
 * const result = inferType(state, traitLam);
 * console.log("inferred:", showType(result.ok));  // "∀Self::* where Eq<Self>. (Self → Self)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, checkType, traitLamTerm, boundedForallType, starKind, varType, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Self")));
 * const expected = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Self")));
 * const result = checkType(state, traitLam, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @example Trait app resolution
 * ```ts
 * import { freshState, instantiateWithTraits, boundedForallType, starKind, varType } from "system-f-omega";
 * // Assume Eq<Int> impls
 *
 * const state = freshState();
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: varType("a") }], varType("a"));
 * const result = instantiateWithTraits(state, bounded);
 * console.log("resolved:", "ok" in result && result.ok.dicts.length === 1);  // true
 * ```
 *
 * @see {@link boundedForallType} Constructor
 * @see {@link traitLamTerm} Term abstraction
 * @see {@link instantiateWithTraits} Resolution
 */
export type BoundedForallType = {
  bounded_forall: {
    var: string;
    kind: Kind;
    constraints: TraitConstraint[];
    body: Type;
  };
};

// Kinds (types of types)
/**
 * Concrete kind `*` (singleton for value-habiting types).
 *
 * **Purpose**: Terminal kind: `Int :: *`, `List<Int> :: *`.
 * Used in `addType`, forall/tylam binders.
 *
 * @typedef {Object} StarKind
 * @property {null} star - Concrete types
 *
 * @example Singleton usage
 * ```ts
 * import { starKind, showKind } from "system-f-omega";
 *
 * console.log("*:", showKind(starKind));  // "*"
 * ```
 *
 * @example addType primitive
 * ```ts
 * import { freshState, addType, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * console.log(showContext(state.ctx));  // "Type: Int = *"
 * ```
 *
 * @example Forall binder
 * ```ts
 * import { forallType, starKind, varType, showType } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, varType("a"));
 * console.log("∀a::*.:", showType(poly));  // "∀a::*. a"
 * ```
 *
 * @see {@link Kind} Union type
 * @see {@link arrowKind} HKT extension
 * @see {@link addType} Binds `:: *`
 */
export type StarKind = { star: null };

/**
 * Arrow kind `from → to` (higher-kinded type constructors).
 *
 * **Purpose**: HKT functions: `List :: * → *`.
 * Recursive: `* → (* → *)`.
 *
 * @typedef {Object} ArrowKind
 * @property {Object} arrow
 * @property {Kind} arrow.from - Domain kind
 * @property {Kind} arrow.to - Codomain kind
 *
 * @example Basic arrow
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const listKind = { arrow: { from: starKind, to: starKind } };
 * console.log("(*→*):", showKind(listKind));  // "(* → *)"
 * ```
 *
 * @example Nested HKT
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const nested = {
 *   arrow: {
 *     from: starKind,
 *     to: { arrow: { from: starKind, to: starKind } }
 *   }
 * };
 * console.log("nested:", showKind(nested));  // "(* → ((* → *) → *))"
 * ```
 *
 * @example addType HKT
 * ```ts
 * import { freshState, addType, arrowKind, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * console.log(showContext(state.ctx));  // "Type: List = (* → *)"
 * ```
 *
 * @see {@link Kind} Union type
 * @see {@link arrowKind} Constructor
 * @see {@link checkAppKind} Uses arrows
 */
export type ArrowKind = { arrow: { from: Kind; to: Kind } };

/**
 * Kinds classify types (type-level types).
 *
 * **Algebra**: `*` (terminal), `κ₁ → κ₂` (functions).
 * Used in binders (`∀a::κ`), HKTs (`List :: * → *`).
 *
 * @typedef {Object} StarKind
 * @property {null} star - Concrete types (`Int :: *`)
 *
 * @typedef {Object} ArrowKind
 * @property {Kind} from - Domain kind
 * @property {Kind} to - Codomain kind
 *
 * @typedef {StarKind | ArrowKind} Kind
 *
 * @example Star kind (concrete)
 * ```ts
 * import { starKind, showKind } from "system-f-omega";
 *
 * console.log("*:", showKind(starKind));  // "*"
 * ```
 *
 * @example Arrow kind (HKT)
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const listKind = arrowKind(starKind, starKind);  // * → *
 * console.log("(*→*):", showKind(listKind));  // "(* → *)"
 * ```
 *
 * @example Nested kinds
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const nested = arrowKind(starKind, arrowKind(starKind, starKind));  // * → (* → *)
 * console.log("nested:", showKind(nested));  // "(* → ((* → *) → *))"
 * ```
 *
 * @example Usage: addType
 * ```ts
 * import { freshState, addType, starKind, arrowKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;  // Int :: *
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;  // List :: * → *
 * console.log("added:", "ok" in state);  // true
 * ```
 *
 * @example Kind checking
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, arrowKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkKind(state, appType(conType("List"), conType("Int")));
 * console.log("List<Int> :: *:", showKind(result.ok));  // "*"
 * ```
 *
 * @see {@link starKind} Singleton
 * @see {@link arrowKind} Constructor
 * @see {@link checkKind} Inference
 * @see {@link kindsEqual} Equality
 */
export type Kind =
  | StarKind // * (base kind for proper types)
  | ArrowKind; // κ₁ → κ₂

/**
 * Variable pattern `var` (binds matched value).
 *
 * **Purpose**: Captures value as binding in match branches.

 * @typedef {Object} VarPattern
 * @property {string} var - Binding name
 *
 * @example Construction
 * ```ts
 * import { varPattern, showPattern } from "system-f-omega";
 *
 * console.log("x:", showPattern(varPattern("x")));  // "x"
 * ```
 *
 * @example Check/bind
 * ```ts
 * import { freshState, addType, checkPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const result = checkPattern(state, varPattern("x"), conType("Int"));
 * console.log("binds:", result.ok.length);  // 1
 * ```
 *
 * @see {@link checkPattern} Extracts binding
 * @see {@link matchTerm} Usage
 */
export type VarPattern = { var: string };

/**
 * Wildcard pattern `_` (matches anything, no binding).
 *
 * **Purpose**: Ignore values. Always exhaustive.

 * @typedef {Object} WildcardPattern
 * @property {null} wildcard - Ignore marker
 *
 * @example Construction
 * ```ts
 * import { wildcardPattern, showPattern } from "system-f-omega";
 *
 * console.log("_:", showPattern(wildcardPattern()));  // "_"
 * ```
 *
 * @example Check (empty bindings)
 * ```ts
 * import { freshState, addType, checkPattern, wildcardPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const result = checkPattern(state, wildcardPattern(), conType("Int"));
 * console.log("empty:", result.ok.length);  // 0
 * ```
 *
 * @see {@link checkPattern} No bindings
 * @see {@link checkExhaustive} Always ok
 */
export type WildcardPattern = { wildcard: null };

/**
 * Constructor pattern `con` (exact literal/tag match, no binding).
 *
 * **Purpose**: Matches constants/enum tags. Validates `type`.

 * @typedef {Object} ConPattern
 * @property {Object} con
 * @property {string} con.name - Constructor name
 * @property {Type} con.type - Expected type

 * @example Construction
 * ```ts
 * import { conPattern, conType, showPattern } from "system-f-omega";
 *
 * console.log("None:", showPattern(conPattern("None", conType("Unit"))));  // "None"
 * ```
 *
 * @example Check success
 * ```ts
 * import { freshState, addType, checkPattern, conPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const result = checkPattern(state, conPattern("true", conType("Bool")), conType("Bool"));
 * console.log("matches:", "ok" in result && result.ok.length === 0);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, conPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", tupleType([])]]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Bool")));
 * const match = matchTerm(scrut, [[conPattern("None", tupleType([])), conTerm("default", conType("Bool"))]]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Bool"
 * ```
 *
 * @example Failure: Type mismatch
 * ```ts
 * import { freshState, addType, checkPattern, conPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 *
 * const result = checkPattern(state, conPattern("true", conType("Int")), conType("Bool"));
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link checkPattern} Constant validation
 * @see {@link matchTerm} Case usage
 * @see {@link varPattern} Binding alternative
 */
export type ConPattern = { con: { name: string; type: Type } };

/**
 * Record pattern `{ l₁: p₁, l₂: p₂, ... }` (labeled destructuring).
 *
 * **Purpose**: Matches records field-by-field. Binds subpatterns to field slices.
 * Supports **width subtyping** (`{x:Int} <: {x:Int, y:Bool}`): extra fields ignored.
 * Recursive: flattens nested vars. Labels must match (order-independent).
 *
 * @typedef {Object} RecordPattern
 * @property {Array<[string, Pattern]>} record - Fields: `[[label, subpattern], ...]`
 *
 * @example Construction
 * ```ts
 * import { recordPattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = recordPattern([["x", varPattern("a")], ["y", varPattern("b")]]);
 * console.log("{x:a, y:b}:", showPattern(pat));  // "{x: a, y: b}"
 * ```
 *
 * @example Check/bind (flattens nested)
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", { record: [["nested", varPattern("b")]] }]  // Nested record pat
 * ]);
 * const ty = recordType([
 *   ["x", conType("Int")],
 *   ["y", recordType([["nested", conType("Bool")]])]
 * ]);
 * const result = checkPattern(state, pat, ty);
 * console.log("binds:", result.ok.length);  // 2: "a: Int", "b: Bool"
 * ```
 *
 * @example Width subtyping (extra fields OK)
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const narrowPat = recordPattern([["x", varPattern("a")]]);
 * const wideTy = recordType([
 *   ["x", conType("Int")],
 *   ["y", conType("Bool")]  // Extra field ignored
 * ]);
 * const result = checkPattern(state, narrowPat, wideTy);
 * console.log("width OK:", "ok" in result);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, inferType, matchTerm, recordPattern, varPattern, recordTerm, conTerm, recordType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const scrut = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const match = matchTerm(scrut, [
 *   [recordPattern([["x", varPattern("a")]), varTerm("a")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Missing field
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["missing", varPattern("a")]]);
 * const ty = recordType([["x", conType("Int")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("missing:", "missing_field" in result.err);  // true
 * ```
 *
 * @see {@link checkRecordPattern} Width-aware validation
 * @see {@link checkPattern} Extracts bindings
 * @see {@link matchTerm} Case usage
 * @see {@link recordType} Matching type
 * @see {@link recordPattern} Constructor
 */
export type RecordPattern = { record: [string, Pattern][] };

/**
 * Variant pattern `Label(pattern)` (tagged destructuring).
 *
 * **Purpose**: Matches enum/variant cases by label. Recurses on **payload pattern**.
 * - **Nominal**: Lookup enum def → instantiate field scheme → bind subpattern.
 * - **Structural**: Direct label match in `<L:τ | ...>` → bind payload.
 * - **Mu unfolding**: Handles recursive types automatically.
 * Supports nested patterns, meta-inference (infer enum from label).
 *
 * @typedef {Object} VariantPattern
 * @property {Object} variant
 * @property {string} variant.label - Variant label (`"Some"`, `"Cons"`)
 * @property {Pattern} variant.pattern - Payload subpattern
 *
 * @example Construction
 * ```ts
 * import { variantPattern, varPattern, showPattern } from "system-f-omega";
 *
 * console.log("Some(x):", showPattern(variantPattern("Some", varPattern("x"))));  // "Some(x)"
 * ```
 *
 * @example Nominal enum check (Option<Bool>)
 * ```ts
 * import { freshState, addType, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const result = checkPattern(state, variantPattern("Some", varPattern("x")), appType(conType("Option"), conType("Bool")));
 * console.log("binds:", result.ok.length === 1);  // true ("x: Bool")
 * ```
 *
 * @example Structural variant check
 * ```ts
 * import { freshState, checkPattern, variantPattern, varPattern, variantType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const pat = variantPattern("Left", varPattern("x"));
 * const ty = variantType([["Left", conType("Int")], ["Right", conType("Bool")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("structural OK:", "ok" in result);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, variantPattern, varPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 * const match = matchTerm(scrut, [
 *   [variantPattern("Some", varPattern("x")), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Invalid label
 * ```ts
 * import { freshState, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }]]).ok;
 *
 * const result = checkPattern(state, variantPattern("Some", varPattern("x")), appType(conType("Option"), conType("Int")));
 * console.log("invalid:", "invalid_variant_label" in result.err);  // true
 * ```
 *
 * @see {@link checkPattern} Nominal/structural dispatch
 * @see {@link matchTerm} Case usage
 * @see {@link injectTerm} Matching injection
 * @see {@link variantType} Structural type
 * @see {@link addEnum} Nominal enums
 */
export type VariantPattern = { variant: { label: string; pattern: Pattern } };

/**
 * Tuple pattern `(p₁, p₂, ...)` (unlabeled destructuring).
 *
 * **Purpose**: Matches tuples **element-by-element**. Binds subpatterns to tuple slices.
 * - **Exact length**: Must match tuple arity (no width subtyping).
 * - **Recursive**: Flattens bindings from nested patterns.
 * - **Zero-arity**: `()` matches unit `{ tuple: [] }`, no bindings.
 * - **Bottom**: `⊥` matches any tuple pattern (unreachable).
 *
 * @typedef {Object} TuplePattern
 * @property {Pattern[]} tuple - Element subpatterns
 *
 * @example Construction
 * ```ts
 * import { tuplePattern, varPattern, showPattern } from "system-f-omega";
 *
 * console.log("(a, b):", showPattern(tuplePattern([varPattern("a"), varPattern("b")])));  // "(a, b)"
 * console.log("unit():", showPattern(tuplePattern([])));  // "()"
 * ```
 *
 * @example Check/bind (flattens nested)
 * ```ts
 * import { freshState, addType, checkPattern, tuplePattern, varPattern, tupleType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = tuplePattern([
 *   varPattern("a"),
 *   tuplePattern([varPattern("nested")])  // Nested tuple pat
 * ]);
 * const ty = tupleType([
 *   conType("Int"),
 *   tupleType([conType("Bool")])
 * ]);
 * const result = checkPattern(state, pat, ty);
 * console.log("binds:", result.ok.length);  // 2: "a: Int", "nested: Bool"
 * ```
 *
 * @example Unit pattern (empty)
 * ```ts
 * import { freshState, checkPattern, tuplePattern, tupleType } from "system-f-omega";
 *
 * const state = freshState();
 * const unitPat = tuplePattern([]);
 * const unitTy = tupleType([]);
 * const result = checkPattern(state, unitPat, unitTy);
 * console.log("unit OK:", "ok" in result && result.ok.length === 0);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, inferType, matchTerm, tuplePattern, varPattern, tupleTerm, conTerm, tupleType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const scrut = tupleTerm([conTerm("1", conType("Int")), conTerm("2", conType("Int"))]);
 * const match = matchTerm(scrut, [
 *   [tuplePattern([varPattern("x"), varPattern("y")]), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Length mismatch
 * ```ts
 * import { freshState, addType, checkPattern, tuplePattern, varPattern, tupleType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const longPat = tuplePattern([varPattern("x"), varPattern("y")]);  // 2 elems
 * const shortTy = tupleType([conType("Int")]);  // 1 elem
 * const result = checkPattern(state, longPat, shortTy);
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link checkTuplePattern} Exact arity validation
 * @see {@link checkPattern} Extracts bindings
 * @see {@link matchTerm} Case usage
 * @see {@link tupleType} Matching type
 * @see {@link tupleTerm} Tuple values
 */
export type TuplePattern = { tuple: Pattern[] };

/**
 * Patterns for destructuring in `match` expressions (`Γ ⊢ pat : τ → bindings`).
 *
 * **Purpose**: **Bidirectional pattern matching**:
 * - **Synthesis** (`infer`): Extract bindings, infer scrutinee type from patterns.
 * - **Analysis** (`check`): Validate against scrutinee type → extend context.
 * - **Exhaustiveness**: `checkExhaustive` ensures total coverage (nominal/structural).
 * Supports: variables (bind), wildcards (ignore), constants (exact), records/variants/tuples (recursive).
 *
 * **Matching rules**:
 * | Pattern | Matches | Bindings |
 * |---------|---------|----------|
 * | `x` | Any `τ` | `x: τ` |
 * | `_` | Any | None |
 * | `C` | `C: τ` | None |
 * | `{l₁:p₁,...}` | `{l₁:τ₁,...}` (width) | Flattened sub-bindings |
 * | `L(p)` | `<L:τ \| ...>` / enum | Sub-bindings from `p: τ` |
 * | `(p₁,p₂,...)` | `(τ₁,τ₂,...)` (exact) | Flattened sub-bindings |
 *
 * @typedef {Union} Pattern
 * @type {VarPattern} `x` - Binds whole value
 * @type {WildcardPattern} `_` - Ignore (exhaustive)
 * @type {ConPattern} `true`/`None` - Exact constant/tag
 * @type {RecordPattern} `{x: p}` - Labeled destructuring (width)
 * @type {VariantPattern} `Cons(p)` - Tagged destructuring
 * @type {TuplePattern} `(p₁, p₂)` - Unlabeled destructuring (exact arity)
 *
 * @example Basic patterns
 * ```ts
 * import {
 *   varPattern, wildcardPattern, conPattern,
 *   recordPattern, variantPattern, tuplePattern,
 *   showPattern
 * } from "system-f-omega";
 *
 * console.log("x:", showPattern(varPattern("x")));              // "x"
 * console.log("_:", showPattern(wildcardPattern()));            // "_"
 * console.log("None:", showPattern(conPattern("None", {})));    // "None"
 * console.log("{x:a}:", showPattern(recordPattern([["x", varPattern("a")]])));  // "{x: a}"
 * console.log("Some(b):", showPattern(variantPattern("Some", varPattern("b")))); // "Some(b)"
 * console.log("(c,d):", showPattern(tuplePattern([varPattern("c"), varPattern("d")]))); // "(c, d)"
 * ```
 *
 * @example Pattern checking + bindings
 * ```ts
 * import { freshState, addType, checkPattern, varPattern, recordPattern, variantPattern, tuplePattern, recordType, variantType, tupleType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * // Complex nested pattern
 * const pat = recordPattern([
 *   ["fields", tuplePattern([
 *     variantPattern("Left", varPattern("l")),
 *     recordPattern([["nested", varPattern("n")]])
 *   ])]
 * ]);
 * const ty = recordType([
 *   ["fields", tupleType([
 *     variantType([["Left", conType("Int")]]),
 *     recordType([["nested", conType("Bool")]])
 *   ])]
 * ]);
 * const result = checkPattern(state, pat, ty);
 * console.log("binds:", result.ok.length);  // 2: "l: Int", "n: Bool"
 * ```
 *
 * @example Match inference + exhaustiveness
 * ```ts
 * import { freshState, addType, addEnum, inferType, checkExhaustive, matchTerm, variantPattern, varPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * // Full match
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 * const patterns = [
 *   variantPattern("None", varPattern("_")),
 *   variantPattern("Some", varPattern("x"))
 * ];
 * const exhaustive = checkExhaustive(state, patterns, appType(conType("Option"), conType("Int")));
 * console.log("exhaustive:", "ok" in exhaustive);  // true
 *
 * const match = matchTerm(scrut, patterns.map((p, i) => [p, conTerm(i.toString(), conType("Int"))]));
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure cases
 * ```ts
 * import { freshState, addType, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }]]).ok;
 *
 * // Invalid variant label
 * const result1 = checkPattern(state, variantPattern("Some", varPattern("x")), appType(conType("Option"), conType("Int")));
 * console.log("invalid label:", "invalid_variant_label" in result1.err);  // true
 *
 * // Record on non-record
 * const result2 = checkPattern(state, recordPattern([["x", varPattern("a")]]), conType("Int"));
 * console.log("not record:", "not_a_record" in result2.err);  // true
 * ```
 *
 * @see {@link checkPattern} Core dispatcher (infer/check + bindings)
 * @see {@link checkExhaustive} Coverage checking (nominal/structural)
 * @see {@link patternBindings} Placeholder extraction
 * @see {@link matchTerm} Full match expression
 * @see {@link inferMatchType} Match inference
 * @see {@link showPattern} Pretty-printer
 */
export type Pattern =
  | VarPattern // x - bind variable
  | WildcardPattern // _ - match anything
  | ConPattern // literal constant
  | RecordPattern // { l1: p1, l2: p2 }
  | VariantPattern // Label(pattern)
  | TuplePattern; // #(...patterns)

// Types
/**
 * Variable type `α` (type variable).
 *
 * **Purpose**: **Free/bound type parameters**:
 * - **Free**: Unknowns in polytypes (`a → b`), solved by unification.
 * - **Bound**: Shadowed in `∀α.τ`, `λα.τ`, `μα.τ` (alpha-renaming safe).
 * Used in polymorphism, HKTs (`List<a>`), records (`{x: a}`).
 *
 * @typedef {Object} VarType
 * @property {string} var - Variable name (`"a"`, `"Self"`, `"F"`)
 *
 * @example Construction
 * ```ts
 * import { varType, showType } from "system-f-omega";
 *
 * console.log("a:", showType(varType("a")));     // "a"
 * console.log("Self:", showType(varType("Self"))); // "Self"
 * ```
 *
 * @example Polymorphism (bound in forall)
 * ```ts
 * import { forallType, arrowType, varType, starKind, showType } from "system-f-omega";
 *
 * const polyId = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * console.log("∀a.a→a:", showType(polyId));  // "∀a::*. (a → a)"
 * ```
 *
 * @example HKT usage (free in app)
 * ```ts
 * import { appType, conType, varType, showType } from "system-f-omega";
 *
 * const listA = appType(conType("List"), varType("a"));
 * console.log("List<a>:", showType(listA));  // "List<a>"
 * ```
 *
 * @example Inference unification (solved)
 * ```ts
 * import { freshState, inferType, lamTerm, varTerm, unifyTypes, varType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const idA = lamTerm("x", varType("a"), varTerm("x"));
 * const result = inferType(state, idA);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)" (a := Int)
 * ```
 *
 * @see {@link varType} Constructor
 * @see {@link forallType} Bound usage
 * @see {@link unifyTypes} Solves free vars
 * @see {@link alphaRename} Binder safety
 * @see {@link collectTypeVars} Free var collection
 */
export type VarType = { var: string };

/**
 * Function type `(τ₁ → τ₂)` (arrow type).
 *
 * **Purpose**: **Core function type** for lambdas/trait methods:
 * - **Bidirectional**: Domain check (`⇐ τ₁`), body infer/check codomain.
 * - **Bottom domains**: `⊥ → τ` subtypes any `σ → τ` (unreachable args).
 * - **Higher-order**: Nested arrows `(a → b) → c`.
 * Unifies structurally: contravariant domain, covariant codomain.
 *
 * @typedef {Object} ArrowType
 * @property {Object} arrow
 * @property {Type} arrow.from - Domain/argument type (`τ₁`)
 * @property {Type} arrow.to - Codomain/result type (`τ₂`)
 *
 * @example Construction
 * ```ts
 * import { arrowType, conType, varType, showType } from "system-f-omega";
 *
 * console.log("Int→Bool:", showType(arrowType(conType("Int"), conType("Bool"))));  // "(Int → Bool)"
 * console.log("a→b:", showType(arrowType(varType("a"), varType("b"))));          // "(a → b)"
 * ```
 *
 * @example Lambda inference
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, arrowType, conType, varType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", varType("a"), varTerm("x"));
 * const result = inferType(state, id);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Checking (domain unify)
 * ```ts
 * import { freshState, addType, checkType, lamTerm, varTerm, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * const result = checkType(state, id, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int → Bool)"
 * ```
 *
 * @example Bottom domain subtyping
 * ```ts
 * import { freshState, isAssignableTo, neverType, arrowType, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const bottomFn = arrowType(neverType, conType("Int"));  // ⊥ → Int
 * const anyFn = arrowType(conType("Bool"), conType("Int"));  // Bool → Int
 * console.log("⊥→Int <: Bool→Int:", isAssignableTo(state, bottomFn, anyFn));  // true
 * ```
 *
 * @example Unification (structural)
 * ```ts
 * import { freshState, unifyTypes, arrowType, varType, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, arrowType(varType("a"), varType("b")), arrowType(conType("Int"), conType("Bool")), worklist, subst);
 * console.log("unified a=Int, b=Bool");
 * ```
 *
 * @see {@link arrowType} Constructor
 * @see {@link inferLamType} Lambda rule
 * @see {@link checkType} Domain checking
 * @see {@link unifyArrowTypes} Structural unification
 * @see {@link subsumes} Bottom subtyping
 * @see {@link showType} Parenthesized printing
 */
export type ArrowType = { arrow: { from: Type; to: Type } };

/**
 * Universal quantifier `∀var::kind. body` (polymorphic type).
 *
 * **Purpose**: **Parametric polymorphism**:
 * - **Bound vars**: `var` shadowed in `body` (alpha-equivalence).
 * - **Instantiation**: `instantiateType` → fresh metas (`?N`) for subsumption/unification.
 * - **Inference**: `tylamTerm` synthesizes `∀α::κ. τ`.
 * - **Checking**: Matches `tylam` structure + kinds.
 * Supports HKT polymorphism (`∀F::(*→*). F<a>`).
 *
 * @typedef {Object} ForallType
 * @property {Object} forall
 * @property {string} forall.var - Bound variable (`"a"`, `"Self"`)
 * @property {Kind} forall.kind - Variable kind (`*`, `*→*`)
 * @property {Type} forall.body - Body type (may contain `var`)
 *
 * @example Construction
 * ```ts
 * import { forallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * const polyId = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * console.log("∀a.a→a:", showType(polyId));  // "∀a::*. (a → a)"
 * ```
 *
 * @example Tylam inference
 * ```ts
 * import { freshState, inferType, tylamTerm, lamTerm, varTerm, varType, starKind, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const result = inferType(state, polyId);
 * console.log("inferred:", showType(result.ok));  // "∀a::*. (a → a)"
 * ```
 *
 * @example Checking (tylam)
 * ```ts
 * import { freshState, checkType, tylamTerm, lamTerm, varTerm, varType, forallType, arrowType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const result = checkType(state, polyId, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @example Instantiation (subsumption)
 * ```ts
 * import { freshState, instantiateType, forallType, arrowType, varType, starKind, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const mono = instantiateType(state, poly);
 * console.log("instantiated:", showType(mono));  // "(?0 → ?0)"
 * ```
 *
 * @example HKT polymorphism
 * ```ts
 * import { forallType, arrowKind, starKind, appType, conType, varType, showType } from "system-f-omega";
 *
 * const listPoly = forallType("F", arrowKind(starKind, starKind), appType(varType("F"), conType("Int")));
 * console.log("∀F.F<Int>:", showType(listPoly));  // "∀F::(* → *). F<Int>"
 * ```
 *
 * @see {@link forallType} Constructor
 * @see {@link tylamTerm} Term abstraction
 * @see {@link tyappTerm} Term application
 * @see {@link instantiateType} Skolemization
 * @see {@link subsumes} Polymorphic subtyping
 * @see {@link typesEqual} Alpha-equivalence
 */
export type ForallType = { forall: { var: string; kind: Kind; body: Type } };

/**
 * Type application `func arg` (left-associative: `F A B = ((F A) B)`).
 *
 * **Purpose**: **Higher-kinded type application**:
 * - **Nominal types**: `Either<Int, Bool>` (spine: `Either<Int, Bool>`).
 * - **HKT saturation**: `List<Int>` requires `List :: * → *`.
 * - **Beta-reduction**: `(λt.τ) σ → τ[t↦σ]` (via `normalizeType`).
 * - **Spine extraction**: `getSpineArgs/Head` for pretty-print/unification.
 * Unifies pairwise on same head (`Either<a,b> ~ Either<Int,Bool>`).
 *
 * @typedef {Object} AppType
 * @property {Object} app
 * @property {Type} app.func - Function/constructor (`List`, `Either`)
 * @property {Type} app.arg - Argument (`Int`, `Bool`)
 *
 * @example Construction (nested spine)
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log("List<Int>:", showType(listInt));  // "List<Int>"
 *
 * const eitherIntBool = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("Either<Int,Bool>:", showType(eitherIntBool));  // "Either<Int, Bool>"
 * ```
 *
 * @example Kind checking (HKT)
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, arrowKind, showKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkKind(state, appType(conType("List"), conType("Int")));
 * console.log("List<Int> :: *:", showKind(result.ok));  // "*"
 * ```
 *
 * @example Normalization (beta-reduce)
 * ```ts
 * import { freshState, normalizeType, lamType, appType, varType, starKind, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const idLam = lamType("t", starKind, varType("t"));
 * const idInt = appType(idLam, conType("Int"));
 * const norm = normalizeType(state, idInt);
 * console.log("β-reduced:", showType(norm));  // "Int"
 * ```
 *
 * @example Unification (spine pairwise)
 * ```ts
 * import { freshState, addType, unifyTypes, appType, conType, varType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Either", starKind).ok;
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const left = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * const right = appType(appType(conType("Either"), varType("a")), varType("b"));
 * const worklist: Constraint[] = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, left, right, worklist, subst);
 * console.log("a=Int, b=Bool");  // Unifies spine args
 * ```
 *
 * @example Spine extraction
 * ```ts
 * import { getSpineArgs, getSpineHead, appType, conType, showType } from "system-f-omega";
 *
 * const either = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("head:", showType(getSpineHead(either)));  // "Either"
 * console.log("args:", getSpineArgs(either).map(showType));  // ["Int", "Bool"]
 * ```
 *
 * @see {@link appType} Constructor
 * @see {@link getSpineArgs} Deconstructs spine
 * @see {@link getSpineHead} Extracts head
 * @see {@link checkAppKind} Kind checking
 * @see {@link normalizeType} β-reduction
 * @see {@link unifyTypes} Spine unification
 * @see {@link showType} Spine-aware printing
 */
export type AppType = { app: { func: Type; arg: Type } };

/**
 * Type lambda `λα::kind. body` (higher-kinded type constructor).
 *
 * **Purpose**: **Type-level abstraction** for HKT definitions:
 * - **Kind inference**: `λα::κ.τ :: κ → κ'`.
 * - **Beta-reduction**: `(λα.τ) σ → τ[α↦σ]` (via `normalizeType`).
 * - **Unification**: Structural (alpha-equivalence on binders).
 * Used for explicit HKTs: `List = λα::*. List<α>` (but often bound directly).
 *
 * @typedef {Object} LamType
 * @property {Object} lam
 * @property {string} lam.var - Bound variable (`"α"`, `"F"`)
 * @property {Kind} lam.kind - Parameter kind (`*`, `*→*`)
 * @property {Type} lam.body - Body (may contain `var`)
 *
 * @example Construction
 * ```ts
 * import { lamType, varType, starKind, showType } from "system-f-omega";
 *
 * const idLam = lamType("α", starKind, varType("α"));
 * console.log("λα.α:", showType(idLam));  // "λα::*. α"
 * ```
 *
 * @example Nested HKT kind
 * ```ts
 * import { lamType, arrowKind, starKind, varType, showType } from "system-f-omega";
 *
 * // λF::(*→*). λa::*. F<a>  ::  (* → *) → * → *
 * const mapLam = lamType("F", arrowKind(starKind, starKind),
 *   lamType("a", starKind, appType(varType("F"), varType("a"))));
 * console.log("nested:", showType(mapLam));  // "λF::(* → *). λa::*. F a"
 * ```
 *
 * @example Kind checking
 * ```ts
 * import { freshState, checkKind, lamType, arrowKind, starKind, varType, showKind } from "system-f-omega";
 *
 * const state = freshState();
 * const listLam = lamType("t", starKind, varType("List"));  // Dummy body
 * const result = checkKind(state, listLam);
 * console.log("λα.τ :: *→*:", showKind(result.ok));  // "(* → *)"
 * ```
 *
 * @example Beta-reduction (normalize)
 * ```ts
 * import { freshState, normalizeType, lamType, appType, varType, starKind, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const idLam = lamType("α", starKind, varType("α"));
 * const idInt = appType(idLam, conType("Int"));
 * const reduced = normalizeType(state, idInt);
 * console.log("β-reduced:", showType(reduced));  // "Int"
 * ```
 *
 * @see {@link lamType} Constructor
 * @see {@link appType} Application
 * @see {@link normalizeType} β-reduction
 * @see {@link checkLamKind} Kind rule
 * @see {@link unifyLamTypes} Unification
 * @see {@link arrowKind} Result kind
 */
export type LamType = { lam: { var: string; kind: Kind; body: Type } };

/**
 * Concrete type constructor `Con` (primitive/HKT head).
 *
 * **Purpose**: **Type constants** bound in context:
 * - **Primitives**: `Int :: *`, `Bool :: *`.
 * - **HKT heads**: `List :: * → *`, `Either :: * → * → *`.
 * - **Nominal enums**: `Option<T>` expands to variants/μ.
 * - **Aliases**: Expand parametrically (`Id<Int> → Int`).
 * Used as app spine heads, unification anchors.
 *
 * @typedef {Object} ConType
 * @property {string} con - Constructor name (`"Int"`, `"List"`, `"Either"`)
 *
 * @example Construction
 * ```ts
 * import { conType, showType } from "system-f-omega";
 *
 * console.log("Int:", showType(conType("Int")));      // "Int"
 * console.log("List:", showType(conType("List")));    // "List"
 * ```
 *
 * @example Context binding (addType)
 * ```ts
 * import { freshState, addType, starKind, arrowKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;                    // Primitive
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok; // HKT
 * console.log(showContext(state.ctx));
 * // "Type: Int = *\nType: List = (* → *)"
 * ```
 *
 * @example Kind checking
 * ```ts
 * import { freshState, addType, checkKind, conType, starKind, arrowKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 *
 * const listKind = checkKind(state, conType("List"));
 * console.log("List :: (*→*):", "ok" in listKind);  // true
 * ```
 *
 * @example HKT application
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, arrowKind, showKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * state = addType(state, "Int", starKind).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const kind = checkKind(state, listInt);
 * console.log("List<Int> :: *:", showKind(kind.ok));  // "*"
 * ```
 *
 * @example Alias expansion
 * ```ts
 * import { freshState, addType, addTypeAlias, normalizeType, appType, conType, varType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const idInt = appType(conType("Id"), conType("Int"));
 * const expanded = normalizeType(state, idInt);
 * console.log("Id<Int> → Int:", showType(expanded));  // "Int"
 * ```
 *
 * @see {@link conType} Constructor
 * @see {@link addType} Binds constructors
 * @see {@link checkConKind} Lookup/alias expansion
 * @see {@link appType} HKT saturation
 * @see {@link normalizeType} Enum/alias expansion
 * @see {@link getSpineHead} Spine extraction
 */
export type ConType = { con: string };

/**
 * Record type `{ l₁: τ₁, l₂: τ₂, ... }` (structural product).
 *
 * **Purpose**: **Labeled products** with **width subtyping**:
 * - `{x:Int} <: {x:Int, y:Bool}` (extra fields OK).
 * - **Row polymorphism** implicit (unification handles widths).
 * - Fields `:: *` (checked via `checkRecordKind`).
 * Used in records, projection, pattern matching.
 *
 * **Subtyping**: Width (permutation-insensitive, labels exact match for checking).
 *
 * @typedef {Object} RecordType
 * @property {Array<[string, Type]>} record - Fields: `[[label, type], ...]` (sorted for equality)
 *
 * @example Construction
 * ```ts
 * import { recordType, conType, showType } from "system-f-omega";
 *
 * const person = recordType([
 *   ["name", conType("String")],
 *   ["age", conType("Int")]
 * ]);
 * console.log("{name:String, age:Int}:", showType(person));  // "{name: String, age: Int}"
 * ```
 *
 * @example Inference (recordTerm)
 * ```ts
 * import { freshState, addType, inferType, recordTerm, conTerm, recordType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "String", starKind).ok;
 *
 * const recVal = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("hello", conType("String"))]
 * ]);
 * const result = inferType(state, recVal);
 * console.log("inferred:", showType(result.ok));  // "{x: Int, y: String}"
 * ```
 *
 * @example Width subtyping
 * ```ts
 * import { freshState, isAssignableTo, recordType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const narrow = recordType([["x", conType("Int")]]);
 * const wide = recordType([
 *   ["x", conType("Int")],
 *   ["y", conType("Bool")]
 * ]);
 * console.log("narrow <: wide:", isAssignableTo(state, narrow, wide));  // true
 * ```
 *
 * @example Projection
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, recordType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const projX = projectTerm(rec, "x");
 * const result = inferType(state, projX);
 * console.log("x:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link recordType} Constructor
 * @see {@link inferRecordType} Inference
 * @see {@link projectTerm} Field access
 * @see {@link checkRecordKind} Fields `:: *`
 * @see {@link unifyRecordTypes} Width unification
 * @see {@link recordPattern} Pattern matching
 */
export type RecordType = { record: [string, Type][] };

/**
 * Variant type `< l₁: τ₁ | l₂: τ₂ | ... >` (disjoint union/sum).
 *
 * **Purpose**: **Tagged sums** for enums/pattern matching:
 * - **Structural**: Direct label match (order-insensitive).
 * - **Empty**: `<>` normalizes to `⊥` (uninhabited).
 * - **Fields `:: *`** (checked via `checkVariantKind`).
 * - **Enum expansion**: Non-recursive enums → variants (recursive → `μ`).
 * Used in injectTerm, matchTerm, normalization.
 *
 * **Unification**: Labels must match exactly (no width).
 *
 * @typedef {Object} VariantType
 * @property {Array<[string, Type]>} variant - Cases: `[[label, type], ...]` (sorted for equality)
 *
 * @example Construction
 * ```ts
 * import { variantType, conType, showType } from "system-f-omega";
 *
 * const either = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("String")]
 * ]);
 * console.log("<Left:Int | Right:String>:", showType(either));  // "<Left: Int | Right: String>"
 * ```
 *
 * @example Empty variant (bottom)
 * ```ts
 * import { freshState, isBottom, variantType } from "system-f-omega";
 *
 * const state = freshState();
 * const empty = variantType([]);
 * console.log("empty ⊥:", isBottom(state, empty));  // true
 * ```
 *
 * @example Injection inference
 * ```ts
 * import { freshState, inferType, injectTerm, conTerm, variantType, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const leftVal = injectTerm("Left", conTerm("42", conType("Int")), variantType([["Left", conType("Int")]]));
 * const result = inferType(state, leftVal);
 * console.log("inferred:", showType(result.ok));  // "<Left: Int | ...>"
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, inferType, matchTerm, variantPattern, varPattern, injectTerm, conTerm, variantType, conType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const scrut = injectTerm("Left", conTerm("42", conType("Int")), variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("String")]
 * ]));
 * const match = matchTerm(scrut, [
 *   [variantPattern("Left", varPattern("x")), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link variantType} Constructor
 * @see {@link injectTerm} Variant values
 * @see {@link matchTerm} Pattern matching
 * @see {@link checkVariantKind} Cases `:: *`
 * @see {@link unifyVariants} Label unification
 * @see {@link variantPattern} Destructuring
 * @see {@link normalizeType} Enum expansion
 */
export type VariantType = { variant: [string, Type][] };

/**
 * Recursive mu type `μvar. body` (equi-recursive fixed-point).
 *
 * **Purpose**: **Recursive types** (lists, trees):
 * - **Unfolding**: `substituteType(var, μ, body)` → body with self-replacement.
 * - **Cycle-safe**: `normalizeType` guards `seen` → unchanged/⊥.
 * - **Enum expansion**: Recursive enums → `μX.<Nil | Cons(T, X<a>)>` (via `addEnum(recursive=true)`).
 * - **Typing**: `fold/unfold` pack/unpack (bidirectional).
 * Kind `*` if `body::*` in extended ctx (`var :: *`).
 *
 * **Equi-recursion**: `μX.τ[X] ≡ τ[μX.τ/X]` (no iso required).
 *
 * @typedef {Object} MuType
 * @property {Object} mu
 * @property {string} mu.var - Recursive variable (`"L"`, `"X0"`)
 * @property {Type} mu.body - Body (contains `var` references)
 *
 * @example Construction
 * ```ts
 * import { muType, varType, showType } from "system-f-omega";
 *
 * const degenerate = muType("X", varType("X"));
 * console.log("μX.X:", showType(degenerate));  // "μX.X"
 * ```
 *
 * @example Recursive list
 * ```ts
 * import { muType, tupleType, conType, varType, showType } from "system-f-omega";
 *
 * const listMu = muType("L", tupleType([conType("Int"), varType("L")]));
 * console.log("μL.(Int,L):", showType(listMu));  // "μL.(Int, L)"
 * ```
 *
 * @example Enum expansion (recursive → μ)
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;  // recursive=true
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const expanded = normalizeType(state, listInt);
 * console.log("List<Int> → μ:", showType(expanded));  // "μX0.<Nil: ⊥ | Cons: (Int, X0)>"
 * ```
 *
 * @example Fold/unfold typing
 * ```ts
 * import { freshState, addEnum, inferType, foldTerm, unfoldTerm, injectTerm, appType, conType, starKind, tupleType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), { var: "T" })])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const resultFold = inferType(state, folded);
 * console.log("fold:", showType(resultFold.ok));  // "List<Int>"
 *
 * const unfolded = unfoldTerm(folded);
 * const resultUnfold = inferType(state, unfolded);
 * console.log("unfold:", showType(resultUnfold.ok));  // "(⊥, List<Int>)"
 * ```
 *
 * @see {@link muType} Constructor
 * @see {@link normalizeType} Cycle-safe unfolding
 * @see {@link foldTerm} Packing
 * @see {@link unfoldTerm} Unpacking
 * @see {@link addEnum} Recursive expansion
 * @see {@link checkMuKind} Kind checking
 * @see {@link unifyMuTypes} Equi-recursive unification
 */
export type MuType = { mu: { var: string; body: Type } };

/**
 * Tuple type `(τ₁, τ₂, ...)` (unlabeled product, exact arity).
 *
 * **Purpose**: **Unlabeled sequences**:
 * - **Exact arity**: No width subtyping (unlike records).
 * - **Zero-arity**: `()` = unit (sole inhabitant: `{tuple:[]}`).
 * - **Elements `:: *`** (via `checkTupleKind`).
 * Used in tuples, projection, pattern matching, enum fields.
 *
 * @typedef {Object} TupleType
 * @property {Type[]} tuple - Element types
 *
 * @example Construction
 * ```ts
 * import { tupleType, conType, showType } from "system-f-omega";
 *
 * console.log("unit ():", showType(tupleType([])));                    // "()"
 * console.log("pair (Int,Bool):", showType(tupleType([conType("Int"), conType("Bool")])));  // "(Int, Bool)"
 * ```
 *
 * @example Nested tuples
 * ```ts
 * import { tupleType, conType, showType } from "system-f-omega";
 *
 * const nested = tupleType([
 *   conType("Int"),
 *   tupleType([conType("Bool"), conType("String")])
 * ]);
 * console.log("nested:", showType(nested));  // "(Int, (Bool, String))"
 * ```
 *
 * @example Inference (tupleTerm)
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, conTerm, tupleType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tupVal = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * const result = inferType(state, tupVal);
 * console.log("inferred:", showType(result.ok));  // "(Int, Bool)"
 * ```
 *
 * @example Projection
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, tupleProjectTerm, conTerm, tupleType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * const proj0 = tupleProjectTerm(tup, 0);
 * const result = inferType(state, proj0);
 * console.log("proj[0]:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link tupleType} Constructor
 * @see {@link tupleTerm} Values
 * @see {@link tupleProjectTerm} Access
 * @see {@link inferTupleType} Inference
 * @see {@link checkTupleKind} Elements `:: *`
 * @see {@link unifyTupleTypes} Exact unification
 * @see {@link tuplePattern} Destructuring
 */
export type TupleType = { tuple: Type[] };

/**
 * Never type `⊥` (bottom/uninhabited type).
 *
 * **Purpose**: **Empty type** (no values):
 * - **Subtyping**: `⊥ <: τ` **always** (if `τ :: *`).
 * - **Unification**: `⊥ ~ τ` succeeds (`τ :: *`), but `τ ~ ⊥` only if `τ = ⊥`.
 * - **Normalization**: Empty variants `<>` → `⊥`, cycle fallback.
 * - **Exhaustiveness**: Unreachable branches → `⊥`.
 * - **Functions**: `⊥ → τ` subtypes any `σ → τ` (unreachable args).
 *
 * **Key invariant**: `isBottom(⊥) = true`, subtypes **everything**.
 *
 * @typedef {Object} NeverType
 * @property {null} never - Bottom marker
 *
 * @example Construction
 * ```ts
 * import { neverType, showType } from "system-f-omega";
 *
 * console.log("⊥:", showType(neverType));  // "⊥"
 * ```
 *
 * @example Subtyping (⊥ <: anything)
 * ```ts
 * import { freshState, isAssignableTo, neverType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * console.log("⊥ <: Int:", isAssignableTo(state, neverType, conType("Int")));  // true
 * console.log("⊥ <: Bool:", isAssignableTo(state, neverType, conType("Bool"))); // true
 * ```
 *
 * @example Unification (asymmetric)
 * ```ts
 * import { freshState, unifyTypes, neverType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map<string, Type>();
 * const worklist: Constraint[] = [];
 *
 * // ⊥ ~ Int succeeds
 * console.log("⊥ ~ Int:", "ok" in unifyTypes(state, neverType, conType("Int"), worklist, subst));
 * // Int ~ ⊥ fails
 * console.log("Int ~ ⊥:", "type_mismatch" in unifyTypes(state, conType("Int"), neverType, [], new Map()).err);
 * ```
 *
 * @example Normalization (empty variant → ⊥)
 * ```ts
 * import { freshState, normalizeType, variantType, isBottom } from "system-f-omega";
 *
 * const state = freshState();
 * const emptyVar = variantType([]);
 * const norm = normalizeType(state, emptyVar);
 * console.log("empty → ⊥:", isBottom(state, norm));  // true
 * ```
 *
 * @example Bottom-domain functions
 * ```ts
 * import { freshState, isAssignableTo, neverType, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const bottomFn = arrowType(neverType, conType("Int"));  // ⊥ → Int
 * const anyFn = arrowType(conType("Bool"), conType("Int"));  // Bool → Int
 * console.log("⊥→Int <: Bool→Int:", isAssignableTo(state, bottomFn, anyFn));  // true
 * ```
 *
 * @see {@link neverType} Singleton
 * @see {@link isBottom} Detection
 * @see {@link isAssignableTo} Subtyping (⊥ <: τ)
 * @see {@link subsumes} Unification fallback
 * @see {@link normalizeType} Empty variant/cycle → ⊥
 * @see {@link variantType} `[]` → ⊥
 */
export type NeverType = { never: null };

/**
 * Existential meta-variable `?N` (unification variable).
 *
 * **Purpose**: **Inference unknowns** (HM-style):
 * - **Fresh**: `freshMetaVar(env, kind?)` → sequential `?0`, `?1`... with tracked `kind`.
 * - **Solving**: `solveMetaVar` binds `?N := τ` (occurs-checked).
 * - **Unification**: Flex-rigid (`?N ~ τ` → bind), rigid-flex (swap).
 * - **Application**: Follow chains via `applySubstitution`/`normalizeType`.
 * Central to **algorithm W**: polymorphism instantiation, app checking.
 *
 * **Lifecycle**:
 * 1. `freshMetaVar` → unbound `?N :: κ`.
 * 2. Unification → `solveMetaVar` (global `meta.solutions`).
 * 3. `applySubstitution` → resolve.
 * 4. `getUnboundMetas` → generalize.
 *
 * @typedef {Object} MetaType
 * @property {string} evar - Meta name (`"?0"`, `" ?42"`)
 *
 * @example Fresh meta-var
 * ```ts
 * import { freshState, freshMetaVar, showType } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta, starKind);
 * console.log("?0:", showType(meta));  // "?0"
 * console.log("kind tracked:", state.meta.kinds.has("?0"));  // true
 * ```
 *
 * @example Solving (unification)
 * ```ts
 * import { freshState, freshMetaVar, solveMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const result = solveMetaVar(state, meta.evar, conType("Int"));
 * console.log("solved:", "ok" in result);  // true
 * console.log("solution:", state.meta.solutions.has(meta.evar));  // true
 * ```
 *
 * @example Flex-rigid unification
 * ```ts
 * import { freshState, freshMetaVar, unifyTypes, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const worklist: Constraint[] = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, meta, arrowType(conType("Int"), conType("Bool")), worklist, subst);
 * console.log("bound ?0 → (Int→Bool)");
 * ```
 *
 * @example Resolution (applySubstitution)
 * ```ts
 * import { freshState, freshMetaVar, applySubstitution, conType, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * state.meta.solutions.set(meta.evar, arrowType(conType("Int"), conType("Bool")));
 * const resolved = applySubstitution(state, new Map(), meta);
 * console.log("resolved:", showType(resolved));  // "(Int → Bool)"
 * ```
 *
 * @example Cycle rejection (occurs check)
 * ```ts
 * import { freshState, freshMetaVar, occursCheckEvar, arrowType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const cyclic = arrowType(meta, varType("Int"));  // ?0 → Int
 * console.log("cycle:", occursCheckEvar(state.meta, meta.evar, cyclic));  // true (reject)
 * ```
 *
 * @see {@link freshMetaVar} Creation
 * @see {@link solveMetaVar} Binding
 * @see {@link unifyTypes} Flex-rigid dispatch
 * @see {@link occursCheckEvar} Cycle detection
 * @see {@link applySubstitution} Resolution
 * @see {@link getUnboundMetas} Generalization
 * @see {@link MetaEnv} Tracking (kinds/solutions)
 */
export type MetaType = { evar: string };

/**
 * Core type language: **System Fω + Records/Variants/μ/Traits**.
 *
 * **Purpose**: Statically typed λ-calculus with:
 * | Constructor | Syntax | Kind | Purpose |
 * |-------------|--------|------|---------|
 * | `MetaType` | `?N` | `κ` | Unification vars (inference) |
 * | `VarType` | `α` | `κ` | Free/bound vars |
 * | `ArrowType` | `τ₁ → τ₂` | `*` | Functions (bottom domains) |
 * | `ForallType` | `∀α::κ.τ` | `*` | Parametric polymorphism |
 * | `AppType` | `F τ` | `κ₂` | HKT application (spine) |
 * | `BoundedForallType` | `∀α::κ where C.τ` | `*` | Trait bounds |
 * | `LamType` | `λα::κ.τ` | `κ → κ'` | Type functions (HKTs) |
 * | `ConType` | `Int`/`List` | `κ` | Primitives/HKT heads/enums |
 * | `RecordType` | `{l:τ,...}` | `*` | Labeled products (width) |
 * | `VariantType` | `<l:τ \| ...>` | `*` | Tagged sums (enums) |
 * | `MuType` | `μα.τ` | `*` | Equi-recursive (lists/trees) |
 * | `TupleType` | `(τ₁,τ₂,...)` | `*` | Unlabeled products |
 * | `NeverType` | `⊥` | `*` | Bottom (uninhabited) |
 *
 * **Features**:
 * - **Bidirectional typing**: `inferType`/`checkType` → constraints → unification.
 * - **Kinds**: `*` (data), `κ₁ → κ₂` (HKTs) via `checkKind`.
 * - **Subtyping**: Width (records), `⊥ <: τ`, parametric (`subsumes`).
 * - **Traits**: Dictionary-passing (`checkTraitConstraints`).
 * - **Normalization**: Aliases/enums/β/μ (`normalizeType`).
 *
 * @typedef {Union} Type
 * @type {MetaType} `?N` - Existential (unification)
 * @type {VarType} `α` - Type variable (free/bound)
 * @type {ArrowType} `τ₁ → τ₂` - Function type
 * @type {ForallType} `∀α::κ.τ` - Universal (polymorphism)
 * @type {AppType} `F τ` - Type application (HKT/nominal)
 * @type {BoundedForallType} `∀α where C.τ` - Trait-bounded
 * @type {LamType} `λα::κ.τ` - Type lambda (HKT constructor)
 * @type {ConType} `Int`/`List` - Concrete constructors
 * @type {RecordType} `{l:τ}` - Row-polymorphic records
 * @type {VariantType} `<l:τ \| ...>` - Disjoint unions
 * @type {MuType} `μα.τ` - Recursive types
 * @type {TupleType} `(τ₁,τ₂)` - Anonymous products
 * @type {NeverType} `⊥` - Bottom type
 *
 * @example Construction (core types)
 * ```ts
 * import {
 *   varType, arrowType, forallType, appType, lamType, conType,
 *   recordType, variantType, muType, tupleType, neverType,
 *   showType
 * } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * console.log("α:", showType(varType("a")));                    // "a"
 * console.log("→:", showType(arrowType(conType("Int"), conType("Bool")))); // "(Int → Bool)"
 * console.log("∀:", showType(forallType("a", starKind, varType("a"))));    // "∀a::*. a"
 * console.log("app:", showType(appType(conType("List"), conType("Int")))); // "List<Int>"
 * console.log("λ:", showType(lamType("F", starKind, varType("F"))));       // "λF::*. F"
 * console.log("{ }:", showType(recordType([["x", conType("Int")]])));      // "{x: Int}"
 * console.log("< \| >:", showType(variantType([["L", conType("Int")]]))); // "<L: Int>"
 * console.log("μ:", showType(muType("L", varType("L"))));                 // "μL.L"
 * console.log("():", showType(tupleType([])));                             // "()"
 * console.log("⊥:", showType(neverType));                                  // "⊥"
 * ```
 *
 * @example Inference (λ + poly + data + traits)
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, lamTerm, tylamTerm, recordTerm, injectTerm, traitLamTerm, showType, starKind } from "system-f-omega";
 * import { conType, varType, arrowType, conTerm, lamTerm as tlam } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", tlam("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * // Poly id
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), { var: "x" }));
 * console.log("poly:", showType(inferType(state, polyId).ok));  // "∀a::*. (a → a)"
 *
 * // Record
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * console.log("record:", showType(inferType(state, rec).ok));  // "{x: Int}"
 *
 * // Variant inject
 * const opt = injectTerm("Some", conTerm("42", conType("Int")), conType("Option"));
 * console.log("variant:", showType(inferType(state, opt).ok));  // "Option<Int>"
 *
 * // Trait lam
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * console.log("trait:", showType(inferType(state, traitLam).ok));  // "∀Self::* where Eq<Self>. (Self → Int)"
 * ```
 *
 * @example Key operations
 * ```ts
 * import { freshState, normalizeType, checkKind, unifyTypes, subsumes, isBottom, showType } from "system-f-omega";
 * import { conType, appType, neverType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * state = addType(state, "List", starKind).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log("kind:", showKind(checkKind(state, listInt).ok));  // "*"
 * console.log("norm:", showType(normalizeType(state, listInt)));  // "List<Int>"
 *
 * console.log("⊥ bottom:", isBottom(state, neverType));  // true
 * console.log("⊥ <: List<Int>:", "ok" in subsumes(state, listInt, neverType, [], new Map()));  // true
 * ```
 *
 * @see {@link inferType} Synthesis (`Γ ⊢ e ⇒ τ`)
 * @see {@link checkType} Analysis (`Γ ⊢ e ⇐ τ`)
 * @see {@link checkKind} `Γ ⊢ τ : κ`
 * @see {@link normalizeType} Expansion/normalization
 * @see {@link unifyTypes} Constraint solving
 * @see {@link subsumes} Subtyping/width
 * @see {@link showType} Pretty-printer
 * @see {@link TypeCheckerState} Inference context
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
 * Term variable `x` (value reference).
 *
 * **Purpose**: **Bound term reference**:
 * - **Lookup**: `inferVarType` → ctx binding (`term`/`dict`).
 * - **Dicts**: `Dict<Trait<Type>>` for bound evidence.
 * - **Unbound error** if missing.
 * Used everywhere: apps, bodies, projections.
 *
 * @typedef {Object} VarTerm
 * @property {string} var - Variable name (`"x"`, `"self"`, `"d"`)
 *
 * @example Construction
 * ```ts
 * import { varTerm, showTerm } from "system-f-omega";
 *
 * console.log("x:", showTerm(varTerm("x")));  // "x"
 * ```
 *
 * @example Inference (lookup)
 * ```ts
 * import { freshState, addType, addTerm, inferType, varTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * const result = inferType(state, varTerm("x"));
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Dict lookup
 * ```ts
 * import { freshState, addDict, dictTerm, inferType, varTerm, conType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addDict(state, "eqInt", dictTerm("Eq", conType("Int"), [])).ok;
 *
 * const result = inferType(state, varTerm("eqInt"));
 * console.log("dict:", showType(result.ok));  // "Dict<Eq, Int>"
 * ```
 *
 * @example Failure: Unbound
 * ```ts
 * import { freshState, inferType, varTerm, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = inferType(state, varTerm("missing"));
 * console.log("error:", showError(result.err));  // "Unbound identifier: missing"
 * ```
 *
 * @see {@link varTerm} Constructor
 * @see {@link inferVarType} Lookup rule
 * @see {@link addTerm} Term binding
 * @see {@link addDict} Dict binding
 */
export type VarTerm = { var: string };

/**
 * Lambda `λarg:τ. body` (annotated function abstraction).
 *
 * **Purpose**: **Bidirectional function typing**:
 * - **Inference** (`inferLamType`): Extend ctx → infer body → `τ → bodyType`.
 * - **Checking** (`checkType lam`): Unify domain → check body in codomain.
 * - **Bottom domains**: `⊥ → τ` from meta unification.
 * Supports polymorphism (nested tylam), traits (self/dicts).
 *
 * @typedef {Object} LamTerm
 * @property {Object} lam
 * @property {string} lam.arg - Parameter name (`"x"`)
 * @property {Type} lam.type - Annotated domain (`Int`, `?0`)
 * @property {Term} lam.body - Body (uses `arg`)
 *
 * @example Construction
 * ```ts
 * import { lamTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log("λx:Int.x:", showTerm(id));  // "λx:Int. x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = inferType(state, id);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Checking (domain unification)
 * ```ts
 * import { freshState, addType, checkType, lamTerm, varTerm, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * const result = checkType(state, id, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int → Bool)"
 * ```
 *
 * @example Bottom domain (meta unification)
 * ```ts
 * import { freshState, inferType, lamTerm, varTerm, neverType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const bottomLam = lamTerm("x", neverType, varTerm("x"));  // Domain ⊥
 * const result = inferType(state, bottomLam);
 * console.log("⊥→?:", showType(result.ok));  // "(⊥ → ?0)"
 * ```
 *
 * @see {@link lamTerm} Constructor
 * @see {@link inferLamType} Inference rule
 * @see {@link checkType} Domain checking
 * @see {@link arrowType} Inferred type
 * @see {@link appTerm} Application
 */
export type LamTerm = { lam: { arg: string; type: Type; body: Term } };

/**
 * Term application `(callee arg)` (function application).
 *
 * **Purpose**: **Beta-reduction typing**:
 * - **Callee inference**: Must be arrow/foralls/bounded_forall.
 * - **Argument check**: Bidirectional against domain (unify metas).
 * - **Instantiation**: Auto-freshen foralls (`?N`), resolve traits (`checkTraitConstraints`).
 * - **Bottom domains**: `⊥ → τ` accepts any arg.
 * Handles higher-order/poly/trait apps.
 *
 * @typedef {Object} AppTerm
 * @property {Object} app
 * @property {Term} app.callee - Function (lam/tylam/trait_lam/dict.method)
 * @property {Term} app.arg - Argument
 *
 * @example Construction
 * ```ts
 * import { appTerm, varTerm, showTerm } from "system-f-omega";
 *
 * const app = appTerm(varTerm("f"), varTerm("x"));
 * console.log("(f x):", showTerm(app));  // "(f x)"
 * ```
 *
 * @example Lambda application
 * ```ts
 * import { freshState, addType, addTerm, inferType, appTerm, varTerm, lamTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "id", lamTerm("x", conType("Int"), varTerm("x"))).ok;
 *
 * const app = appTerm(varTerm("id"), conTerm("42", conType("Int")));
 * const result = inferType(state, app);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Polymorphic instantiation
 * ```ts
 * import { freshState, addType, inferType, appTerm, varTerm, tylamTerm, lamTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const polyId = tylamTerm("a", starKind, lamTerm("x", conType("Int"), varTerm("x")));
 * state = addTerm(state, "polyId", polyId).ok;
 *
 * const app = appTerm(varTerm("polyId"), conTerm("42", conType("Int")));
 * const result = inferType(state, app);
 * console.log("poly app:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Not a function
 * ```ts
 * import { freshState, addType, inferType, appTerm, varTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const badApp = appTerm(conTerm("42", conType("Int")), varTerm("x"));
 * const result = inferType(state, badApp);
 * console.log("error:", showError(result.err));  // "Not a function: Int"
 * ```
 *
 * @see {@link appTerm} Constructor
 * @see {@link inferAppType} Inference (instantiation/check)
 * @see {@link checkType} Arg checking
 * @see {@link lamTerm} Common callee
 * @see {@link tylamTerm} Poly callee
 */
export type AppTerm = { app: { callee: Term; arg: Term } };

/**
 * Type lambda `Λvar::kind. body` (polymorphic abstraction).
 *
 * **Purpose**: **Parametric polymorphism**:
 * - **Inference**: Extend ctx (`var :: kind`) → infer body → `∀var::kind. bodyType`.
 * - **Checking**: Match forall structure/kinds, alpha-rename body.
 * - **No constraints**: Pure F<ω> (traits via `traitLamTerm`).
 * Used for generic functions (`id`), HKT map.
 *
 * @typedef {Object} TyLamTerm
 * @property {Object} tylam
 * @property {string} tylam.var - Bound type var (`"a"`, `"F"`)
 * @property {Kind} tylam.kind - Var kind (`*`, `*→*`)
 * @property {Term} tylam.body - Body (may use `var`)
 *
 * @example Construction
 * ```ts
 * import { tylamTerm, starKind, showTerm } from "system-f-omega";
 *
 * const polyId = tylamTerm("a", starKind, { var: "x" });
 * console.log("Λa.x:", showTerm(polyId));  // "Λa::*. x"
 * ```
 *
 * @example Inference (→ forall)
 * ```ts
 * import { freshState, inferType, tylamTerm, lamTerm, varTerm, varType, starKind, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const result = inferType(state, polyId);
 * console.log("inferred:", showType(result.ok));  // "∀a::*. (a → a)"
 * ```
 *
 * @example Checking (vs forall)
 * ```ts
 * import { freshState, checkType, tylamTerm, lamTerm, varTerm, varType, forallType, arrowType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const result = checkType(state, polyId, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @example HKT type lambda
 * ```ts
 * import { freshState, inferType, tylamTerm, arrowKind, starKind, appType, varType, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const hktLam = tylamTerm("F", arrowKind(starKind, starKind), appType(varType("F"), varType("Int")));
 * const result = inferType(state, hktLam);
 * console.log("HKT:", showType(result.ok));  // "∀F::(* → *). F<Int>"
 * ```
 *
 * @see {@link tylamTerm} Constructor
 * @see {@link inferTylamType} Inference (→ forall)
 * @see {@link tyappTerm} Application
 * @see {@link forallType} Inferred type
 * @see {@link instantiateType} Skolemization
 */
export type TyLamTerm = { tylam: { var: string; kind: Kind; body: Term } };

/**
 * Type application `term [type]` (polymorphic instantiation).
 *
 * **Purpose**: **Saturates type lambdas**:
 * - **Callee**: Must be forall (`∀α::κ.τ`).
 * - **Kind check**: `type :: κ`.
 * - **Substitution**: `τ[α ↦ type]`.
 * Handles nested foralls (auto-instantiate outer).
 * Used for monomorphization: `polyId[Int] : Int → Int`.
 *
 * @typedef {Object} TyAppTerm
 * @property {Object} tyapp
 * @property {Term} tyapp.term - Polymorphic callee (tylam)
 * @property {Type} tyapp.type - Type argument
 *
 * @example Construction
 * ```ts
 * import { tyappTerm, showTerm } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const app = tyappTerm({ var: "polyId" }, conType("Int"));
 * console.log("polyId[Int]:", showTerm(app));  // "polyId [Int]"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, tyappTerm, tylamTerm, lamTerm, varTerm, varType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * state = addTerm(state, "polyId", polyId).ok;
 *
 * const idInt = tyappTerm({ var: "polyId" }, conType("Int"));
 * const result = inferType(state, idInt);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, checkType, tyappTerm, tylamTerm, lamTerm, varTerm, varType, arrowType, conType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const idInt = tyappTerm(polyId, conType("Int"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, idInt, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @example Failure: Not forall
 * ```ts
 * import { freshState, addType, inferType, tyappTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const badApp = tyappTerm(conTerm("42", conType("Int")), conType("Bool"));
 * const result = inferType(state, badApp);
 * console.log("error:", showError(result.err));  // "Type mismatch..." or similar
 * ```
 *
 * @see {@link tyappTerm} Constructor
 * @see {@link inferTyappType} Inference rule
 * @see {@link tylamTerm} Callee (polymorphic)
 * @see {@link forallType} Expected callee type
 * @see {@link instantiateType} Type-level counterpart
 */
export type TyAppTerm = { tyapp: { term: Term; type: Type } };

/**
 * Typed constant `con` (literals/promoted constructors).
 *
 * **Purpose**: **Primitive values** with explicit type:
 * - **Literals**: `"42": Int`, `"true": Bool`.
 * - **Tags**: `"None": Unit` (enum constructors).
 * - **Inference**: Returns annotated `type` (no lookup).
 * Used in records/tuples/injects as fields/payloads.
 *
 * @typedef {Object} ConTerm
 * @property {Object} con
 * @property {string} con.name - Value (`"42"`, `"true"`, `"None"`)
 * @property {Type} con.type - Explicit type annotation
 *
 * @example Construction
 * ```ts
 * import { conTerm, conType, showTerm } from "system-f-omega";
 *
 * const num = conTerm("42", conType("Int"));
 * console.log("42:", showTerm(num));  // "42"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const num = conTerm("42", conType("Int"));
 * const result = inferType(state, num);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Record field
 * ```ts
 * import { freshState, addType, inferType, recordTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const result = inferType(state, rec);
 * console.log("record:", showType(result.ok));  // "{x: Int}"
 * ```
 *
 * @example Enum injection payload
 * ```ts
 * import { freshState, addType, addEnum, inferType, injectTerm, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [["Some", conType("T")]]).ok;
 *
 * const someInt = injectTerm("Some", conTerm("42", conType("Int")), appType(conType("Option"), conType("Int")));
 * const result = inferType(state, someInt);
 * console.log("Some(42):", showType(result.ok));  // "Option<Int>"
 * ```
 *
 * @see {@link conTerm} Constructor
 * @see {@link inferType} Returns `con.type`
 * @see {@link recordTerm} Record fields
 * @see {@link tupleTerm} Tuple elements
 * @see {@link injectTerm} Variant payloads
 */
export type ConTerm = { con: { name: string; type: Type } };

/**
 * Let-binding `let name = value in body` (non-recursive).
 *
 * **Purpose**: **Scoped binding**:
 * - **Inference**: Infer `value` type → extend ctx → infer `body`.
 * - **No generalization**: Monomorphic (use `tylam` for poly).
 * - **Non-recursive**: `value` evaluated before `body` (no self-ref).
 * Used for locals, poly-let (nested tylam), sugar.
 *
 * @typedef {Object} LetTerm
 * @property {Object} let
 * @property {string} let.name - Bound name (`"x"`)
 * @property {Term} let.value - Rhs term
 * @property {Term} let.body - Body (uses `name`)
 *
 * @example Construction
 * ```ts
 * import { letTerm, conTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const letX = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * console.log("let x=42 in x:", showTerm(letX));  // "let x = 42 in x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, letTerm, conTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const letX = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * const result = inferType(state, letX);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Nested let
 * ```ts
 * import { freshState, addType, inferType, letTerm, conTerm, appTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const inner = letTerm("y", conTerm("1", conType("Int")), varTerm("y"));
 * const outer = letTerm("x", conTerm("2", conType("Int")), appTerm(varTerm("x"), inner));
 * const result = inferType(state, outer);
 * console.log("nested:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link letTerm} Constructor
 * @see {@link inferLetType} Inference rule
 * @see {@link addTerm} Global binding
 */
export type LetTerm = { let: { name: string; value: Term; body: Term } };

/**
 * Record value `{ l₁ = t₁, l₂ = t₂, ... }` (labeled product).
 *
 * **Purpose**: **Structural records**:
 * - **Inference**: Field-by-field → `{l:τ}` (labels preserved).
 * - **Width subtyping**: `{x=1} <: {x:Int, y:?}`.
 * Used with projection (`e.l`), pattern matching.
 *
 * @typedef {Object} RecordTerm
 * @property {Array<[string, Term]>} record - Fields: `[[label, term], ...]`
 *
 * @example Construction
 * ```ts
 * import { recordTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const person = recordTerm([
 *   ["name", conTerm("Alice", conType("String"))],
 *   ["age", conTerm("30", conType("Int"))]
 * ]);
 * console.log("{name=Alice, age=30}:", showTerm(person));  // "{name = Alice, age = 30}"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, recordTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "String", starKind).ok;
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("hello", conType("String"))]
 * ]);
 * const result = inferType(state, rec);
 * console.log("inferred:", showType(result.ok));  // "{x: Int, y: String}"
 * ```
 *
 * @example Projection
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 * const result = inferType(state, proj);
 * console.log("x:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link recordTerm} Constructor
 * @see {@link inferRecordType} Inference
 * @see {@link projectTerm} Field access
 * @see {@link recordType} Inferred type
 */
export type RecordTerm = { record: [string, Term][] };

/**
 * Record projection `record.label` (field access).
 *
 * **Purpose**: **Extracts field type** from record:
 * - **Inference**: Lookup label in inferred record type → field slice.
 * - **Errors**: `not_a_record`, `missing_field`.
 * Supports width subtyping (extra fields OK in record).
 *
 * @typedef {Object} ProjectTerm
 * @property {Object} project
 * @property {Term} project.record - Record value
 * @property {string} project.label - Field label
 *
 * @example Construction
 * ```ts
 * import { projectTerm, recordTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 * console.log("rec.x:", showTerm(proj));  // "{x = 1}.x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 * const projX = projectTerm(rec, "x");
 * const result = inferType(state, projX);
 * console.log("x:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Missing field
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const projY = projectTerm(rec, "y");  // Missing
 * const result = inferType(state, projY);
 * console.log("missing:", showError(result.err));  // "Missing field 'y' in record: {x: Int}"
 * ```
 *
 * @see {@link projectTerm} Constructor
 * @see {@link inferProjectType} Inference rule
 * @see {@link recordTerm} Record values
 * @see {@link recordType} Record types
 */
export type ProjectTerm = { project: { record: Term; label: string } };

/**
 * Variant injection `<label=value> as variant_type` (tagged constructor).
 *
 * **Purpose**: **Builds tagged sum**:
 * - **Nominal**: Enum lookup → instantiate field scheme → check `value`.
 * - **Structural**: Direct case match in `<L:τ | ...>` → check `value : τ`.
 * - **Unit fields**: Empty tuple `{tuple:[]}` for nullary (`None = {}`).
 * - **Multi-field**: Tuple payload.
 * Infers full variant/enum type.
 *
 * @typedef {Object} InjectTerm
 * @property {Object} inject
 * @property {string} inject.label - Variant label (`"Left"`, `"Some"`)
 * @property {Term} inject.value - Payload
 * @property {Type} inject.variant_type - Expected variant/enum type
 *
 * @example Construction
 * ```ts
 * import { injectTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const leftVal = injectTerm("Left", conTerm("42", conType("Int")), { variant: [["Left", { con: "Int" }]] });
 * console.log("<Left=42>:", showTerm(leftVal));  // "<Left=42> as <Left: Int | ...>"
 * ```
 *
 * @example Nominal enum inference
 * ```ts
 * import { freshState, addType, addEnum, inferType, injectTerm, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const someInt = injectTerm("Some", conTerm("42", conType("Int")), appType(conType("Option"), conType("Int")));
 * const result = inferType(state, someInt);
 * console.log("inferred:", showType(result.ok));  // "Option<Int>"
 * ```
 *
 * @example Unit variant (None)
 * ```ts
 * import { freshState, addEnum, inferType, injectTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", tupleType([])]]).ok;
 *
 * const noneBool = injectTerm("None", { tuple: [] }, appType(conType("Option"), conType("Bool")));
 * const result = inferType(state, noneBool);
 * console.log("None:", showType(result.ok));  // "Option<Bool>"
 * ```
 *
 * @example Failure: Invalid label
 * ```ts
 * import { freshState, addEnum, inferType, injectTerm, appType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }]]).ok;
 *
 * const badSome = injectTerm("Some", { con: { name: "42", type: { con: "Int" } } }, appType(conType("Option"), conType("Int")));
 * const result = inferType(state, badSome);
 * console.log("invalid:", showError(result.err));  // "Invalid variant label 'Some' for: Option<Int>"
 * ```
 *
 * @see {@link injectTerm} Constructor
 * @see {@link inferInjectType} Inference (nominal/structural)
 * @see {@link variantType} Structural type
 * @see {@link addEnum} Nominal enums
 * @see {@link matchTerm} Pattern matching
 */
export type InjectTerm = {
  inject: { label: string; value: Term; variant_type: Type };
};

/**
 * Pattern match `match scrutinee { pat₁ => body₁ | pat₂ => body₂ | ... }`.
 *
 * **Purpose**: **Exhaustive destructuring**:
 * - **Inference**: Infer scrutinee → check patterns → common branch type (unify).
 * - **Exhaustiveness**: `checkExhaustive` (nominal enums, structural variants).
 * - **Bindings**: Per-branch ctx extension (`checkPattern` → flattened vars).
 * - **Mu unfolding**: Auto-unfolds recursive scrutinees.
 * Supports wildcards (exhaustive), nested patterns.
 *
 * @typedef {Object} MatchTerm
 * @property {Object} match
 * @property {Term} match.scrutinee - Value to destructure
 * @property {Array<[Pattern, Term]>} match.cases - Pattern-body pairs
 *
 * @example Construction
 * ```ts
 * import { matchTerm, varPattern, showTerm } from "system-f-omega";
 *
 * const match = matchTerm({ var: "xs" }, [[varPattern("x"), { var: "x" }]]);
 * console.log("match xs { x => x }:", showTerm(match));  // "match xs { x => x }"
 * ```
 *
 * @example Enum inference (Option)
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, variantPattern, varPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 * const match = matchTerm(scrut, [
 *   [variantPattern("None", varPattern("_")), conTerm("0", conType("Int"))],
 *   [variantPattern("Some", varPattern("x")), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Record/tuple destructuring
 * ```ts
 * import { freshState, addType, inferType, matchTerm, recordPattern, tuplePattern, varPattern, recordTerm, tupleTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const recScrut = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const recMatch = matchTerm(recScrut, [[recordPattern([["x", varPattern("a")]), varTerm("a")]]);
 * console.log("record match:", showType(inferType(state, recMatch).ok));  // "Int"
 *
 * const tupScrut = tupleTerm([conTerm("1", conType("Int")), conTerm("2", conType("Int"))]);
 * const tupMatch = matchTerm(tupScrut, [[tuplePattern([varPattern("x"), varPattern("y")]), varTerm("x")]]);
 * console.log("tuple match:", showType(inferType(state, tupMatch).ok));  // "Int"
 * ```
 *
 * @example Exhaustiveness check
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, appType, conType, starKind } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const patterns = [variantPattern("None", varPattern("_")), variantPattern("Some", varPattern("x"))];
 * const exhaustive = checkExhaustive(state, patterns, appType(conType("Option"), conType("Int")));
 * console.log("exhaustive:", "ok" in exhaustive);  // true
 * ```
 *
 * @see {@link matchTerm} Constructor
 * @see {@link inferMatchType} Inference (common type)
 * @see {@link checkExhaustive} Coverage
 * @see {@link checkPattern} Bindings per branch
 */
export type MatchTerm = {
  match: { scrutinee: Term; cases: [Pattern, Term][] };
};

/**
 * Fold `fold[type](term)` (packs into recursive μ-type).
 *
 * **Purpose**: **Recursive injection**:
 * - `term : τ[μ/α]` → `fold : μ` (where `τ = body`).
 * - Validates `term` against unfolded type.
 * Used for recursive data (lists, trees) from unfolded constructors.
 *
 * @typedef {Object} FoldTerm
 * @property {Object} fold
 * @property {Type} fold.type - Mu type (`μX.τ`)
 * @property {Term} fold.term - Value matching unfolded body
 *
 * @example Construction
 * ```ts
 * import { foldTerm, showTerm } from "system-f-omega";
 * import { muType, tupleType, conType } from "system-f-omega";
 *
 * const listMu = muType("L", tupleType([conType("Int"), { var: "L" }]));
 * const foldVal = foldTerm(listMu, { tuple: [{ con: { name: "1", type: conType("Int") } }, { var: "prev" }] });
 * console.log("fold:", showTerm(foldVal));  // "fold[μL.(Int, L)]((1, prev))"
 * ```
 *
 * @example Inference (recursive enum)
 * ```ts
 * import { freshState, addType, addEnum, inferType, foldTerm, injectTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), { var: "T" })])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const result = inferType(state, folded);
 * console.log("inferred:", showType(result.ok));  // "List<Int>"
 * ```
 *
 * @see {@link foldTerm} Constructor
 * @see {@link inferFoldType} Typing rule
 * @see {@link muType} Recursive type
 * @see {@link unfoldTerm} Dual
 * @see {@link addEnum} Recursive enums
 */
export type FoldTerm = { fold: { type: Type; term: Term } };

/**
 * Unfold `unfold(term)` (projects from recursive μ-type).
 *
 * **Purpose**: **Recursive projection**:
 * - `term : μ` → `unfold : body[μ/α]` (equi-recursive).
 * Used to destructure recursive data (e.g., list cons).
 *
 * @typedef {Object} UnfoldTerm
 * @property {Term} unfold - Folded mu term
 *
 * @example Construction
 * ```ts
 * import { unfoldTerm, showTerm } from "system-f-omega";
 *
 * const unfolded = unfoldTerm({ var: "foldedList" });
 * console.log("unfold:", showTerm(unfolded));  // "unfold(foldedList)"
 * ```
 *
 * @example Inference (recursive enum)
 * ```ts
 * import { freshState, addEnum, inferType, unfoldTerm, foldTerm, injectTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), { var: "T" })])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const unfolded = unfoldTerm(folded);
 * const result = inferType(state, unfolded);
 * console.log("inferred:", showType(result.ok));  // "(⊥, List<Int>)"
 * ```
 *
 * @see {@link unfoldTerm} Constructor
 * @see {@link inferUnfoldType} Typing rule
 * @see {@link foldTerm} Dual
 * @see {@link muType} Recursive type
 */
export type UnfoldTerm = { unfold: Term };

/**
 * Tuple value `(t₁, t₂, ...)` (unlabeled product).
 *
 * **Purpose**: **Anonymous sequences**:
 * - **Inference**: Element-by-element → `(τ₁, τ₂, ...)`.
 * - **Exact arity**: No width (unlike records).
 * - **Zero-arity**: `()` = unit (sole value).
 * Used in tuples, enum fields (multi-arity variants), patterns.
 *
 * @typedef {Object} TupleTerm
 * @property {Term[]} tuple - Element terms
 *
 * @example Construction
 * ```ts
 * import { tupleTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const pair = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * console.log("(1, true):", showTerm(pair));  // "(1, true)"
 * console.log("unit ():", showTerm(tupleTerm([])));  // "()"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tup = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * const result = inferType(state, tup);
 * console.log("inferred:", showType(result.ok));  // "(Int, Bool)"
 * ```
 *
 * @example Nested tuples
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const nested = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   tupleTerm([conTerm("true", conType("Bool"))])
 * ]);
 * const result = inferType(state, nested);
 * console.log("nested:", showType(result.ok));  // "(Int, (Bool,))"
 * ```
 *
 * @see {@link tupleTerm} Constructor
 * @see {@link inferTupleType} Inference
 * @see {@link tupleType} Inferred type
 * @see {@link tupleProjectTerm} Access
 * @see {@link tuplePattern} Destructuring
 */
export type TupleTerm = { tuple: Term[] };

/**
 * Tuple projection `tuple.index` (nth element access).
 *
 * **Purpose**: **Bounds-checked indexing**:
 * - **Inference**: Infer tuple → check `0 ≤ index < arity` → element type.
 * - **Errors**: `not_a_tuple`, `tuple_index_out_of_bounds`.
 * Zero-based (`tuple.0` = first).
 *
 * @typedef {Object} TupleProjectTerm
 * @property {Object} tuple_project
 * @property {Term} tuple_project.tuple - Tuple value
 * @property {number} tuple_project.index - 0-based index
 *
 * @example Construction
 * ```ts
 * import { tupleProjectTerm, tupleTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const tup = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * const proj0 = tupleProjectTerm(tup, 0);
 * console.log("tup.0:", showTerm(proj0));  // "((1, true)).0"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, tupleProjectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tup = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * const proj0 = tupleProjectTerm(tup, 0);
 * const result = inferType(state, proj0);
 * console.log("proj[0]:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Out-of-bounds
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, tupleProjectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int"))]);
 * const proj1 = tupleProjectTerm(tup, 1);  // Out-of-bounds
 * const result = inferType(state, proj1);
 * console.log("error:", showError(result.err));  // "Tuple index out of bounds: Tuple: (Int,), Index: 1"
 * ```
 *
 * @see {@link tupleProjectTerm} Constructor
 * @see {@link inferTupleProjectType} Inference
 * @see {@link tupleTerm} Tuple values
 * @see {@link tupleType} Tuple types
 */
export type TupleProjectTerm = {
  tuple_project: { tuple: Term; index: number };
};

/**
 * Trait dictionary `dict trait<type> { method = impl, ... }` (implementation evidence).
 *
 * **Purpose**: **Dictionary-passing traits** (Haskell-style):
 * - **Validation** (`inferDictType`): Matches trait def methods → checks impls in `self` ctx.
 * - **Arbitrary extras**: Extra methods OK (required only).
 * - **Inference**: `Dict<trait, type>` (abstract marker).
 * - **HKT support**: Partial kinds (`List` vs `List<Int>`).
 * Used in `traitImplBinding`, `addTraitImpl`, resolution (`checkTraitImplementation`).
 *
 * @typedef {Object} DictTerm
 * @property {Object} dict
 * @property {string} dict.trait - Trait name (`"Eq"`, `"Functor"`)
 * @property {Type} dict.type - Implemented type (`Int`, `List<a>`)
 * @property {Array<[string, Term]>} dict.methods - Method impls `[[name, term], ...]`
 *
 * @example Construction
 * ```ts
 * import { dictTerm, conType, showTerm } from "system-f-omega";
 * import { lamTerm, varTerm } from "system-f-omega";
 *
 * const eqInt = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"), varTerm("x"))]
 * ]);
 * console.log("dict:", showTerm(eqInt));  // "dict Eq<Int> { eq = λx:Int.x }"
 * ```
 *
 * @example Inference (requires trait def)
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, dictTerm, conType, starKind, arrowType, varType, lamTerm, varTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(conType("A"), arrowType(conType("A"), conType("Bool")))]
 * ]).ok;
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"), lamTerm("y", conType("Int"), conTerm("true", conType("Bool"))))]
 * ]);
 * const result = inferType(state, eqDict);
 * console.log("inferred:", showType(result.ok));  // "Dict<Eq, Int>"
 * ```
 *
 * @example Trait impl binding
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = traitImplBinding(state, "Eq", conType("Int"), eqDict);
 * console.log(showContext(state.ctx));  // "...Impl: Eq = dict Eq<Int> { eq = λx:Int.true }: Int"
 * ```
 *
 * @see {@link dictTerm} Constructor
 * @see {@link inferDictType} Validation/inference
 * @see {@link traitImplBinding} Context storage
 * @see {@link checkTraitImplementation} Resolution
 * @see {@link traitMethodTerm} Method access
 */
export type DictTerm = {
  dict: {
    trait: string;
    type: Type;
    methods: [string, Term][]; // method implementations
  };
};

/**
 * Trait method access `dict.method` (dictionary projection).
 *
 * **Purpose**: **Method lookup** from evidence:
 * - **Ctx var dict**: Lookup `dict` binding → trait def → substitute `Self`.
 * - **Concrete dictTerm**: Infer method impl type.
 * - **Errors**: Missing dict/trait/method.
 * Used post-resolution (`checkTraitConstraints` → `d.eq`).
 *
 * @typedef {Object} TraitMethodTerm
 * @property {Object} trait_method
 * @property {Term} trait_method.dict - Dictionary evidence (var/dictTerm)
 * @property {string} trait_method.method - Method name (`"eq"`)
 *
 * @example Construction (var dict)
 * ```ts
 * import { traitMethodTerm, showTerm } from "system-f-omega";
 *
 * const eqMethod = traitMethodTerm({ var: "eqInt" }, "eq");
 * console.log("eqInt.eq:", showTerm(eqMethod));  // "eqInt.eq"
 * ```
 *
 * @example Inference (ctx dict var)
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, inferType, traitMethodTerm, varTerm, conType, starKind, arrowType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), arrowType(conType("A"), conType("Bool")))]]);
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), lamTerm("y", conType("Int"), conTerm("true", conType("Bool"))))]]);
 * state = addDict(state, "eqInt", eqDict).ok;
 *
 * const method = traitMethodTerm(varTerm("eqInt"), "eq");
 * const result = inferType(state, method);
 * console.log("inferred:", showType(result.ok));  // "(Int → (Int → Bool))"
 * ```
 *
 * @example Inference (concrete dict)
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, traitMethodTerm, dictTerm, conType, starKind, arrowType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]);
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 *
 * const method = traitMethodTerm(eqDict, "eq");
 * const result = inferType(state, method);
 * console.log("concrete:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @see {@link traitMethodTerm} Constructor
 * @see {@link inferTraitMethodType} Lookup/inference
 * @see {@link dictTerm} Concrete dict
 * @see {@link addDict} Ctx dict var
 * @see {@link dictTerm} Methods
 */
export type TraitMethodTerm = {
  trait_method: {
    dict: Term; // dictionary/evidence
    method: string;
  };
};

/**
 * Trait lambda `Λtrait_var<trait<type_var>>::kind where constraints. body` (bounded polymorphism).
 *
 * **Purpose**: **Abstraction over trait evidence**:
 * - Extend ctx: `type_var :: kind`, `trait_var : Dict<trait<type_var>>`.
 * - Infer body → `∀type_var::kind where constraints. bodyType`.
 * - Constraints validated against trait def (via ctx lookup).
 * Used for generic impls: `Λd<Eq<Self>>. Self → Self`.
 *
 * @typedef {Object} TraitLamTerm
 * @property {Object} trait_lam
 * @property {string} trait_lam.trait_var - Dict binder (`"d"`)
 * @property {string} trait_lam.trait - Trait name (`"Eq"`)
 * @property {string} trait_lam.type_var - Type binder (`"Self"`)
 * @property {Kind} trait_lam.kind - Type var kind
 * @property {TraitConstraint[]} trait_lam.constraints - Bounds `[{trait,type}, ...]`
 * @property {Term} trait_lam.body - Body (uses `trait_var`, `type_var`)
 *
 * @example Construction
 * ```ts
 * import { traitLamTerm, starKind, showTerm } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const eqLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], { var: "body" });
 * console.log("trait lam:", showTerm(eqLam));  // "ΛSelf::* where Eq<Self>. body"
 * ```
 *
 * @example Inference (→ bounded forall)
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, traitLamTerm, starKind, varType, arrowType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(varType("A"), varType("Bool"))]]).ok;
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Int")));
 * const result = inferType(state, traitLam);
 * console.log("inferred:", showType(result.ok));  // "∀Self::* where Eq<Self>. (Self → Int)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addTraitDef, checkType, traitLamTerm, boundedForallType, starKind, varType, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(varType("A"), varType("Bool"))]]).ok;
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Int")));
 * const expected = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Int")));
 * const result = checkType(state, traitLam, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @see {@link traitLamTerm} Constructor
 * @see {@link inferTraitLamType} Inference
 * @see {@link traitAppTerm} Application
 * @see {@link boundedForallType} Inferred type
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
 * Trait application `term [type] with dicts` (bounded instantiation).
 *
 * **Purpose**: **Saturates trait lambdas**:
 * - Callee must be `bounded_forall` (after instantiation).
 * - Kind check: `type :: kind`.
 * - Resolve constraints: `checkTraitConstraints` → verify provided `dicts`.
 * - Substitute `type_var ↦ type` in body.
 * Used post-resolution: `traitLam[Int] with eqIntDict`.
 *
 * @typedef {Object} TraitAppTerm
 * @property {Object} trait_app
 * @property {Term} trait_app.term - Trait lambda
 * @property {Type} trait_app.type - Type argument
 * @property {Term[]} trait_app.dicts - Evidence per constraint
 *
 * @example Construction
 * ```ts
 * import { traitAppTerm, showTerm } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const app = traitAppTerm({ var: "traitLam" }, conType("Int"), [{ var: "eqDict" }]);
 * console.log("trait app:", showTerm(app));  // "traitLam [Int] with dicts {eqDict}"
 * ```
 *
 * @example Inference (with resolution)
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, traitAppTerm, traitLamTerm, conType, starKind, varType, arrowType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * const app = traitAppTerm(traitLam, conType("Int"), [eqDict]);
 * const result = inferType(state, app);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Wrong dict count
 * ```ts
 * import { freshState, inferType, traitAppTerm, traitLamTerm, conType, starKind, showError } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const state = freshState();
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], conType("Int"));
 * const badApp = traitAppTerm(traitLam, conType("Int"), []);  // Missing dict
 * const result = inferType(state, badApp);
 * console.log("wrong dicts:", "wrong_number_of_dicts" in result.err);  // true
 * ```
 *
 * @see {@link traitAppTerm} Constructor
 * @see {@link inferTraitAppType} Inference/resolution
 * @see {@link traitLamTerm} Callee
 * @see {@link checkTraitConstraints} Dict validation
 * @see {@link dictTerm} Evidence
 */
export type TraitAppTerm = {
  trait_app: {
    term: Term;
    type: Type;
    dicts: Term[]; // evidence for each constraint
  };
};

/**
 * Core term language: **Bidirectional λ-calculus + Fω + Records/Variants/μ/Traits**.
 *
 * **Purpose**: Statically typed expressions with:
 * | Constructor | Syntax | Purpose |
 * |-------------|--------|---------|
 * | `AppTerm` | `e₁ e₂` | Function application |
 * | `ConTerm` | `42:τ` | Typed constants/literals |
 * | `DictTerm` | `dict T<τ> { m=e }` | Trait dictionary (evidence) |
 * | `FoldTerm` | `fold[μ](e)` | Recursive packing |
 * | `InjectTerm` | `<L=e> as T` | Variant injection |
 * | `LamTerm` | `λx:τ.e` | Function abstraction |
 * | `LetTerm` | `let x=e₁ in e₂` | Non-recursive binding |
 * | `MatchTerm` | `match e { p⇒e }` | Pattern matching |
 * | `ProjectTerm` | `e.l` | Record projection |
 * | `RecordTerm` | `{l=e}` | Record construction |
 * | `TraitAppTerm` | `e[τ] with dicts` | Trait instantiation |
 * | `TraitLamTerm` | `Λd<T<α>>.e` | Trait abstraction |
 * | `TraitMethodTerm` | `dict.method` | Method access |
 * | `TupleProjectTerm` | `tup.i` | Tuple projection |
 * | `TupleTerm` | `(e₁,e₂)` | Tuple construction |
 * | `TyAppTerm` | `e[τ]` | Type application |
 * | `TyLamTerm` | `Λα::κ.e` | Type abstraction |
 * | `UnfoldTerm` | `unfold(e)` | Recursive unpacking |
 * | `VarTerm` | `x` | Variable reference |
 *
 * **Features**:
 * - **Bidirectional**: `inferType(Γ ⊢ e ⇒ τ)` / `checkType(Γ ⊢ e ⇐ τ)`.
 * - **Polymorphism**: System Fω (`tylam/tyapp`) + traits (`traitLam/app`).
 * - **Data**: Records (width), variants/tuples (exact), μ-recursion.
 * - **Traits**: Dictionary-passing (`inferDictType`, resolution).
 * - **Patterns**: Exhaustive matching (`checkExhaustive`).
 *
 * @typedef {Union} Term
 * @type {AppTerm} `e₁ e₂` - Application
 * @type {ConTerm} `c:τ` - Constants
 * @type {DictTerm} `dict T<τ> {m=e}` - Trait evidence
 * @type {FoldTerm} `fold[μ](e)` - Recursive pack
 * @type {InjectTerm} `<L=e> as T` - Variant constructor
 * @type {LamTerm} `λx:τ.e` - Lambda
 * @type {LetTerm} `let x=e₁ in e₂` - Binding
 * @type {MatchTerm} `match e {p⇒e}` - Destructuring
 * @type {ProjectTerm} `e.l` - Record field
 * @type {RecordTerm} `{l=e}` - Record literal
 * @type {TraitAppTerm} `e[τ] with ds` - Trait app
 * @type {TraitLamTerm} `Λd<T<α>>.e` - Trait lambda
 * @type {TraitMethodTerm} `d.m` - Method projection
 * @type {TupleProjectTerm} `tup.i` - Tuple index
 * @type {TupleTerm} `(e₁,e₂)` - Tuple literal
 * @type {TyAppTerm} `e[τ]` - Type app
 * @type {TyLamTerm} `Λα::κ.e` - Type lambda
 * @type {UnfoldTerm} `unfold(e)` - Recursive unpack
 * @type {VarTerm} `x` - Variable
 *
 * @example Core λ-calculus
 * ```ts
 * import { freshState, addType, inferType, lamTerm, appTerm, varTerm, conTerm, conType, starKind, showTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log("λx.x:", showTerm(id));  // "λx:Int. x"
 * console.log("type:", showType(inferType(state, id).ok));  // "(Int → Int)"
 *
 * const app = appTerm(id, conTerm("42", conType("Int")));
 * console.log("app:", showTerm(app));  // "(λx:Int. x 42)"
 * console.log("type:", showType(inferType(state, app).ok));  // "Int"
 * ```
 *
 * @example Polymorphism + data
 * ```ts
 * import { freshState, addType, inferType, tylamTerm, tyappTerm, recordTerm, injectTerm, matchTerm, variantPattern, varPattern, projectTerm, tupleTerm, tupleProjectTerm, showType, starKind } from "system-f-omega";
 * import { lamTerm, varTerm, conTerm, conType, recordType, variantType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * // Poly
 * const polyId = tylamTerm("a", starKind, lamTerm("x", conType("Int"), varTerm("x")));
 * console.log("poly:", showType(inferType(state, polyId).ok));  // "∀a::*. (Int → Int)"
 *
 * // Data
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * console.log("record:", showType(inferType(state, rec).ok));  // "{x: Int}"
 * console.log("proj:", showType(inferType(state, projectTerm(rec, "x")).ok));  // "Int"
 *
 * const inj = injectTerm("Left", conTerm("true", conType("Bool")), variantType([["Left", conType("Bool")]]));
 * console.log("inject:", showType(inferType(state, inj).ok));  // "<Left: Bool | ...>"
 *
 * const mtch = matchTerm(inj, [[variantPattern("Left", varPattern("x")), varTerm("x")]]);
 * console.log("match:", showType(inferType(state, mtch).ok));  // "Bool"
 *
 * const tup = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * console.log("tuple:", showType(inferType(state, tup).ok));  // "(Int, Bool)"
 * console.log("proj0:", showType(inferType(state, tupleProjectTerm(tup, 0)).ok));  // "Int"
 * ```
 *
 * @example Traits + recursion
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, traitLamTerm, traitAppTerm, traitMethodTerm, foldTerm, unfoldTerm, showType, starKind } from "system-f-omega";
 * import { conType, varType, arrowType, lamTerm, conTerm, appType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * // Traits
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * console.log("traitLam:", showType(inferType(state, traitLam).ok));  // "∀Self::* where Eq<Self>. (Self → Int)"
 *
 * const app = traitAppTerm(traitLam, conType("Int"), [eqDict]);
 * console.log("traitApp:", showType(inferType(state, app).ok));  // "Int"
 *
 * const method = traitMethodTerm(eqDict, "eq");
 * console.log("method:", showType(inferType(state, method).ok));  // "(Int → Bool)"
 * ```
 *
 * @example Key operations
 * ```ts
 * import { freshState, inferType, checkType, showType, showError } from "system-f-omega";
 * import { lamTerm, varTerm, conTerm, conType, arrowType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log("infer:", showType(inferType(state, id).ok));  // "(Int → Int)"
 *
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * console.log("check:", showType(checkType(state, id, expected).ok.type));  // "(Int → Bool)"
 * ```
 *
 * @see {@link inferType} Synthesis
 * @see {@link checkType} Analysis
 * @see {@link showTerm} Pretty-printer
 * @see {@link Type} Types
 * @see {@link Pattern} Patterns
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
 * Term binding `x : τ` (value variable).
 *
 * **Purpose**: Binds term names to types in context (`Γ`):
 * - **Lookup**: `inferVarType` → returns `type`.
 * - **Extension**: `inferLamType`, `checkPattern` → add to ctx.
 * - **No poly**: Monomorphic (use tylam for generalization).
 * Used in `addTerm`, let-bindings, pattern vars.
 *
 * @typedef {Object} TermBinding
 * @property {Object} term
 * @property {string} term.name - Variable name (`"x"`)
 * @property {Type} term.type - Inferred/annotated type
 *
 * @example Construction
 * ```ts
 * import { termBinding, conType, showBinding } from "system-f-omega";
 *
 * const bind = termBinding("x", conType("Int"));
 * console.log("Term: x = Int");  // "Term: x = Int"
 * ```
 *
 * @example Context lookup
 * ```ts
 * import { freshState, addType, addTerm, inferType, varTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * const result = inferType(state, varTerm("x"));
 * console.log("x:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link termBinding} Constructor
 * @see {@link addTerm} Stateful add
 * @see {@link inferVarType} Lookup
 */
export type TermBinding = { term: { name: string; type: Type } };

/**
 * Type binding `name :: kind` (type constructor/kind var).
 *
 * **Purpose**: Binds type names/kind vars in context:
 * - **Lookup**: `checkVarKind`, `checkConKind` → returns `kind`.
 * - **HKTs**: `List :: * → *`.
 * - **Primitives**: `Int :: *`.
 * Used in `addType`, forall/tylam binders.
 *
 * @typedef {Object} TypeBinding
 * @property {Object} type
 * @property {string} type.name - Type name (`"Int"`, `"List"`)
 * @property {Kind} type.kind - Kind (`*`, `*→*`)
 *
 * @example Construction
 * ```ts
 * import { typeBinding, starKind, showBinding } from "system-f-omega";
 *
 * const bind = typeBinding("Int", starKind);
 * console.log("Type: Int = *");  // "Type: Int = *"
 * ```
 *
 * @example Context lookup (kind)
 * ```ts
 * import { freshState, addType, checkKind, conType, starKind, arrowKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 *
 * const result = checkKind(state, conType("List"));
 * console.log("List :: (*→*):", "ok" in result);  // true
 * ```
 *
 * @see {@link typeBinding} Constructor
 * @see {@link addType} Stateful add
 * @see {@link checkKind} Lookup
 */
export type TypeBinding = { type: { name: string; kind: Kind } };

/**
 * Type alias binding `name<params::kinds> = body` (parametric synonym).
 *
 * **Purpose**: Parametric type aliases:
 * - **Expansion**: `normalizeType` → substitute params → body.
 * - **Kind comp**: `name :: k₁→...→kₙ→bodyKind`.
 * - **Ctx ext**: Params bound during body check (`addTypeAlias`).
 * Used for newtypes, HKT wrappers.
 *
 * @typedef {Object} TypeAliasBinding
 * @property {Object} type_alias
 * @property {string} type_alias.name - Alias name (`"Id"`)
 * @property {string[]} type_alias.params - Param names `["A"]`
 * @property {Kind[]} type_alias.kinds - Param kinds `[starKind]`
 * @property {Type} type_alias.body - RHS (uses params)
 *
 * @example Construction
 * ```ts
 * import { typeAliasBinding, varType, starKind, showBinding } from "system-f-omega";
 *
 * const idAlias = typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * console.log("Id<A> = A");  // "Type Alias: Id<A::*> = A"
 * ```
 *
 * @example Expansion
 * ```ts
 * import { freshState, addType, addTypeAlias, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const idInt = appType(conType("Id"), conType("Int"));
 * const expanded = normalizeType(state, idInt);
 * console.log("Id<Int> → Int:", showType(expanded));  // "Int"
 * ```
 *
 * @see {@link typeAliasBinding} Constructor
 * @see {@link addTypeAlias} Stateful add
 * @see {@link normalizeType} Expansion
 * @see {@link checkConKind} Alias lookup
 */
export type TypeAliasBinding = {
  type_alias: { name: string; params: string[]; kinds: Kind[]; body: Type };
};

/**
 * Trait definition `trait name<type_param::kind> { method: sig, ... }` (interface).
 *
 * **Purpose**: **Declares trait signatures**:
 * - `type_param`: Self-type (`"Self"`, `"F"`).
 * - Methods: `name → Type` (uses `type_param`).
 * - **Validation** (`addTraitDef`): Methods `:: *` in extended ctx.
 * - **Lookup**: `inferTraitMethodType`, `inferDictType` → substitute Self.
 * - **HKT traits**: `Functor<F::(*→*)> { map: (A→B) → F<A> → F<B> }`.
 *
 * @typedef {Object} TraitDef
 * @property {string} name - Trait name (`"Eq"`, `"Functor"`)
 * @property {string} type_param - Self param (`"Self"`, `"F"`)
 * @property {Kind} kind - Self kind (`*`, `*→*`)
 * @property {Array<[string, Type]>} methods - Signatures `[[name, type], ...]`
 *
 * @example Construction
 * ```ts
 * import { TraitDef, starKind, arrowType, varType } from "system-f-omega";
 *
 * const eqDef: TraitDef = {
 *   name: "Eq",
 *   type_param: "Self",
 *   kind: starKind,
 *   methods: [["eq", arrowType(varType("Self"), varType("Bool"))]]
 * };
 * console.log("Eq<Self>:", JSON.stringify(eqDef));  // Eq def
 * ```
 *
 * @example addTraitDef (ctx binding)
 * ```ts
 * import { freshState, addType, addTraitDef, starKind, arrowType, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "Self", starKind, [
 *   ["eq", arrowType(varType("Self"), varType("Bool"))]
 * ]).ok;
 * console.log(showContext(state.ctx));  // "...Trait: Eq = TraitDef (Eq Self = *\n  eq : (Self → Bool))"
 * ```
 *
 * @example HKT trait
 * ```ts
 * import { freshState, addTraitDef, arrowKind, starKind, arrowType, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Functor", "F", arrowKind(starKind, starKind), [
 *   ["map", arrowType(varType("A"), arrowType(varType("F"), varType("F")))]
 * ]).ok;
 * console.log(showContext(state.ctx));  // "Trait: Functor = TraitDef (Functor F = (* → *)\n  map : (A → (F → F)))"
 * ```
 *
 * @see {@link addTraitDef} Context binding
 * @see {@link inferDictType} Method validation
 * @see {@link inferTraitMethodType} Signature lookup
 */
export type TraitDef = {
  name: string;
  type_param: string; // e.g., "Self"
  kind: Kind;
  methods: [string, Type][]; // method name -> method type
};

/**
 * Trait definition binding for context (`trait_def: TraitDef`).
 *
 * **Purpose**: Stores trait interfaces in `Γ` for:
 * - Dict validation (`inferDictType`).
 * - Method lookup (`inferTraitMethodType`).
 * Used by `addTraitDef`.
 *
 * @typedef {Object} TraitDefBinding
 * @property {TraitDef} trait_def - Trait interface
 *
 * @example Construction
 * ```ts
 * import { TraitDefBinding, starKind, arrowType, varType } from "system-f-omega";
 *
 * const eqBinding: TraitDefBinding = {
 *   trait_def: {
 *     name: "Eq",
 *     type_param: "Self",
 *     kind: starKind,
 *     methods: [["eq", arrowType(varType("Self"), varType("Bool"))]]
 *   }
 * };
 * console.log("TraitDefBinding:", JSON.stringify(eqBinding));
 * ```
 *
 * @example Context display
 * ```ts
 * import { freshState, addTraitDef, showContext, starKind, arrowType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Eq", "Self", starKind, [["eq", arrowType(varType("Self"), varType("Bool"))]]).ok;
 * console.log(showContext(state.ctx));  // "Trait: Eq = TraitDef (Eq Self = *\n  eq : (Self → Bool))"
 * ```
 *
 * @see {@link TraitDef} Interface
 * @see {@link addTraitDef} Stateful add
 * @see {@link showBinding} Pretty-print
 */
export type TraitDefBinding = {
  trait_def: TraitDef;
};

/**
 * Trait implementation binding `trait_impl { trait, type, dict }` (concrete evidence).
 *
 * **Purpose**: **Registers impls** for dictionary resolution:
 * - **Exact match**: `typesEqual(impl.type, query)` → return `dict`.
 * - **Polymorphic**: Instantiate impl type → unify with query → freshen `dict`.
 * Used by `addTraitImpl`, enables `checkTraitImplementation`/`checkTraitConstraints`.
 * Enables HKT matching (partial kinds).
 *
 * @typedef {Object} TraitImplBinding
 * @property {Object} trait_impl
 * @property {string} trait_impl.trait - Implemented trait (`"Eq"`)
 * @property {Type} trait_impl.type - Concrete/partial type (`Int`, `List`)
 * @property {Term} trait_impl.dict - Dictionary term (instantiated methods)
 *
 * @example Construction
 * ```ts
 * import { traitImplBinding, dictTerm, conType } from "system-f-omega";
 * import { lamTerm, varTerm, conTerm } from "system-f-omega";
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]
 * ]);
 * const impl = traitImplBinding("Eq", conType("Int"), eqDict);
 * console.log("impl:", JSON.stringify(impl));
 * ```
 *
 * @example Context binding (addTraitImpl)
 * ```ts
 * import { freshState, addType, addTraitDef, addTraitImpl, dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addTraitImpl(state, "Eq", conType("Int"), eqDict).ok;
 * console.log(showContext(state.ctx));  // "...Impl: Eq = dict Eq<Int> { eq = λx:Int.true }: Int"
 * ```
 *
 * @example Resolution usage
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, checkTraitImplementation, conType, starKind, arrowType, lamTerm, varTerm, conTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const result = checkTraitImplementation(state, "Eq", conType("Int"));
 * console.log("resolved:", "ok" in result);  // true
 * ```
 *
 * @see {@link traitImplBinding} Constructor
 * @see {@link addTraitImpl} Stateful add
 * @see {@link checkTraitImplementation} Lookup/matching
 * @see {@link DictTerm} Dictionary value
 */
export type TraitImplBinding = {
  trait_impl: {
    trait: string;
    type: Type;
    dict: Term; // dictionary term
  };
};

/**
 * Dictionary binding `dict name : Trait<trait> <type>` (trait evidence var).
 *
 * **Purpose**: **Binds dict vars** in trait lambda ctx:
 * - Enables `trait_method(dict, "eq")` lookup → trait def sig.
 * - Used in `trait_lam` extension, `addDict`.
 * Abstracts over concrete dicts (var vs DictTerm).
 *
 * @typedef {Object} DictBinding
 * @property {Object} dict
 * @property {string} dict.name - Dict var (`"eqSelf"`)
 * @property {string} dict.trait - Trait (`"Eq"`)
 * @property {Type} dict.type - Type param (`Self`, `List<a>`)
 *
 * @example Construction
 * ```ts
 * import { dictBinding, conType } from "system-f-omega";
 *
 * const eqBind = dictBinding("eqInt", "Eq", conType("Int"));
 * console.log("dict bind:", JSON.stringify(eqBind));
 * ```
 *
 * @example Context binding (addDict)
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addDict(state, "eqInt", eqDict).ok;
 * console.log(showContext(state.ctx));  // "...Dict: eqInt = Trait Eq : Int"
 * ```
 *
 * @example Trait method lookup
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, inferType, traitMethodTerm, varTerm, conType, starKind, arrowType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addDict(state, "eqInt", eqDict).ok;
 *
 * const method = traitMethodTerm(varTerm("eqInt"), "eq");
 * const result = inferType(state, method);
 * console.log("method:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @see {@link dictBinding} Constructor
 * @see {@link addDict} Stateful add
 * @see {@link inferTraitMethodType} Lookup via binding
 * @see {@link TraitLamTerm} Ctx extension
 */
export type DictBinding = {
  dict: {
    name: string; // dictionary variable
    trait: string;
    type: Type;
  };
};

/**
 * Enum definition `enum name<params::kinds> { variants }` (algebraic data type).
 *
 * **Purpose**: **Parametric enums/ADTs**:
 * - **Kind**: Computed `params → *` (e.g., `* → *` for unary).
 * - **Variants**: Label → field scheme (uses unbound params).
 * - **Normalization** (`normalizeType`):
 *   - Non-recursive: `Either<t,u>` → `<Left:t | Right:u>`.
 *   - Recursive: `List<t>` → `μX.<Nil | Cons(t, X<t>)>`.
 * - **Validation** (`addEnum`): Fields `:: *`, self-refs → `recursive=true`.
 * Used for tagged unions, pattern matching.
 *
 * @typedef {Object} EnumDef
 * @property {string} name - Enum name (`"Option"`, `"Either"`)
 * @property {Kind} kind - Kind (`* → *`, `* → * → *`)
 * @property {string[]} params - Param names `["T"]`, `["L","R"]`
 * @property {Array<[string, FieldScheme]>} variants - Cases `[[label, scheme], ...]`
 * @property {boolean} recursive - Recursive? (self-refs → μ)
 *
 * @example Construction
 * ```ts
 * import { EnumDef, starKind, arrowKind, varType, tupleType } from "system-f-omega";
 *
 * const optionDef: EnumDef = {
 *   name: "Option",
 *   kind: arrowKind(starKind, starKind),
 *   params: ["T"],
 *   variants: [
 *     ["None", tupleType([])],
 *     ["Some", varType("T")]
 *   ],
 *   recursive: false
 * };
 * console.log("Option<T>:", JSON.stringify(optionDef));
 * ```
 *
 * @example addEnum (ctx binding)
 * ```ts
 * import { freshState, addType, addEnum, starKind, showContext } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 * console.log(showContext(state.ctx));  // "...Enum: Color = ..."
 * ```
 *
 * @example Normalization (non-recursive)
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const optInt = appType(conType("Option"), conType("Int"));
 * const expanded = normalizeType(state, optInt);
 * console.log("Option<Int> → < >:", showType(expanded));  // "<None: ⊥ | Some: Int>"
 * ```
 *
 * @example Recursive normalization (→ μ)
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;  // recursive=true
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const expanded = normalizeType(state, listInt);
 * console.log("List<Int> → μ:", showType(expanded));  // "μX0.<Nil: ⊥ | Cons: (Int, X0)>"
 * ```
 *
 * @see {@link addEnum} Context binding
 * @see {@link normalizeType} Expansion
 * @see {@link FieldScheme} Variant fields
 */
export type EnumDef = {
  name: string; // e.g., "Either"
  kind: Kind; // e.g., * → * → * (for two params)
  params: string[]; // param var names, e.g., ["t", "u"]
  variants: [string, FieldScheme][]; // variant label → field scheme (with param vars unbound)
  recursive: boolean;
};

/**
 * Field scheme for enum variants (unbound param types).
 *
 * **Purpose**: **Parametric variant fields**:
 * - Uses unbound `params`: `{var:"T"}` → `Int` after subst.
 * - Instantiates: `addEnum` → `normalizeType(app(Enum, args))`.
 * Examples: `None: ()`, `Some: T`, `Cons: (T, List<T>)`.
 *
 * @typedef {Type} FieldScheme
 *
 * @example Usage in variants
 * ```ts
 * import { FieldScheme, varType, tupleType } from "system-f-omega";
 *
 * const noneField: FieldScheme = tupleType([]);        // ()
 * const someField: FieldScheme = varType("T");         // T
 * const consField: FieldScheme = tupleType([varType("T"), varType("List")]);  // (T, List)
 * ```
 *
 * @see {@link EnumDef.variants} Container
 * @see {@link normalizeType} Instantiation
 */
export type FieldScheme = Type; // e.g., { var: "t" } for Left, unit for None

/**
 * Enum definition binding for context (`enum: EnumDef`).
 *
 * **Purpose**: Stores ADTs in `Γ` for:
 * - Normalization (`app(Enum, args)` → variants/μ).
 * - Pattern matching (`checkPattern` nominal lookup).
 * Used by `addEnum`.
 *
 * @typedef {Object} EnumDefBinding
 * @property {EnumDef} enum - ADT definition
 *
 * @example Construction
 * ```ts
 * import { EnumDefBinding, starKind, tupleType } from "system-f-omega";
 *
 * const colorBinding: EnumDefBinding = {
 *   enum: {
 *     name: "Color",
 *     kind: starKind,
 *     params: [],
 *     variants: [["Red", tupleType([])]],
 *     recursive: false
 *   }
 * };
 * console.log("EnumDefBinding:", JSON.stringify(colorBinding));
 * ```
 *
 * @example Context display
 * ```ts
 * import { freshState, addEnum, showContext, starKind, tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", tupleType([])]]).ok;
 * console.log(showContext(state.ctx));  // "Enum: Color = ..."
 * ```
 *
 * @see {@link EnumDef} Definition
 * @see {@link addEnum} Stateful add
 * @see {@link showBinding} Pretty-print
 */
export type EnumDefBinding = { enum: EnumDef };

/**
 * Context binding `Γ ⊢` entries for type checking.
 *
 * **Purpose**: **Typing environment** (`TypeCheckerState.ctx`):
 * - **Lookup**: Vars (`inferVarType`), types (`checkKind`), traits/dicts/enums.
 * - **Extension**: Lambdas (`inferLamType`), lets (`inferLetType`), patterns (`checkPattern`).
 * - **Stateful adds**: `addTerm/Type/TraitDef/Impl/Dict/Enum/Alias`.
 * - **Display**: `showContext` multi-line.
 * No duplicates (name-based).
 *
 * **Lookup order**: Term > Dict > Type > TraitDef > etc. (shadowing).
 *
 * | Variant | Syntax | Purpose |
 * |---------|--------|---------|
 * | `TermBinding` | `x : τ` | Value variables |
 * | `TypeBinding` | `α :: κ` | Type constructors/kind vars |
 * | `TraitDefBinding` | `trait T<P::κ> { m:τ }` | Trait interfaces |
 * | `TraitImplBinding` | `impl T for τ = dict` | Concrete evidence |
 * | `DictBinding` | `d : Dict<T,τ>` | Evidence variables (trait_lam) |
 * | `EnumDefBinding` | `enum E<P> { L:σ }` | Algebraic data types |
 * | `TypeAliasBinding` | `type A<P::κs> = τ` | Parametric synonyms |
 *
 * @typedef {Union} Binding
 * @type {TermBinding} `x : τ` - Term variable
 * @type {TypeBinding} `α :: κ` - Type constructor
 * @type {TraitDefBinding} `trait T` - Trait definition
 * @type {TraitImplBinding} `impl T for τ` - Trait implementation
 * @type {DictBinding} `d : Dict<T,τ>` - Dictionary variable
 * @type {EnumDefBinding} `enum E` - Algebraic data type
 * @type {TypeAliasBinding} `type A<P> = τ` - Type alias
 *
 * @example Construction (all variants)
 * ```ts
 * import {
 *   termBinding, typeBinding, traitDefBinding, traitImplBinding,
 *   dictBinding, enumDefBinding, typeAliasBinding,
 *   starKind, conType, varType, arrowType
 * } from "system-f-omega";
 *
 * // Term
 * const termB = termBinding("x", conType("Int"));
 *
 * // Type
 * const typeB = typeBinding("Int", starKind);
 *
 * // Trait def
 * const traitDB = traitDefBinding("Eq", "Self", starKind, [["eq", arrowType(varType("Self"), varType("Bool"))]]);
 *
 * // Trait impl
 * const implB = traitImplBinding("Eq", conType("Int"), { var: "eqDict" });
 *
 * // Dict
 * const dictB = dictBinding("eqInt", "Eq", conType("Int"));
 *
 * // Enum
 * const enumB = enumDefBinding("Color", starKind, [], [["Red", conType("Unit")]], false);
 *
 * // Alias
 * const aliasB = typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * ```
 *
 * @example Context building (add*)
 * ```ts
 * import { freshState, addType, addTerm, addTraitDef, addTraitImpl, addDict, addEnum, addTypeAlias, dictTerm, showContext, starKind } from "system-f-omega";
 * import { conType, conTerm, arrowType, varType, lamTerm, conTerm as cTerm } from "system-f-omega";
 *
 * let state = freshState();
 *
 * // Types
 * state = addType(state, "Int", starKind).ok;
 *
 * // Terms
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 *
 * // Traits
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(varType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("y", conType("Int"), cTerm("true", conType("Bool")))]]);
 * state = addTraitImpl(state, "Eq", conType("Int"), eqDict).ok;
 *
 * // Dicts
 * state = addDict(state, "eqInt", eqDict).ok;
 *
 * // Enums
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", conType("Unit")]]).ok;
 *
 * // Aliases
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * console.log(showContext(state.ctx));
 * // Multi-line: Term, Type, TraitDef, Impl, Dict, Enum, Alias
 * ```
 *
 * @example Inference lookups
 * ```ts
 * import { freshState, addType, addTerm, inferType, varTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;  // TypeBinding
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;  // TermBinding
 *
 * const result = inferType(state, varTerm("x"));  // Uses TermBinding
 * console.log("x:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link TypeCheckerState.ctx} Container
 * @see {@link showContext} Display
 * @see {@link addTerm/Type/TraitDef/Impl/Dict/Enum/Alias} Builders
 * @see {@link inferVarType} Term lookup
 * @see {@link checkKind} Type lookup
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
 * Typing context `Γ` (ordered list of bindings).
 *
 * **Purpose**: **Environment for bidirectional typing**:
 * - **Lookup**: `inferVarType` (terms/dicts), `checkKind` (types), trait/enum/alias resolution.
 * - **Extension**: Prepend for binders (`inferLamType`, `checkPattern`, `inferTylamType`).
 * - **Shadowing**: Later bindings override earlier (let, patterns).
 * - **Stateful**: `TypeCheckerState.ctx`, mutated by `add*`/`freshState`.
 * No duplicates (name-based via `addBinding`).
 *
 * **Search order**: Term > Dict > Type > TraitDef/Impl > Enum/Alias (first match).
 *
 * @typedef {Array<Binding>} Context
 *
 * @example Empty context
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(showContext(state.ctx));  // ""
 * ```
 *
 * @example Building context (add*)
 * ```ts
 * import { freshState, addType, addTerm, addTraitDef, showContext, starKind } from "system-f-omega";
 * import { conType, conTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;                    // TypeBinding
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok; // TermBinding
 * state = addTraitDef(state, "Eq", "A", starKind, []).ok;       // TraitDefBinding
 *
 * console.log(showContext(state.ctx));
 * // "Type: Int = *\nTerm: x = Int\nTrait: Eq = TraitDef (Eq A = *)"
 * ```
 *
 * @example Extension (lambda ctx)
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, conType, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * // inferLamType extends: [...ctx, {term: {name:"x", type:Int}}]
 * const result = inferType(state, id);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Pattern bindings (match ctx)
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const pat = recordPattern([["x", varPattern("a")]]);
 * const ty = recordType([["x", conType("Int")]]);
 * const bindings = checkPattern(state, pat, ty);  // [{term: {name:"a", type:Int}}]
 * console.log("extended ctx:", bindings.ok.length);  // 1
 * ```
 *
 * @see {@link TypeCheckerState.ctx} State field
 * @see {@link Binding} Entries
 * @see {@link showContext} Pretty-print
 * @see {@link addType/Term/TraitDef/Impl/Dict/Enum/Alias} Builders
 * @see {@link inferType} Uses ctx (recursive extension)
 * @see {@link checkKind} Type lookup
 */
export type Context = Binding[];

/**
 * Meta-environment for existential unification variables (`?N`).
 *
 * **Purpose**: **Tracks inference state** for `MetaType` (`?N`):
 * - **Freshening**: `counter` → sequential names, `kinds` assigns `?N :: κ`.
 * - **Solving**: `solutions` binds `?N := τ` (occurs-checked).
 * - **Resolution**: Follow chains (`applySubstitution`/`normalizeType`).
 * Central to **constraint solving** (`solveConstraints`).
 * Part of `TypeCheckerState.meta` (mutable, scoped).
 *
 * **Lifecycle**:
 * 1. `freshMetaVar(meta)` → `?N`, `kinds.set("?N", κ)`, `counter++`.
 * 2. Unify → `solveMetaVar(meta, "?N", τ)` → `solutions.set("?N", τ)`.
 * 3. Resolve → follow `solutions` (cycle-safe).
 *
 * @typedef {Object} MetaEnv
 * @property {Map<string, Type>} solutions - `?N → τ` (solved types)
 * @property {Map<string, Kind>} kinds - `?N → κ` (assigned kinds)
 * @property {number} counter - Next meta name (`?${counter++}`)
 *
 * @example Fresh state (empty)
 * ```ts
 * import { freshState } from "system-f-omega";
 *
 * const state = freshState();
 * console.log("empty:", state.meta.solutions.size === 0);  // true
 * console.log("counter:", state.meta.counter === 0);       // true
 * ```
 *
 * @example Fresh meta-var
 * ```ts
 * import { freshState, freshMetaVar } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta, starKind);
 * console.log("meta:", meta.evar);             // "?0"
 * console.log("kind:", state.meta.kinds.has("?0")); // true
 * console.log("counter:", state.meta.counter); // 1
 * ```
 *
 * @example Solving meta-var
 * ```ts
 * import { freshState, freshMetaVar, solveMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const result = solveMetaVar(state, meta.evar, conType("Int"));
 * console.log("solved:", "ok" in result);                  // true
 * console.log("solution:", state.meta.solutions.has("?0")); // true
 * ```
 *
 * @example Resolution (applySubstitution)
 * ```ts
 * import { freshState, freshMetaVar, applySubstitution, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * state.meta.solutions.set(meta.evar, conType("Int"));
 * const resolved = applySubstitution(state, new Map(), meta);
 * console.log("resolved:", resolved.con === "Int");  // true
 * ```
 *
 * @see {@link TypeCheckerState.meta} State field
 * @see {@link freshMetaVar} Creation/tracking
 * @see {@link solveMetaVar} Binding
 * @see {@link applySubstitution} Resolution
 * @see {@link occursCheckEvar} Cycle check
 * @see {@link freshState} Initializer
 */
export type MetaEnv = {
  solutions: Map<string, Type>; // evar -> Type
  kinds: Map<string, Kind>; // evar -> Kind
  counter: number;
};

/**
 * Type checker state (`Γ, meta`) for bidirectional inference/checking.
 *
 * **Purpose**: **Mutable environment**:
 * - **ctx**: Bindings (`addType/Term/Trait/Enum/Alias` → new state).
 * - **meta**: Unification vars (`freshMetaVar`, `solveMetaVar`).
 * - **Threaded**: Functions return `{ok: newState | err}` (immutable style).
 * - **Scoped extension**: Nested `inferLamType/checkPattern` → temp ctx.
 * Central to all APIs: `inferType`, `checkType`, `checkKind`, solvers.
 *
 * **Workflow**:
 * 1. `freshState()` → empty.
 * 2. `add*` → build bindings.
 * 3. `infer/check` → extend → solve → resolve.
 *
 * @typedef {Object} TypeCheckerState
 * @property {MetaEnv} meta - Unification variables (`?N`)
 * @property {Context} ctx - Bindings (`Γ`)
 *
 * @example Fresh state
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * console.log("empty ctx:", showContext(state.ctx));  // ""
 * console.log("empty meta:", state.meta.solutions.size === 0);  // true
 * ```
 *
 * @example Building state (add*)
 * ```ts
 * import { freshState, addType, addTerm, addTraitDef, showContext, starKind } from "system-f-omega";
 * import { conTerm, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, []).ok;
 *
 * console.log(showContext(state.ctx));
 * // "Type: Int = *\nTerm: x = Int\nTrait: Eq = TraitDef (Eq A = *)"
 * ```
 *
 * @example Inference (ctx/meta usage)
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = inferType(state, id);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Nested extension (lambda ctx)
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * // inferLamType: {ctx: [...state.ctx, {term: {name:"x", type:Int}}], meta}
 * const result = inferType(state, id);
 * console.log("ctx extended internally");
 * ```
 *
 * @example Meta solving
 * ```ts
 * import { freshState, freshMetaVar, solveMetaVar, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * solveMetaVar(state, meta.evar, conType("Int"));  // Mutates meta.solutions
 * console.log("solved:", state.meta.solutions.has(meta.evar));  // true
 * ```
 *
 * @see {@link freshState} Initializer
 * @see {@link addType/Term/TraitDef/Impl/Dict/Enum/Alias} Builders
 * @see {@link inferType} Synthesis
 * @see {@link checkType} Analysis
 * @see {@link MetaEnv} Unification state
 * @see {@link Context} Bindings
 * @see {@link showContext} Display
 */
export type TypeCheckerState = {
  meta: MetaEnv;
  ctx: Context;
};

/**
 * User-specified renaming map for `importModule` (qualified imports).
 *
 * **Purpose**: **Avoid conflicts** during module import:
 * - Maps **old names → new names** per category.
 * - **Optional**: Partial maps OK (unmapped → auto-fresh or error).
 * - **Categories**: Traits/types/terms/labels (records/variants).
 * Builds `renameType/Term/Pattern/Binding` maps via `buildRenameMap`.
 *
 * **Workflow** (`importModule`):
 * 1. User `aliases` → `finalRen` (user + auto-fresh deps).
 * 2. Rename deps → append to target ctx.
 *
 * @typedef {Object} ImportAliases
 * @property {Record<string,string>} [traits] - `"Eq" → "PartialEq"`
 * @property {Record<string,string>} [types] - `"Int32" → "Int"`
 * @property {Record<string,string>} [terms] - `"add" → "plus"`
 * @property {Record<string,string>} [labels] - `"x" → "fieldX"`, `"Left" → "L"`
 *
 * @example Basic aliases (types/traits)
 * ```ts
 * import { ImportAliases } from "system-f-omega";
 *
 * const aliases: ImportAliases = {
 *   types: { "Int32": "Int" },
 *   traits: { "Eq": "PartialEq" }
 * };
 * console.log("aliases:", JSON.stringify(aliases));
 * ```
 *
 * @example importModule with aliases
 * ```ts
 * import { freshState, addType, importModule, starKind, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int32", starKind).ok;  // Will rename
 *
 * let into = freshState();
 * const result = importModule({
 *   from,
 *   into,
 *   roots: ["Int32"],
 *   aliases: { types: { "Int32": "Int" } }
 * });
 * console.log("imported as 'Int':", "ok" in result);
 * console.log(showContext(result.ok.ctx));  // "Type: Int = *"
 * ```
 *
 * @example Labels (records/variants)
 * ```ts
 * import { freshState, addType, importModule, starKind, recordType, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from.ctx.push({ type: { name: "Point", kind: starKind } });  // Assume Point def
 *
 * let into = freshState();
 * const result = importModule({
 *   from,
 *   into,
 *   roots: ["Point"],
 *   aliases: { labels: { "x": "xCoord", "y": "yCoord" } }  // Rename fields
 * });
 * console.log("labels renamed:", "ok" in result);
 * ```
 *
 * @example Full multi-category
 * ```ts
 * import { ImportAliases } from "system-f-omega";
 *
 * const fullAliases: ImportAliases = {
 *   traits: { "Eq": "PartialEq", "Ord": "Compare" },
 *   types: { "Int32": "Int", "UInt": "Nat" },
 *   terms: { "add": "plus", "mul": "times" },
 *   labels: { "Left": "L", "Right": "R" }
 * };
 * console.log("full:", JSON.stringify(fullAliases));
 * ```
 *
 * @see {@link importModule} Primary usage
 * @see {@link renameType/Term/Pattern/Binding} Apply renames
 * @see {@link buildRenameMap} Internal map builder
 * @see {@link collectDependencies} Dep collection (pre-rename)
 */
export type ImportAliases = {
  traits?: Record<string, string>;
  types?: Record<string, string>;
  terms?: Record<string, string>;
  labels?: Record<string, string>;
};

/**
 * Creates fresh checker state (empty meta, optional ctx).
 *
 * **Purpose**: Initializer for inference/checking:
 * - **Meta reset**: `counter=0`, empty `solutions/kinds`.
 * - **Ctx seed**: Optional initial bindings.
 * Used as `freshState()` or `freshState(existingCtx)`.
 *
 * @param ctx - Initial bindings (defaults `[]`)
 * @returns Fresh `{meta, ctx}`
 *
 * @example Empty state
 * ```ts
 * import { freshState, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * console.log(showContext(state.ctx));  // ""
 * ```
 *
 * @example Seeded
 * ```ts
 * import { freshState, typeBinding, starKind } from "system-f-omega";
 *
 * const seeded = freshState([{ type: { name: "Int", kind: starKind } }]);
 * console.log("seeded Int");
 * ```
 *
 * @see {@link TypeCheckerState} Full state
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
 * Unbound type identifier error (missing type var/constructor).
 *
 * **Purpose**: Reports unbound names in kinding/checking:
 * - **Type vars**: `checkVarKind` → no ctx `TypeBinding`.
 * - **Constructors**: `checkConKind` → no `TypeBinding`/`EnumDefBinding`/`TypeAliasBinding`.
 * - **Lenient mode**: Assumes `*` (subtyping/bottom), strict → error.
 * Common in unbound polymorphism, missing imports.
 *
 * @typedef {Object} UnboundTypeError
 * @property {string} unbound - Missing name (`"a"`, `"MissingType"`)
 *
 * @example Construction
 * ```ts
 * import { UnboundTypeError } from "system-f-omega";
 *
 * const err: UnboundTypeError = { unbound: "Missing" };
 * console.log(JSON.stringify(err));  // { "unbound": "Missing" }
 * ```
 *
 * @example checkKind failure (unbound var)
 * ```ts
 * import { freshState, checkKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = checkKind(state, { var: "a" });  // No binding
 * console.log("unbound var:", "unbound" in result.err);  // true
 * console.log(showError(result.err));  // "Unbound identifier: a"
 * ```
 *
 * @example checkKind failure (unbound con)
 * ```ts
 * import { freshState, checkKind, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = checkKind(state, { con: "Foo" });  // No addType("Foo")
 * console.log("unbound con:", "unbound" in result.err);  // true
 * console.log(showError(result.err));  // "Unbound identifier: Foo"
 * ```
 *
 * @example Lenient unbound (assumes *)
 * ```ts
 * import { freshState, checkKind, varType, starKind, showKind } from "system-f-omega";
 *
 * const state = freshState();
 * const result = checkKind(state, { var: "a" }, true);  // lenient=true
 * console.log("lenient *: ", showKind(result.ok));  // "*"
 * ```
 *
 * @example Real inference failure
 * ```ts
 * import { freshState, inferType, lamTerm, varTerm, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const badLam = lamTerm("x", { var: "Missing" }, varTerm("x"));  // Unbound domain
 * const result = inferType(state, badLam);
 * console.log("inference err:", showError(result.err));  // Propagates unbound
 * ```
 *
 * @see {@link checkKind} Primary producer (var/con lookup)
 * @see {@link checkVarKind} Type var case
 * @see {@link checkConKind} Constructor/alias/enum case
 * @see {@link showError} User-facing message
 * @see {@link addType} Binds constructors
 */
export type UnboundTypeError = { unbound: string };

/**
 * Kind mismatch error (type has wrong kind).
 *
 * **Purpose**: Reports ill-formed types:
 * - **HKT app**: `List<Int>` requires `List :: * → *` (wrong arity/kind).
 * - **Binders**: `∀a::κ.τ` requires `body :: *` (concrete).
 * - **Data fields**: Records/variants/tuples/enum fields → `*` only.
 * - **Method sigs**: Trait methods `:: *`.
 * Triggered by `checkKind` helpers (`checkAppKind`, `checkLamKind`, etc.).
 *
 * @typedef {Object} KindMismatchTypeError
 * @property {Object} kind_mismatch
 * @property {Kind} kind_mismatch.expected - Expected kind
 * @property {Kind} kind_mismatch.actual - Actual kind
 *
 * @example Construction
 * ```ts
 * import { KindMismatchTypeError, starKind, arrowKind } from "system-f-omega";
 *
 * const err: KindMismatchTypeError = {
 *   kind_mismatch: { expected: starKind, actual: arrowKind(starKind, starKind) }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example HKT application (wrong arity)
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, arrowKind, showError, showKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;  // * → *
 * state = addType(state, "Int", starKind).ok;
 *
 * const wrongApp = appType(appType(conType("List"), conType("Int")), conType("Bool"));  // List<Int,Bool> (wrong!)
 * const result = checkKind(state, wrongApp);
 * console.log("error:", showError(result.err));  // "Kind mismatch: Expected: * Actual: (* → *)"
 * ```
 *
 * @example Record field not concrete
 * ```ts
 * import { freshState, checkKind, recordType, arrowKind, starKind, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const badRec = recordType([["f", arrowKind(starKind, starKind)]]);  // Field not *
 * const result = checkKind(state, badRec);
 * console.log("bad field:", showError(result.err));  // "Kind mismatch: Expected: * Actual: (* → *)"
 * ```
 *
 * @example Wrong binder kind (forall body)
 * ```ts
 * import { freshState, checkKind, forallType, arrowKind, starKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const badForall = forallType("a", starKind, arrowKind(starKind, starKind));  // Body not *
 * const result = checkKind(state, badForall);
 * console.log("bad body:", showError(result.err));  // "Kind mismatch: Expected: * Actual: (* → *)"
 * ```
 *
 * @example User-facing via inference
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, varType, starKind, arrowKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;  // HKT
 * const badLam = lamTerm("x", { con: "List" }, varTerm("x"));  // List not * (arg)
 * const result = inferType(state, badLam);
 * console.log("inference kind err:", showError(result.err));  // Propagates kind_mismatch
 * ```
 *
 * @see {@link checkKind} Primary producer
 * @see {@link checkAppKind} HKT apps
 * @see {@link checkRecordKind} Data fields
 * @see {@link checkForallKind} Binders
 * @see {@link kindsEqual} Equality check
 * @see {@link showError} Formatted message
 */
export type KindMismatchTypeError = {
  kind_mismatch: { expected: Kind; actual: Kind };
};

/**
 * Type mismatch error (incompatible types).
 *
 * **Purpose**: Reports unification/subsumption failures:
 * - **Rigid-rigid**: `Int ~ Bool` (structural `typesEqual` fail).
 * - **Checking**: `checkType` inferred ≰ expected.
 * - **Patterns**: Con mismatch, record/tuple fields/length.
 * - **Apps**: Arg ≰ domain.
 * - **Traits**: Method sig/impl, dict type/trait.
 * Triggered by `unifyTypes`/`subsumes` after normalization.
 *
 * @typedef {Object} TypeMismatchTypeError
 * @property {Object} type_mismatch
 * @property {Type} type_mismatch.expected - Expected type
 * @property {Type} type_mismatch.actual - Inferred/actual type
 *
 * @example Construction
 * ```ts
 * import { TypeMismatchTypeError, conType } from "system-f-omega";
 *
 * const err: TypeMismatchTypeError = {
 *   type_mismatch: { expected: conType("Int"), actual: conType("Bool") }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Unification failure (rigid-rigid)
 * ```ts
 * import { freshState, unifyTypes, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: any[] = [];
 * const subst = new Map<string, any>();
 * const result = unifyTypes(state, conType("Int"), conType("Bool"), worklist, subst);
 * console.log("unify err:", showError(result.err));
 * // "Type mismatch:
 * //   Expected: Int
 * //   Actual:   Bool"
 * ```
 *
 * @example Lambda checking (domain mismatch)
 * ```ts
 * import { freshState, addType, checkType, lamTerm, varTerm, arrowType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const boolId = lamTerm("x", conType("Bool"), varTerm("x"));
 * const intExpected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, boolId, intExpected);
 * console.log("domain err:", showError(result.err));
 * // "Type mismatch:
 * //   Expected: (Int → Int)
 * //   Actual:   (Bool → Bool)"
 * ```
 *
 * @example Record pattern mismatch
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["x", varPattern("a")]]);
 * const wrongTy = recordType([["y", conType("Bool")]]);  // Wrong label
 * const result = checkPattern(state, pat, wrongTy);
 * console.log("record err:", showError(result.err));
 * // "Missing field 'x' in record: {y: Bool}"
 * ```
 *
 * @example Function app arg mismatch
 * ```ts
 * import { freshState, addType, addTerm, inferType, appTerm, varTerm, lamTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * const intId = lamTerm("x", conType("Int"), varTerm("x"));
 * state = addTerm(state, "intId", intId).ok;
 *
 * const badApp = appTerm(varTerm("intId"), conTerm("true", conType("Bool")));
 * const result = inferType(state, badApp);
 * console.log("app arg err:", showError(result.err));
 * // Propagates via unification: "Type mismatch: Expected: Int Actual: Bool"
 * ```
 *
 * @see {@link unifyTypes} Primary producer (rigid-rigid)
 * @see {@link subsumes} Subtyping failure
 * @see {@link checkType} Inference ≰ expected
 * @see {@link checkPattern} Pattern mismatches
 * @see {@link showError} Formatted display
 * @see {@link typesEqual} Early structural check
 */
export type TypeMismatchTypeError = {
  type_mismatch: { expected: Type; actual: Type };
};

/**
 * Not-a-function error (callee not applicable).
 *
 * **Purpose**: Application on non-function:
 * - **Callee inference**: Not arrow/foralls/bounded_forall.
 * - **Triggers**: `Int f`, `42 7`, record projection misuse.
 * Reports callee type (after normalization).
 * From `inferAppType` post-instantiation check.
 *
 * @typedef {Object} NotAFunctionTypeError
 * @property {Type} not_a_function - Callee type (non-function)
 *
 * @example Construction
 * ```ts
 * import { NotAFunctionTypeError, conType } from "system-f-omega";
 *
 * const err: NotAFunctionTypeError = { not_a_function: conType("Int") };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example App on constant
 * ```ts
 * import { freshState, addType, inferType, appTerm, conTerm, varTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const badApp = appTerm(conTerm("42", conType("Int")), varTerm("x"));
 * const result = inferType(state, badApp);
 * console.log("error:", showError(result.err));  // "Not a function: Int"
 * ```
 *
 * @example App on record
 * ```ts
 * import { freshState, addType, inferType, appTerm, recordTerm, conTerm, varTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const badApp = appTerm(rec, varTerm("arg"));
 * const result = inferType(state, badApp);
 * console.log("record callee:", showError(result.err));  // "Not a function: {x: Int}"
 * ```
 *
 * @example App on variant
 * ```ts
 * import { freshState, inferType, appTerm, injectTerm, conTerm, varTerm, conType, variantType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const inj = injectTerm("Left", conTerm("42", conType("Int")), variantType([["Left", conType("Int")]]));
 * const badApp = appTerm(inj, varTerm("arg"));
 * const result = inferType(state, badApp);
 * console.log("variant callee:", showError(result.err));  // "Not a function: <Left: Int | ...>"
 * ```
 *
 * @see {@link inferAppType} Primary producer
 * @see {@link appTerm} Application constructor
 * @see {@link showError} "Not a function: τ"
 */
export type NotAFunctionTypeError = { not_a_function: Type };

/**
 * Not-a-type-function error (type app on non-HKT).
 *
 * **Purpose**: Type application on non-constructor:
 * - **Kind check**: `checkAppKind` → `func :: κ₁ → κ₂` required.
 * - **Triggers**: `Int<Bool>`, `a<b>` (non-arrow func).
 * Reports `func` type (after normalization).
 * From HKT saturation failures.
 *
 * @typedef {Object} NotATypeFunctionTypeError
 * @property {Type} not_a_type_function - Non-HKT func type
 *
 * @example Construction
 * ```ts
 * import { NotATypeFunctionTypeError, conType } from "system-f-omega";
 *
 * const err: NotATypeFunctionTypeError = { not_a_type_function: conType("Int") };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example App on primitive (Int<Bool>)
 * ```ts
 * import { freshState, addType, checkKind, appType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;  // Int :: * (not * → *)
 * state = addType(state, "Bool", starKind).ok;
 *
 * const badApp = appType(conType("Int"), conType("Bool"));
 * const result = checkKind(state, badApp);
 * console.log("error:", showError(result.err));  // "Not a type-level function: Int"
 * ```
 *
 * @example App on var (non-arrow)
 * ```ts
 * import { freshState, checkKind, appType, varType, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const badApp = appType(varType("a"), conType("Int"));  // a not arrow
 * const result = checkKind(state, badApp, true);  // lenient
 * console.log("var func:", showError(result.err));  // "Not a type-level function: a"
 * ```
 *
 * @example Real inference failure (HKT misuse)
 * ```ts
 * import { freshState, addType, inferType, appTerm, varTerm, lamTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;  // Primitive, not HKT
 * const id = lamTerm("x", appType(conType("Int"), conType("Bool")), varTerm("x"));  // Bad domain
 * const result = inferType(state, id);
 * console.log("inference err:", showError(result.err));  // Propagates via kind_mismatch or not_a_type_function
 * ```
 *
 * @see {@link checkAppKind} Primary producer
 * @see {@link appType} Type app constructor
 * @see {@link checkKind} Caller
 * @see {@link showError} "Not a type-level function: τ"
 */
export type NotATypeFunctionTypeError = { not_a_type_function: Type };

/**
 * Cyclic type error (infinite type detected).
 *
 * **Purpose**: Prevents loops in unification/normalization:
 * - **Occurs check**: `α` free in `τ` → reject `α := τ` (`unifyVariable`/`solveMetaVar`).
 * - **Meta cycles**: `?N` in `τ` → reject binding (`occursCheckEvar`).
 * - **Degenerate μ**: `μX.X` → cyclic (`unifyTypes`).
 * - **Normalization**: Cycle → unchanged/`⊥` (guarded `seen`).
 * Common in self-recursive unification without proper binders.

 * @typedef {Object} CyclicTypeError
 * @property {string} cyclic - Cyclic variable (`"a"`, `"?0"`, `"X"`)
 *
 * @example Construction
 * ```ts
 * import { CyclicTypeError } from "system-f-omega";
 *
 * const err: CyclicTypeError = { cyclic: "?0" };
 * console.log(JSON.stringify(err));  // { "cyclic": "?0" }
 * ```
 *
 * @example Occurs check (meta cycle)
 * ```ts
 * import { freshState, freshMetaVar, occursCheckEvar, arrowType } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const cyclicTy = arrowType(meta, varType("Int"));  // ?0 → Int
 * console.log("cycle:", occursCheckEvar(state.meta, meta.evar, cyclicTy));  // true
 * ```
 *
 * @example solveMetaVar rejection
 * ```ts
 * import { freshState, freshMetaVar, solveMetaVar, arrowType } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const cyclicTy = arrowType(meta, varType("Int"));
 * const result = solveMetaVar(state, meta.evar, cyclicTy);
 * console.log("rejected:", "cyclic" in result.err);  // true
 * ```
 *
 * @example Var occurs check (rigid cycle)
 * ```ts
 * import { occursCheck, arrowType, varType } from "system-f-omega";
 *
 * const cyclicTy = arrowType(varType("a"), varType("Int"));  // a → Int
 * console.log("a occurs:", occursCheck("a", cyclicTy));  // true
 * ```
 *
 * @example User-facing via unification
 * ```ts
 * import { freshState, unifyTypes, arrowType, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map<string, Type>();
 * const worklist: any[] = [];
 * const result = unifyTypes(state, varType("a"), arrowType(varType("a"), varType("Int")), worklist, subst);
 * console.log("unify cycle:", showError(result.err));  // "Cyclic type detected involving: a"
 * ```
 *
 * @see {@link occursCheck} Rigid var check
 * @see {@link occursCheckEvar} Meta check
 * @see {@link solveMetaVar} Binding rejection
 * @see {@link unifyVariable} Rigid-flex cycle
 * @see {@link normalizeType} Cycle guard (`seen`)
 * @see {@link showError} "Cyclic type detected involving: X"
 */
export type CyclicTypeError = { cyclic: string };

/**
 * Not-a-record error (projection/pattern on non-record type).
 *
 * **Purpose**: Record operations on non-record:
 * - **Projection** (`inferProjectType`): `e.l` where `e : Int`.
 * - **Patterns** (`checkRecordPattern`): `{x:p}` on `Int`.
 * Reports actual type (after normalization).
 *
 * @typedef {Object} NotARecordTypeError
 * @property {Type} not_a_record - Non-record type
 *
 * @example Construction
 * ```ts
 * import { NotARecordTypeError, conType } from "system-f-omega";
 *
 * const err: NotARecordTypeError = { not_a_record: conType("Int") };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Projection on constant
 * ```ts
 * import { freshState, addType, inferType, projectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const num = conTerm("42", conType("Int"));
 * const proj = projectTerm(num, "x");  // Int.x
 * const result = inferType(state, proj);
 * console.log("error:", showError(result.err));  // "Not a record type: Int"
 * ```
 *
 * @example Projection on variant
 * ```ts
 * import { freshState, inferType, projectTerm, injectTerm, conTerm, conType, variantType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const varn = injectTerm("Left", conTerm("42", conType("Int")), variantType([["Left", conType("Int")]]));
 * const proj = projectTerm(varn, "x");  // Variant.x
 * const result = inferType(state, proj);
 * console.log("variant proj:", showError(result.err));  // "Not a record type: <Left: Int | ...>"
 * ```
 *
 * @example Record pattern on non-record
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["x", varPattern("a")]]);
 * const result = checkPattern(state, pat, conType("Int"));
 * console.log("pattern err:", showError(result.err));  // "Not a record type: Int"
 * ```
 *
 * @see {@link inferProjectType} Projection producer
 * @see {@link checkRecordPattern} Pattern producer
 * @see {@link projectTerm} Record access
 * @see {@link recordPattern} Record destructuring
 * @see {@link showError} "Not a record type: τ"
 */
export type NotARecordTypeError = { not_a_record: Type };

/**
 * Missing field error (record lacks required label).
 *
 * **Purpose**: Field access/pattern on absent label:
 * - **Projection** (`inferProjectType`): `e.l` where `l ∉ record`.
 * - **Patterns** (`checkRecordPattern`): `{l:p}` where `l ∉ record` (exact match).
 * Reports record type + missing label (post-normalization).
 *
 * @typedef {Object} MissingFieldTypeError
 * @property {Object} missing_field
 * @property {Type} missing_field.record - Record type
 * @property {string} missing_field.label - Missing label
 *
 * @example Construction
 * ```ts
 * import { MissingFieldTypeError, recordType, conType } from "system-f-omega";
 *
 * const err: MissingFieldTypeError = {
 *   missing_field: { record: recordType([["x", conType("Int")]]), label: "y" }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Projection (missing field)
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);  // No "y"
 * const projY = projectTerm(rec, "y");
 * const result = inferType(state, projY);
 * console.log("error:", showError(result.err));  // "Missing field 'y' in record: {x: Int}"
 * ```
 *
 * @example Record pattern (label mismatch)
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["y", varPattern("b")]]);  // Expects "y"
 * const ty = recordType([["x", conType("Int")]]);      // Has "x"
 * const result = checkPattern(state, pat, ty);
 * console.log("pattern err:", showError(result.err));  // "Missing field 'y' in record: {x: Int}"
 * ```
 *
 * @see {@link inferProjectType} Projection producer
 * @see {@link checkRecordPattern} Pattern producer
 * @see {@link projectTerm} Field access
 * @see {@link recordPattern} Destructuring
 * @see {@link showError} "Missing field 'l' in record: τ"
 */
export type MissingFieldTypeError = {
  missing_field: { record: Type; label: string };
};

/**
 * Not-a-variant error (variant op on non-variant type).
 *
 * **Purpose**: Variant operations on non-variant:
 * - **Injection** (`inferInjectType`): `<L=e> as Int`.
 * - **Patterns** (`checkPattern` variant): `L(p)` on `Int`/record.
 * Reports actual type (post-normalization).
 *
 * @typedef {Object} NotAVariantTypeError
 * @property {Type} not_a_variant - Non-variant type
 *
 * @example Construction
 * ```ts
 * import { NotAVariantTypeError, conType } from "system-f-omega";
 *
 * const err: NotAVariantTypeError = { not_a_variant: conType("Int") };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Injection on primitive
 * ```ts
 * import { freshState, inferType, injectTerm, conTerm, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const badInject = injectTerm("Left", conTerm("42", conType("Int")), conType("Int"));  // Int not variant
 * const result = inferType(state, badInject);
 * console.log("error:", showError(result.err));  // "Not a variant type: Int"
 * ```
 *
 * @example Variant pattern on record
 * ```ts
 * import { freshState, addType, checkPattern, variantPattern, varPattern, recordType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = variantPattern("Left", varPattern("x"));
 * const ty = recordType([["x", conType("Int")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("pattern err:", showError(result.err));  // "Not a variant type: {x: Int}"
 * ```
 *
 * @example Variant pattern on primitive
 * ```ts
 * import { freshState, addType, checkPattern, variantPattern, varPattern, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = variantPattern("Left", varPattern("x"));
 * const result = checkPattern(state, pat, conType("Int"));
 * console.log("primitive err:", showError(result.err));  // "Not a variant type: Int"
 * ```
 *
 * @see {@link inferInjectType} Injection producer
 * @see {@link checkPattern} Pattern producer (variant case)
 * @see {@link injectTerm} Variant constructor
 * @see {@link variantPattern} Variant destructuring
 * @see {@link showError} "Not a variant type: τ"
 */
export type NotAVariantTypeError = { not_a_variant: Type };

/**
 * Invalid variant label error (label not in variant/enum).
 *
 * **Purpose**: Wrong label in patterns/injections:
 * - **Patterns** (`checkPattern` variant): `Some(p)` on `Option` without `Some`.
 * - **Injections** (`inferInjectType`): `<Bad=e> as Option`.
 * Nominal: No matching variant in enum def.
 * Reports variant type + label (post-normalization).
 *
 * @typedef {Object} InvalidVariantTypeError
 * @property {Object} invalid_variant_label
 * @property {Type} invalid_variant_label.variant - Variant/enum type
 * @property {string} invalid_variant_label.label - Invalid label
 *
 * @example Construction
 * ```ts
 * import { InvalidVariantTypeError, appType, conType } from "system-f-omega";
 *
 * const err: InvalidVariantTypeError = {
 *   invalid_variant_label: { variant: appType(conType("Option"), conType("Int")), label: "Bad" }
 * };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Pattern (nominal enum, missing label)
 * ```ts
 * import { freshState, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind, showError } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", tupleType([])]]).ok;  // Only None
 *
 * const result = checkPattern(state, variantPattern("Some", varPattern("x")), appType(conType("Option"), conType("Int")));
 * console.log("error:", showError(result.err));  // "Invalid variant label 'Some' for: Option<Int>"
 * ```
 *
 * @example Injection (wrong label)
 * ```ts
 * import { freshState, addEnum, inferType, injectTerm, conTerm, appType, conType, starKind, showError } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", tupleType([])]]).ok;  // Only None
 *
 * const badInject = injectTerm("Some", conTerm("42", conType("Int")), appType(conType("Option"), conType("Int")));
 * const result = inferType(state, badInject);
 * console.log("inject err:", showError(result.err));  // "Invalid variant label 'Some' for: Option<Int>"
 * ```
 *
 * @example Structural variant (missing case)
 * ```ts
 * import { freshState, checkPattern, variantPattern, varPattern, variantType, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = variantType([["Left", conType("Int")]]);  // Only Left
 * const result = checkPattern(state, variantPattern("Right", varPattern("x")), ty);
 * console.log("structural err:", showError(result.err));  // "Invalid variant label 'Right' for: <Left: Int>"
 * ```
 *
 * @see {@link checkPattern} Pattern producer (variant case)
 * @see {@link inferInjectType} Injection producer
 * @see {@link variantPattern} Wrong label usage
 * @see {@link injectTerm} Wrong label usage
 * @see {@link showError} "Invalid variant label 'L' for: τ"
 */
export type InvalidVariantTypeError = {
  invalid_variant_label: { variant: Type; label: string };
};

/**
 * Missing case error (non-exhaustive match).
 *
 * **Purpose**: Pattern match misses variant/enum case:
 * - **Nominal**: Enum labels not covered (`checkExhaustive` enum lookup).
 * - **Structural**: Variant labels missing.
 * Reports **first** uncovered label (sorted).
 * Used in `inferMatchType` → requires exhaustive.
 *
 * @typedef {Object} MissingCaseTypeError
 * @property {Object} missing_case
 * @property {string} missing_case.label - First missing label
 *
 * @example Construction
 * ```ts
 * import { MissingCaseTypeError } from "system-f-omega";
 *
 * const err: MissingCaseTypeError = { missing_case: { label: "Blue" } };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Nominal enum (missing case)
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", { var: "Unit" }],
 *   ["Blue", { var: "Unit" }]
 * ]).ok;
 *
 * const patterns = [variantPattern("Red", varPattern("x"))];  // Missing Blue
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("error:", showError(result.err));  // "Non-exhaustive match: missing case 'Blue'"
 * ```
 *
 * @example Structural variant (missing case)
 * ```ts
 * import { freshState, checkExhaustive, variantPattern, varPattern, variantType, conType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const patterns = [variantPattern("Left", varPattern("x"))];
 * const ty = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 * const result = checkExhaustive(state, patterns, ty);
 * console.log("structural err:", showError(result.err));  // "Non-exhaustive match: missing case 'Right'"
 * ```
 *
 * @example Match inference failure
 * ```ts
 * import { freshState, addEnum, inferType, matchTerm, variantPattern, varPattern, conTerm, appType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", { var: "Unit" }],
 *   ["Blue", { var: "Unit" }]
 * ]).ok;
 *
 * const scrut = conTerm("c", conType("Color"));
 * const incomplete = matchTerm(scrut, [[variantPattern("Red", varPattern("x")), conTerm("red", conType("String"))]]);  // Missing Blue
 * const result = inferType(state, incomplete);
 * console.log("inference err:", showError(result.err));  // Propagates missing_case
 * ```
 *
 * @see {@link checkExhaustive} Primary producer
 * @see {@link inferMatchType} Match inference (requires exhaustive)
 * @see {@link variantPattern} Common culprit
 * @see {@link showError} "Non-exhaustive match: missing case 'L'"
 */
export type MissingCaseTypeError = { missing_case: { label: string } };

/**
 * Extra case error (match covers unreachable/non-existent label).
 *
 * **Purpose**: Patterns include labels not in variant/enum:
 * - **Exhaustiveness** (`checkExhaustive`): Extra patterns (over-coverage).
 * - Reports **first** extra label (conservative warning).
 * Used in safe matching (warn unreachable cases).
 *
 * @typedef {Object} ExtraCaseTypeError
 * @property {Object} extra_case
 * @property {string} extra_case.label - Extra/unreachable label
 *
 * @example Construction
 * ```ts
 * import { ExtraCaseTypeError } from "system-f-omega";
 *
 * const err: ExtraCaseTypeError = { extra_case: { label: "Extra" } };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Extra pattern label
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", { var: "Unit" }]]).ok;  // Only Red
 *
 * const patterns = [
 *   variantPattern("Red", varPattern("x")),
 *   variantPattern("Extra", varPattern("y"))  // Extra!
 * ];
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("error:", showError(result.err));  // "Unreachable case in match: 'Extra'"
 * ```
 *
 * @see {@link checkExhaustive} Producer (over-coverage)
 * @see {@link showError} "Unreachable case in match: 'L'"
 */
export type ExtraCaseTypeError = { extra_case: { label: string } };

/**
 * Not-a-tuple error (tuple op on non-tuple type).
 *
 * **Purpose**: Tuple operations on non-tuple:
 * - **Projection** (`inferTupleProjectType`): `e.i` where `e : Int`.
 * - **Patterns** (`checkTuplePattern`): `(p1,p2)` on `Int`/record.
 * Reports actual type (post-normalization).
 *
 * @typedef {Object} NotATupleTypeError
 * @property {Type} not_a_tuple - Non-tuple type
 *
 * @example Construction
 * ```ts
 * import { NotATupleTypeError, conType } from "system-f-omega";
 *
 * const err: NotATupleTypeError = { not_a_tuple: conType("Int") };
 * console.log(JSON.stringify(err));
 * ```
 *
 * @example Projection on constant
 * ```ts
 * import { freshState, addType, inferType, tupleProjectTerm, conTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const num = conTerm("42", conType("Int"));
 * const proj = tupleProjectTerm(num, 0);  // Int.0
 * const result = inferType(state, proj);
 * console.log("error:", showError(result.err));  // "Not a tuple type: Int"
 * ```
 *
 * @example Tuple pattern on record
 * ```ts
 * import { freshState, addType, checkPattern, tuplePattern, varPattern, recordType, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = tuplePattern([varPattern("a")]);
 * const ty = recordType([["x", conType("Int")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("pattern err:", showError(result.err));  // "Not a tuple type: {x: Int}"
 * ```
 *
 * @see {@link inferTupleProjectType} Projection producer
 * @see {@link checkTuplePattern} Pattern producer
 * @see {@link tupleProjectTerm} Tuple access
 * @see {@link tuplePattern} Tuple destructuring
 * @see {@link showError} "Not a tuple type: τ"
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
