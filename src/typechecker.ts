// ./src/typechecker.ts
import type {
  AppTerm,
  AppType,
  ArrowType,
  Binding,
  BoundedForallType,
  ConPattern,
  Constraint,
  ConType,
  Context,
  DictTerm,
  FieldScheme,
  FoldTerm,
  ForallType,
  FreePatternNames,
  FreeTermNames,
  FreeTypeNames,
  HasKindConstraint,
  HasTypeConstraint,
  ImportAliases,
  InjectTerm,
  Kind,
  KindEqConstraint,
  LamTerm,
  LamType,
  LetTerm,
  MatchTerm,
  MetaEnv,
  MetaType,
  MuType,
  Pattern,
  ProjectTerm,
  RecordPattern,
  RecordTerm,
  RecordType,
  Result,
  Substitution,
  Term,
  TraitAppTerm,
  TraitConstraint,
  TraitLamTerm,
  TraitMethodTerm,
  TuplePattern,
  TupleProjectTerm,
  TupleTerm,
  TupleType,
  TyAppTerm,
  TyLamTerm,
  Type,
  TypeCheckerState,
  TypeEqConstraint,
  TypingError,
  UnfoldTerm,
  VariantType,
  VarTerm,
  VarType,
  Worklist,
} from "./types.js";
import { err, getSpineArgs, ok, showType } from "./types.js";

/**
 * Constructs a **type equality constraint** `left = right` for the unification
 * solver.
 *
 * ```
 * typeEq(A, Int)
 *   → { type_eq: { left: A, right: Int } }
 * ```
 *
 * **What it represents**
 * `typeEq` is a helper that wraps two types into a {@link TypeEqConstraint},
 * which is the core unit of work for the constraint‑based unification engine.
 *
 * These constraints are processed by:
 * - {@link solveConstraints}
 * - {@link processConstraint}
 * - {@link unifyTypes}
 *
 * Anytime the typechecker needs to enforce that two types must be equal—
 * whether in function application, pattern checking, subsumption, or trait
 * validation—it emits a `typeEq` constraint.
 *
 * **Why it's useful**
 * Type equality constraints support:
 * - incremental unification
 * - deferred constraint solving
 * - pairing unification with kind checking
 * - higher‑kinded polymorphism
 * - trait resolution
 *
 * They simplify inference rules: instead of immediately unifying, rules simply
 * generate constraints, and the solver does the rest.
 *
 * **Related**
 * - {@link TypeEqConstraint} — the object produced by this function
 * - {@link KindEqConstraint} — analogous for kinds
 * - {@link HasTypeConstraint} — deferred type check
 * - {@link unifyTypes} — main unification algorithm
 *
 * **Examples**
 *
 * Creating a simple constraint:
 * ```ts
 * import { typeEq, varType, conType } from "system-f-omega";
 *
 * const c = typeEq(varType("A"), conType("Int"));
 * // { type_eq: { left: A, right: Int } }
 * ```
 *
 * Adding constraints to a worklist:
 * ```ts
 * import { typeEq } from "system-f-omega";
 *
 * const worklist = [];
 * worklist.push(typeEq(leftType, rightType));
 * ```
 *
 * Solving constraints:
 * ```ts
 * import {
 *   typeEq, solveConstraints,
 *   varType, conType, freshState
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 *
 * const worklist = [typeEq(varType("X"), conType("Int"))];
 * solveConstraints(state, worklist, subst);
 *
 * console.log(subst.get("X"));  // { con: "Int" }
 * ```
 */
export const typeEq = (left: Type, right: Type): TypeEqConstraint => ({
  type_eq: { left, right },
});

/**
 * Constructs a **kind equality constraint** `left = right` for the kind
 * unification solver.
 *
 * ```
 * kindEq(*, * → *)
 *   → { kind_eq: { left: *, right: (* → *) } }
 * ```
 *
 * **What it represents**
 * `kindEq` wraps two kinds into a {@link KindEqConstraint}, which expresses the
 * requirement:
 *
 * > “These two kinds must be equal.”
 *
 * These constraints are consumed by the solver (via {@link solveConstraints})
 * and unified structurally using {@link unifyKinds}.
 *
 * Kind equality constraints arise when:
 * - Checking type application (`F<T>`)
 * - Verifying type lambda binders (`ΛF::κ. e`)
 * - Instantiating polymorphic types (`∀A::κ. τ`)
 * - Validating enum/alias definitions
 * - Ensuring record/variant fields are of kind `*`
 *
 * **Why it's useful**
 * `kindEq` supports:
 * - Higher‑kinded polymorphism (System F‑ω)
 * - Reasoning about type constructors (`* → *`, `(* → *) → *`, ...)
 * - Delayed kind checking (paired with {@link HasKindConstraint})
 * - Ensuring type application respects arity and expected shapes
 *
 * It allows kind checking to work incrementally rather than requiring full
 * information up‑front.
 *
 * **Related**
 * - {@link KindEqConstraint} — the object this function produces
 * - {@link unifyKinds} — actual kind unification logic
 * - {@link checkAppKind} — generates kindEq constraints for type application
 * - {@link HasKindConstraint} — deferred kind checking constraint
 *
 * **Examples**
 *
 * Creating a simple kind equality:
 * ```ts
 * import { kindEq, starKind } from "system-f-omega";
 *
 * const c = kindEq(starKind, starKind);
 * // { kind_eq: { left: *, right: * } }
 * ```
 *
 * Adding a kind constraint to a worklist:
 * ```ts
 * const worklist = [];
 * worklist.push(kindEq(starKind, starKind));
 * ```
 *
 * Solving kind constraints:
 * ```ts
 * import {
 *   solveConstraints, kindEq,
 *   starKind, arrowKind, freshState, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 *
 * const eq = kindEq(starKind, starKind); // valid
 * console.log("ok" in solveConstraints(state, [eq]));  // true
 *
 * const bad = kindEq(starKind, arrowKind(starKind, starKind)); // mismatch
 * const r = solveConstraints(state, [bad]);
 * console.log(showError(r.err)); // "Kind mismatch: Expected: * Actual: (* → *)"
 * ```
 */
export const kindEq = (left: Kind, right: Kind): KindEqConstraint => ({
  kind_eq: { left, right },
});

/**
 * Creates a **deferred kind-checking constraint** of the form:
 *
 * ```
 * Γ ⊢ ty : kind
 * ```
 *
 * wrapped as a {@link HasKindConstraint}.
 *
 * **What it represents**
 * `hasKind` packages a request to check that:
 *
 * > “Type `ty` has kind `kind`, using the provided `state`.”
 *
 * Instead of performing the kind check immediately, this constraint is added to
 * the solver’s worklist and processed later by {@link processConstraint} inside
 * {@link solveConstraints}.
 *
 * This allows kind checking to be delayed until:
 * - meta‑variables have been solved
 * - type applications have normalized
 * - alias/enum expansions have settled
 *
 * **Why it's useful**
 * Higher‑kinded type systems (like System F‑ω) often require *deferred*
 * constraints:
 *
 * - Checking the kind of a type may depend on earlier unification steps
 * - Some kinds only become known after solving type equations
 * - Kind checking must wait until certain type forms have normalized
 *
 * `hasKind` allows the typechecker to queue these checks safely.
 *
 * **Where it is used**
 * - Generated during kind checking for type applications
 * - Used in polymorphic and higher‑kinded inference paths
 * - May be emitted by subsumption and alias expansion logic
 * - Ultimately handled by {@link processConstraint}
 *
 * **Related**
 * - {@link HasKindConstraint} — the constraint object produced
 * - {@link kindEq} — added after a deferred kind check succeeds
 * - {@link checkKind} — actual kind inference/checking logic
 * - {@link solveConstraints} — solves deferred checks
 *
 * **Examples**
 *
 * Creating a simple deferred kind check:
 * ```ts
 * import { hasKind, conType, starKind, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const constraint = hasKind(conType("Int"), starKind, state);
 * // { has_kind: { ty: Int, kind: *, state } }
 * ```
 *
 * Adding it to a solver worklist:
 * ```ts
 * import { hasKind, solveConstraints, starKind, conType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [hasKind(conType("Int"), starKind, state)];
 *
 * console.log("ok" in solveConstraints(state, worklist));  // true
 * ```
 *
 * A failing deferred kind check:
 * ```ts
 * import {
 *   hasKind, lamType, starKind, arrowKind,
 *   freshState, solveConstraints, showError
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const ty = lamType("A", starKind, { var: "A" });  // * → *
 *
 * const res = solveConstraints(state, [hasKind(ty, starKind, state)]);
 * console.log(showError(res.err));
 * // Kind mismatch: Expected: * Actual: (* → *)
 * ```
 */
export const hasKind = (
  ty: Type,
  kind: Kind,
  state: TypeCheckerState,
): HasKindConstraint => ({
  has_kind: { ty, kind, state },
});

/**
 * Creates a **deferred type‑checking constraint**:
 *
 * ```
 * Γ ⊢ term : ty
 * ```
 *
 * wrapped as a {@link HasTypeConstraint}.
 *
 * **What it represents**
 * `hasType` tells the constraint solver:
 *
 * > “Later, infer the type of `term` in `state`, and unify it with `ty`.”
 *
 * Instead of immediately calling {@link inferType}, the typechecker delays the
 * operation, placing a constraint into the worklist.  
 * This is essential when the type of a subterm depends on unification still in
 * progress.
 *
 * **Why it's useful**
 * Deferred type checking enables:
 *
 * - **Constraint‑based inference** (collect constraints first, solve later)  
 * - Handling complex expressions such as:
 *   - dictionaries and trait method checking  
 *   - let‑bindings  
 *   - match branches  
 *   - polymorphic instantiation  
 * - Avoiding premature errors when meta‑variables (`?N`) are unresolved  
 * - Ordering‑independent unification
 *
 * This mechanism is especially important for features like:
 * - bounded polymorphism (trait constraints)  
 * - higher‑rank type inference  
 * - dictionary validation (`inferDictType`)
 *
 * **How it is processed**
 * In {@link processConstraint}, the solver:
 * 1. Calls `inferType(state, term)` to synthesize a type  
 * 2. Adds a {@link TypeEqConstraint} equating the inferred type with `ty`  
 * 3. Continues solving the worklist recursively  
 *
 * **Where it is used**
 * - Dictionary checking in {@link inferDictType}  
 * - Let‑binding checking  
 * - Pattern checking and variant handling  
 - Trait method resolution  
 - Subsumption and general type checking
 *
 * **Related**
 * - {@link HasTypeConstraint} — the structure produced  
 * - {@link TypeEqConstraint} — added after deferred inference  
 * - {@link inferType} — performs actual synthesis  
 * - {@link solveConstraints} — processes deferred operations  
 *
 * **Examples**
 *
 * Creating a deferred type check:
 * ```ts
 * import { hasType, lamTerm, varTerm, conType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const term = lamTerm("x", conType("Int"), varTerm("x"));
 *
 * const constraint = hasType(term, conType("Bool"), state);
 * // { has_type: { term: λx:Int.x, ty: Bool, state } }
 * ```
 *
 * Solving a deferred check (this will fail):
 * ```ts
 * import { solveConstraints, hasType, conType, freshState, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = solveConstraints(
 *   state,
 *   [hasType({ var: "x" }, conType("Int"), state)],
 *   new Map()
 * );
 *
 * console.log(showError(result.err));  // likely "Unbound identifier: x"
 * ```
 *
 * A valid deferred check:
 * ```ts
 * import {
 *   hasType, solveConstraints, lamTerm,
 *   varTerm, conType, freshState
 * } from "system-f-omega";
 *
 * const state = freshState();
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 *
 * const res = solveConstraints(state, [hasType(id, conType("Int → Int"), state)], new Map());
 * console.log("ok" in res);  // true
 * ```
 */
export const hasType = (
  term: Term,
  ty: Type,
  state: TypeCheckerState,
): HasTypeConstraint => ({
  has_type: { term, ty, state },
});

/**
 * The mode flag used by {@link inferTypeWithMode} to control **bidirectional**
 * typechecking:
 *
 * - `{ infer: null }` → *infer mode*  (`Γ ⊢ e ⇒ τ`)
 * - `{ check: Type }` → *check mode*  (`Γ ⊢ e ⇐ τ`)
 *
 * **What it represents**
 * `InferMode` distinguishes between:
 *
 * 1. **Inference mode**
 *    The typechecker attempts to *synthesize* the type of an expression with no
 *    prior expectation. This is the default mode.
 *
 * 2. **Checking mode**
 *    The typechecker verifies that an expression has a *specific* type supplied
 *    by the caller.
 *    Useful for lambdas, annotated expressions, pattern bodies, and trait
 *    applications.
 *
 * This dual‑mode system enables a more expressive and predictable typechecker
 * (a standard technique in bidirectional type systems).
 *
 * **Why it's useful**
 * Bidirectional typing gives:
 * - clearer inference for lambdas (whose types cannot be inferred blindly)
 * - better error messages
 * - more flexible polymorphism and trait‑bounded checking
 * - compatibility with partially annotated code
 *
 * `InferMode` is a lightweight and convenient way to pass this mode between
 * functions.
 *
 * **Where it's used**
 * - {@link inferTypeWithMode} — dispatches to `inferType` or `checkType`
 * - Trait apps, lambdas, type app/lambda, and other expression forms
 *
 * **Related**
 * - {@link inferType} — synthesizes a type
 * - {@link checkType} — validates against an expected type
 * - {@link Type} — expected type for check mode
 *
 * **Examples**
 *
 * Using inference mode:
 * ```ts
 * import { inferTypeWithMode, inferMode, lamTerm, varTerm, conType } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = inferTypeWithMode(state, id, inferMode);
 * // infers: (Int → Int)
 * ```
 *
 * Using check mode:
 * ```ts
 * import { inferTypeWithMode, checkMode, arrowType, conType } from "system-f-omega";
 *
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * const result = inferTypeWithMode(state, someTerm, checkMode(expected));
 * ```
 *
 * Pattern:
 * ```ts
 * const mode: InferMode = { check: conType("Int") };
 * ```
 */
export type InferMode =
  | { infer: null } // Synthesize a type
  | { check: Type }; // Check against an expected type

/**
 * A convenient constant representing **inference mode**.
 */
export const inferMode = { infer: null };

/**
 * A helper for constructing **checking mode** with an expected type.
 *
 * @param check - The type the expression must be checked against.
 * @returns An {@link InferMode} value indicating check mode.
 */
export const checkMode = (check: Type) => ({ check });

/**
 * Bidirectional type inference **dispatcher**.
 *
 * This function selects between:
 *
 * - **Inference mode** (`{ infer: null }`)
 *   Compute a type for the term with no prior expectation
 *   → `inferType(state, term)`
 *
 * - **Checking mode** (`{ check: expectedType }`)
 *   Verify that the term has the given expected type
 *   → `checkType(state, term, expectedType)`
 *
 * It always returns a **final Type** (not a `{ type, subst }` pair), so both
 * modes have a consistent public interface.
 *
 * Why this exists:
 * - Bidirectional typing improves error messages (especially for lambdas)
 * - Checking mode allows the caller to guide inference
 * - Inference mode keeps ordinary expressions annotation‑free
 *
 * Related:
 * - {@link InferMode} — mode union type
 * - {@link inferMode} / {@link checkMode} — constructors
 * - {@link inferType} — synthesis
 * - {@link checkType} — checking
 * - {@link TypeCheckerState}, {@link Term}, {@link Type}
 *
 * @param state - The current typechecker state (environment + meta‑vars)
 * @param term - The expression whose type we want to infer or check
 * @param mode - Either `{ infer: null }` or `{ check: Type }`
 *
 * @returns A type for `term`, or a {@link TypingError}
 *
 * @example Inferring a type
 * ```ts
 * const result = inferTypeWithMode(state, lamTerm("x", Int, varTerm("x")), inferMode);
 * // => ok(Int → Int)
 * ```
 *
 * @example Checking a type
 * ```ts
 * const expected = arrowType(Int, Bool);
 * const result = inferTypeWithMode(state, someTerm, checkMode(expected));
 * // => ok(expected) or an error if the term doesn’t match
 * ```
 */
export function inferTypeWithMode(
  state: TypeCheckerState,
  term: Term,
  mode: InferMode,
): Result<TypingError, Type> {
  // Delegate based on mode
  if ("check" in mode) {
    const result = checkType(state, term, mode.check);
    if ("ok" in result) return ok(result.ok.type);
    return result;
  }
  return inferType(state, term);
}

/**
 * The **base kind** `*` (“star kind”) used for ordinary, fully‑applied types.
 *
 * What it represents:
 * - `*` classifies **value‑level types** — types that describe actual runtime
 *   values.
 * - Examples:
 *   - `Int :: *`
 *   - `Bool :: *`
 *   - `List<Int> :: *`
 *
 * Why it's important:
 * - `*` is the **terminal kind** in the kind system.
 * - Any type you can store in a variable, pass to a function, or return as a
 *   result must have kind `*`.
 * - Higher‑kinded types (like `List :: * → *`) are built *from* `*` using
 *   {@link arrowKind}.
 *
 * Used in:
 * - Type declarations: `addType(state, "Int", starKind)`
 * - Type parameter binders: `forallType("A", starKind, ...)`
 * - Kind checking: ensuring a type is concrete before using it as a value
 *
 * Related:
 * - {@link Kind} — the full kind grammar
 * - {@link arrowKind} — constructs higher‑kinded arrows
 * - {@link checkKind} — verifies kinds during typechecking
 *
 * @example Declaring a primitive type:
 * ```ts
 * addType(state, "Bool", starKind);  // Bool :: *
 * ```
 *
 * @example As a polymorphic binder:
 * ```ts
 * const id = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * // ∀A::*. A → A
 * ```
 */
export const starKind: Kind = { star: null };

/**
 * The **bottom type** `⊥` (read: “bottom”), represented as `neverType`.
 *
 * What it represents:
 * - A type with **no possible values**.
 * - It describes computations that never return, unreachable code paths, or
 *   logically impossible values.
 *
 * Analogues in other languages:
 * - Haskell: `Void`
 * - TypeScript: `never`
 * - Scala: `Nothing`
 *
 * Why it’s useful:
 * - **Subtyping**:
 *   `⊥ <: τ` for *any* type `τ`.
 *   This means a program can pretend that bottom has *any* type—useful for code
 *   paths that cannot occur.
 *
 * - **Unification** (special rule):
 *   - `⊥ ~ τ` succeeds whenever `τ :: *`
 *   - but `τ ~ ⊥` only succeeds if `τ` is also `⊥`
 *   This asymmetry maintains type safety during inference.
 *
 * - **Pattern matching**:
 *   A pattern scrutinee of type `⊥` is considered exhaustive—no cases can occur.
 *
 * - **Normalization fallback**:
 *   - Empty variants (e.g., `< >`) normalize to `⊥`
 *   - Detecting impossible recursive types collapses to `⊥`
 *
 * Related:
 * - {@link isBottom} — checks if a type normalizes to `⊥`
 * - {@link unifyTypes} — handles bottom‑type unification rules
 * - {@link Type} — includes `NeverType` as one of its forms
 *
 * @example Direct bottom:
 * ```ts
 * console.log(showType(neverType));  // "⊥"
 * ```
 *
 * @example Subtyping:
 * ```ts
 * isAssignableTo(state, neverType, conType("Int"));  // true
 * ```
 *
 * @example Normalization of empty variant:
 * ```ts
 * const empty = variantType([]);       // < >
 * const norm = normalizeType(state, empty);
 * console.log(isBottom(state, norm));  // true
 * ```
 */
export const neverType = { never: null };

/**
 * Merges two **type substitutions** into a single substitution map.
 *
 * What it represents:
 * - During type inference, constraints are solved in **layers**:
 *   - **Global substitutions** come from long‑lived meta‑variable solutions
 *     (`state.meta.solutions`)
 *   - **Local substitutions** come from solving a specific unification or
 *     checking task (e.g. inside `checkType` or `inferAppType`)
 *
 * `mergeSubsts` combines these two environments so downstream code sees the
 * most up‑to‑date solutions.
 *
 * Merge rule:
 * - **Local overrides global**: if both maps bind the same variable name,
 *   the local binding wins. This is safe because unification guarantees
 *   consistency between them.
 *
 * Why it's useful:
 * - Ensures new solutions discovered in a sub‑computation propagate upward
 * - Prevents stale solutions from shadowing newer ones
 * - Used during lambda checking, application checking, and match branches
 *
 * Related:
 * - {@link Substitution} — the map structure being merged
 * - {@link solveConstraints} — produces local substitutions
 * - {@link applySubstitution} — consumes merged substitution maps
 *
 * @param local - A substitution produced by the current inference/checking step
 * @param globals - The persistent substitution map (e.g. `state.meta.solutions`)
 *
 * @returns A new substitution map where local solutions override global ones
 *
 * @example Local override:
 * ```ts
 * const globals = new Map([["a", conType("Int")]]);
 * const local   = new Map([["a", conType("Bool")], ["b", conType("String")]]);
 *
 * const merged = mergeSubsts(local, globals);
 * console.log(showType(merged.get("a"))); // "Bool" (local wins)
 * console.log(showType(merged.get("b"))); // "String"
 * ```
 *
 * @example No conflicts:
 * ```ts
 * const merged = mergeSubsts(local, new Map());
 * console.log(merged === local); // false, but same contents
 * ```
 */
export function mergeSubsts(
  local: Substitution,
  globals: Substitution,
): Substitution {
  const merge = new Map<string, Type>(globals); // Start with globals
  for (const [key, value] of local.entries()) {
    // Keep existing or merge - for now, keep local
    merge.set(key, value);
  }
  return merge;
}

/** Check is a given type is a meta (or existential) variable. */
export const isMetaVar = (type: Type): type is MetaType => "evar" in type;

/**
 * Creates a **fresh meta‑variable** (existential type variable) for type inference.
 *
 * What it represents:
 * - A meta‑variable `?N` stands for an **unknown type** that will be solved later.
 * - Meta‑vars behave like placeholders created during:
 *   - instantiating polymorphic types (`∀A. τ`)
 *   - inferring lambda argument types
 *   - solving trait constraints
 *   - unifying partially known types
 *
 * How it works:
 * - Allocates a new name like `?0`, `?1`, `?2`, … using a counter stored in
 *   the {@link MetaEnv}.
 * - Records the meta‑variable’s **kind** in `env.kinds`, so later kind checking
 *   knows what kind of type it must unify with.
 * - The new meta‑var is added *unsolved*. Its eventual solution will be placed
 *   in `env.solutions`.
 *
 * Why it’s needed:
 * - Higher‑order type inference (System F‑ω) relies heavily on fresh unknowns.
 * - Meta‑vars allow the typechecker to proceed before all type information
 *   is known. Unification and constraint solving later fill in the correct types.
 * - This is the core mechanism behind Hindley–Milner‑style inference and
 *   polymorphic instantiation.
 *
 * Related:
 * - {@link MetaType} — representation of a meta‑var
 * - {@link MetaEnv} — environment holding counters, kinds, and solutions
 * - {@link solveMetaVar} — assigns a concrete type to a meta‑var
 * - {@link instantiateType} — uses fresh meta‑vars to instantiate foralls
 *
 * @param env - The meta‑environment that stores the counter, kind map, and solutions
 * @param kind - The kind of this meta‑variable (defaults to `*`)
 *
 * @returns A new unsolved meta‑variable `{ evar: "?N" }`
 *
 * @example Creating a fresh meta‑variable:
 * ```ts
 * const state = freshState();
 * const mv = freshMetaVar(state.meta);
 * console.log(mv);  // { evar: "?0" }
 * console.log(state.meta.kinds.get("?0")); // "*"
 * ```
 *
 * @example Higher‑kinded meta‑var:
 * ```ts
 * const mv = freshMetaVar(state.meta, arrowKind(starKind, starKind));
 * // mv :: * → *
 * ```
 */
export function freshMetaVar(env: MetaEnv, kind: Kind = starKind): MetaType {
  const name = `?${env.counter++}`;
  env.kinds.set(name, kind);
  return { evar: name };
}

/**
 * Checks whether a type **normalizes to the bottom type** `⊥` (never type).
 *
 * What it does:
 * - Normalizes the input type (expanding aliases, enums, μ‑types).
 * - Returns `true` if the result is the bottom/never type.
 *
 * Why it matters:
 * - `⊥` represents an *uninhabited* or *impossible* type.
 * - Used in subtyping (`⊥ <: τ`), pattern exhaustiveness, and unification rules.
 *
 * @param state - Typechecker state for normalization
 * @param type - The type to test
 * @returns `true` if the type normalizes to `⊥`
 *
 * @example
 * ```ts
 * isBottom(state, neverType);          // true
 * isBottom(state, variantType([]));    // true (empty variant normalizes to ⊥)
 * ```
 */
export const isBottom = (state: TypeCheckerState, type: Type) =>
  "never" in normalizeType(state, type);

/**
 * Assigns a **solution type** to a meta‑variable (`?N`) during inference.
 *
 * What it does:
 * 1. If the meta‑var is **already solved**, checks the new solution for
 *    consistency (via {@link typesEqual}).
 * 2. If unsolved, runs an **occurs check** to prevent cyclic types.
 * 3. Records the solution in `state.meta.solutions`.
 *
 * Why it's important:
 * - Meta‑variables (`?N`) start as unknowns and are gradually solved by
 *   unification.
 * - This function is the *only safe way* to assign a solution.
 * - Prevents infinite types and ensures consistent inference.
 *
 * @param state - Typechecker state containing meta‑variable info
 * @param evar - The meta‑variable name (`"?0"`, `"?1"`, …)
 * @param solution - The type to assign to this meta‑variable
 * @returns `ok(null)` on success, or a {@link TypingError} on mismatch/cycle
 *
 * @example
 * ```ts
 * const mv = freshMetaVar(state.meta);   // ?0
 * solveMetaVar(state, mv.evar, conType("Int"));
 * // ?0 := Int
 * ```
 */
export function solveMetaVar(
  state: TypeCheckerState,
  evar: string,
  solution: Type,
): Result<TypingError, null> {
  // Case 1: evar already solved → unify with existing
  if (state.meta.solutions.has(evar)) {
    const existing = state.meta.solutions.get(evar)!;
    return typesEqual(state, existing, solution)
      ? ok(null)
      : err({ type_mismatch: { expected: existing, actual: solution } });
  }

  // Case 2: not solved yet → occurs check
  if (occursCheckEvar(state.meta, evar, solution)) return err({ cyclic: evar });

  // Insert new solution
  state.meta.solutions.set(evar, solution);

  return ok(null);
}

/**
 * Performs the **occurs check** for a meta‑variable.
 *
 * What it checks:
 * - Returns `true` if meta‑variable `evar` appears *anywhere* inside type `ty`.
 * - Follows solved meta‑vars recursively (e.g., `?1 := ?0`, so checking ?0 inside ?1 succeeds).
 *
 * Why it matters:
 * - Prevents assigning a meta‑variable a type that **contains itself**, which would
 *   create an infinite type such as:
 *   - `?0 := (?0 → Int)`
 * - Used by {@link solveMetaVar} to reject cyclic unification.
 *
 * How it recurses:
 * - Walks all type constructors: arrows, apps, records, variants, tuples, μ‑types.
 * - Ignores regular type variables (they are not meta‑vars).
 *
 * @param env - Meta‑environment containing current meta‑var solutions
 * @param evar - Meta‑variable name to search for (`"?0"`)
 * @param ty - Type to scan for occurrences of `evar`
 * @returns `true` if `evar` occurs in `ty`, otherwise `false`
 *
 * @example
 * ```ts
 * // ?0 appears inside (?0 → Int)
 * const ty = arrowType({ evar: "?0" }, conType("Int"));
 * occursCheckEvar(env, "?0", ty);  // true
 * ```
 *
 * @example
 * ```ts
 * // Following solved meta-vars:
 * env.solutions.set("?1", { evar: "?0" });
 * occursCheckEvar(env, "?0", { evar: "?1" });  // true
 * ```
 */
export function occursCheckEvar(env: MetaEnv, evar: string, ty: Type): boolean {
  if ("evar" in ty) {
    if (ty.evar === evar) return true;

    const sol = env.solutions.get(ty.evar);
    return sol ? occursCheckEvar(env, evar, sol) : false;
  }

  if ("var" in ty) return false;

  if ("arrow" in ty)
    return (
      occursCheckEvar(env, evar, ty.arrow.from) ||
      occursCheckEvar(env, evar, ty.arrow.to)
    );

  if ("app" in ty)
    return (
      occursCheckEvar(env, evar, ty.app.func) ||
      occursCheckEvar(env, evar, ty.app.arg)
    );

  if ("forall" in ty) return occursCheckEvar(env, evar, ty.forall.body);

  if ("bounded_forall" in ty)
    return (
      occursCheckEvar(env, evar, ty.bounded_forall.body) ||
      ty.bounded_forall.constraints.some((c) =>
        occursCheckEvar(env, evar, c.type),
      )
    );

  if ("record" in ty)
    return ty.record.some(([, t]) => occursCheckEvar(env, evar, t));

  if ("variant" in ty)
    return ty.variant.some(([, t]) => occursCheckEvar(env, evar, t));

  if ("tuple" in ty) return ty.tuple.some((t) => occursCheckEvar(env, evar, t));

  if ("mu" in ty) return occursCheckEvar(env, evar, ty.mu.body);

  return false;
}

/**
 * Instantiates **term‑level type lambdas** by replacing their bound type
 * variable with a fresh meta‑variable.
 *
 * This is the *term‑level* analogue of {@link instantiateType}:
 * - `instantiateType` handles `forall` at the *type* level.
 * - `instantiateTerm` handles `ΛA::κ. body` at the *term* level.
 *
 * Why this exists:
 * ---------------------------------------
 * A type‑lambda term:
 *   ΛA::*.  λx:A. x
 *
 * represents a polymorphic value.
 * To *use* it concretely, we must replace `A` with a fresh unknown type (a
 * meta‑variable), producing a monomorphic “instance”:
 *
 *   (λx:?0. x)
 *
 * This is exactly what `instantiateTerm` does: it walks the term, finds
 * `tylam` binders, and replaces their bound type variable with a new meta‑var,
 * producing an implicit `tyapp`.
 *
 * High‑level algorithm:
 * ---------------------------------------
 * For a term `ΛA::κ. body`:
 * 1. Recursively instantiate the body first (post‑order traversal).
 * 2. Create a fresh meta‑var `?N` with kind `κ`.
 * 3. Substitute `A ↦ ?N` inside the instantiated body.
 * 4. Return the term `(body[?N]) [?N]` — a type application.
 *
 * This ensures:
 * - each instantiation uses *fresh* unknown types
 * - nested polymorphic terms are handled bottom‑up
 * - type arguments in annotations and lambdas are also updated
 *
 * Used in:
 * - Dictionary instantiation during trait resolution
 * - Applying polymorphic values without explicit type arguments
 * - Auto‑instantiation via {@link autoInstantiate}
 *
 * Related:
 * - {@link freshMetaVar}
 * - {@link applySubstitutionToTerm}
 * - {@link instantiateType}
 * - {@link tyappTerm}
 *
 * @param state - The typechecker state used to generate fresh meta‑variables
 * @param term - A possibly polymorphic term containing type lambdas (`ΛA`)
 * @returns A new term where all outermost `tylam`s are instantiated
 */
export function instantiateTerm(state: TypeCheckerState, term: Term): Term {
  // Recurse first: Instantiate inner tytams (post-order)
  let instBody = term;
  if ("tylam" in term) {
    // For this tytam: Instantiate the body first (inner first)
    instBody = instantiateTerm(state, term.tylam.body);
    // Now, create fresh for this level and substitute it into the (already-instantiated) body
    const freshType = freshMetaVar(state.meta);
    const subst = new Map<string, Type>([[term.tylam.var, freshType]]);
    // Apply substitution to the body term (updates embedded types like lam.type; recurses on subterms)
    instBody = applySubstitutionToTerm(
      state,
      subst,
      instBody,
      new Set([term.tylam.var]),
    );
    // Return as tyapp: Apply the fresh type to the substituted body
    return tyappTerm(instBody, freshType);
  }

  // Recurse on non-tylam cases (e.g., app, lam, match, inject, dict, etc.)
  // Use the existing applySubstitutionToTerm pattern, but since no subst here, just recurse structurally
  if ("app" in term)
    return appTerm(
      instantiateTerm(state, term.app.callee),
      instantiateTerm(state, term.app.arg),
    );
  if ("lam" in term)
    return lamTerm(
      term.lam.arg,
      instantiateType(state, term.lam.type),
      instantiateTerm(state, term.lam.body),
    );
  if ("tyapp" in term)
    return tyappTerm(
      instantiateTerm(state, term.tyapp.term),
      instantiateType(state, term.tyapp.type),
    );
  if ("match" in term)
    return matchTerm(
      instantiateTerm(state, term.match.scrutinee),
      term.match.cases.map(([pattern, body]) => [
        pattern, // Patterns don't have types to instantiate (structural only)
        instantiateTerm(state, body),
      ]),
    );
  if ("inject" in term)
    return injectTerm(
      term.inject.label,
      instantiateTerm(state, term.inject.value),
      instantiateType(state, term.inject.variant_type), // Instantiate variant type
    );

  if ("dict" in term) {
    return dictTerm(
      term.dict.trait,
      instantiateType(state, term.dict.type),
      term.dict.methods.map(([name, impl]) => [
        name,
        instantiateTerm(state, impl),
      ]),
    );
  }
  if ("trait_lam" in term) {
    const t = term.trait_lam;
    return traitLamTerm(
      t.trait_var,
      t.trait,
      t.type_var,
      t.kind,
      t.constraints.map((c) => ({
        ...c,
        type: instantiateType(state, c.type),
      })),
      instantiateTerm(state, t.body),
    );
  }
  // Instantiate inner body, but don't substitute "Self" (constrained separately)
  // Add similar recursion for fold, unfold, record, project, tuple, let, etc. (structural)
  if ("record" in term)
    return recordTerm(
      term.record.map(([label, field]) => [
        label,
        instantiateTerm(state, field),
      ]),
    );

  if ("let" in term)
    return letTerm(
      term.let.name,
      instantiateTerm(state, term.let.value),
      instantiateTerm(state, term.let.body),
    );

  if ("tuple" in term)
    return tupleTerm(term.tuple.map((t) => instantiateTerm(state, t)));

  // Default: Recurse on any unrecognized (exhaustive on known constructors)
  return term;
}

/**
 * Instantiates **polymorphic types** by replacing bound type variables with
 * fresh meta‑variables.
 *
 * What it does:
 * ---------------------------------------
 * When you have a polymorphic type such as:
 *
 *   ∀A::*. A → A
 *
 * you cannot use it directly — it must be *instantiated* to a monomorphic
 * version:
 *
 *   ?0 → ?0
 *
 * where `?0` is a fresh meta‑variable representing an unknown concrete type.
 * `instantiateType` performs this instantiation automatically.
 *
 * How it works (high‑level):
 * ---------------------------------------
 * - If the type is a `forall`:
 *     1. Generate a fresh meta‑variable `?N`
 *     2. Substitute the bound variable with `?N` in the body
 *     3. Recurse, in case the body contains nested `forall`s
 *
 * - If the type is a `bounded_forall` (trait‑bounded polymorphism):
 *     Same steps as `forall`, except constraints are **not** resolved here.
 *     The constraints will be handled later (e.g., by trait application).
 *
 * - If the type contains no quantifier:
 *     Return it unchanged.
 *
 * Why it's important:
 * ---------------------------------------
 * - Needed for polymorphic function calls
 *   (`f : ∀A. A → A` → instantiate → `?0 → ?0`)
 * - Enables unification to assign concrete types later
 * - Prevents type variable capture by replacing them with meta‑vars
 * - Works for both standard System‑F polymorphism (`forall`) and the extended
 *   trait‑bounded polymorphism (`bounded_forall`)
 *
 * Related concepts:
 * - {@link instantiateTerm} — term‑level instantiation for `ΛA::κ. term`
 * - {@link freshMetaVar} — creates the meta‑variables used here
 * - {@link substituteType} — replaces the bound variable with `?N`
 * - {@link boundedForallType}, {@link forallType}
 *
 * @param state - Typechecker state providing fresh meta‑variables
 * @param type - A type that may contain universal quantifiers
 *
 * @returns A type with all outer quantifiers replaced by fresh meta‑variables
 *
 * @example Instantiating a polymorphic identity type:
 * ```ts
 * const poly = forallType("A", starKind, arrowType(varType("A"), varType("A")));
 * const inst = instantiateType(state, poly);
 * // inst is (?0 → ?0)
 * ```
 *
 * @example Bounded polymorphism:
 * ```ts
 * const bounded = boundedForallType("A", starKind, [{trait:"Eq", type:varType("A")}], varType("A"));
 * const inst = instantiateType(state, bounded);
 * // inst is ?0  (constraints handled elsewhere)
 * ```
 */
export function instantiateType(state: TypeCheckerState, type: Type): Type {
  if ("forall" in type) {
    const fv = freshMetaVar(state.meta);
    const instantiatedBody = substituteType(
      type.forall.var,
      fv,
      type.forall.body,
    );
    return instantiateType(state, instantiatedBody);
  }

  if ("bounded_forall" in type) {
    const fv = freshMetaVar(state.meta);

    // Instantiate constraints
    const instBody = substituteType(
      type.bounded_forall.var,
      fv,
      type.bounded_forall.body,
    );
    // Recurse (ignore constraints for now; assume provided externally)
    return instantiateType(state, instBody);
  }

  return type;
}

/**
 * Checks whether **`specific` is a subtype of `general`**
 * (i.e., whether `specific` *subsumes into* `general`).
 *
 * In traditional type theory this is written:
 *
 *    specific <: general
 *
 * but in our implementation the parameters appear as:
 *
 *    subsumes(state, general, specific, ...)
 *
 * because we check whether `specific` can be *used where* `general` is expected.
 *
 * ------------------------------------------------------------
 * Why this matters
 * ------------------------------------------------------------
 * Subsumption is used in:
 * - **Checking mode** (`checkType`) to see if inferred types match expectations
 * - **Pattern matching** (merging branch types)
 * - **Applying polymorphic terms**
 * - **Record width subtyping**
 *
 * This system uses a *structural* notion of subtyping combined with:
 * - instantiation of polymorphic types
 * - specialized rules for bottom (`⊥`)
 * - fallback to unification when possible
 *
 * ------------------------------------------------------------
 * High‑level rules implemented here
 * ------------------------------------------------------------
 *
 * 1. **Instantiate polymorphism in the general type**
 *    ```
 *    general = ∀A. τ   →   instantiateType → τ[A := ?0]
 *    ```
 *    This means:
 *    a polymorphic type is a supertype of *all its instances*.
 *
 * 2. **Bottom rules (`⊥`)**
 *    - `⊥ <: T` for any concrete type `T`
 *      (bottom is a subtype of everything — unreachable code is valid everywhere)
 *
 *    - `T <: ⊥` only if `T` is also `⊥`
 *      (you cannot treat real data as bottom)
 *
 * 3. **Otherwise, fall back to structural unification**
 *    `specific <: general`
 *    is approximated by trying to unify:
 *    ```
 *    unifyTypes(instGeneral, specific)
 *    ```
 *
 *    This works because unification:
 *    - checks structural compatibility
 *    - fills meta‑variables created during instantiation
 *    - handles record width subtyping, variants, mu‑types, etc.
 *
 * ------------------------------------------------------------
 * Summary of behavior:
 * ------------------------------------------------------------
 * - Polymorphic supertype? Instantiate it.
 * - `⊥` is always a valid subtype (except when the expected type is also ⊥).
 * - Otherwise: structural compatibility via unification.
 *
 * ------------------------------------------------------------
 * Related:
 * - {@link instantiateType} (step 1)
 * - {@link isBottom} (step 2)
 * - {@link unifyTypes} (step 3)
 * - {@link isAssignableTo} (simple fast-path version)
 * - {@link checkType} (primary caller)
 *
 * @param state - Current typechecker state
 * @param general - The expected supertype
 * @param specific - The inferred subtype
 * @param worklist - Constraint worklist passed to unification
 * @param subst - Substitution map mutated by unification
 *
 * @returns `ok(null)` if `specific` is a subtype of `general`, or an error
 *
 * @example Bottom subtype:
 * ```ts
 * subsumes(state, Int, ⊥)  // ok
 * ```
 *
 * @example Polymorphic supertype:
 * ```ts
 * ∀A. A → A   <:   Int → Int
 * // instantiate: ?0 → ?0
 * // unify:        ?0=Int → ok
 * ```
 *
 * @example Failure:
 * ```ts
 * subsumes(state, Bool, Int)
 * // err: type_mismatch
 * ```
 */
export function subsumes(
  state: TypeCheckerState,
  general: Type, // Supertype (e.g., t_ok)
  specific: Type, // Subtype (e.g., ⊥)
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  // Instantiate foralls in general
  const instGeneral = instantiateType(state, general);

  // Early bottom check: if specific is ⊥, always succeed (⊥ <: anything)
  if (isBottom(state, specific)) {
    const genKind = checkKind(state, instGeneral, true);
    if ("err" in genKind || !isStarKind(genKind.ok))
      return err({
        type_mismatch: { expected: instGeneral, actual: specific },
      });

    return ok(null);
  }

  // NEW: If general is ⊥, then specific must also be ⊥ (already checked above)
  if (isBottom(state, instGeneral)) {
    return err({
      type_mismatch: { expected: instGeneral, actual: specific },
    });
  }

  // Otherwise, standard unification
  return unifyTypes(state, instGeneral, specific, worklist, subst);
}

/**
 * Checks whether a type `from` can be **assigned to** a type `to`
 * (a lightweight, fast version of subtyping).
 *
 * What it does:
 * - Handles the two special rules for **bottom (`⊥`)**:
 *   - `⊥` is assignable to *any* type (`⊥ <: T`)
 *   - No type is assignable *to* `⊥` unless it is also `⊥`
 * - Otherwise, falls back to **structural type equality** after normalization.
 *
 * Why this exists:
 * - Many checks only need a *simple* notion of compatibility:
 *   - pattern checking
 *   - tuple/record element comparisons
 *   - constructor payload validation
 * - Full subtyping (`subsumes`) is more expensive and handles polymorphism,
 *   so this function provides a quick path when that power isn’t required.
 *
 * Related:
 * - {@link isBottom} — detects `⊥`
 * - {@link typesEqual} — structural equality used as the final check
 * - {@link subsumes} — the full subtyping engine (more general)
 *
 * @param state - Typechecker state used for normalization and bottom detection
 * @param from - The source type (value's type)
 * @param to - The target type (expected type)
 * @returns `true` if `from` is assignable to `to`, else `false`
 *
 * @example Bottom:
 * ```ts
 * isAssignableTo(state, neverType, conType("Int"));  // true
 * isAssignableTo(state, conType("Int"), neverType);  // false
 * ```
 *
 * @example Regular assignment:
 * ```ts
 * isAssignableTo(state, conType("Bool"), conType("Bool")); // true
 * isAssignableTo(state, conType("Int"),  conType("Bool")); // false
 * ```
 */
export function isAssignableTo(
  state: TypeCheckerState,
  from: Type,
  to: Type,
): boolean {
  if (isBottom(state, from)) return true; // ⊥ <: anything
  if (isBottom(state, to)) return isBottom(state, from); // anything <: ⊥ only if ⊥
  return typesEqual(state, from, to); // Otherwise, equality
}

/**
 * Extracts **variable bindings** from a pattern, producing a flat list of
 * `[name, placeholderType]` entries used to extend the typing context.
 *
 * What it does:
 * ---------------------------------------
 * When type‑checking a `match` expression, each pattern introduces **new
 * variables** that must be added to the context before checking the branch body.
 *
 * For example:
 *   - `x` binds `x`
 *   - `(x, y)` binds `x` and `y`
 *   - `{ point = (a, b) }` binds `a` and `b`
 *
 * This function walks the pattern **structurally** and collects all variable
 * names that appear inside it.
 *
 * The placeholder type:
 * ---------------------------------------
 * Each bound variable is assigned an **unknown type** `{ var: "$unknown" }`.
 * The real type is filled in later by `checkPattern`, which knows the scrutinee
 * type and can assign the correct concrete type.
 *
 * What it does **not** do:
 * - Does **not** check types
 * - Does **not** validate labels or constructors
 * - Does **not** resolve variant payloads
 *
 * It is purely a *name collector*.
 *
 * Pattern forms:
 * ---------------------------------------
 * - **Variable pattern** → one binding
 * - **Wildcard / constructor pattern** → no bindings
 * - **Record pattern** → recurse into each field
 * - **Variant pattern** → recurse into payload pattern
 * - **Tuple pattern** → recurse into each element
 *
 * Related:
 * - {@link checkPattern} — assigns the *actual* types to these bindings
 * - {@link Pattern} — the pattern AST
 * - {@link MatchTerm} — uses these bindings per branch
 *
 * @param pattern - The pattern to extract variable bindings from
 * @returns A flat array of `[name, placeholderType]`
 *
 * @example Variable:
 * ```ts
 * patternBindings(varPattern("x"));
 * // => [["x", { var: "$unknown" }]]
 * ```
 *
 * @example Tuple:
 * ```ts
 * patternBindings(tuplePattern([varPattern("a"), varPattern("b")]));
 * // => [["a", $unk], ["b", $unk]]
 * ```
 *
 * @example Nested:
 * ```ts
 * patternBindings(recordPattern([
 *   ["pt", tuplePattern([varPattern("x"), wildcardPattern()])]
 * ]));
 * // => [["x", $unknown]]
 * ```
 */
export function patternBindings(pattern: Pattern): [string, Type][] {
  if ("var" in pattern)
    // We'll need the type from context during type checking
    return [[pattern.var, { var: "$unknown" }]];
  if ("wildcard" in pattern) return [];
  if ("con" in pattern) return [];
  if ("record" in pattern) {
    const bindings: [string, Type][] = [];
    for (const [_, subPattern] of pattern.record) {
      bindings.push(...patternBindings(subPattern));
    }
    return bindings;
  }
  if ("variant" in pattern) {
    return patternBindings(pattern.variant.pattern);
  }
  if ("tuple" in pattern) {
    const b: [string, Type][] = [];
    for (const subp of pattern.tuple) {
      b.push(...patternBindings(subp));
    }
    return b;
  }
  return [];
}

// Helper function to apply substitution to terms (you'll need to add this)
function applySubstitutionToTerm(
  state: TypeCheckerState,
  subst: Substitution,
  term: Term,
  avoidFree: Set<string> = new Set(),
): Term {
  // Apply substitution to the types within the term structure

  if ("var" in term) return term;
  if ("lam" in term)
    return lamTerm(
      term.lam.arg,
      applySubstitution(state, subst, term.lam.type, avoidFree),
      applySubstitutionToTerm(state, subst, term.lam.body, avoidFree),
    );
  if ("app" in term)
    return appTerm(
      applySubstitutionToTerm(state, subst, term.app.callee, avoidFree),
      applySubstitutionToTerm(state, subst, term.app.arg, avoidFree),
    );
  if ("tylam" in term) {
    const newSubst = new Map(subst);
    newSubst.delete(term.tylam.var);

    return tylamTerm(
      term.tylam.var,
      term.tylam.kind,
      applySubstitutionToTerm(state, newSubst, term.tylam.body, avoidFree),
    );
  }
  if ("tyapp" in term)
    return tyappTerm(
      applySubstitutionToTerm(state, subst, term.tyapp.term, avoidFree),
      applySubstitution(state, subst, term.tyapp.type, avoidFree),
    );
  if ("con" in term)
    return conTerm(
      term.con.name,
      applySubstitution(state, subst, term.con.type, avoidFree),
    );
  if ("dict" in term)
    return dictTerm(
      term.dict.trait,
      applySubstitution(state, subst, term.dict.type, avoidFree),
      term.dict.methods.map(([name, methodTerm]) => [
        name,
        applySubstitutionToTerm(state, subst, methodTerm, avoidFree),
      ]),
    );
  if ("trait_lam" in term) {
    const newSubst = new Map(subst);
    newSubst.delete(term.trait_lam.type_var);

    const newConstraints = term.trait_lam.constraints.map((constraint) => ({
      ...constraint,
      type: applySubstitution(state, newSubst, constraint.type, avoidFree),
    }));

    return {
      trait_lam: {
        ...term.trait_lam,
        constraints: newConstraints,
        body: applySubstitutionToTerm(
          state,
          newSubst,
          term.trait_lam.body,
          avoidFree,
        ),
      },
    };
  }
  if ("trait_app" in term)
    return {
      trait_app: {
        term: applySubstitutionToTerm(
          state,
          subst,
          term.trait_app.term,
          avoidFree,
        ),
        type: applySubstitution(state, subst, term.trait_app.type, avoidFree),
        dicts: term.trait_app.dicts.map((dict) =>
          applySubstitutionToTerm(state, subst, dict, avoidFree),
        ),
      },
    };
  if ("trait_method" in term)
    return traitMethodTerm(
      applySubstitutionToTerm(state, subst, term.trait_method.dict, avoidFree),
      term.trait_method.method,
    );
  if ("let" in term)
    return letTerm(
      term.let.name,
      applySubstitutionToTerm(state, subst, term.let.value, avoidFree),
      applySubstitutionToTerm(state, subst, term.let.body, avoidFree),
    );
  if ("match" in term)
    return matchTerm(
      applySubstitutionToTerm(state, subst, term.match.scrutinee, avoidFree),
      term.match.cases.map(([pattern, body]) => [
        pattern, // Patterns don't contain types that need substitution
        applySubstitutionToTerm(state, subst, body, avoidFree),
      ]),
    );
  if ("record" in term)
    return recordTerm(
      term.record.map(([label, field]) => [
        label,
        applySubstitutionToTerm(state, subst, field, avoidFree),
      ]),
    );
  if ("project" in term)
    return projectTerm(
      applySubstitutionToTerm(state, subst, term.project.record, avoidFree),
      term.project.label,
    );
  if ("inject" in term)
    return injectTerm(
      term.inject.label,
      applySubstitutionToTerm(state, subst, term.inject.value, avoidFree),
      applySubstitution(state, subst, term.inject.variant_type, avoidFree),
    );
  if ("tuple" in term)
    return tupleTerm(
      term.tuple.map((t) =>
        applySubstitutionToTerm(state, subst, t, avoidFree),
      ),
    );
  if ("tuple_project" in term)
    return tupleProjectTerm(
      applySubstitutionToTerm(
        state,
        subst,
        term.tuple_project.tuple,
        avoidFree,
      ),
      term.tuple_project.index,
    );
  if ("fold" in term)
    return foldTerm(
      applySubstitution(state, subst, term.fold.type, avoidFree),
      applySubstitutionToTerm(state, subst, term.fold.term, avoidFree),
    );
  if ("unfold" in term)
    return unfoldTerm(
      applySubstitutionToTerm(state, subst, term.unfold, avoidFree),
    );
  // For other term constructors, recurse on subterms
  return term;
}

/**
 * Resolves a **trait implementation** (dictionary) for a given trait–type pair.
 *
 * In other words, this answers the question:
 *
 *    “Does type `T` implement trait `Trait`?
 *     If yes, return the dictionary (method table) for it.”
 *
 * This is the core of the **dictionary‑passing translation** used to implement
 * typeclasses / traits in System F‑ω.
 *
 * ------------------------------------------------------------
 * High‑level behavior
 * ------------------------------------------------------------
 *
 * Given a trait name and a concrete type:
 *
 *   checkTraitImplementation(state, "Eq", List<Int>)
 *
 * the function:
 * 1. Normalizes the target type (`normalizeType`)
 * 2. Searches for an **exact implementation**
 * 3. If none exists, tries **polymorphic implementations** by:
 *    - instantiating type parameters (fresh meta‑vars)
 *    - unifying impl type with the target type
 *    - solving constraints
 * 4. Instantiates the dictionary term accordingly
 * 5. Returns an error if no implementation fits
 *
 * ------------------------------------------------------------
 * Why this function is needed
 * ------------------------------------------------------------
 * - Trait applications (`f[Int] with {dict}`) rely on finding the correct dictionary.
 * - Bounded polymorphism (`∀Self where Eq<Self>. ...`) requires resolving trait
 *   constraints to actual evidence.
 * - Pattern matching, method calls, and auto‑instantiation also depend on this.
 *
 * This function is the **engine** that enables:
 * - “typeclass instance resolution”
 * - trait bounds
 * - polymorphic trait implementations
 *
 * ------------------------------------------------------------
 * Two categories of implementations it checks
 * ------------------------------------------------------------
 * 1. **Exact (monomorphic) instances**
 *    ```
 *    impl Eq<Int> = { eq = ... }
 *    ```
 *    If the target type normalizes to `Int`, the match is immediate.
 *
 * 2. **Polymorphic implementations**
 *    ```
 *    impl Eq<List<t>> = ...
 *    impl Functor<F> = ...
 *    ```
 *    These require:
 *    - normalizing both impl and target types
 *    - instantiating any `forall`
 *    - applying type‑lambdas if needed
 *    - unifying the impl type with the target type
 *    - instantiating the dictionary with the inferred substitutions
 *
 * ------------------------------------------------------------
 * Steps in the polymorphic path (simplified)
 * ------------------------------------------------------------
 * 1. Normalize impl type and target type
 * 2. Instantiate impl type (∀ vars → meta‑vars)
 * 3. If target type is a lambda constructor (HKT), apply it to fresh arguments
 *    until it is comparable to the impl type
 * 4. Attempt unification
 * 5. Solve resulting constraints
 * 6. Instantiate the dictionary term itself
 * 7. Apply solved substitutions to the dictionary
 *
 * If any step fails → the impl is not a match.
 *
 * ------------------------------------------------------------
 * Error behavior
 * ------------------------------------------------------------
 * If no implementation matches, returns:
 *
 *   { missing_trait_impl: { trait, type } }
 *
 * This is used by:
 * - bounded forall type checking
 * - trait applications
 * - auto‑instantiation of trait lambdas
 *
 * ------------------------------------------------------------
 * Related functions
 * ------------------------------------------------------------
 * - {@link normalizeType} — expands aliases, enums, lambdas before matching
 * - {@link instantiateType} — replaces quantified vars with meta‑vars
 * - {@link instantiateTerm} — freshens polymorphic dictionary terms
 * - {@link unifyTypes} — checks structural compatibility
 * - {@link solveConstraints} — resolves meta‑var bindings
 * - {@link checkTraitConstraints} — resolves multiple constraints
 *
 * ------------------------------------------------------------
 * @param state - Full typechecker state (context + meta‑vars)
 * @param trait - The trait name to resolve (e.g. `"Eq"`)
 * @param type - The concrete type for which we want an implementation
 *
 * @returns The instantiated dictionary term, or a `missing_trait_impl` error
 *
 * ------------------------------------------------------------
 * @example Exact implementation
 * ```ts
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqIntDict));
 * checkTraitImplementation(state, "Eq", conType("Int"));
 * // => ok(eqIntDict)
 * ```
 *
 * @example Polymorphic implementation
 * ```ts
 * // impl Eq<List<t>> { ... }
 * checkTraitImplementation(state, "Eq",
 *   appType(conType("List"), conType("Int")));
 * // => ok(dictionary specialized to Int)
 * ```
 *
 * @example Failure
 * ```ts
 * checkTraitImplementation(state, "Eq", conType("String"));
 * // => err({ missing_trait_impl: { trait: "Eq", type: String }})
 * ```
 */
export function checkTraitImplementation(
  state: TypeCheckerState,
  trait: string,
  type: Type,
): Result<TypingError, Term> {
  const normalizedType = normalizeType(state, type);

  // First, look for exact match
  const impl = state.ctx.find(
    (b) =>
      "trait_impl" in b &&
      b.trait_impl.trait === trait &&
      typesEqual(state, b.trait_impl.type, normalizedType),
  );

  if (impl && "trait_impl" in impl) return ok(impl.trait_impl.dict);

  const polymorphicImpls = state.ctx.filter(
    (b) => "trait_impl" in b && b.trait_impl.trait === trait,
  );

  for (const polyImpl of polymorphicImpls) {
    if ("trait_impl" in polyImpl && polyImpl.trait_impl.dict) {
      const implType = polyImpl.trait_impl.type;

      // Fully normalize BOTH types by beta-reducing all applications
      // This turns ((λt.λu.variant) l) r) into <variant with l, r>
      // and λt.λu.variant into λt.λu.variant (stays as is)

      const normalizedImpl = normalizeType(state, implType);
      const normalizedTarget = normalizeType(state, normalizedType);

      // Now instantiate the impl (replaces any forall-bound vars with metas)
      const instImplTy = instantiateType(state, normalizedImpl);

      // For the target, if it's a lambda that needs to be applied to match the impl's level,
      // apply it to fresh metas
      let matchingTarget = normalizedTarget;

      // Check if target is still a lambda while impl is not
      if ("lam" in matchingTarget && !("lam" in instImplTy)) {
        // Apply the lambda to fresh metas until it matches the impl's structure

        while ("lam" in matchingTarget) {
          const fv = freshMetaVar(state.meta);
          matchingTarget = normalizeType(
            state,
            substituteType(matchingTarget.lam.var, fv, matchingTarget.lam.body),
          );
        }
      }

      // Try to unify
      const worklist: Worklist = [];
      const subst = new Map<string, Type>();

      const unifyRes = unifyTypes(
        state,
        instImplTy,
        matchingTarget,
        worklist,
        subst,
      );

      if ("ok" in unifyRes) {
        const solveRes = solveConstraints(state, worklist, subst);

        if ("ok" in solveRes) {
          // Successfully unified - instantiate and substitute into the dict
          const instantiatedDict = instantiateTerm(
            state,
            polyImpl.trait_impl.dict,
          );
          const finalDict = applySubstitutionToTerm(
            state,
            solveRes.ok,
            instantiatedDict,
          );
          return ok(finalDict);
        }
      }
    }
  }

  return err({ missing_trait_impl: { trait, type } } as TypingError);
}

/**
 * Resolves a **list of trait constraints** into their corresponding
 * **dictionary values**.
 *
 * What it does:
 * ---------------------------------------
 * Each constraint has the form:
 *
 *   { trait: "Eq", type: τ }
 *
 * meaning “we need evidence that `τ` implements trait `Eq`”.
 *
 * This function:
 * 1. Iterates through each constraint
 * 2. Calls {@link checkTraitImplementation} to find the dictionary for it
 * 3. Collects all dictionaries in order
 * 4. Stops on the *first* error (missing implementation, mismatched type, etc.)
 *
 * Why this matters:
 * ---------------------------------------
 * Trait‑bounded polymorphism (`∀Self where Eq<Self>. ...`) and explicit
 * trait applications (`term[T] with {dicts}`) rely on assembling all necessary
 * dictionaries before typechecking can continue.
 *
 * This function is the “batch mode” version of trait resolution:
 * - used by {@link instantiateWithTraits}
 * - used by {@link inferTraitAppType}
 * - used when instantiating a trait‑lambda automatically
 *
 * In effect: it validates that *all* required constraints for an expression
 * have valid trait implementations.
 *
 * Failure mode:
 * ---------------------------------------
 * Returns the first error from {@link checkTraitImplementation}, typically:
 * - `missing_trait_impl`
 * - other type errors arising while unifying a polymorphic implementation
 *
 * Success mode:
 * ---------------------------------------
 * Returns:
 *
 *   ok([dict₁, dict₂, ...])
 *
 * where each element is a fully instantiated dictionary term.
 *
 * Related:
 * - {@link TraitConstraint} — input format
 * - {@link checkTraitImplementation} — resolves a single constraint
 * - {@link TraitLamTerm} / {@link TraitAppTerm} — where constraints originate
 *
 * @param state - Typechecker state holding available trait implementations
 * @param constraints - List of trait requirements to satisfy
 * @returns All resolved dictionary terms, or an error
 *
 * @example Success:
 * ```ts
 * const constraints = [
 *   { trait: "Eq", type: conType("Int") },
 *   { trait: "Show", type: conType("Int") }
 * ];
 *
 * const result = checkTraitConstraints(state, constraints);
 * // => ok([eqIntDict, showIntDict])
 * ```
 *
 * @example Failure (first missing impl is reported):
 * ```ts
 * const constraints = [{ trait: "Ord", type: conType("String") }];
 * const result = checkTraitConstraints(state, constraints);
 * // => err({ missing_trait_impl: ... })
 * ```
 */
export function checkTraitConstraints(
  state: TypeCheckerState,
  constraints: TraitConstraint[],
): Result<TypingError, Term[]> {
  const dicts: Term[] = [];

  for (const constraint of constraints) {
    const result = checkTraitImplementation(
      state,
      constraint.trait,
      constraint.type,
    );

    if ("err" in result) return result;
    dicts.push(result.ok);
  }

  return ok(dicts);
}

/**
 * Collects all **constructor and label names** that appear inside a pattern.
 *
 * What it extracts:
 * ---------------------------------------
 * This function returns a `Set<string>` containing every **variant label** or
 * **record field label** that occurs anywhere inside a pattern.
 *
 * Examples of what counts as a “label”:
 * - `Some(x)`  → `"Some"`
 * - `Left(v)` → `"Left"`
 * - `{ x: p, y: q }` → `"x"`, `"y"` (record field labels)
 * - `(Some(x), y)` → `"Some"`
 *
 * Names **not** added to the set:
 * - variable names (`x`, `hd`, etc.)
 * - wildcards (`_`)
 * - constructor‑literal patterns (`true`, `"None"`) using `conPattern`
 *
 * Why this exists:
 * ---------------------------------------
 * Pattern matching needs to know **which cases are covered**, especially for
 * exhaustiveness checking.
 *
 * For example:
 * ```ts
 * match xs {
 *   Some(x) => ...
 *   None    => ...
 * }
 * ```
 * To determine whether the match is exhaustive, we must extract:
 *
 *   `{ "Some", "None" }`
 *
 * This helper isolates that logic.
 *
 * Where it's used:
 * ---------------------------------------
 * - {@link checkExhaustive} — determines which constructors are covered
 * - pattern utilities for dependency tracking and renaming
 *
 * Behavior summary:
 * ---------------------------------------
 * - Variable / wildcard / constructor‑literal → no labels
 * - Variant pattern → include its label, then recurse into payload
 * - Record pattern → recurse into each field’s pattern
 * - Tuple pattern → recurse into each element
 *
 * @param pattern - The pattern to extract labels from
 * @returns A set of all variant or record labels appearing in the pattern
 *
 * @example Variant:
 * ```ts
 * extractPatternLabels(variantPattern("Some", varPattern("x")));
 * // => Set(["Some"])
 * ```
 *
 * @example Nested:
 * ```ts
 * extractPatternLabels(
 *   tuplePattern([
 *     variantPattern("Left", varPattern("v")),
 *     recordPattern([["y", variantPattern("Right", varPattern("w"))]])
 *   ])
 * );
 * // => Set(["Left", "y", "Right"])
 * ```
 */
export function extractPatternLabels(pattern: Pattern): Set<string> {
  const labels = new Set<string>();
  if ("var" in pattern || "wildcard" in pattern || "con" in pattern)
    return labels; // Covers all, no specific label

  if ("variant" in pattern) {
    labels.add(pattern.variant.label);
    // Recurse on inner for nested
    for (const innerLabel of extractPatternLabels(pattern.variant.pattern))
      labels.add(innerLabel);
  } else if ("record" in pattern) {
    for (const [, subPat] of pattern.record) {
      for (const l of extractPatternLabels(subPat)) labels.add(l);
    }
  } else if ("tuple" in pattern) {
    for (const subPat of pattern.tuple)
      for (const l of extractPatternLabels(subPat)) labels.add(l);
  }
  return labels;
}

/**
 * Checks whether a list of patterns **exhaustively covers** all cases of a
 * given type — i.e., whether a `match` expression is *complete*.
 *
 * In other words:
 *   “Is it possible for the scrutinee to have a shape that none of the patterns match?”
 *
 * ---------------------------------------------------------------------------
 * Why exhaustiveness matters
 * ---------------------------------------------------------------------------
 * Pattern matching should be **total**: every possible value of the scrutinee
 * type must be handled by one of the patterns.
 *
 * Examples:
 *
 *   match opt {
 *     Some(x) => ...
 *     None    => ...
 *   }
 *
 * → exhaustive for `Option<T>`
 *
 *   match opt {
 *     Some(x) => ...
 *   }
 *
 * → **NOT** exhaustive: missing `None`
 *
 * This function detects such missing cases.
 *
 * ---------------------------------------------------------------------------
 * How coverage checking works
 * ---------------------------------------------------------------------------
 * The algorithm follows a simple structure:
 *
 * 1. **Normalize the type** (`normalizeType`)
 *    Needed because:
 *    - Enums may expand into structural variants
 *    - Type lambdas may β‑reduce
 *    - Mu‑types may unfold
 *
 * 2. **Nominal enum case**
 *    If the type is of the form `Enum<T1, T2, ...>`, we:
 *    - find the enum definition in the context
 *    - extract *all variant labels* declared by the enum
 *      (e.g., `{"None", "Some"}`)
 *    - collect all labels covered by the patterns
 *      using {@link extractPatternLabels}
 *    - if any labels are missing → `missing_case` error
 *    - wildcard `_` or variable pattern matches everything → automatically exhaustive
 *
 * 3. **Structural variant case**
 *    If the normalized type is a structural variant:
 *    - collect all labels appearing in the type
 *    - collect those covered by the patterns
 *    - missing label → error
 *
 * 4. **Other types** (e.g., records, tuples, primitives, functions)
 *    These have *no variant cases*, so matching on them cannot be non-exhaustive.
 *    → always succeed
 *
 * ---------------------------------------------------------------------------
 * Wildcard and variable patterns
 * ---------------------------------------------------------------------------
 * Any pattern of the form:
 *   `_`
 *   `x`
 *
 * matches **every possible value** of the scrutinee type.
 *
 * Therefore, if such a pattern appears anywhere, coverage checking stops early
 * and returns `ok(null)`.
 *
 * ---------------------------------------------------------------------------
 * Errors produced
 * ---------------------------------------------------------------------------
 * - `not_a_variant`
 *   The scrutinee type is used as if it were a variant/enum but isn’t.
 *
 * - `kind_mismatch`
 *   Occurs when enum parameters don’t match expected arity.
 *
 * - `missing_case`
 *   At least one constructor is not covered by any pattern.
 *
 * ---------------------------------------------------------------------------
 * Related functions
 * ---------------------------------------------------------------------------
 * - {@link extractPatternLabels} — collects constructor/field labels inside patterns
 * - {@link checkPattern} — validates individual pattern shapes
 * - {@link inferMatchType} — uses this to validate full match expressions
 * - {@link normalizeType} — expands enums and aliases before analysis
 *
 * @param state - The current typechecker state (context + meta-vars)
 * @param patterns - The list of patterns in the match expression
 * @param type - The scrutinee type to check against
 * @returns `ok(null)` if exhaustive, or a `missing_case` / `not_a_variant` error
 *
 * @example Exhaustive enum match:
 * ```ts
 * checkExhaustive(state,
 *   [variantPattern("Red", _), variantPattern("Blue", _)],
 *   conType("Color")
 * );
 * // ok
 * ```
 *
 * @example Missing case:
 * ```ts
 * checkExhaustive(state,
 *   [variantPattern("Some", varPattern("x"))],
 *   appType(conType("Option"), conType("Int"))
 * );
 * // err({ missing_case: { label: "None" } })
 * ```
 *
 * @example Wildcard case:
 * ```ts
 * checkExhaustive(state, [wildcardPattern()], conType("Color"));
 * // ok — wildcard covers all cases
 * ```
 */
export function checkExhaustive(
  state: TypeCheckerState,
  patterns: Pattern[],
  type: Type,
): Result<TypingError, null> {
  const normType = normalizeType(state, type);

  // Nominal check
  if ("app" in normType && "con" in normType.app.func) {
    const conName = normType.app.func.con;
    const spineArgs = getSpineArgs(normType);

    const enumBinding = state.ctx.find(
      (b) => "enum" in b && b.enum.name === conName,
    );
    if (!enumBinding || !("enum" in enumBinding))
      return err({ not_a_variant: type }); // Triggered if no binding
    const def = enumBinding.enum;

    if (spineArgs.length !== def.params.length)
      return err({
        kind_mismatch: { expected: def.kind, actual: starKind },
      });

    const allLabels = new Set(def.variants.map(([l]) => l));
    const coveredLabels = new Set<string>();

    for (const pattern of patterns) {
      if ("wildcard" in pattern || "var" in pattern) return ok(null);
      const patLabels = extractPatternLabels(pattern);
      for (const label of patLabels) coveredLabels.add(label);
    }

    const missing = [...allLabels].filter((l) => !coveredLabels.has(l)).sort();
    // Report first
    if (missing.length > 0)
      return err({ missing_case: { label: missing[0]! } });

    return ok(null);
  }

  // Structural fallback (unchanged, with log)
  if ("variant" in normType) {
    const variantLabels = new Set(normType.variant.map(([l]) => l));
    const coveredLabels = new Set<string>();
    for (const pattern of patterns) {
      if ("wildcard" in pattern || "var" in pattern) return ok(null);
      if ("variant" in pattern) coveredLabels.add(pattern.variant.label);
    }
    const missing = [...variantLabels].filter((l) => !coveredLabels.has(l));
    return missing.length > 0
      ? err({ missing_case: { label: missing[0]! } })
      : ok(null);
  }

  // Non-variant types (e.g., primitives, arrows): Always exhaustive (no cases needed)
  return ok(null);
}

/**
 * Checks whether a **pattern** is valid for a given **scrutinee type**, and
 * returns all variable bindings introduced by that pattern.
 *
 * In other words:
 *
 *    “If the scrutinee has type `T`, is this pattern allowed,
 *     and what variables does it bind (with their types)?”
 *
 * This is the core of pattern‑matching typechecking.
 *
 * ---------------------------------------------------------------------------
 * What the function returns
 * ---------------------------------------------------------------------------
 * - **ok(Context)**: a list of `{ name, type }` bindings for variables inside the pattern
 * - **err(TypingError)**: if the pattern is not valid for the given type
 *
 * Example:
 * ```ts
 * checkPattern(state, tuplePattern([varPattern("x"), varPattern("y")]),
 *              tupleType([Int, Bool]));
 *
 * // => ok([
 * //   { term: { name: "x", type: Int } },
 * //   { term: { name: "y", type: Bool } }
 * // ])
 * ```
 *
 * ---------------------------------------------------------------------------
 * Patterns handled
 * ---------------------------------------------------------------------------
 * 1. **Variable pattern (`x`)**
 *    - Binds the *entire* scrutinee type to variable `x`
 *
 * 2. **Wildcard pattern (`_`)**
 *    - Always matches, binds nothing
 *
 * 3. **Variant pattern (`Some(p)` / `Left(p)`)**
 *    - Works with:
 *      - **μ‑types** (recursive): unfold once and continue
 *      - **Meta‑variables**: infer the correct enum type by label
 *      - **Structural variants** (`<L:A | R:B>`)
 *      - **Nominal enums** (`Option<Int>`)
 *
 *    Errors include:
 *    - `invalid_variant_label` (e.g., pattern uses `Foo` but enum has no `Foo`)
 *    - `not_a_variant` (scrutinee is not a variant/enum)
 *    - `kind_mismatch` (wrong number of enum type parameters)
 *
 * 4. **Record patterns (`{ x: p, y: q }`)**
 *    → Delegated to `checkRecordPattern`
 *
 * 5. **Tuple patterns (`(p1, p2, ...)`)**
 *    → Delegated to `checkTuplePattern`
 *
 * 6. **Constructor literal patterns (`true`, `None`, `Zero`)**
 *    → Delegated to `checkConPattern`
 *
 * ---------------------------------------------------------------------------
 * Special feature: Meta‑variable scrutinees
 * ---------------------------------------------------------------------------
 * If `type` is a **meta‑variable** (unknown type), but the pattern is a variant,
 * example:
 *
 * ```ts
 * match v {
 *   Some(x) => ...
 * }
 * ```
 *
 * The checker infers that `v` *must* be some enum containing `"Some"`.
 * It:
 *  - finds which enum has a `"Some"` constructor
 *  - builds an enum type with fresh meta‑vars
 *  - unifies the scrutinee type with this inferred enum
 *  - then recurses
 *
 * This enables powerful inference in match expressions.
 *
 * ---------------------------------------------------------------------------
 * Recursive behavior
 * ---------------------------------------------------------------------------
 * Most pattern forms recursively call `checkPattern` on their subpatterns,
 * building a flat list of variable bindings.
 *
 * ---------------------------------------------------------------------------
 * Related:
 * ---------------------------------------------------------------------------
 * - {@link checkTuplePattern}
 * - {@link checkRecordPattern}
 * - {@link checkConPattern}
 * - {@link normalizeType}
 * - {@link unifyTypes} / {@link solveConstraints}
 * - {@link patternBindings}
 *
 * ---------------------------------------------------------------------------
 * @param state - The typechecker state (context + meta‑variable environment)
 * @param pattern - The pattern to validate
 * @param type - The expected type of the scrutinee for this pattern
 * @returns A list of variable bindings introduced by the pattern, or an error
 *
 * ---------------------------------------------------------------------------
 * @example Variant (nominal enum)
 * ```ts
 * checkPattern(
 *   state,
 *   variantPattern("Some", varPattern("x")),
 *   appType(conType("Option"), conType("Int"))
 * );
 * // => ok([{ term: { name: "x", type: Int } }])
 * ```
 *
 * @example Variant (meta‑variable: type inferred from pattern)
 * ```ts
 * checkPattern(state, variantPattern("Left", varPattern("x")), ?0);
 * // => infers that ?0 must be an enum with constructor Left
 * ```
 *
 * @example Wildcard
 * ```ts
 * checkPattern(state, wildcardPattern(), Int);
 * // => ok([])
 * ```
 */
export function checkPattern(
  state: TypeCheckerState,
  pattern: Pattern,
  type: Type,
): Result<TypingError, Context> {
  // Variable pattern binds the whole value
  if ("var" in pattern) return ok([{ term: { name: pattern.var, type } }]);

  // Wildcard matches anything, no bindings
  if ("wildcard" in pattern) return ok([]);

  if ("variant" in pattern) {
    if ("mu" in type) {
      const unfolded = substituteType(type.mu.var, type, type.mu.body);
      return checkPattern(state, pattern, unfolded);
    }

    const normType = normalizeType(state, type);

    // Handle meta variable case - infer enum type from pattern
    if (isMetaVar(normType)) {
      const label = pattern.variant.label;

      // Find enum with this variant label
      const enumBinding = state.ctx.find(
        (b) => "enum" in b && b.enum.variants.some(([l]) => l === label),
      );

      if (!enumBinding || !("enum" in enumBinding)) {
        return err({ unbound: label });
      }

      const def = enumBinding.enum;

      // Build enum type with fresh meta variables: Result<?1, ?2>
      let enumType: Type = conType(def.name);
      for (let i = 0; i < def.params.length; i++) {
        enumType = appType(enumType, freshMetaVar(state.meta));
      }

      // Unify the scrutinee's meta variable with the enum type
      const worklist: Worklist = [];
      const subst = new Map<string, Type>();
      const unifyRes = unifyTypes(state, normType, enumType, worklist, subst);
      if ("err" in unifyRes) return unifyRes;

      const solveRes = solveConstraints(state, worklist, subst);
      if ("err" in solveRes) return solveRes;

      // Update global meta variable solutions
      for (const [varName, soln] of solveRes.ok.entries()) {
        const globalSolve = solveMetaVar(state, varName, soln);
        if ("err" in globalSolve) return globalSolve;
      }

      // Recurse with the resolved type
      const resolvedType = applySubstitution(state, solveRes.ok, normType);
      return checkPattern(state, pattern, resolvedType);
    }

    // Structural
    if ("variant" in normType) {
      const caseType = normType.variant.find(
        ([t]) => t === pattern.variant.label,
      );
      if (!caseType)
        return err({
          invalid_variant_label: {
            variant: normType,
            label: pattern.variant.label,
          },
        });
      return checkPattern(state, pattern.variant.pattern, caseType[1]);
    }

    // Nominal
    if ("app" in normType || "con" in normType) {
      const head = "con" in normType ? normType : getSpineHead(normType);
      if (!("con" in head)) return err({ not_a_variant: type });

      const conName = head.con;
      const spineArgs = "con" in normType ? [] : getSpineArgs(normType);

      const enumBinding = state.ctx.find(
        (b) => "enum" in b && b.enum.name === conName,
      );
      if (!enumBinding || !("enum" in enumBinding))
        return err({ not_a_variant: type });

      const def = enumBinding.enum;

      if (spineArgs.length !== def.params.length)
        return err({
          kind_mismatch: { expected: def.kind, actual: starKind },
        });

      const label = pattern.variant.label;
      const variantEntry = def.variants.find(([l]) => l === label);
      if (!variantEntry)
        return err({ invalid_variant_label: { variant: type, label } });

      let fieldType = variantEntry[1];
      for (let i = 0; i < def.params.length; i++) {
        fieldType = substituteType(def.params[i]!, spineArgs[i]!, fieldType);
      }
      fieldType = normalizeType(state, fieldType);

      return checkPattern(state, pattern.variant.pattern, fieldType);
    }

    return err({ not_a_variant: type });
  }

  // Existing cases (con, record, tuple, etc.)
  if ("con" in pattern) return checkConPattern(state, pattern, type);
  if ("record" in pattern) return checkRecordPattern(state, pattern, type);
  if ("tuple" in pattern) return checkTuplePattern(state, pattern, type);

  // Fallback: No bindings
  return ok([]);
}

function checkTuplePattern(
  state: TypeCheckerState,
  pattern: TuplePattern,
  type: Type,
) {
  // Allow ⊥
  if (!("tuple" in type) && !isBottom(state, type))
    return err({ not_a_tuple: type });

  if ("tuple" in type && pattern.tuple.length !== type.tuple.length)
    return err({
      type_mismatch: {
        expected: type,
        actual: { tuple: pattern.tuple.map(() => unitType) },
      },
    });

  const bindings: Context = [];
  // For zero-arity (unit): empty tuple binds nothing
  const effectiveElements = "tuple" in type ? type.tuple : [];
  for (let i = 0; i < pattern.tuple.length; i++) {
    const subPattern = pattern.tuple[i]!;
    const elementType =
      i < effectiveElements.length ? effectiveElements[i]! : unitType;
    const subResult = checkPattern(state, subPattern, elementType);
    if ("err" in subResult) return subResult;
    bindings.push(...subResult.ok);
  }
  return ok(bindings);
}

const checkConPattern = (
  state: TypeCheckerState,
  pattern: ConPattern,
  type: Type,
) => {
  return isAssignableTo(state, pattern.con.type, type)
    ? ok([])
    : err({ type_mismatch: { expected: type, actual: pattern.con.type } });
};

// Helper (add if not already present)
const first = <T, U>(tuple: [T, U]) => tuple[0];

function checkRecordPattern(
  state: TypeCheckerState,
  pattern: RecordPattern,
  type: Type,
): Result<TypingError, Context> {
  // Handle bottom type: ⊥ matches any record pattern (unreachable code paths, etc.)
  if (isBottom(state, type)) {
    // Extract bindings from subpatterns (but types are arbitrary since ⊥ <: anything)
    const bindings: Context = [];
    for (const [label, subPattern] of pattern.record) {
      // For bottom, bind subpattern vars to a fresh meta or unit (safe)
      const subResult = checkPattern(state, subPattern, unitType); // Or freshMetaVar()
      if ("err" in subResult) return subResult;
      // Augment bindings with label (optional, for record projection later)
      subResult.ok.forEach((b) => {
        if ("term" in b) b.term.name = `${label}_${b.term.name}`; // Namespace if needed
      });
      bindings.push(...subResult.ok);
    }
    return ok(bindings);
  }
  if (!("record" in type)) return err({ not_a_record: type });

  const patternRecord = pattern.record; // [string, Pattern][]
  const typeRecord = type.record; // [string, Type][]

  if (patternRecord.length !== typeRecord.length)
    return err({
      type_mismatch: {
        expected: type,
        actual: {
          record: patternRecord.map(([l]) => [l, unitType]), // Infer missing types as unit
        } as RecordType,
      },
    });

  // Extract and sort labels for order-independent matching
  const typeLabels = typeRecord.map(first).sort(); // strings, e.g., ["x", "y"]
  const patternLabels = patternRecord.map(([label]) => label).sort(); // strings, e.g., ["y", "x"]

  // Check that the sets of labels match exactly
  for (let i = 0; i < typeLabels.length; i++)
    if (typeLabels[i] !== patternLabels[i])
      return err({
        missing_field: {
          record: type,
          label: typeLabels[i]!, // The missing/expected label
        },
      });

  // All labels match: Now check each field's subpattern against the field's type
  const bindings: Context = [];
  for (const [label, subPattern] of patternRecord) {
    const fieldEntry = typeRecord.find(([l]) => l === label);
    if (!fieldEntry) return err({ missing_field: { record: type, label } });

    const fieldType = fieldEntry[1];
    const subResult = checkPattern(state, subPattern, fieldType);
    if ("err" in subResult) return subResult;

    // Collect bindings (e.g., vars from subPattern bound to fieldType slices)
    bindings.push(...subResult.ok);
  }

  return ok(bindings);
}

/**
 * Performs **type‑level substitution**:
 *
 *    substituteType(target, replacement, inType)
 *
 * meaning:
 *
 *    “Replace every *free* occurrence of type variable `target`
 *     with `replacement` inside `inType`.”
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * It recursively walks a type and substitutes:
 *
 *   target ↦ replacement
 *
 * while respecting **binders** (`∀`, `λ`, `μ`) so that substitution does not
 * accidentally replace *bound* occurrences of the variable.
 *
 * Example (free variable):
 * ```ts
 * substituteType("A", Int, A → B)
 * // => Int → B
 * ```
 *
 * Example (bound variable — *skipped*):
 * ```ts
 * substituteType("A", Int, ∀A. A → B)
 * // => ∀A. A → B   (inner A is bound; not replaced)
 * ```
 *
 * ---------------------------------------------------------------------------
 * Why binder safety matters
 * ---------------------------------------------------------------------------
 * Types have structure and scoping, just like terms.
 * Replacing inside a bound variable’s scope would produce an invalid type:
 *
 *   substitute A ↦ Int in ∀A. A → A   // WRONG
 *
 * would incorrectly yield:
 *
 *   ∀A. Int → Int   // changes meaning!
 *
 * This function avoids such errors by detecting binder variables and skipping
 * substitution beneath them.
 *
 * ---------------------------------------------------------------------------
 * Role in the typechecker
 * ---------------------------------------------------------------------------
 * - **Instantiation** of polymorphic types (`instantiateType`)
 * - **Beta‑reduction** of type lambdas during normalization
 * - **Enum and alias expansion** inside `normalizeType`
 * - **Trait application** (substituting type parameters)
 * - **Mu‑type unfolding** (`inferFoldType`, `inferUnfoldType`)
 *
 * ---------------------------------------------------------------------------
 * Special feature: Cycle avoidance for μ‑types
 * ---------------------------------------------------------------------------
 * The optional `avoidInfinite` set tracks which recursive variables are already
 * being substituted.
 * This prevents infinite loops like:
 *
 *   μX. X   but substituting X inside its own body forever.
 *
 * Instead, when a variable is in `avoidInfinite`, substitution stops at that
 * recursion boundary.
 *
 * ---------------------------------------------------------------------------
 * Recursion rules (simplified)
 * ---------------------------------------------------------------------------
 * - `var` → replace if free match
 * - `con` → never replaced
 * - `forall`, `lam`, `mu` → stop if binder name matches `target`
 * - composite types (`arrow`, `app`, `record`, `tuple`, `variant`) → recurse
 *
 * ---------------------------------------------------------------------------
 * @param target - The type variable name being replaced (e.g., `"A"`)
 * @param replacement - The type substituted in place of the target
 * @param inType - The type expression where substitution occurs
 * @param avoidInfinite - Internal set to prevent infinite recursion on μ‑types
 *
 * @returns A new type expression with the substitution applied safely
 *
 * ---------------------------------------------------------------------------
 * @example Simple:
 * ```ts
 * substituteType("A", conType("Int"), arrowType(varType("A"), varType("B")));
 * // => (Int → B)
 * ```
 *
 * @example Bound variable (safe skip):
 * ```ts
 * const poly = forallType("A", starKind, arrowType(varType("A"), varType("X")));
 * substituteType("A", conType("Int"), poly);
 * // => ∀A. (A → X)
 * ```
 *
 * @example Mu cycle safety:
 * ```ts
 * const rec = muType("L", tupleType([varType("Int"), varType("L")]));
 * substituteType("L", varType("X"), rec);
 * // => μL. (Int, L)  (inner L is bound; safe)
 * ```
 */
export function substituteType(
  target: string,
  replacement: Type,
  inType: Type,
  avoidInfinite: Set<string> = new Set(),
): Type {
  // In substituteType top-level:
  if ("con" in inType) {
    return inType.con === target ? replacement : inType;
  }

  if ("var" in inType) return inType.var === target ? replacement : inType;

  if ("arrow" in inType)
    return substituteArrowType(target, replacement, inType, avoidInfinite);

  if ("bounded_forall" in inType && inType.bounded_forall.var !== target)
    return substituteBoundForallType(
      inType,
      target,
      replacement,
      avoidInfinite,
    );

  if ("forall" in inType && inType.forall.var !== target)
    return substituteForallType(inType, target, replacement, avoidInfinite);

  if ("app" in inType)
    return substituteAppType(target, replacement, inType, avoidInfinite);

  if ("lam" in inType) {
    if (inType.lam.var === target) return inType; // FIX: Skip bound var
    return substituteLamType(target, replacement, inType, avoidInfinite);
  }
  if ("record" in inType)
    return substituteRecordType(inType, target, replacement, avoidInfinite);

  if ("variant" in inType)
    return substituteVariantType(inType, target, replacement, avoidInfinite);

  if ("mu" in inType)
    return subtituteMuType(inType, target, replacement, avoidInfinite);

  if ("tuple" in inType)
    return substituteTupleType(inType, target, replacement, avoidInfinite);

  return inType;
}

function substituteTupleType(
  inType: TupleType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
) {
  return tupleType(
    inType.tuple.map((t) =>
      substituteType(target, replacement, t, avoidInfinite),
    ),
  );
}

function subtituteMuType(
  inType: MuType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
) {
  if (inType.mu.var === target) return inType; // bound variable, don't substitute

  // Check if we're about to create an infinite recursion
  if (avoidInfinite.has(inType.mu.var)) return inType; // Stop recursion

  return muType(
    inType.mu.var,
    substituteType(
      target,
      replacement,
      inType.mu.body,
      new Set([inType.mu.var, ...avoidInfinite]),
    ),
  );
}

function substituteVariantType(
  inType: VariantType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
) {
  {
    const variant: [string, Type][] = [];
    for (const [label, caseType] of inType.variant)
      variant.push([
        label,
        substituteType(target, replacement, caseType, avoidInfinite),
      ]);
    return { variant };
  }
}

function substituteRecordType(
  inType: RecordType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
) {
  {
    const record: [string, Type][] = [];
    for (const [label, fieldType] of inType.record)
      record.push([
        label,
        substituteType(target, replacement, fieldType, avoidInfinite),
      ]);
    return { record };
  }
}

function substituteLamType(
  target: string,
  replacement: Type,
  inType: LamType,
  avoidInfinite: Set<string>,
): Type {
  return lamType(
    inType.lam.var,
    inType.lam.kind,
    substituteType(target, replacement, inType.lam.body, avoidInfinite),
  );
}

function substituteAppType(
  target: string,
  replacement: Type,
  inType: AppType,
  avoidInfinite: Set<string>,
): Type {
  return appType(
    substituteType(target, replacement, inType.app.func, avoidInfinite),
    substituteType(target, replacement, inType.app.arg, avoidInfinite),
  );
}

function substituteForallType(
  inType: ForallType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
): Type {
  return forallType(
    inType.forall.var,
    inType.forall.kind,
    substituteType(target, replacement, inType.forall.body, avoidInfinite),
  );
}

function substituteBoundForallType(
  inType: BoundedForallType,
  target: string,
  replacement: Type,
  avoidInfinite: Set<string>,
) {
  return boundedForallType(
    inType.bounded_forall.var,
    inType.bounded_forall.kind,
    inType.bounded_forall.constraints.map((c) => ({
      trait: c.trait,
      type: substituteType(target, replacement, c.type, avoidInfinite),
    })),
    substituteType(
      target,
      replacement,
      inType.bounded_forall.body,
      avoidInfinite,
    ),
  );
}

function substituteArrowType(
  target: string,
  replacement: Type,
  inType: ArrowType,
  avoidInfinite: Set<string>,
): Type {
  return arrowType(
    substituteType(target, replacement, inType.arrow.from, avoidInfinite),
    substituteType(target, replacement, inType.arrow.to, avoidInfinite),
  );
}

/**
 * Checks whether a kind is the **base kind** `*` (pronounced “star”).
 *
 * What it means:
 * - `*` is the kind of **concrete, fully‑applied types** such as:
 *   - `Int :: *`
 *   - `Bool :: *`
 *   - `List<Int> :: *`
 *
 * This predicate distinguishes ordinary value‑level types from
 * higher‑kinded type constructors (e.g., `* → *`).
 *
 * Used in:
 * - kind checking (`checkKind`)
 * - enforcing field kinds in records/variants
 * - bottom‑type rules (`⊥` must be kind `*`)
 *
 * @param kind - The kind to test
 * @returns `true` if the kind is `*`, otherwise `false`
 *
 * @example
 * ```ts
 * isStarKind(starKind);                 // true
 * isStarKind(arrowKind(starKind, starKind)); // false
 * ```
 */
export const isStarKind = (kind: Kind) => "star" in kind;

/**
 * Checks whether two **kinds** are structurally equal.
 *
 * What it means:
 * ---------------------------------------
 * Kinds describe the “shape” of types:
 * - `*` — the kind of fully‑applied, concrete types
 * - `* → *` — the kind of unary type constructors (e.g., `List`)
 * - `* → (* → *)` — higher‑kinded constructors
 *
 * `kindsEqual` compares two kinds recursively and returns `true` only if:
 * - they are both `*`, or
 * - they are both arrow kinds whose input and output kinds are equal.
 *
 * Why it’s important:
 * ---------------------------------------
 * - Ensures type constructors are used with the correct number of arguments
 *   (`List<Int>` is OK, `Int<Int>` is not)
 * - Used heavily during kind checking (`checkKind`)
 * - Ensures polymorphic and type‑lambda binders have matching kinds
 *
 * Used by:
 * - {@link unifyKinds}
 * - {@link checkAppKind}
 * - {@link checkForallKind}
 *
 * @param left - The first kind
 * @param right - The second kind
 * @returns `true` if both kinds are the same shape, otherwise `false`
 *
 * @example
 * ```ts
 * kindsEqual(starKind, starKind);                          // true
 * kindsEqual(arrowKind(starKind, starKind),
 *            arrowKind(starKind, starKind));               // true
 * kindsEqual(starKind, arrowKind(starKind, starKind));     // false
 * ```
 */
export const kindsEqual = (left: Kind, right: Kind): boolean =>
  ("star" in left && "star" in right) ||
  ("arrow" in left &&
    "arrow" in right &&
    kindsEqual(left.arrow.from, right.arrow.from) &&
    kindsEqual(left.arrow.to, right.arrow.to));

/**
 * Infers or verifies the **kind** of a type.
 *
 * In other words:
 *
 *    “What kind does this type have — `*`, `* → *`, etc. —
 *     and is it used correctly?”
 *
 * Kinds classify *types* the same way types classify *values*:
 * - `*` (star kind) — fully‑applied, concrete types (e.g., `Int`, `List<Int>`)
 * - `* → *` — unary type constructors (e.g., `List`)
 * - `(* → *) → *` — higher‑kinded type constructors
 *
 * `checkKind` is the **kind checker / kind inference engine** for the system.
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * 1. Dispatches on every type constructor (`arrow`, `record`, `variant`, etc.)
 * 2. Ensures type applications are well‑kinded:
 *      - if `F :: κ1 → κ2` and `A :: κ1` then `F<A> :: κ2`
 * 3. Ensures all fields of records, variants, and tuples have kind `*`
 * 4. Ensures λ‑bound type variables and ∀‑quantified variables are used properly
 * 5. Expands aliases and enums before checking (`normalizeType`)
 * 6. Uses context entries (`TypeBinding`) to look up constructor kinds
 *
 * ---------------------------------------------------------------------------
 * The `lenient` mode
 * ---------------------------------------------------------------------------
 * Normally, unbound type variables or constructors are an error:
 *
 *    Unknown type: X
 *
 * But when `lenient = true`, unbound names are treated as having kind `*`.
 *
 * This is used in:
 * - subtyping (`subsumes`)
 * - bottom‑type checks (`⊥`)
 * - internal fast paths where strict kind checking would be too early
 *
 * ---------------------------------------------------------------------------
 * Errors produced
 * ---------------------------------------------------------------------------
 * - `unbound`: missing type constructor or type variable
 * - `not_a_type_function`: applying a non‑arrow kind
 * - `kind_mismatch`: expected one kind but found another
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 * ```ts
 * checkKind(state, conType("Int"));             // => ok(*)
 *
 * checkKind(state, appType(conType("List"), conType("Int")));
 * // => ok(*), assuming List :: * → *
 *
 * checkKind(state, appType(conType("Int"), conType("Bool")));
 * // => err(not_a_type_function), because Int :: *
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link Kind} — star kinds and arrow kinds
 * - {@link arrowKind} — constructs arrow kinds
 * - {@link isStarKind} — checks for `*`
 * - {@link kindsEqual} — kind comparison
 * - {@link normalizeType} — alias/enum expansion before checking
 *
 * @param state - The type checker state (context + meta‑variable environment)
 * @param type - The type whose kind must be checked or inferred
 * @param lenient - If true, treat unbound names as having kind `*`
 *
 * @returns `ok(kind)` if the type is well‑kinded, or a `TypingError` otherwise
 */
export function checkKind(
  state: TypeCheckerState,
  type: Type,
  lenient: boolean = false,
): Result<TypingError, Kind> {
  if ("evar" in type) {
    return state.meta.kinds.has(type.evar)
      ? ok(state.meta.kinds.get(type.evar)!)
      : err({ unbound: type.evar });
  }
  if ("var" in type) return checkVarKind(state, type, lenient);
  if ("con" in type) return checkConKind(state, type, lenient);

  if ("never" in type) return ok(starKind);
  if ("arrow" in type) return checkArrowKind(state, type, lenient);
  if ("forall" in type) return checkForallKind(state, type, lenient);
  if ("bounded_forall" in type)
    return checkBoundedForallKind(state, type, lenient);
  if ("lam" in type) return checkLamKind(state, type, lenient);
  if ("app" in type) return checkAppKind(state, type, lenient);
  if ("record" in type) return checkRecordKind(state, type, lenient);
  if ("variant" in type) return checkVariantKind(state, type, lenient);
  if ("mu" in type) return checkMuKind(state, type, lenient);
  if ("tuple" in type) return checkTupleKind(state, type, lenient);

  throw new Error(`Unknown type: ${Object.keys(type)[0]}`);
}

function checkConKind(
  state: TypeCheckerState,
  type: ConType,
  lenient: boolean,
) {
  // Check for type alias first
  const aliasBinding = state.ctx.find(
    (b) => "type_alias" in b && b.type_alias.name === type.con,
  );

  if (aliasBinding && "type_alias" in aliasBinding) {
    const alias = aliasBinding.type_alias;

    // Extend context with parameters before checking body
    const extendedContext: Context = [
      ...alias.params.map((param, i) => typeBinding(param, alias.kinds[i]!)),
      ...state.ctx,
    ];

    // Check the kind of the body with extended context
    const bodyKindResult = checkKind(
      {
        ctx: extendedContext,
        meta: state.meta,
      },
      alias.body,
      lenient,
    );
    if ("err" in bodyKindResult) return bodyKindResult;

    // Build the kind: kind₁ → kind₂ → ... → result_kind
    // Start with the body's kind
    let kind: Kind = bodyKindResult.ok;

    // Build arrow kinds from right to left
    for (let i = alias.params.length - 1; i >= 0; i--) {
      kind = arrowKind(alias.kinds[i]!, kind);
    }

    return ok(kind);
  }

  // Lookup kind in context (like vars) for user-defined type constructors
  const binding = state.ctx.find(
    (b) => "type" in b && b.type.name === type.con,
  );
  if (binding && "type" in binding) return ok(binding.type.kind);

  // Also check for enum definitions
  const enumBinding = state.ctx.find(
    (b) => "enum" in b && b.enum.name === type.con,
  );
  if (enumBinding && "enum" in enumBinding) return ok(enumBinding.enum.kind);

  // Unbound con: Error if strict, else assume * for lenient
  return lenient ? ok(starKind) : err({ unbound: type.con });
}

function checkTupleKind(
  state: TypeCheckerState,
  type: TupleType,
  lenient: boolean,
) {
  // All element types must have kind *
  for (const elemType of type.tuple) {
    const elemKind = checkKind(state, elemType, lenient);
    if ("err" in elemKind) return elemKind;
    if (!isStarKind(elemKind.ok))
      return err({
        kind_mismatch: { expected: starKind, actual: elemKind.ok },
      });
  }
  return ok(starKind);
}

function checkMuKind(state: TypeCheckerState, type: MuType, lenient: boolean) {
  // μα.τ has kind * if τ has kind * in context extended with α::*
  const extendedContext: Context = [
    { type: { name: type.mu.var, kind: starKind } },
    ...state.ctx,
  ];

  const bodyKind = checkKind(
    { ctx: extendedContext, meta: state.meta },
    type.mu.body,
    lenient,
  );
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({
      kind_mismatch: { expected: starKind, actual: bodyKind.ok },
    });

  return ok(starKind);
}

function checkVariantKind(
  state: TypeCheckerState,
  type: VariantType,
  lenient: boolean,
) {
  // All case types must have kind *
  for (const [_, caseType] of type.variant) {
    const caseKind = checkKind(state, caseType, lenient);
    if ("err" in caseKind) return caseKind;

    if (!isBottom(state, caseType) && !isStarKind(caseKind.ok)) {
      return err({
        kind_mismatch: { expected: starKind, actual: caseKind.ok },
      });
    }
  }

  return ok(starKind);
}

function checkRecordKind(
  state: TypeCheckerState,
  type: RecordType,
  lenient: boolean,
) {
  // All field types must have kind *
  for (const [_, fieldType] of type.record) {
    const fieldKind = checkKind(state, fieldType, lenient);
    if ("err" in fieldKind) return fieldKind;

    if (!isStarKind(fieldKind.ok))
      return err({
        kind_mismatch: { expected: starKind, actual: fieldKind.ok },
      });
  }

  return ok(starKind);
}

function checkAppKind(
  state: TypeCheckerState,
  type: AppType,
  lenient: boolean,
) {
  const funcKind = checkKind(state, type.app.func, lenient);
  if ("err" in funcKind) return funcKind;

  const argKind = checkKind(state, type.app.arg, lenient);
  if ("err" in argKind) return argKind;

  if (!("arrow" in funcKind.ok))
    return err({ not_a_type_function: type.app.func });

  if (!kindsEqual(funcKind.ok.arrow.from, argKind.ok)) {
    return err({
      kind_mismatch: { expected: funcKind.ok.arrow.from, actual: argKind.ok },
    });
  }

  return ok(funcKind.ok.arrow.to);
}

function checkLamKind(
  state: TypeCheckerState,
  type: LamType,
  lenient: boolean,
) {
  const extendedContext: Context = [
    { type: { name: type.lam.var, kind: type.lam.kind } },
    ...state.ctx,
  ];

  const bodyKind = checkKind(
    { ctx: extendedContext, meta: state.meta },
    type.lam.body,
    lenient,
  );
  if ("err" in bodyKind) return bodyKind;

  return ok(arrowKind(type.lam.kind, bodyKind.ok));
}

function checkBoundedForallKind(
  state: TypeCheckerState,
  type: BoundedForallType,
  lenient: boolean,
) {
  const extendedContext: Context = [
    {
      type: {
        name: type.bounded_forall.var,
        kind: type.bounded_forall.kind,
      },
    },
    ...state.ctx,
  ];

  const extendedState = { ctx: extendedContext, meta: state.meta };
  // Check that all constraint types are well-kinded
  for (const constraint of type.bounded_forall.constraints) {
    const constraintKind = checkKind(extendedState, constraint.type, lenient);
    if ("err" in constraintKind) return constraintKind;

    if (!isStarKind(constraintKind.ok))
      return err({
        kind_mismatch: {
          expected: starKind,
          actual: constraintKind.ok,
        },
      });
  }

  const bodyKind = checkKind(extendedState, type.bounded_forall.body, lenient);
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: bodyKind.ok } });

  return ok(starKind);
}

function checkVarKind(
  state: TypeCheckerState,
  type: VarType,
  lenient: boolean,
) {
  if (state.meta.kinds.has(type.var))
    return ok(state.meta.kinds.get(type.var)!);

  const binding = state.ctx.find(
    (b) => "type" in b && b.type.name === type.var,
  );
  if (binding && "type" in binding) {
    return ok(binding.type.kind);
  }
  // For subtyping/bottom checks, assume unbound vars have kind * (safe assumption)
  if (lenient) return ok(starKind);
  // Strict mode: unbound is an error
  return err({ unbound: type.var });
}

function checkArrowKind(
  state: TypeCheckerState,
  type: ArrowType,
  lenient: boolean,
) {
  const fromKind = checkKind(state, type.arrow.from, lenient);
  if ("err" in fromKind) return fromKind;

  const toKind = checkKind(state, type.arrow.to, lenient);
  if ("err" in toKind) return toKind;

  // Both operands must have kind *
  if (!isStarKind(fromKind.ok) || !isStarKind(toKind.ok))
    return err({
      kind_mismatch: { expected: starKind, actual: fromKind.ok },
    });

  return ok(starKind);
}

function checkForallKind(
  state: TypeCheckerState,
  type: ForallType,
  lenient: boolean,
) {
  const extendedContext: Context = [
    { type: { name: type.forall.var, kind: type.forall.kind } },
    ...state.ctx,
  ];

  const bodyKind = checkKind(
    {
      ctx: extendedContext,
      meta: state.meta,
    },
    type.forall.body,
    lenient,
  );
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: bodyKind.ok } });

  return ok(starKind);
}

function typesEqualSpine(
  state: TypeCheckerState,
  left: Type,
  right: Type,
): boolean {
  const lArgs = getSpineArgs(left);
  const rArgs = getSpineArgs(right);
  if (lArgs.length !== rArgs.length) return false;
  for (let i = 0; i < lArgs.length; i++) {
    if (!typesEqual(state, lArgs[i]!, rArgs[i]!)) return false;
  }
  return true;
}

/**
 * Determines whether two **types are equal**, after full normalization.
 *
 * This is *structural, alpha‑equivalent* type equality — not pointer equality.
 *
 * In other words, this function answers:
 *
 *    “Do these two types represent the exact same type,
 *     possibly after expanding aliases, normalizing enums,
 *     beta‑reducing type lambdas, and renaming bound variables?”
 *
 * ---------------------------------------------------------------------------
 * How equality is checked
 * ---------------------------------------------------------------------------
 *
 * 1. **Normalization**
 *    Both `left` and `right` are passed through {@link normalizeType}, which:
 *    - expands type aliases
 *    - expands enum applications to structural variants
 *    - beta‑reduces type lambdas
 *    - unfolds μ‑types (recursion) safely
 *
 *    This ensures two types are compared in their “canonical” form.
 *
 * 2. **Structural comparison**
 *    The function recurses into every type constructor:
 *    - arrows: `(A → B) == (A' → B')`
 *    - apps: `(F A) == (F' A')`
 *    - records: same fields after sorting
 *    - variants: same labels + equal payload types
 *    - tuples: same length + equal elements
 *
 * 3. **Alpha‑equivalence**
 *    For binders (`∀`, `λ`, `μ`), bound variable names do *not* matter:
 *
 *    ```
 *    ∀a. a -> a   ==   ∀b. b -> b
 *    μX. T[X]     ==   μY. T[Y]
 *    ```
 *
 *    This works by renaming the right‑hand side’s binder variable to match
 *    the left before comparing bodies (using {@link alphaRename}).
 *
 * 4. **Nominal type applications**
 *    Types like `Either<Int, Bool>` are compared using their **spine**:
 *    - check same constructor (`Either`)
 *    - check each argument pairwise
 *    This is handled by {@link getSpineArgs} and the nominal check branch.
 *
 * ---------------------------------------------------------------------------
 * When typesEqual is used
 * ---------------------------------------------------------------------------
 * - Early exits in unification (if types are already equal)
 * - Checking for exact dictionary matches in traits
 * - Detecting duplicate type definitions
 * - Type printing, debugging tools, and REPL features
 * - Subtyping fast‑path (`isAssignableTo`)
 *
 * ---------------------------------------------------------------------------
 * Important: What typesEqual is *not*
 * ---------------------------------------------------------------------------
 * - It is **not** subtyping
 *   (`Int` is NOT equal to `⊥`, but `⊥` *is* a subtype of `Int`)
 *
 * - It is **not** unification
 *   `typesEqual(?0, Int)` does not bind `?0` — it simply returns false.
 *
 * It only checks whether two fully normalized types are *identical*.
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 * ```ts
 * typesEqual(state, Int, Int);                        // true
 * typesEqual(state, Int, Bool);                       // false
 *
 * // Arrow types
 * typesEqual(state, A → B, A → B);                    // true
 *
 * // Alpha-equivalent polymorphism
 * typesEqual(
 *   state,
 *   forallType("a", *, a → a),
 *   forallType("b", *, b → b)
 * );                                                  // true
 *
 * // Nominal type applications
 * typesEqual(
 *   state,
 *   Either<Int, Bool>,
 *   Either<Int, Bool>
 * );                                                  // true
 *
 * typesEqual(
 *   state,
 *   Either<Int, Bool>,
 *   Either<Bool, Int>
 * );                                                  // false
 * ```
 *
 * ---------------------------------------------------------------------------
 * @param state - Typechecker state (needed for normalization and alias/enum lookup)
 * @param left - First type
 * @param right - Second type
 * @returns `true` if the types are equal after normalization, `false` otherwise
 */
export function typesEqual(
  state: TypeCheckerState,
  left: Type,
  right: Type,
): boolean {
  left = normalizeType(state, left);
  right = normalizeType(state, right);

  if ("evar" in left && "evar" in right && left.evar === right.evar)
    return true;

  if ("var" in left && "var" in right && left.var === right.var) return true;

  if ("con" in left && "con" in right && left.con === right.con) return true;

  if (
    "app" in left &&
    "con" in left.app.func &&
    "app" in right &&
    "con" in right.app.func
  ) {
    if (left.app.func.con !== right.app.func.con) return false;
    return typesEqualSpine(state, left, right); // Pairwise
  }

  if ("never" in left && "never" in right) return true;

  if (
    "arrow" in left &&
    "arrow" in right &&
    typesEqual(state, left.arrow.from, right.arrow.from) &&
    typesEqual(state, left.arrow.to, right.arrow.to)
  )
    return true;

  if ("forall" in left && "forall" in right) {
    const r = right as { forall: { var: string; kind: Kind; body: Type } };
    // Kind must match
    if (!kindsEqual(left.forall.kind, r.forall.kind)) return false;

    // Since bound variables are alpha‑equivalent, rename `r`’s var
    const renamedBody = alphaRename(
      r.forall.var,
      left.forall.var,
      r.forall.body,
    );
    return typesEqual(state, left.forall.body, renamedBody);
  }

  if ("lam" in left && "lam" in right) {
    const r = right as { lam: { var: string; kind: Kind; body: Type } };
    if (!kindsEqual(left.lam.kind, r.lam.kind)) return false;

    // Alpha‑equivalence: rename RHS variable
    const renamedBody = alphaRename(r.lam.var, left.lam.var, r.lam.body);
    return typesEqual(state, left.lam.body, renamedBody);
  }

  if ("app" in left && "app" in right) {
    const r = right as { app: { func: Type; arg: Type } };
    return (
      typesEqual(state, left.app.func, r.app.func) &&
      typesEqual(state, left.app.arg, r.app.arg)
    );
  }

  if ("record" in left && "record" in right) {
    const leftFields = left.record;
    const rightFields = right.record;

    const leftLabels = leftFields.map(first).sort();
    const rightLabels = rightFields.map(first).sort();

    // Must have same labels
    if (leftLabels.length !== rightLabels.length) return false;
    if (!leftLabels.every((l, i) => l === rightLabels[i])) return false;

    // All field types must be equal
    return leftLabels.every((label) =>
      typesEqual(
        state,
        leftFields.find((t) => t[0] === label)![1],
        rightFields.find((t) => t[0] === label)![1],
      ),
    );
  }

  if ("bounded_forall" in left && "bounded_forall" in right) {
    if (!kindsEqual(left.bounded_forall.kind, right.bounded_forall.kind))
      return false;

    // Check constraints match
    if (
      left.bounded_forall.constraints.length !==
      right.bounded_forall.constraints.length
    )
      return false;

    for (let i = 0; i < left.bounded_forall.constraints.length; i++) {
      const lc = left.bounded_forall.constraints[i]!;
      const rc = right.bounded_forall.constraints[i]!;

      if (lc.trait !== rc.trait) return false;

      const renamedConstraintType = alphaRename(
        right.bounded_forall.var,
        left.bounded_forall.var,
        rc.type,
      );

      if (!typesEqual(state, lc.type, renamedConstraintType)) return false;
    }
    const renamedBody = alphaRename(
      right.bounded_forall.var,
      left.bounded_forall.var,
      right.bounded_forall.body,
    );
    return typesEqual(state, left.bounded_forall.body, renamedBody);
  }

  if ("variant" in left && "variant" in right) {
    const leftCases = left.variant;
    const rightCases = right.variant;

    const leftLabels = leftCases.map(first).sort();
    const rightLabels = rightCases.map(first).sort();

    // Must have same labels
    if (leftLabels.length !== rightLabels.length) return false;
    if (!leftLabels.every((l, i) => l === rightLabels[i])) return false;

    // All case types must be equal
    return leftLabels.every((label) =>
      typesEqual(
        state,
        leftCases.find((t) => t[0] === label)![1],
        rightCases.find((t) => t[0] === label)![1],
      ),
    );
  }

  if ("mu" in left && "mu" in right) {
    // μα.τ₁ = μβ.τ₂ if τ₁ = τ₂[β/α]
    const renamedBody = alphaRename(right.mu.var, left.mu.var, right.mu.body);
    return typesEqual(state, left.mu.body, renamedBody);
  }

  if ("tuple" in left && "tuple" in right) {
    if (left.tuple.length !== right.tuple.length) return false;

    return left.tuple.every((leftElem, i) =>
      typesEqual(state, leftElem, right.tuple[i]!),
    );
  }

  return false;
}

/**
 * Performs **alpha‑renaming** inside a type:
 *
 *    alphaRename(from, to, type)
 *
 * meaning:
 *
 *    “Rename all **free** occurrences of type variable `from`
 *     to the variable name `to`, without touching bound occurrences.”
 *
 * ---------------------------------------------------------------------------
 * Why alpha‑renaming matters
 * ---------------------------------------------------------------------------
 * This operation ensures that two types with different binder names are treated
 * as equivalent when comparing them.
 * For example:
 *
 * ```
 * ∀a. a → a
 * ∀b. b → b
 * ```
 *
 * These are the **same type**, even though the binder uses a different name.
 * `alphaRename` makes bound-variable names consistent so that
 * {@link typesEqual} can compare the bodies structurally.
 *
 * ---------------------------------------------------------------------------
 * What counts as a “bound” variable?
 * ---------------------------------------------------------------------------
 * A variable is *bound* when introduced by:
 * - `forall A::κ. ...`
 * - `λA::κ. ...` (type-level lambda)
 * - `μA. ...` (recursive types)
 * - `∀{constraints}. ...` (bounded forall)
 *
 * In these cases:
 * - If the binder uses the same name as `from`, renaming **stops** — the
 *   bound variable shadows the outer name.
 *
 * ---------------------------------------------------------------------------
 * Behavior summary
 * ---------------------------------------------------------------------------
 * - If `from === to` → no change.
 * - Free occurrences of `from` become `to`.
 * - Bound occurrences are **not** renamed (binder‑safe).
 * - Recursively renames inside:
 *   - arrows
 *   - applications
 *   - records
 *   - variants
 *   - tuples
 *   - forall / bounded_forall (except bound variable)
 *   - lam and mu types (except bound variable)
 *
 * ---------------------------------------------------------------------------
 * Used in:
 * ---------------------------------------------------------------------------
 * - {@link typesEqual} — checking alpha‑equivalent types
 * - {@link unifyTypes} — comparing polymorphic types
 * - Everywhere we treat type binders as renamable identifiers
 *
 * ---------------------------------------------------------------------------
 * @param from - The variable name to rename (e.g., `"a"`)
 * @param to - The new variable name (e.g., `"X"`)
 * @param type - The type expression being renamed
 * @returns A type with free occurrences of `from` rewritten to `to`
 *
 * ---------------------------------------------------------------------------
 * @example Renaming free variables:
 * ```ts
 * alphaRename("a", "X", arrowType(varType("a"), varType("b")));
 * // => (X → b)
 * ```
 *
 * @example Bound variable is shadowed (renaming skipped):
 * ```ts
 * const t = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * alphaRename("a", "X", t)
 * // => ∀a::*. (a → b)   (inner 'a' is bound)
 * ```
 */
export function alphaRename(from: string, to: string, type: Type): Type {
  if (from === to) return type; // no need to rename

  if ("var" in type) return type.var === from ? { var: to } : type;

  if ("arrow" in type)
    return {
      arrow: {
        from: alphaRename(from, to, type.arrow.from),
        to: alphaRename(from, to, type.arrow.to),
      },
    };

  if ("forall" in type) {
    if (type.forall.var === from) return type; // shadowed, stop
    return {
      forall: {
        var: type.forall.var,
        kind: type.forall.kind,
        body: alphaRename(from, to, type.forall.body),
      },
    };
  }

  if ("lam" in type) {
    if (type.lam.var === from) return type; // shadowed
    return {
      lam: {
        var: type.lam.var,
        kind: type.lam.kind,
        body: alphaRename(from, to, type.lam.body),
      },
    };
  }

  if ("bounded_forall" in type) {
    if (type.bounded_forall.var === from) return type;
    return {
      bounded_forall: {
        var: type.bounded_forall.var,
        kind: type.bounded_forall.kind,
        constraints: type.bounded_forall.constraints.map((c) => ({
          trait: c.trait,
          type: alphaRename(from, to, c.type),
        })),
        body: alphaRename(from, to, type.bounded_forall.body),
      },
    };
  }

  if ("app" in type) {
    return {
      app: {
        func: alphaRename(from, to, type.app.func),
        arg: alphaRename(from, to, type.app.arg),
      },
    };
  }

  if ("record" in type) {
    const record: [string, Type][] = [];
    for (const [label, fieldType] of type.record) {
      record.push([label, alphaRename(from, to, fieldType)]);
    }
    return { record };
  }

  if ("variant" in type) {
    const variant: [string, Type][] = [];
    for (const [label, caseType] of type.variant) {
      variant.push([label, alphaRename(from, to, caseType)]);
    }
    return { variant };
  }

  if ("mu" in type) {
    if (type.mu.var === from) return type; // shadowed
    return {
      mu: {
        var: type.mu.var,
        body: alphaRename(from, to, type.mu.body),
      },
    };
  }

  if ("tuple" in type) {
    return {
      tuple: type.tuple.map((t) => alphaRename(from, to, t)),
    };
  }

  return type;
}

/**
 * Attempts to **unify two types** (`left ~ right`) and records any resulting
 * meta‑variable bindings in the provided substitution map.
 *
 * This is the heart of the type inference engine.
 *
 * ---------------------------------------------------------------------------
 * What “unification” means
 * ---------------------------------------------------------------------------
 * Unification attempts to make two types **structurally identical** by:
 * - Expanding aliases / enums / lambdas (`normalizeType`)
 * - Equating corresponding subcomponents
 * - Solving meta‑variables (`?0 := Int`)
 * - Adding new type‑equality constraints to the worklist
 *
 * If successful, the caller’s substitution map `subst` accumulates bindings that
 * describe how unknown types should be instantiated.
 *
 * If unification fails → returns a `type_mismatch` or other error.
 *
 * ---------------------------------------------------------------------------
 * Why unification is needed
 * ---------------------------------------------------------------------------
 * - Inferring types of applications (`f x`)
 * - Matching polymorphic types to concrete instantiations
 * - Checking record/variant structure compatibility
 * - Solving trait constraints
 * - Merging match branch types
 *
 * Unification is the “engine” behind all higher‑order inference.
 *
 * ---------------------------------------------------------------------------
 * Overview of the unification algorithm
 * ---------------------------------------------------------------------------
 * 1. **Normalize** both types to eliminate syntactic noise
 *    (aliases, enums, beta‑reduction, μ‑unfolding).
 *
 * 2. **Trivial equality**
 *    If types are already equal (`typesEqual`) → succeed immediately.
 *
 * 3. **Cyclic μ‑type detection**
 *    Reject degenerate recursive types like:
 *      μX. X
 *
 * 4. **Bottom‑type rules (`⊥`)**
 *    Special asymmetric behavior:
 *      - `⊥ ~ T` succeeds if `T :: *`
 *      - `T ~ ⊥` only when `T` is also bottom
 *
 * 5. **Rigid–rigid mismatch**
 *    Concrete types (`Int`, `Bool`, arrow types, variants, etc.)
 *    must match structurally or unification fails.
 *
 * 6. **Flex–rigid (meta‑variable binding)**
 *    A meta‑variable (`?N`) can unify with any type of appropriate kind,
 *    unless doing so would create a cycle (occurs‑check).
 *
 * 7. **Nominal application unification**
 *    For types like:
 *      Either<Int, Bool> ~ Either<a, b>
 *    unify their spines argument‑by‑argument.
 *
 * 8. **Structural unification**
 *    Recurse into:
 *      - arrows
 *      - apps
 *      - foralls / bounded foralls
 *      - records (label‑matching + width subtyping)
 *      - variants (label‑matching)
 *      - tuples
 *      - μ‑types
 *
 * 9. **Add constraints to the worklist**
 *    Instead of solving immediately, unification produces **type‑equality
 *    constraints** which `solveConstraints` resolves afterward.
 *
 * ---------------------------------------------------------------------------
 * Substitution behavior
 * ---------------------------------------------------------------------------
 * - `subst` stores *local* meta‑variable solutions for this unification step
 * - global solutions live in `state.meta.solutions`
 * - both are consulted during meta‑var resolution
 * - occurs‑check prevents:
 *     `?0 := (?0 → Int)`
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `type_mismatch`: incompatible structures
 * - `cyclic`: illegal recursive type detected
 * - `kind_mismatch`: meta‑variable or nested type kind conflict
 * - `not_a_variant` / `not_a_record` / etc. from structural mismatch
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 * Basic unification:
 * ```ts
 * unifyTypes(state, varType("a"), conType("Int"), worklist, subst);
 * // => subst["a"] = Int
 * ```
 *
 * Unifying arrows:
 * ```ts
 * unifyTypes(state, A → B, Int → Bool)
 * // => worklist adds constraints: A = Int, B = Bool
 * ```
 *
 * Enum applications:
 * ```ts
 * unifyTypes(state,
 *   Either<Int, Bool>,
 *   Either<a, b>
 * );
 * // => a = Int, b = Bool
 * ```
 *
 * Bottom rules:
 * ```ts
 * unifyTypes(state, ⊥, Int);    // ok
 * unifyTypes(state, Int, ⊥);    // error
 * ```
 *
 * ---------------------------------------------------------------------------
 * @param state - Complete typechecker state (context + meta-env)
 * @param left - First type to unify
 * @param right - Second type to unify
 * @param worklist - Accumulates type-equality constraints to solve later
 * @param subst - Local substitution map mutated with meta‑variable bindings
 * @returns `ok(null)` on success or a `TypingError` on failure
 */
export function unifyTypes(
  state: TypeCheckerState,
  left: Type,
  right: Type,
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  left = normalizeType(state, left);
  right = normalizeType(state, right);

  if (typesEqual(state, left, right)) return ok(null);

  if ("mu" in left && "var" in left.mu.body && left.mu.body.var === left.mu.var)
    return err({ cyclic: left.mu.var });
  if (
    "mu" in right &&
    "var" in right.mu.body &&
    right.mu.body.var === right.mu.var
  )
    return err({ cyclic: right.mu.var });

  if (isBottom(state, left) && isBottom(state, right)) return ok(null);

  // ⊥ <: right? Check right :: *
  if (isBottom(state, left)) {
    // Empty ctx for base kind check
    const rightKind = checkKind({ ctx: [], meta: state.meta }, right, true);
    if ("err" in rightKind || !isStarKind(rightKind.ok))
      return err({ type_mismatch: { expected: right, actual: left } });

    return ok(null);
  }

  if (isBottom(state, right))
    // Unification is asymmetric: left ~ ⊥ only if left is also ⊥
    // (since non-bottom types are not subtypes of bottom)
    return isBottom(state, left)
      ? ok(null)
      : err({ type_mismatch: { expected: right, actual: left } });

  const leftRigid = "var" in left && !isMetaVar(left);
  const rightRigid = "var" in right && !isMetaVar(right);

  if (leftRigid && rightRigid)
    return typesEqual(state, left, right)
      ? ok(null)
      : err({ type_mismatch: { expected: left, actual: right } });

  if (leftRigid) {
    // Check for cycles with rigid variables
    if ("var" in left && occursCheck(left.var, right))
      return err({ cyclic: left.var });

    if ("var" in right && isMetaVar(right))
      return unifyVariable(state, right.var, left, subst);

    return err({ type_mismatch: { expected: left, actual: right } });
  }

  if (rightRigid) return unifyTypes(state, right, left, worklist, subst);

  // Variable cases
  if ("var" in left) return unifyVariable(state, left.var, right, subst);

  if ("var" in right) return unifyVariable(state, right.var, left, subst);

  const unifyFlex = (
    flexName: string,
    rigidTy: Type,
  ): Result<TypingError, null> => {
    const appliedTy = applySubstitution(
      state,
      subst,
      normalizeType(state, rigidTy),
    ); // Local subst first
    // Global sol?
    if (state.meta.solutions.has(flexName)) {
      const existing = normalizeType(
        state,
        state.meta.solutions.get(flexName)!,
      );
      return unifyTypes(state, existing, appliedTy, worklist, subst);
    }
    // Local subst?
    if (subst.has(flexName)) {
      const existing = applySubstitution(state, subst, subst.get(flexName)!);
      return unifyTypes(state, existing, appliedTy, worklist, subst);
    }
    // Occurs (follow global sols; local subst already applied)
    if (occursCheckEvar(state.meta, flexName, appliedTy))
      return err({ cyclic: flexName });
    subst.set(flexName, appliedTy); // Bind locally
    return ok(null);
  };

  if (isMetaVar(left)) return unifyFlex(left.evar, right);
  if (isMetaVar(right)) return unifyFlex(right.evar, left);

  if (
    "app" in left &&
    "con" in left.app.func &&
    "app" in right &&
    "con" in right.app.func
  ) {
    // Nominal enum unification: same head, unify spines
    if (left.app.func.con !== right.app.func.con)
      return err({ type_mismatch: { expected: left, actual: right } });

    const leftArgs = getSpineArgs(left);
    const rightArgs = getSpineArgs(right);
    if (leftArgs.length !== rightArgs.length)
      return err({ type_mismatch: { expected: left, actual: right } });

    for (let i = 0; i < leftArgs.length; i++)
      worklist.push(typeEq(leftArgs[i]!, rightArgs[i]!));

    return ok(null);
  }
  if ("app" in left && "con" in left.app.func && "variant" in right) {
    const enumName = left.app.func.con;
    const enumBinding = state.ctx.find(
      (b) => "enum" in b && b.enum.name === enumName,
    );
    if (enumBinding && "enum" in enumBinding) {
      const def = enumBinding.enum;
      const leftArgs = getSpineArgs(left);
      if (leftArgs.length !== def.params.length)
        return err({ type_mismatch: { expected: left, actual: right } });

      // Check variant labels match
      const rightLabels = new Set(right.variant.map(([l]) => l));
      const defLabels = new Set(def.variants.map(([l]) => l));
      if (
        !Array.from(rightLabels).every((l) => defLabels.has(l)) ||
        rightLabels.size !== defLabels.size
      )
        return err({ type_mismatch: { expected: left, actual: right } });

      // Unify each case: Instantiate def variant with leftArgs, unify with right case
      for (const [label, rightCase] of right.variant) {
        const defVariant = def.variants.find(([l]) => l === label);
        if (!defVariant)
          return err({ type_mismatch: { expected: left, actual: right } });
        let instCase = defVariant[1];
        for (let i = 0; i < def.params.length; i++) {
          instCase = substituteType(def.params[i]!, leftArgs[i]!, instCase);
        }
        worklist.push(typeEq(instCase, rightCase));
      }
      return ok(null);
    }
  }
  // Symmetric: variant ~ app(con)
  if ("variant" in left && "app" in right && "con" in right.app.func) {
    return unifyTypes(state, right, left, worklist, subst); // Swap
  }

  // Also, for app vs. legacy variant: mismatch (or convert, but migrate to nominal)
  if (
    ("app" in left && "con" in left.app.func && "variant" in right) ||
    ("variant" in left && "app" in right && "con" in right.app.func)
  ) {
    return err({ type_mismatch: { expected: left, actual: right } });
  }

  // After the early bottom cases and before other structural cases
  if ("arrow" in left && "arrow" in right)
    return unifyArrowTypes(left, right, worklist, subst);

  // Special case: Bottom-domain functions (⊥ → α ~ τ₁ → τ₂)
  if ("arrow" in left && "arrow" in right && isBottom(state, left.arrow.from)) {
    // Bottom domain matches anything, so only unify codomains
    worklist.push(typeEq(left.arrow.to, right.arrow.to));

    // Note: We might want to collect τ₁ as a constraint for α if needed,
    // but for now just succeed since ⊥ is a valid subtype
    return ok(null);
  }

  // Symmetric case: functions with bottom domain on right
  if (
    "arrow" in left &&
    "arrow" in right &&
    isBottom(state, right.arrow.from)
  ) {
    // Only unify codomains, ignore domains
    worklist.push(typeEq(left.arrow.to, right.arrow.to));
    return ok(null);
  }

  if ("forall" in left && "forall" in right)
    return unifyForallTypes(left, right, worklist, subst);

  if ("bounded_forall" in left && "bounded_forall" in right)
    return unifyBoundedForallTypes(left, right, worklist, subst);

  if ("app" in left && "app" in right)
    return unifyAppTypes(left, right, worklist, subst);

  if ("lam" in left && "lam" in right)
    return unifyLamTypes(left, right, worklist, subst);

  if ("record" in left && "record" in right)
    return unifyRecordTypes(left, right, worklist, subst);

  if ("variant" in left && "variant" in right)
    return unifyVariants(left, right, worklist, subst);

  if ("mu" in left && "mu" in right)
    return unifyMuTypes(left, right, worklist, subst);

  if ("tuple" in left && "tuple" in right)
    return unifyTupleTypes(left, right, worklist, subst);

  return err({ type_mismatch: { expected: left, actual: right } });
}

function unifyTupleTypes(
  left: TupleType,
  right: TupleType,
  worklist: Worklist,
  _subst: Substitution,
) {
  if (left.tuple.length !== right.tuple.length)
    return err({ type_mismatch: { expected: left, actual: right } });

  // Unify all element types
  for (let i = 0; i < left.tuple.length; i++)
    worklist.push(typeEq(left.tuple[i]!, right.tuple[i]!));

  return ok(null);
}

function unifyMuTypes(
  left: MuType,
  right: MuType,
  worklist: Worklist,
  _subst: Substitution,
) {
  // Unify bodies after alpha-renaming
  const renamedRight = alphaRename(right.mu.var, left.mu.var, right.mu.body);
  worklist.push(typeEq(left.mu.body, renamedRight));
  return ok(null);
}

function unifyVariants(
  left: VariantType,
  right: VariantType,
  worklist: Worklist,
  _subst: Substitution,
) {
  const leftCases = left.variant;
  const rightCases = right.variant;

  const leftLabels = leftCases.map(first).sort();
  const rightLabels = rightCases.map(first).sort();

  // Must have same labels
  if (leftLabels.length !== rightLabels.length)
    return err({ type_mismatch: { expected: left, actual: right } });

  for (let i = 0; i < leftLabels.length; i++) {
    if (leftLabels[i] !== rightLabels[i])
      return err({ type_mismatch: { expected: left, actual: right } });
  }

  // Unify all case types
  for (const label of leftLabels) {
    worklist.push(
      typeEq(
        leftCases.find((t) => t[0] === label)![1],
        rightCases.find((t) => t[0] === label)![1],
      ),
    );
  }

  return ok(null);
}

function unifyRecordTypes(
  left: RecordType,
  right: RecordType,
  worklist: Worklist,
  _subst: Substitution,
) {
  const leftFields = left.record;
  const rightFields = right.record;

  const leftLabels = leftFields.map(first).sort();
  const rightLabels = rightFields.map(first).sort();

  const rightLabelSet = new Set(rightLabels);

  // Check if this is a width subtyping scenario
  // Right (specific) has all left's (general) fields (possibly more)
  const leftIsSubset = leftLabels.every((l) => rightLabelSet.has(l));

  if (leftIsSubset) {
    // Width subtyping: right <: left if right has all of left's fields
    // Unify only the common fields
    for (const [label, leftType] of left.record) {
      const rightField = right.record.find(([l]) => l === label);
      if (!rightField) {
        // Should never happen given leftIsSubset check
        return err({ missing_field: { record: right, label } });
      }
      worklist.push(typeEq(leftType, rightField[1]));
    }
    return ok(null);
  }

  // Must have same labels
  if (leftLabels.length !== rightLabels.length)
    return err({ type_mismatch: { expected: left, actual: right } });

  for (let i = 0; i < leftLabels.length; i++) {
    if (leftLabels[i] !== rightLabels[i])
      return err({ type_mismatch: { expected: left, actual: right } });
  }

  // Unify all field types
  for (const label of leftLabels) {
    worklist.push(
      typeEq(
        leftFields.find((t) => t[0] === label)![1],
        rightFields.find((t) => t[0] === label)![1],
      ),
    );
  }

  return ok(null);
}

function unifyLamTypes(
  left: LamType,
  right: LamType,
  worklist: Worklist,
  _subst: Substitution,
) {
  // Check kinds immediately
  if (!kindsEqual(left.lam.kind, right.lam.kind)) {
    return err({
      kind_mismatch: {
        expected: left.lam.kind,
        actual: right.lam.kind,
      },
    });
  }

  const renamedRight = alphaRename(right.lam.var, left.lam.var, right.lam.body);
  worklist.push(typeEq(left.lam.body, renamedRight));

  return ok(null);
}

function unifyAppTypes(
  left: AppType,
  right: AppType,
  worklist: Worklist,
  _subst: Substitution,
) {
  worklist.push(typeEq(left.app.func, right.app.func));
  worklist.push(typeEq(left.app.arg, right.app.arg));
  return ok(null);
}

function unifyForallTypes(
  left: ForallType,
  right: ForallType,
  worklist: Worklist,
  _subst: Substitution,
) {
  // Check kinds immediately
  if (!kindsEqual(left.forall.kind, right.forall.kind)) {
    return err({
      kind_mismatch: {
        expected: left.forall.kind,
        actual: right.forall.kind,
      },
    });
  }

  // Alpha-rename if necessary and unify bodies
  const renamedRight = alphaRename(
    right.forall.var,
    left.forall.var,
    right.forall.body,
  );
  worklist.push(typeEq(left.forall.body, renamedRight));

  return ok(null);
}

function unifyArrowTypes(
  left: ArrowType,
  right: ArrowType,
  worklist: Worklist,
  _subst: Substitution,
) {
  // Standard arrow unification - requires both domains and codomains to match
  worklist.push(typeEq(left.arrow.from, right.arrow.from));
  worklist.push(typeEq(left.arrow.to, right.arrow.to));
  return ok(null);
}

function unifyBoundedForallTypes(
  left: BoundedForallType,
  right: BoundedForallType,
  worklist: Worklist,
  _subst: Substitution,
) {
  // Check kinds immediately
  if (!kindsEqual(left.bounded_forall.kind, right.bounded_forall.kind)) {
    return err({
      kind_mismatch: {
        expected: left.bounded_forall.kind,
        actual: right.bounded_forall.kind,
      },
    });
  }

  // Check constraints match
  if (
    left.bounded_forall.constraints.length !==
    right.bounded_forall.constraints.length
  )
    return err({ type_mismatch: { expected: left, actual: right } });

  for (let i = 0; i < left.bounded_forall.constraints.length; i++) {
    const lc = left.bounded_forall.constraints[i]!;
    const rc = right.bounded_forall.constraints[i]!;

    if (lc.trait !== rc.trait)
      return err({ type_mismatch: { expected: left, actual: right } });

    const renamedConstraintType = alphaRename(
      right.bounded_forall.var,
      left.bounded_forall.var,
      rc.type,
    );

    worklist.push(typeEq(lc.type, renamedConstraintType));
  }

  const renamedRight = alphaRename(
    right.bounded_forall.var,
    left.bounded_forall.var,
    right.bounded_forall.body,
  );
  worklist.push(typeEq(left.bounded_forall.body, renamedRight));

  return ok(null);
}

/**
 * Unifies a **rigid type variable** (`varName`) with another type.
 *
 * This is the rigid‑flex version of unification:
 *
 *    α ~ τ
 *
 * where `α` is a *named type variable* (not a meta‑variable) and `τ` is any type.
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * Type variables introduced by:
 * - `∀α. ...` (polymorphism)
 * - type‑level lambdas (`λα. ...`)
 * - recursive types (`μα. ...`)
 *
 * must obey **rigid** unification rules:
 * they cannot be arbitrarily rewritten unless the rules allow it.
 *
 * The rules implemented here are:
 *
 * 1. **If α already has a substitution in `subst`:**
 *    Check that the new type is consistent with the existing one
 *    (using {@link typesEqual}).
 *
 * 2. **α ~ α**
 *    A trivial tautology — succeed immediately.
 *
 * 3. **Bottom type rule**
 *    If the type is bottom (`⊥`), do *not* bind α; simply succeed.
 *    Bottom is a subtype of all types (`⊥ <: τ`) and can unify with anything,
 *    but should not change the substitution environment.
 *
 * 4. **Occurs check (cycle detection)**
 *    Disallow recursive bindings like:
 *      α := (α → Int)
 *    If such a cycle is detected, report a `cyclic` error.
 *
 * 5. **Otherwise, bind α := type**
 *    This adds a new entry to the local substitution map.
 *
 * This is similar to the flex‑rigid case of `unifyTypes`, but specialized
 * for *named* type variables (not meta‑vars).
 *
 * ---------------------------------------------------------------------------
 * Why rigid type variables need special handling
 * ---------------------------------------------------------------------------
 * - Meta‑variables (`?0`) are flexible: they can unify with anything.
 * - Rigid variables (`A`, `Self`, etc.) behave like *constants*
 *   unless inference rules explicitly allow solving them.
 *
 * This prevents improperly instantiating a polymorphic function or violating
 * the scoping of quantified type variables.
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `type_mismatch`: conflicting substitution for α
 * - `cyclic`: type α occurs inside the type being assigned
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 * **Successful bind**
 * ```ts
 * unifyVariable(state, "A", Int, subst);
 * // subst["A"] = Int
 * ```
 *
 * **Tautology**
 * ```ts
 * unifyVariable(state, "A", varType("A"), subst);  // ok
 * ```
 *
 * **Bottom rule**
 * ```ts
 * unifyVariable(state, "A", neverType, subst);  // ok, no binding created
 * ```
 *
 * **Cycle detection**
 * ```ts
 * unifyVariable(state, "A", A → Int, subst);
 * // err: { cyclic: "A" }
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link unifyTypes} — top‑level unification algorithm
 * - {@link occursCheck} — detects illegal cycles
 * - {@link isBottom} — bottom‑type rule
 * - {@link typesEqual} — structural equality for consistency checks
 *
 * @param state - Typechecker state (needed for bottom checks, normalization)
 * @param varName - The rigid type variable to unify (e.g. "A")
 * @param type - The type we want to unify it with
 * @param subst - Current substitution map (mutated on success)
 * @returns `ok(null)` on success or a `TypingError` on failure
 */
export function unifyVariable(
  state: TypeCheckerState,
  varName: string,
  type: Type,
  subst: Substitution,
): Result<TypingError, null> {
  if (subst.has(varName)) {
    const existing = subst.get(varName)!;
    return typesEqual(state, existing, type)
      ? ok(null)
      : err({ type_mismatch: { expected: existing, actual: type } });
  }

  // var ~ var (tautology)
  if ("var" in type && type.var === varName) return ok(null);

  if (isBottom(state, type)) {
    // Find var's binding kind (if bound in context, but since subst doesn't have kinds, assume *)
    // Check occurs to avoid cycles, but allow ⊥ <: var
    if (occursCheck(varName, type)) return err({ cyclic: varName });
    // Don't bind var := ⊥ - just succeed (subtyping will handle later)
    return ok(null);
  }

  // Occurs check (with degenerate mu detection)
  if (occursCheck(varName, type)) {
    // Check if it's a degenerate mu type
    if (
      "mu" in type &&
      "var" in type.mu.body &&
      type.mu.body.var === type.mu.var
    )
      return err({ cyclic: type.mu.var }); // Report the mu variable
    return err({ cyclic: varName });
  }

  subst.set(varName, type);
  return ok(null);
}

/**
 * Unifies two **kinds**, producing a `kind_mismatch` error if they differ.
 *
 * What it checks:
 * ---------------------------------------
 * - Kind equality is purely **structural**:
 *   - `*` unifies with `*`
 *   - `* → *` unifies with `* → *`
 *     (recursively unifying input and output kinds)
 * - Uses {@link kindsEqual} for the structural comparison.
 *
 * Why it matters:
 * ---------------------------------------
 * Kind unification is the kind‑level analogue of type unification.
 * It ensures type constructors are used correctly:
 *
 * - `List :: * → *`
 * - `List<Int> :: *`
 * - `Int<Int>` → error (`Int :: *`, not `* → *`)
 *
 * This function is used by:
 * - the constraint solver (`processConstraint`)
 * - type application kind checking (`checkAppKind`)
 * - polymorphic binder validation (`checkForallKind`, `checkLamKind`)
 *
 * Errors produced:
 * - `kind_mismatch`: kinds differ structurally
 *
 * @param left - The first kind
 * @param right - The second kind
 * @returns `ok(null)` if equal, otherwise `kind_mismatch`
 *
 * @example
 * ```ts
 * unifyKinds(starKind, starKind);                  // ok
 * unifyKinds(arrowKind(starKind, starKind),
 *            arrowKind(starKind, starKind));       // ok
 *
 * unifyKinds(starKind, arrowKind(starKind, starKind));
 * // err({ kind_mismatch: ... })
 * ```
 */
export function unifyKinds(left: Kind, right: Kind): Result<TypingError, null> {
  if (kindsEqual(left, right)) return ok(null);
  return err({ kind_mismatch: { expected: left, actual: right } });
}

/**
 * Performs the **occurs check** for a *rigid* type variable.
 *
 * In other words, this tests whether a type variable `varName` appears
 * **anywhere inside** a type expression `type`.
 *
 * This is used to prevent forming **infinite types**, such as:
 *
 *    a = (a → Int)
 *
 * which cannot exist in this type system.
 *
 * ---------------------------------------------------------------------------
 * What it does
 * ---------------------------------------------------------------------------
 * - Recursively walks the structure of `type`
 * - Returns `true` if it finds a **free occurrence** of `varName`
 * - Ignores *bound* occurrences of the variable:
 *     - inside `∀a. ...`
 *     - inside `λα. ...` (type lambdas)
 *     - inside `μa. ...` (recursive types)
 *
 * If a bound variable shadows `varName`, the search stops at that binder.
 *
 * ---------------------------------------------------------------------------
 * Why this is needed
 * ---------------------------------------------------------------------------
 * During unification, when trying to bind a rigid variable:
 *
 *    a := τ
 *
 * we must ensure `a` does not appear anywhere inside `τ`.
 * Failing to do this would create illegal self‑referential types.
 *
 * Example of a cycle:
 * ```ts
 * occursCheck("A", arrowType(varType("A"), Int));
 * // => true (A occurs inside the type)
 *
 * unifyVariable(...) would reject this binding.
 * ```
 *
 * Example of a safe case:
 * ```ts
 * occursCheck("A", forallType("A", *, varType("A")));
 * // => false (inner A is bound/shadowed)
 * ```
 *
 * ---------------------------------------------------------------------------
 * Algorithm summary
 * ---------------------------------------------------------------------------
 * - If `type` is `varType(varName)` → return `true`
 * - If type is a binder with the same name (`∀A`, `λA`, `μA`) → stop (shadowed)
 * - Otherwise, recurse into all child types
 *
 * ---------------------------------------------------------------------------
 * Used by
 * ---------------------------------------------------------------------------
 * - {@link unifyVariable}
 * - {@link unifyTypes}
 *
 * @param varName - The variable we are checking for (e.g. `"A"`)
 * @param type - The type expression to scan
 * @returns `true` if `varName` occurs free inside `type`
 */
export function occursCheck(varName: string, type: Type): boolean {
  if ("var" in type) return type.var === varName;

  if ("arrow" in type)
    return (
      occursCheck(varName, type.arrow.from) ||
      occursCheck(varName, type.arrow.to)
    );

  if ("forall" in type) {
    if (type.forall.var === varName) return false;
    return occursCheck(varName, type.forall.body);
  }

  if ("lam" in type) {
    if (type.lam.var === varName) return false;
    return occursCheck(varName, type.lam.body);
  }

  if ("app" in type)
    return (
      occursCheck(varName, type.app.func) || occursCheck(varName, type.app.arg)
    );

  if ("record" in type)
    return type.record.some((fieldType) => occursCheck(varName, fieldType[1]));

  if ("variant" in type)
    return type.variant.some((caseType) => occursCheck(varName, caseType[1]));

  if ("mu" in type) {
    if (type.mu.var === varName) return false; // bound

    // Detect degenerate mu: μM.M (body is just the bound var)
    if ("var" in type.mu.body && type.mu.body.var === type.mu.var)
      // This is cyclic - report as if varName occurs
      return true;

    return occursCheck(varName, type.mu.body);
  }

  if ("tuple" in type)
    return type.tuple.some((elementType) => occursCheck(varName, elementType));

  return false;
}

/**
 * Applies a **type substitution** to a type.
 *
 * This resolves:
 *   - **meta‑variables** (`?0`, `?1`, …) using both local `subst`
 *     and global `state.meta.solutions`
 *   - **rigid type variables** (`A`, `Self`, etc.) using `subst` only
 *
 * In other words:
 *
 *    applySubstitution(state, subst, τ)
 *
 * replaces any variables mentioned in `subst` with their solutions,
 * recursively rewriting the structure of `τ`.
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * After unification or constraint solving, we accumulate substitutions such as:
 *
 *   ?0 := Int
 *   A  := Bool
 *
 * These substitutions must be applied to types produced later in inference:
 * - results of `inferType`
 * - branch types in `inferMatchType`
 * - type arguments in polymorphic applications
 * - dictionary instantiation for traits
 *
 * `applySubstitution` ensures types remain **up‑to‑date** with the solver.
 *
 * ---------------------------------------------------------------------------
 * Behavior summary
 * ---------------------------------------------------------------------------
 *
 * **Meta‑variables (`?N`):**
 * - If solved in `subst`, replace with its value
 * - Otherwise, if solved in `state.meta.solutions`, replace with that value
 * - Otherwise, leave as an unsolved meta‑variable
 *
 * **Rigid type variables (`A`):**
 * - If bound in `subst`, replace recursively
 * - Otherwise, leave unchanged
 *
 * **Binders** (`∀A`, `λα`, `μα`):
 * - Substitution must **not** rewrite a bound variable
 *   (to avoid capture or invalid types)
 * - We remove the bound variable name from `subst` for the recursive call
 *
 * **Composite types**:
 * - Recurse into every sub‑type: arrows, apps, records, tuples, variants, etc.
 *
 * ---------------------------------------------------------------------------
 * Cycle prevention
 * ---------------------------------------------------------------------------
 * The optional `visited` set tracks rigid type variables already substituted.
 * This prevents infinite loops when substitutions form chains like:
 *
 *   A := B, B := A
 *
 * or when substitution expands into another variable referencing the first.
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Meta‑variable resolution**
 * ```ts
 * subst = new Map([["?0", Int]]);
 * applySubstitution(state, subst, ?0)
 * // => Int
 * ```
 *
 * **Rigid variable chain**
 * ```ts
 * subst = new Map([
 *   ["A", varType("B")],
 *   ["B", conType("Int")]
 * ]);
 *
 * applySubstitution(state, subst, varType("A"))
 * // => Int
 * ```
 *
 * **Binder safety**
 * ```ts
 * const poly = forallType("A", *, arrowType(varType("A"), varType("B")));
 * subst = new Map([["A", Int]]);
 *
 * applySubstitution(state, subst, poly)
 * // => ∀A. (A → B)   // Binder shadows substitution
 * ```
 *
 * ---------------------------------------------------------------------------
 * Used by
 * ---------------------------------------------------------------------------
 * - {@link solveConstraints} — post‑solver type cleanup
 * - {@link inferAppType}, {@link checkType} — resolving instantiated types
 * - {@link instantiateTerm} — applying substitutions inside terms
 * - {@link typesEqual}, {@link unifyTypes} — normalization paths
 *
 * ---------------------------------------------------------------------------
 * @param state - Typechecker state (used for meta‑var global solutions)
 * @param subst - Local substitution map (flexible and rigid variable bindings)
 * @param type - The type to rewrite under the substitution
 * @param visited - Internal set used to prevent infinite substitution loops
 *
 * @returns A new type with substitutions applied everywhere they apply
 */
export function applySubstitution(
  state: TypeCheckerState,
  subst: Substitution,
  type: Type,
  visited = new Set<string>(),
): Type {
  if (isMetaVar(type)) {
    const sol = subst.get(type.evar) || state.meta.solutions.get(type.evar); // Add state param?
    return sol ? applySubstitution(state, subst, sol, visited) : type;
  }

  if ("var" in type) {
    // Cycle detection, return the variable unchanged
    if (visited.has(type.var)) return type;

    const replacement = subst.get(type.var);
    if (!replacement) return type;

    // Add to visited set and recursively substitute
    const newVisited = new Set(visited);
    newVisited.add(type.var);
    return applySubstitution(state, subst, replacement, newVisited);
  }

  if ("con" in type) return type;

  if ("arrow" in type)
    return arrowType(
      applySubstitution(state, subst, type.arrow.from),
      applySubstitution(state, subst, type.arrow.to),
    );

  if ("forall" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.forall.var);
    return forallType(
      type.forall.var,
      type.forall.kind,
      applySubstitution(state, newSubst, type.forall.body),
    );
  }

  if ("bounded_forall" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.bounded_forall.var);
    return boundedForallType(
      type.bounded_forall.var,
      type.bounded_forall.kind,
      type.bounded_forall.constraints.map((c) => ({
        trait: c.trait,
        type: applySubstitution(state, subst, c.type),
      })),
      applySubstitution(state, newSubst, type.bounded_forall.body),
    );
  }

  if ("lam" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.lam.var);
    return {
      lam: {
        var: type.lam.var,
        kind: type.lam.kind,
        body: applySubstitution(state, newSubst, type.lam.body),
      },
    };
  }

  if ("app" in type) {
    return appType(
      applySubstitution(state, subst, type.app.func),
      applySubstitution(state, subst, type.app.arg),
    );
  }

  if ("record" in type) {
    const record: [string, Type][] = [];
    for (const [label, fieldType] of type.record)
      record.push([label, applySubstitution(state, subst, fieldType)]);
    return { record };
  }

  if ("variant" in type) {
    const variant: [string, Type][] = [];
    for (const [label, caseType] of type.variant)
      variant.push([label, applySubstitution(state, subst, caseType)]);
    return { variant };
  }

  if ("mu" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.mu.var);
    return muType(
      type.mu.var,
      applySubstitution(state, newSubst, type.mu.body),
    );
  }

  if ("tuple" in type)
    return tupleType(type.tuple.map((t) => applySubstitution(state, subst, t)));

  return type;
}

/**
 * Checks whether a term has a **specific expected type**
 * (bidirectional “checking mode”).
 *
 * In other words:
 *
 *     Γ ⊢ term ⇐ expectedType
 *
 * This is the *analysis* half of the bidirectional typing system:
 * - **Infer mode** synthesizes a type (`inferType`)
 * - **Check mode** verifies a term *against* a known type (`checkType`)
 *
 * ---------------------------------------------------------------------------
 * Why `checkType` exists
 * ---------------------------------------------------------------------------
 * Many terms require **external type guidance** because their type cannot be
 * uniquely inferred in isolation:
 *
 * - Lambdas: `λx. x`
 *   (we need to know the parameter’s expected type)
 *
 * - Pattern match branches
 *   (each branch must be checked against a type merged from other branches)
 *
 * - Trait applications and polymorphic boundaries
 *   (where instantiation direction matters)
 *
 * Checking mode enables these cases by type‑checking with an **expected type**.
 *
 * ---------------------------------------------------------------------------
 * What the return value means
 * ---------------------------------------------------------------------------
 * The function returns:
 *
 *     ok({ type, subst })
 *
 * where:
 *
 * - **type**
 *   The fully resolved version of `expectedType` after applying substitutions.
 *
 * - **subst**
 *   A *local substitution* containing meta‑variable bindings discovered while
 *   checking.
 *
 * Why return a substitution?
 * ---------------------------------------
 * Because checking can cause meta‑variables to be solved.
 *
 * Example:
 * ```ts
 * expectedType = ?0 → Int
 * term = λx. x
 *
 * checkType(...) must bind ?0 := Int
 * ```
 *
 * Returning `{ subst }` allows the caller to merge new solutions into the
 * global meta‑environment and propagate them upward.
 *
 * Substitution is the “output” of unification, and checking may need to unify:
 * - lambda parameter types
 * - return types
 * - tuple/record field types
 * - pattern‑derived types
 * - polymorphic instantiation results
 *
 * ---------------------------------------------------------------------------
 * High‑level algorithm
 * ---------------------------------------------------------------------------
 *
 * 1. **Verify kind correctness** of `expectedType` (e.g. not applying a record).
 *
 * 2. **Term‑specific rules**:
 *    - Lambda (`λx:τ.body`): unify parameter types, check body
 *    - Type lambda (`ΛA::κ. body`): expected must be a `forall`
 *    - Trait lambda: expected must be a bounded ∀
 *    - Records, tuples, variants: check fields/branches element‑wise
 *    - Fold: ensure annotation is a μ‑type and body matches its unfolding
 *
 * 3. **Fallback to inference**:
 *    If no specialized rule applies:
 *    ```
 *    inferred = inferType(term)
 *    check that inferred <: expectedType
 *    ```
 *    using {@link subsumes}.
 *
 * 4. **Solve constraints** and apply meta‑variable substitutions.
 *
 * 5. **Return updated expectedType** (substituted + normalized) and the
 *    substitution collected along the way.
 *
 * ---------------------------------------------------------------------------
 * Important behaviors
 * ---------------------------------------------------------------------------
 * - Lambda checking uses **expectedType.arrow.from** to enforce argument type.
 * - Polymorphic expected types are handled by **alpha‑renaming** and recursion.
 * - Trait lambdas must match constraint lists and kinds exactly.
 * - The function **never generalizes**; it only instantiates.
 * - Returns **local** substitutions; the caller is responsible for merging them.
 *
 * ---------------------------------------------------------------------------
 * Common error cases
 * ---------------------------------------------------------------------------
 * - `type_mismatch` — body return type does not match expected return type
 * - `kind_mismatch` — expectedType has wrong kind
 * - `not_a_function` — checking `λx. ...` against non‑arrow type
 * - `invalid_variant_label`, `missing_field`, etc. for mismatched patterns
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * ✔️ Checking a lambda:
 * ```ts
 * const expected = arrowType(Int, Int);
 * checkType(state, lamTerm("x", Int, varTerm("x")), expected);
 * // => ok({ type: Int → Int, subst: Map() })
 * ```
 *
 * ✔️ Checking via inference fallback:
 * ```ts
 * const expected = Int;
 * checkType(state, conTerm("42", Int), expected);
 * // inferred Int <: Int → ok
 * ```
 *
 * ✔️ Checking with meta‑vars:
 * ```ts
 * const expected = arrowType(freshMetaVar(state.meta), Bool);
 * checkType(state, lamTerm("x", Bool, varTerm("x")), expected);
 * // => binds ?0 := Bool
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link inferType} — synthesis mode
 * - {@link inferTypeWithMode} — dispatcher between infer/check
 * - {@link subsumes} — subtyping check used as fallback
 * - {@link unifyTypes} — solves structural constraints during checking
 * - {@link solveConstraints} — finalizes meta‑var solutions
 *
 * @param state - Current typechecker state (context + meta‑env)
 * @param term - The term being type‑checked
 * @param expectedType - The type the term must have
 * @returns Either a `{ type, subst }` pair or a `TypingError`
 */
export function checkType(
  state: TypeCheckerState,
  term: Term,
  expectedType: Type,
): Result<TypingError, { type: Type; subst: Substitution }> {
  // Check kind of expected type
  const kindResult = checkKind(state, expectedType);
  if ("err" in kindResult) return kindResult;

  // Lambda: check against arrow type
  if ("lam" in term && "arrow" in expectedType) {
    // Unify the lambda's declared parameter type with the expected domain
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const domainUnify = unifyTypes(
      state,
      term.lam.type,
      expectedType.arrow.from,
      worklist,
      subst,
    );
    if ("err" in domainUnify) return domainUnify;

    const solveRes = solveConstraints(state, worklist, subst);
    if ("err" in solveRes) return solveRes;

    // Populate global meta variable solutions
    for (const [varName, soln] of solveRes.ok.entries()) {
      if (state.meta.solutions.has(varName)) {
        const globalSolve = solveMetaVar(state, varName, soln);
        if ("err" in globalSolve) return globalSolve;
      }
    }

    // Apply substitution to get the resolved domain type
    let effectiveFromType = applySubstitution(
      state,
      solveRes.ok,
      expectedType.arrow.from,
    );

    if (isBottom(state, expectedType.arrow.from))
      effectiveFromType = freshMetaVar(state.meta);

    const extendedContext: Context = [
      ...state.ctx,
      { term: { name: term.lam.arg, type: effectiveFromType } },
    ];

    const bodyCheckRes = checkType(
      { ctx: extendedContext, meta: state.meta },
      term.lam.body,
      applySubstitution(state, solveRes.ok, expectedType.arrow.to),
    );
    if ("err" in bodyCheckRes) return bodyCheckRes;

    const mergedSubst = mergeSubsts(solveRes.ok, bodyCheckRes.ok.subst);

    let finalType: Type = applySubstitution(state, mergedSubst, expectedType);
    if (isBottom(state, expectedType.arrow.from))
      finalType = arrowType(neverType, (finalType as ArrowType).arrow.to);

    return ok({ type: finalType, subst: mergedSubst });
  }

  // Type lambda: check against forall (unchanged)
  if ("tylam" in term && "forall" in expectedType) {
    // Verify kinds match
    if (!kindsEqual(term.tylam.kind, expectedType.forall.kind))
      return err({
        kind_mismatch: {
          expected: expectedType.forall.kind,
          actual: term.tylam.kind,
        },
      });

    const extendedContext: Context = [
      ...state.ctx,
      { type: { name: term.tylam.var, kind: term.tylam.kind } },
    ];

    // Alpha-rename expected type if necessary
    const renamedExpected = alphaRename(
      expectedType.forall.var,
      term.tylam.var,
      expectedType.forall.body,
    );

    const bodyResult = checkType(
      { ctx: extendedContext, meta: state.meta },
      term.tylam.body,
      renamedExpected,
    );
    if ("err" in bodyResult) return bodyResult;

    return ok({ type: expectedType, subst: new Map() });
  }

  // Trait lambda: check against bounded forall
  if ("trait_lam" in term && "bounded_forall" in expectedType) {
    // Verify kinds match
    if (!kindsEqual(term.trait_lam.kind, expectedType.bounded_forall.kind))
      return err({
        kind_mismatch: {
          expected: expectedType.bounded_forall.kind,
          actual: term.trait_lam.kind,
        },
      });

    // Check constraints match
    if (
      term.trait_lam.constraints.length !==
      expectedType.bounded_forall.constraints.length
    )
      return err({
        type_mismatch: { expected: expectedType, actual: expectedType },
      });

    for (let i = 0; i < term.trait_lam.constraints.length; i++) {
      const termConstraint = term.trait_lam.constraints[i]!;
      const expectedConstraint = expectedType.bounded_forall.constraints[i]!;

      if (termConstraint.trait !== expectedConstraint.trait)
        return err({
          type_mismatch: { expected: expectedType, actual: expectedType },
        });

      // Alpha-rename constraint types
      const renamedConstraintType = alphaRename(
        expectedType.bounded_forall.var,
        term.trait_lam.type_var,
        expectedConstraint.type,
      );

      if (!typesEqual(state, termConstraint.type, renamedConstraintType))
        return err({
          type_mismatch: {
            expected: renamedConstraintType,
            actual: termConstraint.type,
          },
        });
    }

    const extendedContext: Context = [
      ...state.ctx,
      {
        type: {
          name: term.trait_lam.type_var,
          kind: term.trait_lam.kind,
        },
      },
      {
        dict: {
          name: term.trait_lam.trait_var,
          trait: term.trait_lam.trait,
          type: { var: term.trait_lam.type_var },
        },
      },
    ];

    // Alpha-rename expected body
    const renamedExpected = alphaRename(
      expectedType.bounded_forall.var,
      term.trait_lam.type_var,
      expectedType.bounded_forall.body,
    );

    const bodyResult = checkType(
      { ctx: extendedContext, meta: state.meta },
      term.trait_lam.body,
      renamedExpected,
    );
    if ("err" in bodyResult) return bodyResult;

    return ok({ type: expectedType, subst: new Map() });
  }

  // Record: check field by field
  if ("record" in term && "record" in expectedType) {
    const termLabels = term.record.map(first).sort();
    const typeLabels = expectedType.record.map(first).sort();

    // Check labels match
    if (
      termLabels.length !== typeLabels.length ||
      !termLabels.every((l, i) => l === typeLabels[i])
    )
      return err({
        type_mismatch: {
          expected: expectedType,
          actual: { record: term.record.map(([l, _]) => [l, unitType]) },
        },
      });

    // Check each field
    for (const [label, fieldTerm] of term.record) {
      const expectedFieldType = expectedType.record.find(
        (f) => f[0] === label,
      )![1];

      const fieldResult = checkType(state, fieldTerm, expectedFieldType);
      if ("err" in fieldResult) return fieldResult;
    }

    return ok({ type: expectedType, subst: new Map() });
  }

  // Tuple: check element by element
  if ("tuple" in term && "tuple" in expectedType) {
    if (term.tuple.length !== expectedType.tuple.length)
      return err({
        type_mismatch: {
          expected: expectedType,
          actual: { tuple: term.tuple.map(() => unitType) },
        },
      });

    for (let i = 0; i < term.tuple.length; i++) {
      const elementResult = checkType(
        state,
        term.tuple[i]!,
        expectedType.tuple[i]!,
      );
      if ("err" in elementResult) return elementResult;
    }

    return ok({ type: expectedType, subst: new Map() });
  }

  // Injection: check value against variant case type
  if ("inject" in term) {
    const variantType = normalizeType(state, expectedType);

    if (!("variant" in variantType))
      return err({ not_a_variant: expectedType });

    const caseType = variantType.variant.find(
      (c) => c[0] === term.inject.label,
    );

    if (!caseType)
      return err({
        invalid_variant_label: {
          variant: variantType,
          label: term.inject.label,
        },
      });

    const valueResult = checkType(state, term.inject.value, caseType[1]);
    if ("err" in valueResult) return valueResult;

    return ok({ type: expectedType, subst: new Map() });
  }

  // Fold: check the inner term against the unfolded type
  if ("fold" in term) {
    // if no mu exists for the fold, return err
    if (!("mu" in expectedType)) {
      return err({
        type_mismatch: {
          expected: expectedType,
          actual: term.fold.type,
        },
      });
    }

    const unfoldedType = substituteType(
      expectedType.mu.var,
      expectedType,
      expectedType.mu.body,
      new Set([expectedType.mu.var]),
    );

    const termResult = checkType(state, term.fold.term, unfoldedType);
    if ("err" in termResult) return termResult;

    return ok({ type: expectedType, subst: new Map() });
  }

  // Subsumption: infer and check if compatible
  const inferredType = inferType(state, term);
  if ("err" in inferredType) return inferredType;

  let polyInferred = inferredType.ok;
  if ("forall" in polyInferred && !("forall" in expectedType)) {
    // Instantiate poly to match expected
    polyInferred = instantiateType(state, polyInferred);
    // Unify with expected (solves metas)
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(
      state,
      polyInferred,
      expectedType,
      worklist,
      subst,
    );
    if ("err" in unifyRes) {
      // Original subsumption as fallback
      const subsumesRes = subsumes(
        state,
        inferredType.ok,
        expectedType,
        [],
        new Map(),
      );
      if ("err" in subsumesRes) return subsumesRes;
    } else {
      const solveRes = solveConstraints(state, worklist, subst);
      if ("err" in solveRes) return solveRes;
      polyInferred = applySubstitution(state, solveRes.ok, polyInferred);
    }
  }

  // Proceed with subsumption
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const subsumesResult = subsumes(
    state,
    expectedType,
    polyInferred,
    worklist,
    subst,
  );
  if ("err" in subsumesResult) return subsumesResult;

  const solveResult = solveConstraints(state, worklist, subst);
  if ("err" in solveResult) return solveResult;

  const finalSubst = solveResult.ok;
  for (const [varName, soln] of finalSubst.entries()) {
    const globalSolve = solveMetaVar(state, varName, soln);
    if ("err" in globalSolve) return globalSolve;
  }

  const resolvedExpected = applySubstitution(state, finalSubst, expectedType);

  let finalInferred = polyInferred;
  if (!isAssignableTo(state, polyInferred, resolvedExpected)) {
    finalInferred = applySubstitution(state, finalSubst, polyInferred);
    return err({
      type_mismatch: { expected: resolvedExpected, actual: finalInferred },
    });
  }

  return ok({ type: resolvedExpected, subst: finalSubst });
}

/**
 * Synthesizes (infers) the **type** of a term.
 *
 * This is the “infer mode” of the bidirectional type system:
 *
 *     Γ ⊢ term ⇒ τ
 *
 * meaning:
 *
 *     “Given only the term, figure out what type it must have.”
 *
 * In many languages, this is the default typing behavior. In System F‑ω with
 * traits, inference must cooperate closely with checking and unification.
 *
 * ---------------------------------------------------------------------------
 * When inference is appropriate
 * ---------------------------------------------------------------------------
 * You can infer the type of:
 * - variables (`x`)
 * - constants and constructors (`42 : Int`)
 * - applications (`f x`)
 * - records and tuples
 * - type applications (`t[Int]`)
 * - type lambdas (`ΛA::*. e`)
 * - trait dictionaries (`dict Eq<Int> { ... }`)
 * - variant injections
 * - match expressions
 *
 * You **cannot** infer the type of some forms without an annotation:
 * - lambdas (`λx. e`) — need parameter types
 * - polymorphic lambdas (`ΛA. e`) — okay only because type lambdas contain kind annotations
 *
 * When inference is not enough, the typechecker uses **checking mode**
 * (`checkType`), which takes an expected type.
 *
 * ---------------------------------------------------------------------------
 * How inference works (high‑level)
 * ---------------------------------------------------------------------------
 * `inferType` dispatches on the shape of the term:
 *
 * 1. **VarTerm**
 *    Look up the variable’s type in the context.
 *
 * 2. **ConTerm**
 *    Return its annotated type.
 *
 * 3. **LamTerm**
 *    Infer using the lambda typing rule:
 *    parameter types must already be provided (`λx:τ. body`)
 *
 * 4. **AppTerm** (`f x`)
 *    - infer the function type
 *    - infer the argument type
 *    - unify to extract the result type
 *
 * 5. **TyLamTerm** / **TyAppTerm**
 *    Handle System F polymorphism: `ΛA` and `t[A]`.
 *
 * 6. **TraitLamTerm** / **TraitAppTerm**
 *    Handle bounded polymorphism and dictionary resolution.
 *
 * 7. **DictTerm**
 *    Validate the dictionary against the trait definition.
 *
 * 8. **RecordTerm**, **TupleTerm**, **InjectTerm**, **MatchTerm**, **FoldTerm**, **UnfoldTerm**
 *    Structural inference rules.
 *
 * The function may call:
 * - {@link unifyTypes} when inference introduces constraints
 * - {@link solveConstraints} during application inference
 * - {@link normalizeType} to simplify results
 *
 * ---------------------------------------------------------------------------
 * Result behavior
 * ---------------------------------------------------------------------------
 * Returns a `Result<TypingError, Type>` where:
 * - `ok(type)` is the fully normalized inferred type
 * - `err(error)` is a detailed typing error if inference fails
 *
 * Unlike `checkType`, inference does **not** return a substitution pair — the
 * top‑level type is the final inferred type after all required solving
 * operations inside the inference rules.
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Lambda with annotation**
 * ```ts
 * inferType(state, lamTerm("x", Int, varTerm("x")));
 * // => ok(Int → Int)
 * ```
 *
 * **Simple application**
 * ```ts
 * inferType(state, appTerm(varTerm("id"), conTerm("42", Int)));
 * // => ok(Int)
 * ```
 *
 * **Polymorphic type lambda**
 * ```ts
 * inferType(state, tylamTerm("A", starKind,
 *   lamTerm("x", varType("A"), varTerm("x"))
 * ));
 * // => ok(∀A::*. A → A)
 * ```
 *
 * **Trait dictionary method**
 * ```ts
 * inferType(state, traitMethodTerm(varTerm("eqDict"), "eq"));
 * // => ok(Int → Int → Bool)
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link checkType} — checking mode (expects a type)
 * - {@link inferTypeWithMode} — unified bidirectional dispatcher
 * - {@link unifyTypes}, {@link solveConstraints} — constraint machinery
 * - {@link normalizeType} — ensures inferred types are in canonical form
 *
 * @param state - The typechecker state (environment + meta variables)
 * @param term - The term whose type we want to infer
 * @returns The inferred and normalized type of the term, or a {@link TypingError}
 */
export function inferType(
  state: TypeCheckerState,
  term: Term,
): Result<TypingError, Type> {
  if ("var" in term) return inferVarType(state, term);
  if ("con" in term) return ok(term.con.type);
  if ("lam" in term) return inferLamType(state, term);
  if ("app" in term) return inferAppType(state, term);
  if ("let" in term) return inferLetType(state, term);
  if ("tylam" in term) return inferTylamType(state, term);
  if ("tyapp" in term) return inferTyappType(state, term);
  if ("dict" in term) return inferDictType(state, term);
  if ("trait_lam" in term) return inferTraitLamType(state, term);
  if ("trait_app" in term) return inferTraitAppType(state, term);
  if ("trait_method" in term) return inferTraitMethodType(state, term);
  if ("record" in term) return inferRecordType(state, term);
  if ("project" in term) return inferProjectType(state, term);
  if ("inject" in term) return inferInjectType(state, term);
  if ("match" in term) return inferMatchType(state, term);
  if ("fold" in term) return inferFoldType(state, term);
  if ("unfold" in term) return inferUnfoldType(state, term);
  if ("tuple" in term) return inferTupleType(state, term);
  if ("tuple_project" in term) return inferTupleProjectType(state, term);

  throw new Error(`Unknown term: ${Object.keys(term)[0]}`);
}

function inferTupleProjectType(
  state: TypeCheckerState,
  term: TupleProjectTerm,
) {
  const tupleType = inferType(state, term.tuple_project.tuple);
  if ("err" in tupleType) return tupleType;

  // Normalize to expand type aliases
  const normalizedType = normalizeType(state, tupleType.ok);

  if (!("tuple" in normalizedType)) return err({ not_a_tuple: normalizedType });

  const index = term.tuple_project.index;
  if (index < 0 || index >= normalizedType.tuple.length) {
    return err({
      tuple_index_out_of_bounds: {
        tuple: normalizedType,
        index,
      },
    });
  }

  return ok(normalizedType.tuple[index]!);
}

function inferTupleType(state: TypeCheckerState, term: TupleTerm) {
  const elementTypes: Type[] = [];

  for (const element of term.tuple) {
    const elementType = inferType(state, element);
    if ("err" in elementType) return elementType;

    elementTypes.push(elementType.ok);
  }

  return ok(tupleType(elementTypes));
}

function inferUnfoldType(
  state: TypeCheckerState,
  term: UnfoldTerm,
): Result<TypingError, Type> {
  const termTypeRes = inferType(state, term.unfold);
  if ("err" in termTypeRes) return termTypeRes;

  const norm = normalizeType(state, termTypeRes.ok);

  if (!("mu" in norm)) {
    return err({ not_a_function: termTypeRes.ok });
  }

  // FIX: Do not pass avoidInfinite set
  const unfoldedSubstituted = substituteType(norm.mu.var, norm, norm.mu.body);

  const unfoldedType = normalizeType(state, unfoldedSubstituted);
  return ok(unfoldedType);
}

/**
 * Infers type of fold term: `fold[τ](e)`.
 *
 * **Typing rule**:
 * - `Γ ⊢ τ` (well-kinded annotation).
 * - `norm(τ) = μX.body` (must normalize to recursive type).
 * - `Γ ⊢ e : body[μX.body/X]` (inner term must match unfolded body).
 * - Result: `τ`.
 */
function inferFoldType(
  state: TypeCheckerState,
  term: FoldTerm,
): Result<TypingError, Type> {
  // 1. Ensure the annotation is well-kinded
  const kindRes = checkKind(state, term.fold.type);
  if ("err" in kindRes) return kindRes;

  // 2. Normalize the annotation to see the structural μ-type
  const norm = normalizeType(state, term.fold.type);

  if (!("mu" in norm)) {
    return err({
      type_mismatch: {
        expected: norm,
        actual: term.fold.type,
      },
    });
  }

  // 3. Compute the unfolded body: body[μX.body / X]
  //    CRITICAL: Do not pass 'avoidInfinite' set here; we WANT to substitute X.
  const unfoldedSubstituted = substituteType(norm.mu.var, norm, norm.mu.body);
  const unfoldedType = normalizeType(state, unfoldedSubstituted);

  // 4. Infer type of the inner term
  const innerRes = inferType(state, term.fold.term);
  if ("err" in innerRes) return innerRes;

  // Normalize inner type to ensure structural comparison works
  const normInner = normalizeType(state, innerRes.ok);

  // 5. Check: Inner type must be assignable to Unfolded Body
  if (!isAssignableTo(state, normInner, unfoldedType)) {
    return err({
      type_mismatch: {
        expected: unfoldedType,
        actual: normInner,
      },
    });
  }

  // 6. Return the nominal annotation
  return ok(term.fold.type);
}

function inferMatchType(state: TypeCheckerState, term: MatchTerm) {
  const scrutineeType = inferType(state, term.match.scrutinee);
  if ("err" in scrutineeType) return scrutineeType;
  let normalizedScrutinee = normalizeType(state, scrutineeType.ok);
  if ("mu" in normalizedScrutinee) {
    normalizedScrutinee = substituteType(
      normalizedScrutinee.mu.var,
      normalizedScrutinee,
      normalizedScrutinee.mu.body,
    );
  }

  const patterns = term.match.cases.map((c) => c[0]);
  const exhaustCheck = checkExhaustive(state, patterns, normalizedScrutinee);
  if ("err" in exhaustCheck) return exhaustCheck;

  let commonType: Type | null = null;

  for (const [pat, bod] of term.match.cases) {
    // Apply global meta variable solutions before checking each pattern
    const globalSubst = state.meta.solutions;
    const currentScrutineeType = normalizeType(
      state,
      applySubstitution(state, globalSubst, normalizedScrutinee),
    );

    const patternResult = checkPattern(state, pat, currentScrutineeType); // ← Use currentScrutineeType
    if ("err" in patternResult) return patternResult;

    const extendedCtx: Context = [...state.ctx, ...patternResult.ok];
    const extendedState = { ctx: extendedCtx, meta: state.meta };
    const bodyType = inferType(extendedState, bod);
    if ("err" in bodyType) return bodyType;

    let instBodyType = instantiateType(state, bodyType.ok);
    instBodyType = normalizeType(state, instBodyType);

    if (commonType === null) {
      commonType = instBodyType;
    } else {
      const worklist: Worklist = [];
      const subst = new Map<string, Type>();

      let subsumesRes = subsumes(
        extendedState,
        instBodyType,
        commonType,
        worklist,
        subst,
      );

      if ("err" in subsumesRes) {
        subst.clear();
        worklist.length = 0;
        subsumesRes = subsumes(
          extendedState,
          commonType,
          instBodyType,
          worklist,
          subst,
        );
      }

      if ("err" in subsumesRes) {
        const unifyRes = unifyTypes(
          state,
          commonType,
          instBodyType,
          worklist,
          subst,
        );
        if ("err" in unifyRes) return unifyRes;
      }

      const solveRes = solveConstraints(state, worklist, subst);
      if ("err" in solveRes) return solveRes;

      commonType = applySubstitution(state, solveRes.ok, commonType!);
    }
  }

  return ok(normalizeType(state, commonType!));
}

function inferInjectType(
  state: TypeCheckerState,
  term: InjectTerm,
): Result<TypingError, Type> {
  const variantType = term.inject.variant_type; // Don't normalize yet!

  // Case 1: Nominal enum (app with con head, e.g., Option<t>, Either<l, r>)
  if ("app" in variantType || "con" in variantType) {
    const head = "con" in variantType ? variantType : getSpineHead(variantType);
    if ("con" in head) {
      const conName = head.con;
      const spineArgs = "con" in variantType ? [] : getSpineArgs(variantType);
      // Lookup enum definition in context
      const enumBinding = state.ctx.find(
        (b) => "enum" in b && b.enum.name === conName,
      );
      if (enumBinding && "enum" in enumBinding) {
        const def = enumBinding.enum;

        // Check arity: Spine args must match param count
        if (spineArgs.length !== def.params.length)
          return err({
            kind_mismatch: { expected: def.kind, actual: starKind },
          });

        const label = term.inject.label;
        const variantEntry = def.variants.find(([l]) => l === label);
        if (!variantEntry)
          return err({
            invalid_variant_label: { variant: variantType, label },
          });

        // Instantiate the field scheme with spine args
        let expectedFieldType: Type = variantEntry[1];
        for (let i = 0; i < def.params.length; i++) {
          const paramName = def.params[i]!;
          const concreteArg = spineArgs[i]!;
          expectedFieldType = substituteType(
            paramName,
            concreteArg,
            expectedFieldType,
          );
        }
        expectedFieldType = normalizeType(state, expectedFieldType);

        // Check the injected value against the field type
        const valueCheck = checkInjectValue(
          state,
          term.inject.value,
          expectedFieldType,
        );

        return "err" in valueCheck ? valueCheck : ok(variantType);
      }
    }
  }

  // Case 2: Structural variant - NOW normalize to expand
  const normalizedVariant = normalizeType(state, variantType);
  if ("variant" in normalizedVariant) {
    const caseEntry = normalizedVariant.variant.find(
      ([l]) => l === term.inject.label,
    );
    if (!caseEntry)
      return err({
        invalid_variant_label: {
          variant: normalizedVariant,
          label: term.inject.label,
        },
      });

    const expectedFieldType = caseEntry[1];
    const valueCheck = checkInjectValue(
      state,
      term.inject.value,
      expectedFieldType,
    );

    return "err" in valueCheck ? valueCheck : ok(variantType); // Return original
  }

  // Neither nominal nor structural: Fail
  return err({ not_a_variant: variantType });
}

// Check injected value against field type (handles unit, single, tuple/multi-field)
function checkInjectValue(
  state: TypeCheckerState,
  value: Term,
  expectedFieldType: Type,
): Result<TypingError, { valueType: Type }> {
  if (isBottom(state, expectedFieldType)) {
    // Bottom field: Always OK (unreachable variant)
    return ok({ valueType: neverType });
  }

  // Case: Zero fields (unit variant, e.g., None)
  if ("tuple" in expectedFieldType && expectedFieldType.tuple.length === 0) {
    // Value should be unit {} or wildcard-ish
    if (!("tuple" in value) || value.tuple.length !== 0) {
      const inferred = inferType(state, value);
      return err({
        type_mismatch: {
          expected: expectedFieldType,
          actual: "ok" in inferred ? inferred.ok : unitType,
        },
      });
    }
    return ok({ valueType: unitType });
  }

  // Case: Single field (most common, e.g., Some(val) where field = {var: "t"})
  if (!("tuple" in expectedFieldType)) {
    // Treat single as non-tuple
    const valueType = inferType(state, value);
    if ("err" in valueType) return valueType;

    const checkRes = checkType(state, value, expectedFieldType);
    if ("err" in checkRes) return checkRes;

    return ok({ valueType: checkRes.ok.type });
  }

  // Case: Multi-field (tuple field, e.g., {fields: [ {ty: "t1"}, {ty: "t2"} ] } → {tuple: [{var: "t1"}, {var: "t2"}]}
  if (!("tuple" in value)) {
    // Value is not tuple, but expected is: Mismatch
    return err({
      type_mismatch: { expected: expectedFieldType, actual: { tuple: [] } },
    });
  }

  if (value.tuple.length !== expectedFieldType.tuple.length) {
    return err({
      type_mismatch: {
        expected: expectedFieldType,
        actual: { tuple: value.tuple.map(() => freshMetaVar(state.meta)) },
      },
    });
  }

  const valueType: Type = { tuple: [] };
  for (let i = 0; i < value.tuple.length; i++) {
    const valueElem = value.tuple[i]!;
    const expectedElemType = expectedFieldType.tuple[i]!;

    const elemType = inferType(state, valueElem);
    if ("err" in elemType) return elemType;

    const checkRes = checkType(state, valueElem, expectedElemType);
    if ("err" in checkRes) return checkRes;

    valueType.tuple.push(checkRes.ok.type); // Collect for overall tuple type
  }

  return ok({ valueType });
}

/**
 * Extracts the **head constructor** of a left‑associated type application.
 *
 * Many type constructors are applied in *spine form*:
 *
 *   Either<Int, Bool>
 *   ≡ appType(appType(Either, Int), Bool)
 *
 * The **spine head** is the leftmost element:
 *
 *   getSpineHead(Either<Int, Bool>)  →  Either
 *
 * This helper walks through nested `AppType` nodes until it reaches the base
 * constructor or variable.
 *
 * Why it's useful:
 * - Identifying the root constructor of nominal types (`Either`, `List`)
 * - Enum/ADT lookup during pattern checking and injection
 * - Unification of nominal applications
 * - Pretty‑printing types (`showType`)
 *
 * @param ty - A possibly nested type application
 * @returns The head type (e.g., a `con` or `var` node)
 *
 * @example
 * ```ts
 * const t = appType(appType(conType("Either"), Int), Bool);
 * getSpineHead(t);   // => conType("Either")
 * ```
 *
 * @example Non-application:
 * ```ts
 * getSpineHead(conType("Int"));  // => Int
 * ```
 */
export function getSpineHead(ty: Type): Type {
  let current = ty;
  while ("app" in current) {
    current = current.app.func;
  }
  return current;
}

function inferProjectType(state: TypeCheckerState, term: ProjectTerm) {
  const recordType = inferType(state, term.project.record);
  if ("err" in recordType) return recordType;

  // Normalize to expand type aliases
  const normalizedType = normalizeType(state, recordType.ok);

  if (!("record" in normalizedType))
    return err({ not_a_record: normalizedType });

  const fieldType = normalizedType.record.find(
    (t) => t[0] === term.project.label,
  );
  if (!fieldType) {
    return err({
      missing_field: {
        record: normalizedType,
        label: term.project.label,
      },
    });
  }

  return ok(fieldType[1]);
}

function inferRecordType(state: TypeCheckerState, term: RecordTerm) {
  const record: [string, Type][] = [];

  for (const [label, fieldTerm] of term.record) {
    const fieldType = inferType(state, fieldTerm);
    if ("err" in fieldType) return fieldType;

    record.push([label, fieldType.ok]);
  }

  return ok({ record });
}

function inferTraitMethodType(state: TypeCheckerState, term: TraitMethodTerm) {
  const dictType = inferType(state, term.trait_method.dict);
  if ("err" in dictType) return dictType;

  // Check if the dictionary is a variable bound in context
  const dictTerm = term.trait_method.dict;

  if ("var" in dictTerm) {
    // dictTerm is a VarTerm
    const dictBinding = state.ctx.find(
      (b) => "dict" in b && b.dict.name === dictTerm.var,
    );

    if (dictBinding && "dict" in dictBinding) {
      // Look up the trait definition
      const traitDef = state.ctx.find(
        (b) => "trait_def" in b && b.trait_def.name === dictBinding.dict.trait,
      );

      if (!traitDef || !("trait_def" in traitDef))
        return err({ unbound: dictBinding.dict.trait });

      // Find the method in the trait def
      const method = traitDef.trait_def.methods.find(
        (m) => m[0] === term.trait_method.method,
      );

      if (!method)
        return err({
          missing_method: {
            trait: dictBinding.dict.trait,
            method: term.trait_method.method,
          },
        });

      // Substitute the type parameter with the concrete type
      const methodType = substituteType(
        traitDef.trait_def.type_param,
        dictBinding.dict.type,
        method[1],
      );

      return ok(methodType);
    }
  }

  // If it's a concrete dictionary term
  if ("dict" in dictTerm) {
    // dictTerm is a DictTerm
    const dict = dictTerm.dict;

    // Look up the trait definition
    const traitDef = state.ctx.find(
      (b) => "trait_def" in b && b.trait_def.name === dict.trait,
    );

    if (!traitDef || !("trait_def" in traitDef))
      return err({ unbound: dict.trait });

    // Find the method
    const methodImpl = dict.methods.find(
      (m) => m[0] === term.trait_method.method,
    );

    if (!methodImpl)
      return err({
        missing_method: {
          trait: dict.trait,
          method: term.trait_method.method,
        },
      });

    // Return the type of the method implementation
    return inferType(state, methodImpl[1]);
  }
  return err({
    type_mismatch: {
      expected: { con: "Dictionary" },
      actual: dictType.ok,
    },
  });
}

function inferTraitAppType(state: TypeCheckerState, term: TraitAppTerm) {
  const termType = inferType(state, term.trait_app.term);
  if ("err" in termType) return termType;

  if (!("bounded_forall" in termType.ok))
    return err({
      type_mismatch: {
        expected: termType.ok,
        actual: term.trait_app.type,
      },
    });

  // Check that the type argument has the expected kind
  const argKind = checkKind(state, term.trait_app.type);
  if ("err" in argKind) return argKind;
  const boundedForall = termType.ok.bounded_forall;
  if (!kindsEqual(boundedForall.kind, argKind.ok))
    return err({
      kind_mismatch: {
        expected: termType.ok.bounded_forall.kind,
        actual: argKind.ok,
      },
    });

  // Substitute type variable in constraints
  const instantiatedConstraints = termType.ok.bounded_forall.constraints.map(
    (c) => ({
      trait: c.trait,
      type: substituteType(boundedForall.var, term.trait_app.type, c.type),
    }),
  );

  // Check dict count BEFORE checking trait constraints
  if (term.trait_app.dicts.length !== instantiatedConstraints.length) {
    return err({
      wrong_number_of_dicts: {
        expected: instantiatedConstraints.length,
        actual: term.trait_app.dicts.length,
      },
    });
  }

  // Check that all trait constraints are satisfied
  const dictsResult = checkTraitConstraints(state, instantiatedConstraints);
  if ("err" in dictsResult) return dictsResult;

  // Type check each provided dictionary
  for (let i = 0; i < term.trait_app.dicts.length; i++) {
    const providedDict = term.trait_app.dicts[i]!;
    const dictType = inferType(state, providedDict);
    if ("err" in dictType) return dictType;

    // Verify it's actually a dictionary for the right trait/type
    if ("dict" in providedDict) {
      const constraint = instantiatedConstraints[i]!;
      if (
        providedDict.dict.trait !== constraint.trait ||
        !typesEqual(state, providedDict.dict.type, constraint.type)
      )
        return err({
          type_mismatch: {
            expected: { con: `Dict<${constraint.trait}>` },
            actual: dictType.ok,
          },
        });
    }
  }

  // Substitute the type argument in the body
  const resultType = substituteType(
    termType.ok.bounded_forall.var,
    term.trait_app.type,
    termType.ok.bounded_forall.body,
  );

  return ok(resultType);
}

function inferTraitLamType(state: TypeCheckerState, term: TraitLamTerm) {
  // Add type variable to context
  const extendedContext: Context = [
    ...state.ctx,
    {
      type: {
        name: term.trait_lam.type_var,
        kind: term.trait_lam.kind,
      },
    },
    // Add dictionary variable for the trait constraint
    {
      dict: {
        name: term.trait_lam.trait_var,
        trait: term.trait_lam.trait,
        type: { var: term.trait_lam.type_var },
      },
    },
  ];

  // Verify trait exists
  const traitDef = state.ctx.find(
    (b) => "trait_def" in b && b.trait_def.name === term.trait_lam.trait,
  );

  if (!traitDef || !("trait_def" in traitDef))
    return err({ unbound: term.trait_lam.trait });

  const bodyType = inferType(
    { ctx: extendedContext, meta: state.meta },
    term.trait_lam.body,
  );
  if ("err" in bodyType) return bodyType;

  return ok(
    boundedForallType(
      term.trait_lam.type_var,
      term.trait_lam.kind,
      term.trait_lam.constraints,
      bodyType.ok,
    ),
  );
}

function inferDictType(state: TypeCheckerState, term: DictTerm) {
  const traitDef = state.ctx.find(
    (b) => "trait_def" in b && b.trait_def.name === term.dict.trait,
  );

  if (!traitDef || !("trait_def" in traitDef))
    return err({ unbound: term.dict.trait });

  const dictType = term.dict.type;
  const typeKindResult = checkKind(state, dictType); // Full kind for basic well-formedness
  if ("err" in typeKindResult) return typeKindResult;

  // Compute STRIPPED partial kind (e.g., Option<t> → Option : * → *)
  const strippedResult = computeStrippedKind(state, dictType, []);
  if ("err" in strippedResult) return strippedResult;
  const { kind: partialKind, stripped: strippedArity } = strippedResult.ok;

  const expectedKind = traitDef.trait_def.kind;
  if (!kindsEqual(expectedKind, partialKind))
    return err({
      kind_mismatch: {
        expected: expectedKind,
        actual: partialKind, // Now * → *, not *
      },
    });

  // Arity validation only for concrete types (kind *); skip for HKT constructors (arrow kind)
  const fullKindStar = isStarKind(typeKindResult.ok);
  const expectedArity = kindArity(expectedKind); // e.g., 1 for * → *
  if (fullKindStar && strippedArity !== expectedArity) {
    // Only enforce for concrete (ensure we stripped the exact param count)
    // For HKT (e.g., impl for Option :: * → *), stripped=0 is fine if kinds match
    return err({
      kind_mismatch: {
        expected: expectedKind,
        actual: partialKind,
      },
    });
  }

  // This is the base type family (stripped of open args like t)
  const partialDictType = stripAppsByArity(state, dictType, strippedArity);

  const requiredMethods = new Set(traitDef.trait_def.methods.map((m) => m[0]));
  const providedMethods = new Set(term.dict.methods.map((m) => m[0]));

  // 1. Check all REQUIRED methods are provided
  for (const [requiredName] of traitDef.trait_def.methods) {
    if (!providedMethods.has(requiredName)) {
      return err({
        missing_method: { trait: term.dict.trait, method: requiredName },
      });
    }
  }

  // Bind 'self' to dictType in a local method context for each impl inference
  const methodCtx: Context = [
    ...state.ctx,
    { term: { name: "self", type: dictType } },
  ];

  // 2. Typecheck each PROVIDED method (skip extras)
  for (const [methodName, methodImpl] of term.dict.methods) {
    if (!requiredMethods.has(methodName)) continue; // Extra OK!

    const expectedMethod = traitDef.trait_def.methods.find(
      (m) => m[0] === methodName,
    );
    if (!expectedMethod)
      return err({
        missing_method: { trait: term.dict.trait, method: methodName },
      });

    // Instantiate expected method type with PARTIAL dict type (shared)
    let expectedMethodType = expectedMethod[1];
    expectedMethodType = substituteType(
      traitDef.trait_def.type_param, // "Self" or "F"
      partialDictType, // e.g., Option (lam)
      expectedMethodType,
    );

    const implType = inferType(
      { ctx: methodCtx, meta: state.meta },
      methodImpl,
    );
    if ("err" in implType) return implType;

    // Subsumption: allow impl to provide the expected type (handles instantiation)
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(
      state,
      normalizeType(state, expectedMethodType), // Normalize both sides
      normalizeType(state, implType.ok),
      worklist,
      subst,
    );

    // Always solve the worklist after subsumes
    if ("err" in unifyRes) {
      // Solve any constraints from unification, then error if failed
      const solveRes = solveConstraints(state, worklist, subst);
      if ("err" in solveRes)
        return err({
          type_mismatch: {
            expected: expectedMethodType,
            actual: implType.ok,
          },
        });

      return unifyRes; // Still error, but with solved types for better diagnostics
    }

    // If unification succeeded, solve remaining constraints (e.g., from body unification)
    const solveRes = solveConstraints(state, worklist, subst);
    // Propagate if constraints fail (rare here)
    if ("err" in solveRes) return solveRes;

    // Apply subst to verify (optional, for safety)
    const resolvedImpl = applySubstitution(state, solveRes.ok, implType.ok);
    if (
      !typesEqual(
        state,
        normalizeType(state, resolvedImpl),
        normalizeType(state, expectedMethodType),
      )
    ) {
      return err({
        type_mismatch: {
          expected: expectedMethodType,
          actual: resolvedImpl,
        },
      });
    }
  }
  const abstractedType = `Dict<${term.dict.trait}, ${showType(partialDictType)}>`;
  return ok(conType(abstractedType));
}

function inferTyappType(state: TypeCheckerState, term: TyAppTerm) {
  const termType = inferType(state, term.tyapp.term);
  if ("err" in termType) return termType;

  if (!("forall" in termType.ok))
    return err({
      type_mismatch: {
        expected: termType.ok,
        actual: term.tyapp.type,
      },
    });

  const argKind = checkKind(state, term.tyapp.type);
  if ("err" in argKind) return argKind;

  if (!kindsEqual(termType.ok.forall.kind, argKind.ok))
    return err({
      kind_mismatch: {
        expected: termType.ok.forall.kind,
        actual: argKind.ok,
      },
    });

  const substituted = substituteType(
    termType.ok.forall.var,
    term.tyapp.type,
    termType.ok.forall.body,
  );

  return ok(substituted);
}

function inferTylamType(state: TypeCheckerState, term: TyLamTerm) {
  const extendedContext: Context = [
    { type: { name: term.tylam.var, kind: term.tylam.kind } },
    ...state.ctx,
  ];

  const bodyType = inferType(
    { ctx: extendedContext, meta: state.meta },
    term.tylam.body,
  );
  if ("err" in bodyType) return bodyType;

  return ok(forallType(term.tylam.var, term.tylam.kind, bodyType.ok));
}

function inferLetType(state: TypeCheckerState, term: LetTerm) {
  const valueType = inferType(state, term.let.value);
  if ("err" in valueType) return valueType;

  const extendedContext: Context = [
    { term: { name: term.let.name, type: valueType.ok } },
    ...state.ctx,
  ];

  return inferType({ ctx: extendedContext, meta: state.meta }, term.let.body);
}

function inferAppType(state: TypeCheckerState, term: AppTerm) {
  const calleeInferred = inferType(state, term.app.callee);
  if ("err" in calleeInferred) return calleeInferred;

  const argInferred = inferType(state, term.app.arg);
  if ("err" in argInferred) return argInferred;

  let instantiatedCallee = calleeInferred.ok;

  if (
    !instantiatedCallee ||
    !(
      "arrow" in instantiatedCallee ||
      "forall" in instantiatedCallee ||
      "bounded_forall" in instantiatedCallee
    )
  ) {
    let reportedType: Type = { never: null };

    // Case 1: Proper ConTerm (term-level constant)
    const callee = term.app.callee;

    if ("con" in callee) {
      const conField = callee.con;
      if (conField && typeof conField === "object" && "type" in conField) {
        // e.g. con_term("42", Int)
        reportedType = conField.type;
      } else if (typeof conField === "string") {
        // e.g. con_type("Int") used incorrectly as term
        reportedType = { con: conField };
      }
    }

    // Case 2: Inferred type exists
    if ("con" in instantiatedCallee || "var" in instantiatedCallee)
      reportedType = instantiatedCallee;

    return err({ not_a_function: reportedType });
  }

  // Instantiate regular foralls first
  while ("forall" in instantiatedCallee) {
    const fv = freshMetaVar(state.meta);
    instantiatedCallee = substituteType(
      instantiatedCallee.forall.var,
      fv,
      instantiatedCallee.forall.body,
    );
  }

  // Handle bounded_forall by inferring Self from argument
  while ("bounded_forall" in instantiatedCallee) {
    let body = instantiatedCallee.bounded_forall.body;
    while ("forall" in body) {
      const fv = freshMetaVar(state.meta);
      body = substituteType(body.forall.var, fv, body.forall.body);
    }

    if (!("arrow" in body)) return err({ not_a_function: instantiatedCallee });

    const expectedParamType = body.arrow.from;

    // Try to infer Self from the argument
    const selfType = inferSelfFromArgument(
      state,
      argInferred.ok,
      expectedParamType,
      instantiatedCallee.bounded_forall.var,
      instantiatedCallee.bounded_forall.kind,
    );

    // If we can't infer Self yet, return a partially applied type
    // with the bounded_forall still in place
    if ("err" in selfType) {
      // Apply the argument but keep the bounded_forall wrapper
      const resultType = substituteType(
        "self", // or whatever the param name is
        argInferred.ok,
        body.arrow.to,
      );

      // Wrap result in bounded_forall again
      return ok(
        boundedForallType(
          instantiatedCallee.bounded_forall.var,
          instantiatedCallee.bounded_forall.kind,
          instantiatedCallee.bounded_forall.constraints,
          resultType,
        ),
      );
    }

    // We successfully inferred Self - continue with constraint checking
    const inferredSelf = selfType.ok;

    // Instantiate constraints with inferred Self
    const constraints = instantiatedCallee.bounded_forall.constraints.map(
      (c) => ({
        trait: c.trait,
        type: substituteType(
          (instantiatedCallee as BoundedForallType).bounded_forall.var,
          inferredSelf,
          c.type,
        ),
      }),
    );

    // Check trait constraints
    const dictsResult = checkTraitConstraints(state, constraints);
    if ("err" in dictsResult) return dictsResult;

    // Apply to get instantiated body (with Self substituted)
    instantiatedCallee = substituteType(
      instantiatedCallee.bounded_forall.var,
      inferredSelf,
      instantiatedCallee.bounded_forall.body,
    );

    // Instantiate any remaining foralls
    while ("forall" in instantiatedCallee) {
      instantiatedCallee = substituteType(
        instantiatedCallee.forall.var,
        freshMetaVar(state.meta),
        instantiatedCallee.forall.body,
      );
    }
  }

  // Rest continues as before...
  if (!("arrow" in instantiatedCallee))
    return err({ not_a_function: instantiatedCallee });

  const paramType = instantiatedCallee.arrow.from;
  const resultTypeBase = instantiatedCallee.arrow.to;

  // Bidirectional check
  const argCheckRes = checkType(state, term.app.arg, paramType);
  if ("err" in argCheckRes) {
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(
      state,
      argInferred.ok,
      paramType,
      worklist,
      subst,
    );
    if ("err" in unifyRes) return argCheckRes;

    const solveRes = solveConstraints(state, worklist, subst);
    if ("err" in solveRes) return solveRes;

    const resolvedResultType = applySubstitution(
      state,
      solveRes.ok,
      resultTypeBase,
    );
    return ok(resolvedResultType);
  }

  const { subst: localSubst } = argCheckRes.ok;
  const mergedSubst = mergeSubsts(localSubst, state.meta.solutions);
  let resultType = applySubstitution(state, mergedSubst, resultTypeBase);
  resultType = normalizeType(state, resultType);

  return ok(resultType);
}

function inferSelfFromArgument(
  state: TypeCheckerState,
  argType: Type,
  expectedType: Type,
  selfVar: string,
  selfKind: Kind,
): Result<TypingError, Type> {
  const normArg = normalizeType(state, argType);
  const normExpected = normalizeType(state, expectedType);

  // If expected is (Self t), extract constructor from arg
  if ("app" in normExpected && "var" in normExpected.app.func) {
    if (normExpected.app.func.var === selfVar) {
      // For variants like <Left: I32 | Right: ?14>,
      // reconstruct as Either<I32> by finding the enum def
      if ("variant" in normArg) {
        // Try to find which enum this variant belongs to
        const etype = findEnumForVariant(state, normArg);
        return etype
          ? ok(etype)
          : // Fallback: create a lambda that captures the variant structure
            ok(createVariantLambda(normArg, selfKind));
      }

      if ("app" in normArg) return ok(normArg.app.func);
    }
  }

  return err({ unbound: "Self" });
}

function findEnumForVariant(
  state: TypeCheckerState,
  variantType: Type,
): Type | null {
  if (!("variant" in variantType)) return null;

  // Get the variant labels
  const labels = new Set(variantType.variant.map(([label]) => label));

  // Search context for an enum type that has exactly these variants
  for (const binding of state.ctx) {
    if ("type" in binding) {
      const typeEntry = state.ctx.find(
        (b) => "term" in b && b.term.name === Array.from(labels)[0], // Check if any label matches a constructor
      );

      if (typeEntry && "term" in typeEntry) {
        const termType = typeEntry.term.type;
        // Extract the enum constructor from the term type
        // e.g., ∀t::*.∀u::*.(t → <Left: t | Right: u>) => Either
        if ("forall" in termType) {
          // Find the variant in the body and extract its parent
          const parent = extractParentFromConstructor(termType);
          if (parent) return parent;
        }
      }
    }
  }

  return null;
}

function extractParentFromConstructor(type: Type): Type | null {
  // Navigate through foralls to find the variant injection
  let acc = type;
  const typeVars: string[] = [];

  while ("forall" in acc) {
    typeVars.push(acc.forall.var);
    acc = acc.forall.body;
  }

  // Should end in: t → variant_type
  if ("arrow" in acc) {
    const resType = acc.arrow.to;
    // If it's a variant, we need to wrap it in lambdas to get the constructor
    if ("variant" in resType) {
      let lambdaType: Type = resType;
      for (let i = typeVars.length - 1; i >= 0; i--)
        lambdaType = lamType(typeVars[i]!, starKind, lambdaType);
      return lambdaType;
    }
  }
  return null;
}

/**
 * Synthesizes a **type‑level lambda constructor** from a structural variant.
 *
 * This function takes a *structural variant type* like:
 *
 *   <Left: t0 | Right: t1>
 *
 * and produces a **higher‑kinded type constructor** that can be applied to
 * type arguments:
 *
 *   λt0::*. λt1::*. <Left: t0 | Right: t1>
 *
 * This allows structural variants to behave like named enums (e.g. `Either`)
 * when performing trait resolution or higher‑kinded unification.
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * Sometimes the typechecker encounters a **variant pattern** or **scrutinee**
 * without a nominal enum name.
 *
 * Example:
 * ```ts
 * match x {
 *   Left(v)  => ...
 *   Right(w) => ...
 * }
 * ```
 *
 * Here the scrutinee might be a structural type:
 *
 *   <Left: A | Right: B>
 *
 * But to unify this with a polymorphic enum implementation like:
 *
 *   impl Functor<Either> { ... }
 *
 * we need a *lambda constructor* that acts like:
 *
 *   Either ≡ λL::*. λR::*. <Left: L | Right: R>
 *
 * `createVariantLambda` generates exactly that.
 *
 * In short:
 * **It turns a structural variant into a reusable type constructor.**
 *
 * ---------------------------------------------------------------------------
 * How it works
 * ---------------------------------------------------------------------------
 * 1. The `selfKind` tells us **how many type parameters** the constructor should take:
 *    - `* → *` → unary: generate λt0
 *    - `* → (* → *)` → binary: generate λt1. λt0
 *
 * 2. It extracts the number and order of argument kinds by peeling the `arrowKind`.
 *
 * 3. It wraps the variant body in that many type‑lambdas.
 *
 * Example:
 * ```ts
 * vtype = <Left: a | Right: b>
 * selfKind = * → * → *
 *
 * createVariantLambda(vtype, selfKind)
 *   → λt1::*. λt0::*.
 *        <Left: t0 | Right: t1>
 * ```
 *
 * ---------------------------------------------------------------------------
 * When it's used
 * ---------------------------------------------------------------------------
 * - **Trait resolution**: inferring the “self” type for trait implementations
 * - **Nominalizing** structural variants for unification
 * - **Pattern inference**: determining enum identity from variant patterns
 *
 * This is one of the key glue functions that allow the system to interoperate
 * between:
 * - structural types (`variantType`)
 * - nominal ADTs (declared enums)
 * - higher‑kinded trait implementations
 *
 * ---------------------------------------------------------------------------
 * @param vtype - A structural variant type (must contain `"variant"` tag)
 * @param selfKind - The kind of the overall type constructor (`*`, `* → *`, ...)
 * @returns A type‑level lambda that abstracts over the appropriate number of
 *          type parameters, or `vtype` unchanged if it is not a variant.
 *
 * ---------------------------------------------------------------------------
 * @example Unary example
 * ```ts
 * const v = variantType([
 *   ["None", tupleType([])],
 *   ["Some", varType("a")]
 * ]);
 *
 * createVariantLambda(v, arrowKind(starKind, starKind));
 * // => λt0::*. <None: ⊥ | Some: t0>
 * ```
 *
 * @example Binary example
 * ```ts
 * const v = variantType([
 *   ["Left",  varType("l")],
 *   ["Right", varType("r")]
 * ]);
 *
 * createVariantLambda(v,
 *   arrowKind(starKind, arrowKind(starKind, starKind))
 * );
 * // => λt1::*. λt0::*. <Left: t0 | Right: t1>
 * ```
 */
export function createVariantLambda(vtype: Type, selfKind: Kind): Type {
  if (!("variant" in vtype)) return vtype;

  // Determine argument kinds by peeling arrows
  const argKinds: Kind[] = [];
  let k: Kind = selfKind;
  while ("arrow" in k) {
    argKinds.push(k.arrow.from);
    k = k.arrow.to;
  }

  // Synthesize variable names: t0, t1, ...
  const argNames = argKinds.map((_, i) => `t${i}`);

  // Build λ abstractions from inside out
  let res: Type = vtype;
  for (let i = argNames.length - 1; i >= 0; i--) {
    res = lamType(argNames[i]!, argKinds[i]!, res);
  }

  return res;
}

function inferLamType(state: TypeCheckerState, term: LamTerm) {
  const argKind = checkKind(state, term.lam.type);
  if ("err" in argKind) return argKind;

  if (!isStarKind(argKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: argKind.ok } });

  const extendedContext: Context = [
    { term: { name: term.lam.arg, type: term.lam.type } },
    ...state.ctx,
  ];

  const bodyType = inferType(
    { ctx: extendedContext, meta: state.meta },
    term.lam.body,
  );
  if ("err" in bodyType) return bodyType;

  // Apply meta solutions to resolve the parameter type, but don't fully normalize
  // (which would expand enums to structural form)
  const resolvedParamType = applySubstitution(
    state,
    state.meta.solutions,
    term.lam.type,
  );

  return ok(arrowType(resolvedParamType, normalizeType(state, bodyType.ok)));
}

function inferVarType(state: TypeCheckerState, term: VarTerm) {
  // Check for term binding
  const termBinding = state.ctx.find(
    (b) => "term" in b && b.term.name === term.var,
  );
  if (termBinding && "term" in termBinding) return ok(termBinding.term.type);

  // Check for dict binding
  const dictBinding = state.ctx.find(
    (b) => "dict" in b && b.dict.name === term.var,
  );
  if (dictBinding && "dict" in dictBinding)
    // Return a dictionary type marker
    return ok(
      conType(
        `Dict<${dictBinding.dict.trait}, ${showType(dictBinding.dict.type)}>`,
      ),
    );

  return err({ unbound: term.var });
}

/**
 * Collects all **unbound meta‑variables** (`?N`) appearing inside a type.
 *
 * Meta‑variables represent *unknown types* created during inference
 * (via {@link freshMetaVar}).
 * A meta‑var is **unbound** if it does not yet have a solution recorded in
 * `state.meta.solutions`.
 *
 * This helper walks the structure of a type and gathers the names of all such
 * unsolved metas.
 *
 * ---------------------------------------------------------------------------
 * Why this matters
 * ---------------------------------------------------------------------------
 * Unbound meta‑vars indicate:
 * - type inference is incomplete
 * - a type still depends on unknown information
 *
 * This function is useful for:
 * - **generalization checks** (do not generalize a type with unresolved metas)
 * - **error reporting** (show which metas are stuck)
 * - **debugging** normalization and unification
 *
 * ---------------------------------------------------------------------------
 * How it works
 * ---------------------------------------------------------------------------
 * - Recursively scans the structure of `ty`
 * - When it sees a meta‑var `?N`:
 *   - If `state.meta.solutions` has no entry for `?N`
 *     → add to result
 * - Traverses:
 *   - applications
 *   - arrows
 *   - tuples
 *   - records
 *   - variants
 * - Does **not** recurse into binders (`∀`, `λ`, `μ`) since they do not bind metas
 *
 * NOTE: This function only looks for **meta‑vars**, not rigid type variables.
 *
 * ---------------------------------------------------------------------------
 * @param state - Checker state containing meta‑var solutions
 * @param ty - Type to inspect
 * @param metas - Internal accumulator (optional)
 * @returns A list of unsolved meta‑variable names (e.g., `["?0", "?3"]`)
 *
 * ---------------------------------------------------------------------------
 * @example One unbound meta:
 * ```ts
 * const mv = freshMetaVar(state.meta); // ?0
 * getUnboundMetas(state, mv);  // ["?0"]
 * ```
 *
 * @example Solved meta:
 * ```ts
 * state.meta.solutions.set("?0", conType("Int"));
 * getUnboundMetas(state, varType("A"));  // []
 * ```
 *
 * @example Nested structure:
 * ```ts
 * const t = recordType([["x", ?0], ["y", ?1]]);
 * getUnboundMetas(state, t);  // ["?0", "?1"]
 * ```
 */
export function getUnboundMetas(
  state: TypeCheckerState,
  ty: Type,
  metas = new Set<string>(),
): string[] {
  if ("evar" in ty) {
    if (!state.meta.solutions.has(ty.evar)) metas.add(ty.evar);
  } else if ("app" in ty) {
    getUnboundMetas(state, ty.app.func, metas);
    getUnboundMetas(state, ty.app.arg, metas);
  } else if ("arrow" in ty) {
    getUnboundMetas(state, ty.arrow.from, metas);
    getUnboundMetas(state, ty.arrow.to, metas);
  } else if ("tuple" in ty)
    for (const t of ty.tuple) getUnboundMetas(state, t, metas);
  else if ("record" in ty)
    for (const [, t] of ty.record) getUnboundMetas(state, t, metas);
  else if ("variant" in ty)
    for (const [, t] of ty.variant) getUnboundMetas(state, t, metas);

  return Array.from(metas);
}

/**
 * Processes and resolves a **worklist of constraints** produced during
 * type inference and unification.
 *
 * This is the “constraint solver” at the heart of the typechecker.
 *
 * A constraint may be:
 * - **Type equality** (`τ₁ = τ₂`)
 * - **Kind equality** (`κ₁ = κ₂`)
 * - **Deferred kind check** (`Γ ⊢ τ : κ`)
 * - **Deferred type check** (`Γ ⊢ e : τ`)
 *
 * Each constraint is handled by {@link processConstraint}, which may:
 * - generate new constraints,
 * - update the substitution map,
 * - or raise a typing error.
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * The typechecker uses a **worklist‑based algorithm**:
 *
 * 1. Typing rules do *not* immediately solve unifications.
 * 2. Instead, they generate *constraints* describing relationships that must hold.
 * 3. The constraint solver repeatedly processes these until:
 *    - all constraints are solved → success, or
 *    - a contradiction is found → type error.
 *
 * This makes the typechecker:
 * - more modular (inference rules just generate constraints)
 * - more expressive (supports deferred checks, HKTs, trait evidence, etc.)
 * - able to unify many interacting constraints at once
 *
 * ---------------------------------------------------------------------------
 * Substitution behavior
 * ---------------------------------------------------------------------------
 * `subst` is a map of meta‑variable bindings accumulated during solving:
 *
 *   ?0 := Int
 *   ?1 := List<?2>
 *
 * The solver *mutates* this map:
 * - `unifyTypes` updates it for flex‑rigid bindings
 * - `unifyKinds` may add no bindings, only validation
 * - deferred checks add new `type_eq` / `kind_eq` constraints
 *
 * At the end:
 *
 *     ok(subst)
 *
 * contains all meta‑variable solutions discovered during solving.
 *
 * The caller (e.g. `checkType`, `inferAppType`) typically merges these with
 * global meta‑var solutions.
 *
 * ---------------------------------------------------------------------------
 * Algorithm (simplified)
 * ---------------------------------------------------------------------------
 *
 * while (worklist not empty):
 *   - pop next constraint
 *   - call `processConstraint`
 *   - `processConstraint` may:
 *       - update `subst`
 *       - push new constraints
 *       - return an error
 *
 * If we reach the end with no errors:
 *   return ok(subst)
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * Any error produced by `processConstraint`, including:
 * - `type_mismatch`
 * - `kind_mismatch`
 * - `cyclic`
 * - `not_a_type_function`
 * - `missing_trait_impl` (if deferred typechecking fails)
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Simple type equality**
 * ```ts
 * const wl = [typeEq(varType("a"), conType("Int"))];
 * solveConstraints(state, wl, new Map());
 * // => ok(Map { "a" -> Int })
 * ```
 *
 * **Kind mismatch**
 * ```ts
 * const wl = [kindEq(starKind, arrowKind(starKind, starKind))];
 * solveConstraints(state, wl);
 * // => err({ kind_mismatch: ... })
 * ```
 *
 * **Chained unification**
 * Constraints may add more constraints before they can be solved.
 * ```ts
 * unifyTypes(state, A → B, Int → Bool, wl, subst);
 * solveConstraints(state, wl, subst);
 * // => A := Int, B := Bool
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related:
 * ---------------------------------------------------------------------------
 * - {@link Constraint} — the supported constraint types
 * - {@link processConstraint} — processes a single constraint
 * - {@link unifyTypes} — generates `type_eq` constraints
 * - {@link hasType} / {@link hasKind} — generate deferred constraints
 * - {@link mergeSubsts} — combines solver results with global substitutions
 *
 * @param state - The typechecker state (context + meta‑vars)
 * @param worklist - A list of constraints to solve
 * @param subst - (Optional) existing substitution map to extend
 * @returns The completed substitution map, or a typing error
 */
export function solveConstraints(
  state: TypeCheckerState,
  worklist: Worklist,
  subst: Substitution = new Map(),
): Result<TypingError, Substitution> {
  while (worklist.length > 0) {
    const result = processConstraint(state, worklist.shift()!, worklist, subst);
    if ("err" in result) return result;
  }

  return ok(subst);
}

/**
 * Processes a **single constraint** in the solver worklist.
 *
 * This is the central dispatcher used by {@link solveConstraints}.
 * Each constraint describes something the typechecker must eventually enforce:
 *
 * - **Type equality**        (`τ₁ = τ₂`)
 * - **Kind equality**        (`κ₁ = κ₂`)
 * - **Deferred kind check**  (`Γ ⊢ τ : κ`)
 * - **Deferred type check**  (`Γ ⊢ e : τ`)
 *
 * `processConstraint` handles exactly one of these, possibly:
 * - updating the local substitution map
 * - pushing new constraints onto the worklist
 * - or returning a typing error
 *
 * ---------------------------------------------------------------------------
 * Constraint types and how they are processed
 * ---------------------------------------------------------------------------
 *
 * 1. **Type equality** (`{ type_eq: { left, right } }`)
 *    - First apply current substitutions to both sides
 *    - Normalize both sides
 *    - Call {@link unifyTypes}, which:
 *      - may update `subst`
 *      - may add new constraints to `worklist`
 *      - may return an error
 *
 * 2. **Kind equality** (`{ kind_eq: { left, right } }`)
 *    - Compare kinds structurally using {@link unifyKinds}
 *    - Errors if mismatched
 *
 * 3. **Deferred kind check** (`{ has_kind: { ty, kind, state } }`)
 *    - Apply current substitutions to the type
 *    - Run {@link checkKind} using the stored state
 *    - If successful, push a new **kind equality** constraint:
 *        `inferredKind = expectedKind`
 *    - This allows kind checking to wait until meta‑vars are solved
 *
 * 4. **Deferred type check** (`{ has_type: { term, ty, state } }`)
 *    - Infer the type of the term using the stored state
 *    - Add a new **type equality** constraint:
 *        `inferredType = expectedType`
 *    - Like `has_kind`, this supports staged checking
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * Deferred and incremental solving is essential for:
 * - higher‑kinded polymorphism
 * - type‑level lambdas and beta‑reduction
 * - trait dictionary validation
 * - match typing (especially branches)
 * - general constraint‑based inference
 *
 * `unifyTypes` alone cannot solve all relationships immediately.
 * Instead, constraints build up, and `processConstraint` handles them
 * one step at a time.
 *
 * ---------------------------------------------------------------------------
 * Worklist interaction
 * ---------------------------------------------------------------------------
 * - This function always consumes **one** constraint.
 * - It may push *more* constraints to the end of `worklist`.
 * - `solveConstraints` repeats until the worklist is empty or an error occurs.
 *
 * ---------------------------------------------------------------------------
 * Substitution interaction
 * ---------------------------------------------------------------------------
 * - Type and kind equality may bind meta‑variables
 * - Substitution is mutated *in place*
 * - Deferred constraints use the updated substitutions when re‑processing
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Type equality**
 * ```ts
 * processConstraint(state, typeEq(A, Int), worklist, subst);
 * // => subst["A"] = Int
 * ```
 *
 * **Kind equality**
 * ```ts
 * processConstraint(state, kindEq(starKind, starKind), wl, subst);
 * // => ok
 * ```
 *
 * **Deferred kind check**
 * ```ts
 * hasKind(conType("List"), arrowKind(*, *), state)
 * // resolves to: kindEq(ListKind, arrowKind(*, *))
 * ```
 *
 * **Deferred type check**
 * ```ts
 * hasType(term, expectedTy, state)
 * // resolves to: typeEq(inferredTy, expectedTy)
 * ```
 *
 * ---------------------------------------------------------------------------
 * @param state - Full typechecker state (used for kind/type inference)
 * @param constraint - The constraint to process
 * @param worklist - The active constraint queue (may be mutated)
 * @param subst - The local substitution map (mutated by solving)
 * @returns `ok(null)` on success, or a `TypingError`
 */
export function processConstraint(
  state: TypeCheckerState,
  constraint: Constraint,
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  if ("type_eq" in constraint) {
    return unifyTypes(
      state,
      normalizeType(
        state,
        applySubstitution(state, subst, constraint.type_eq.left),
      ),
      normalizeType(
        state,
        applySubstitution(state, subst, constraint.type_eq.right),
      ),
      worklist,
      subst,
    );
  }

  if ("kind_eq" in constraint)
    return unifyKinds(constraint.kind_eq.left, constraint.kind_eq.right);

  if ("has_kind" in constraint) {
    const type = applySubstitution(state, subst, constraint.has_kind.ty);
    const kindResult = checkKind(constraint.has_kind.state, type);

    if ("err" in kindResult) return kindResult;

    worklist.push(kindEq(kindResult.ok, constraint.has_kind.kind));

    return ok(null);
  }

  if ("has_type" in constraint) {
    const typeResult = inferType(
      constraint.has_type.state,
      constraint.has_type.term,
    );

    if ("err" in typeResult) return typeResult;

    worklist.push(typeEq(typeResult.ok, constraint.has_type.ty));

    return ok(null);
  }

  throw new Error("Unknown constraint kind");
}

/**
 * Top‑level entrypoint for **type inference**.
 *
 * This is simply an alias for {@link inferType}, provided for convenience and
 * symmetry with `checkType` and `inferTypeWithMode`.
 *
 * Use this when you want to *infer* a type (synthesis mode), i.e.:
 *
 *    Γ ⊢ term ⇒ τ
 *
 * If you instead need to *check* a term against a known type, use
 * {@link checkType} or {@link inferTypeWithMode} with check mode.
 *
 * @param state - Typechecker state (context + meta‑variables)
 * @param term - The term to infer a type for
 * @returns The inferred type or a {@link TypingError}
 *
 * @see {@link inferType} The underlying implementation
 * @see {@link inferTypeWithMode} Bidirectional dispatcher
 * @see {@link checkType} Checking mode
 */
export const typeCheck = inferType;

/**
 * Performs **constraint‑based type inference** for a term.
 *
 * This is an alternative entrypoint to plain `inferType`. Instead of inferring
 * the type directly, it:
 *
 * 1. Creates a fresh meta‑variable for the result type (`$result`)
 * 2. Generates a **deferred type‑checking constraint**
 *      Γ ⊢ term : $result
 * 3. Solves all resulting constraints using {@link solveConstraints}
 * 4. If `$result` is solved → return it
 *    otherwise → fall back to normal inference
 *
 * ------------------------------------------------------------
 * Why this exists
 * ------------------------------------------------------------
 * Most of the typechecker eagerly solves constraints inside inference rules.
 * However, some situations benefit from **fully deferring** typechecking:
 *
 * - large or deeply nested terms
 * - terms involving many meta‑variables
 * - debugging unification behavior
 * - explicit constraint‑driven inference (Hindley–Milner style)
 *
 * This function lets the solver accumulate *all* constraints generated by the
 * typing of the term and resolve them in one batch.
 *
 * It is mainly a **utility / experimental helper** rather than a primary
 * typing API.
 *
 * ------------------------------------------------------------
 * Returned type
 * ------------------------------------------------------------
 * The result is:
 *
 *   ok(τ)     if $result was solved
 *   err(e)    on any constraint or unification error
 *
 * If the result meta‑var `$result` was never solved (the constraint system did
 * not determine a final type), we fall back to:
 *
 *   inferType(state, term)
 *
 * so the function always produces a type unless a real error occurs.
 *
 * ------------------------------------------------------------
 * Example
 * ------------------------------------------------------------
 * ```ts
 * const id = lamTerm("x", Int, varTerm("x"));
 * const res = typecheckWithConstraints(state, id);
 * // => ok(Int → Int)
 * ```
 *
 * With prior context:
 * ```ts
 * state = addTerm(state, "f", lamTerm("x", Int, varTerm("x"))).ok;
 * const res = typecheckWithConstraints(state, appTerm(varTerm("f"), conTerm("42", Int)));
 * // => ok(Int)
 * ```
 *
 * ------------------------------------------------------------
 * Related
 * ------------------------------------------------------------
 * - {@link hasType} — creates deferred type constraints
 * - {@link solveConstraints} — processes the worklist
 * - {@link inferType} — fallback inference
 * - {@link applySubstitution} — used to extract `$result`
 *
 * @param state - The typechecker state (context + meta env)
 * @param term - The term to infer using constraint solving
 * @returns The inferred type or a {@link TypingError}
 */
export function typecheckWithConstraints(
  state: TypeCheckerState,
  term: Term,
): Result<TypingError, Type> {
  const worklist: Worklist = [hasType(term, { var: "$result" }, state)];

  const subst = new Map<string, Type>();
  const result = solveConstraints(state, worklist, subst);

  if ("err" in result) return result;

  const resultType = subst.get("$result");
  if (!resultType) return inferType(state, term);

  return ok(resultType);
}

/**
 * Fully **normalizes** a type by recursively expanding, reducing, and resolving
 * all type‑level structure until it reaches its canonical form.
 *
 * This is one of the most important functions in the entire type system.
 *
 * “Normalization” means:
 *   - Expand type aliases
 *   - Expand nominal enums into structural variants (and μ‑types if recursive)
 *   - β‑reduce type‑level lambdas (`(λA. body) T`)
 *   - Follow solved meta‑variables
 *   - Unfold μ‑types safely (with cycle protection)
 *   - Normalize inside all compound types (arrows, records, variants, tuples, ...)
 *
 * After normalization, two semantically identical types have the **same shape**,
 * allowing consistent:
 *   - type equality (`typesEqual`)
 *   - unification (`unifyTypes`)
 *   - constructor checking
 *   - trait resolution
 *   - pattern matching
 *
 * ---------------------------------------------------------------------------
 * Why normalization is needed
 * ---------------------------------------------------------------------------
 * Almost every subsystem of the typechecker depends on being able to compare
 * types in a canonical form:
 *
 * - **Alias expansion**
 *     ```
 *     type Id<A> = A
 *     normalize(Id<Int>) → Int
 *     ```
 *
 * - **Enum expansion**
 *     ```
 *     enum Option<T> = None | Some(T)
 *     normalize(Option<Int>)
 *         → <None: ⊥ | Some: Int>
 *     ```
 *
 * - **Recursive enum expansion**
 *     ```
 *     List<T> = Nil | Cons(T, List<T>)
 *     normalize(List<Int>)
 *         → μX. <Nil: ⊥ | Cons: (Int, X)>
 *     ```
 *
 * - **Type lambda β‑reduction**
 *     ```
 *     (λA. A → A) Int  →  Int → Int
 *     ```
 *
 * - **Meta‑variable resolution**
 *     ```
 *     ?0 := Int
 *     normalize(?0) → Int
 *     ```
 *
 * Without full normalization, unification, equality, and pattern matching would fail
 * on semantically equivalent but syntactically different types.
 *
 * ---------------------------------------------------------------------------
 * Cycle detection (`seen`)
 * ---------------------------------------------------------------------------
 * Recursive types or aliases can create cycles:
 *
 *   μX. X
 *   type Bad = Bad
 *
 * To prevent infinite recursion, `seen` stores variables and alias keys that we
 * have already attempted to normalize.
 * If a cycle is detected, normalization returns either:
 *   - the unresolved type, or
 *   - `⊥` (never type) for clearly impossible cycles
 *
 * ---------------------------------------------------------------------------
 * Key normalization steps
 * ---------------------------------------------------------------------------
 *
 * 1. **Meta variables**
 *    Follow the global solution if solved:
 *      `?0 := Int` → normalize(Int)
 *
 * 2. **Type aliases**
 *    If `Alias<A, B> = body` and we see `Alias<T, U>`:
 *      - substitute parameters
 *      - normalize substituted body
 *
 * 3. **Enum expansion**
 *    Converts nominal enum types into *structural variant types*, applying
 *    parameters appropriately.
 *
 * 4. **Recursive enums**
 *    Wrap the variant in `μX` when the enum is marked recursive.
 *
 * 5. **Type lambdas**
 *    For `appType(lamType(var, kind, body), arg)`:
 *      substitute and normalize the resulting body (`β`‑reduction)
 *
 * 6. **Compound types**
 *    Normalize subcomponents in:
 *      - arrow types
 *      - tuples
 *      - records
 *      - variants
 *      - bounded foralls / foralls
 *      - apps, recursively
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Alias**
 * ```ts
 * addTypeAlias(state, "Id", ["A"], [*], A);
 * normalize(Id<Int>) → Int
 * ```
 *
 * **Enum**
 * ```ts
 * enum Option<T> = None | Some(T)
 * normalize(Option<Int>) → <None: ⊥ | Some: Int>
 * ```
 *
 * **Recursive enum**
 * ```ts
 * enum List<T> (recursive)
 * normalize(List<Int>)
 *   → μX. <Nil: ⊥ | Cons: (Int, X)>
 * ```
 *
 * **Lambda**
 * ```ts
 * normalize((λA. A) Int) → Int
 * ```
 *
 * **Meta‑vars**
 * ```ts
 * ?0 := Bool
 * normalize(?0) → Bool
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link substituteType} — used in alias, lambda, and μ‑type unfolding
 * - {@link getSpineArgs} / {@link getSpineHead} — used for enum expansion
 * - {@link unifyTypes} — called *after* normalization
 * - {@link typesEqual} — depends critically on normalized types
 *
 * @param state - Typechecker state containing context and meta‑var solutions
 * @param ty - The type to normalize
 * @param seen - Internal set used to prevent infinite recursion (cycle detection)
 * @returns A normalized type in canonical form
 */
export function normalizeType(
  state: TypeCheckerState,
  ty: Type,
  seen = new Set<string>(),
): Type {
  // Cycle detection for variables
  if ("var" in ty && seen.has(ty.var)) return ty;
  const newSeen = "var" in ty ? new Set(seen).add(ty.var) : seen;

  if ("var" in ty || "never" in ty) return ty;

  if (isMetaVar(ty)) {
    if (seen.has(ty.evar)) return neverType; // Cycle → bottom
    const newSeen = new Set(seen).add(ty.evar);
    const sol = state.meta.solutions.get(ty.evar);
    return sol ? normalizeType(state, sol, newSeen) : ty;
  }

  if ("con" in ty) {
    const aliasBinding = state.ctx.find(
      (b) => "type_alias" in b && b.type_alias.name === ty.con,
    );

    if (aliasBinding && "type_alias" in aliasBinding) {
      const alias = aliasBinding.type_alias;

      // Only expand if it's a zero-parameter alias
      if (alias.params.length === 0) {
        // Create key for cycle detection
        const aliasKey = `alias:${ty.con}`;
        if (newSeen.has(aliasKey)) return ty;

        const expandSeen = new Set(newSeen).add(aliasKey);
        return normalizeType(state, alias.body, expandSeen);
      }
      return ty;
    }

    return ty;
  }

  if ("app" in ty) {
    const head = getSpineHead(ty);
    if ("con" in head) {
      const conName = head.con;

      // Check for type alias BEFORE enum
      const aliasBinding = state.ctx.find(
        (b) => "type_alias" in b && b.type_alias.name === conName,
      );

      if (aliasBinding && "type_alias" in aliasBinding) {
        const alias = aliasBinding.type_alias;
        const spineArgs = "con" in ty ? [] : getSpineArgs(ty);

        // Check arity matches
        if (spineArgs.length === alias.params.length) {
          // Create a key to detect recursive expansion
          const aliasKey = `alias:${conName}<${spineArgs.map(showType).join(",")}>`;

          // If we're already expanding this exact alias application, return as-is
          if (newSeen.has(aliasKey)) {
            return ty; // Don't expand recursively
          }

          // Add to seen set before expanding
          const expandSeen = new Set(newSeen).add(aliasKey);

          // Substitute params with concrete args
          let expanded = alias.body;
          for (let i = 0; i < alias.params.length; i++) {
            expanded = substituteType(
              alias.params[i]!,
              spineArgs[i]!,
              expanded,
            );
          }
          // Recursively normalize with the updated seen set
          return normalizeType(state, expanded, expandSeen);
        }
      }

      const enumBinding = state.ctx.find(
        (b) => "enum" in b && b.enum.name === conName,
      );
      // In normalizeType, for "con" in head (enum case):
      if (enumBinding && "enum" in enumBinding) {
        const def = enumBinding.enum;
        const spineArgs = getSpineArgs(ty);
        if (spineArgs.length !== def.params.length) return ty;

        // SINGLE muVar for entire normalization (if recursive)
        let muVar: string | null = null;
        if (def.recursive) {
          muVar = `X${state.meta.counter++}`;
        }

        const structuralVariant: [string, Type][] = [];
        for (const [label, fieldScheme] of def.variants) {
          let instField = fieldScheme;
          for (let i = 0; i < def.params.length; i++) {
            instField = substituteType(
              def.params[i]!,
              spineArgs[i]!,
              instField,
            );
          }

          let fieldForMu = instField;
          if (def.recursive) {
            // Use SHARED muVar (consistent!)
            fieldForMu = substituteType(
              def.name,
              { var: muVar! },
              instField,
              new Set([muVar!]),
            );
          }
          structuralVariant.push([
            label,
            normalizeType(state, fieldForMu, seen),
          ]);
        }

        if (def.recursive) {
          // Use SAME muVar for outer binder
          const muBody = { variant: structuralVariant } as VariantType;
          return muType(muVar!, normalizeType(state, muBody, seen));
        }

        return { variant: structuralVariant };
      }
    }
  }

  // For app - normalize func FIRST, then check for lam reduction
  if ("app" in ty) {
    const normFunc = normalizeType(state, ty.app.func, newSeen);
    if ("lam" in normFunc) {
      // Beta-reduce: [arg / var] body
      const substituted = substituteType(
        normFunc.lam.var,
        ty.app.arg,
        normFunc.lam.body,
      );
      return normalizeType(state, substituted, newSeen); // Recurse to fold further
    }
    // No beta: form normalized app
    const normArg = normalizeType(state, ty.app.arg, newSeen);
    return { app: { func: normFunc, arg: normArg } };
  }

  // Recurse on compounds
  if ("arrow" in ty)
    return arrowType(
      normalizeType(state, ty.arrow.from, newSeen),
      normalizeType(state, ty.arrow.to, newSeen),
    );

  if ("forall" in ty)
    return forallType(
      ty.forall.var,
      ty.forall.kind,
      normalizeType(state, ty.forall.body, newSeen),
    );

  if ("bounded_forall" in ty)
    return boundedForallType(
      ty.bounded_forall.var,
      ty.bounded_forall.kind,
      ty.bounded_forall.constraints.map((c) => ({
        trait: c.trait,
        type: normalizeType(state, c.type, newSeen),
      })),
      normalizeType(state, ty.bounded_forall.body, newSeen),
    );

  if ("lam" in ty)
    return lamType(
      ty.lam.var,
      ty.lam.kind,
      normalizeType(state, ty.lam.body, newSeen),
    );

  if ("record" in ty)
    return recordType(
      ty.record.map(([l, f]) => [l, normalizeType(state, f, newSeen)]),
    );

  if ("variant" in ty)
    return variantType(
      ty.variant.map(([l, c]) => [l, normalizeType(state, c, newSeen)]),
    );

  if ("mu" in ty) {
    if (newSeen.has(ty.mu.var)) return ty;
    const muSeen = new Set(newSeen).add(ty.mu.var);
    return muType(ty.mu.var, normalizeType(state, ty.mu.body, muSeen));
  }

  if ("tuple" in ty)
    return tupleType(ty.tuple.map((t) => normalizeType(state, t, newSeen)));

  return ty; // Fallback
}

/**
 * Instantiates a **bounded polymorphic type** (a `∀{constraints}. τ`) and
 * resolves all required **trait dictionaries** for it.
 *
 * In other words, this converts:
 *
 *     ∀Self::K where C₁(Self), C₂(Self), ... . body
 *
 * into:
 *
 *     body[Self := ?N],  along with  dictionaries for each constraint
 *
 * producing a monomorphic type plus the trait evidence needed at runtime.
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * A *bounded forall* (also called constrained polymorphism) introduces:
 * - a type variable (e.g. `Self`)
 * - a kind for that type variable
 * - one or more **trait constraints**, e.g.:
 *
 *       Eq<Self>, Show<Self>
 *
 * To use such a type concretely, we must:
 * 1. Instantiate `Self` with a fresh type meta‑variable (`?N`)
 * 2. Substitute that meta‑var into every constraint
 * 3. Resolve each constraint into an actual dictionary term
 *    using {@link checkTraitConstraints}
 * 4. Substitute the meta‑var into the body type
 *
 * This is the bounded‑forall analogue of {@link instantiateType}.
 *
 * ---------------------------------------------------------------------------
 * What it returns
 * ---------------------------------------------------------------------------
 * On success:
 *
 *   ok({ type: instantiatedBody, dicts: [d₁, d₂, ...] })
 *
 * where:
 * - `type`  = the instantiated body with fresh meta‑vars
 * - `dicts` = the dictionaries needed to satisfy all trait constraints
 *
 * On failure:
 *   - the first trait constraint error (e.g. `missing_trait_impl`)
 *
 * ---------------------------------------------------------------------------
 * Algorithm (simplified)
 * ---------------------------------------------------------------------------
 *
 * If `ty` is:
 *
 *   ∀Self::K where [C₁, C₂, ...]. body
 *
 * then:
 *
 * 1. Create a fresh meta‑variable `?N` to replace `Self`
 *
 * 2. Instantiate each constraint:
 *        Ci[Self := ?N]
 *
 * 3. Resolve all constraints:
 *        dicts = checkTraitConstraints(state, instantiatedConstraints)
 *
 * 4. Substitute `Self := ?N` into the body:
 *        instantiatedBody = substituteType(Self, ?N, body)
 *
 * 5. Return `{ instantiatedBody, dicts }`
 *
 * If `ty` is **not** a bounded‑forall:
 *   → Return the type unchanged with `dicts: []`
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Basic bounded forall**
 * ```ts
 * const ty =
 *   ∀Self::* where Eq<Self>. (Self → Int)
 *
 * instantiateWithTraits(state, ty)
 *   → {
 *       type: (?0 → Int),
 *       dicts: [eqDictFor?0]
 *     }
 * ```
 *
 * **Multiple constraints**
 * ```ts
 * ∀T where [Eq<T>, Show<T>]. ...
 * // Resolves to [eqDictForT, showDictForT]
 * ```
 *
 * **Missing trait implementation**
 * ```ts
 * instantiateWithTraits(state,
 *   ∀A where Ord<A>. A
 * );
 * // err: { missing_trait_impl: { trait: "Ord", type: A } }
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link checkTraitConstraints} — resolves each constraint into a dictionary
 * - {@link substituteType} — performs Self := ?N substitution
 * - {@link instantiateType} — non‑bounded forall instantiation
 * - {@link traitAppTerm} — the term‑level application of trait lambdas
 *
 * @param state - The typechecker state (used to resolve trait implementations)
 * @param ty - A type that may or may not be a bounded forall
 * @returns A monomorphic instantiated type plus its trait dictionaries
 */
export function instantiateWithTraits(
  state: TypeCheckerState,
  ty: Type,
): Result<TypingError, { type: Type; dicts: Term[] }> {
  // Only bother for bounded forall
  if (!("bounded_forall" in ty)) return ok({ type: ty, dicts: [] });

  const bound = ty.bounded_forall;

  // Instantiate the type variable with a fresh meta variable
  const fresh = freshMetaVar(state.meta);

  // Substitute fresh into constraints BEFORE checking
  const instantiatedConstraints = bound.constraints.map((c) => ({
    trait: c.trait,
    type: substituteType(bound.var, fresh, c.type),
  }));

  // Now check constraints with the instantiated type
  const dictsResult = checkTraitConstraints(state, instantiatedConstraints);
  if ("err" in dictsResult) return dictsResult;

  // Substitute fresh into body
  const body = substituteType(bound.var, fresh, bound.body);

  // Return the substituted type plus the dict terms we found
  return ok({ type: body, dicts: dictsResult.ok });
}

/**
 * Automatically **instantiates polymorphic terms**, including both:
 *
 * 1. **System F type polymorphism**
 *      ∀A. τ    →    τ[A := ?N]
 *
 * 2. **Trait‑bounded polymorphism**
 *      ∀Self where C(Self). τ    →    τ[Self := ?M] with dictionaries
 *
 * It returns both the **instantiated term** (with implicit `tyapp` or
 * `trait_app` inserted) and the resulting **monomorphic type**.
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * Normally, to use a polymorphic value you must explicitly apply:
 * - type arguments (for type lambdas / `∀`)
 * - dictionaries (for trait‑bounded foralls)
 *
 * Example (explicit):
 * ```ts
 * poly    : ∀A. A → A
 * polyInt : (Int → Int)    = poly[Int]
 *
 * eqLam   : ∀Self where Eq<Self>. Self → Bool
 * app     : Int → Bool     = eqLam[Int] with { eqIntDict }
 * ```
 *
 * `autoInstantiate` makes this implicit and ergonomic:
 *
 * ```ts
 * autoInstantiate(state, poly)   // inserts [ ?N ]
 * autoInstantiate(state, eqLam)  // inserts [ ?M ] with dicts
 * ```
 *
 * This is especially useful when the user never writes explicit type
 * applications or dictionary arguments.
 *
 * ---------------------------------------------------------------------------
 * How it works (high‑level)
 * ---------------------------------------------------------------------------
 * 1. **Infer the type of the term** using {@link inferType}.
 *
 * 2. While the type begins with a `forall`:
 *      - allocate a fresh meta‑variable `?N`
 *      - insert an implicit `tyapp` into the term
 *      - substitute `A := ?N` into the type
 *
 * 3. While the type begins with a `bounded_forall`:
 *      - use {@link instantiateWithTraits} to instantiate `Self := ?M`
 *      - obtain required dictionaries
 *      - insert a `trait_app` node into the term
 *
 * 4. When no more polymorphic binders remain:
 *      → return the instantiated term and resulting type.
 *
 * This yields a **fully applied, monomorphic** version of the original term.
 *
 * ---------------------------------------------------------------------------
 * What it returns
 * ---------------------------------------------------------------------------
 * ```ts
 * ok({
 *   term:  instantiatedTerm,   // term with tyapps / traitApps inserted
 *   type:  monomorphicType     // all foralls eliminated
 * })
 * ```
 *
 * On error:
 *   - Any trait implementation lookup failure
 *     (missing impl, wrong number of dictionaries, etc.)
 *   - Errors encountered during inference
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Simple ∀ instantiation**
 * ```ts
 * const poly = ΛA::*. λx:A. x
 * autoInstantiate(state, poly)
 * // => term: poly [?0]
 * //    type: (?0 → ?0)
 * ```
 *
 * **Trait‑bounded instantiation**
 * ```ts
 * const lam = ΛSelf where Eq<Self>. λx:Self. x
 * autoInstantiate(state, lam)
 * // => term: lam [?1] with { eqDictFor?1 }
 * //    type: (?1 → ?1)
 * ```
 *
 * **Mixed case**
 * Terms may have nested foralls and bounded foralls; both are handled.
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link inferType} — gets the starting polymorphic type
 * - {@link tyappTerm} — inserted for ∀ instantiation
 * - {@link traitAppTerm} — inserted for trait-bounded instantiation
 * - {@link instantiateWithTraits} — handles constraints + dicts
 *
 * @param state - The typechecker state
 * @param term - A possibly polymorphic term
 * @returns The instantiated term and resulting monomorphic type, or a typing error
 */
export function autoInstantiate(
  state: TypeCheckerState,
  term: Term,
): Result<TypingError, { term: Term; type: Type }> {
  const termType = inferType(state, term);
  if ("err" in termType) return termType;

  let accTerm = term;
  let accType = termType.ok;

  // Auto-apply type arguments
  while ("forall" in accType) {
    const fv = freshMetaVar(state.meta);
    accTerm = tyappTerm(accTerm, fv);
    accType = substituteType(accType.forall.var, fv, accType.forall.body);
  }

  // Auto-apply trait dictionaries
  while ("bounded_forall" in accType) {
    const instantiateRes = instantiateWithTraits(state, accType);
    if ("err" in instantiateRes) return instantiateRes;

    accTerm = traitAppTerm(
      accTerm,
      freshMetaVar(state.meta),
      instantiateRes.ok.dicts,
    );
    accType = instantiateRes.ok.type;
  }

  return ok({ term: accTerm, type: accType });
}

/**
 * Resolves **solved meta‑variables** inside a type by following their solutions
 * in `state.meta.solutions`.
 *
 * This is a lightweight helper used to “chase” meta‑vars:
 *
 *   ?0 := Int
 *   resolveMetaVars(state, ?0)   →   Int
 *
 * Unlike {@link applySubstitution}, this function:
 * - only replaces **meta‑variables** (not rigid variables or full structures)
 * - only recursively resolves **arrow types** beyond the head
 * - does not apply a general substitution map
 *
 * It is mainly used to:
 * - clean up types for error reporting
 * - display more readable results in the REPL
 * - simplify arrow types whose components contain meta‑var chains
 *
 * ---------------------------------------------------------------------------
 * When to use this vs. applySubstitution
 * ---------------------------------------------------------------------------
 *
 * Use `resolveMetaVars` when:
 * - you just want to collapse solved meta‑vars
 * - you want a fast, shallow cleanup for printing or debugging
 *
 * Use `applySubstitution` when:
 * - you need full substitution (including rigid variables)
 * - you need binder‑aware rewriting
 * - you are performing unification or typechecking
 *
 * ---------------------------------------------------------------------------
 * @param state - The typechecker state (contains meta‑var solutions)
 * @param ty - The type whose meta‑vars should be resolved
 * @returns A type with all solved meta‑vars replaced by their solutions
 *
 * @example
 * ```ts
 * // Suppose ?0 := Int
 * const t = { evar: "?0" };
 * resolveMetaVars(state, t);   // => Int
 * ```
 *
 * @example Arrow chain:
 * ```ts
 * // Suppose ?1 := (?0 → Bool), and ?0 := Int
 * resolveMetaVars(state, { evar: "?1" });
 * // => (Int → Bool)
 * ```
 *
 * @example Unsolved meta:
 * ```ts
 * resolveMetaVars(state, { evar: "?5" });
 * // => ?5   (unchanged)
 * ```
 */
export function resolveMetaVars(state: TypeCheckerState, ty: Type): Type {
  if (isMetaVar(ty)) {
    const solution = state.meta.solutions.get(ty.evar);
    return solution ? resolveMetaVars(state, solution) : ty;
  }

  if ("arrow" in ty)
    return arrowType(
      resolveMetaVars(state, ty.arrow.from),
      resolveMetaVars(state, ty.arrow.to),
    );

  return ty;
}

/**
 * Computes the **arity** of a kind — the number of type arguments it expects.
 *
 * Examples:
 * - `*` has arity **0**
 * - `* → *` has arity **1**
 * - `* → (* → *)` has arity **2**
 *
 * This is useful when validating:
 * - type constructor applications (`List<Int>` expects 1 argument)
 * - enum definitions (checking parameter count)
 * - trait implementations (ensuring correct constructor shape)
 * - type alias expansion
 *
 * The function simply walks along the right‑associated chain of arrow kinds:
 *
 *    κ = κ₁ → (κ₂ → (* → *))
 *    arity = 3
 *
 * @param kind - The kind to measure
 * @returns The number of arguments the kind expects
 *
 * @example
 * ```ts
 * kindArity(starKind);                       // 0
 * kindArity(arrowKind(starKind, starKind));  // 1
 * kindArity(arrowKind(starKind,
 *            arrowKind(starKind, starKind))); // 2
 * ```
 */
export function kindArity(kind: Kind): number {
  if ("star" in kind) return 0;

  let acc = 0;
  while ("arrow" in kind) {
    acc += 1;
    kind = kind.arrow.to;
  }

  return acc;
}

/**
 * Checks whether a type contains **any unsolved meta‑variables** (`?N`).
 *
 * Meta‑variables represent unknown types created during inference
 * (via {@link freshMetaVar}). A meta‑var is **unbound** if it does not have a
 * solution recorded in `state.meta.solutions`.
 *
 * This function answers the yes/no question:
 *
 *    “Is this type fully solved, or does it still contain unknowns?”
 *
 * Why this matters:
 * - Used to decide whether a type may be generalized
 * - Helps detect incomplete inference
 * - Useful for debugging or reporting unsolved meta‑vars in errors
 *
 * The function recursively inspects:
 * - type applications (`F<A>`)
 * - arrows
 * - tuples
 * - records
 * - variants
 *
 * It does **not** inspect binders (`forall`, `lambda`, `mu`), because those
 * bind rigid variables, not meta‑variables.
 *
 * @param state - The typechecker state (contains meta‑var solutions)
 * @param type - The type to inspect
 * @returns `true` if any meta‑variables inside `type` remain unsolved
 *
 * @example
 * ```ts
 * const a = freshMetaVar(state.meta); // ?0
 * hasUnboundMetas(state, a);          // true
 *
 * state.meta.solutions.set("?0", conType("Int"));
 * hasUnboundMetas(state, a);          // false
 * ```
 */
export function hasUnboundMetas(state: TypeCheckerState, type: Type): boolean {
  if (isMetaVar(type) && !state.meta.solutions.has(type.evar)) {
    return true;
  }
  // Recurse on subterms...
  if ("app" in type)
    return (
      hasUnboundMetas(state, type.app.func) ||
      hasUnboundMetas(state, type.app.arg)
    );
  if ("arrow" in type)
    return (
      hasUnboundMetas(state, type.arrow.from) ||
      hasUnboundMetas(state, type.arrow.to)
    );
  if ("tuple" in type) return type.tuple.some((t) => hasUnboundMetas(state, t));
  if ("record" in type)
    return type.record.some(([, ty]) => hasUnboundMetas(state, ty));
  if ("variant" in type)
    return type.variant.some(([, ty]) => hasUnboundMetas(state, ty));
  // Add for other constructors
  return false;
}

/**
 * Collects all **free type variable names** that appear inside a type.
 *
 * This function walks the structure of a type and gathers every occurrence of a
 * `VarType` (`{ var: "A" }`). It *excludes* variables that are **bound** by:
 *
 * - `forall` (universal quantification)
 * - `lam`   (type‑level lambda abstraction)
 * - `mu`    (recursive type binder)
 *
 * In other words, it returns the set of **free type variables** in the type.
 *
 * ---------------------------------------------------------------------------
 * Why this matters
 * ---------------------------------------------------------------------------
 * Free type variables are used for:
 * - **Dependency analysis** during module importing
 *   (e.g., which type constructors a type depends on)
 * - **Generalization checks**
 *   (e.g., only generalize variables not in scope)
 * - **Renaming / alpha‑conversion** tasks
 * - **Pretty‑printing and debugging**
 *
 * This function does *not* detect meta‑variables (`?N`).
 * For that, see {@link getUnboundMetas}.
 *
 * ---------------------------------------------------------------------------
 * Bound vs free example
 * ---------------------------------------------------------------------------
 * ```ts
 * const t = forallType("A", starKind,
 *   arrowType(varType("A"), varType("B"))
 * );
 *
 * collectTypeVars(t)
 * // => ["B"]   (A is bound, B is free)
 * ```
 *
 * ---------------------------------------------------------------------------
 * What it walks
 * ---------------------------------------------------------------------------
 * Recurses through:
 * - type applications (`F<A>`)
 * - arrow types
 * - tuples
 * - records
 * - variants
 *
 * Skips substitution under binders:
 * - `forall A. ...`
 * - `lam A. ...`
 * - `mu A. ...`
 *
 * ---------------------------------------------------------------------------
 * @param type - The type to inspect
 * @param vars - Internal accumulator (optional)
 * @returns All free type variable names as an array
 *
 * ---------------------------------------------------------------------------
 * @example Simple
 * ```ts
 * collectTypeVars(arrowType(varType("A"), varType("B")));
 * // => ["A", "B"]
 * ```
 *
 * @example Bound variable (not collected)
 * ```ts
 * collectTypeVars(forallType("A", starKind, varType("A")));
 * // => []
 * ```
 *
 * @example Records and variants
 * ```ts
 * collectTypeVars(recordType([["x", varType("A")], ["y", varType("B")]]));
 * // => ["A", "B"]
 * ```
 */
export function collectTypeVars(
  type: Type,
  vars = new Set<string>(),
): string[] {
  if ("var" in type) {
    vars.add(type.var);
  } else if ("app" in type) {
    collectTypeVars(type.app.func, vars);
    collectTypeVars(type.app.arg, vars);
  } else if ("arrow" in type) {
    collectTypeVars(type.arrow.from, vars);
    collectTypeVars(type.arrow.to, vars);
  } else if ("forall" in type) {
    // Don't collect bound variables
    const inner = new Set<string>();
    collectTypeVars(type.forall.body, inner);
    inner.delete(type.forall.var);
    for (const v of inner) vars.add(v);
  } else if ("record" in type) {
    for (const [_, fieldType] of type.record) collectTypeVars(fieldType, vars);
  } else if ("tuple" in type) {
    for (const elem of type.tuple) collectTypeVars(elem, vars);
  } else if ("variant" in type) {
    for (const [_, caseType] of type.variant) collectTypeVars(caseType, vars);
  } else if ("lam" in type) {
    const inner = new Set<string>();
    collectTypeVars(type.lam.body, inner);
    inner.delete(type.lam.var);
    for (const v of inner) vars.add(v);
  }

  return Array.from(vars);
}

function computeStrippedKind(
  state: TypeCheckerState, // For kind checks
  type: Type,
  strippableVars: string[], // e.g., ["r", "u"] for impl params
): Result<TypingError, { stripped: number; kind: Kind }> {
  let current = normalizeType(state, type); // Start normalized
  let stripped = 0;

  // Peel trailing apps if arg is strippable var
  while ("app" in current) {
    const arg = current.app.arg;
    if ("var" in arg && strippableVars.includes(arg.var)) {
      // Kind check (as before)
      const argKindRes = checkKind(state, arg);
      if ("err" in argKindRes) return err(argKindRes.err);

      const funcKindRes = checkKind(state, current.app.func);
      if ("err" in funcKindRes) return err(funcKindRes.err);

      if (!("arrow" in funcKindRes.ok))
        return err({ not_a_type_function: current.app.func });

      if (!kindsEqual(funcKindRes.ok.arrow.from, argKindRes.ok)) {
        return err({
          kind_mismatch: {
            expected: funcKindRes.ok.arrow.from,
            actual: argKindRes.ok,
          },
        });
      }

      // Strip: move to func (e.g., from Either l r → Either l)
      current = current.app.func;
      stripped++;

      // Otherwise non-strippable (e.g., concrete or non-impl-var): stop
    } else break;
  }

  // Final kind of stripped (e.g., app(con "Either", l) : * → *)
  const finalKindRes = checkKind(state, current);
  return "err" in finalKindRes
    ? finalKindRes
    : ok({ stripped, kind: finalKindRes.ok });
}

function stripAppsByArity(
  state: TypeCheckerState,
  type: Type,
  arity: number,
): Type {
  let acc = normalizeType(state, type);
  for (let i = 0; i < arity; i++) {
    if ("app" in acc) {
      // Only strip if arg is bound var (as in computeStrippedKind)
      const arg = acc.app.arg;
      if (
        "var" in arg &&
        state.ctx.some((b) => "type" in b && b.type.name === arg.var)
      ) {
        acc = acc.app.func;
      } else break; // Cannot strip further
    } else break;
  }
  return acc;
}

/**
 * Constructs a **function kind** (`from → to`) at the kind level.
 *
 * Kinds describe the “shape” of types:
 * - `*` is the kind of concrete types
 * - `* → *` is the kind of unary type constructors (`List`, `Option`)
 * - `(* → *) → *` is the kind of higher‑order type constructors (`Functor`)
 *
 * `arrowKind(from, to)` creates a kind‑level function that maps types of kind
 * `from` to types of kind `to`.
 *
 * Used when:
 * - declaring higher‑kinded type constructors (`addType`)
 * - building polymorphic binders (`forall`, `λ`)
 * - checking type applications (`checkAppKind`)
 *
 * @param from - Domain kind
 * @param to - Codomain kind
 * @returns A new arrow‑kind (`{ arrow: { from, to } }`)
 *
 * @example
 * ```ts
 * const listKind = arrowKind(starKind, starKind); // List :: * → *
 * const functorKind = arrowKind(
 *   arrowKind(starKind, starKind),
 *   starKind
 * ); // Functor :: (* → *) → *
 * ```
 */
export const arrowKind = (from: Kind, to: Kind): Kind => ({
  arrow: { from, to },
});

/**
 * Constructs a **type variable**.
 *
 * Type variables represent:
 * - parameters in polymorphic types (`∀A. ...`)
 * - parameters in type‑level lambdas (`λA::*. ...`)
 * - unknown types during inference (rigid variables, not meta‑vars)
 *
 * A type variable has no intrinsic meaning by itself; its interpretation
 * depends on how it is bound in the surrounding type.
 *
 * Used in:
 * - arrow types (`A → B`)
 * - polymorphic bodies (`∀A. A → A`)
 * - type constructors and aliases
 * - type‑level substitution
 *
 * @param name - The variable name (`"A"`, `"Self"`, `"T"`)
 * @returns A `VarType` object `{ var: name }`
 *
 * @example
 * ```ts
 * varType("A");               // A
 * arrowType(varType("A"), varType("B"));  // A → B
 * forallType("A", starKind, varType("A"));
 * ```
 */
export const varType = (name: string): VarType => ({ var: name });

/**
 * Constructs a **function type** (`from → to`).
 *
 * Function types are one of the core type constructors in the language.
 *
 * Examples:
 * - `Int → Bool`
 * - `(A → B) → C`
 * - `Self → Int` (inside traits)
 *
 * Used in:
 * - lambda terms (`λx:τ. body`)
 * - trait method signatures
 * - unification of function applications
 * - pattern checking and type‑level substitution
 *
 * The `from` and `to` types must each have kind `*` (checked by `checkArrowKind`).
 *
 * @param from - Parameter type (domain)
 * @param to - Result type (codomain)
 * @returns A `Type` representing `from → to`
 *
 * @example
 * ```ts
 * arrowType(conType("Int"), conType("Bool"));
 * // => (Int → Bool)
 *
 * arrowType(
 *   arrowType(varType("A"), varType("B")),
 *   varType("C")
 * );
 * // => ((A → B) → C)
 * ```
 */
export const arrowType = (from: Type, to: Type): Type => ({
  arrow: { from, to },
});

/**
 * Constructs a **universal (polymorphic) type**:
 *
 *     ∀name::kind. body
 *
 * This binds a **type variable** (`name`) of a given **kind** (`kind`) within
 * the `body` type.
 *
 * Universal types represent *parametric polymorphism* (System F):
 *
 * - `∀A::*. A → A` — the polymorphic identity function
 * - `∀F::(* → *). F<Int>` — higher‑kinded polymorphism
 *
 * The binder associates `name` with a kind so that type applications can be
 * checked for correctness (`A` must be applied only to arguments of the right
 * kind).
 *
 * Used in:
 * - type‑level abstractions (`ΛA::κ. e`)
 * - polymorphic functions
 * - auto‑instantiation via `instantiateType`
 * - type λ‑calculus and higher‑kinded inference
 *
 * @param name - The bound type variable (e.g. `"A"`, `"Self"`)
 * @param kind - The kind of the variable (`*`, `* → *`, ...)
 * @param body - The body type in which the variable is in scope
 * @returns A `ForallType` node
 *
 * @example Basic polymorphism:
 * ```ts
 * forallType("A", starKind,
 *   arrowType(varType("A"), varType("A"))
 * );
 * // => ∀A::*. (A → A)
 * ```
 *
 * @example Higher‑kinded:
 * ```ts
 * forallType("F", arrowKind(starKind, starKind), varType("F"));
 * // => ∀F::(* → *). F
 * ```
 */
export const forallType = (name: string, kind: Kind, body: Type) => ({
  forall: { var: name, kind, body },
});

/**
 * Constructs a **type application**:
 *
 *     func arg
 *
 * This is how higher‑kinded types (type constructors) receive type arguments.
 *
 * Examples:
 * - `List<Int>`     → `appType(conType("List"), conType("Int"))`
 * - `Either<A, B>`  → `appType(appType(Either, A), B)`
 *
 * Internally, type applications are always represented in **left‑associated**
 * form:
 *
 *     F A B  ≡  ((F A) B)
 *
 * Used in:
 * - applying type constructors (`List`, `Either`, etc.)
 * - instantiating polymorphic types
 * - type‑level lambda application and beta‑reduction
 * - enum/alias expansion during `normalizeType`
 * - nominal type unification (using `getSpineHead` / `getSpineArgs`)
 *
 * Kind checking:
 * - `func` must have a kind of the form `κ₁ → κ₂`
 * - `arg` must have kind `κ₁`
 * - the resulting application has kind `κ₂`
 * (checked by `checkAppKind`)
 *
 * @param func - The type‑level function or constructor
 * @param arg - The type argument to apply
 * @returns A type application node
 *
 * @example Unary type constructor:
 * ```ts
 * appType(conType("List"), conType("Int"));
 * // => List<Int>
 * ```
 *
 * @example Binary constructor:
 * ```ts
 * const either = conType("Either");
 * appType(appType(either, conType("String")), conType("Bool"));
 * // => Either<String, Bool>
 * ```
 */
export const appType = (func: Type, arg: Type) => ({ app: { func, arg } });

/**
 * Constructs a **type‑level lambda abstraction**:
 *
 *     λname::kind. body
 *
 * This is the type‑level analogue of a term‑level lambda (`λx. e`), but it
 * abstracts over **types** rather than values.
 *
 * Type lambdas make it possible to write **type functions**, such as:
 * - higher‑kinded constructors
 *   ```
 *   λT::*. List<T>
 *   ```
 * - type‑level identity
 *   ```
 *   λA::*. A
 *   ```
 * - currying multi‑argument type constructors
 *   ```
 *   λA::*. λB::*. (Either<A, B>)
 *   ```
 *
 * Type applications (`appType`) can then apply arguments to type lambdas, and
 * `normalizeType` will **β‑reduce**:
 *
 *     (λA. body) arg   →   body[A := arg]
 *
 * Used in:
 * - enum normalization (recursive ADTs often expand into lambdas)
 * - `createVariantLambda` for structural variant constructors
 * - type‑level β‑reduction in `normalizeType`
 * - higher‑kinded polymorphism
 *
 * @param name - Bound type variable name
 * @param kind - The kind of the bound variable (`*`, `* → *`, etc.)
 * @param body - The type expression where the variable is in scope
 * @returns A type lambda node
 *
 * @example Identity type function:
 * ```ts
 * lamType("A", starKind, varType("A"));
 * // => λA::*. A
 * ```
 *
 * @example Higher‑kinded:
 * ```ts
 * lamType(
 *   "F",
 *   arrowKind(starKind, starKind),
 *   appType(varType("F"), conType("Int"))
 * );
 * // => λF::(* → *). F<Int>
 * ```
 */
export const lamType = (name: string, kind: Kind, body: Type) => ({
  lam: { var: name, kind, body },
});

/**
 * Constructs a **concrete type constructor**.
 *
 * A `ConType` represents:
 * - primitive types (`"Int"`, `"Bool"`, `"String"`)
 * - user‑defined nominal types (`"List"`, `"Option"`)
 * - enum/ADT names before they are expanded by `normalizeType`
 * - type constructors waiting for arguments (`List :: * → *`)
 *
 * `conType("Int")` corresponds to the type `Int`.
 *
 * When applied via {@link appType}, it forms higher‑kinded applications:
 *
 * ```ts
 * appType(conType("List"), conType("Int"));  // List<Int>
 * ```
 *
 * Used in:
 * - type applications
 * - enum / alias resolution
 * - pattern checking (`checkPattern`)
 * - unification and nominal matching
 *
 * @param con - The type constructor name
 * @returns A `ConType` node `{ con: name }`
 *
 * @example
 * ```ts
 * conType("Int");         // Int
 * conType("List");        // List
 * appType(conType("List"), conType("Int"));  // List<Int>
 * ```
 */
export const conType = (con: string) => ({ con });

/**
 * Constructs a **record type**:
 *
 *     { label₁: T₁, label₂: T₂, ... }
 *
 * Record types describe **structural products** with **named fields**.
 * They support **width subtyping**:
 *
 *     { x: Int }  <:  { x: Int, y: Bool }
 *
 * meaning a record with *more* fields can be used where a record with *fewer*
 * fields is expected.
 *
 * Examples:
 * - `{ x: Int, y: Bool }`
 * - `{ name: String, age: Int }`
 *
 * Used in:
 * - record terms (`recordTerm`)
 * - pattern matching (`recordPattern`)
 * - projection (`projectTerm`)
 * - structural unification (`unifyRecordTypes`)
 * - normalization and type equality
 *
 * Kind checking:
 * - Every field type must have kind `*`
 *   (validated by `checkRecordKind`)
 *
 * @param record - An array of `[label, type]` pairs describing fields
 * @returns A `RecordType` node `{ record: [...] }`
 *
 * @example
 * ```ts
 * recordType([
 *   ["x", conType("Int")],
 *   ["y", conType("Bool")]
 * ]);
 * // => { x: Int, y: Bool }
 * ```
 *
 * @example Width subtyping:
 * ```ts
 * const small = recordType([["x", Int]]);
 * const big   = recordType([["x", Int], ["y", Bool]]);
 *
 * isAssignableTo(state, small, big);  // true
 * ```
 */
export const recordType = (record: [string, Type][]) => ({ record });

/**
 * Constructs a **structural variant (sum) type**:
 *
 *     < Label₁: T₁ | Label₂: T₂ | ... >
 *
 * Variant types represent **tagged unions**, also known as:
 * - algebraic sum types
 * - discriminated unions
 * - enum‑like data structures
 *
 * Each case consists of:
 *   - a **label** (e.g. `"Some"`, `"None"`, `"Left"`)
 *   - a **payload type** (e.g. `Int`, `(A, B)`, or `()` for unit / zero payload)
 *
 * Examples:
 * - `<None: () | Some: Int>`
 * - `<Left: A | Right: B>`
 * - `<Nil: () | Cons: (A, List<A>)>`
 *
 * This is the *structural* counterpart to **nominal enums** defined via
 * `addEnum`. Nominal enums are **expanded** into structural variants by
 * {@link normalizeType}.
 *
 * Features of structural variants:
 * - They do **not** rely on a named enum definition.
 * - They support **recursive shapes**, especially under `muType`.
 * - They interact with pattern matching (`variantPattern`).
 * - They unify structurally via `unifyVariants`.
 *
 * Kind checking:
 * - Each payload type must have kind `*`
 *   (validated by `checkVariantKind`)
 *
 * Used in:
 * - pattern matching (`checkPattern`)
 * - variant injections (`injectTerm`)
 * - enum expansion (`normalizeType`)
 * - structural unification and type equality (`unifyVariants`, `typesEqual`)
 *
 * @param variant - An array of `[label, type]` pairs representing cases
 * @returns A `VariantType` node `{ variant: [...] }`
 *
 * @example Binary variant:
 * ```ts
 * variantType([
 *   ["Left",  conType("Int")],
 *   ["Right", conType("Bool")]
 * ]);
 * // => <Left: Int | Right: Bool>
 * ```
 *
 * @example Recursive (combined with muType):
 * ```ts
 * muType("X", variantType([
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("Int"), varType("X")])]
 * ]));
 * // => μX.<Nil: () | Cons: (Int, X)>
 * ```
 */
export const variantType = (variant: [string, Type][]) => ({ variant });

/**
 * Constructs a **recursive type** using a µ‑binder:
 *
 *     μX. body
 *
 * This represents an **equi‑recursive type**, where the type is considered
 * equal to its own unfolding:
 *
 *     μX. T   ≡   T[X := μX. T]
 *
 * Recursive types are used to encode:
 * - linked lists
 * - trees
 * - recursive enums (after normalization)
 * - self‑referential or cyclic data structures
 *
 * Examples:
 * - `μL. (Int, L)` — a simple recursive pair (list‑like)
 * - `μT. <Leaf: Int | Node: (T, T)>` — a recursive tree
 *
 * `muType` does **not** unfold automatically.
 * Unfolding happens when:
 * - matching variant patterns on a recursive enum
 * - using `unfoldTerm` in evaluation
 * - normalization requires expansion of a recursive enum
 *
 * Kind checking:
 * - The µ‑variable is treated as having kind `*`
 * - The body must also check as kind `*`
 *   (verified by `checkMuKind`)
 *
 * Used in:
 * - `normalizeType` (expanding recursive enums into µ‑types)
 * - `inferUnfoldType` / `inferFoldType`
 * - `unifyMuTypes` (alpha‑renaming + structural unification)
 * - pattern matching on recursive structures
 *
 * @param var_name - The bound recursive type variable name (e.g., `"X"`)
 * @param body - The body of the recursive type, which may refer to `var_name`
 * @returns A `MuType` node `{ mu: { var, body } }`
 *
 * @example List‑like recursive structure:
 * ```ts
 * muType("L", tupleType([conType("Int"), varType("L")]));
 * // => μL.(Int, L)
 * ```
 *
 * @example Recursive enum after normalization:
 * ```ts
 * muType("X",
 *   variantType([
 *     ["Nil",  tupleType([])],
 *     ["Cons", tupleType([conType("Int"), varType("X")])]
 *   ])
 * );
 * ```
 */
export const muType = (var_name: string, body: Type): Type => ({
  mu: { var: var_name, body },
});

/**
 * Constructs a **tuple (product) type**:
 *
 *     (T₁, T₂, ..., Tₙ)
 *
 * Tuples represent ordered, fixed‑length collections of values.
 * They differ from records in that:
 * - tuple fields are **positional**, not named
 * - tuple types must have **exact arity** (no width subtyping)
 *
 * Examples:
 * - `(Int, Bool)` — a 2‑tuple
 * - `(A, (B, C))` — nested tuples
 * - `()` — the empty tuple (unit type)
 *
 * Used in:
 * - tuple terms (`tupleTerm`)
 * - tuple pattern matching (`tuplePattern`)
 * - tuple projection (`tupleProjectTerm`)
 * - structural unification (`unifyTupleTypes`)
 * - recursive types (payload of variant cases in lists/trees)
 *
 * Kind checking:
 * - All elements must have kind `*`
 *   (validated by `checkTupleKind`)
 *
 * @param elements - Array of element types in order
 * @returns A `TupleType` node `{ tuple: [...] }`
 *
 * @example
 * ```ts
 * tupleType([conType("Int"), conType("Bool")]);
 * // => (Int, Bool)
 * ```
 *
 * @example Unit tuple:
 * ```ts
 * tupleType([]);
 * // => ()
 * ```
 */
export const tupleType = (elements: Type[]): Type => ({ tuple: elements });

/**
 * Constructs a **bounded universal type**, also written:
 *
 *     ∀name::kind where C₁, C₂, ... . body
 *
 * This represents *trait‑bounded polymorphism*:
 * a type that is universally quantified over a type variable **with
 * additional constraints** that the variable must satisfy.
 *
 * For example:
 *
 * ```ts
 * ∀Self::* where Eq<Self>. (Self → Int)
 * ```
 *
 * means:
 *   “For every type `Self` that implements `Eq`, the function has type
 *    `Self → Int`.”
 *
 * ---------------------------------------------------------------------------
 * Components
 * ---------------------------------------------------------------------------
 * - `name` — the bound type variable (`"Self"`, `"A"`, `"T"`, …)
 * - `kind` — the kind of the variable (`*`, `* → *`, …)
 * - `constraints` — list of trait requirements, each a `TraitConstraint`:
 *     `{ trait: "Eq", type: varType("Self") }`
 * - `body` — the type in which the bound variable is in scope
 *
 * ---------------------------------------------------------------------------
 * How it is used
 * ---------------------------------------------------------------------------
 * Bounded foralls are produced by:
 * - {@link traitLamTerm} (trait lambdas)
 * - trait‑polymorphic functions and methods
 *
 * They are consumed by:
 * - {@link instantiateWithTraits}
 * - {@link inferTraitAppType}
 * - {@link autoInstantiate}
 *
 * The idea:
 *
 * - A type variable introduced by a bounded forall must satisfy certain trait
 *   constraints.
 * - When instantiating the type (e.g., during function application), the
 *   typechecker must **find dictionaries** that satisfy all constraints.
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Single constraint**
 * ```ts
 * boundedForallType(
 *   "Self",
 *   starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   arrowType(varType("Self"), conType("Int"))
 * );
 *
 * // ∀Self::* where Eq<Self>. (Self → Int)
 * ```
 *
 * **Multiple constraints**
 * ```ts
 * boundedForallType(
 *   "T",
 *   starKind,
 *   [
 *     { trait: "Eq",   type: varType("T") },
 *     { trait: "Show", type: varType("T") },
 *   ],
 *   varType("T")
 * );
 * ```
 *
 * ---------------------------------------------------------------------------
 * Related
 * ---------------------------------------------------------------------------
 * - {@link TraitConstraint} — describes each constraint
 * - {@link instantiateWithTraits} — performs instantiation and dictionary lookup
 * - {@link traitLamTerm} — term‑level constructor for bounded polymorphism
 * - {@link checkType} — checks trait lambdas against bounded forall types
 *
 * @param name - The bound type variable
 * @param kind - The variable's kind
 * @param constraints - Trait constraints required on the variable
 * @param body - The type expression under the quantifier
 * @returns A `BoundedForallType` node
 */
export const boundedForallType = (
  name: string,
  kind: Kind,
  constraints: TraitConstraint[],
  body: Type,
): Type => ({
  bounded_forall: { var: name, kind, constraints, body },
});

/**
 * Constructs a **term variable**.
 *
 * Term variables refer to values bound in:
 * - lambda abstractions (`λx. body`)
 * - let-bindings (`let x = value in body`)
 * - pattern matches (variables introduced by patterns)
 * - the global or local typing context
 *
 * During inference, the variable’s type is looked up in the context using
 * {@link inferVarType}.
 *
 * This is the term‑level analogue of {@link varType} for type variables.
 *
 * @param name - The variable name (`"x"`, `"f"`, `"self"`, ...)
 * @returns A `VarTerm` node `{ var: name }`
 *
 * @example
 * ```ts
 * varTerm("x");        // => "x"
 * lamTerm("x", Int, varTerm("x"));
 * ```
 *
 * @see {@link inferVarType} Variable lookup rule
 */
export const varTerm = (name: string) => ({ var: name });

/**
 * Constructs a **lambda term** (function abstraction):
 *
 *     λarg:type. body
 *
 * This represents a function value in the language.
 * The parameter type **must be annotated**, since the system does not infer
 * function argument types automatically in pure inference mode.
 *
 * Lambda terms are typed using the rule:
 *
 *     Γ, arg : type ⊢ body : T
 *     ─────────────────────────  (Lam)
 *       Γ ⊢ λarg:type. body : (type → T)
 *
 * The annotation ensures checking mode and inference are well‑behaved.
 *
 * Used in:
 * - function definitions
 * - dictionary methods
 * - trait lambdas
 * - match branches (functions as values)
 *
 * Typechecking/inference:
 * - {@link inferLamType} handles inference for lambdas
 * - {@link checkType} checks lambdas against expected arrow types
 *
 * @param arg - The function argument name (`"x"`)
 * @param type - The annotated parameter type
 * @param body - The function body term
 * @returns A `LamTerm` node `{ lam: { arg, type, body } }`
 *
 * @example
 * ```ts
 * lamTerm("x", conType("Int"), varTerm("x"));
 * // => λx:Int. x
 * ```
 *
 * @example Higher‑order:
 * ```ts
 * lamTerm("f",
 *   arrowType(Int, Int),
 *   appTerm(varTerm("f"), conTerm("0", Int))
 * );
 * ```
 *
 * @see {@link inferLamType}
 * @see {@link appTerm}
 */
export const lamTerm = (arg: string, type: Type, body: Term) => ({
  lam: { arg, type, body },
});

/**
 * Constructs a **term‑level function application**:
 *
 *     (callee arg)
 *
 * This represents applying a function to an argument.
 * It is the term analogue of type application (`tyappTerm`) and is typed using
 * the usual application rule:
 *
 *     Γ ⊢ callee : A → B
 *     Γ ⊢ arg : A
 *     ───────────────────── (App)
 *     Γ ⊢ callee arg : B
 *
 * Inference:
 * - {@link inferAppType} handles application inference
 * - It automatically instantiates polymorphic functions (`∀`) as needed
 * - It also handles trait‑bounded functions by resolving dictionaries
 *
 * Used in:
 * - calling user‑defined functions
 * - calling lambda expressions
 * - applying dictionary methods
 * - applying polymorphic terms once instantiated
 *
 * @param callee - The function term being called
 * @param arg - The argument term being passed
 * @returns An `AppTerm` node `{ app: { callee, arg } }`
 *
 * @example Basic application:
 * ```ts
 * appTerm(varTerm("f"), varTerm("x"));
 * // => (f x)
 * ```
 *
 * @example Calling a lambda:
 * ```ts
 * const id = lamTerm("x", Int, varTerm("x"));
 * appTerm(id, conTerm("42", Int));
 * // => (λx:Int. x 42)
 * ```
 *
 * @see {@link inferAppType} Application typing rule
 * @see {@link lamTerm} Function abstraction
 */
export const appTerm = (callee: Term, arg: Term) => ({ app: { callee, arg } });

/**
 * Constructs a **type‑level lambda term**:
 *
 *     Λname::kind. body
 *
 * This introduces a **polymorphic type parameter** at the term level.
 * It is the term‑level analogue of a universal type (`∀name::kind. ...`),
 * produced during type inference by {@link inferTylamType}.
 *
 * `tylamTerm` allows terms to be *explicitly polymorphic*, similar to:
 * - System F `ΛA. e`
 * - Haskell with `RankNTypes` and `/\` notation
 *
 * When applied using {@link tyappTerm}, a fresh or concrete type is substituted
 * for the bound type variable.
 *
 * ---------------------------------------------------------------------------
 * Example: Polymorphic identity function
 * ---------------------------------------------------------------------------
 * ```ts
 * const id =
 *   tylamTerm("A", starKind,
 *     lamTerm("x", varType("A"), varTerm("x"))
 *   );
 *
 * // Printed: ΛA::*. λx:A. x
 * ```
 *
 * Applying it to a type:
 * ```ts
 * tyappTerm(id, conType("Int"));
 * // => (ΛA. λx:A. x) [Int]
 * ```
 *
 * ---------------------------------------------------------------------------
 * Usage
 * ---------------------------------------------------------------------------
 * - Represent explicitly polymorphic functions
 * - Support higher‑rank polymorphism (passing polymorphic functions as values)
 * - Enable controlled instantiation via `tyappTerm`, `inferTyappType`, and
 *   `autoInstantiate`
 *
 * Kind checking ensures the parameter has the correct kind inside the body.
 *
 * @param name - The bound type variable (`"A"`)
 * @param kind - The kind of the variable (`*`, `* → *`, ...)
 * @param body - The term in which the variable is in scope
 * @returns A `TyLamTerm` node `{ tylam: { var, kind, body } }`
 *
 * @example Higher‑kinded polymorphism:
 * ```ts
 * tylamTerm("F", arrowKind(starKind, starKind),
 *   lamTerm("x", appType(varType("F"), Int), varTerm("x"))
 * );
 * ```
 *
 * @see {@link tyappTerm} Type application
 * @see {@link inferTylamType} Inference rule
 * @see {@link forallType} Type‑level universal
 */
export const tylamTerm = (name: string, kind: Kind, body: Term) => ({
  tylam: { var: name, kind, body },
});

/**
 * Constructs a **type application term**:
 *
 *     term [type]
 *
 * This applies a polymorphic term (introduced with {@link tylamTerm}) to a
 * specific **type argument**. It is the term‑level analogue of applying a
 * type constructor with {@link appType}.
 *
 * In System F notation:
 *
 *     (ΛA::κ. body) [T]
 *
 * performs `A := T` inside `body`, after kind checking and substitution.
 *
 * ---------------------------------------------------------------------------
 * When this is used
 * ---------------------------------------------------------------------------
 * - To instantiate explicitly polymorphic functions:
 *     ```ts
 *     tyappTerm(polyId, Int)    // polyId[Int]
 *     ```
 *
 * - As an intermediate step during inference:
 *     - `inferTyappType` handles type‑application typing
 *     - type arguments must have the correct kind for the binder
 *
 * - For higher‑rank polymorphism:
 *     ```ts
 *     f (ΛA. e)   // passing a polymorphic function
 *     ```
 *     and the caller may then apply it using `tyappTerm`.
 *
 * - In `autoInstantiate`, this is inserted automatically when a term with a
 *   `forall` type is used without explicit type arguments.
 *
 * ---------------------------------------------------------------------------
 * Kind checking
 * ---------------------------------------------------------------------------
 * Via {@link inferTyappType}, the type argument must match the kind declared
 * by the type lambda:
 *
 *     ΛA::κ. ...   applied to   T
 *
 * requires:
 *
 *     Γ ⊢ T : κ
 *
 * ---------------------------------------------------------------------------
 * @param term - The polymorphic term being instantiated
 * @param type - The type argument to apply
 * @returns A `TyAppTerm` node `{ tyapp: { term, type } }`
 *
 * @example
 * ```ts
 * const polyId = tylamTerm("A", starKind,
 *   lamTerm("x", varType("A"), varTerm("x"))
 * );
 *
 * const idInt = tyappTerm(polyId, conType("Int"));
 * // Printed: (ΛA::*. λx:A. x) [Int]
 * ```
 *
 * @see {@link tylamTerm} Type‑level lambda
 * @see {@link inferTyappType} Typing rule for type application
 * @see {@link forallType} Polymorphic types
 */
export const tyappTerm = (term: Term, type: Type) => ({
  tyapp: { term, type },
});

/**
 * Constructs a **constant term** (literal or nullary constructor) with an
 * explicit type annotation.
 *
 * A `ConTerm` represents values such as:
 * - numeric literals (`"42" : Int`)
 * - boolean literals (`"true" : Bool`)
 * - nullary enum constructors (`None : Option<T>`, `Nil : List<T>`)
 * - other primitive or built‑in constants
 *
 * The type annotation is required so inference for constants is immediate:
 * the typechecker simply returns `type` during {@link inferType}.
 *
 * ---------------------------------------------------------------------------
 * When it is used
 * ---------------------------------------------------------------------------
 * - Literal values in source programs
 * - Enum constructors with no payload
 * - Built‑in constants
 * - Term‑level representation for pattern matching (`conPattern`)
 *
 * ---------------------------------------------------------------------------
 * How it interacts with the typechecker
 * ---------------------------------------------------------------------------
 * - Inference: returns the annotated type unchanged
 *   (`inferType(state, conTerm(...)) → type`)
 *
 * - Pattern matching: constructor patterns (`conPattern`) use the `name`
 *   field for matching and check the type for compatibility.
 *
 * - Injection: nullary variant constructors can be expressed as `conTerm`
 *   when combined with `injectTerm`.
 *
 * @param name - The literal or constructor name (e.g. `"42"`, `"true"`, `"None"`)
 * @param type - The type annotation for this value
 * @returns A `ConTerm` node `{ con: { name, type } }`
 *
 * @example
 * ```ts
 * conTerm("42", conType("Int"));
 * // => 42 : Int
 * ```
 *
 * @example Nullary enum constructor:
 * ```ts
 * conTerm("None", appType(conType("Option"), varType("A")));
 * ```
 *
 * @see {@link inferType} Constant typing rule
 * @see {@link conPattern} Pattern‑matching counterpart
 */
export const conTerm = (name: string, type: Type) => ({ con: { name, type } });

/**
 * Constructs a **record value**:
 *
 *     { label₁ = e₁, label₂ = e₂, ... }
 *
 * A `RecordTerm` pairs each field label with a term expression.
 * Records are **structural**: the order of fields does not matter, and the type
 * of a record is determined entirely by the types of its fields.
 *
 * Example values:
 * - `{ x = 1, y = true }`
 * - `{ point = (x, y) }`
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * `inferRecordType` infers a record’s type by inferring the type of each field:
 *
 * ```ts
 * { x = 1, y = true }
 *   ⇒ { x: Int, y: Bool }
 * ```
 *
 * Record types unify structurally (labels must match), and are compatible
 * with record patterns in `match` expressions.
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - constructing structured data values
 * - pattern matching (`recordPattern`)
 * - field projection (`projectTerm`)
 * - unification of record types (`unifyRecordTypes`)
 *
 * ---------------------------------------------------------------------------
 * @param record - An array of `[label, term]` field pairs
 * @returns A `RecordTerm` node `{ record: [...] }`
 *
 * @example
 * ```ts
 * recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conTerm("Bool"))]
 * ]);
 * // => { x = 1, y = true }
 * ```
 *
 * @see {@link inferRecordType} Infers the type of a record term
 * @see {@link recordType} The type‑level counterpart
 * @see {@link projectTerm} Field access
 * @see {@link recordPattern} Pattern‑matching form
 */
export const recordTerm = (record: [string, Term][]) => ({ record });

/**
 * Constructs a **record field projection**:
 *
 *     record.label
 *
 * This extracts a field from a record value.
 * For example, given:
 *
 *     { x = 1, y = true }.x   ⇒   1
 *
 * The term stores:
 * - `record` — the record expression being accessed
 * - `label`  — the field name to extract
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * Handled by {@link inferProjectType}:
 *
 * 1. Infer the type of the `record` expression.
 * 2. Normalize the type (expands aliases/variants if needed).
 * 3. Verify it is a `RecordType`.
 * 4. Look up the field `label`.
 * 5. Return the corresponding field type.
 *
 * Errors:
 * - `not_a_record` — the scrutinee is not a record type
 * - `missing_field` — the record does not contain the requested label
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - accessing parts of record values
 * - constructing more complex expressions
 * - typing record projections inside match branches
 *
 * @param record - The record expression to project from
 * @param label - The field label to extract
 *
 * @returns A `ProjectTerm` node `{ project: { record, label } }`
 *
 * @example
 * ```ts
 * const rec = recordTerm([["x", conTerm("1", Int)]]);
 * projectTerm(rec, "x");
 * // => {x = 1}.x
 * ```
 *
 * @see {@link inferProjectType} Inference rule for projections
 * @see {@link recordTerm} Value constructor
 * @see {@link recordType} Type constructor
 */
export const projectTerm = (record: Term, label: string) => ({
  project: { record, label },
});

/**
 * Constructs a **variant injection** (tagged value):
 *
 *     <label = value> as variant_type
 *
 * This creates a value belonging to a sum type (variant or enum), such as:
 *
 * - `<Some = 42> as Option<Int>`
 * - `<Left = "err"> as Either<String, Int>`
 * - `<Nil = ()> as List<Int>`
 *
 * The term carries:
 * - `label`         — the constructor/tag name
 * - `value`         — the payload expression
 * - `variant_type`  — the expected variant/enum type
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * The typing rule for injections is handled by {@link inferInjectType}:
 *
 * 1. Infer and normalize `variant_type`.
 * 2. Determine whether it is a **nominal enum** or **structural variant**.
 * 3. Check that `label` exists in the variant definition.
 * 4. Look up the expected payload type for that label.
 * 5. Type‑check `value` against that payload type.
 * 6. Return `variant_type`.
 *
 * Errors produced:
 * - `not_a_variant` — supplied type is not a variant/enum
 * - `invalid_variant_label` — label not present in variant definition
 * - `type_mismatch` — payload does not match the expected case type
 *
 * ---------------------------------------------------------------------------
 * When it is used
 * ---------------------------------------------------------------------------
 * - Constructing values for enums or ADTs
 * - Creating structural variant values (`variantType`)
 * - Defining recursive values for lists/trees (`muType`)
 * - Pattern matching (`variantPattern`) expects matching injected values
 *
 * ---------------------------------------------------------------------------
 * @param label - Variant constructor / tag name
 * @param value - The payload term for this case
 * @param variant_type - The variant/enum type the value should belong to
 *
 * @returns An `InjectTerm` node `{ inject: { label, value, variant_type } }`
 *
 * @example Nominal enum:
 * ```ts
 * injectTerm("Some", conTerm("42", conType("Int")),
 *   appType(conType("Option"), conType("Int"))
 * );
 * ```
 *
 * @example Structural:
 * ```ts
 * injectTerm("Left", conTerm("1", Int),
 *   variantType([["Left", Int], ["Right", Bool]])
 * );
 * ```
 *
 * @see {@link inferInjectType} Inference rule for injection
 * @see {@link variantType} Structural variant constructor
 * @see {@link variantPattern} Pattern‑matching form
 */
export const injectTerm = (label: string, value: Term, variant_type: Type) => ({
  inject: { label, value, variant_type },
});

/**
 * Constructs a **pattern match expression**:
 *
 *     match scrutinee {
 *       pattern₁ => body₁
 *       pattern₂ => body₂
 *       ...
 *     }
 *
 * A `MatchTerm` performs structural case analysis over values such as:
 * - variants / enums (`Some(x)`, `Left(v)`, …)
 * - records (`{ x: p }`)
 * - tuples (`(a, b)`)
 *
 * Each branch consists of:
 * - a **pattern** describing the shape to match
 * - a **body** expression evaluated when the pattern succeeds
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * Typed by {@link inferMatchType}, which:
 *
 * 1. Infers the type of the scrutinee
 * 2. Validates patterns against that type (`checkPattern`)
 * 3. Ensures all patterns together are **exhaustive** (`checkExhaustive`)
 * 4. Extends the context with any variables bound by each pattern
 * 5. Infers each branch’s result type
 * 6. Merges all branch types via subtyping or unification
 *
 * Errors include:
 * - non‑exhaustive matches (`missing_case`)
 * - unreachable or invalid constructors (`extra_case`, `invalid_variant_label`)
 * - incorrect pattern structure (`not_a_variant`, `not_a_record`, etc.)
 * - inconsistent branch result types (`type_mismatch`)
 *
 * ---------------------------------------------------------------------------
 * @param scrutinee - The expression being matched
 * @param cases - An array of `[Pattern, Term]` pairs
 * @returns A `MatchTerm` AST node
 *
 * @example Variant match:
 * ```ts
 * matchTerm(
 *   varTerm("opt"),
 *   [
 *     [variantPattern("None", wildcardPattern()), conTerm("0", Int)],
 *     [variantPattern("Some", varPattern("x")), varTerm("x")]
 *   ]
 * );
 * ```
 *
 * @example Record match:
 * ```ts
 * matchTerm(
 *   recordTerm([["x", conTerm("1", Int)]]),
 *   [
 *     [recordPattern([["x", varPattern("n")]]), varTerm("n")]
 *   ]
 * );
 * ```
 *
 * @see {@link inferMatchType} The match typing rule
 * @see {@link checkPattern} Pattern correctness
 * @see {@link checkExhaustive} Exhaustiveness checking
 */
export const matchTerm = (scrutinee: Term, cases: [Pattern, Term][]): Term => ({
  match: { scrutinee, cases },
});

/**
 * Constructs a **fold** term:
 *
 *     fold[μX. body](term)
 *
 * `foldTerm` *packs* a value into a recursive `μ`‑type.
 * It is the term‑level counterpart of a recursive type constructor.
 *
 * In a recursive type:
 *
 *     μX. T
 *
 * the `fold` operation takes a value of type:
 *
 *     T[X := μX. T]
 *
 * and wraps it into the recursive type `μX. T`.
 *
 * ---------------------------------------------------------------------------
 * Why `fold` is needed
 * ---------------------------------------------------------------------------
 * System F‑ω models recursive types explicitly.
 * To treat a concrete structure as an instance of a recursive type, we must
 * use `fold` to “roll it up.”
 *
 * Example (list-like type):
 *
 *     ListInt = μL. (Int, L)
 *
 * To construct a list node:
 *
 *     fold[ListInt] (1, tail)
 *
 * ---------------------------------------------------------------------------
 * How it is typed
 * ---------------------------------------------------------------------------
 * Handled by {@link inferFoldType}:
 *
 * 1. Check that `type` normalizes to a recursive type (`μX. body`).
 * 2. Compute the unfolded type `body[X := μX. body]`.
 * 3. Check that `term` has this unfolded type.
 * 4. Return the recursive type `type`.
 *
 * Errors include:
 * - folding a non‑recursive type (`type_mismatch`)
 * - incorrect payload structure
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - constructing values for recursive enums (lists, trees)
 * - representing ADTs expanded by {@link normalizeType}
 * - working with structural recursion in the evaluator
 *
 * ---------------------------------------------------------------------------
 * @param type - A recursive type annotation (`μX. body`)
 * @param term - A value matching the one‑step unfolded form of the recursive type
 * @returns A `FoldTerm` node `{ fold: { type, term } }`
 *
 * @example
 * ```ts
 * const listInt = muType("L", tupleType([Int, varType("L")]));
 *
 * const consNode = foldTerm(
 *   listInt,
 *   tupleTerm([conTerm("1", Int), varTerm("tail")])
 * );
 * ```
 *
 * @see {@link inferFoldType} Typing rule
 * @see {@link unfoldTerm} Dual operation
 * @see {@link muType} Recursive types
 */
export const foldTerm = (type: Type, term: Term): Term => ({
  fold: { type, term },
});

/**
 * Constructs an **unfold** term:
 *
 *     unfold(term)
 *
 * `unfoldTerm` *unpacks* a value of a recursive `μ`‑type.
 *
 * For a recursive type:
 *
 *     μX. body
 *
 * the `unfold` operation takes a value of type `μX. body` and produces a value
 * of the **one‑step unfolded type**:
 *
 *     body[X := μX. body]
 *
 * This is the term‑level counterpart to peeling off one layer of recursion.
 *
 * ---------------------------------------------------------------------------
 * Why `unfold` is needed
 * ---------------------------------------------------------------------------
 * Recursive types in System F‑ω do not automatically unroll themselves.
 *
 * To inspect or pattern‑match a recursive structure (like a list or tree),
 * you must call `unfold` to reveal its immediate structure.
 *
 * For example:
 *
 *     ListInt = μL. <Nil: () | Cons: (Int, L)>
 *
 * When matching:
 *
 *     match xs {
 *       Nil      => ...
 *       Cons(h,t)=> ...
 *     }
 *
 * The scrutinee `xs` must be unfolded once so the pattern sees the `<Nil | Cons>` variant.
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * {@link inferUnfoldType} checks:
 *
 * 1. Infer the type of `term`.
 * 2. Ensure it normalizes to a recursive type (`μX. body`).
 * 3. Compute the unfolded type `body[X := μX. body]`.
 * 4. Return the unfolded type as the type of the whole expression.
 *
 * Errors include:
 * - `not_a_function` (if the scrutinee is not a μ‑type)
 * - underlying mismatches when unfolding
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - pattern matching on recursive ADTs
 * - stepping and evaluating recursive structures
 * - explicit recursion handling in `inferUnfoldType`
 * - normalizing recursive values for further analysis
 *
 * @param term - A term whose type is expected to be a μ‑type
 * @returns An `UnfoldTerm` node `{ unfold: term }`
 *
 * @example
 * ```ts
 * // Given xs : μL.(Int, L)
 * const headTail = unfoldTerm(varTerm("xs"));
 * // headTail : (Int, μL.(Int, L))
 * ```
 *
 * @see {@link foldTerm} Dual “pack” operation
 * @see {@link inferUnfoldType} Typing rule
 * @see {@link muType} Recursive type form
 */
export const unfoldTerm = (term: Term): Term => ({
  unfold: term,
});

/**
 * Constructs a **tuple value**:
 *
 *     (e₁, e₂, ..., eₙ)
 *
 * Tuples are ordered, fixed‑size collections of terms.
 * Unlike records, tuple fields are **positional**, not named.
 *
 * Examples of tuple terms:
 * - `(1, true)`
 * - `(x, (y, z))`
 * - `()` — the empty tuple (unit)
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * Handled by {@link inferTupleType}:
 *
 * - Infers the type of each element
 * - Produces a corresponding `TupleType`
 *
 * For example:
 * ```ts
 * tupleTerm([1, true])  ⇒  (Int, Bool)
 * ```
 *
 * Tuples also support indexing via {@link tupleProjectTerm}.
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - constructing structured data
 * - variant payloads (`Cons(hd, tl)`)
 * - recursive ADTs combined with `muType`
 * - pattern matching (`tuplePattern`)
 *
 * ---------------------------------------------------------------------------
 * @param elements - The ordered list of element expressions
 * @returns A `TupleTerm` node `{ tuple: [...] }`
 *
 * @example
 * ```ts
 * tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * // => (1, true)
 * ```
 *
 * @example Unit tuple:
 * ```ts
 * tupleTerm([]);   // => ()
 * ```
 *
 * @see {@link inferTupleType} Tuple type inference
 * @see {@link tupleType} Type-level constructor
 * @see {@link tupleProjectTerm} Accessing tuple elements
 */
export const tupleTerm = (elements: Term[]): Term => ({ tuple: elements });

/**
 * Constructs a **tuple projection** term:
 *
 *     tuple.index
 *
 * This extracts the `index`‑th element (0‑based) from a tuple value.
 * For example:
 *
 *     (1, true, "x").1   ⇒   true
 *
 * The term stores:
 * - `tuple` — the tuple expression being projected
 * - `index` — which element to extract (0 = first)
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * Handled by {@link inferTupleProjectType}:
 *
 * 1. Infer the type of the tuple expression.
 * 2. Normalize it.
 * 3. Ensure it is a `TupleType`:
 *      - otherwise → `not_a_tuple` error.
 * 4. Check that the index is within bounds:
 *      - otherwise → `tuple_index_out_of_bounds`.
 * 5. Return the element type at that position.
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - Selecting fields from tuple values
 * - Working with tuple‑encoded data structures
 * - Recursive ADTs using tuples for payloads
 *
 * ---------------------------------------------------------------------------
 * @param tuple - The tuple term being projected
 * @param index - The 0‑based element index to extract
 * @returns A `TupleProjectTerm` node `{ tuple_project: { tuple, index } }`
 *
 * @example Basic usage:
 * ```ts
 * const tup = tupleTerm([conTerm("1", Int), conTerm("true", Bool)]);
 * tupleProjectTerm(tup, 0);
 * // => ( (1, true) ).0
 * ```
 *
 * @example Out‑of‑bounds (typechecking):
 * ```ts
 * tupleProjectTerm(tupleTerm([x]), 1);
 * // inferTupleProjectType → tuple_index_out_of_bounds error
 * ```
 *
 * @see {@link inferTupleProjectType} Typing rule
 * @see {@link tupleTerm} Tuple value constructor
 * @see {@link tupleType} Type‑level counterpart
 */
export const tupleProjectTerm = (tuple: Term, index: number): Term => ({
  tuple_project: { tuple, index },
});

/**
 * Constructs a **let‑binding** term:
 *
 *     let name = value in body
 *
 * A `LetTerm` introduces a **local variable binding**.
 * The `value` is first typechecked or inferred, then the binding
 * `name : type(value)` is added to the context used for typing `body`.
 *
 * Let‑bindings are **non‑recursive**:
 * - `value` cannot reference `name`
 * - `body` *can* reference `name`
 *
 * ---------------------------------------------------------------------------
 * Type inference
 * ---------------------------------------------------------------------------
 * Handled by {@link inferLetType}:
 *
 * 1. Infer the type of `value`.
 *    This yields a concrete type `T`.
 * 2. Extend the context with `name : T`.
 * 3. Infer the type of `body` in the extended context.
 * 4. The type of the whole expression is the type of `body`.
 *
 * Example:
 * ```ts
 * let x = 42 in x + 1
 * ```
 * becomes:
 * - infer `42 : Int`
 * - extend Γ with `x : Int`
 * - infer `x + 1 : Int`
 * → result: `Int`
 *
 * ---------------------------------------------------------------------------
 * Used in
 * ---------------------------------------------------------------------------
 * - binding intermediate expressions
 * - improving readability and structure of code
 * - carrying local dictionary bindings during trait inference
 *
 * ---------------------------------------------------------------------------
 * @param name - The name introduced by the binding
 * @param value - The expression bound to that name
 * @param body - The expression that can reference `name`
 * @returns A `LetTerm` node
 *
 * @example
 * ```ts
 * letTerm("x", conTerm("42", Int), varTerm("x"));
 * // => let x = 42 in x
 * ```
 *
 * @see {@link inferLetType} Inference rule for let‑bindings
 * @see {@link varTerm} Local variable references
 */
export const letTerm = (name: string, value: Term, body: Term): Term => ({
  let: { name, value, body },
});

/**
 * Constructs a **trait lambda**:
 *
 *     Λtype_var::kind where constraints. body
 *
 * This introduces:
 * - a **type parameter** (`type_var`)
 * - a **dictionary variable** (`trait_var`) giving access to trait methods
 * - a list of **trait constraints** that the type parameter must satisfy
 *
 * Conceptually, it is the term‑level analogue of a **bounded universal type**:
 *
 *     ∀type_var::kind where constraints. body_type
 *
 * but with an **implicit dictionary argument** inside the term.
 *
 * ---------------------------------------------------------------------------
 * Example
 * ---------------------------------------------------------------------------
 * A trait‑polymorphic identity‑like function:
 *
 * ```ts
 * traitLamTerm(
 *   "d",          // dictionary var
 *   "Eq",         // required trait
 *   "Self",       // type param
 *   starKind,     // Self :: *
 *   [{ trait: "Eq", type: varType("Self") }],
 *   lamTerm("x", varType("Self"), varTerm("x"))
 * )
 *
 * // Printed as:
 * //   ΛSelf::* where Eq<Self>. λx:Self. x
 * ```
 *
 * ---------------------------------------------------------------------------
 * How typechecking works
 * ---------------------------------------------------------------------------
 * See {@link inferTraitLamType}, which:
 *
 * 1. Extends the typechecker context with:
 *      - the type parameter (`type_var :: kind`)
 *      - a dictionary variable (`trait_var : Dict<trait, type_var>`)
 * 2. Typechecks the `body` in this extended context
 * 3. Returns a **bounded forall type**:
 *
 *    ∀type_var::kind where constraints. body_type
 *
 * ---------------------------------------------------------------------------
 * Why this form exists
 * ---------------------------------------------------------------------------
 * Trait lambdas allow functions to be generic *and* require trait evidence.
 * They are similar to Haskell’s:
 *
 * ```hs
 * f :: forall a. Eq a => a -> Bool
 * f x = ...
 * ```
 *
 * where `Eq a` corresponds to a trait constraint and the implicit dictionary
 * corresponds to `trait_var`.
 *
 * Trait lambdas form the basis of:
 * - trait‑polymorphic functions
 * - typeclass‑style method dispatch
 * - implicit dictionary passing (via {@link autoInstantiate} and {@link traitAppTerm})
 *
 * ---------------------------------------------------------------------------
 * @param trait_var - The name of the implicit dictionary variable
 * @param trait - The primary trait name associated with the dictionary variable
 * @param type_var - The bound type parameter name
 * @param kind - The kind of the type parameter (usually `*`)
 * @param constraints - Additional trait bounds (e.g. `Eq<Self>`, `Show<Self>`)
 * @param body - The function body that may use both `type_var` and `trait_var`
 *
 * @returns A `TraitLamTerm` node
 *
 * @example With multiple constraints:
 * ```ts
 * traitLamTerm(
 *   "d",
 *   "Ord",
 *   "A",
 *   starKind,
 *   [
 *     { trait: "Ord",  type: varType("A") },
 *     { trait: "Show", type: varType("A") }
 *   ],
 *   body
 * );
 * ```
 *
 * @see {@link inferTraitLamType} Typing rule
 * @see {@link boundedForallType} Type-level representation
 * @see {@link traitAppTerm} Application of a trait lambda
 */
export const traitLamTerm = (
  trait_var: string,
  trait: string,
  type_var: string,
  kind: Kind,
  constraints: TraitConstraint[],
  body: Term,
): Term => ({
  trait_lam: { trait_var, trait, type_var, kind, constraints, body },
});

/**
 * Constructs a **trait application** term:
 *
 *     term [type] with dicts { d₁, d₂, ... }
 *
 * This applies a **trait‑polymorphic** term (a `traitLamTerm`) to:
 * - a **type argument**, and
 * - an explicit list of **dictionary arguments** providing evidence for the
 *   trait constraints required by the trait lambda.
 *
 * Conceptually similar to Haskell's:
 *
 *     f @Int (eqIntDict)
 *
 * but presented explicitly in the AST.
 *
 * ---------------------------------------------------------------------------
 * How it works
 * ---------------------------------------------------------------------------
 * A trait lambda has the form:
 *
 *     ΛSelf::K where C(Self). body
 *
 * To instantiate it, a trait application supplies:
 * - a concrete type `T` (or fresh meta‑variable)
 * - actual dictionary values that satisfy all constraints
 *
 * The typing rule is implemented in {@link inferTraitAppType}:
 *
 * 1. Infer the type of `term`
 * 2. Check that it is a bounded forall:
 *        ∀Self::K where C. τ
 * 3. Check that the provided type argument has kind `K`
 * 4. Substitute `Self := type` in all constraints
 * 5. Verify the number and shape of `dicts` matches the constraints
 * 6. Substitute `Self := type` in the body to produce the result type
 *
 * Errors include:
 * - `wrong_number_of_dicts`
 * - `type_mismatch` (dictionary not matching constraint)
 * - `kind_mismatch`
 * - `missing_trait_impl` (if dictionary inference is attempted elsewhere)
 *
 * ---------------------------------------------------------------------------
 * Example
 * ---------------------------------------------------------------------------
 * Given:
 * ```ts
 * const lam = traitLamTerm(
 *   "d", "Eq", "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   arrowType(varType("Self"), conType("Bool"))
 * );
 * ```
 *
 * Application:
 * ```ts
 * traitAppTerm(lam, conType("Int"), [eqIntDict])
 * ```
 *
 * Represents:
 * ```
 * ΛSelf where Eq<Self>. body   applied to   [Int] with {eqIntDict}
 * ```
 *
 * ---------------------------------------------------------------------------
 * When it is used
 * ---------------------------------------------------------------------------
 * - Explicit trait applications in user code (if exposed)
 * - Automatically inserted by {@link autoInstantiate}
 * - Trait dictionary passing for inference
 * - Handling bounded polymorphism at term level
 *
 * ---------------------------------------------------------------------------
 * @param term - The trait‑polymorphic term being instantiated
 * @param type - The type argument being applied
 * @param dicts - Dictionary terms satisfying the required trait constraints
 * @returns A `TraitAppTerm` node
 *
 * @example
 * ```ts
 * traitAppTerm(varTerm("eqFunctor"), conType("Int"), [dict1, dict2]);
 * ```
 *
 * @see {@link traitLamTerm} Introduction form
 * @see {@link inferTraitAppType} Typing rule
 * @see {@link instantiateWithTraits} Dictionary resolution
 */
export const traitAppTerm = (term: Term, type: Type, dicts: Term[]): Term => ({
  trait_app: { term, type, dicts },
});

/**
 * Constructs a **trait dictionary** term:
 *
 *     dict Trait<Type> { method₁ = impl₁, method₂ = impl₂, ... }
 *
 * A dictionary packages the concrete implementations of all methods required
 * by a trait for a specific type.
 * This is the dictionary‑passing interpretation of typeclasses.
 *
 * Example:
 * ```ts
 * dict Eq<Int> {
 *   eq = λx:Int. λy:Int. ...
 * }
 * ```
 *
 * The dictionary contains:
 * - `trait`   — the trait name (`"Eq"`, `"Show"`, `"Functor"`, ...)
 * - `type`    — the type for which the trait is implemented
 * - `methods` — a list of `[name, term]` pairs giving each method’s implementation
 *
 * ---------------------------------------------------------------------------
 * How dictionaries are used
 * ---------------------------------------------------------------------------
 * Dictionaries serve as **explicit trait evidence** and are used by:
 * - {@link traitMethodTerm} for method projection (`d.eq`)
 * - {@link inferTraitAppType} when fulfilling trait constraints
 * - {@link instantiateWithTraits} during bounded forall instantiation
 * - {@link traitImplBinding} when storing global implementations in the context
 *
 * In other words, dictionaries are *runtime* or *term-level* witnesses that a
 * type satisfies a trait.
 *
 * ---------------------------------------------------------------------------
 * Typechecking dictionaries
 * ---------------------------------------------------------------------------
 * {@link inferDictType} validates that:
 * - the dictionary implements a known trait
 * - all required methods are supplied
 * - each method’s implementation matches the trait’s signature
 * - the type argument has the correct kind
 *
 * Errors include:
 * - `missing_method`
 * - `kind_mismatch`
 * - `type_mismatch` during method checking
 *
 * ---------------------------------------------------------------------------
 * @param trait - The trait name being implemented
 * @param type - The type for which this trait implementation applies
 * @param methods - List of method implementations `[methodName, methodTerm]`
 *
 * @returns A `DictTerm` node `{ dict: { trait, type, methods } }`
 *
 * @example
 * ```ts
 * dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", Int,
 *            lamTerm("y", Int,
 *              conTerm("true", Bool)
 *            ))]
 * ]);
 * ```
 *
 * @see {@link inferDictType} Dictionary typing rule
 * @see {@link traitMethodTerm} Accessing methods in a dictionary
 * @see {@link checkTraitImplementation} Resolving trait constraints
 */
export const dictTerm = (
  trait: string,
  type: Type,
  methods: [string, Term][],
): DictTerm => ({
  dict: { trait, type, methods },
});

/**
 * Constructs a **trait method access** term:
 *
 *     dict.method
 *
 * This extracts a method implementation from a **trait dictionary**.
 * It is the term‑level mechanism for calling trait‑based operations.
 *
 * Example:
 * ```ts
 * eqDict.eq     // access the 'eq' method of an Eq<T> dictionary
 * showDict.show // access the 'show' method of a Show<T> dictionary
 * ```
 *
 * ---------------------------------------------------------------------------
 * What it represents
 * ---------------------------------------------------------------------------
 * A `traitMethodTerm` is a projection on a dictionary term.
 * The dictionary may come from:
 * - a local dictionary binding inside a trait lambda (`traitLamTerm`)
 * - a dictionary supplied in a trait application (`traitAppTerm`)
 * - a global implementation (`traitImplBinding`)
 *
 * The typechecker uses the dictionary’s trait and type information to determine
 * which method is being accessed and what its resulting type is.
 *
 * ---------------------------------------------------------------------------
 * How it is typed
 * ---------------------------------------------------------------------------
 * {@link inferTraitMethodType} performs the typing:
 *
 * 1. Infer the type of the dictionary expression.
 * 2. Ensure it is a dictionary type (either a `dictTerm` or a dict binding).
 * 3. Look up the trait definition (`TraitDef`).
 * 4. Verify that the requested method exists in the trait.
 * 5. Substitute the dictionary’s type argument into the method’s type.
 *
 * Errors include:
 * - `unbound` (dictionary variable not found)
 * - `missing_method` (method not defined by the trait)
 * - type mismatches inside the dictionary body
 *
 * ---------------------------------------------------------------------------
 * When it is used
 * ---------------------------------------------------------------------------
 * - Calling trait methods explicitly
 * - Implementing typeclass dispatch (dictionary‑passing)
 * - Building method bodies in user-defined dictionaries
 * - Typechecking trait‑polymorphic code
 *
 * ---------------------------------------------------------------------------
 * @param dict - A term that evaluates to a trait dictionary
 * @param method - The method name to extract (e.g. `"eq"`, `"map"`)
 * @returns A `TraitMethodTerm` node
 *
 * @example
 * ```ts
 * const eqInt = dictTerm("Eq", Int, [
 *   ["eq", lamTerm("x", Int, lamTerm("y", Int, conTerm("true", Bool)))]
 * ]);
 *
 * traitMethodTerm(eqInt, "eq");
 * // => eqInt.eq
 * ```
 *
 * @example Using a dictionary variable inside a trait lambda:
 * ```ts
 * // Inside ΛSelf where Eq<Self>. body:
 * traitMethodTerm(varTerm("d"), "eq");   // d.eq
 * ```
 *
 * @see {@link inferTraitMethodType} Typing rule
 * @see {@link dictTerm} Dictionary construction
 * @see {@link traitLamTerm} Dictionary binding introduction
 */
export const traitMethodTerm = (dict: Term, method: string): Term => ({
  trait_method: { dict, method },
});

/**
 * Constructs a **variable pattern**:
 *
 *     x
 *
 * A variable pattern matches **any value** and binds it to the given name.
 *
 * Example in a match expression:
 * ```ts
 * match xs {
 *   x => ...   // x binds the entire scrutinee
 * }
 * ```
 *
 * During pattern checking:
 * - {@link checkPattern} assigns the **scrutinee’s type** to this variable
 * - The binding is added to the typing context for the pattern’s body
 *
 * Variable patterns are the pattern‑level analogue of term variables
 * (`varTerm("x")`).
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - Capture the entire value of a match branch:
 *   ```ts
 *   Some(x) => x
 *   ```
 *
 * - As a “catch‑all with binding,” unlike `_` which discards the value
 *
 * - Useful in:
 *   - match expressions
 *   - tuple patterns
 *   - record patterns
 *   - variant patterns
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * - Patterns do not determine types themselves.
 * - The scrutinee type is assigned during `checkPattern`.
 * - The result is a binding:
 *   ```ts
 *   { term: { name: patternName, type: scrutineeType } }
 *   ```
 *
 * ---------------------------------------------------------------------------
 * @param name - The variable name to bind (e.g. `"x"`)
 * @returns A `VarPattern` node `{ var: name }`
 *
 * ---------------------------------------------------------------------------
 * @example
 * ```ts
 * varPattern("x");     // matches anything, binds it to x
 * ```
 *
 * @example In a tuple:
 * ```ts
 * tuplePattern([varPattern("a"), varPattern("b")])
 * // matches (a, b)
 * ```
 *
 * @see {@link checkPattern} Determines the type of the bound variable
 * @see {@link wildcardPattern} Pattern that ignores the value
 */
export const varPattern = (name: string): Pattern => ({ var: name });

/**
 * Constructs a **wildcard pattern**:
 *
 *     _
 *
 * A wildcard pattern matches **any value** but does **not** bind a variable.
 *
 * It is useful when:
 * - You want to ignore part (or all) of a value
 * - You don’t need the matched value in the branch body
 * - Serving as a “catch‑all” case in pattern matching
 *
 * In a match expression:
 * ```ts
 * match xs {
 *   _ => 0      // matches everything
 * }
 * ```
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * - Wildcards never introduce bindings.
 * - {@link checkPattern} always accepts them.
 * - They immediately make a match expression **exhaustive** in
 *   {@link checkExhaustive}, since `_` covers all possible cases.
 *
 * ---------------------------------------------------------------------------
 * @returns A `WildcardPattern` node `{ wildcard: null }`
 *
 * @example
 * ```ts
 * wildcardPattern();  // => _
 * ```
 *
 * @see {@link varPattern} Binds a value instead of ignoring it
 * @see {@link checkPattern} Pattern validation
 * @see {@link checkExhaustive} Coverage checking (wildcards always exhaustive)
 */
export const wildcardPattern = (): Pattern => ({ wildcard: null });

/**
 * Constructs a **constructor (constant) pattern**:
 *
 *     SomeConst
 *
 * This pattern matches **only one exact constructor or literal value**.
 *
 * Examples:
 * - `true`
 * - `false`
 * - `None`
 * - `"Zero"`
 *
 * A constructor pattern contains:
 * - `name` — the literal or constructor label
 * - `type` — the expected type of that constructor
 *
 * The type annotation is needed so that pattern checking can verify that this
 * constructor is compatible with the scrutinee’s type.
 *
 * ---------------------------------------------------------------------------
 * How it is used
 * ---------------------------------------------------------------------------
 * Constructor patterns are used in:
 * - variant cases with **no payload**
 *   (e.g. `None`, `Nil`)
 * - literal matching
 *   (e.g. `true`, `"hello"`)
 * - simple pattern matches that don’t bind variables
 *
 * Example:
 * ```ts
 * match b {
 *   true  => 1
 *   false => 0
 * }
 * ```
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * {@link checkPattern} verifies:
 * - the scrutinee type matches the expected type provided here
 * - the constructor name is valid for that type (e.g., `true : Bool`)
 *
 * If the scrutinee type is incompatible, a `type_mismatch` error is produced.
 *
 * This pattern **never binds variables**.
 *
 * ---------------------------------------------------------------------------
 * @param name - Constructor or literal name to match
 * @param type - The expected type of that constructor/literal
 *
 * @returns A `ConPattern` node
 *
 * @example
 * ```ts
 * conPattern("None", appType(conType("Option"), Int));
 * ```
 *
 * @example Boolean:
 * ```ts
 * conPattern("true", conType("Bool"));
 * ```
 *
 * @see {@link checkPattern} Validates constructor compatibility
 * @see {@link variantPattern} For constructors with payloads
 */
export const conPattern = (name: string, type: Type): Pattern => ({
  con: { name, type },
});

/**
 * Constructs a **record pattern**:
 *
 *     { label₁: p₁, label₂: p₂, ... }
 *
 * A record pattern matches a **record value** field‑by‑field.
 * Each field pairs a **label** with a **subpattern** that must match the
 * corresponding field in the scrutinee.
 *
 * Examples:
 * ```ts
 * { x: a, y: b }
 * { point: (x, y) }
 * ```
 *
 * ---------------------------------------------------------------------------
 * How it behaves
 * ---------------------------------------------------------------------------
 * - The pattern must contain **exactly the same labels** as the scrutinee’s
 *   record type (order does not matter).
 * - For each field:
 *   - {@link checkRecordPattern} validates label presence and type
 *   - subpatterns are recursively checked with the field’s type
 * - All variable bindings from subpatterns are collected and returned.
 *
 * This is the pattern‑level analogue of destructuring a record.
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - Matching structured data from records:
 *   ```ts
 *   match rec {
 *     { x: a, y: b } => ...
 *   }
 *   ```
 *
 * - Nested patterns:
 *   ```ts
 *   { pos: (x, y), color: c }
 *   ```
 *
 * - Extracting only certain fields:
 *   (subpatterns may include `_`)
 *   ```ts
 *   { x: x, y: _ }
 *   ```
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * - The scrutinee must be a `RecordType` (`{ label: Type, ... }`).
 * - Missing or extra labels produce `missing_field` or `type_mismatch`.
 * - Field types must be well‑kinded (`*`).
 *
 * {@link checkPattern} delegates record patterns to
 * {@link checkRecordPattern}, which:
 * - verifies label sets match
 * - recursively checks each corresponding subpattern
 * - aggregates all variable bindings
 *
 * ---------------------------------------------------------------------------
 * @param fields - An array of `[label, subpattern]` field patterns
 * @returns A `RecordPattern` node
 *
 * @example
 * ```ts
 * recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", varPattern("b")]
 * ]);
 * // matches { x = ?, y = ? }
 * ```
 *
 * @example Nested:
 * ```ts
 * recordPattern([
 *   ["pos", tuplePattern([varPattern("x"), varPattern("y")])]
 * ]);
 * ```
 *
 * @see {@link checkRecordPattern} Typechecking rule for record patterns
 * @see {@link recordType} Type-level record
 * @see {@link checkPattern} Dispatcher for all patterns
 */
export const recordPattern = (fields: [string, Pattern][]): Pattern => ({
  record: fields,
});

/**
 * Constructs a **variant pattern**:
 *
 *     Label(p)
 *
 * This pattern matches a specific **constructor case** of a variant or enum,
 * and then recursively matches its **payload** using the inner pattern.
 *
 * Examples:
 * ```ts
 * Some(x)
 * Left(v)
 * Cons(hd, tl)
 * ```
 *
 * ---------------------------------------------------------------------------
 * Structure
 * ---------------------------------------------------------------------------
 * - `label`   — variant constructor name (`"Some"`, `"None"`, `"Cons"`, …)
 * - `pattern` — a subpattern for the constructor’s payload
 *
 * For zero‑payload constructors (e.g. `None`, `Nil`), the payload pattern is
 * usually a `tuplePattern([])` or a wildcard/variable.
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * {@link checkPattern} handles variant patterns with several cases:
 *
 * 1. **Scrutinee is a `μ`‑type**
 *    Unfold one layer, then retry.
 *
 * 2. **Scrutinee is a meta‑variable (`?N`)**
 *    Infer the enum/variant type by searching for a definition containing
 *    the specified label, unify `?N` with that enum, then retry.
 *
 * 3. **Scrutinee is a structural variant (`variantType`)**
 *    Ensure the label exists; recursively check its payload type.
 *
 * 4. **Scrutinee is a nominal enum (`conType` or applied enum)**
 *    Look up the enum definition, check arity, substitute type parameters,
 *    locate the labeled case, and recursively check the payload.
 *
 * Errors include:
 * - `invalid_variant_label` (label not found)
 * - `not_a_variant` (scrutinee is not a variant/enum)
 * - `kind_mismatch` (incorrect number of type arguments for the enum)
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - Pattern matching on ADTs and enum cases
 * - Matching structural variants
 * - Deconstructing recursive types such as lists or trees
 *
 * ---------------------------------------------------------------------------
 * @param label - Constructor name to match
 * @param pattern - Pattern for the constructor’s payload
 * @returns A `VariantPattern` node
 *
 * ---------------------------------------------------------------------------
 * @example
 * ```ts
 * variantPattern("Some", varPattern("x"));
 * // matches Some(x)
 * ```
 *
 * @example Recursive:
 * ```ts
 * variantPattern("Cons",
 *   tuplePattern([varPattern("hd"), varPattern("tl")])
 * );
 * ```
 *
 * @see {@link checkPattern} Full pattern checking logic
 * @see {@link variantType} Structural variant representation
 * @see {@link normalizeType} Enum expansion
 */
export const variantPattern = (label: string, pattern: Pattern): Pattern => ({
  variant: { label, pattern },
});

/**
 * Constructs a **tuple pattern**:
 *
 *     (p₁, p₂, ..., pₙ)
 *
 * A tuple pattern matches a **tuple value** of the same arity.
 * Each element pattern is matched position‑by‑position against the corresponding
 * element of the scrutinee.
 *
 * Examples:
 * ```ts
 * (x, y)
 * (hd, tl)
 * (a, (b, c))
 * ()
 * ```
 *
 * ---------------------------------------------------------------------------
 * Type behavior
 * ---------------------------------------------------------------------------
 * {@link checkTuplePattern} performs the typechecking:
 *
 * - The scrutinee must have a tuple type (`TupleType`).
 * - The number of elements must match exactly (arity check).
 * - Each subpattern is checked recursively against the corresponding element type.
 * - All variable bindings from subpatterns are collected.
 *
 * Errors include:
 * - `not_a_tuple` when the scrutinee isn’t a tuple type
 * - `type_mismatch` for arity mismatches
 * - errors from recursive pattern checks (invalid labels, wrong type, etc.)
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - Pattern matching on tuple‑encoded data
 * - Deconstructing multi‑argument constructor payloads
 * - Matching recursive ADTs where payloads are tuples (e.g., list cons cells)
 *
 * ---------------------------------------------------------------------------
 * @param elements - A list of subpatterns corresponding to tuple positions
 * @returns A `TuplePattern` node
 *
 * ---------------------------------------------------------------------------
 * @example
 * ```ts
 * tuplePattern([varPattern("x"), varPattern("y")]);
 * // matches (x, y)
 * ```
 *
 * @example Empty tuple (unit):
 * ```ts
 * tuplePattern([]);
 * // matches ()
 * ```
 *
 * @see {@link checkTuplePattern} Typechecking rule
 * @see {@link tupleType} Tuple type constructor
 * @see {@link checkPattern} Pattern dispatcher
 */
export const tuplePattern = (elements: Pattern[]): Pattern => ({
  tuple: elements,
});

/**
 * The **unit type**:
 *
 *     ()
 *
 * Represented internally as an empty tuple (`{ tuple: [] }`), this type has
 * exactly **one value**, also written `()`.
 * It is the tuple type of arity zero.
 *
 * The unit type is useful for:
 * - constructors with no payload (e.g., `None`, `Nil`)
 * - functions that conceptually return “no meaningful value”
 * - representing zero-field records
 * - pattern matching where “nothing” is expected
 *
 * Kind:
 * - Always has kind `*`
 *
 * Used in:
 * - tuple patterns (`tuplePattern([])`)
 * - variant payloads (zero-argument cases)
 * - fold/unfold of recursive types that use unit
 *
 * @example
 * ```ts
 * unitType;        // ()
 * tupleType([]);   // same representation
 * ```
 */
export const unitType: Type = { tuple: [] };

/**
 * The **unit value**:
 *
 *     ()
 *
 * Represented as an empty tuple term (`{ tuple: [] }`), this is the *only*
 * value inhabiting the unit type {@link unitType}.
 *
 * The unit value is useful for:
 * - variant constructors with no payload (e.g., `<None=()>`)
 * - record or tuple destructuring when no information is carried
 * - serving as a placeholder in recursive or structural types
 * - representing “no meaningful value” in functional code
 *
 * Type inference:
 * - {@link inferTupleType} infers its type as `unitType`
 *
 * @example
 * ```ts
 * unitValue;        // ()
 * tupleTerm([]);    // same representation
 * ```
 */
export const unitValue: Term = { tuple: [] };

/**
 * Constructs a **term binding** for the typing context (`Γ`):
 *
 *     name : type
 *
 * A `termBinding` represents a variable in scope with an associated type.
 * These bindings are stored in the context and used during type inference
 * whenever a variable (`varTerm`) is looked up.
 *
 * Examples of where term bindings are introduced:
 * - lambda parameters (`λx:τ. body` adds `x : τ`)
 * - let‑bindings (`let x = value in body` adds `x : type(value)`)
 * - global or top‑level definitions
 * - dictionary variables introduced by trait lambdas
 *
 * `inferVarType` uses these bindings to determine the type of a variable term.
 *
 * ---------------------------------------------------------------------------
 * @param name - The variable name being added to the context
 * @param type - The type assigned to that variable
 *
 * @returns A `TermBinding` node suitable for insertion into `state.ctx`
 *
 * @example
 * ```ts
 * termBinding("x", conType("Int"));
 * // => { term: { name: "x", type: Int } }
 * ```
 *
 * @see {@link inferVarType} Looks up term bindings
 * @see {@link checkPattern} Introduces bindings from patterns
 * @see {@link letTerm} Local variable introduction
 * @see {@link TraitLamTerm} Introduces dictionary term bindings
 */
export const termBinding = (name: string, type: Type) => ({
  term: { name, type },
});

/**
 * Constructs a **type binding** for the typing context (`Γ`):
 *
 *     name :: kind
 *
 * A `typeBinding` records the kind of a **type constructor** or
 * **type variable** currently in scope.
 * These bindings appear in the context and are used during kind checking.
 *
 * Type bindings are introduced when:
 * - declaring built‑in or user‑defined types (`addType`)
 * - introducing type variables in polymorphic types (`∀A::κ. ...`)
 * - introducing parameters in type‑level lambdas (`λA::κ. ...`)
 * - handling bounded foralls in trait lambdas (`ΛSelf::* where ...`)
 *
 * Kind checking (`checkKind`) uses type bindings to ensure:
 * - constructors receive the correct number of type arguments
 * - type applications (`F<T>`) are well‑kinded
 * - type variables have valid kinds
 *
 * ---------------------------------------------------------------------------
 * @param name - The type constructor or type variable name
 * @param kind - Its kind (`*`, `* → *`, `(* → *) → *`, ...)
 *
 * @returns A `TypeBinding` node suitable for insertion into `state.ctx`
 *
 * ---------------------------------------------------------------------------
 * @example Declaring a type constructor:
 * ```ts
 * typeBinding("List", arrowKind(starKind, starKind));
 * // => List :: * → *
 * ```
 *
 * @example Binding a polymorphic type variable:
 * ```ts
 * typeBinding("A", starKind);
 * // => A :: *
 * ```
 *
 * @see {@link checkKind} Kind inference and validation
 * @see {@link addType} Adds type constructors to the context
 * @see {@link lamType} Type-level lambdas introduce type bindings
 * @see {@link forallType} Universal quantifiers introduce type bindings
 */
export const typeBinding = (name: string, kind: Kind) => ({
  type: { name, kind },
});

/**
 * Constructs a **type alias binding** for the typing context (`Γ`):
 *
 *     type Name<A₁::K₁, A₂::K₂, ...> = Body
 *
 * A type alias gives a *name* to a type expression.
 * It is **purely syntactic** — it does **not** introduce a new nominal type.
 * Instead, aliases are expanded during normalization (`normalizeType`).
 *
 * Example:
 * ```ts
 * type Pair<A,B> = (A, B)
 * ```
 *
 * ---------------------------------------------------------------------------
 * Structure
 * ---------------------------------------------------------------------------
 * - `name`   — the alias name (e.g., `"Id"`, `"Pair"`)
 * - `params` — type parameter names (`["A"]`, `["A","B"]`, …)
 * - `kinds`  — the corresponding parameter kinds (`*`, `*→*`, …)
 * - `body`   — the type expression defining the alias
 *
 * A `typeAliasBinding` is stored in the context, allowing:
 * - kind checking to validate alias usage (`checkConKind`)
 * - alias expansion when the alias name appears at the head of a type application
 *
 * ---------------------------------------------------------------------------
 * How aliases behave
 * ---------------------------------------------------------------------------
 * Given:
 * ```ts
 * type Id<A> = A
 * ```
 *
 * The type:
 * ```ts
 * Id<Int>
 * ```
 * expands to:
 * ```ts
 * Int
 * ```
 *
 * Expansion occurs in {@link normalizeType}, *not* immediately.
 *
 * Aliases support higher‑kinded parameters as well:
 * ```ts
 * type Const<F::(* → *), X> = F<Int>
 * ```
 *
 * ---------------------------------------------------------------------------
 * Kind behavior
 * ---------------------------------------------------------------------------
 * Aliases have kinds derived from their parameters:
 *
 * ```ts
 * type Id<A::*> = A
 * // Id :: * → *
 * ```
 *
 * Kind checking:
 * - validates that parameters are used correctly inside `body`
 * - verifies that alias applications supply the correct number of arguments
 *
 * ---------------------------------------------------------------------------
 * @param name - The alias name
 * @param params - Names of type parameters
 * @param kinds - Kinds corresponding to each parameter
 * @param body - The type expression defining the alias
 *
 * @returns A `TypeAliasBinding` node for insertion into `state.ctx`
 *
 * ---------------------------------------------------------------------------
 * @example Simple alias:
 * ```ts
 * typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * // type Id<A> = A
 * ```
 *
 * @example Multi‑parameter alias:
 * ```ts
 * typeAliasBinding(
 *   "Pair",
 *   ["A", "B"],
 *   [starKind, starKind],
 *   tupleType([varType("A"), varType("B")])
 * );
 * // type Pair<A,B> = (A, B)
 * ```
 *
 * @see {@link normalizeType} Expands aliases
 * @see {@link checkConKind} Kind checking for constructors and aliases
 * @see {@link typeBinding} Non‑alias type bindings
 */
export const typeAliasBinding = (
  name: string,
  params: string[],
  kinds: Kind[],
  body: Type,
) => ({
  type_alias: { name, params, kinds, body },
});

/**
 * Constructs a **trait definition binding** for the typing context (`Γ`).
 *
 * A trait definition describes:
 * - the **trait name** (e.g. `"Eq"`, `"Show"`)
 * - the **type parameter** it abstracts over (e.g. `"Self"`, `"A"`)
 * - the **kind** of that type parameter (`*`, `* → *`, …)
 * - the list of **method signatures** required by the trait
 *
 * For example, the trait:
 * ```ts
 * trait Eq<Self :: *> {
 *   eq : Self → Self → Bool
 * }
 * ```
 * is represented as:
 * ```ts
 * traitDefBinding("Eq", "Self", starKind, [
 *   ["eq", arrowType(Self, arrowType(Self, Bool))]
 * ]);
 * ```
 *
 * ---------------------------------------------------------------------------
 * Why this binding exists
 * ---------------------------------------------------------------------------
 * When added to the context, a `TraitDefBinding`:
 * - declares a **new trait**
 * - provides method signatures used by:
 *   - {@link inferTraitMethodType} (dictionary method lookup)
 *   - {@link inferDictType} (dictionary validation)
 *   - {@link checkTraitImplementation} (instance resolution)
 *   - {@link traitLamTerm} and {@link traitAppTerm}
 * - serves as the authoritative specification for all dictionaries implementing
 *   the trait
 *
 * ---------------------------------------------------------------------------
 * Structure
 * ---------------------------------------------------------------------------
 * - `name`       — The name of the trait (`"Eq"`)
 * - `type_param` — The trait’s type parameter (`"Self"`)
 * - `kind`       — Kind of the parameter (`*`, `* → *`, …)
 * - `methods`    — List of `[methodName, methodType]` pairs
 *
 * The method types may reference the trait’s type parameter.
 *
 * ---------------------------------------------------------------------------
 * @param name - Trait name
 * @param type_param - Name of the trait’s type parameter
 * @param kind - Kind of the type parameter
 * @param methods - List of method signatures `[string, Type]`
 *
 * @returns A `TraitDefBinding` node for insertion into `state.ctx`
 *
 * ---------------------------------------------------------------------------
 * @example Defining the `Eq` trait:
 * ```ts
 * traitDefBinding("Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), arrowType(varType("A"), conType("Bool")))]
 * ]);
 * ```
 *
 * @example Higher‑kinded trait:
 * ```ts
 * traitDefBinding("Functor", "F",
 *   arrowKind(starKind, starKind),
 *   [["map", ...]]
 * );
 * ```
 *
 * @see {@link checkTraitImplementation} Resolving trait instances
 * @see {@link dictTerm} Concrete dictionary construction
 * @see {@link traitMethodTerm} Using trait methods
 * @see {@link inferDictType} Dictionary validation
 */
export const traitDefBinding = (
  name: string,
  type_param: string,
  kind: Kind,
  methods: [string, Type][],
) => ({
  trait_def: {
    name,
    type_param,
    kind,
    methods,
  },
});

/**
 * Constructs a **trait implementation binding** for the typing context (`Γ`):
 *
 *     impl Trait for Type = dict
 *
 * This declares that a specific **type** implements a specific **trait**, and
 * provides the corresponding **dictionary** (`dict`) containing all method
 * implementations for that trait and type.
 *
 * Example:
 * ```ts
 * traitImplBinding("Eq", conType("Int"), eqIntDict);
 * // Represents: impl Eq<Int> = dict Eq<Int> { eq = ... }
 * ```
 *
 * ---------------------------------------------------------------------------
 * What this binding means
 * ---------------------------------------------------------------------------
 * A `trait_impl` binding registers a **global instance** of a trait:
 *
 * - `trait` — the trait name (e.g., `"Eq"`)
 * - `type`  — the type for which the trait is implemented
 * - `dict`  — a concrete dictionary giving method implementations
 *
 * These bindings are consulted whenever the typechecker needs **trait evidence**
 * during:
 * - trait application (`traitAppTerm`)
 * - bounded polymorphism instantiation (`instantiateWithTraits`)
 * - dictionary lookup (`checkTraitImplementation`)
 *
 * In effect, this is the typeclass instance table for the language.
 *
 * ---------------------------------------------------------------------------
 * How it is used
 * ---------------------------------------------------------------------------
 *
 * 1. **Trait constraint solving**
 *    {@link checkTraitImplementation} scans the context for `trait_impl`
 *    bindings to resolve constraints:
 *
 *    ```
 *    Eq<Int>  →  find impl Eq for Int
 *    ```
 *
 * 2. **Polymorphic trait implementations**
 *    A trait implementation may itself involve `forall` or type‑lambdas,
 *    enabling:
 *
 *    ```ts
 *    impl Functor<List> { ... }
 *    impl Eq<List<T>>   { ... }
 *    ```
 *
 *    The unification logic determines whether a polymorphic implementation
 *    matches the required constraint.
 *
 * 3. **Dictionary method access**
 *    {@link traitMethodTerm} extracts method implementations from the dictionary
 *    stored here.
 *
 * ---------------------------------------------------------------------------
 * Errors avoided by this binding
 * ---------------------------------------------------------------------------
 * - Prevents duplicate trait instances (checked elsewhere during `addTraitImpl`)
 * - Allows precise error reporting when a required trait has **no**
 *   implementation (`missing_trait_impl`)
 *
 * ---------------------------------------------------------------------------
 * @param trait - The trait name implemented (e.g. `"Eq"`)
 * @param type - The type for which the instance is defined
 * @param dict - The dictionary term providing method implementations
 *
 * @returns A `TraitImplBinding` suitable for insertion into `state.ctx`
 *
 * ---------------------------------------------------------------------------
 * @example Registering an implementation:
 * ```ts
 * const eqInt = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", Int, lamTerm("y", Int, conTerm("true", Bool)))]
 * ]);
 *
 * traitImplBinding("Eq", conType("Int"), eqInt);
 * ```
 *
 * @see {@link traitDefBinding} Declares traits
 * @see {@link dictTerm} Dictionary construction
 * @see {@link checkTraitImplementation} Resolves trait instances
 * @see {@link instantiateWithTraits} Instantiates bounded foralls
 */
export const traitImplBinding = (trait: string, type: Type, dict: Term) => ({
  trait_impl: { trait, type, dict },
});

/**
 * Constructs a **dictionary binding** for the typing context (`Γ`).
 *
 * A dictionary binding introduces a **local dictionary variable** that provides
 * evidence that a particular type implements a particular trait:
 *
 *     name : Dict<trait, type>
 *
 * These bindings occur in *local scopes*, such as:
 * - inside a `traitLamTerm` (trait lambda)
 * - inside explicit trait applications
 * - when passing dictionaries manually
 *
 * They are **not** global trait instances — those are stored using
 * {@link traitImplBinding}. Instead, a `dictBinding` behaves like a
 * term‑level variable that carries trait evidence.
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * When typechecking trait‑bounded functions:
 *
 * ```ts
 * ΛSelf where Eq<Self>. body
 * ```
 *
 * the typechecker introduces a binding:
 *
 *     dictVar : Dict<Eq, Self>
 *
 * inside the body’s context. This allows:
 * - accessing trait methods via {@link traitMethodTerm} (e.g. `d.eq`)
 * - passing the dictionary to nested trait‑polymorphic calls
 *
 * Likewise, explicit dictionary arguments in `traitAppTerm` also introduce
 * these bindings when checking branch bodies.
 *
 * ---------------------------------------------------------------------------
 * Structure
 * ---------------------------------------------------------------------------
 * - `name`  — local dictionary variable name (e.g. `"d"`, `"eqSelf"`)
 * - `trait` — the trait this dictionary provides evidence for
 * - `type`  — the type for which the evidence applies
 *
 * During typechecking, the dictionary’s *actual* implementation is carried by
 * the term itself (usually as a `dictTerm`).
 * This binding only records the *type of the dictionary*.
 *
 * ---------------------------------------------------------------------------
 * @param name - The name of the dictionary variable
 * @param trait - The trait being implemented
 * @param type - The concrete type the trait applies to
 *
 * @returns A `DictBinding` node added to the context
 *
 * ---------------------------------------------------------------------------
 * @example Inside a trait lambda:
 * ```ts
 * // ΛSelf where Eq<Self>. body
 * dictBinding("d", "Eq", varType("Self"));
 * // => d : Dict<Eq, Self>
 * ```
 *
 * @example Used with trait application:
 * ```ts
 * const app = traitAppTerm(f, Int, [eqIntDict]);
 * // internally introduces: eqInt : Dict<Eq, Int>
 * ```
 *
 * @see {@link traitLamTerm} Introduces dictionary bindings implicitly
 * @see {@link traitMethodTerm} Accessing trait methods from a dict variable
 * @see {@link traitImplBinding} Global (non-local) trait implementations
 */
export const dictBinding = (name: string, trait: string, type: Type) => ({
  dict: { name, trait, type },
});

/**
 * Constructs an **enum (algebraic data type) definition binding** for the
 * typing context (`Γ`).
 *
 * An enum definition introduces a **nominal sum type** with:
 * - a name         (`"Option"`, `"Either"`, `"List"`)
 * - a kind         (`* → *`, `* → (* → *)`, …)
 * - type parameters (`["T"]`, `["A","B"]`)
 * - a list of **variants** (constructors), each with a payload type scheme
 * - an optional `recursive` flag for mutually or self‑referential definitions
 *
 * Example:
 * ```ts
 * enum Option<T :: *> {
 *   None : ()
 *   Some : T
 * }
 *
 * // Binding:
 * enumDefBinding(
 *   "Option",
 *   arrowKind(starKind, starKind),
 *   ["T"],
 *   [
 *     ["None", tupleType([])],
 *     ["Some", varType("T")]
 *   ],
 *   false
 * )
 * ```
 *
 * ---------------------------------------------------------------------------
 * Role of enum bindings
 * ---------------------------------------------------------------------------
 * Enum definitions are used by:
 * - **Normalization** (`normalizeType`)
 *   to expand nominal enums into structural variants:
 *   ```
 *   Option<Int>  ⇒  <None: () | Some: Int>
 *   ```
 *
 * - **Pattern checking** (`checkPattern`)
 *   to validate variant labels during:
 *   ```
 *   Some(x)
 *   ```
 *
 * - **Exhaustiveness checking** (`checkExhaustive`)
 *   to determine which constructors exist.
 *
 * - **Variant injection** (`inferInjectType`)
 *   to verify payload types for constructors.
 *
 * - **Trait implementations**
 *   to unify polymorphic instance heads against enum applications.
 *
 * ---------------------------------------------------------------------------
 * Parameters
 * ---------------------------------------------------------------------------
 * - `name` — name of the enum (e.g. `"Option"`)
 * - `kind` — the kind of the type constructor (e.g. `* → *`)
 * - `params` — list of type parameter names
 * - `variants` — list of `[label, FieldScheme]` pairs describing constructors:
 *     ```
 *     ["Some", varType("T")]
 *     ["Cons", tupleType([T, List<T>])]
 *     ```
 * - `recursive` — whether the enum may reference itself (affects normalization)
 *
 * ---------------------------------------------------------------------------
 * Recursive enums
 * ---------------------------------------------------------------------------
 * If `recursive = true`, normalization produces a `μ`‑type:
 *
 * ```ts
 * List<T> =
 *   Nil  : ()
 *   Cons : (T, List<T>)
 *
 * normalize(List<Int>)
 *   ⇒ μX. <Nil: () | Cons: (Int, X)>
 * ```
 *
 * ---------------------------------------------------------------------------
 * @returns An `EnumDefBinding` node placed in the context
 *
 * ---------------------------------------------------------------------------
 * @example Simple enum:
 * ```ts
 * enumDefBinding(
 *   "Bool",
 *   starKind,
 *   [],
 *   [
 *     ["true",  tupleType([])],
 *     ["false", tupleType([])]
 *   ]
 * );
 * ```
 *
 * @example Recursive enum:
 * ```ts
 * enumDefBinding(
 *   "List",
 *   arrowKind(starKind, starKind),
 *   ["T"],
 *   [
 *     ["Nil",  tupleType([])],
 *     ["Cons", tupleType([varType("T"), appType(conType("List"), varType("T"))])]
 *   ],
 *   true
 * );
 * ```
 *
 * @see {@link normalizeType} Expands enums to structural variants
 * @see {@link checkPattern} Validates variant labels
 * @see {@link checkExhaustive} Exhaustiveness analysis
 * @see {@link inferInjectType} Variant injection typing
 */
export const enumDefBinding = (
  name: string,
  kind: Kind,
  params: string[],
  variants: [string, FieldScheme][],
  recursive: boolean = false,
) => ({
  enum: { name, kind, params, variants, recursive },
});

/**
 * Renames **type‑level identifiers** inside a type according to a provided
 * rename map.
 *
 * This is used during **module imports**, **aliasing**, and **name rewriting**
 * to avoid collisions and apply import‑side renaming rules.
 *
 * The renaming map `ren` can include:
 * - type constructor names   (`List → MyList`)
 * - type variable names      (`A → X`)
 * - variant / record labels  (`Left → L`, `x → xCoord`)
 *   (labels are handled by callers; this function renames only type-level names)
 *
 * ---------------------------------------------------------------------------
 * What gets renamed?
 * ---------------------------------------------------------------------------
 * - **Type constructors** (`ConType`)
 * - **Free type variables** (`VarType`) that are *not* bound by a quantifier
 * - Names inside:
 *   - type applications
 *   - records
 *   - variants
 *   - tuples
 *   - `forall`, `bounded_forall`, `lam`, and `mu` *bodies* (but not their binders)
 *
 * ---------------------------------------------------------------------------
 * Binder safety
 * ---------------------------------------------------------------------------
 * The `bound` set tracks **type variables introduced by binders**:
 * - `∀A::κ. ...`
 * - `λA::κ. ...`
 * - `μA. ...`
 *
 * These should **not** be renamed, because renaming them would break scoping
 * or change the meaning of the type.
 *
 * For example:
 * ```ts
 * // renaming A → X
 * ∀A. A → B
 * // A is bound → remains A
 * // B may be renamed
 * ```
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * Module imports often allow renaming:
 * - type constructors (`MyModule.List → MList`)
 * - parameters of aliases
 * - type names referenced inside terms and patterns
 *
 * `renameType` ensures types remain consistent and binder‑safe while applying
 * such renamings.
 *
 * It is used by:
 * - `renameBinding`
 * - `renameTerm`
 * - `renamePattern`
 * - `importModule`
 *
 * ---------------------------------------------------------------------------
 * Algorithm overview
 * ---------------------------------------------------------------------------
 * 1. Recursively walk the structure of `ty`
 * 2. When encountering a *free* type variable or constructor:
 *    - If it appears in `ren`, rename it
 * 3. When encountering a binder (`∀`, `λ`, `μ`):
 *    - Add its variable to `bound`
 *    - Recurse into its body without renaming the binder
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state (used for normalization context)
 * @param ty - The type to rename
 * @param ren - A map of `oldName → newName` renamings
 * @param bound - Set of type variables currently bound (internal use)
 *
 * @returns A new type with all eligible names renamed, respecting binders
 *
 * ---------------------------------------------------------------------------
 * @example Rename a type constructor:
 * ```ts
 * renameType(state, conType("List"), new Map([["List", "Vec"]]));
 * // => Vec
 * ```
 *
 * @example Rename free vars but not bound ones:
 * ```ts
 * renameType(
 *   state,
 *   forallType("A", starKind, arrowType(varType("A"), varType("B"))),
 *   new Map([["A", "X"], ["B", "Y"]])
 * );
 * // => ∀A::*. (A → Y)
 * // (A is bound; B is renamed)
 * ```
 *
 * @example Rename inside applications and structural types:
 * ```ts
 * renameType(state,
 *   appType(conType("Either"), varType("x")),
 *   new Map([["Either", "Result"], ["x", "X"]])
 * );
 * // => Result<X>
 * ```
 */
export function renameType(
  state: TypeCheckerState,
  ty: Type,
  ren: Map<string, string>,
  bound: Set<string> = new Set(),
): Type {
  // Variable type: rename unless bound
  if ("var" in ty) {
    const v = ty.var;
    return bound.has(v) ? ty : varType(ren.get(v) ?? v);
  }

  // Constructor type
  if ("con" in ty) {
    const c = ty.con;
    return conType(ren.get(c) ?? c);
  }

  if ("evar" in ty) return ty; // Never rename meta-vars

  if ("never" in ty) return ty;

  // Arrow
  if ("arrow" in ty) {
    return arrowType(
      renameType(state, ty.arrow.from, ren, bound),
      renameType(state, ty.arrow.to, ren, bound),
    );
  }

  // Application
  if ("app" in ty) {
    return appType(
      renameType(state, ty.app.func, ren, bound),
      renameType(state, ty.app.arg, ren, bound),
    );
  }

  // Forall: introduce new bound type variable
  if ("forall" in ty) {
    const v = ty.forall.var;
    const newBound = new Set(bound);
    newBound.add(v);

    return forallType(
      v,
      ty.forall.kind,
      renameType(state, ty.forall.body, ren, newBound),
    );
  }

  // Bounded forall
  if ("bounded_forall" in ty) {
    const v = ty.bounded_forall.var;
    const newBound = new Set(bound);
    newBound.add(v);

    const newConstraints = ty.bounded_forall.constraints.map((c) => ({
      trait: ren.get(c.trait) ?? c.trait,
      type: renameType(state, c.type, ren, newBound),
    }));

    return boundedForallType(
      v,
      ty.bounded_forall.kind,
      newConstraints,
      renameType(state, ty.bounded_forall.body, ren, newBound),
    );
  }

  // Lambda type
  if ("lam" in ty) {
    const v = ty.lam.var;
    const newBound = new Set(bound);
    newBound.add(v);

    return lamType(
      v,
      ty.lam.kind,
      renameType(state, ty.lam.body, ren, newBound),
    );
  }

  // Record
  if ("record" in ty) {
    return recordType(
      ty.record.map(([label, field]) => [
        ren.get(label) ?? label,
        renameType(state, field, ren, bound),
      ]),
    );
  }

  // Variant
  if ("variant" in ty) {
    return variantType(
      ty.variant.map(([label, field]) => [
        ren.get(label) ?? label,
        renameType(state, field, ren, bound),
      ]),
    );
  }

  // Tuple
  if ("tuple" in ty) {
    return tupleType(ty.tuple.map((t) => renameType(state, t, ren, bound)));
  }

  // Mu
  if ("mu" in ty) {
    const v = ty.mu.var;
    const newBound = new Set(bound);
    newBound.add(v);

    return muType(v, renameType(state, ty.mu.body, ren, newBound));
  }

  return ty;
}

/**
 * Recursively renames **term‑level identifiers** (variables, dictionary names,
 * labels, etc.) inside a term according to a provided rename map.
 *
 * This is used during **module imports**, **aliasing**, and **qualified name
 * rewriting** to avoid naming collisions and ensure imported code uses the
 * caller’s naming conventions.
 *
 * Like all renamers, `renameTerm` is **binder‑aware**:
 * it will rename *free* variables but will **not** rename variables that are
 * introduced (bound) inside the term.
 *
 * ---------------------------------------------------------------------------
 * What gets renamed?
 * ---------------------------------------------------------------------------
 * - Free **term variables** (`VarTerm`)
 * - Bound dictionary variables used by trait method access (`traitMethodTerm`)
 * - Labels inside records, variants, and patterns (delegated to callers)
 * - Anything in the term structure referencing a name mapped by `ren`
 *
 * What does *not* get renamed?
 * - Variables **introduced by the term itself**, such as:
 *   - lambda parameters (`λx. ...`)
 *   - let‑bound variables (`let x = ...`)
 *   - type‑level binders inside `tylamTerm`, `traitLamTerm`
 *   - dictionary binders inside trait lambdas
 *
 * These names are added to the `bound` set so they won’t be renamed.
 *
 * ---------------------------------------------------------------------------
 * Why renaming is needed
 * ---------------------------------------------------------------------------
 * During `importModule`, the importer may specify renaming rules such as:
 *
 * ```ts
 * aliases = { terms: { oldName: "newName" }, labels: {...}, types: {...} }
 * ```
 *
 * `renameTerm` applies the `terms` map to all *use sites* in a term, ensuring:
 * - no name collisions occur when merging modules
 * - imported code refers to the correct bindings in the new context
 * - local scoping and binding structure remain intact
 *
 * It is the term‑level counterpart to:
 * - {@link renameType}
 * - {@link renamePattern}
 *
 * ---------------------------------------------------------------------------
 * Binder safety
 * ---------------------------------------------------------------------------
 * The `bound` set tracks variable names introduced inside the term.
 *
 * For example:
 *
 * ```ts
 * lamTerm("x", Int, varTerm("x"))
 * ```
 *
 * Even if the rename map contains `"x" → "y"`, the *inner* `x` is bound and
 * must **not** be renamed or it would change the semantics:
 *
 *     λx. x    ↛   λy. x     (incorrect)
 *
 * Instead:
 * - binder is added to `bound`
 * - all occurrences of that binder within its scope are left unchanged
 *
 * ---------------------------------------------------------------------------
 * High‑level algorithm
 * ---------------------------------------------------------------------------
 * 1. If the term is a variable and not bound:
 *        rename if `ren` contains the name
 * 2. If the term introduces a binder:
 *        add binder name to `bound` and recurse inside with updated `bound`
 * 3. For composite expressions:
 *        recursively rename all subterms and embedded types
 * 4. Preserve all binder structure and semantics
 *
 * ---------------------------------------------------------------------------
 * @param state - The typechecker state (used for type renaming and normalization)
 * @param term - The term whose identifiers should be renamed
 * @param ren - A map of `oldName → newName` renamings
 * @param bound - The set of names currently bound (internal use)
 *
 * @returns A new term with free identifiers renamed according to `ren`
 *
 * ---------------------------------------------------------------------------
 * @example Renaming free variables:
 * ```ts
 * renameTerm(state, varTerm("x"), new Map([["x", "y"]]));
 * // => y
 * ```
 *
 * @example Bound variables are not renamed:
 * ```ts
 * const t = lamTerm("x", Int, varTerm("x"));
 * renameTerm(state, t, new Map([["x", "y"]]));
 * // => λx:Int. x    (unchanged)
 * ```
 *
 * @example Renaming inside nested terms:
 * ```ts
 * renameTerm(state,
 *   appTerm(varTerm("f"), varTerm("x")),
 *   new Map([["f", "foo"], ["x", "arg"]])
 * );
 * // => (foo arg)
 * ```
 *
 * @see {@link renameType} Renames in types
 * @see {@link renamePattern} Renames inside patterns
 * @see {@link importModule} Applies renaming when importing modules
 */
export function renameTerm(
  state: TypeCheckerState,
  term: Term,
  ren: Map<string, string>,
  bound: Set<string> = new Set(),
): Term {
  // Term variables
  if ("var" in term) {
    const v = term.var;
    return bound.has(v) ? term : varTerm(ren.get(v) ?? v);
  }

  // Lambda
  if ("lam" in term) {
    const v = term.lam.arg;
    const newBound = new Set(bound);
    newBound.add(v);

    return lamTerm(
      v,
      renameType(state, term.lam.type, ren),
      renameTerm(state, term.lam.body, ren, newBound),
    );
  }

  // Application
  if ("app" in term) {
    return appTerm(
      renameTerm(state, term.app.callee, ren, bound),
      renameTerm(state, term.app.arg, ren, bound),
    );
  }

  // Type lambda
  if ("tylam" in term) {
    const v = term.tylam.var;
    const newBound = new Set(bound);
    newBound.add(v);

    return tylamTerm(
      v,
      term.tylam.kind,
      renameTerm(state, term.tylam.body, ren, newBound),
    );
  }

  // Type application
  if ("tyapp" in term) {
    return tyappTerm(
      renameTerm(state, term.tyapp.term, ren, bound),
      renameType(state, term.tyapp.type, ren),
    );
  }

  // Constant constructor
  if ("con" in term) {
    const name = term.con.name;
    return conTerm(
      ren.get(name) ?? name,
      renameType(state, term.con.type, ren),
    );
  }

  // Record
  if ("record" in term) {
    return recordTerm(
      term.record.map(([label, f]) => [
        ren.get(label) ?? label,
        renameTerm(state, f, ren, bound),
      ]),
    );
  }

  // Projection
  if ("project" in term) {
    return projectTerm(
      renameTerm(state, term.project.record, ren, bound),
      ren.get(term.project.label) ?? term.project.label,
    );
  }

  // Variant injection
  if ("inject" in term) {
    return injectTerm(
      ren.get(term.inject.label) ?? term.inject.label,
      renameTerm(state, term.inject.value, ren, bound),
      renameType(state, term.inject.variant_type, ren),
    );
  }

  // Tuple
  if ("tuple" in term) {
    return tupleTerm(term.tuple.map((t) => renameTerm(state, t, ren, bound)));
  }

  // Tuple projection
  if ("tuple_project" in term) {
    return tupleProjectTerm(
      renameTerm(state, term.tuple_project.tuple, ren, bound),
      term.tuple_project.index,
    );
  }

  // Let binding
  if ("let" in term) {
    const v = term.let.name;
    const newBound = new Set(bound);
    newBound.add(v);

    return letTerm(
      v,
      renameTerm(state, term.let.value, ren, bound),
      renameTerm(state, term.let.body, ren, newBound),
    );
  }

  // Match
  if ("match" in term) {
    return matchTerm(
      renameTerm(state, term.match.scrutinee, ren, bound),
      term.match.cases.map(([pat, body]) => [
        renamePattern(state, pat, ren, bound),
        renameTerm(state, body, ren, bound),
      ]),
    );
  }

  // Fold
  if ("fold" in term) {
    return foldTerm(
      renameType(state, term.fold.type, ren),
      renameTerm(state, term.fold.term, ren, bound),
    );
  }

  // Unfold
  if ("unfold" in term) {
    return unfoldTerm(renameTerm(state, term.unfold, ren, bound));
  }

  // Dictionary term
  if ("dict" in term) {
    return dictTerm(
      ren.get(term.dict.trait) ?? term.dict.trait,
      renameType(state, term.dict.type, ren),
      term.dict.methods.map(([name, impl]) => [
        ren.get(name) ?? name,
        renameTerm(state, impl, ren, bound),
      ]),
    );
  }

  // Trait lambda
  if ("trait_lam" in term) {
    const vType = term.trait_lam.type_var;
    const vDict = term.trait_lam.trait_var;

    const newBound = new Set(bound);
    newBound.add(vType);
    newBound.add(vDict);

    return traitLamTerm(
      ren.get(vDict) ?? vDict,
      ren.get(term.trait_lam.trait) ?? term.trait_lam.trait,
      ren.get(vType) ?? vType,
      term.trait_lam.kind,
      term.trait_lam.constraints.map((c) => ({
        trait: ren.get(c.trait) ?? c.trait,
        type: renameType(state, c.type, ren, newBound),
      })),
      renameTerm(state, term.trait_lam.body, ren, newBound),
    );
  }

  // Trait app
  if ("trait_app" in term) {
    return traitAppTerm(
      renameTerm(state, term.trait_app.term, ren, bound),
      renameType(state, term.trait_app.type, ren),
      term.trait_app.dicts.map((d) => renameTerm(state, d, ren, bound)),
    );
  }

  // Trait method
  if ("trait_method" in term) {
    return traitMethodTerm(
      renameTerm(state, term.trait_method.dict, ren, bound),
      ren.get(term.trait_method.method) ?? term.trait_method.method,
    );
  }

  return term;
}

/**
 * Renames identifiers **inside a pattern** according to a rename map,
 * while respecting **binding structure**.
 *
 * This is the pattern‑level analogue of {@link renameTerm} and
 * {@link renameType}. It is used primarily during **module import renaming**
 * to avoid name collisions and rewrite field/constructor names consistently.
 *
 * ---------------------------------------------------------------------------
 * What gets renamed?
 * ---------------------------------------------------------------------------
 * - **Variable patterns** (`x`)
 *   Renamed unless the variable is already in the `bound` set.
 *
 * - **Record labels** (`{ x: p }`)
 *   Labels are renamed if present in the `ren` map (usually via `aliases.labels`)
 *
 * - **Variant constructor labels** (`Some(x)`)
 *   The `Some` is renamed if mapped in `ren`.
 *
 * - **Subpatterns**
 *   Recursively renamed using the same renaming map.
 *
 * ---------------------------------------------------------------------------
 * What does *not* get renamed?
 * ---------------------------------------------------------------------------
 * Pattern binders introduce new *bound variables* which should not be renamed
 * inside their scope:
 *
 * ```ts
 * variantPattern("Some", varPattern("x"))
 * // 'x' is a binder — recursive renaming should NOT rename occurrences of 'x'
 * ```
 *
 * These binder names are added to the `bound` set so renaming rules will not
 * accidentally overwrite them.
 *
 * The `bound` set is updated similarly to how `renameTerm` handles
 * `lamTerm`/`letTerm` binders.
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * During module import, users may specify renaming rules such as:
 *
 * ```ts
 * aliases = {
 *   labels: { Left: "L", right: "r" },
 *   terms: { hd: "head" },
 *   types: { Option: "Maybe" },
 * };
 * ```
 *
 * `renamePattern` is responsible for rewriting **label** and **variable**
 * occurrences inside patterns so they correctly reference imported names.
 *
 * It is crucial for:
 * - avoiding pattern label collisions
 * - keeping patterns aligned with renamed variant/record definitions
 * - ensuring the match cases use the correct labels after import
 *
 * ---------------------------------------------------------------------------
 * Binder‑aware behavior
 * ---------------------------------------------------------------------------
 * The `bound` set tracks pattern variables **introduced** by:
 * - `varPattern("x")`
 * - nested variable bindings in record/tuple/variant patterns
 *
 * Variables in `bound` are *never* renamed:
 *
 * ```ts
 * renamePattern(state,
 *   recordPattern([["x", varPattern("y")]]),
 *   ren = Map([["y", "z"]]),
 *   bound = new Set()
 * );
 *
 * // result: { x: y }   (y is bound; left unchanged)
 * ```
 *
 * ---------------------------------------------------------------------------
 * @param state - Typechecker state (passed for consistency; not always needed)
 * @param pat - The pattern to rename
 * @param ren - A map of identifier renamings (`oldName → newName`)
 * @param bound - Set of currently bound pattern variables (internal)
 *
 * @returns A new pattern with free names renamed according to `ren`
 *
 * ---------------------------------------------------------------------------
 * @example Renaming a constructor label:
 * ```ts
 * renamePattern(
 *   state,
 *   variantPattern("Some", varPattern("x")),
 *   new Map([["Some", "Just"]]),
 *   new Set()
 * );
 * // => Just(x)
 * ```
 *
 * @example Renaming variable patterns:
 * ```ts
 * renamePattern(
 *   state,
 *   varPattern("x"),
 *   new Map([["x", "y"]]),
 *   new Set()
 * );
 * // => y
 * ```
 *
 * @example Bound variables not renamed:
 * ```ts
 * renamePattern(
 *   state,
 *   recordPattern([["x", varPattern("a")]]),
 *   new Map([["a", "b"]]),
 *   new Set(["a"])
 * );
 * // => { x: a }   // 'a' is bound, so not renamed
 * ```
 *
 * @see {@link renameTerm} Term‑level renaming
 * @see {@link renameType} Type‑level renaming
 * @see {@link importModule} Applies renaming to imported definitions
 */
export function renamePattern(
  state: TypeCheckerState,
  pat: Pattern,
  ren: Map<string, string>,
  bound: Set<string>,
): Pattern {
  if ("var" in pat) {
    // Pattern variable becomes bound
    const v = pat.var;
    const newName = ren.get(v) ?? v;
    bound.add(v);
    return varPattern(newName);
  }

  if ("wildcard" in pat) return pat;

  if ("con" in pat) {
    return conPattern(
      ren.get(pat.con.name) ?? pat.con.name,
      renameType(state, pat.con.type, ren, bound),
    );
  }

  if ("record" in pat) {
    return recordPattern(
      pat.record.map(([label, p]) => [
        ren.get(label) ?? label,
        renamePattern(state, p, ren, bound),
      ]),
    );
  }

  if ("variant" in pat) {
    return variantPattern(
      ren.get(pat.variant.label) ?? pat.variant.label,
      renamePattern(state, pat.variant.pattern, ren, bound),
    );
  }

  if ("tuple" in pat) {
    return tuplePattern(
      pat.tuple.map((p) => renamePattern(state, p, ren, bound)),
    );
  }

  return pat;
}

/**
 * Renames the identifier(s) inside a **context binding** according to a rename map.
 *
 * This is part of the module‑import renaming system.
 * When importing a module, users may supply alias maps to rename:
 * - type constructors
 * - term variables
 * - trait names
 * - enum constructors
 * - dictionary variables
 *
 * `renameBinding` applies these renaming rules to a single binding in the
 * typing context (`Γ`), producing a new binding with updated names.
 *
 * ---------------------------------------------------------------------------
 * What this function renames
 * ---------------------------------------------------------------------------
 * Depending on the kind of binding (`Binding` is a tagged union), the rename map
 * may apply to:
 *
 * 1. **TermBinding**
 *    Renames the term variable name and renames inside its type via {@link renameType}.
 *
 * 2. **TypeBinding**
 *    Renames the type constructor or type variable name using `ren`.
 *
 * 3. **TraitDefBinding**
 *    Renames the **trait name**, and renames types in all method signatures.
 *
 * 4. **TraitImplBinding**
 *    Renames:
 *    - the trait name
 *    - the implemented type (via `renameType`)
 *    - all method implementations inside the dictionary term (via {@link renameTerm})
 *
 * 5. **DictBinding**
 *    Renames:
 *    - the dictionary variable name
 *    - the trait name
 *    - the associated type (via `renameType`)
 *
 * 6. **EnumDefBinding**
 *    Renames:
 *    - enum name
 *    - variant labels
 *      (labels renamed using the caller's label alias map)
 *    - type parameters (only if free, not bound)
 *    - variant payload types (via `renameType`)
 *
 * 7. **TypeAliasBinding**
 *    Renames:
 *    - alias name
 *    - free parameter names (only if not shadowed)
 *    - the alias body (via `renameType`)
 *
 * ---------------------------------------------------------------------------
 * What *doesn't* get renamed?
 * ---------------------------------------------------------------------------
 * - Bound type variables (e.g. alias parameters or `∀A` binders)
 * - Internal dictionary variable names bound by a trait lambda
 * - Labels inside patterns or terms (those are handled by callers)
 *
 * This function focuses solely on **context entries**, not full terms or patterns.
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * During module imports, users can write:
 *
 * ```ts
 * import Foo as Bar (
 *   types = { List: "Vec" },
 *   terms = { head: "first" },
 *   traits = { Show: "Printable" },
 *   labels = { Cons: "Node", Nil: "Empty" }
 * )
 * ```
 *
 * These renaming rules must apply *everywhere*:
 * - in binding names
 * - in types stored inside bindings
 * - inside dictionaries and trait definitions
 *
 * `renameBinding` ensures each binding is correctly rewritten before merging
 * contexts.
 *
 * ---------------------------------------------------------------------------
 * @param state - Typechecker state (used by type and term renamers)
 * @param b - The binding to rename
 * @param ren - A map of `oldName → newName` renamings
 *
 * @returns A new binding with identifiers appropriately renamed
 *
 * ---------------------------------------------------------------------------
 * @example Rename a type binding:
 * ```ts
 * renameBinding(state,
 *   typeBinding("List", arrowKind(starKind, starKind)),
 *   new Map([["List", "Vec"]])
 * );
 * // => type Vec :: * → *
 * ```
 *
 * @example Rename dictionary bindings:
 * ```ts
 * dictBinding("eqInt", "Eq", Int)
 * // rename Eq → Equal
 * ```
 *
 * @see {@link renameType} Renaming inside types
 * @see {@link renameTerm} Renaming inside terms
 * @see {@link renamePattern} Renaming inside patterns
 * @see {@link importModule} Applies renaming to imported contexts
 */
export function renameBinding(
  state: TypeCheckerState,
  b: Binding,
  ren: Map<string, string>,
): Binding {
  if ("term" in b) {
    return termBinding(
      ren.get(b.term.name) ?? b.term.name,
      renameType(state, b.term.type, ren),
    );
  }

  if ("type" in b) {
    return typeBinding(ren.get(b.type.name) ?? b.type.name, b.type.kind);
  }

  if ("trait_def" in b) {
    return traitDefBinding(
      ren.get(b.trait_def.name) ?? b.trait_def.name,
      b.trait_def.type_param,
      b.trait_def.kind,
      b.trait_def.methods.map(([m, t]) => [
        ren.get(m) ?? m,
        renameType(state, t, ren),
      ]),
    );
  }

  if ("trait_impl" in b) {
    return traitImplBinding(
      ren.get(b.trait_impl.trait) ?? b.trait_impl.trait,
      renameType(state, b.trait_impl.type, ren),
      renameTerm(state, b.trait_impl.dict, ren),
    );
  }

  if ("dict" in b) {
    return dictBinding(
      ren.get(b.dict.name) ?? b.dict.name,
      ren.get(b.dict.trait) ?? b.dict.trait,
      renameType(state, b.dict.type, ren),
    );
  }

  if ("enum" in b) {
    return enumDefBinding(
      ren.get(b.enum.name) ?? b.enum.name,
      b.enum.kind,
      b.enum.params,
      b.enum.variants.map(([l, t]) => [
        ren.get(l) ?? l,
        renameType(state, t, ren),
      ]),
    );
  }

  if ("type_alias" in b) {
    return typeAliasBinding(
      ren.get(b.type_alias.name) ?? b.type_alias.name,
      b.type_alias.params,
      b.type_alias.kinds,
      renameType(state, b.type_alias.body, ren),
    );
  }

  return b;
}

/**
 * Computes all **free names** that appear inside a type.
 *
 * This includes:
 * - free **type variables**
 * - referenced **type constructors**
 * - trait names inside **bounded foralls**
 * - record / variant **labels**
 *
 * The result is a {@link FreeTypeNames} structure with four sets:
 * - `typeVars`
 * - `typeCons`
 * - `traits`
 * - `labels`
 *
 * Only **free** names are collected:
 * - Bound type variables introduced by `∀`, `λ`, or `μ` are tracked in the
 *   `bound` set and *not* added to the result.
 *
 * ---------------------------------------------------------------------------
 * Why this function exists
 * ---------------------------------------------------------------------------
 * `computeFreeTypes` is used mainly for:
 *
 * **1. Module dependency analysis**
 *   The importer must determine which types, constructors, traits, and labels
 *   are referenced so it can decide what to import.
 *
 * **2. Renaming**
 *   Tools like `renameType` and `renameBinding` must know which names appear
 *   free inside types to avoid renaming bound variables.
 *
 * **3. Cycle detection**
 *   Used by the module system to detect type alias/enumeration dependency loops.
 *
 * ---------------------------------------------------------------------------
 * What it collects
 * ---------------------------------------------------------------------------
 * - **Type constructors**
 *   e.g., `List`, `Either`, `Option`
 *
 * - **Free type variables**
 *   Variables not introduced by a binder:
 *   ```
 *   ∀A. B → A     => free var: B
 *   ```
 *
 * - **Trait names** inside bounded foralls
 *   ```
 *   ∀Self where Eq<Self>. ...
 *   => traits = {"Eq"}
 *   ```
 *
 * - **Labels** of variants and records
 *   ```
 *   <Left: A | Right: B> => labels = {"Left", "Right"}
 *   { x: Int, y: Bool }   => labels = {"x", "y"}
 *   ```
 *
 * ---------------------------------------------------------------------------
 * Binder‑aware behavior
 * ---------------------------------------------------------------------------
 * Whenever a type binder appears:
 * - `∀A::K. body`
 * - `λA::K. body`
 * - `μA. body`
 *
 * the type variable `A` is added to `bound` and **not** considered free
 * within its body.
 *
 * ---------------------------------------------------------------------------
 * Summary of recursion
 * ---------------------------------------------------------------------------
 * `computeFreeTypes` recursively walks:
 * - applications (`F<T>`)
 * - arrows
 * - tuples
 * - records
 * - variants
 * - polymorphic types (`forall`, `bounded_forall`)
 * - lambda and µ‑types
 *
 * Each node contributes the appropriate names to the result.
 *
 * ---------------------------------------------------------------------------
 * @param _state - Typechecker state (present for API symmetry; not used here)
 * @param ty - The type to analyze
 * @param bound - Set of type variable names currently bound (internal use)
 * @returns A {@link FreeTypeNames} record containing sets of free names
 *
 * ---------------------------------------------------------------------------
 * @example
 * ```ts
 * const ty = appType(
 *   conType("Either"),
 *   arrowType(varType("A"), conType("Int"))
 * );
 *
 * computeFreeTypes(state, ty);
 * // => {
 * //   typeVars: Set(["A"]),
 * //   typeCons: Set(["Either", "Int"]),
 * //   traits:   Set([]),
 * //   labels:   Set([])
 * // }
 * ```
 *
 * @example With bounded forall:
 * ```ts
 * const ty = boundedForallType(
 *   "Self", starKind,
 *   [{ trait: "Eq", type: varType("Self") }],
 *   varType("Self")
 * );
 *
 * computeFreeTypes(state, ty);
 * // => {
 * //   typeVars: Set([]),   // Self is bound
 * //   typeCons: Set([]),
 * //   traits:   Set(["Eq"]),
 * //   labels:   Set([])
 * // }
 * ```
 */
export function computeFreeTypes(
  _state: TypeCheckerState,
  ty: Type,
  bound: Set<string> = new Set(),
): FreeTypeNames {
  const out: FreeTypeNames = {
    typeVars: new Set(),
    typeCons: new Set(),
    traits: new Set(),
    labels: new Set(),
  };

  function go(t: Type, boundVars: Set<string>) {
    if ("var" in t) {
      if (!boundVars.has(t.var)) out.typeVars.add(t.var);
      return;
    }

    if ("con" in t) {
      out.typeCons.add(t.con);
      return;
    }

    if ("evar" in t || "never" in t) return;

    if ("arrow" in t) {
      go(t.arrow.from, boundVars);
      go(t.arrow.to, boundVars);
      return;
    }

    if ("app" in t) {
      go(t.app.func, boundVars);
      go(t.app.arg, boundVars);
      return;
    }

    if ("forall" in t) {
      const newBound = new Set(boundVars);
      newBound.add(t.forall.var);
      go(t.forall.body, newBound);
      return;
    }

    if ("bounded_forall" in t) {
      const newBound = new Set(boundVars);
      newBound.add(t.bounded_forall.var);

      for (const c of t.bounded_forall.constraints) {
        out.traits.add(c.trait);
        go(c.type, newBound);
      }

      go(t.bounded_forall.body, newBound);
      return;
    }

    if ("lam" in t) {
      const newBound = new Set(boundVars);
      newBound.add(t.lam.var);
      go(t.lam.body, newBound);
      return;
    }

    if ("record" in t) {
      for (const [label, field] of t.record) {
        out.labels.add(label);
        go(field, boundVars);
      }
      return;
    }

    if ("variant" in t) {
      for (const [label, caseType] of t.variant) {
        out.labels.add(label);
        go(caseType, boundVars);
      }
      return;
    }

    if ("tuple" in t) {
      for (const e of t.tuple) go(e, boundVars);
      return;
    }

    if ("mu" in t) {
      const newBound = new Set(boundVars);
      newBound.add(t.mu.var);
      go(t.mu.body, newBound);
      return;
    }
  }

  go(ty, bound);
  return out;
}

/**
 * Extracts all **free names** that appear inside a pattern.
 *
 * Unlike type or term free‑variable analysis, pattern extraction is simpler:
 * patterns are *syntactic matchers*, not expressions with scoping rules.
 * Therefore **all identifiers in a pattern are considered free**, because
 * patterns do not introduce nested scopes the way terms do.
 *
 * The result is a {@link FreePatternNames} object containing three sets:
 * - `vars`          — variable names bound by the pattern (`x`, `hd`, `rest`)
 * - `constructors`  — literal/constructor names (`"None"`, `"true"`)
 * - `labels`        — record field labels or variant labels (`x`, `"Left"`)
 *
 * ---------------------------------------------------------------------------
 * Why this exists
 * ---------------------------------------------------------------------------
 * Pattern free‑name extraction is used by:
 *
 * **1. Renaming during module import**
 *   The importer needs to know which labels/constructors occur in patterns so
 *   it can apply alias maps correctly.
 *
 * **2. Dependency analysis**
 *   For example, matching `Some(x)` depends on the variant label `"Some"` and
 *   therefore on the enum that defines it.
 *
 * **3. Pretty‑printing and linting**
 *   Tools may need to inspect patterns for referenced names.
 *
 * ---------------------------------------------------------------------------
 * What it collects
 * ---------------------------------------------------------------------------
 * Pattern form              | Collected names
 * --------------------------|-------------------------------
 * `varPattern("x")`         | vars = { "x" }
 * `wildcardPattern()`       | none
 * `conPattern("None")`      | constructors = { "None" }
 * `variantPattern("Some", p)` | labels = { "Some" } ∪ free names of `p`
 * `recordPattern([["x", p]])` | labels = { "x" } ∪ free names of `p`
 * `tuplePattern([p1, p2])` | union of free names of elements
 *
 * Note: Pattern variables are *collected*, but they are not “bound” in the
 * sense of shadowing—they are all treated as free metadata for renaming.
 *
 * ---------------------------------------------------------------------------
 * @param _state - Typechecker state (present for API symmetry; not used here)
 * @param pat - The pattern to analyze
 * @returns A {@link FreePatternNames} object with sets of free identifiers
 *
 * ---------------------------------------------------------------------------
 * @example
 * ```ts
 * computeFreePatterns(state,
 *   variantPattern("Some", varPattern("x"))
 * );
 * // => {
 * //      vars: Set(["x"]),
 * //      constructors: Set([]),
 * //      labels: Set(["Some"])
 * //    }
 * ```
 *
 * @example Record + tuple:
 * ```ts
 * computeFreePatterns(state,
 *   recordPattern([
 *     ["pt", tuplePattern([varPattern("a"), varPattern("b")])]
 *   ])
 * );
 * // vars: ["a", "b"]
 * // labels: ["pt"]
 * // constructors: []
 * ```
 *
 * @see {@link FreePatternNames} Output shape
 * @see {@link renamePattern} Renaming patterns using this information
 * @see {@link computeFreeTypes} Free names in types
 * @see {@link computeFreeTerms} Free names in full terms
 */
export function computeFreePatterns(
  _state: TypeCheckerState,
  pat: Pattern,
): FreePatternNames {
  const out: FreePatternNames = {
    vars: new Set(),
    constructors: new Set(),
    labels: new Set(),
  };

  function go(p: Pattern) {
    if ("var" in p) {
      out.vars.add(p.var);
      return;
    }

    if ("wildcard" in p) return;

    if ("con" in p) {
      out.constructors.add(p.con.name);
      return;
    }

    if ("record" in p) {
      for (const [label, sub] of p.record) {
        out.labels.add(label);
        go(sub);
      }
      return;
    }

    if ("variant" in p) {
      out.labels.add(p.variant.label);
      go(p.variant.pattern);
      return;
    }

    if ("tuple" in p) {
      for (const sub of p.tuple) go(sub);
      return;
    }
  }

  go(pat);
  return out;
}

/**
 * Computes all **free names** that appear anywhere inside a term.
 *
 * This includes names coming from:
 * - term variables
 * - type constructors inside embedded types
 * - trait names referenced by dictionaries or constraints
 * - dictionary variable names
 * - variant / record / tuple labels
 * - constructors used in patterns or values
 *
 * The result is a {@link FreeTermNames} object with seven sets:
 * - `terms`        — free term variable names
 * - `constructors` — constructor/literal names (from `conTerm`)
 * - `traits`       — trait names appearing in dictionaries, trait lambdas, etc.
 * - `dicts`        — dictionary variable names (from `dictBinding`)
 * - `labels`       — record/variant labels appearing in the term
 * - `typeVars`     — free type variable names inside embedded types
 * - `typeCons`     — type constructor names inside embedded types
 *
 * Term variables bound by constructs such as lambdas or lets are added to
 * the `bound` set and **not** counted as free.
 *
 * ---------------------------------------------------------------------------
 * Why this analysis exists
 * ---------------------------------------------------------------------------
 *
 * Free‑name extraction over terms is required by the module system for:
 *
 * **1. Import dependency analysis**
 *   Determine which types, traits, or constructors from another module are
 *   needed to support the term.
 *
 * **2. Renaming**
 *   {@link renameTerm}, {@link renameType}, and {@link renamePattern} use
 *   this information to safely rewrite terms without renaming bound variables.
 *
 * **3. Pattern‑embedded free names**
 *   Match expressions contain patterns, so this integrates:
 *   - {@link computeFreePatterns} for pattern names
 *   - {@link computeFreeTypes} for type annotations
 *
 * **4. Detecting use of dictionary variables**
 *   Needed for traits, since dictionary variables behave like term bindings.
 *
 * ---------------------------------------------------------------------------
 * What is considered “free”?
 * ---------------------------------------------------------------------------
 *
 * **Free:**
 * - variables used in the term but not introduced locally
 *   (`x` in an outer scope, imported definitions, etc.)
 * - dictionary variables (`d` in `d.eq`)
 * - constructor names from `conTerm`
 * - labels in variant injections and record terms
 * - type names from embedded types (`List`, `Either`, etc.)
 * - trait names (e.g. `"Eq"` in `dict Eq<Int> {...}`)
 *
 * **Not free (i.e., bound):**
 * - lambda parameters: `λx:τ. ...`
 * - let‑bindings: `let x = e in ...`
 * - dictionary variables introduced by `traitLamTerm`
 * - type variables bound by `tylamTerm`, `traitLamTerm`, or type quantifiers
 *
 * ---------------------------------------------------------------------------
 * Bound‑variable handling
 * ---------------------------------------------------------------------------
 * The `bound` set tracks term variables that should **not** be reported as free.
 * For example:
 *
 * ```ts
 * lamTerm("x", Int, varTerm("x"))
 * ```
 *
 * Free‑term collection should report no free term names, because `x` is bound.
 *
 * ---------------------------------------------------------------------------
 * Breakdown of what is collected
 * ---------------------------------------------------------------------------
 * - **Term variables:** from `varTerm`
 * - **Constructors:** from `conTerm`
 * - **Labels:** from `recordTerm`, `variantPattern`, `injectTerm`
 * - **Traits:** from `dictTerm`, `traitLamTerm`, `traitMethodTerm`
 * - **Dictionary variables:** from `traitLamTerm`, `dictBinding`, `traitAppTerm`
 * - **Type-level names:** delegated to {@link computeFreeTypes}
 * - **Pattern names:** delegated to {@link computeFreePatterns}
 *
 * ---------------------------------------------------------------------------
 * @param state - The typechecker state (used for type‑level free names)
 * @param term - The term to analyze
 * @param bound - Names of term variables currently bound (internal)
 *
 * @returns A {@link FreeTermNames} structure describing all free names
 *
 * ---------------------------------------------------------------------------
 * @example Simple application:
 * ```ts
 * computeFreeTerms(state, appTerm(varTerm("f"), varTerm("x")));
 * // => terms = {"f", "x"}
 * ```
 *
 * @example With patterns:
 * ```ts
 * matchTerm(
 *   scrutinee,
 *   [[variantPattern("Some", varPattern("x")), varTerm("x")]]
 * );
 * // free labels = {"Some"}
 * // free variables = {"scrutinee"}
 * ```
 *
 * @example With dictionaries:
 * ```ts
 * traitMethodTerm(varTerm("d"), "eq");
 * // free dicts = {"d"}
 * // free traits = {"Eq"}  (via dictionary type)
 * ```
 *
 * @see {@link computeFreeTypes} Free names inside types
 * @see {@link computeFreePatterns} Free names inside patterns
 * @see {@link renameTerm} Applies renaming to term ASTs
 * @see {@link importModule} Uses this to gather dependencies
 */
export function computeFreeTerms(
  state: TypeCheckerState,
  term: Term,
  bound: Set<string> = new Set(),
): FreeTermNames {
  const out: FreeTermNames = {
    terms: new Set(),
    constructors: new Set(),
    traits: new Set(),
    dicts: new Set(),
    labels: new Set(),
    typeVars: new Set(),
    typeCons: new Set(),
  };

  function mergeTypeNames(t: Type) {
    const r = computeFreeTypes(state, t);
    for (const x of r.typeVars) out.typeVars.add(x);
    for (const x of r.typeCons) out.typeCons.add(x);
    for (const x of r.traits) out.traits.add(x);
    for (const x of r.labels) out.labels.add(x);
  }

  function go(e: Term, boundNames: Set<string>) {
    if ("var" in e) {
      if (!boundNames.has(e.var)) out.terms.add(e.var);
      return;
    }

    if ("con" in e) {
      out.constructors.add(e.con.name);
      mergeTypeNames(e.con.type);
      return;
    }

    if ("lam" in e) {
      mergeTypeNames(e.lam.type);
      const newBound = new Set(boundNames).add(e.lam.arg);
      go(e.lam.body, newBound);
      return;
    }

    if ("app" in e) {
      go(e.app.callee, boundNames);
      go(e.app.arg, boundNames);
      return;
    }

    if ("tylam" in e) {
      const newBound = new Set(boundNames).add(e.tylam.var);
      go(e.tylam.body, newBound);
      return;
    }

    if ("tyapp" in e) {
      mergeTypeNames(e.tyapp.type);
      go(e.tyapp.term, boundNames);
      return;
    }

    if ("let" in e) {
      go(e.let.value, boundNames);
      const newBound = new Set(boundNames).add(e.let.name);
      go(e.let.body, newBound);
      return;
    }

    if ("record" in e) {
      for (const [label, field] of e.record) {
        out.labels.add(label);
        go(field, boundNames);
      }
      return;
    }

    if ("project" in e) {
      out.labels.add(e.project.label);
      go(e.project.record, boundNames);
      return;
    }

    if ("inject" in e) {
      out.labels.add(e.inject.label);
      mergeTypeNames(e.inject.variant_type);
      go(e.inject.value, boundNames);
      return;
    }

    if ("match" in e) {
      go(e.match.scrutinee, boundNames);
      for (const [pat, body] of e.match.cases) {
        const pFree = computeFreePatterns(state, pat);
        for (const c of pFree.constructors) out.constructors.add(c);
        for (const l of pFree.labels) out.labels.add(l);

        const newBound = new Set(boundNames);
        for (const v of pFree.vars) newBound.add(v);

        go(body, newBound);
      }
      return;
    }

    if ("trait_method" in e) {
      go(e.trait_method.dict, boundNames);
      out.labels.add(e.trait_method.method);
      return;
    }

    if ("dict" in e) {
      out.traits.add(e.dict.trait);
      mergeTypeNames(e.dict.type);
      for (const [m, impl] of e.dict.methods) {
        out.labels.add(m);
        go(impl, boundNames);
      }
      return;
    }

    if ("trait_lam" in e) {
      out.traits.add(e.trait_lam.trait);

      const newBound = new Set(boundNames);
      newBound.add(e.trait_lam.type_var);
      newBound.add(e.trait_lam.trait_var);

      for (const c of e.trait_lam.constraints) {
        out.traits.add(c.trait);
        mergeTypeNames(c.type);
      }

      go(e.trait_lam.body, newBound);
      return;
    }

    if ("trait_app" in e) {
      mergeTypeNames(e.trait_app.type);
      go(e.trait_app.term, boundNames);
      for (const d of e.trait_app.dicts) go(d, boundNames);
      return;
    }

    if ("tuple" in e) {
      for (const t of e.tuple) go(t, boundNames);
      return;
    }

    if ("tuple_project" in e) {
      go(e.tuple_project.tuple, boundNames);
      return;
    }

    if ("fold" in e) {
      mergeTypeNames(e.fold.type);
      go(e.fold.term, boundNames);
      return;
    }

    if ("unfold" in e) {
      go(e.unfold, boundNames);
      return;
    }
  }

  go(term, bound);
  return out;
}

/**
 * Imports selected bindings from one module (`from`) into another (`into`),
 * performing **dependency analysis**, **renaming**, **conflict detection**, and
 * **topological ordering** to ensure a well‑formed merged context.
 *
 * This is the heart of the module import system.
 *
 * ---------------------------------------------------------------------------
 * High‑level overview
 * ---------------------------------------------------------------------------
 * Given:
 *   - a source module (`from`)
 *   - a target module (`into`)
 *   - a list of **root names** to import (`roots`)
 *   - optional **rename rules** (`aliases`)
 *   - optional **overwrite permission** (`allowOverrides`)
 *
 * The algorithm:
 *
 * 1. Build user‑provided rename map (`aliases`)
 * 2. Collect all **transitive dependencies** of the requested roots
 *    using {@link collectDependencies}
 * 3. Check for **direct name conflicts** in the target module
 * 4. Build a **final rename map**:
 *      - apply user renames
 *      - auto‑rename only non‑root dependencies that would conflict
 * 5. **Topologically sort** all dependency bindings
 * 6. Rename each binding with {@link renameBinding}
 * 7. Insert renamed bindings into the target context, respecting
 *    the `allowOverrides` setting
 *
 * Returns a new `TypeCheckerState` whose context includes the imported
 * (and possibly renamed) bindings.
 *
 * ---------------------------------------------------------------------------
 * Why so many steps?
 * ---------------------------------------------------------------------------
 * Module import is tricky because:
 * - bindings can depend on each other (aliases, enums, traits, etc.)
 * - names from one module can collide with names in another
 * - renaming must be **systematic** and **binder‑safe**
 * - only the explicitly imported roots should keep their names
 * - dependencies must be imported **in order**, so type aliases and enums
 *   appear before things that depend on them
 *
 * This function ensures all of that.
 *
 * ---------------------------------------------------------------------------
 * Renaming rules
 * ---------------------------------------------------------------------------
 * 1. **User renaming (`aliases`) overrides everything.**
 *    If the user renames `List → Vec`, that applies globally to all imported
 *    references.
 *
 * 2. **Roots keep the user name or their original name.**
 *    They are never auto‑renamed.
 *
 * 3. **Dependencies may be auto‑renamed** *only if* they would collide with
 *    an existing binding in `into`.
 *
 * 4. All renaming is applied through:
 *    - {@link renameBinding}
 *    - which uses {@link renameType}, {@link renameTerm}, {@link renamePattern}
 *
 * ---------------------------------------------------------------------------
 * Conflict handling
 * ---------------------------------------------------------------------------
 * - If a root binding conflicts with the target context and
 *   `allowOverrides = false`, the import fails with a `duplicate_binding` error.
 *
 * - If a dependency conflicts:
 *     → it is auto‑renamed to a fresh, unique name via `freshName`.
 *
 * - If `allowOverrides = true`:
 *     → existing bindings in `into` are replaced.
 *
 * ---------------------------------------------------------------------------
 * Topological ordering
 * ---------------------------------------------------------------------------
 * Bindings must be imported **in dependency order**, e.g.:
 *
 *     type alias A uses B → B must be imported before A
 *     enum Option depends on its type params → bring parameters first
 *     trait implementations depend on trait definitions
 *
 * This is handled by {@link topoSortBindings}.
 *
 * ---------------------------------------------------------------------------
 * Example usage
 * ---------------------------------------------------------------------------
 * ```ts
 * importModule({
 *   from: libState,
 *   into: currentState,
 *   roots: ["List", "map"],
 *   aliases: {
 *     types: { List: "Vec" },
 *     terms: { map: "fmap" }
 *   }
 * });
 * ```
 *
 * - imports `List` as `Vec`
 * - imports `map` as `fmap`
 * - automatically renames any conflicting helper types from the `List` module
 * - inserts renamed dependencies in the correct order
 *
 * ---------------------------------------------------------------------------
 * Parameters
 * ---------------------------------------------------------------------------
 * @param from - The source module’s typechecker state
 * @param into - The target module’s typechecker state
 * @param roots - Names of bindings to import (user‑requested)
 * @param aliases - Optional renaming rules for traits, types, terms, labels
 * @param allowOverrides - Whether existing names in `into` may be overwritten
 *
 * @returns A new state with imported bindings, or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * Errors produced
 * ---------------------------------------------------------------------------
 * - `duplicate_binding` — name conflict for a root binding
 * - `circular_import` — via {@link collectDependencies}
 * - `unbound` / various others — from rename functions or normalization
 *
 * ---------------------------------------------------------------------------
 * See also
 * ---------------------------------------------------------------------------
 * - {@link collectDependencies}
 * - {@link renameBinding}
 * - {@link renameType}, {@link renameTerm}, {@link renamePattern}
 * - {@link topoSortBindings}
 * - {@link ImportAliases}
 */
export function importModule(args: {
  from: TypeCheckerState;
  into: TypeCheckerState;
  roots: string[];
  aliases?: ImportAliases;
  allowOverrides?: boolean;
}): Result<TypingError, TypeCheckerState> {
  const { from, into, roots, aliases = {}, allowOverrides = false } = args;

  // Build user rename map
  const userRen = buildRenameMap(aliases);

  // Step 1: Collect all dependencies (roots + transitive)
  const depResult = collectDependencies(from, roots);
  if ("err" in depResult) return depResult;

  const allDeps = depResult.ok;

  // Step 2: Check ROOT names for direct conflicts (before any renaming)
  // Roots must not conflict unless allowOverrides
  for (const root of roots) {
    // Apply user rename to root if provided
    const rootRenamed = userRen.get(root) ?? root;

    // Check if it conflicts in target
    const existing = into.ctx.find((b) => bindingName(b) === rootRenamed);
    if (existing && !allowOverrides) {
      const incoming = from.ctx.find((b) => bindingName(b) === root)!;
      if (!incoming) continue; // Should never happen

      return err({
        duplicate_binding: {
          name: rootRenamed,
          existing,
          incoming,
        },
      });
    }
  }

  // Step 3: Compute full rename map
  // - User renames apply to everything
  // - Auto-renames ONLY for NON-ROOT dependencies
  const finalRen = new Map(userRen);

  for (const dep of allDeps) {
    // Skip roots (we already checked them above)
    if (roots.includes(dep)) continue;

    // Skip if user already renamed it
    if (userRen.has(dep)) continue;

    // Check for conflict and auto-rename ONLY if it would conflict
    const depRenamed = finalRen.get(dep) ?? dep;
    const exists = into.ctx.some((b) => bindingName(b) === depRenamed);
    if (exists) {
      // Generate fresh name for this hidden dependency
      const fresh = freshName(into, depRenamed);
      finalRen.set(dep, fresh);
    }
  }

  // Step 4: Topo-sort ALL deps (roots + renamed deps)
  const ordered = topoSortBindings(from, allDeps);

  // Step 5: Import using final renames
  const newCtx = [...into.ctx];

  for (const name of ordered) {
    const original = from.ctx.find((b) => bindingName(b) === name);
    if (!original) continue;

    const renamed = renameBinding(from, original, finalRen);
    const newName = bindingName(renamed);

    // No need to check roots again (we did it in Step 2)
    // For deps, we've already auto-renamed, so no conflicts here
    if (allowOverrides) {
      // If overrides allowed, replace if exists
      const idx = newCtx.findIndex((b) => bindingName(b) === newName);
      if (idx !== -1) newCtx.splice(idx, 1, renamed);
      else newCtx.push(renamed);
    } else {
      // Just append (deps shouldn't conflict due to auto-rename)
      newCtx.push(renamed);
    }
  }

  return ok({ ctx: newCtx, meta: into.meta });
}

/**
 * Collects **all transitive dependencies** of the given root bindings
 * in a module’s context.
 *
 * This is the first major step of the module import process.
 * It answers:
 *
 *     “Which bindings must be imported in order for these names to work?”
 *
 * For each root name in `roots`, this function recursively discovers:
 * - types referenced inside its type annotations
 * - traits referenced inside its definitions
 * - constructors, labels, and patterns referenced by enums or dicts
 * - any other bindings indirectly referenced by the above
 *
 * The result is a `Set<string>` containing **all binding names** (including
 * the roots themselves) required for a correct import.
 *
 * ---------------------------------------------------------------------------
 * What counts as a dependency?
 * ---------------------------------------------------------------------------
 * For each binding `b`:
 *
 * • **TermBinding**
 *   Dependencies come from free names in its type.
 *
 * • **TypeBinding**
 *   No direct dependencies (just the kind).
 *
 * • **TypeAliasBinding**
 *   Dependencies come from types referenced in its body and parameter kinds.
 *
 * • **TraitDefBinding**
 *   Dependencies come from types used in method signatures.
 *
 * • **TraitImplBinding**
 *   Dependencies come from:
 *   - the implemented type
 *   - method implementation terms
 *   - referenced traits and types used in dictionary definitions
 *
 * • **DictBinding**
 *   Depends on:
 *   - the trait name
 *   - the type the dictionary applies to
 *
 * • **EnumDefBinding**
 *   Depends on:
 *   - payload types of each variant
 *   - type parameter kinds
 *   - labels associated with variants
 *
 * Dependencies are discovered using:
 * - {@link computeFreeTerms}
 * - {@link computeFreeTypes}
 * - {@link computeFreePatterns}
 * - plus binding‑specific scanning logic
 *
 * ---------------------------------------------------------------------------
 * Cycle detection
 * ---------------------------------------------------------------------------
 * If enums, type aliases, or other bindings form a **dependency cycle**:
 *
 *     A depends on B
 *     B depends on C
 *     C depends on A
 *
 * then `collectDependencies` returns a `circular_import` error.
 *
 * Cycles are tracked through DFS (depth‑first search) using:
 * - a `visited` set
 * - an `active` stack for detecting back‑edges
 *
 * ---------------------------------------------------------------------------
 * Algorithm summary
 * ---------------------------------------------------------------------------
 * 1. Initialize a dependency set with the root names.
 * 2. For each root:
 *      - find the corresponding binding
 *      - extract its free names (dependents)
 *      - recursively process each dependent name
 * 3. Track visited nodes to avoid duplication
 * 4. Track an active recursion stack to detect cycles
 * 5. Return all collected names
 *
 * The output ordering is *not* topological — ordering is handled later by
 * {@link topoSortBindings}. This function only discovers *which* items
 * are required.
 *
 * ---------------------------------------------------------------------------
 * @param state - The module's typechecker state to analyze
 * @param roots - The names explicitly requested for import
 *
 * @returns
 * - `ok(Set<string>)` containing all dependencies, or
 * - `err({ circular_import: ... })` if a cycle is found
 *
 * ---------------------------------------------------------------------------
 * Examples
 * ---------------------------------------------------------------------------
 *
 * **Simple case:**
 * ```ts
 * // Importing "List"
 * // collectDependencies finds: ["List", "Int"]
 * ```
 *
 * **Alias chain:**
 * ```ts
 * type A = B
 * type B = C
 * type C = Int
 * collectDependencies(["A"]) => { "A", "B", "C", "Int" }
 * ```
 *
 * **Cycle:**
 * ```ts
 * type A = B
 * type B = A
 * collectDependencies(["A"])
 * // => err({ circular_import: { name: "A", cycle: ["A", "B", "A"] }})
 * ```
 *
 * ---------------------------------------------------------------------------
 * @see {@link importModule} Uses this to find everything that must be imported
 * @see {@link computeFreeTerms} Extracts free term-level names
 * @see {@link computeFreeTypes} Extracts free type-level names
 * @see {@link computeFreePatterns} For pattern references
 * @see {@link topoSortBindings} For dependency ordering
 */
export function collectDependencies(
  state: TypeCheckerState,
  roots: string[],
): Result<TypingError, Set<string>> {
  const visited = new Set<string>();
  const visiting: string[] = []; // stack for cycle detection
  const deps = new Set<string>();

  function dfs(name: string): Result<TypingError, null> {
    if (visited.has(name)) return ok(null);

    if (visiting.includes(name)) {
      // cycle detected
      const cycleStart = visiting.indexOf(name);
      const cycle = visiting.slice(cycleStart).concat([name]);

      return err({
        circular_import: { name, cycle },
      });
    }

    visiting.push(name);

    const binding = state.ctx.find((b) => bindingName(b) === name);
    if (!binding) {
      visiting.pop();
      return ok(null); // silently ignore missing for now
    }

    deps.add(name);

    const directDeps = bindingDependencies(state, binding);
    for (const d of directDeps) {
      const r = dfs(d);
      if ("err" in r) return r;
    }

    visiting.pop();
    visited.add(name);
    return ok(null);
  }

  for (const root of roots) {
    const r = dfs(root);
    if ("err" in r) return r;
  }

  return ok(deps);
}

function bindingDependencies(state: TypeCheckerState, b: Binding): Set<string> {
  const out = new Set<string>();

  if ("term" in b) {
    const f = computeFreeTypes(state, b.term.type);
    for (const x of f.typeVars) out.add(x);
    for (const x of f.typeCons) out.add(x);
    return out;
  }

  if ("type" in b) return out;

  if ("type_alias" in b) {
    const f = computeFreeTypes(state, b.type_alias.body);
    for (const x of f.typeCons) out.add(x);
    return out;
  }

  if ("enum" in b) {
    for (const [, field] of b.enum.variants) {
      const f = computeFreeTypes(state, field);
      for (const x of f.typeCons) out.add(x);
    }
    return out;
  }

  if ("trait_def" in b) {
    for (const [, ty] of b.trait_def.methods) {
      const f = computeFreeTypes(state, ty);
      for (const x of f.typeCons) out.add(x);
    }
    return out;
  }

  if ("trait_impl" in b) {
    out.add(b.trait_impl.trait);
    const f = computeFreeTypes(state, b.trait_impl.type);
    for (const x of f.typeCons) out.add(x);
    return out;
  }

  if ("dict" in b) {
    out.add(b.dict.trait);
    return out;
  }

  return out;
}

function buildRenameMap(a: ImportAliases): Map<string, string> {
  const ren = new Map<string, string>();

  for (const [k, v] of Object.entries(a.types ?? {})) ren.set(k, v);
  for (const [k, v] of Object.entries(a.traits ?? {})) ren.set(k, v);
  for (const [k, v] of Object.entries(a.terms ?? {})) ren.set(k, v);
  for (const [k, v] of Object.entries(a.labels ?? {})) ren.set(k, v);

  return ren;
}

function topoSortBindings(
  state: TypeCheckerState,
  selected: Set<string>,
): string[] {
  const out: string[] = [];
  const visited = new Set<string>();

  function dfs(name: string) {
    if (visited.has(name)) return;
    visited.add(name);

    const b = state.ctx.find((bb) => bindingName(bb) === name);
    if (!b) return;

    const deps = bindingDependencies(state, b);
    for (const d of deps) if (selected.has(d)) dfs(d);

    out.push(name);
  }

  for (const r of selected) dfs(r);

  return out;
}

function freshName(state: TypeCheckerState, base: string): string {
  let i = 1;
  let name = `${base}_${i}`;
  while (state.ctx.some((b) => bindingName(b) === name)) {
    i++;
    name = `${base}_${i}`;
  }
  return name;
}

function bindingName(b: Binding): string {
  if ("type" in b) return b.type.name;
  if ("term" in b) return b.term.name;
  if ("dict" in b) return b.dict.name;
  if ("trait_def" in b) return b.trait_def.name;
  if ("trait_impl" in b) {
    return `${b.trait_impl.trait}<${showType(b.trait_impl.type)}>`;
  }
  if ("type_alias" in b) return b.type_alias.name;
  if ("enum" in b) return b.enum.name;
  return "<unknown>";
}

function addBinding(
  state: TypeCheckerState,
  binding: Binding,
): Result<TypingError, TypeCheckerState> {
  // Simple duplicate name check
  const name = bindingName(binding);
  const exists = state.ctx.some((b) => bindingName(b) === name);
  if (exists)
    return err({
      duplicate_binding: { name, existing: binding, incoming: binding },
    });

  return ok({ ctx: [...state.ctx, binding], meta: state.meta });
}

/**
 * Adds a **new term binding** to a typechecker state.
 *
 * This is used for:
 * - defining global terms in a module
 * - adding local bindings in a REPL or top‑level environment
 * - programmatically extending a context with a value definition
 *
 * The steps performed:
 *
 * 1. **Infer the type** of the provided term (`inferType`).
 * 2. On success, build a {@link TermBinding}:
 *        name : inferredType
 * 3. Insert the binding into the context using {@link addBinding}.
 *
 * If the term fails to typecheck, the error is returned unchanged.
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - Any error produced by {@link inferType}
 * - `duplicate_binding` (raised inside `addBinding` if the name already exists
 *   in the context, unless overrides are permitted)
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state (context + meta environment)
 * @param name - The term variable name to bind
 * @param term - The term whose type should be inferred and added
 *
 * @returns An updated `TypeCheckerState` or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Add a simple value:
 * ```ts
 * addTerm(state, "x", conTerm("42", conType("Int")));
 * // adds: x : Int
 * ```
 *
 * @example Add a function:
 * ```ts
 * addTerm(state, "id", lamTerm("x", Int, varTerm("x")));
 * // adds: id : Int → Int
 * ```
 *
 * @see {@link inferType} Determines the term’s type
 * @see {@link termBinding} Constructs the context binding
 * @see {@link addBinding} Inserts the binding into the context
 */
export function addTerm(
  state: TypeCheckerState,
  name: string,
  term: Term,
): Result<TypingError, TypeCheckerState> {
  const inferred = inferType(state, term);
  if ("err" in inferred) return inferred;

  const binding = termBinding(name, inferred.ok);
  return addBinding(state, binding);
}

/**
 * Adds a **new type constructor** to the typing context (`Γ`):
 *
 *     name :: kind
 *
 * This function is used when declaring:
 * - primitive types (`Int`, `Bool`, `String`)
 * - user‑defined types
 * - higher‑kinded type constructors (`List :: * → *`)
 * - phantom or marker types
 *
 * The type constructor is recorded as a {@link TypeBinding} and inserted into
 * the context using {@link addBinding}.
 *
 * ---------------------------------------------------------------------------
 * What this does
 * ---------------------------------------------------------------------------
 * 1. Creates a `TypeBinding(name, kind)`
 * 2. Calls {@link addBinding} to insert it into the context
 *    - If the name already exists and overrides are not allowed:
 *      → returns a `duplicate_binding` error
 *    - Otherwise adds or replaces the existing binding
 *
 * Unlike `addTypeAlias` or `addEnum`, this function registers **only a name and
 * a kind**, without a structural definition.
 *
 * The “meaning” of the type is defined elsewhere (via normalization, enums,
 * or user code); this binding simply declares that the name is a valid type
 * constructor with arity determined by its kind.
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - defining primitive types in the initial environment
 * - registering user‑defined type constructors before using them
 * - adding higher‑kinded constructors needed by polymorphic code
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `duplicate_binding` (if the name already exists and overrides are not allowed)
 *
 * ---------------------------------------------------------------------------
 * @param state - The current typechecker state (context + meta environment)
 * @param name - The type constructor name
 * @param kind - The kind of the type constructor (e.g. `*`, `* → *`)
 *
 * @returns An updated `TypeCheckerState` or a `TypingError`
 *
 * ---------------------------------------------------------------------------
 * @example Add simple types:
 * ```ts
 * addType(state, "Int", starKind);   // Int :: *
 * addType(state, "Bool", starKind);  // Bool :: *
 * ```
 *
 * @example Higher‑kinded type:
 * ```ts
 * addType(state, "List", arrowKind(starKind, starKind));
 * // List :: * → *
 * ```
 *
 * @see {@link TypeBinding} Context binding format
 * @see {@link addBinding} Generic binding insertion
 * @see {@link addTypeAlias} Declares type aliases
 * @see {@link addEnum} Declares enums (nominal sum types)
 */
export function addType(
  state: TypeCheckerState,
  name: string,
  kind: Kind,
): Result<TypingError, TypeCheckerState> {
  // No type-level kindchecking required beyond duplicate check
  const binding = typeBinding(name, kind);
  return addBinding(state, binding);
}

/**
 * Adds a **parametric type alias** to the typing context (`Γ`):
 *
 *     type Name<A₁::K₁, A₂::K₂, ...> = Body
 *
 * A type alias introduces a *syntactic abbreviation* for a type expression.
 * It does **not** create a new nominal type; aliases are expanded during
 * normalization by {@link normalizeType}.
 *
 * This function:
 * 1. Validates that the kinds of all parameters are well‑formed.
 * 2. Ensures no conflicting binding exists (unless overrides are allowed).
 * 3. Creates a {@link TypeAliasBinding}.
 * 4. Inserts it into the context via {@link addBinding}.
 *
 * ---------------------------------------------------------------------------
 * Kind and well‑formedness rules
 * ---------------------------------------------------------------------------
 * Each parameter `Aᵢ` is assigned a kind `Kᵢ`. The alias body is checked for
 * kind correctness **inside a context extended with those bindings**.
 *
 * Example:
 * ```ts
 * type Id<A :: *> = A
 * // Body A must have kind *, consistent with A :: *
 * ```
 *
 * If the body is ill‑kinded, a `kind_mismatch` error is returned.
 *
 * ---------------------------------------------------------------------------
 * Purpose of aliases
 * ---------------------------------------------------------------------------
 * Type aliases are used to:
 * - simplify large or complex type expressions
 * - define type‑level synonyms (e.g., `type Pair<A,B> = (A, B)`)
 * - reduce repetition in signatures and ADT payloads
 *
 * They are expanded transparently during:
 * - type equality (`typesEqual`)
 * - unification (`unifyTypes`)
 * - normalization (`normalizeType`)
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `duplicate_binding` — alias name already defined
 * - `kind_mismatch` — alias body has the wrong kind under parameter bindings
 * - `unbound` errors in the alias body
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state
 * @param name - Alias name
 * @param params - Type parameter names
 * @param kinds - Kinds for each parameter
 * @param body - The type expression defining the alias
 *
 * @returns An updated `TypeCheckerState` or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Simple identity alias:
 * ```ts
 * addTypeAlias(state, "Id", ["A"], [starKind], varType("A"));
 * // type Id<A> = A
 * ```
 *
 * @example Multi‑parameter alias:
 * ```ts
 * addTypeAlias(
 *   state,
 *   "Pair",
 *   ["A", "B"],
 *   [starKind, starKind],
 *   tupleType([varType("A"), varType("B")])
 * );
 * // type Pair<A,B> = (A, B)
 * ```
 *
 * @example Higher‑kinded alias:
 * ```ts
 * addTypeAlias(
 *   state,
 *   "Const",
 *   ["F", "X"],
 *   [arrowKind(starKind, starKind), starKind],
 *   appType(varType("F"), conType("Int"))
 * );
 * ```
 *
 * @see {@link typeAliasBinding} The binding inserted by this function
 * @see {@link addBinding} Context insertion logic
 * @see {@link normalizeType} Alias expansion
 * @see {@link addType} Declares concrete type constructors
 */
export function addTypeAlias(
  state: TypeCheckerState,
  name: string,
  params: string[],
  kinds: Kind[],
  body: Type,
): Result<TypingError, TypeCheckerState> {
  let aliasKind = starKind;
  for (let i = params.length - 1; i >= 0; i--)
    aliasKind = arrowKind(kinds[i]!, aliasKind);

  const extendedCtx: Context = [
    { type: { name, kind: aliasKind } },
    ...params.map((p, i) => typeBinding(p, kinds[i]!)),
    ...state.ctx,
  ];

  const kindRes = checkKind({ ctx: extendedCtx, meta: state.meta }, body);
  if ("err" in kindRes) return kindRes;

  const binding = typeAliasBinding(name, params, kinds, body);
  return addBinding(state, binding);
}

/**
 * Adds a **nominal enum (algebraic data type)** definition to the typing
 * context (`Γ`).
 *
 * This declares a named sum type with variants, similar to:
 *
 * ```ts
 * enum Option<T :: *> {
 *   None : ()
 *   Some : T
 * }
 * ```
 *
 * The definition records:
 * - the enum **name**
 * - its **kind** (derived from the parameter kinds)
 * - its **type parameters**
 * - its **variants**, each with a payload type scheme
 * - whether the enum is **recursive**
 *
 * The resulting binding is stored as an {@link EnumDefBinding}.
 *
 * ---------------------------------------------------------------------------
 * How enums are used in the typechecker
 * ---------------------------------------------------------------------------
 *
 * **1. Normalization**
 * During {@link normalizeType}, nominal enums are expanded into structural
 * variant types, e.g.:
 *
 * ```
 * Option<Int>  ⇒  <None: (), Some: Int>
 * ```
 *
 * If `recursive = true`, the expansion forms a recursive `μ`‑type:
 *
 * ```
 * List<Int> ⇒ μX. <Nil: (), Cons: (Int, X)>
 * ```
 *
 * **2. Pattern matching**
 * {@link checkPattern} uses enum definitions to:
 * - validate constructor labels
 * - substitute type parameters into variant payloads
 *
 * **3. Exhaustiveness checking**
 * {@link checkExhaustive} uses the enum’s variant labels to determine whether
 * match expressions cover all cases.
 *
 * **4. Variant injection typing**
 * {@link inferInjectType} uses enum metadata to typecheck
 * `<Label = value> as Enum<Args>`.
 *
 * ---------------------------------------------------------------------------
 * Kind and arity checking
 * ---------------------------------------------------------------------------
 * - Each parameter must be assigned a kind (`params[i] :: kinds[i]`).
 * - The enum’s overall kind is constructed as:
 *
 *     kinds[0] → kinds[1] → ... → *
 *
 * - Each variant payload (a `FieldScheme`) is checked to ensure all contained
 *   types have kind `*`.
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `duplicate_binding` if the enum name already exists
 * - `kind_mismatch` if a parameter or payload has an invalid kind
 * - invalid type expressions in the variant payloads
 *
 * ---------------------------------------------------------------------------
 * @param state - The current typechecker state
 * @param name - The enum name (e.g. `"Option"`)
 * @param params - Type parameter names (e.g. `["T"]`)
 * @param kinds - Kinds of each parameter (e.g. `[starKind]`)
 * @param variants - List of `[label, FieldScheme]` variant definitions
 * @param recursive - Whether the ADT may recursively reference itself
 *                    (defaults to `true`)
 *
 * @returns A new `TypeCheckerState` or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Simple ADT:
 * ```ts
 * addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", varType("T")]
 * ]);
 * ```
 *
 * @example Recursive list:
 * ```ts
 * addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([varType("T"), appType(conType("List"), varType("T"))])]
 * ], true);
 * ```
 *
 * @see {@link enumDefBinding} Binding structure stored in the context
 * @see {@link normalizeType} Expands enums into structural variants
 * @see {@link inferInjectType} Variant‑injection typing rule
 * @see {@link checkPattern} Variant pattern checking
 * @see {@link checkExhaustive} Match coverage analysis
 */
export function addEnum(
  state: TypeCheckerState,
  name: string,
  params: string[],
  kinds: Kind[],
  variants: [string, FieldScheme][],
  recursive: boolean = true, // Optional flag: treat as recursive ADT (default: true)
): Result<TypingError, TypeCheckerState> {
  // Step 1: compute List<T> kind
  let enumKind: Kind = starKind;
  for (let i = params.length - 1; i >= 0; i--)
    enumKind = arrowKind(kinds[i]!, enumKind);

  // Step 2: create a temporary binding for recursive kind checking
  const extendedCtx: Context = [
    { type: { name, kind: enumKind } },
    ...params.map((p, i) => typeBinding(p, kinds[i]!)),
    ...state.ctx,
  ];

  // Check kind of each variant's field (must be *)
  let hasSelfReference = false;
  for (let i = 0; i < variants.length; i++) {
    const [label, field] = variants[i]!;
    const kindRes = checkKind({ ctx: extendedCtx, meta: state.meta }, field);
    if ("err" in kindRes) return kindRes;
    if (!isStarKind(kindRes.ok)) {
      return err({
        kind_mismatch: {
          expected: starKind,
          actual: kindRes.ok,
          context: `in enum ${name} variant ${label}`,
        },
      });
    }

    // Detect self-reference if recursive mode
    if (recursive) {
      const free = computeFreeTypes(
        { ctx: extendedCtx, meta: state.meta },
        field,
      );
      if (free.typeCons.has(name)) {
        hasSelfReference = true;
      }
    }
  }

  // Only set recursive if flag + self-reference found
  const effectiveRecursive = recursive && hasSelfReference;

  // Bind with recursive flag
  const binding = enumDefBinding(
    name,
    enumKind,
    params,
    variants,
    effectiveRecursive,
  );
  return addBinding(state, binding);
}

/**
 * Adds a **trait definition** to the typing context (`Γ`).
 *
 * A trait definition introduces a *typeclass‑like interface* with:
 * - a **trait name** (e.g. `"Eq"`, `"Show"`, `"Ord"`)
 * - a **type parameter** the trait abstracts over (e.g. `"Self"`, `"A"`)
 * - the **kind** of that parameter (`*`, `* → *`, etc.)
 * - a list of **method signatures**, where each method has a type possibly
 *   referencing the trait’s type parameter
 *
 * Example:
 * ```ts
 * trait Eq<Self :: *> {
 *   eq : Self → Self → Bool
 * }
 * ```
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * 1. Constructs a trait definition binding via {@link traitDefBinding}.
 * 2. Checks for:
 *    - **duplicate names** (trait already defined)
 *    - **kind correctness** of all method types
 * 3. Inserts the trait definition into the context using {@link addBinding}.
 *
 * After insertion, the trait becomes available for:
 * - dictionary validation (`inferDictType`)
 * - method access typing (`inferTraitMethodType`)
 * - trait‑bounded polymorphism (`traitLamTerm`, `boundedForallType`)
 * - instance resolution (`checkTraitImplementation`)
 *
 * ---------------------------------------------------------------------------
 * Method signature rules
 * ---------------------------------------------------------------------------
 * Each method type may reference the trait’s type parameter.
 * For example:
 * ```ts
 * ["eq", arrowType(varType("Self"), arrowType(varType("Self"), Bool))]
 * ```
 *
 * The body of every method type must have kind `*`, and any type constructor
 * usage inside its signature must be well‑kinded.
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - `duplicate_binding` if a trait with the same name already exists
 * - `kind_mismatch` if a method’s type has the wrong kind
 * - `unbound` if a method refers to unknown type constructors
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state (context + meta environment)
 * @param name - Trait name (e.g. `"Eq"`)
 * @param typeParam - The type parameter name (`"Self"`, `"A"`)
 * @param kind - The kind of the type parameter (`*`, `* → *`, ...)
 * @param methods - Method signatures `[methodName, methodType]`
 *
 * @returns A new `TypeCheckerState` with the trait added, or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Adding a simple trait:
 * ```ts
 * addTraitDef(
 *   state,
 *   "Eq",
 *   "A",
 *   starKind,
 *   [
 *     ["eq", arrowType(varType("A"), arrowType(varType("A"), conType("Bool")))]
 *   ]
 * );
 * ```
 *
 * @example Higher‑kinded trait:
 * ```ts
 * addTraitDef(
 *   state,
 *   "Functor",
 *   "F",
 *   arrowKind(starKind, starKind),
 *   [
 *     ["map",
 *       arrowType(
 *         arrowType(varType("A"), varType("B")),
 *         arrowType(
 *           appType(varType("F"), varType("A")),
 *           appType(varType("F"), varType("B"))
 *         )
 *       )
 *     ]
 *   ]
 * );
 * ```
 *
 * @see {@link traitDefBinding} Creates the binding object
 * @see {@link traitImplBinding} Declares trait implementations
 * @see {@link dictTerm} Method implementation storage
 * @see {@link inferTraitMethodType} Method projection typing
 * @see {@link inferDictType} Validates dictionaries
 */
export function addTraitDef(
  state: TypeCheckerState,
  name: string,
  typeParam: string,
  kind: Kind,
  methods: [string, Type][],
): Result<TypingError, TypeCheckerState> {
  const extendedCtx: Context = [typeBinding(typeParam, kind), ...state.ctx];

  for (const [, ty] of methods) {
    const kindRes = checkKind({ ctx: extendedCtx, meta: state.meta }, ty);
    if ("err" in kindRes) return kindRes;
    if (!isStarKind(kindRes.ok))
      return err({
        kind_mismatch: { expected: starKind, actual: kindRes.ok },
      });
  }

  const binding = traitDefBinding(name, typeParam, kind, methods);
  return addBinding(state, binding);
}

/**
 * Adds a **trait implementation** (typeclass instance) to the typing context.
 *
 * Conceptually:
 *     impl Trait for Type = dict
 *
 * This declares that a specific **type** implements a specific **trait**, using
 * the given **dictionary** (`dict`) as evidence.
 *
 * For example:
 * ```ts
 * addTraitImpl(state, "Eq", conType("Int"), eqIntDict);
 * ```
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * 1. Validates that the dictionary term is well‑typed using {@link inferDictType}.
 * 2. Checks that an implementation for `(trait, type)` does not already exist
 *    (unless overriding is permitted elsewhere).
 * 3. Constructs a `TraitImplBinding` via {@link traitImplBinding}.
 * 4. Inserts the binding into the context through `state.ctx.push(...)`.
 *
 * After insertion, this instance becomes available for:
 * - trait constraint solving (`checkTraitImplementation`)
 * - bounded polymorphism instantiation (`instantiateWithTraits`)
 * - trait‑application typing (`inferTraitAppType`)
 * - dictionary‑based method lookup (`traitMethodTerm`)
 *
 * ---------------------------------------------------------------------------
 * Dictionary validation
 * ---------------------------------------------------------------------------
 * Before adding the implementation, the dictionary is typechecked:
 * - all required methods must be present
 * - each method must match the trait’s signature (after substitution)
 * - the trait must exist in the current context
 * - the implemented type must have the correct kind
 *
 * Any failure here results in a `TypingError`.
 *
 * ---------------------------------------------------------------------------
 * Duplicate implementation rules
 * ---------------------------------------------------------------------------
 * A type may not implement the same trait more than once.
 *
 * If `state.ctx` already contains:
 *     trait_impl: { trait: "Eq", type: Int }
 *
 * then attempts to add a second implementation yield a
 * `duplicate_binding` error (unless the hosting environment allows overrides).
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state
 * @param trait - Trait name being implemented
 * @param type - Type for which the trait is implemented
 * @param dict - Dictionary term providing method implementations
 *
 * @returns A new state with the implementation added, or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Adding a simple implementation:
 * ```ts
 * const eqIntDict = dictTerm("Eq", Int, [
 *   ["eq", lamTerm("x", Int, lamTerm("y", Int, conTerm("true", Bool)))]
 * ]);
 * addTraitImpl(state, "Eq", Int, eqIntDict);
 * ```
 *
 * @example Used for bounded polymorphism:
 * ```ts
 * // Trait-bound: ∀Self where Eq<Self>. Self → Bool
 * // addTraitImpl allows resolving Eq<Int> or Eq<MyType> constraints.
 * ```
 *
 * @see {@link traitImplBinding} Context representation of trait implementations
 * @see {@link inferDictType} Validates dictionary correctness
 * @see {@link checkTraitImplementation} Resolves trait constraints
 * @see {@link instantiateWithTraits} Instantiates bounded foralls
 */
export function addTraitImpl(
  state: TypeCheckerState,
  trait: string,
  type: Type,
  dict: Term, // DictTerm
): Result<TypingError, TypeCheckerState> {
  // Validate the actual dictionary implementation
  const dictType = inferDictType(state, dict as DictTerm);
  if ("err" in dictType) return dictType;

  // Install trait impl binding
  const binding = traitImplBinding(trait, type, dict);
  return addBinding(state, binding);
}

/**
 * Adds a **dictionary value** to the typing context (`Γ`) under a given name.
 *
 * A dictionary is a term of the form:
 *
 *     dict Trait<Type> { method₁ = impl₁, ... }
 *
 * and represents **explicit evidence** that a type implements a trait.
 *
 * Unlike {@link addTraitImpl}, which registers a *global* trait instance,
 * `addDict` introduces a **local dictionary variable**, similar to:
 *
 *     d : Dict<Eq, Int>
 *
 * This is useful in:
 * - REPL environments
 * - manual dictionary passing
 * - intermediate testing
 * - debugging trait logic
 *
 * ---------------------------------------------------------------------------
 * What this function does
 * ---------------------------------------------------------------------------
 * 1. Infers the type of the dictionary using {@link inferDictType}.
 *    This ensures:
 *    - the trait exists
 *    - all required methods are present
 *    - method implementations are correctly typed
 *    - the dictionary type is well‑formed
 *
 * 2. Creates a {@link DictBinding}:
 *
 *        name : Dict<trait, type>
 *
 * 3. Inserts this binding into the context using {@link addBinding}.
 *
 * The full dictionary term itself remains available in `state.ctx` under
 * the `dict` property of the binding.
 *
 * ---------------------------------------------------------------------------
 * When to use
 * ---------------------------------------------------------------------------
 * - When the user explicitly writes a dictionary value they want to name:
 *   ```ts
 *   let eqInt = dict Eq<Int> { eq = ... }
 *   ```
 *
 * - When testing trait implementations manually:
 *   ```ts
 *   addDict(state, "eqInt", eqIntDict);
 *   ```
 *
 * - When manually passing dictionaries during trait applications
 *   (without relying on auto‑instantiation).
 *
 * ---------------------------------------------------------------------------
 * Error cases
 * ---------------------------------------------------------------------------
 * - Any error produced by {@link inferDictType}
 * - `duplicate_binding` if the dictionary name already exists
 *
 * ---------------------------------------------------------------------------
 * @param state - Current typechecker state
 * @param name - Variable name for the dictionary (e.g., `"eqInt"`)
 * @param dict - The dictionary term to bind
 *
 * @returns Updated state or a {@link TypingError}
 *
 * ---------------------------------------------------------------------------
 * @example Adding a dictionary:
 * ```ts
 * const dict = dictTerm("Eq", Int, [
 *   ["eq", lamTerm("x", Int, lamTerm("y", Int, conTerm("true", Bool)))]
 * ]);
 *
 * addDict(state, "eqInt", dict);
 * // => adds eqInt : Dict<Eq, Int>
 * ```
 *
 * @example Using the dictionary:
 * ```ts
 * traitMethodTerm(varTerm("eqInt"), "eq");
 * // accesses the eq method inside eqInt
 * ```
 *
 * @see {@link inferDictType} Validates the dictionary
 * @see {@link dictBinding} Context storage of dictionary variables
 * @see {@link traitMethodTerm} Accessing dictionary methods
 */
export function addDict(
  state: TypeCheckerState,
  name: string,
  dict: DictTerm,
): Result<TypingError, TypeCheckerState> {
  const ty = inferType(state, dict);
  if ("err" in ty) return ty;

  const binding = dictBinding(name, dict.dict.trait, dict.dict.type);
  return addBinding(state, binding);
}
