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
 * Creates a type equality constraint for the worklist solver.
 *
 * **Purpose**: Adds a unification constraint `left = right` to a worklist.
 * This is the core primitive for type equivalence during inference, checking,
 * and subsumption. The solver will normalize both sides, handle meta-vars,
 * and propagate substitutions via `solveConstraints(worklist, subst)`.
 *
 * Used in:
 * - `unifyTypes()` (structural matching)
 * - `subsumes()` (subtyping)
 * - Pattern matching unification
 *
 * @param left - Left-hand type (normalized by solver)
 * @param right - Right-hand type (normalized by solver)
 * @returns Type equality constraint
 *
 * @example Basic unification
 * ```ts
 * import { typeEq, solveConstraints, freshState } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [typeEq(varType("a"), varType("Int"))];
 * const subst = new Map<string, Type>();
 *
 * const result = solveConstraints(state, worklist, subst);
 * // subst: { "a" => Int }
 * ```
 *
 * @example Recursive unification (arrow types)
 * ```ts
 * import { typeEq, arrowType, solveConstraints, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq(
 *   arrowType({ var: "a" }, { var: "b" }),
 *   arrowType(conType("Int"), conType("Bool"))
 * )];
 * const subst = new Map();
 * solveConstraints(state, worklist, subst);
 * // Unifies a=Int, b=Bool
 * ```
 *
 * @see {@link solveConstraints}
 * @see {@link unifyTypes}
 */
export const typeEq = (left: Type, right: Type): TypeEqConstraint => ({
  type_eq: { left, right },
});

/**
 * Creates a kind equality constraint for kind unification.
 *
 * **Purpose**: Ensures two kinds are equivalent (e.g., during higher-kinded
 * type application). Kinds unify structurally: `* ≡ *`, `κ₁→κ₂ ≡ κ₁'→κ₂'`.
 *
 * Less common than type equality (triggers on HKT apps like `List<Int>` where
 * `List :: * → *`).
 *
 * @param left - Left-hand kind
 * @param right - Right-hand kind
 * @returns Kind equality constraint
 *
 * @example HKT application kind check
 * ```ts
 * import { kindEq, arrowKind, starKind, solveConstraints, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [kindEq(
 *   arrowKind(starKind, starKind),  // * → *
 *   arrowKind(starKind, starKind)   // Matches
 * )];
 * // Processes via unifyKinds() → ok(null)
 * ```
 *
 * @example Kind mismatch (fails)
 * ```ts
 * import { kindEq, starKind, arrowKind, solveConstraints, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [kindEq(starKind, arrowKind(starKind, starKind))];
 * const result = solveConstraints(state, worklist);
 * // err: { kind_mismatch: { expected: *, actual: (* → *) } }
 * ```
 *
 * @see {@link solveConstraints}
 * @see {@link checkAppKind}
 */
export const kindEq = (left: Kind, right: Kind): KindEqConstraint => ({
  kind_eq: { left, right },
});

/**
 * Creates a "has kind" constraint to defer kind checking.
 *
 * **Purpose**: Schedules `Γ ⊢ ty : kind` for later resolution. Used when a type's
 * well-formedness is needed but context/metas aren't ready (e.g., during
 * unification of polymorphic types, or checking alias bodies).
 *
 * The solver calls `checkKind(state, ty)` and adds a follow-up `kindEq` if needed.
 *
 * @param ty - Type to check
 * @param kind - Expected kind
 * @param state - Checker state (context + metas)
 * @returns Has-kind constraint
 *
 * @example Defer kind check during unification
 * ```ts
 * import { hasKind, solveConstraints, freshState, lamType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [hasKind(
 *   lamType("X", starKind, varType("X")),  // λX::*.X : * → *
 *   starKind
 * )];
 * solveConstraints(state, worklist);
 * // Triggers checkKind(lam...) → adds kindEq(*→*, *) → fails safely
 * ```
 *
 * @example Valid HKT kinding
 * ```ts
 * import { hasKind, appType, conType, starKind, solveConstraints } from "system-f-omega";
 * // Assumes List :: * → * in ctx
 * const worklist = [hasKind(appType(conType("List"), conType("Int")), starKind)];
 * // checkKind(List<Int>) → * ✓
 * ```
 *
 * @see {@link checkKind}
 * @see {@link solveConstraints}
 */
export const hasKind = (
  ty: Type,
  kind: Kind,
  state: TypeCheckerState,
): HasKindConstraint => ({
  has_kind: { ty, kind, state },
});

/**
 * Creates a "has type" constraint to defer type checking/inference of a subterm.
 *
 * **Purpose**: Schedules `Γ ⊢ term : ty` (via `inferType` or `checkType`).
 * Used in bidirectional checking when a subterm's type needs resolution but
 * context isn't finalized (e.g., during let-bindings, trait method checking,
 * or dictionary validation).
 *
 * Triggers `inferType(state, term)` → adds `typeEq(result, ty)`.
 *
 * @param term - Term to type
 * @param ty - Expected type
 * @param state - Checker state
 * @returns Has-type constraint
 *
 * @example Defer subterm checking in let-binding
 * ```ts
 * import { hasType, solveConstraints, freshState, lamTerm } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [hasType(
 *   lamTerm("x", conType("Int"), { var: "x" }),  // λx:Int.x
 *   { arrow: { from: conType("Int"), to: conType("Int") } }
 * )];
 * solveConstraints(state, worklist);
 * // infers (Int → Int) → typeEq ✓
 * ```
 *
 * @example Trait method validation
 * ```ts
 * // Inside inferDictType: defer each method impl check
 * worklist.push(hasType(methodImpl, expectedMethodType));
 * ```
 *
 * @see {@link inferType}
 * @see {@link solveConstraints}
 */
export const hasType = (
  term: Term,
  ty: Type,
  state: TypeCheckerState,
): HasTypeConstraint => ({
  has_type: { term, ty, state },
});

/** Infer mode used for the inferTypeWithMode function. */
export type InferMode =
  | { infer: null } // Infer type arguments
  | { check: Type }; // Check against expected type

export const inferMode = { infer: null };
export const checkMode = (check: Type) => ({ check });

/**
 * Bidirectional type inference/checking dispatcher.
 *
 * **Purpose**: Unified entrypoint for **bidirectional type checking**.
 * - **Infer mode** (`{ infer: null }`): Synthesizes type via `inferType` (`Γ ⊢ e ⇒ τ`).
 * - **Check mode** (`{ check: Type }`): Validates against expected type via `checkType` (`Γ ⊢ e ⇐ τ`), returning inferred/resolved type.
 *
 * Returns `Type` in **both modes** (unifies APIs). Handles polymorphism, traits, and constraints seamlessly.
 * Central to the typechecker — used in applications, lets, trait methods, pattern branches, etc.
 *
 * **Why bidirectional?**
 * - **Robust**: Infers when possible, checks when expected (e.g., lambdas, records).
 * - **Precise errors**: Checking gives better diagnostics than pure inference.
 * - **Efficient**: Avoids unnecessary generalization.
 *
 * @param state - Type checker state (context + meta-vars)
 * @param term - Term to type
 * @param mode - Inference mode: `{ infer: null }` or `{ check: Type }`
 * @returns Inferred/checked type, or error (mismatch, unbound, etc.)
 *
 * @example Inference mode (synthesize type)
 * ```ts
 * import { inferTypeWithMode, freshState, lamTerm, conType, varTerm } from "system-f-omega";
 *
 * const state = freshState();
 * const identity = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = inferTypeWithMode(state, identity, { infer: null });
 * console.log(showType(result.ok));  // (Int → Int)
 * ```
 *
 * @example Checking mode (validate against expected)
 * ```ts
 * import { inferTypeWithMode, arrowType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * const result = inferTypeWithMode(state, identity, { check: expected });
 * // ok({ type: (Int → Bool), subst: Map }) → returns (Int → Bool)
 * // or err(type_mismatch) if incompatible
 * ```
 *
 * @example Error case (mismatch in check mode)
 * ```ts
 * import { inferTypeWithMode, freshState, conTerm } from "system-f-omega";
 * import { arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const num = conTerm("42", conType("Int"));
 * const result = inferTypeWithMode(state, num, {
 *   check: arrowType(conType("Int"), conType("Bool"))
 * });
 * // err: { type_mismatch: { expected: (Int → Bool), actual: Int } }
 * ```
 *
 * @see {@link inferType} Synthesis-only (infer mode)
 * @see {@link checkType} Analysis-only (check mode)
 * @see {@link InferMode} Mode discriminator
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
 * The base kind `*` representing concrete types.
 *
 * **Purpose**: The terminal kind in the kind lattice. All value-habiting types
 * have kind `*`: `Int :: *`, `Bool :: *`, `List<Int> :: *`. Higher-kinded types
 * (type constructors) use arrow kinds: `List :: * → *`.
 *
 * **Usage**:
 * - Type bindings: `addType(state, "Int", starKind)`
 * - Polymorphic binders: `forallType("a", starKind, ...)`, `tylamTerm("a", starKind, ...)`
 * - Kind unification/app checking: `List<Int>` requires `List :: * → *`
 *
 * @example Type constructor declaration
 * ```ts
 * import { addType, starKind, arrowKind } from "system-f-omega";
 *
 * // Int :: *
 * addType(freshState(), "Int", starKind);
 *
 * // List :: * → *
 * addType(freshState(), "List", arrowKind(starKind, starKind));
 * ```
 *
 * @example Polymorphic lambda
 * ```ts
 * import { tylamTerm, starKind } from "system-f-omega";
 *
 * const id = tylamTerm("a", starKind, lamTerm("x", { var: "a" }, { var: "x" }));
 * // Λa::*. (a → a)
 * ```
 *
 * @see {@link arrowKind}
 * @see {@link addType}
 * @see {@link checkKind}
 */
export const starKind: Kind = { star: null };

/**
 * The bottom type `⊥` (never type) — inhabits no values.
 *
 * **Purpose**: Represents the empty type (uninhabited). Key properties:
 * - **Subtyping**: `⊥ <: τ` for *any* `τ` (anything matches bottom).
 * - **Unification**: `⊥ ~ τ` succeeds if `τ :: *` (but `τ ~ ⊥` only if `τ = ⊥`).
 * - **Uses**: Unreachable branches, empty variants (`<>`), cycle detection fallback,
 *   error recovery in inference.
 *
 * **Never confuses with `void`**: `⊥` is a *type*, not a value (no `neverValue`).
 *
 * @example Subtyping (⊥ matches anything)
 * ```ts
 * import { neverType, isBottom, isAssignableTo, freshState } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * isBottom(state, neverType);           // true
 * isAssignableTo(state, neverType, conType("Int"));  // true (⊥ <: Int)
 * ```
 *
 * @example Unification behavior
 * ```ts
 * import { unifyTypes, neverType, freshState } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * unifyTypes(state, neverType, conType("Int"), [], new Map());  // ok(null)
 * unifyTypes(state, conType("Int"), neverType, [], new Map());  // err(mismatch)
 * ```
 *
 * @example Empty variant (unreachable case)
 * ```ts
 * import { variantType } from "system-f-omega";
 *
 * const emptyVariant = variantType([]);  // < > :: ⊥
 * // normalizeType(state, emptyVariant) → { never: null }
 * ```
 *
 * @see {@link isBottom}
 * @see {@link isAssignableTo}
 * @see {@link subsumes}
 */
export const neverType = { never: null };

/**
 * Merges local and global substitutions, with **local shadowing global**.
 *
 * **Purpose**: Combines substitutions from nested inference/checking scopes.
 * - **Globals first**: Persistent solutions (`meta.solutions`).
 * - **Local overrides**: Temporary bindings from current `solveConstraints` take precedence.
 *
 * Used after constraint solving to propagate solutions upward:
 * - `checkType` → `mergeSubsts(solveRes.ok, bodyCheckRes.ok.subst)`
 * - Trait methods, pattern branches, let-bindings.
 * Ensures meta-vars solved locally update globals without losing prior solutions.
 *
 * **Key invariant**: Local subst **never conflicts** with globals (unification ensures compatibility).
 *
 * @param local - Temporary substitution (higher precedence)
 * @param globals - Persistent/global solutions (base layer)
 * @returns Merged `Map<string, Type>` (local shadows globals)
 *
 * @example Basic merge (local shadows)
 * ```ts
 * import { mergeSubsts } from "system-f-omega";
 * import { varType, conType } from "system-f-omega";
 *
 * const globals = new Map([["a", conType("Int")]]);
 * const local = new Map([["a", conType("Bool")], ["b", conType("String")]]);
 *
 * const merged = mergeSubsts(local, globals);
 * console.log(merged.get("a"));  // Bool (local wins!)
 * console.log(merged.get("b"));  // String
 * ```
 *
 * @example Real unification flow (checkType)
 * ```ts
 * import { mergeSubsts, solveConstraints, freshState, typeEq } from "system-f-omega";
 * import { varType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq({ var: "a" }, { var: "b" })];
 * const localSubst = new Map();  // From solveConstraints(worklist)
 * solveConstraints(state, worklist, localSubst);  // { "a" => { var: "b" } }
 *
 * const globals = state.meta.solutions;  // { "b" => Int }
 * const merged = mergeSubsts(localSubst, globals);  // { "a" => Int, "b" => Int }
 * ```
 *
 * @example Empty cases
 * ```ts
 * const emptyLocal = new Map();
 * const merged1 = mergeSubsts(emptyLocal, globals);  // === globals
 *
 * const emptyGlobal = new Map();
 * const merged2 = mergeSubsts(local, emptyGlobal);   // === local
 * ```
 *
 * @see {@link solveConstraints} Produces local subst
 * @see {@link checkType} Uses merge for nested results
 * @see {@link applySubstitution} Consumes merged subst
 * @see {@link Substitution} `Map<string, Type>`
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
 * Creates a fresh existential meta-variable `?N` for type inference.
 *
 * **Purpose**: Generates unification variables during inference/checking.
 * - **Unbound metas**: Represent unknowns solved later by `solveConstraints`.
 * - **Kind-tracked**: `env.kinds.set(name, kind)` enables `checkKind(?N)`.
 * - **Counter-based**: Sequential `?0`, `?1`, ... (avoids clashes).
 *
 * Core to **algorithm W/HM-style inference**: Instantiate foralls, defer decisions.
 * Used everywhere: polymorphism (`instantiateType`), app checking, pattern matching.
 *
 * @param env - Meta environment (`state.meta`) with counter + solutions
 * @param kind - Kind of meta-var (defaults `*` for concrete types)
 * @returns Fresh `{ evar: "?N" }`
 *
 * @example Basic inference variable
 * ```ts
 * import { freshMetaVar, freshState } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta, starKind);
 * console.log(meta);  // { evar: "?0" }
 * console.log(state.meta.kinds.get("?0"));  // { star: null }
 * ```
 *
 * @example HKT meta-variable
 * ```ts
 * import { freshMetaVar, freshState, arrowKind } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const hktMeta = freshMetaVar(state.meta, arrowKind(starKind, starKind));  // ?1 :: * → *
 * // Used for: inferType(app(List, Int)) → List<Int> where List = ?1
 * ```
 *
 * @example Polymorphism instantiation
 * ```ts
 * import { freshMetaVar, freshState, forallType } from "system-f-omega";
 * import { starKind, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const freshA = freshMetaVar(state.meta);  // ?0
 * // instantiateType(poly) → ?0 → ?0 (id specialized)
 * ```
 *
 * @see {@link solveMetaVar} Solves `?N := τ`
 * @see {@link MetaEnv} Tracks `counter`, `kinds`, `solutions`
 * @see {@link instantiateType} Uses for forall instantiation
 */
export function freshMetaVar(env: MetaEnv, kind: Kind = starKind): MetaType {
  const name = `?${env.counter++}`;
  env.kinds.set(name, kind);
  return { evar: name };
}

/**
 * Checks if a type normalizes to the bottom type `⊥` (never).
 *
 * **Purpose**: Detects uninhabited types for:
 * - **Subtyping**: `⊥ <: τ` always holds (`isAssignableTo`).
 * - **Unification**: `⊥ ~ τ` succeeds if `τ :: *`.
 * - **Exhaustiveness**: Empty variants/matches → `⊥`.
 * - **Cycles**: Infinite normalization → `⊥` fallback.
 *
 * Normalizes first (`normalizeType(state, type)`), then checks `"never" in ty`.
 *
 * @param state - Checker state (for normalization)
 * @param type - Input type (may be complex/aliased)
 * @returns `true` if `⊥`, `false` otherwise
 *
 * @example Direct bottom
 * ```ts
 * import { isBottom, neverType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * isBottom(state, neverType);  // true
 * ```
 *
 * @example Subtyping use (⊥ matches anything)
 * ```ts
 * import { isBottom, isAssignableTo, freshState, conType } from "system-f-omega";
 * import { neverType } from "system-f-omega";
 *
 * const state = freshState();
 * const unreachable = neverType;
 * isBottom(state, unreachable);                  // true
 * isAssignableTo(state, unreachable, conType("Int"));  // true (⊥ <: Int)
 * ```
 *
 * @example Normalization to bottom (empty variant)
 * ```ts
 * import { isBottom, freshState, variantType } from "system-f-omega";
 *
 * const state = freshState();
 * const emptyVar = variantType([]);  // < >
 * isBottom(state, emptyVar);         // true (normalizes to ⊥)
 * ```
 *
 * @example Cycle detection fallback
 * ```ts
 * import { isBottom, freshState, muType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const cyclic = muType("X", { var: "X" });  // Degenerate μX.X
 * isBottom(state, cyclic);                   // true (normalize → ⊥)
 * ```
 *
 * @see {@link neverType} The `⊥` constructor
 * @see {@link normalizeType} Preprocessing step
 * @see {@link isAssignableTo} Uses for `⊥ <: τ`
 * @see {@link subsumes} Bottom early-exit
 */
export const isBottom = (state: TypeCheckerState, type: Type) =>
  "never" in normalizeType(state, type);

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
 * Occurs check: detects if meta-var `evar` appears in `ty` (prevents cycles).
 *
 * **Purpose**: Ensures no cyclic bindings like `?X := ?X → Int` during unification.
 * Recurses structurally, follows solutions (`?Y → sol`), skips bound vars/foralls.
 * Called by `solveMetaVar`/`unifyMetaVar` before binding.
 *
 * @param env - Meta environment (for following solutions)
 * @param evar - Meta-var name to find (`"?X"`)
 * @param ty - Type to search
 * @returns `true` if `evar` occurs (cycle!), `false` otherwise
 *
 * @example Cycle detection (blocks binding)
 * ```ts
 * import { occursCheckEvar, freshState } from "system-f-omega";
 * import { arrowType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const env = state.meta;
 * const cycleTy = arrowType({ evar: "?0" }, varType("Int"));  // ?0 → Int
 * occursCheckEvar(env, "?0", cycleTy);  // true → reject ?0 := ?0 → Int
 * ```
 *
 * @example Follows solutions
 * ```ts
 * env.solutions.set("?1", { evar: "?0" });  // ?1 := ?0
 * occursCheckEvar(env, "?0", { evar: "?1" });  // true (follows ?1 → ?0)
 * ```
 *
 * @see {@link solveMetaVar} Caller (rejects on `true`)
 * @see {@link unifyMetaVar} Caller during unification
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
 * Instantiates polymorphic terms by freshening type variables (term-level `instantiateType`).
 *
 * **Purpose**: Monomorphizes type-lambda-bound terms for concrete use:
 * - **Type lambdas** (`Λα. e`): Freshen `α → ?N`, substitute into body, return `e[?N] [?N]`.
 * - **Structural recursion**: Instantiates subterms/types recursively (post-order).
 *
 * Used for:
 * - Trait dictionary instantiation (`checkTraitImplementation`).
 * - Polymorphic let-bindings, applications.
 * - Avoids capture during substitution.
 *
 * **Algorithm** (tylam special case):
 * 1. Recurse: `instBody = instantiateTerm(body)`
 * 2. Fresh: `?N = freshMetaVar()`
 * 3. Subst: `body[α ↦ ?N]` (via `applySubstitutionToTerm`)
 * 4. Apply: `tyappTerm(body[?N], ?N)`
 *
 * Other constructors: Recurse structurally + `instantiateType` on embedded types.
 *
 * @param state - Checker state (metas for freshening)
 * @param term - Input term (possibly polymorphic)
 * @returns Instantiated term with fresh metas
 *
 * @example Basic type-lambda instantiation
 * ```ts
 * import { instantiateTerm, freshState, tylamTerm, lamTerm, varTerm, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * // Λa::*. λx:a. x
 *
 * const inst = instantiateTerm(state, polyId);
 * // λx:?0. x [?0]  (monomorphized)
 * ```
 *
 * @example Nested: Dictionary methods
 * ```ts
 * import { instantiateTerm, freshState, dictTerm } from "system-f-omega";
 * // Assumes poly methods with tylams
 *
 * const polyDict = dictTerm("Eq", { var: "Self" }, [
 *   ["eq", tylamTerm("a", starKind,  poly impl )]
 * ]);
 * const instDict = instantiateTerm(state, polyDict);
 * // Methods now monomorphized with fresh ?N
 * ```
 *
 * @example Trait lambda (constraints + body)
 * ```ts
 * import { instantiateTerm, freshState, traitLamTerm } from "system-f-omega";
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [], body);
 * const inst = instantiateTerm(state, traitLam);
 * // Constraints/types freshened, body instantiated
 * ```
 *
 * @see {@link instantiateType} Type-level counterpart (foralls)
 * @see {@link applySubstitutionToTerm} Substitutes fresh metas
 * @see {@link freshMetaVar} Generates `?N`
 * @see {@link checkTraitImplementation} Primary caller
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
 * Instantiates universal quantifiers in types by freshening bound variables.
 *
 * **Purpose**: Skolemizes polymorphic types for concrete use (e.g., subsumption, unification):
 * - **`∀α. τ`**: Replace `α ↦ ?N`, recurse on body.
 * - **`∀{C}. τ`**: Same (constraints handled externally via dicts).
 * - **Recurses** until quantifier-free.
 *
 * Used in:
 * - `subsumes()`: Instantiate general type before subtyping.
 * - Trait resolution: Freshen impl types.
 * - Unification: Avoid capture.
 *
 * **Algorithm**:
 * 1. `∀α. τ` → `fv = freshMetaVar()` → `τ[α ↦ fv]` → recurse
 * 2. `∀{C}. τ` → same (skip `C`)
 * 3. Base: return `τ`
 *
 * @param state - Checker state (metas for freshening)
 * @param type - Input type (possibly polymorphic)
 * @returns Quantifier-free type with fresh metas
 *
 * @example Basic forall instantiation
 * ```ts
 * import { instantiateType, freshState, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const inst = instantiateType(state, polyId);
 * console.log(showType(inst));  // (?0 → ?0)
 * ```
 *
 * @example Nested foralls
 * ```ts
 * import { instantiateType, freshState, forallType, tupleType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const nested = forallType("a", starKind,
 *   forallType("b", starKind, tupleType([varType("a"), varType("b")])));
 * const inst = instantiateType(state, nested);
 * console.log(showType(inst));  // (?0, ?1)
 * ```
 *
 * @example Bounded forall (constraints external)
 * ```ts
 * import { instantiateType, freshState, boundedForallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const bounded = boundedForallType("a", starKind, [], arrowType(varType("a"), varType("a")));
 * const inst = instantiateType(state, bounded);
 * console.log(showType(inst));  // (?0 → ?0)  (ignores constraints)
 * ```
 *
 * @see {@link substituteType} Performs `[α ↦ ?N]`
 * @see {@link freshMetaVar} Generates `?N`
 * @see {@link subsumes} Primary caller (instantiate general)
 * @see {@link instantiateTerm} Term-level counterpart
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
 * Subtyping relation: `specific <: general` (mutates `worklist`/`subst`).
 *
 * **Purpose**: Checks if `specific` is a subtype of `general`:
 * 1. Instantiate `general` (Skolemize foralls).
 * 2. **Bottom rules**:
 *    - `⊥ <: τ` always (if `τ :: *`).
 *    - `τ <: ⊥` only if `τ = ⊥`.
 * 3. Otherwise: `unifyTypes(instGeneral, specific)` (structural).
 *
 * Supports width subsumption (records), equi-recursion (μ), nominal enums.
 * Used in checking, pattern matching, trait resolution.
 *
 * @param state - Checker state
 * @param general - Supertype (e.g., `List<a>`)
 * @param specific - Subtype (e.g., `List<Int>`, `⊥`)
 * @param worklist - Constraint accumulator
 * @param subst - Mutable substitution
 * @returns `ok(null)` if subtypes, else error
 *
 * @example Bottom subtyping (⊥ <: anything)
 * ```ts
 * import { subsumes, freshState, neverType, conType, listType } from "system-f-omega";
 * // Assume List<Int> in ctx
 *
 * const state = freshState();
 * const result = subsumes(state, conType("List<Int>"), neverType, [], new Map());
 * // ok(null) ✓
 * ```
 *
 * @example Record width subsumption
 * ```ts
 * import { subsumes, freshState, recordType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const wide = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 * const narrow = recordType([["x", conType("Int")]]);
 * subsumes(state, wide, narrow, [], new Map());  // ok(null) ✓ (narrow <: wide)
 * ```
 *
 * @example Polymorphic instantiation + unify
 * ```ts
 * import { subsumes, freshState, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const mono = arrowType(conType("Int"), conType("Int"));
 * subsumes(state, poly, mono, [], new Map());  // instantiate → ?0→?0 ~ Int→Int ✓
 * ```
 *
 * @example Failure (Int not <: Bool)
 * ```ts
 * import { subsumes, freshState, conType } from "system-f-omega";
 *
 * const state = freshState();
 * subsumes(state, conType("Bool"), conType("Int"), [], new Map());
 * // err: { type_mismatch: { expected: Bool, actual: Int } }
 * ```
 *
 * @see {@link instantiateType} Skolemizes `general`
 * @see {@link isBottom} Early bottom checks
 * @see {@link unifyTypes} Structural fallback
 * @see {@link isAssignableTo} Simplified wrapper
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
 * Quick subtyping check: `from <: to` (assignable).
 *
 * **Purpose**: Decidable `τ₁ <: τ₂` for simple cases **without constraints**:
 * - `⊥ <: τ` always (bottom subtypes anything).
 * - `τ <: ⊥` only if `τ = ⊥`.
 * - Otherwise: `typesEqual(τ₁, τ₂)` (normalize + structural).
 *
 * **Fast path** for checking, patterns, unification guards (no worklist).
 * Use `subsumes` for full polymorphic/width subtyping.
 *
 * @param state - Checker state (for normalization/equality)
 * @param from - Source type (subtype)
 * @param to - Target type (supertype)
 * @returns `true` if assignable
 *
 * @example Bottom subtypes anything
 * ```ts
 * import { isAssignableTo, freshState, neverType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * isAssignableTo(state, neverType, conType("Int"));  // true (⊥ <: Int)
 * ```
 *
 * @example Non-bottom cannot subtype ⊥
 * ```ts
 * import { isAssignableTo, freshState, neverType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * isAssignableTo(state, conType("Int"), neverType);  // false
 * ```
 *
 * @example Equality (normal case)
 * ```ts
 * import { isAssignableTo, freshState, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const fnTy = arrowType(conType("Int"), conType("Bool"));
 * isAssignableTo(state, fnTy, fnTy);  // true
 * ```
 *
 * @see {@link subsumes} Full subtyping (polymorphic/width)
 * @see {@link typesEqual} Structural equality fallback
 * @see {@link isBottom} Bottom detection
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
 * Extracts variable bindings from a pattern (for context extension).
 *
 * **Purpose**: Collects pattern variables as `[name, type]` pairs to extend
 * the typing context during `checkPattern`/`matchTerm`. Leaf vars get placeholder
 * `{ var: "$unknown" }` (resolved to actual slice during checking).
 *
 * Recursive: flattens nested records/variants/tuples. Ignores wildcards/cons.
 *
 * Used in: `checkPattern` → `extendedCtx = [...state.ctx, ...patternBindings(pat)]`.
 *
 * @param pattern - Input pattern
 * @returns Flat list of `[varName, placeholderType]` bindings
 *
 * @example Simple variable
 * ```ts
 * import { patternBindings, varPattern } from "system-f-omega";
 *
 * patternBindings(varPattern("x"));  // [["x", { var: "$unknown" }]]
 * ```
 *
 * @example Nested collection
 * ```ts
 * import { patternBindings, recordPattern, variantPattern, tuplePattern } from "system-f-omega";
 * import { varPattern, wildcardPattern } from "system-f-omega";
 *
 * // {x: (hd, _)} → ["x", ...] + ["hd"]
 * patternBindings(recordPattern([["head", tuplePattern([varPattern("hd"), wildcardPattern()])]]));
 * // [["head", { var: "$unknown" }], ["hd", { var: "$unknown" }]]
 *
 * patternBindings(variantPattern("Cons", varPattern("xs")));  // [["xs", { var: "$unknown" }]]
 * ```
 *
 * @example No bindings
 * ```ts
 * import { patternBindings, wildcardPattern } from "system-f-omega";
 *
 * patternBindings(wildcardPattern());  // []
 * ```
 *
 * @see {@link checkPattern} Resolves placeholders to real types
 * @see {@link matchTerm} Uses for branch contexts
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
 * Resolves a trait dictionary for `type` implementing `trait`.
 *
 * **Purpose**: **Dictionary-passing trait resolution** (Haskell-style):
 * 1. **Exact match**: Lookup `trait_impl` with `typesEqual(impl.type, target)`.
 * 2. **Polymorphic**:
 *    - Normalize/impl/target.
 *    - Instantiate impl (`∀ → ?N`).
 *    - Apply target lambdas to fresh metas (HKT matching).
 *    - Unify → solve → instantiate dict + apply subst.
 * 3. Fail: `{ missing_trait_impl: { trait, type } }`.
 *
 * Returns instantiated dictionary term (methods specialized).
 *
 * @param state - Checker state (ctx for impls, metas)
 * @param trait - Trait name (`"Eq"`, `"Functor"`)
 * @param type - Concrete type (`List<Int>`, `Option<Bool>`)
 * @returns Dictionary `Term` or error
 *
 * @example Exact match
 * ```ts
 * import { checkTraitImplementation, freshState, conType, dictTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = state.ctx.push({
 *   trait_impl: { trait: "Eq", type: conType("Int"), dict: dictTerm("Eq", conType("Int"), []) }
 * });
 * const dict = checkTraitImplementation(state, "Eq", conType("Int"));
 * // ok(dictTerm("Eq", Int, [...]))
 * ```
 *
 * @example Polymorphic impl (List for List<Int>)
 * ```ts
 * import { checkTraitImplementation, freshState, forallType, appType } from "system-f-omega";
 * // Assume List :: * → *, impl: ∀F. Eq<F> given List impl
 *
 * const state = freshState();  // + trait_impl { trait: "Eq", type: conType("List"), dict: polyDict }
 * const dict = checkTraitImplementation(state, "Eq", appType(conType("List"), conType("Int")));
 * // ok(instantiated dict for List<Int>)
 * ```
 *
 * @example Failure (no impl)
 * ```ts
 * import { checkTraitImplementation, freshState, conType } from "system-f-omega";
 *
 * const state = freshState();
 * checkTraitImplementation(state, "Eq", conType("String"));
 * // err: { missing_trait_impl: { trait: "Eq", type: String } }
 * ```
 *
 * @see {@link checkTraitConstraints} Multi-constraint resolution
 * @see {@link instantiateType} Skolemizes impl types
 * @see {@link instantiateTerm} Freshens dict
 * @see {@link traitImplBinding} Stores impls
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
 * Resolves dictionaries for multiple trait constraints.
 *
 * **Purpose**: Batch-resolves `[{trait: "Eq", type: τ}, ...]` → `[dict1, dict2, ...]`.
 * Short-circuits on first failure. Used for bounded polymorphism/trait apps.
 *
 * Sequential: Calls `checkTraitImplementation` per constraint.
 *
 * @param state - Checker state
 * @param constraints - List of `{trait, type}` bounds
 * @returns Array of dictionary terms or first error
 *
 * @example Success (multiple dicts)
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, conType, checkTraitConstraints, arrowType, lamTerm, varTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", { star: null }).ok;
 * state = addType(state, "Bool", { star: null }).ok;
 * state = addTraitDef(state, "Eq", "A", { star: null }, [
 *   ["eq", arrowType(conType("A"), arrowType(conType("A"), conType("Bool")))]
 * ]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"), lamTerm("y", conType("Int"), conTerm("true", conType("Bool"))))]
 * ]);
 * state = traitImplBinding("Eq", conType("Int"), eqDict);
 *
 * const constraints = [{ trait: "Eq", type: conType("Int") }];
 * const result = checkTraitConstraints(state, constraints);
 * console.log("ok:", result.ok.length === 1);  // true
 * ```
 *
 * @example Failure (propagates first error)
 * ```ts
 * import { freshState, addType, addTraitDef, conType, checkTraitConstraints } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", { star: null }).ok;
 * state = addTraitDef(state, "Eq", "A", { star: null }, [["eq", conType("Bool")]]).ok;
 * // No Eq<String> impl!
 *
 * const constraints = [{ trait: "Eq", type: conType("String") }];
 * const result = checkTraitConstraints(state, constraints);
 * console.log("err:", "missing_trait_impl" in result.err);  // true
 * ```
 *
 * @example Bounded forall resolution
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, conType, boundedForallType, checkTraitConstraints, starKind, arrowType } from "system-f-omega";
 * import { lamTerm, varTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = traitImplBinding("Eq", conType("Int"), dict);
 *
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: conType("Int") }], arrowType(varType("a"), conType("Int")));
 * const constraints = bounded.bounded_forall.constraints;
 * const dicts = checkTraitConstraints(state, constraints);
 * console.log("dicts:", dicts.ok.length);  // 1
 * ```
 *
 * @see {@link checkTraitImplementation} Resolves single constraint
 * @see {@link traitAppTerm} Uses resolved dicts
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

function extractPatternLabels(pattern: Pattern): Set<string> {
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
 * Checks if patterns exhaustively cover all cases of `type` (variant/enum).
 *
 * **Purpose**: Pattern match safety: ensures no uncovered cases.
 * - **Nominal**: Lookup enum binding → check arity → label coverage.
 * - **Structural**: Direct variant labels.
 * - **Wildcard/Var**: Always exhaustive.
 * - **Primitives/Functions**: Always ok (no cases).
 *
 * Errors: `not_a_variant`, `kind_mismatch` (arity), `missing_case`.
 *
 * @param state - Checker state (ctx for enums)
 * @param patterns - Match cases
 * @param type - Scrutinee type (normalized)
 * @returns `ok(null)` if exhaustive, else error
 *
 * @example Success: Nominal enum full coverage
 * ```ts
 * import { freshState, addType, addEnum, checkExhaustive, conType, variantPattern, varPattern, appType, starKind } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 *
 * const patterns = [
 *   variantPattern("Red", varPattern("x")),
 *   variantPattern("Blue", varPattern("y"))
 * ];
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("exhaustive:", "ok" in result);  // true
 * ```
 *
 * @example Success: Wildcard early exit
 * ```ts
 * import { freshState, checkExhaustive, varPattern } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const patterns = [varPattern("x")];  // Catches all
 * const result = checkExhaustive(state, patterns, conType("Any"));
 * console.log("wildcard ok:", "ok" in result);  // true
 * ```
 *
 * @example Failure: Missing case
 * ```ts
 * import { freshState, addEnum, checkExhaustive, conType, variantPattern, varPattern, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", { var: "Unit" }],
 *   ["Blue", { var: "Unit" }]
 * ]).ok;
 *
 * const patterns = [variantPattern("Red", varPattern("x"))];  // Missing Blue
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("missing:", "missing_case" in result.err);  // true
 * ```
 *
 * @example Failure: Non-variant type
 * ```ts
 * import { freshState, checkExhaustive, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const patterns = [];  // Empty OK for primitives
 * const result = checkExhaustive(state, patterns, conType("Int"));
 * console.log("non-variant ok:", "ok" in result);  // true
 * ```
 *
 * @see {@link inferMatchType} Calls during match inference
 * @see {@link checkPattern} Single-pattern validation
 * @see {@link extractPatternLabels} Label collection
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
 * Type-checks pattern against `type`, returning bindings for context extension.
 *
 * **Purpose**: Validates `pat :: type` → extracts vars as `Context` for branch typing:
 * - **Var**: Binds whole `type`.
 * - **Wildcard/Con**: No bindings.
 * - **Variant**: Unfold μ, infer metas, structural/nominal lookup → recurse on payload.
 * - **Record/Tuple**: Recurse on fields/elements.
 *
 * Errors: `unbound`, `not_a_variant`, `invalid_variant_label`, `kind_mismatch`.
 *
 * @param state - Checker state (ctx/metas)
 * @param pattern - Pattern to check
 * @param type - Expected type (normalized)
 * @returns Bindings `[{ term: { name: "x", type: τ } }, ...]` or error
 *
 * @example Success: Variable binding
 * ```ts
 * import { freshState, addType, checkPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkPattern(state, varPattern("x"), conType("Int"));
 * console.log("bindings:", result.ok.length === 1);  // true
 * console.log("name:", result.ok[0].term.name);      // "x"
 * ```
 *
 * @example Success: Nested variant (nominal enum)
 * ```ts
 * import { freshState, addType, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind, tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const result = checkPattern(state, variantPattern("Some", varPattern("x")), appType(conType("Option"), conType("Int")));
 * console.log("bindings:", result.ok.length === 1);  // true
 * console.log("name:", result.ok[0].term.name);      // "x"
 * ```
 *
 * @example Success: Record flattening
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, conType, recordType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const result = checkPattern(state, recordPattern([
 *   ["x", varPattern("a")],
 *   ["y", varPattern("b")]
 * ]), recordType([["x", conType("Int")], ["y", conType("Bool")]]));
 * console.log("bindings:", result.ok.length === 2);  // true ("a", "b")
 * ```
 *
 * @example Failure: Invalid variant label
 * ```ts
 * import { freshState, addEnum, checkPattern, variantPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", { var: "Unit" }]]).ok;
 *
 * const result = checkPattern(state, variantPattern("Blue", varPattern("x")), conType("Color"));
 * console.log("error:", "invalid_variant_label" in result.err);  // true
 * ```
 *
 * @see {@link inferMatchType} Uses bindings per branch
 * @see {@link checkExhaustive} Coverage check
 * @see {@link patternBindings} Placeholder extraction
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
 * Captures `[target ↦ replacement]` in `inType` (alpha-safe substitution).
 *
 * **Purpose**: Core type transformation:
 * - Replace free `target` vars with `replacement`.
 * - **Skip bound vars**: `∀α.τ[α↦σ] = ∀α.τ`, `λ/μ` same.
 * - **Cycle guard**: `avoidInfinite` stops infinite recursion.
 * - **Structural**: Recurses on arrows/apps/records/etc.
 * - **Cons**: Now substitutes constructors too.
 *
 * Used in: `instantiateType`, enum expansion, mu unfolding, normalization.
 *
 * @param target - Var/con name to replace
 * @param replacement - New type
 * @param inType - Input type
 * @param avoidInfinite - Cycle detection set (defaults empty)
 * @returns Substituted type
 *
 * @example Basic variable capture
 * ```ts
 * import { substituteType, varType } from "system-f-omega";
 * import { arrowType, conType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), varType("b"));
 * const subst = substituteType("a", conType("Int"), ty);
 * console.log(showType(subst));  // "(Int → b)"
 * ```
 *
 * @example Skip bound variable (alpha-safe)
 * ```ts
 * import { substituteType, forallType, varType, starKind } from "system-f-omega";
 * import { arrowType } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * const subst = substituteType("a", varType("X"), poly);
 * console.log(showType(subst));  // "∀a::*. (a → b)" (skipped!)
 * ```
 *
 * @example Mu cycle guard
 * ```ts
 * import { substituteType, muType, varType, tupleType } from "system-f-omega";
 *
 * const rec = muType("L", tupleType([varType("Int"), varType("L")]));
 * const avoid = new Set(["L"]);
 * const subst = substituteType("L", varType("X"), rec, avoid);
 * console.log(showType(subst));  // "μL.(Int, L)" (guarded!)
 * ```
 *
 * @example Constructor substitution
 * ```ts
 * import { substituteType, conType, appType } from "system-f-omega";
 *
 * const either = appType(conType("Either"), conType("String"));
 * const subst = substituteType("Either", conType("Result"), either);
 * console.log(showType(subst));  // "Result<String>"
 * ```
 *
 * @see {@link instantiateType} Uses for Skolemization
 * @see {@link normalizeType} Mu/enum expansion
 * @see {@link applySubstitution} Term-level counterpart
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
 * Checks if kind is concrete `*` (value-habiting types).
 *
 * **Purpose**: Guards HKT apps, record/variant fields, trait methods.
 * All "data types" must be `:: *`.
 *
 * @param kind - Kind to test
 * @returns `true` if `*`
 *
 * @example Concrete vs HKT
 * ```ts
 * import { isStarKind, starKind, arrowKind } from "system-f-omega";
 *
 * isStarKind(starKind);                    // true (Int :: *)
 * isStarKind(arrowKind(starKind, starKind));  // false (List :: * → *)
 * ```
 *
 * @see {@link kindsEqual}
 * @see {@link checkKind}
 */
export const isStarKind = (kind: Kind) => "star" in kind;

/**
 * Structural equality for kinds (recursive).
 *
 * **Purpose**: Unifies kinds in apps (`List<Int>`), polymorphism binders.
 * Alpha-equivalent: `* ≡ *`, `κ₁→κ₂ ≡ κ₁'→κ₂'`.
 *
 * @param left - First kind
 * @param right - Second kind
 * @returns `true` if equal
 *
 * @example Basic + nested
 * ```ts
 * import { kindsEqual, starKind, arrowKind } from "system-f-omega";
 *
 * kindsEqual(starKind, starKind);  // true
 *
 * const hkt1 = arrowKind(starKind, starKind);      // * → *
 * const hkt2 = arrowKind(starKind, arrowKind(starKind, starKind));  // * → (* → *)
 * kindsEqual(hkt1, hkt1);  // true
 * kindsEqual(hkt1, hkt2);  // false
 * ```
 *
 * @see {@link isStarKind} Concrete check
 * @see {@link unifyKinds} Constraint version
 */
export const kindsEqual = (left: Kind, right: Kind): boolean =>
  ("star" in left && "star" in right) ||
  ("arrow" in left &&
    "arrow" in right &&
    kindsEqual(left.arrow.from, right.arrow.from) &&
    kindsEqual(left.arrow.to, right.arrow.to));

/**
 * Infers/validates kind of `type` under context (`Γ ⊢ τ : κ`).
 *
 * **Purpose**: Ensures types are well-formed:
 * - **EVar**: Lookup `meta.kinds`.
 * - **Var/Con**: Context lookup (aliases expand).
 * - **Compounds**: Recurse + structural rules (app: func arg → result).
 * - **Lenient**: Assume `*` for unbound vars (subtyping/bottom checks).
 *
 * Dispatcher → helpers (`checkAppKind`, etc.). Errors: `unbound`, `kind_mismatch`.
 *
 * @param state - Checker state (ctx/metas)
 * @param type - Type to kind
 * @param lenient - Assume `*` for unbound (defaults `false`)
 * @returns Inferred `Kind` or error
 *
 * @example Concrete type (star)
 * ```ts
 * import { freshState, addType, checkKind, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkKind(state, { con: "Int" });
 * console.log("kind:", showKind(result.ok));  // "*"
 * ```
 *
 * @example HKT application
 * ```ts
 * import { freshState, addType, checkKind, arrowKind, appType, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkKind(state, appType(conType("List"), conType("Int")));
 * console.log("List<Int>:", showKind(result.ok));  // "*"
 * ```
 *
 * @example Type alias expansion
 * ```ts
 * import { freshState, addType, addTypeAlias, checkKind, starKind, arrowType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const result = checkKind(state, { con: "Id" });
 * console.log("Id kind:", showKind(result.ok));  // "*"
 * ```
 *
 * @example Failure: Kind mismatch
 * ```ts
 * import { freshState, addType, checkKind, arrowKind, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 *
 * const result = checkKind(state, conType("List"));  // List alone: * → *
 * console.log("error:", "kind_mismatch" in result.err);  // true
 * ```
 *
 * @example Lenient unbound
 * ```ts
 * import { freshState, checkKind, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const result = checkKind(state, varType("Unknown"), true);  // lenient=true
 * console.log("lenient:", showKind(result.ok));  // "*"
 * ```
 *
 * @see {@link isStarKind} Concrete check
 * @see {@link kindsEqual} Equality
 * @see {@link addType} Binds constructors
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
 * Alpha-equivalent structural equality after normalization (`τ₁ ≡ τ₂`).
 *
 * **Purpose**: Decidable type equality for unification guards, subsumption:
 * - **Normalize first**: Expands aliases, β-reduces, unfolds μ.
 * - **Exact**: EVar/Var/Con by name.
 * - **Spine**: Nominal apps (`Either<a,b>` pairwise args).
 * - **Alpha**: Rename binders (`∀a.τ ≡ ∀b.τ[b/a]`).
 * - **Structural**: Records/variants/tuples (labels sorted).
 *
 * Used in: Lookup, unification early-exit, trait matching.
 *
 * @param state - Checker state (normalization)
 * @param left - First type
 * @param right - Second type
 * @returns `true` if equivalent
 *
 * @example Basic + nominal spine
 * ```ts
 * import { freshState, addType, typesEqual, appType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Either", starKind).ok;
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const left = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * const right = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("Either<Int,Bool> == Either<Int,Bool>:", typesEqual(state, left, right));  // true
 * ```
 *
 * @example Alpha-equivalence (binders)
 * ```ts
 * import { freshState, typesEqual, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const left = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const right = forallType("b", starKind, arrowType(varType("b"), varType("b")));
 * console.log("∀a.a→a == ∀b.b→b:", typesEqual(state, left, right));  // true
 * ```
 *
 * @example Data structures (labels sorted)
 * ```ts
 * import { freshState, typesEqual, recordType, variantType, tupleType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const recLeft = recordType([["y", conType("Bool")], ["x", conType("Int")]]);
 * const recRight = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 * console.log("{x:Int,y:Bool} == {y:Bool,x:Int}:", typesEqual(state, recLeft, recRight));  // true
 *
 * const varLeft = variantType([["Right", conType("Bool")], ["Left", conType("Int")]]);
 * const varRight = variantType([["Left", conType("Int")], ["Right", conType("Bool")]]);
 * console.log("variant equal:", typesEqual(state, varLeft, varRight));  // true
 * ```
 *
 * @example Failure (mismatch)
 * ```ts
 * import { freshState, typesEqual, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const fn1 = arrowType(conType("Int"), conType("Bool"));
 * const fn2 = arrowType(conType("Bool"), conType("Int"));
 * console.log("Int→Bool == Bool→Int:", typesEqual(state, fn1, fn2));  // false
 * ```
 *
 * @see {@link normalizeType} Preprocessing
 * @see {@link alphaRename} Binder equivalence
 * @see {@link typesEqualSpine} Nominal spine
 * @see {@link subsumes} Uses for unification fallback
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
 * Alpha-renames free occurrences of `from` to `to` (binder-safe).
 *
 * **Purpose**: Enables alpha-equivalence in `typesEqual`:
 * - Rename free vars.
 * - **Skip shadowed binders**: `∀α.τ[α↦β] = ∀α.τ`.
 * - Structural recurse (arrow/app/record/etc.).
 *
 * Used for: `typesEqual(∀a.τ, ∀b.σ)` → rename `b→a` → compare bodies.

 * @param from - Var to rename
 * @param to - New var name
 * @param type - Input type
 * @returns Renamed type (unchanged if `from===to`)
 *
 * @example Free variable rename
 * ```ts
 * import { alphaRename, varType, arrowType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), varType("b"));
 * const renamed = alphaRename("a", "X", ty);
 * console.log(showType(renamed));  // "(X → b)"
 * ```
 *
 * @example Skip bound binder
 * ```ts
 * import { alphaRename, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * const renamed = alphaRename("a", "X", poly);
 * console.log(showType(renamed));  // "∀a::*. (a → b)" (skipped!)
 * ```
 *
 * @example Nested data structures
 * ```ts
 * import { alphaRename, recordType, varType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const rec = recordType([["x", varType("a")], ["y", conType("Int")]]);
 * const renamed = alphaRename("a", "T", rec);
 * console.log(showType(renamed));  // "{x: T, y: Int}"
 * ```
 *
 * @example Identity (no-op)
 * ```ts
 * import { alphaRename, varType } from "system-f-omega";
 *
 * const ty = varType("a");
 * const same = alphaRename("a", "a", ty);
 * console.log(showType(same));  // "a"
 * ```
 *
 * @see {@link typesEqual} Primary caller (alpha-equivalence)
 * @see {@link substituteType} Similar (no binder skip)
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
 * Core unification engine: `left ~ right` (mutates `worklist`/`subst`).
 *
 * **Purpose**: Solves type equations via worklist:
 * 1. **Normalize** + early `typesEqual`.
 * 2. **Degenerate μ** → cyclic error.
 * 3. **Bottom**: `⊥ ~ ⊥`, `⊥ ~ τ::*` (asymmetric).
 * 4. **Rigid-rigid**: `typesEqual` or mismatch.
 * 5. **Flex-rigid**: Bind meta (occurs-checked).
 * 6. **Nominal spine**: Head + arg pairs → worklist.
 * 7. **Arrows**: Bottom-domain → codomain only.
 * 8. **Structural**: Dispatch to helpers (`unifyArrowTypes`, etc.).
 *
 * Defers to worklist. Heart of inference/checking.
 *
 * @param state - Checker state
 * @param left - Left type
 * @param right - Right type
 * @param worklist - Constraint queue
 * @param subst - Mutable bindings
 * @returns `ok(null)` or error
 *
 * @example Success: Basic unification
 * ```ts
 * import { freshState, unifyTypes, solveConstraints, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, varType("a"), conType("Int"), worklist, subst);
 * solveConstraints(state, worklist, subst);
 * console.log("a:", showType(subst.get("a")!));  // "Int"
 * ```
 *
 * @example Flex-rigid binding (meta)
 * ```ts
 * import { freshState, freshMetaVar, unifyTypes, solveConstraints, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const subst = new Map<string, Type>();
 * unifyTypes(state, meta, arrowType(conType("Int"), conType("Bool")), [], subst);
 * console.log("bound:", showType(subst.get(meta.evar)!));  // "(Int → Bool)"
 * ```
 *
 * @example Nominal spine (Either args)
 * ```ts
 * import { freshState, addType, unifyTypes, solveConstraints, appType, conType, varType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Either", starKind).ok;
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const left = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * const right = appType(appType(conType("Either"), varType("a")), varType("b"));
 * const subst = new Map();
 * unifyTypes(state, left, right, [], subst);
 * solveConstraints(state, [], subst);
 * console.log("a:", showType(subst.get("a")!));  // "Int"
 * ```
 *
 * @example Bottom rules (asymmetric)
 * ```ts
 * import { freshState, unifyTypes, neverType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 *
 * unifyTypes(state, neverType, conType("Int"), [], subst);  // ok (⊥ ~ Int)
 * unifyTypes(state, conType("Int"), neverType, [], subst);  // err(mismatch)
 * ```
 *
 * @example Failure: Rigid mismatch
 * ```ts
 * import { freshState, unifyTypes, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const result = unifyTypes(state, conType("Int"), conType("Bool"), [], new Map());
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link solveConstraints} Processes worklist
 * @see {@link unifyFlex} Meta binding
 * @see {@link typesEqual} Early exit
 * @see {@link unifyArrowTypes} Arrow dispatch
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
 * Unifies type variable `varName` with `type` (rigid-flex).
 *
 * **Purpose**: `α ~ τ` for **type vars** (not metas):
 * 1. Existing subst → check equal.
 * 2. Tautology: `α ~ α`.
 * 3. `⊥` special: No bind (subtyping later).
 * 4. Occurs-check → cyclic.
 * 5. Bind: `subst.set(α, τ)`.
 *
 * Called by `unifyTypes`. Handles non-meta vars.
 *
 * @param state - Checker state
 * @param varName - Type var (`"a"`)
 * @param type - Type to unify
 * @param subst - Mutable bindings
 * @returns `ok(null)` or error
 *
 * @example Success: Bind var
 * ```ts
 * import { freshState, unifyVariable, arrowType, conType, typesEqual } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map<string, Type>();
 * const result = unifyVariable(state, "a", arrowType(conType("Int"), conType("Bool")), subst);
 * console.log("bound:", subst.has("a"));  // true
 * console.log("equal:", typesEqual(state, subst.get("a")!, arrowType(conType("Int"), conType("Bool"))));  // true
 * ```
 *
 * @example Tautology (α ~ α)
 * ```ts
 * import { freshState, unifyVariable, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const result = unifyVariable(state, "a", varType("a"), subst);
 * console.log("tautology:", "ok" in result);  // true (no bind)
 * ```
 *
 * @example Bottom special (no bind)
 * ```ts
 * import { freshState, unifyVariable, neverType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const result = unifyVariable(state, "a", neverType, subst);
 * console.log("bottom ok:", "ok" in result && !subst.has("a"));  // true
 * ```
 *
 * @example Failure: Cyclic
 * ```ts
 * import { freshState, unifyVariable, arrowType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const cyclicTy = arrowType(varType("a"), varType("Int"));
 * const subst = new Map();
 * const result = unifyVariable(state, "a", cyclicTy, subst);
 * console.log("cyclic:", "cyclic" in result.err);  // true
 * ```
 *
 * @internal Called by {@link unifyTypes}
 * @see {@link occursCheck} Cycle detection
 * @see {@link unifyMetaVar} Meta counterpart
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
 * Unifies two kinds: wrapper over `kindsEqual`.
 *
 * **Purpose**: Constraint solver primitive for kind equality.
 * Returns `kind_mismatch` on failure.
 *
 * @param left - First kind
 * @param right - Second kind
 * @returns `ok(null)` if equal
 *
 * @example Success: Equal kinds
 * ```ts
 * import { unifyKinds, starKind, arrowKind } from "system-f-omega";
 *
 * const result1 = unifyKinds(starKind, starKind);
 * console.log("star equal:", "ok" in result1);  // true
 *
 * const hkt = arrowKind(starKind, starKind);
 * const result2 = unifyKinds(hkt, hkt);
 * console.log("HKT equal:", "ok" in result2);  // true
 * ```
 *
 * @example Failure: Mismatch
 * ```ts
 * import { unifyKinds, starKind, arrowKind } from "system-f-omega";
 *
 * const result = unifyKinds(starKind, arrowKind(starKind, starKind));
 * console.log("mismatch:", "kind_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link kindsEqual} Structural check
 * @see {@link solveConstraints} Worklist consumer
 */
export function unifyKinds(left: Kind, right: Kind): Result<TypingError, null> {
  if (kindsEqual(left, right)) return ok(null);
  return err({ kind_mismatch: { expected: left, actual: right } });
}

/**
 * Occurs check for type variables: `varName` free in `type`?
 *
 * **Purpose**: Cycle detection in `unifyVariable`: blocks `a := a → Int`.
 * Skips bound vars (`∀a.τ`, `λ/μ`). Flags degenerate `μM.M`.
 *
 * @param varName - Type var (`"a"`)
 * @param type - Type to search
 * @returns `true` if free occurrence
 *
 * @example Occurs in structure
 * ```ts
 * import { occursCheck, arrowType, varType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), varType("Int"));
 * console.log("a occurs:", occursCheck("a", ty));  // true
 * ```
 *
 * @example Skipped binder
 * ```ts
 * import { occursCheck, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * console.log("outer a:", occursCheck("a", poly));  // false (bound)
 * ```
 *
 * @example Degenerate mu (cyclic)
 * ```ts
 * import { occursCheck, muType, varType } from "system-f-omega";
 *
 * const degenerate = muType("M", varType("M"));
 * console.log("degenerate:", occursCheck("X", degenerate));  // true (flags μM.M)
 * ```
 *
 * @see {@link unifyVariable} Caller
 * @see {@link occursCheckEvar} Meta-var version
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
 * Applies substitution to type (metas → solutions, vars → bindings).
 *
 * **Purpose**: Resolves `subst`/`meta.solutions` in `type`:
 * - **Metas**: `?N → sol` (follow chains).
 * - **Vars**: `α → subst(α)` (cycle-detect via `visited`).
 * - **Binders**: Shadow subst (`∀α.τ[α↦σ] = ∀α.τ[free↦σ]`).
 * - **Structural**: Recurse on compounds.
 *
 * Used post-unification: `applySubstitution(solveRes.ok, resultTy)`.
 *
 * @param state - Checker state (metas fallback)
 * @param subst - Local bindings `Map<string, Type>`
 * @param type - Input type
 * @param visited - Cycle set (defaults empty)
 * @returns Resolved type
 *
 * @example Meta resolution
 * ```ts
 * import { freshState, freshMetaVar, applySubstitution, conType, arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const subst = new Map([ [meta.evar, arrowType(conType("Int"), conType("Bool"))] ]);
 * const resolved = applySubstitution(state, subst, meta);
 * console.log("meta:", showType(resolved));  // "(Int → Bool)"
 * ```
 *
 * @example Var chain (cycle safe)
 * ```ts
 * import { freshState, applySubstitution, varType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map([
 *   ["a", { var: "b" }],
 *   ["b", conType("Int")]
 * ]);
 * const resolved = applySubstitution(state, subst, varType("a"));
 * console.log("chain:", showType(resolved));  // "Int"
 * ```
 *
 * @example Binder shadowing
 * ```ts
 * import { freshState, applySubstitution, forallType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map([["a", varType("X")]]);
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * const resolved = applySubstitution(state, subst, poly);
 * console.log("shadow:", showType(resolved));  // "∀a::*. (a → b)"
 * ```
 *
 * @example Data structures
 * ```ts
 * import { freshState, applySubstitution, recordType, varType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map([["a", conType("Int")]]);
 * const rec = recordType([["x", varType("a")], ["y", conType("Bool")]]);
 * const resolved = applySubstitution(state, subst, rec);
 * console.log("record:", showType(resolved));  // "{x: Int, y: Bool}"
 * ```
 *
 * @see {@link solveConstraints} Produces subst
 * @see {@link mergeSubsts} Combines subst
 * @see {@link applySubstitutionToTerm} Term counterpart
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
 * Bidirectional checking: `Γ ⊢ term ⇐ expectedType` (returns resolved type + subst).
 *
 * **Purpose**: Analysis mode (`⇐`):
 * - **Specialized**: Lam/tylam/trait_lam/record/tuple/inject/fold (direct rules).
 * - **Fallback**: `inferType` → `subsumes(expected, inferred)` (polymorphic/general).
 * Returns `{ type: resolvedExpected, subst }`.
 *
 * Validates + resolves metas/constraints.
 *
 * @param state - Checker state
 * @param term - Term to check
 * @param expectedType - Expected type
 * @returns Resolved type + subst, or error
 *
 * @example Lambda: Domain unify + body check
 * ```ts
 * import { freshState, addType, checkType, lamTerm, varTerm, arrowType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, id, expected);
 * console.log("lam ok:", "ok" in result);  // true
 * ```
 *
 * @example Record: Field-by-field
 * ```ts
 * import { freshState, addType, checkType, recordTerm, conTerm, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const recTerm = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 * const expected = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 * const result = checkType(state, recTerm, expected);
 * console.log("record ok:", "ok" in result);  // true
 * ```
 *
 * @example Subsumption fallback (poly)
 * ```ts
 * import { freshState, addType, checkType, tylamTerm, lamTerm, varTerm, forallType, arrowType, varType, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, polyId, expected);
 * console.log("subsumption ok:", "ok" in result);  // true
 * ```
 *
 * @example Tylam: Kind + alpha-rename
 * ```ts
 * import { freshState, checkType, tylamTerm, lamTerm, varTerm, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const tyLam = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = forallType("α", starKind, arrowType(varType("α"), varType("α")));
 * const result = checkType(state, tyLam, expected);
 * console.log("tylam ok:", "ok" in result);  // true
 * ```
 *
 * @example Failure: Type mismatch
 * ```ts
 * import { freshState, addType, checkType, conTerm, arrowType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const num = conTerm("42", conType("Int"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, num, expected);
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link inferType} Synthesis counterpart
 * @see {@link subsumes} Fallback subtyping
 * @see {@link inferTypeWithMode} Dispatcher
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
 * Synthesizes type: `Γ ⊢ term ⇒ τ` (inference mode).
 *
 * **Purpose**: Dispatcher for term-specific inference rules:
 * - **Primitives**: Var/con lookup, lam/app, let.
 * - **Poly**: Tylam/tyapp/trait-lam/app.
 * - **Data**: Record/project/inject/match/tuple/fold.
 * - **Traits**: Dict/trait-app/method.
 *
 * Recursive. Errors bubble from helpers.
 *
 * @param state - Checker state
 * @param term - Term to infer
 * @returns Inferred `Type` or error
 *
 * @example Variable lookup
 * ```ts
 * import { freshState, addType, addTerm, inferType, varTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", { con: { name: "42", type: conType("Int") } }).ok;
 *
 * const result = inferType(state, varTerm("x"));
 * console.log("var:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Lambda + app
 * ```ts
 * import { freshState, addType, inferType, lamTerm, appTerm, varTerm, conType, arrowType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result1 = inferType(state, id);
 * console.log("lam:", showType(result1.ok));  // "(Int → Int)"
 *
 * const app = appTerm(id, { con: { name: "0", type: conType("Int") } });
 * const result2 = inferType(state, app);
 * console.log("app:", showType(result2.ok));  // "Int"
 * ```
 *
 * @example Record projection
 * ```ts
 * import { freshState, addType, inferType, recordTerm, projectTerm, conTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const rec = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 * const proj = projectTerm(rec, "x");
 * const result = inferType(state, proj);
 * console.log("project:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Match on enum
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, variantPattern, varPattern, conTerm, appType, conType, tuplePattern, wildcardPattern, starKind } from "system-f-omega";
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
 *   [variantPattern("None", tuplePattern([])), conTerm("0", conType("Int"))],
 *   [variantPattern("Some", tuplePattern([varPattern("x"), wildcardPattern()])), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("match:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link checkType} Checking counterpart
 * @see {@link inferTypeWithMode} Bidirectional dispatcher
 * @see {@link inferLamType} Lambda rule
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
 * Extracts spine head (constructor) from left-associated applications.
 *
 * **Purpose**: Deconstructs nominal types: `Either<Int,Bool>` → `Either`.
 * Used with `getSpineArgs` in unification, enum lookup, `showType`.
 *
 * @param ty - Possibly nested app type
 * @returns Head type (con/var)
 *
 * @example Nested nominal app
 * ```ts
 * import { getSpineHead, appType, conType } from "system-f-omega";
 *
 * const either = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("head:", showType(getSpineHead(either)));  // "Either"
 * ```
 *
 * @example Single app
 * ```ts
 * import { getSpineHead, appType, conType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log("head:", showType(getSpineHead(listInt)));  // "List"
 * ```
 *
 * @example Non-app
 * ```ts
 * import { getSpineHead, conType, arrowType } from "system-f-omega";
 *
 * console.log("con:", showType(getSpineHead(conType("Int"))));       // "Int"
 * console.log("arrow:", showType(getSpineHead(arrowType(conType("Int"), conType("Bool")))));  // "(Int → Bool)"
 * ```
 *
 * @internal Used by {@link unifyTypes}, {@link checkPattern}
 * @see {@link getSpineArgs} Args extractor
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
 * Synthesizes HKT constructor from structural variant (infer self-type).
 *
 * **Purpose**: Converts `<Left: a | Right: b>` → `λt0.λt1.<Left:t0|Right:t1>`.
 * Peels `selfKind` → arg kinds/names → nest lambdas inside-out.
 * Used to infer enum constructors from patterns.
 *
 * @param vtype - Structural variant
 * @param selfKind - Target kind (e.g., `* → *`)
 * @returns Lambda type constructor
 *
 * @example Unary variant → * → *
 * ```ts
 * import { createVariantLambda, variantType, starKind, arrowKind, lamType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const v = variantType([["None", { tuple: [] }], ["Some", conType("a")]]);
 * const lambda = createVariantLambda(v, arrowKind(starKind, starKind));
 * console.log(showType(lambda));  // "λt0::*. <None: ⊥ | Some: t0>"
 * ```
 *
 * @example Binary → * → * → *
 * ```ts
 * import { createVariantLambda, variantType, starKind, arrowKind } from "system-f-omega";
 * import { tupleType, varType } from "system-f-omega";
 *
 * const v = variantType([
 *   ["Left", varType("l")],
 *   ["Right", varType("r")]
 * ]);
 * const lambda = createVariantLambda(v, arrowKind(starKind, arrowKind(starKind, starKind)));
 * console.log(showType(lambda));  // "λt1::*. λt0::*. <Left: t0 | Right: t1>"
 * ```
 *
 * @example Non-variant passthrough
 * ```ts
 * import { createVariantLambda, conType, starKind } from "system-f-omega";
 *
 * const ty = conType("Int");
 * const result = createVariantLambda(ty, starKind);
 * console.log("passthrough:", showType(result));  // "Int"
 * ```
 *
 * @internal Used by {@link inferSelfFromArgument}
 * @see {@link inferSelfFromArgument} Pattern inference
 */
export function createVariantLambda(vtype: Type, selfKind: Kind): Type {
  if (!("variant" in vtype)) return vtype;

  // 1️⃣ Determine argument kinds by peeling arrows
  const argKinds: Kind[] = [];
  let k: Kind = selfKind;
  while ("arrow" in k) {
    argKinds.push(k.arrow.from);
    k = k.arrow.to;
  }

  // 2️⃣ Synthesize variable names: t0, t1, ...
  const argNames = argKinds.map((_, i) => `t${i}`);

  // 3️⃣ Build λ abstractions from inside out
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
 * Collects unbound meta-variables (`?N` without solutions) in `ty`.
 *
 * **Purpose**: Finds unsolved evars for generalization, error reporting.
 * Recurses structurally, skips solved metas.
 *
 * @param state - Checker state (solutions lookup)
 * @param ty - Type to scan
 * @param metas - Accumulator set (defaults empty)
 * @returns Array of unbound evar names
 *
 * @example Single unbound meta
 * ```ts
 * import { freshState, freshMetaVar, getUnboundMetas } from "system-f-omega";
 * import { arrowType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * const ty = arrowType(meta, meta);
 * const unbound = getUnboundMetas(state, ty);
 * console.log("unbound:", unbound);  // ["?0"]
 * ```
 *
 * @example Solved vs unbound
 * ```ts
 * import { freshState, freshMetaVar, getUnboundMetas, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta1 = freshMetaVar(state.meta);  // ?0 unbound
 * state.meta.solutions.set(meta1.evar, conType("Int"));  // Solved
 * const meta2 = freshMetaVar(state.meta);  // ?1 unbound
 * const unbound = getUnboundMetas(state, meta2);
 * console.log("unbound:", unbound);  // ["?1"]
 * ```
 *
 * @example Nested data
 * ```ts
 * import { freshState, freshMetaVar, getUnboundMetas, recordType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta1 = freshMetaVar(state.meta);
 * const meta2 = freshMetaVar(state.meta);
 * const rec = recordType([["x", meta1], ["y", meta2]]);
 * const unbound = getUnboundMetas(state, rec);
 * console.log("record metas:", unbound);  // ["?0", "?1"]
 * ```
 *
 * @internal Utility for generalization/errors
 * @see {@link freshMetaVar} Creates metas
 * @see {@link solveMetaVar} Solves metas
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
 * Solves constraint worklist: processes until empty.
 *
 * **Purpose**: Unification engine: `while(constraints) processConstraint()`.
 * Mutates `subst`. Short-circuits on first error.
 *
 * Core solver for inference/checking.
 *
 * @param state - Checker state
 * @param worklist - Constraints to solve
 * @param subst - Bindings (mutated, defaults empty)
 * @returns Final `subst` or first error
 *
 * @example Success: Simple type equality
 * ```ts
 * import { freshState, solveConstraints, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [typeEq({ var: "a" }, conType("Int"))];
 * const subst = new Map<string, Type>();
 * const result = solveConstraints(state, worklist, subst);
 * console.log("ok:", "ok" in result);  // true
 * console.log("a:", showType(subst.get("a")!));  // "Int"
 * ```
 *
 * @example Failure: Kind mismatch
 * ```ts
 * import { freshState, solveConstraints, kindEq, starKind, arrowKind } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist = [kindEq(starKind, arrowKind(starKind, starKind))];
 * const result = solveConstraints(state, worklist);
 * console.log("error:", "kind_mismatch" in result.err);  // true
 * ```
 *
 * @example Chained unification (worklist growth)
 * ```ts
 * import { freshState, solveConstraints, unifyTypes, arrowType, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const worklist: Constraint[] = [];
 * const subst = new Map<string, Type>();
 * unifyTypes(state, varType("a"), arrowType(conType("Int"), conType("Bool")), worklist, subst);
 * const result = solveConstraints(state, worklist, subst);
 * console.log("chained ok:", "ok" in result);  // true
 * ```
 *
 * @example Empty worklist
 * ```ts
 * import { freshState, solveConstraints } from "system-f-omega";
 *
 * const state = freshState();
 * const result = solveConstraints(state, []);
 * console.log("empty ok:", "ok" in result && result.ok.size === 0);  // true
 * ```
 *
 * @see {@link processConstraint} Constraint dispatcher
 * @see {@link typeEq} Type constraint
 * @see {@link unifyTypes} Adds to worklist
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
 * Dispatches constraint processing (worklist solver step).
 *
 * **Purpose**: Handles each `Constraint` variant:
 * - `type_eq`: Apply subst/normalize → `unifyTypes` (recursive).
 * - `kind_eq`: `unifyKinds`.
 * - `has_kind`: Subst → `checkKind` → add `kindEq`.
 * - `has_type`: `inferType` → add `typeEq`.
 *
 * Called by `solveConstraints` in loop.
 *
 * @param state - Checker state
 * @param constraint - Single constraint
 * @param worklist - Queue (mutated by generators)
 * @param subst - Bindings (mutated)
 * @returns `ok(null)` or error
 *
 * @example type_eq: Unification
 * ```ts
 * import { freshState, processConstraint, typeEq, varType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map<string, Type>();
 * const worklist: Constraint[] = [];
 * const result = processConstraint(state, typeEq(varType("a"), conType("Int")), worklist, subst);
 * console.log("type_eq ok:", "ok" in result);  // true
 * console.log("bound:", subst.has("a"));       // true
 * ```
 *
 * @example kind_eq: Success/failure
 * ```ts
 * import { freshState, processConstraint, kindEq, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const worklist = [];
 *
 * const eqOk = processConstraint(state, kindEq(starKind, starKind), worklist, subst);
 * console.log("kind_eq ok:", "ok" in eqOk);  // true
 *
 * const eqErr = processConstraint(state, kindEq(starKind, { arrow: { from: starKind, to: starKind } }), [], new Map());
 * console.log("kind mismatch:", "kind_mismatch" in eqErr.err);  // true
 * ```
 *
 * @example has_kind: Defers to kindEq
 * ```ts
 * import { freshState, processConstraint, hasKind, conType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const worklist: Constraint[] = [];
 * const result = processConstraint(state, hasKind(conType("Int"), starKind, state), worklist, subst);
 * console.log("has_kind ok:", "ok" in result);  // true
 * console.log("worklist grew:", worklist.length > 0);  // true (kindEq added)
 * ```
 *
 * @example has_type: Defers to typeEq
 * ```ts
 * import { freshState, processConstraint, hasType, lamTerm, varTerm, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const subst = new Map();
 * const worklist: Constraint[] = [];
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = processConstraint(state, hasType(id, expected, state), worklist, subst);
 * console.log("has_type ok:", "ok" in result);  // true
 * console.log("worklist grew:", worklist.length > 0);  // true (typeEq added)
 * ```
 *
 * @internal Called by {@link solveConstraints}
 * @see {@link typeEq} Type constraint
 * @see {@link unifyTypes} Recursive unifier
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
 * Top-level type inference: `Γ ⊢ term : τ` (alias for `inferType`).
 *
 * **Purpose**: Convenience entrypoint. Use directly or via `inferTypeWithMode`.
 *
 * @param state - Checker state
 * @param term - Term to infer
 * @returns Inferred type or error
 *
 * @see {@link inferType} Implementation
 * @see {@link inferTypeWithMode} Bidirectional
 * @see {@link checkType} Checking mode
 */
export const typeCheck = inferType;

/**
 * Constraint-based type inference: `Γ ⊢ term : ?result`.
 *
 * **Purpose**: Meta-inference via worklist: `hasType(term, $result, state)` → solve.
 * Fallback to `inferType` if unsolved. For complex scenarios (deferred solving).
 *
 * @param state - Checker state
 * @param term - Term to infer
 * @returns Solved `$result` or fallback inference
 *
 * @example Success: Extracts $result
 * ```ts
 * import { freshState, addType, typecheckWithConstraints, lamTerm, varTerm, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = typecheckWithConstraints(state, id);
 * console.log("constraint:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example With bindings (let-like)
 * ```ts
 * import { freshState, addType, addTerm, typecheckWithConstraints, appTerm, varTerm, conTerm, conType, starKind } from "system-f-omega";
 * import { lamTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "id", lamTerm("x", conType("Int"), varTerm("x"))).ok;
 *
 * const app = appTerm(varTerm("id"), conTerm("0", conType("Int")));
 * const result = typecheckWithConstraints(state, app);
 * console.log("app:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Fallback (no constraints solved)
 * ```ts
 * import { freshState, typecheckWithConstraints, conTerm, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const num = conTerm("42", conType("Int"));
 * const result = typecheckWithConstraints(state, num);
 * console.log("fallback:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link inferType} Fallback implementation
 * @see {@link hasType} Generated constraint
 * @see {@link solveConstraints} Solver
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
 * Normalizes types: expands aliases/enums, β-reduces apps, unfolds μ (cycle-safe).
 *
 * **Purpose**: Simplifies to core form:
 * - **Aliases**: Expand param-matching (`Id<Int>` → `Int`).
 * - **Enums**: Nominal → structural variant (recursive → `μX.<...X...>`).
 * - **Apps**: β-reduce `(λt.τ) σ` → `τ[t↦σ]`.
 * - **Cycles**: Guard `seen` → unchanged/⊥.
 * - **Metas**: Follow solutions.
 *
 * Used everywhere: unification, equality, printing, checking.
 *
 * @param state - Checker state (ctx/metas)
 * @param ty - Input type
 * @param seen - Cycle set (defaults empty)
 * @returns Normalized type
 *
 * @example Alias expansion
 * ```ts
 * import { freshState, addType, addTypeAlias, normalizeType, conType, varType, starKind, appType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const idInt = appType(conType("Id"), conType("Int"));
 * const norm = normalizeType(state, idInt);
 * console.log("alias:", showType(norm));  // "Int"
 * ```
 *
 * @example Enum expansion (non-recursive)
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind } from "system-f-omega";
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
 * const norm = normalizeType(state, optInt);
 * console.log("enum:", showType(norm));  // "<None: ⊥ | Some: Int>"
 * ```
 *
 * @example Recursive enum → μ
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind, varType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const norm = normalizeType(state, listInt);
 * console.log("recursive:", showType(norm));  // "μX0.<Nil: ⊥ | Cons: (Int, X0<Int>)>"
 * ```
 *
 * @example Beta-reduction (app lam)
 * ```ts
 * import { freshState, normalizeType, lamType, appType, varType, starKind, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const idLam = lamType("t", starKind, varType("t"));
 * const idInt = appType(idLam, conType("Int"));
 * const norm = normalizeType(state, idInt);
 * console.log("beta:", showType(norm));  // "Int"
 * ```
 *
 * @see {@link substituteType} Used in expansions
 * @see {@link getSpineArgs} Nominal spine
 * @see {@link typesEqual} Calls normalize
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
 * Instantiates bounded forall + resolves trait dictionaries.
 *
 * **Purpose**: `∀{C}. τ` → `τ[α↦?N]` + `checkTraitConstraints(C[α↦?N])`.
 * Non-bounded: Passthrough `{type: ty, dicts: []}`.
 *
 * Used for trait app auto-resolution.
 *
 * @param state - Checker state
 * @param ty - Bounded forall type
 * @returns `{ type: instantiatedBody, dicts: Term[] }` or error
 *
 * @example Success: Resolves constraints
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, conType, boundedForallType, instantiateWithTraits, starKind, arrowType, lamTerm, varTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: conType("Int") }], arrowType(varType("a"), conType("Int")));
 * const result = instantiateWithTraits(state, bounded);
 * console.log("success:", "ok" in result && result.ok.dicts.length === 1);  // true
 * ```
 *
 * @example Passthrough: Non-bounded
 * ```ts
 * import { freshState, instantiateWithTraits, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const simple = arrowType(conType("Int"), conType("Bool"));
 * const result = instantiateWithTraits(state, simple);
 * console.log("passthrough:", "ok" in result && result.ok.dicts.length === 0);  // true
 * ```
 *
 * @example Failure: Missing impl
 * ```ts
 * import { freshState, addType, addTraitDef, boundedForallType, instantiateWithTraits, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")]]).ok;
 * // No Eq<String>!
 *
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: conType("String") }], conType("String"));
 * const result = instantiateWithTraits(state, bounded);
 * console.log("missing:", "missing_trait_impl" in result.err);  // true
 * ```
 *
 * @see {@link checkTraitConstraints} Resolves dicts
 * @see {@link autoInstantiate} Uses for trait apps
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
 * Auto-instantiates polymorphic terms: applies type args + trait dicts.
 *
 * **Purpose**: Convenience: `polyTerm` → `polyTerm[?N] with dicts` (quantifier-free).
 * - **Forall**: Fresh `?N` → `tyappTerm` → substitute.
 * - **Bounded**: `instantiateWithTraits` → `traitAppTerm(?N, dicts)`.
 *
 * Used for implicit application of polymorphic values/dicts.
 *
 * @param state - Checker state
 * @param term - Possibly polymorphic term
 * @returns `{ term: instantiated, type: monomorphic }`
 *
 * @example Forall: Auto-tyapp
 * ```ts
 * import { freshState, inferType, autoInstantiate, tylamTerm, lamTerm, varTerm, varType, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const result = autoInstantiate(state, polyId);
 * console.log("instantiated:", showTerm(result.ok.term));  // "Λa::*. λx:a. x [?0]"
 * console.log("type:", showType(result.ok.type));         // "?0 → ?0"
 * ```
 *
 * @example Bounded forall: Auto-trait-app
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, autoInstantiate, traitLamTerm, conType, starKind, arrowType, lamTerm, varTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), dict));
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: { var: "Self" } }], arrowType(varType("Self"), conType("Int")));
 * const result = autoInstantiate(state, traitLam);
 * console.log("trait-app:", "ok" in result && result.ok.dicts.length > 0);  // true
 * ```
 *
 * @example Failure: Missing trait impl
 * ```ts
 * import { freshState, addType, addTraitDef, traitLamTerm, autoInstantiate, starKind, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "String", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", varType("Bool")]]).ok;
 * // No Eq<String>!
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: conType("String") }], varType("Self"));
 * const result = autoInstantiate(state, traitLam);
 * console.log("missing impl:", "missing_trait_impl" in result.err);  // true
 * ```
 *
 * @example Mixed: Forall + bounded
 * ```ts
 * import { freshState, autoInstantiate, tylamTerm, traitLamTerm } from "system-f-omega";
 * // Complex setup omitted - combines tyapp + trait-app
 * ```
 *
 * @see {@link instantiateWithTraits} Trait instantiation
 * @see {@link inferType} Initial type
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
 * Recursively resolves meta-vars in `ty` via `meta.solutions` (arrow-only recurse).
 *
 * **Purpose**: Eliminates solved `?N` (follow chains). Partial: only arrows recurse fully.
 *
 * @param state - Checker state
 * @param ty - Type with metas
 * @returns Resolved type (unresolved metas unchanged)
 *
 * @example Resolved meta
 * ```ts
 * import { freshState, freshMetaVar, resolveMetaVars, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * state.meta.solutions.set(meta.evar, conType("Int"));
 * const resolved = resolveMetaVars(state, meta);
 * console.log("resolved:", showType(resolved));  // "Int"
 * ```
 *
 * @example Arrow chain
 * ```ts
 * import { freshState, freshMetaVar, resolveMetaVars, arrowType, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta1 = freshMetaVar(state.meta);  // ?0
 * const meta2 = freshMetaVar(state.meta);  // ?1
 * state.meta.solutions.set(meta1.evar, conType("Int"));
 * state.meta.solutions.set(meta2.evar, arrowType(meta1, conType("Bool")));
 * const resolved = resolveMetaVars(state, meta2);
 * console.log("chain:", showType(resolved));  // "(Int → Bool)"
 * ```
 *
 * @example Unresolved meta
 * ```ts
 * import { freshState, freshMetaVar, resolveMetaVars } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);  // No solution
 * const resolved = resolveMetaVars(state, meta);
 * console.log("unresolved:", showType(resolved));  // "?0"
 * ```
 *
 * @internal Partial resolver (arrows only)
 * @see {@link applySubstitution} Full substitution
 * @see {@link freshMetaVar} Creates metas
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
 * Computes kind arity: number of arguments until `*`.
 *
 * **Purpose**: Counts HKT parameters: `* → *` → 1, `* → (* → *)` → 2.
 * Used for enum/alias arity matching, trait param validation.
 *
 * @param kind - Input kind
 * @returns Arity (0 for `*`)
 *
 * @example Base cases
 * ```ts
 * import { kindArity, starKind, arrowKind } from "system-f-omega";
 *
 * console.log("star:", kindArity(starKind));  // 0
 * console.log("unary:", kindArity(arrowKind(starKind, starKind)));  // 1
 * ```
 *
 * @example Nested HKT
 * ```ts
 * import { kindArity, starKind, arrowKind } from "system-f-omega";
 *
 * const binary = arrowKind(starKind, arrowKind(starKind, starKind));
 * console.log("binary:", kindArity(binary));  // 2
 * ```
 *
 * @internal HKT utility
 * @see {@link inferDictType} Trait arity
 * @see {@link addEnum} Param matching
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
 * Checks if `type` contains unbound meta-variables (unsolved `?N`).
 *
 * **Purpose**: Detects inference incompleteness (generalization guard).
 * Recurses structurally. Used for error reporting, generalization.
 *
 * @param state - Checker state (solutions lookup)
 * @param type - Type to scan
 * @returns `true` if any unbound meta
 *
 * @example Unbound meta
 * ```ts
 * import { freshState, freshMetaVar, hasUnboundMetas } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * console.log("unbound:", hasUnboundMetas(state, meta));  // true
 * ```
 *
 * @example Solved meta
 * ```ts
 * import { freshState, freshMetaVar, hasUnboundMetas, conType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta = freshMetaVar(state.meta);
 * state.meta.solutions.set(meta.evar, conType("Int"));
 * console.log("solved:", hasUnboundMetas(state, meta));  // false
 * ```
 *
 * @example Nested unbound
 * ```ts
 * import { freshState, freshMetaVar, hasUnboundMetas, recordType } from "system-f-omega";
 *
 * const state = freshState();
 * const meta1 = freshMetaVar(state.meta);
 * const meta2 = freshMetaVar(state.meta);
 * const rec = recordType([["x", meta1], ["y", meta2]]);
 * console.log("nested:", hasUnboundMetas(state, rec));  // true
 * ```
 *
 * @example No metas
 * ```ts
 * import { freshState, hasUnboundMetas, conType } from "system-f-omega";
 *
 * const state = freshState();
 * console.log("concrete:", hasUnboundMetas(state, conType("Int")));  // false
 * ```
 *
 * @internal Utility for generalization
 * @see {@link getUnboundMetas} Collects names
 * @see {@link freshMetaVar} Creates metas
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
 * Collects **free** type variables in `type` (skips bound in ∀/λ).
 *
 * **Purpose**: FTV for dependency analysis, renaming, generalization.
 * Recurses structurally, shadows binders.
 *
 * @param type - Input type
 * @param vars - Accumulator set (defaults empty)
 * @returns Array of free var names
 *
 * @example Free vars in arrow
 * ```ts
 * import { collectTypeVars, arrowType, varType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), varType("b"));
 * console.log("free:", collectTypeVars(ty));  // ["a", "b"]
 * ```
 *
 * @example Skips forall binder
 * ```ts
 * import { collectTypeVars, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * console.log("free:", collectTypeVars(poly));  // ["b"] (a bound)
 * ```
 *
 * @example Nested data
 * ```ts
 * import { collectTypeVars, recordType, varType } from "system-f-omega";
 *
 * const rec = recordType([["x", varType("a")], ["y", varType("b")]]);
 * console.log("record:", collectTypeVars(rec));  // ["a", "b"]
 * ```
 *
 * @example No free vars
 * ```ts
 * import { collectTypeVars } from "system-f-omega";
 *
 * console.log("concrete:", collectTypeVars({ con: "Int" }));  // []
 * ```
 *
 * @internal FTV utility
 * @see {@link computeFreeTypes} Full free names
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
 * Constructs arrow kind `from → to`.
 *
 * **Purpose**: HKT constructors: `* → *` (List), `* → (* → *)` (nested).
 * Used in `addType`, polymorphism binders.
 *
 * @param from - Domain kind
 * @param to - Codomain kind
 * @returns `{ arrow: { from, to } }`
 *
 * @example Unary HKT
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const listKind = arrowKind(starKind, starKind);
 * console.log("List:", showKind(listKind));  // "(* → *)"
 * ```
 *
 * @example Nested HKT
 * ```ts
 * import { arrowKind, starKind, showKind } from "system-f-omega";
 *
 * const nested = arrowKind(starKind, arrowKind(starKind, starKind));
 * console.log("nested:", showKind(nested));  // "(* → ((* → *) → *))"
 * ```
 *
 * @example Usage: addType
 * ```ts
 * import { freshState, addType, arrowKind, starKind } from "system-f-omega";
 *
 * const state = addType(freshState(), "List", arrowKind(starKind, starKind));
 * console.log("added:", "ok" in state);  // true
 * ```
 *
 * @see {@link starKind} Base kind
 * @see {@link kindsEqual} Equality
 * @see {@link addType} Binds HKTs
 */
export const arrowKind = (from: Kind, to: Kind): Kind => ({
  arrow: { from, to },
});

/**
 * Constructs type variable `{ var: name }`.
 *
 * **Purpose**: Free/bound vars in arrows, foralls, records.
 *
 * @param name - Variable name (`"a"`, `"Self"`)
 * @returns `{ var: name }`
 *
 * @example Basic var
 * ```ts
 * import { varType, showType } from "system-f-omega";
 *
 * console.log("a:", showType(varType("a")));  // "a"
 * ```
 *
 * @example Arrow/foralls
 * ```ts
 * import { varType, arrowType, forallType, starKind, showType } from "system-f-omega";
 *
 * console.log("a→b:", showType(arrowType(varType("a"), varType("b"))));  // "(a → b)"
 * console.log("∀a.a:", showType(forallType("a", starKind, varType("a"))));  // "∀a::*. a"
 * ```
 *
 * @see {@link conType} Concrete types
 * @see {@link arrowType} Usage
 * @see {@link forallType} Bound vars
 */
export const varType = (name: string): VarType => ({ var: name });

/**
 * Constructs function type `from → to`.
 *
 * **Purpose**: Lambda/trait method types. Core to typing.
 *
 * @param from - Domain type
 * @param to - Codomain type
 * @returns `{ arrow: { from, to } }`
 *
 * @example Basic function
 * ```ts
 * import { arrowType, conType, showType } from "system-f-omega";
 *
 * console.log("Int→Bool:", showType(arrowType(conType("Int"), conType("Bool"))));  // "(Int → Bool)"
 * ```
 *
 * @example Nested/poly
 * ```ts
 * import { arrowType, varType, conType, showType } from "system-f-omega";
 *
 * console.log("a→b:", showType(arrowType(varType("a"), varType("b"))));  // "(a → b)"
 * console.log("((a→b)→c):", showType(arrowType(arrowType(varType("a"), varType("b")), conType("c"))));  // "((a → b) → c)"
 * ```
 *
 * @example Lambda inference
 * ```ts
 * import { freshState, addType, inferType, lamTerm, varTerm, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const result = inferType(state, id);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @see {@link lamTerm} Usage
 * @see {@link inferLamType} Infers arrows
 * @see {@link varType} Domain/codomain vars
 */
export const arrowType = (from: Type, to: Type): Type => ({
  arrow: { from, to },
});

/**
 * Constructs universal quantifier `∀name::kind. body`.
 *
 * **Purpose**: Polymorphism: type variables, trait bounds.
 *
 * @param name - Bound var (`"a"`, `"Self"`)
 * @param kind - Var kind (`*`, `*→*`)
 * @param body - Body type
 * @returns `{ forall: { var, kind, body } }`
 *
 * @example Basic polymorphism
 * ```ts
 * import { forallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * console.log("∀a.a→a:", showType(forallType("a", starKind, arrowType(varType("a"), varType("a")))));  // "∀a::*. (a → a)"
 * ```
 *
 * @example HKT bound
 * ```ts
 * import { forallType, varType, arrowType, arrowKind, starKind, showType } from "system-f-omega";
 *
 * console.log("∀F:F<A>:", showType(forallType("F", arrowKind(starKind, starKind), varType("F"))));  // "∀F::(* → *). F"
 * ```
 *
 * @example Tylam inference
 * ```ts
 * import { freshState, inferType, tylamTerm, lamTerm, varTerm, forallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const result = inferType(state, polyId);
 * console.log("inferred:", showType(result.ok));  // "∀a::*. (a → a)"
 * ```
 *
 * @see {@link tylamTerm} Term counterpart
 * @see {@link instantiateType} Skolemizes
 * @see {@link starKind} Common kind
 */
export const forallType = (name: string, kind: Kind, body: Type) => ({
  forall: { var: name, kind, body },
});

/**
 * Constructs type application `func arg`.
 *
 * **Purpose**: HKT saturation: `List<Int>`, `Either<Int,Bool>`.
 *
 * @param func - Type constructor/function
 * @param arg - Argument type
 * @returns `{ app: { func, arg } }`
 *
 * @example Unary HKT
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * console.log("List<Int>:", showType(listInt));  // "List<Int>"
 * ```
 *
 * @example Nested app (binary)
 * ```ts
 * import { appType, conType, showType } from "system-f-omega";
 *
 * const eitherIntBool = appType(appType(conType("Either"), conType("Int")), conType("Bool"));
 * console.log("Either<Int,Bool>:", showType(eitherIntBool));  // "Either<Int, Bool>"
 * ```
 *
 * @example Normalized spine
 * ```ts
 * import { freshState, addType, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", starKind).ok;
 * const listInt = appType(conType("List"), conType("Int"));
 * const norm = normalizeType(state, listInt);
 * console.log("normalized:", showType(norm));  // "List<Int>"
 * ```
 *
 * @see {@link getSpineArgs} Deconstructs
 * @see {@link normalizeType} β-reduces apps
 * @see {@link showType} Pretty-prints
 */
export const appType = (func: Type, arg: Type) => ({ app: { func, arg } });

/**
 * Constructs type lambda `λname::kind. body` (HKT constructor).
 *
 * **Purpose**: Type functions: `λt::*. t → t` (id), `λF::(*→*). F<Int>`.
 *
 * @param name - Bound var
 * @param kind - Var kind
 * @param body - Body type
 * @returns `{ lam: { var, kind, body } }`
 *
 * @example Basic type lambda
 * ```ts
 * import { lamType, varType, starKind, showType } from "system-f-omega";
 *
 * const idLam = lamType("t", starKind, varType("t"));
 * console.log("λt.t:", showType(idLam));  // "λt::*. t"
 * ```
 *
 * @example HKT constructor
 * ```ts
 * import { lamType, arrowKind, starKind, varType, showType } from "system-f-omega";
 *
 * const listLam = lamType("F", arrowKind(starKind, starKind), varType("F"));
 * console.log("λF:F:", showType(listLam));  // "λF::(* → *). F"
 * ```
 *
 * @example App + normalize
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
 * @see {@link appType} Apply lambdas
 * @see {@link normalizeType} β-reduces
 * @see {@link tylamTerm} Term counterpart
 */
export const lamType = (name: string, kind: Kind, body: Type) => ({
  lam: { var: name, kind, body },
});

/**
 * Constructs concrete type constructor `{ con: name }`.
 *
 * **Purpose**: Primitives/enums: `"Int"`, `"List"`, `"Either"`.
 *
 * @param con - Constructor name
 * @returns `{ con: name }`
 *
 * @example Primitive
 * ```ts
 * import { conType, showType } from "system-f-omega";
 *
 * console.log("Int:", showType(conType("Int")));  // "Int"
 * ```
 *
 * @example Type constructor
 * ```ts
 * import { conType, showType } from "system-f-omega";
 *
 * console.log("List:", showType(conType("List")));  // "List"
 * ```
 *
 * @example App usage
 * ```ts
 * import { conType, appType, showType } from "system-f-omega";
 *
 * console.log("List<Int>:", showType(appType(conType("List"), conType("Int"))));  // "List<Int>"
 * ```
 *
 * @see {@link appType} HKT saturation
 * @see {@link addType} Binds constructors
 * @see {@link addEnum} Enum heads
 */
export const conType = (con: string) => ({ con });

/**
 * Constructs record type `{ label: τ, ... }` (structural rows).
 *
 * **Purpose**: Product types with labeled fields. Supports width subsumption.
 *
 * @param record - Field list `[[label, type], ...]`
 * @returns `{ record: [[string, Type]] }`
 *
 * @example Basic record
 * ```ts
 * import { recordType, conType, showType } from "system-f-omega";
 *
 * const person = recordType([
 *   ["name", conType("String")],
 *   ["age", conType("Int")]
 * ]);
 * console.log("record:", showType(person));  // "{name: String, age: Int}"
 * ```
 *
 * @example Nested fields
 * ```ts
 * import { recordType, conType, arrowType, showType } from "system-f-omega";
 *
 * const funcRec = recordType([
 *   ["f", arrowType(conType("Int"), conType("Bool"))],
 *   ["g", conType("String")]
 * ]);
 * console.log("nested:", showType(funcRec));  // "{f: (Int → Bool), g: String}"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, recordTerm, conTerm, recordType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const recVal = recordTerm([
 *   ["x", conTerm("1", conType("Int"))],
 *   ["y", conTerm("true", conType("Bool"))]
 * ]);
 * const result = inferType(state, recVal);
 * console.log("inferred:", showType(result.ok));  // "{x: Int, y: Bool}"
 * ```
 *
 * @see {@link recordTerm} Value constructor
 * @see {@link inferRecordType} Inference rule
 * @see {@link projectTerm} Field access
 */
export const recordType = (record: [string, Type][]) => ({ record });

/**
 * Constructs variant type `<label: τ | ...>` (sum types).
 *
 * **Purpose**: Disjoint unions. Used in enum expansion, injectTerm.
 *
 * @param variant - Case list `[[label, type], ...]`
 * @returns `{ variant: [[string, Type]] }`
 *
 * @example Basic variant
 * ```ts
 * import { variantType, conType, showType } from "system-f-omega";
 *
 * const either = variantType([
 *   ["Left", conType("Int")],
 *   ["Right", conType("String")]
 * ]);
 * console.log("variant:", showType(either));  // "<Left: Int | Right: String>"
 * ```
 *
 * @example Nested cases
 * ```ts
 * import { variantType, conType, arrowType, showType } from "system-f-omega";
 *
 * const result = variantType([
 *   ["Ok", conType("Int")],
 *   ["Err", arrowType(conType("String"), conType("String"))]
 * ]);
 * console.log("nested:", showType(result));  // "<Ok: Int | Err: (String → String)>"
 * ```
 *
 * @example Enum expansion inference
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, variantType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", { tuple: [] }],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const optInt = appType(conType("Option"), conType("Int"));
 * const expanded = normalizeType(state, optInt);
 * console.log("expanded:", showType(expanded));  // "<None: ⊥ | Some: Int>"
 * ```
 *
 * @see {@link injectTerm} Variant values
 * @see {@link addEnum} Expands to variant
 * @see {@link normalizeType} Enum normalization
 */
export const variantType = (variant: [string, Type][]) => ({ variant });

/**
 * Constructs recursive mu type `μvar. body` (equi-recursive).
 *
 * **Purpose**: Fixed-points: lists, trees. Unfolds via `substituteType`.
 *
 * @param var_name - Binder (`"L"`)
 * @param body - Body (contains `var_name`)
 * @returns `{ mu: { var, body } }`
 *
 * @example Basic mu
 * ```ts
 * import { muType, varType, showType } from "system-f-omega";
 *
 * const listMu = muType("L", varType("L"));
 * console.log("μL.L:", showType(listMu));  // "μL.L"
 * ```
 *
 * @example Recursive list
 * ```ts
 * import { muType, tupleType, varType, conType, showType } from "system-f-omega";
 *
 * const listInt = muType("L", tupleType([conType("Int"), varType("L")]));
 * console.log("list:", showType(listInt));  // "μL.(Int, L)"
 * ```
 *
 * @example Enum expansion
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, muType, starKind, showType } from "system-f-omega";
 * import { tupleType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const expanded = normalizeType(state, listInt);
 * console.log("expanded:", showType(expanded));  // "μX.<Nil: ⊥ | Cons: (Int, X<Int>)>"
 * ```
 *
 * @see {@link normalizeType} Unfolds in enums
 * @see {@link foldTerm} Packs into mu
 * @see {@link inferFoldType} Typing rule
 */
export const muType = (var_name: string, body: Type): Type => ({
  mu: { var: var_name, body },
});

/**
 * Constructs tuple type `(τ₁, τ₂, ...)` (product without labels).
 *
 * **Purpose**: Unlabeled products. Zero-arity = unit `()`.
 *
 * @param elements - Tuple element types
 * @returns `{ tuple: Type[] }`
 *
 * @example Unit (empty tuple)
 * ```ts
 * import { tupleType, showType } from "system-f-omega";
 *
 * const unit = tupleType([]);
 * console.log("unit:", showType(unit));  // "()"
 * ```
 *
 * @example Basic tuple
 * ```ts
 * import { tupleType, conType, showType } from "system-f-omega";
 *
 * const pair = tupleType([conType("Int"), conType("Bool")]);
 * console.log("pair:", showType(pair));  // "(Int, Bool)"
 * ```
 *
 * @example Nested tuple
 * ```ts
 * import { tupleType, conType, showType } from "system-f-omega";
 *
 * const nested = tupleType([conType("Int"), tupleType([conType("Bool"), conType("String")])]);
 * console.log("nested:", showType(nested));  // "(Int, (Bool, String))"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, conTerm, tupleType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const tupVal = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * const result = inferType(state, tupVal);
 * console.log("inferred:", showType(result.ok));  // "(Int, Bool)"
 * ```
 *
 * @see {@link tupleTerm} Value constructor
 * @see {@link inferTupleType} Inference rule
 * @see {@link tuplePattern} Pattern matching
 */
export const tupleType = (elements: Type[]): Type => ({ tuple: elements });

/**
 * Constructs bounded universal `∀name::kind where C₁, C₂. body`.
 *
 * **Purpose**: Trait-bounded polymorphism: `∀Self::*. Eq<Self>. Self → Self`.
 *
 * @param name - Bound var (`"Self"`)
 * @param kind - Var kind
 * @param constraints - Trait bounds `[{trait: "Eq", type: τ}, ...]`
 * @param body - Body type
 * @returns `{ bounded_forall: { var, kind, constraints, body } }`
 *
 * @example Basic bounded forall
 * ```ts
 * import { boundedForallType, varType, starKind, showType } from "system-f-omega";
 *
 * const eqSelf = boundedForallType("Self", starKind, [], varType("Self"));
 * console.log("basic:", showType(eqSelf));  // "∀Self::* where . Self"
 * ```
 *
 * @example With constraints
 * ```ts
 * import { boundedForallType, varType, starKind, showType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const eqId = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Self")));
 * console.log("constrained:", showType(eqId));  // "∀Self::* where Eq<Self>. (Self → Self)"
 * ```
 *
 * @example Trait lambda checking
 * ```ts
 * import { freshState, addType, addTraitDef, checkType, traitLamTerm, boundedForallType, varType, arrowType, starKind, conType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * const expected = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * const result = checkType(state, traitLam, expected);
 * console.log("checked:", "ok" in result);  // true
 * ```
 *
 * @see {@link traitLamTerm} Term counterpart
 * @see {@link checkType} Validates bounds
 * @see {@link instantiateWithTraits} Resolves constraints
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
 * Constructs term variable `{ var: name }`.
 *
 * **Purpose**: References bound vars in lambdas/apps/lets.
 *
 * @param name - Variable name (`"x"`, `"self"`)
 * @returns `{ var: name }`
 *
 * @example Basic variable
 * ```ts
 * import { varTerm, showTerm } from "system-f-omega";
 *
 * console.log("x:", showTerm(varTerm("x")));  // "x"
 * ```
 *
 * @example Lambda usage
 * ```ts
 * import { varTerm, lamTerm, conType, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log("λx.x:", showTerm(id));  // "λx:Int.x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, addTerm, inferType, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", { con: { name: "42", type: conType("Int") } }).ok;
 *
 * const result = inferType(state, varTerm("x"));
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link lamTerm} Bound usage
 * @see {@link inferType} Lookup
 * @see {@link addTerm} Binding
 */
export const varTerm = (name: string) => ({ var: name });

/**
 * Constructs lambda `λarg:τ. body`.
 *
 * **Purpose**: Function abstraction. Infers arrow type.
 *
 * @param arg - Parameter name
 * @param type - Parameter type (annotated)
 * @param body - Body term
 * @returns `{ lam: { arg, type, body } }`
 *
 * @example Basic lambda
 * ```ts
 * import { lamTerm, conType, varTerm, showTerm } from "system-f-omega";
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * console.log("λx.x:", showTerm(id));  // "λx:Int.x"
 * ```
 *
 * @example Inference
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
 * @example Checking
 * ```ts
 * import { freshState, addType, checkType, lamTerm, varTerm, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, id, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int → Int)"
 * ```
 *
 * @see {@link inferLamType} Inference rule
 * @see {@link varTerm} Body var
 * @see {@link inferType} Usage
 */
export const lamTerm = (arg: string, type: Type, body: Term) => ({
  lam: { arg, type, body },
});

/**
 * Constructs term application `(callee arg)`.
 *
 * **Purpose**: Function application. Infers result via callee type.
 *
 * @param callee - Function term
 * @param arg - Argument term
 * @returns `{ app: { callee, arg } }`
 *
 * @example Basic application
 * ```ts
 * import { appTerm, varTerm, showTerm } from "system-f-omega";
 *
 * const app = appTerm(varTerm("f"), varTerm("x"));
 * console.log("app:", showTerm(app));  // "(f x)"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, addTerm, inferType, appTerm, varTerm, lamTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "id", lamTerm("x", conType("Int"), varTerm("x"))).ok;
 *
 * const app = appTerm(varTerm("id"), conTerm("0", conType("Int")));
 * const result = inferType(state, app);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addType, addTerm, checkType, appTerm, varTerm, lamTerm, conTerm, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "add1", lamTerm("x", conType("Int"), varTerm("x"))).ok;
 *
 * const app = appTerm(varTerm("add1"), conTerm("0", conType("Int")));
 * const expected = conType("Int");
 * const result = checkType(state, app, expected);
 * console.log("checked:", showType(result.ok.type));  // "Int"
 * ```
 *
 * @see {@link inferAppType} Inference rule
 * @see {@link lamTerm} Callee usage
 * @see {@link inferType} Full inference
 */
export const appTerm = (callee: Term, arg: Term) => ({ app: { callee, arg } });

/**
 * Constructs type lambda `Λname::kind. body` (polymorphic abstraction).
 *
 * **Purpose**: Type-level functions. Infers forall type.
 *
 * @param name - Bound type var
 * @param kind - Var kind
 * @param body - Body term
 * @returns `{ tylam: { var, kind, body } }`
 *
 * @example Basic type lambda
 * ```ts
 * import { tylamTerm, showTerm } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const polyId = tylamTerm("a", starKind, { var: "x" });
 * console.log("Λa.x:", showTerm(polyId));  // "Λa::*. x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, inferType, tylamTerm, lamTerm, varTerm, varType, starKind, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const result = inferType(state, polyId);
 * console.log("inferred:", showType(result.ok));  // "∀a::*. (a → a)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, checkType, tylamTerm, lamTerm, varTerm, varType, forallType, arrowType, starKind, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const expected = forallType("a", starKind, arrowType(varType("a"), varType("a")));
 * const result = checkType(state, polyId, expected);
 * console.log("checked:", showType(result.ok.type));  // "∀a::*. (a → a)"
 * ```
 *
 * @see {@link inferTylamType} Inference rule
 * @see {@link tyappTerm} Application
 * @see {@link forallType} Inferred type
 */
export const tylamTerm = (name: string, kind: Kind, body: Term) => ({
  tylam: { var: name, kind, body },
});
/**
 * Constructs type application `term [type]`.
 *
 * **Purpose**: Saturates type lambdas. Infers via callee forall.
 *
 * @param term - Polymorphic term (tylam)
 * @param type - Type argument
 * @returns `{ tyapp: { term, type } }`
 *
 * @example Basic type app
 * ```ts
 * import { tyappTerm, showTerm } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const app = tyappTerm({ var: "polyId" }, conType("Int"));
 * console.log("app:", showTerm(app));  // "polyId [Int]"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, inferType, tyappTerm, tylamTerm, lamTerm, varTerm, varType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const idInt = tyappTerm(polyId, conType("Int"));
 * const result = inferType(state, idInt);
 * console.log("inferred:", showType(result.ok));  // "(Int → Int)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, checkType, tyappTerm, tylamTerm, lamTerm, varTerm, varType, arrowType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * const polyId = tylamTerm("a", starKind, lamTerm("x", varType("a"), varTerm("x")));
 * const idInt = tyappTerm(polyId, conType("Int"));
 * const expected = arrowType(conType("Int"), conType("Int"));
 * const result = checkType(state, idInt, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int → Int)"
 * ```
 *
 * @see {@link inferTyappType} Inference rule
 * @see {@link tylamTerm} Callee usage
 * @see {@link inferType} Full inference
 */
export const tyappTerm = (term: Term, type: Type) => ({
  tyapp: { term, type },
});
/**
 * Constructs typed constant `{ con: { name, type } }`.
 *
 * **Purpose**: Literals/promoted constructors with explicit type.
 *
 * @param name - Constant name/value (`"42"`, `"true"`)
 * @param type - Type annotation
 * @returns `{ con: { name, type } }`
 *
 * @example Basic constant
 * ```ts
 * import { conTerm, conType, showTerm } from "system-f-omega";
 *
 * const num = conTerm("42", conType("Int"));
 * console.log("con:", showTerm(num));  // "42"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
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
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const result = inferType(state, rec);
 * console.log("record:", showType(result.ok));  // "{x: Int}"
 * ```
 *
 * @see {@link inferType} Constant lookup
 * @see {@link recordTerm} Field usage
 * @see {@link injectTerm} Variant payload
 */
export const conTerm = (name: string, type: Type) => ({ con: { name, type } });

/**
 * Constructs record value `{ label = term, ... }`.
 *
 * **Purpose**: Labeled products. Infers record type.
 *
 * @param record - Field list `[[label, term], ...]`
 * @returns `{ record: [[string, Term]] }`
 *
 * @example Basic record
 * ```ts
 * import { recordTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const person = recordTerm([
 *   ["name", conTerm("Alice", conType("String"))],
 *   ["age", conTerm("30", conType("Int"))]
 * ]);
 * console.log("record:", showTerm(person));  // "{name = Alice, age = 30}"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, recordTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "String", starKind).ok;
 *
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
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 * const result = inferType(state, proj);
 * console.log("project:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link inferRecordType} Inference rule
 * @see {@link projectTerm} Field access
 * @see {@link recordType} Type counterpart
 */
export const recordTerm = (record: [string, Term][]) => ({ record });

/**
 * Constructs record projection `record.label`.
 *
 * **Purpose**: Field access. Infers field type.
 *
 * @param record - Record term
 * @param label - Field name
 * @returns `{ project: { record, label } }`
 *
 * @example Basic projection
 * ```ts
 * import { projectTerm, recordTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 * console.log("proj:", showTerm(proj));  // "{x = 1}.x"
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
 * const proj = projectTerm(rec, "x");
 * const result = inferType(state, proj);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addType, checkType, recordTerm, projectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const proj = projectTerm(rec, "x");
 * const expected = conType("Int");
 * const result = checkType(state, proj, expected);
 * console.log("checked:", showType(result.ok.type));  // "Int"
 * ```
 *
 * @see {@link inferProjectType} Inference rule
 * @see {@link recordTerm} Record values
 * @see {@link inferType} Full inference
 */
export const projectTerm = (record: Term, label: string) => ({
  project: { record, label },
});

/**
 * Constructs variant injection `<label=value> as variant_type`.
 *
 * **Purpose**: Tagged sum values. Infers via case lookup.
 *
 * @param label - Variant label (`"Left"`, `"Some"`)
 * @param value - Payload term
 * @param variant_type - Variant/enum type
 * @returns `{ inject: { label, value, variant_type } }`
 *
 * @example Basic injection
 * ```ts
 * import { injectTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const someInt = injectTerm("Some", conTerm("42", conType("Int")), conType("Option"));
 * console.log("inject:", showTerm(someInt));  // "<Some=42> as Option"
 * ```
 *
 * @example Inference (enum)
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
 * @example Checking (wrong label)
 * ```ts
 * import { freshState, addEnum, checkType, injectTerm, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]).ok;
 *
 * const badInject = injectTerm("Bad", conTerm("42", conType("Int")), appType(conType("Option"), conType("Int")));
 * const expected = appType(conType("Option"), conType("Int"));
 * const result = checkType(state, badInject, expected);
 * console.log("error:", "invalid_variant_label" in result.err);  // true
 * ```
 *
 * @see {@link inferInjectType} Inference rule
 * @see {@link addEnum} Enum variants
 * @see {@link variantType} Structural type
 */
export const injectTerm = (label: string, value: Term, variant_type: Type) => ({
  inject: { label, value, variant_type },
});

/**
 * Constructs pattern match `match scrutinee { pat => body | ... }`.
 *
 * **Purpose**: Exhaustive destructuring. Infers common branch type.
 *
 * @param scrutinee - Value to match
 * @param cases - Pattern-body pairs
 * @returns `{ match: { scrutinee, cases } }`
 *
 * @example Basic enum match
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
 *   [variantPattern("None", varPattern("x")), conTerm("0", conType("Int"))],
 *   [variantPattern("Some", varPattern("x")), varTerm("x")]
 * ]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Checking exhaustive
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", { var: "Unit" }], ["Blue", { var: "Unit" }]]).ok;
 *
 * const patterns = [variantPattern("Red", varPattern("x")), variantPattern("Blue", varPattern("y"))];
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("exhaustive:", "ok" in result);  // true
 * ```
 *
 * @example Failure: Non-exhaustive
 * ```ts
 * import { freshState, addEnum, checkExhaustive, variantPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", { var: "Unit" }], ["Blue", { var: "Unit" }]]).ok;
 *
 * const patterns = [variantPattern("Red", varPattern("x"))];  // Missing Blue
 * const result = checkExhaustive(state, patterns, conType("Color"));
 * console.log("missing:", "missing_case" in result.err);  // true
 * ```
 *
 * @see {@link inferMatchType} Inference rule
 * @see {@link checkExhaustive} Coverage check
 * @see {@link checkPattern} Pattern validation
 */
export const matchTerm = (scrutinee: Term, cases: [Pattern, Term][]): Term => ({
  match: { scrutinee, cases },
});

/**
 * Constructs fold `fold[μ-type](term)` (packs into recursive type).
 *
 * **Purpose**: Recursive injection: wraps term matching unfolded μ-body.
 *
 * @param type - Mu type (`μX. <Cons: (a, X)>`)
 * @param term - Body term (must match unfolded type)
 * @returns `{ fold: { type, term } }`
 *
 * @example Basic fold construction
 * ```ts
 * import { foldTerm, muType, showTerm } from "system-f-omega";
 * import { tupleType, conType } from "system-f-omega";
 *
 * const listMu = muType("L", tupleType([conType("Int"), { var: "L" }]));
 * const foldVal = foldTerm(listMu, { tuple: [{ con: { name: "1", type: conType("Int") } }, { var: "prev" }] });
 * console.log("fold:", showTerm(foldVal));  // "fold[μL.(Int, L)]((1, prev))"
 * ```
 *
 * @example Inference (recursive enum)
 * ```ts
 * import { freshState, addType, addEnum, inferType, foldTerm, injectTerm, appType, conType, muType, starKind, showType } from "system-f-omega";
 * import { tupleType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const result = inferType(state, folded);
 * console.log("inferred:", showType(result.ok));  // "List<Int>"
 * ```
 *
 * @example Checking success
 * ```ts
 * import { freshState, addType, addEnum, checkType, foldTerm, injectTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), conType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const expected = listInt;
 * const result = checkType(state, folded, expected);
 * console.log("checked:", showType(result.ok.type));  // "List<Int>"
 * ```
 *
 * @example Failure: Non-mu type
 * ```ts
 * import { freshState, addType, checkType, foldTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const folded = foldTerm(conType("Int"), { var: "x" });  // Wrong mu-type
 * const expected = conType("Int");
 * const result = checkType(state, folded, expected);
 * console.log("error:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link inferFoldType} Inference rule
 * @see {@link muType} Recursive type
 * @see {@link unfoldTerm} Dual operation
 */
export const foldTerm = (type: Type, term: Term): Term => ({
  fold: { type, term },
});

/**
 * Constructs unfold `unfold(term)` (unpacks recursive mu type).
 *
 * **Purpose**: Recursive projection: extracts from folded μ-body.
 * Dual to `foldTerm`.

 * @param term - Folded mu term
 * @returns `{ unfold: term }`
 *
 * @example Basic unfold construction
 * ```ts
 * import { unfoldTerm, showTerm } from "system-f-omega";
 *
 * const unfolded = unfoldTerm({ var: "foldedList" });
 * console.log("unfold:", showTerm(unfolded));  // "unfold(foldedList)"
 * ```
 *
 * @example Inference (recursive enum)
 * ```ts
 * import { freshState, addType, addEnum, inferType, unfoldTerm, foldTerm, injectTerm, appType, conType, starKind, showType } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), conType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const unfolded = unfoldTerm(folded);
 * const result = inferType(state, unfolded);
 * console.log("inferred:", showType(result.ok));  // "(Int, List<Int>)"
 * ```
 *
 * @example Checking success
 * ```ts
 * import { freshState, addType, addEnum, checkType, unfoldTerm, foldTerm, injectTerm, appType, conType, starKind, tupleType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), conType("T"))])]
 * ], true).ok;
 *
 * const listInt = appType(conType("List"), conType("Int"));
 * const nil = injectTerm("Nil", { tuple: [] }, listInt);
 * const folded = foldTerm(listInt, nil);
 * const unfolded = unfoldTerm(folded);
 * const expected = tupleType([conType("Int"), listInt]);
 * const result = checkType(state, unfolded, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int, List<Int>)"
 * ```
 *
 * @see {@link inferUnfoldType} Inference rule
 * @see {@link foldTerm} Dual packing
 * @see {@link muType} Recursive type
 */
export const unfoldTerm = (term: Term): Term => ({
  unfold: term,
});

/**
 * Constructs tuple value `(term₁, term₂, ...)` (unlabeled product).
 *
 * **Purpose**: Unlabeled sequences. Zero-arity = unit `{}`.
 *
 * @param elements - Tuple element terms
 * @returns `{ tuple: Term[] }`
 *
 * @example Unit (empty tuple)
 * ```ts
 * import { tupleTerm, showTerm } from "system-f-omega";
 *
 * const unit = tupleTerm([]);
 * console.log("unit:", showTerm(unit));  // "()"
 * ```
 *
 * @example Basic tuple
 * ```ts
 * import { tupleTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const pair = tupleTerm([
 *   conTerm("1", conType("Int")),
 *   conTerm("true", conType("Bool"))
 * ]);
 * console.log("pair:", showTerm(pair));  // "(1, true)"
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
 * @example Projection
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
 * const proj = tupleProjectTerm(tup, 0);
 * const result = inferType(state, proj);
 * console.log("proj0:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link inferTupleType} Inference rule
 * @see {@link tupleType} Type counterpart
 * @see {@link tupleProjectTerm} Access
 */
export const tupleTerm = (elements: Term[]): Term => ({ tuple: elements });

/**
 * Constructs tuple projection `tuple.index`.
 *
 * **Purpose**: Nth element access. Infers element type.
 *
 * @param tuple - Tuple term
 * @param index - 0-based index
 * @returns `{ tuple_project: { tuple, index } }`
 *
 * @example Basic projection
 * ```ts
 * import { tupleProjectTerm, tupleTerm, conTerm, conType, showTerm } from "system-f-omega";
 *
 * const tup = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * const proj = tupleProjectTerm(tup, 0);
 * console.log("proj:", showTerm(proj));  // "((1, true)).0"
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
 * const proj = tupleProjectTerm(tup, 0);
 * const result = inferType(state, proj);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Checking success
 * ```ts
 * import { freshState, addType, checkType, tupleTerm, tupleProjectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int")), conTerm("true", conType("Bool"))]);
 * const proj = tupleProjectTerm(tup, 0);
 * const expected = conType("Int");
 * const result = checkType(state, proj, expected);
 * console.log("checked:", showType(result.ok.type));  // "Int"
 * ```
 *
 * @example Failure: Out-of-bounds (inferred)
 * ```ts
 * import { freshState, addType, inferType, tupleTerm, tupleProjectTerm, conTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const tup = tupleTerm([conTerm("1", conType("Int"))]);
 * const proj = tupleProjectTerm(tup, 1);  // Out-of-bounds
 * const result = inferType(state, proj);
 * console.log("error:", "tuple_index_out_of_bounds" in result.err);  // true
 * ```
 *
 * @see {@link inferTupleProjectType} Inference rule
 * @see {@link tupleTerm} Tuple values
 * @see {@link tupleType} Tuple types
 */
export const tupleProjectTerm = (tuple: Term, index: number): Term => ({
  tuple_project: { tuple, index },
});

/**
 * Constructs let-binding `let name = value in body`.
 *
 * **Purpose**: Non-recursive binding. Infers via `value` type in `body` context.
 *
 * @param name - Bound name
 * @param value - Value term
 * @param body - Body term (uses `name`)
 * @returns `{ let: { name, value, body } }`
 *
 * @example Basic let construction
 * ```ts
 * import { letTerm, conTerm, conType, varTerm, showTerm } from "system-f-omega";
 *
 * const letExpr = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * console.log("let:", showTerm(letExpr));  // "let x = 42 in x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, inferType, letTerm, conTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const letExpr = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * const result = inferType(state, letExpr);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Nested let
 * ```ts
 * import { freshState, addType, inferType, letTerm, conTerm, varTerm, appTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const inner = letTerm("y", conTerm("true", conType("Bool")), varTerm("y"));
 * const outer = letTerm("x", conTerm("1", conType("Int")), appTerm(varTerm("x"), inner));
 * const result = inferType(state, outer);
 * console.log("nested:", showType(result.ok));  // "(Int, Bool)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addType, checkType, letTerm, conTerm, varTerm, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const letExpr = letTerm("x", conTerm("42", conType("Int")), varTerm("x"));
 * const expected = conType("Int");
 * const result = checkType(state, letExpr, expected);
 * console.log("checked:", showType(result.ok.type));  // "Int"
 * ```
 *
 * @see {@link inferLetType} Inference rule
 * @see {@link addTerm} Context binding
 * @see {@link inferType} Full inference
 */
export const letTerm = (name: string, value: Term, body: Term): Term => ({
  let: { name, value, body },
});

/**
 * Constructs trait lambda `Λtrait_var<trait<type_var>>::kind where C. body`.
 *
 * **Purpose**: Bounded polymorphism abstraction. Infers bounded forall.
 *
 * @param trait_var - Dict var (`"d"`)
 * @param trait - Trait name (`"Eq"`)
 * @param type_var - Type var (`"Self"`)
 * @param kind - Type var kind
 * @param constraints - Bounds `[{trait, type}, ...]`
 * @param body - Body term
 * @returns `{ trait_lam: { ... } }`
 *
 * @example Basic construction
 * ```ts
 * import { traitLamTerm, showTerm } from "system-f-omega";
 * import { starKind } from "system-f-omega";
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [], { var: "x" });
 * console.log("traitLam:", showTerm(traitLam));  // "ΛSelf::* where . x"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, traitLamTerm, varType, arrowType, starKind, showType } from "system-f-omega";
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
 * import { freshState, addType, addTraitDef, checkType, traitLamTerm, boundedForallType, varType, arrowType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(varType("A"), varType("Bool"))]]).ok;
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Int")));
 * const expected = boundedForallType("Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), varType("Int")));
 * const result = checkType(state, traitLam, expected);
 * console.log("checked:", showType(result.ok.type));  // "∀Self::* where Eq<Self>. (Self → Int)"
 * ```
 *
 * @see {@link inferTraitLamType} Inference rule
 * @see {@link boundedForallType} Inferred type
 * @see {@link traitAppTerm} Application
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
 * Constructs trait application `term [type] with dicts`.
 *
 * **Purpose**: Saturates trait lambdas. Infers via constraints resolution.
 *
 * @param term - Trait lambda term
 * @param type - Type argument
 * @param dicts - Resolved dictionaries
 * @returns `{ trait_app: { term, type, dicts } }`
 *
 * @example Basic construction
 * ```ts
 * import { traitAppTerm, showTerm } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const app = traitAppTerm({ var: "traitLam" }, conType("Int"), [{ var: "eqDict" }]);
 * console.log("traitApp:", showTerm(app));  // "traitLam [Int] with dicts {eqDict}"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, traitAppTerm, traitLamTerm, conType, starKind, arrowType, varType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), dict));
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * const app = traitAppTerm(traitLam, conType("Int"), [{ var: "eqDict" }]);
 * const result = inferType(state, app);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, checkType, traitAppTerm, traitLamTerm, conType, starKind, arrowType, varType, lamTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), dict));
 *
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: varType("Self") }], arrowType(varType("Self"), conType("Int")));
 * const app = traitAppTerm(traitLam, conType("Int"), [{ var: "eqDict" }]);
 * const expected = conType("Int");
 * const result = checkType(state, app, expected);
 * console.log("checked:", showType(result.ok.type));  // "Int"
 * ```
 *
 * @see {@link inferTraitAppType} Inference rule
 * @see {@link traitLamTerm} Callee usage
 * @see {@link checkTraitConstraints} Resolves dicts
 */
export const traitAppTerm = (term: Term, type: Type, dicts: Term[]): Term => ({
  trait_app: { term, type, dicts },
});

/**
 * Constructs trait dictionary `dict trait<type> { method = impl, ... }`.
 *
 * **Purpose**: Explicit impl proof. Used in traitImplBinding, inferDictType.
 *
 * @param trait - Trait name (`"Eq"`)
 * @param type - Impl type (`Int`)
 * @param methods - Method impls `[[name, term], ...]`
 * @returns `{ dict: { trait, type, methods } }`
 *
 * @example Basic dictionary
 * ```ts
 * import { dictTerm, conType, showTerm } from "system-f-omega";
 * import { lamTerm, varTerm } from "system-f-omega";
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [
 *   ["eq", lamTerm("x", conType("Int"), varTerm("x"))]
 * ]);
 * console.log("dict:", showTerm(eqDict));  // "dict Eq<Int> { eq = λx:Int.x }"
 * ```
 *
 * @example Trait impl binding + inference
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, traitMethodTerm, conType, starKind, arrowType, lamTerm, varTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const method = traitMethodTerm(eqDict, "eq");
 * const result = inferType(state, method);
 * console.log("method:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @example inferDictType validation
 * ```ts
 * import { freshState, addType, addTraitDef, inferType, dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 *
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * const result = inferType(state, eqDict);
 * console.log("dictType:", showType(result.ok));  // "Dict<Eq, Int>"
 * ```
 *
 * @see {@link inferDictType} Validates methods
 * @see {@link traitImplBinding} Context storage
 * @see {@link traitMethodTerm} Method access
 */
export const dictTerm = (
  trait: string,
  type: Type,
  methods: [string, Term][],
): DictTerm => ({
  dict: { trait, type, methods },
});

/**
 * Constructs trait method access `dict.method`.
 *
 * **Purpose**: Dictionary method projection. Infers method signature.
 *
 * @param dict - Dictionary term
 * @param method - Method name
 * @returns `{ trait_method: { dict, method } }`
 *
 * @example Basic construction
 * ```ts
 * import { traitMethodTerm, showTerm } from "system-f-omega";
 *
 * const method = traitMethodTerm({ var: "eqDict" }, "eq");
 * console.log("method:", showTerm(method));  // "eqDict.eq"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, inferType, traitMethodTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const method = traitMethodTerm(eqDict, "eq");
 * const result = inferType(state, method);
 * console.log("inferred:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @example Checking
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, checkType, traitMethodTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const eqDict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), eqDict));
 *
 * const method = traitMethodTerm(eqDict, "eq");
 * const expected = arrowType(conType("Int"), conType("Bool"));
 * const result = checkType(state, method, expected);
 * console.log("checked:", showType(result.ok.type));  // "(Int → Bool)"
 * ```
 *
 * @see {@link inferTraitMethodType} Inference rule
 * @see {@link dictTerm} Dictionary values
 * @see {@link inferType} Full inference
 */
export const traitMethodTerm = (dict: Term, method: string): Term => ({
  trait_method: { dict, method },
});

/**
 * Constructs variable pattern `var` (binds whole value).
 *
 * **Purpose**: Captures matched value as binding. Wildcard-like for exhaustiveness.
 *
 * @param name - Binding name
 * @returns `{ var: name }`
 *
 * @example Basic construction
 * ```ts
 * import { varPattern, showPattern } from "system-f-omega";
 *
 * console.log("x:", showPattern(varPattern("x")));  // "x"
 * ```
 *
 * @example Pattern checking (binds type)
 * ```ts
 * import { freshState, addType, checkPattern, varPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkPattern(state, varPattern("x"), conType("Int"));
 * console.log("binds:", result.ok.length === 1);  // true
 * ```
 *
 * @example Match inference (wildcard-like)
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, varPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }], ["Some", conType("T")]]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 * const match = matchTerm(scrut, [[varPattern("x"), varTerm("x")]]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Option<Int>"
 * ```
 *
 * @see {@link checkPattern} Binding extraction
 * @see {@link matchTerm} Usage in cases
 * @see {@link wildcardPattern} No-binding alternative
 */
export const varPattern = (name: string): Pattern => ({ var: name });

/**
 * Constructs wildcard pattern `_` (matches anything, no binding).
 *
 * **Purpose**: Ignore values. Exhaustive for any type.
 *
 * @returns `{ wildcard: null }`
 *
 * @example Basic construction
 * ```ts
 * import { wildcardPattern, showPattern } from "system-f-omega";
 *
 * console.log("wildcard:", showPattern(wildcardPattern()));  // "_"
 * ```
 *
 * @example Pattern checking (no bindings)
 * ```ts
 * import { freshState, addType, checkPattern, wildcardPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkPattern(state, wildcardPattern(), conType("Int"));
 * console.log("no bindings:", result.ok.length === 0);  // true
 * ```
 *
 * @example Match inference (exhaustive)
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, wildcardPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }], ["Some", conType("T")]]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Int")));
 * const match = matchTerm(scrut, [[wildcardPattern(), conTerm("default", conType("Int"))]]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link checkPattern} Empty bindings
 * @see {@link checkExhaustive} Always exhaustive
 * @see {@link varPattern} Binding alternative
 */
export const wildcardPattern = (): Pattern => ({ wildcard: null });

/**
 * Constructs constructor pattern `con` (exact constant/tag match).
 *
 * **Purpose**: Matches literals/enum constructors. No bindings.
 *
 * @param name - Constructor name (`"None"`, `"true"`)
 * @param type - Expected type
 * @returns `{ con: { name, type } }`
 *
 * @example Basic construction
 * ```ts
 * import { conPattern, conType, showPattern } from "system-f-omega";
 *
 * console.log("None:", showPattern(conPattern("None", conType("Unit"))));  // "None"
 * ```
 *
 * @example Pattern checking success
 * ```ts
 * import { freshState, addType, checkPattern, conPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Unit", starKind).ok;
 *
 * const result = checkPattern(state, conPattern("true", conType("Bool")), conType("Bool"));
 * console.log("matches:", "ok" in result && result.ok.length === 0);  // true
 * ```
 *
 * @example Pattern checking failure
 * ```ts
 * import { freshState, addType, checkPattern, conPattern, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const result = checkPattern(state, conPattern("true", conType("Bool")), conType("Int"));
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, addEnum, inferType, matchTerm, conPattern, conTerm, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", conType("Unit")]]).ok;
 *
 * const scrut = conTerm("opt", appType(conType("Option"), conType("Bool")));
 * const match = matchTerm(scrut, [[conPattern("None", conType("Unit")), conTerm("default", conType("Bool"))]]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Bool"
 * ```
 *
 * @see {@link checkPattern} Constant matching
 * @see {@link matchTerm} Case usage
 * @see {@link varPattern} Variable alternative
 */
export const conPattern = (name: string, type: Type): Pattern => ({
  con: { name, type },
});
/**
 * Constructs record pattern `{ label: pat, ... }`.
 *
 * **Purpose**: Destructures records. Binds nested patterns.
 *
 * @param fields - Field patterns `[[label, pattern], ...]`
 * @returns `{ record: [[string, Pattern]] }`
 *
 * @example Basic construction
 * ```ts
 * import { recordPattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = recordPattern([["x", varPattern("a")], ["y", varPattern("b")]]);
 * console.log("record:", showPattern(pat));  // "{x: a, y: b}"
 * ```
 *
 * @example Pattern checking success
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = recordPattern([["x", varPattern("a")], ["y", varPattern("b")]]);
 * const ty = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("binds:", result.ok.length === 2);  // true
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
 * const pat = recordPattern([["x", varPattern("a")]]);
 * const match = matchTerm(scrut, [[pat, varTerm("a")]]);
 * const result = inferType(state, match);
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @example Failure: Label mismatch
 * ```ts
 * import { freshState, addType, checkPattern, recordPattern, varPattern, recordType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const pat = recordPattern([["y", varPattern("b")]]);  // Wrong label
 * const ty = recordType([["x", conType("Int")]]);
 * const result = checkPattern(state, pat, ty);
 * console.log("missing:", "missing_field" in result.err);  // true
 * ```
 *
 * @see {@link checkPattern} Record validation
 * @see {@link matchTerm} Nested usage
 * @see {@link recordType} Matching type
 */
export const recordPattern = (fields: [string, Pattern][]): Pattern => ({
  record: fields,
});

/**
 * Constructs variant pattern `label(pat)` (tagged destructuring).
 *
 * **Purpose**: Matches enum/variant cases. Recurses on payload.
 *
 * @param label - Variant label (`"Cons"`, `"Some"`)
 * @param pattern - Payload pattern
 * @returns `{ variant: { label, pattern } }`
 *
 * @example Basic construction
 * ```ts
 * import { variantPattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = variantPattern("Cons", varPattern("x"));
 * console.log("variant:", showPattern(pat));  // "Cons(x)"
 * ```
 *
 * @example Pattern checking success
 * ```ts
 * import { freshState, addType, addEnum, checkPattern, variantPattern, varPattern, appType, conType, starKind } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), conType("T"))])]
 * ]).ok;
 *
 * const result = checkPattern(state, variantPattern("Cons", varPattern("x")), appType(conType("List"), conType("Int")));
 * console.log("binds:", result.ok.length === 1);  // true
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
 * @see {@link checkPattern} Variant case lookup
 * @see {@link matchTerm} Case usage
 * @see {@link injectTerm} Matching injection
 */
export const variantPattern = (label: string, pattern: Pattern): Pattern => ({
  variant: { label, pattern },
});

/**
 * Constructs tuple pattern `(pat₁, pat₂, ...)` (unlabeled destructuring).
 *
 * **Purpose**: Matches tuples. Binds nested patterns.
 *
 * @param elements - Pattern elements
 * @returns `{ tuple: Pattern[] }`
 *
 * @example Basic construction
 * ```ts
 * import { tuplePattern, varPattern, showPattern } from "system-f-omega";
 *
 * const pat = tuplePattern([varPattern("a"), varPattern("b")]);
 * console.log("tuple:", showPattern(pat));  // "(a, b)"
 * ```
 *
 * @example Pattern checking success
 * ```ts
 * import { freshState, addType, checkPattern, tuplePattern, varPattern, tupleType, conType, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 *
 * const pat = tuplePattern([varPattern("a"), varPattern("b")]);
 * const ty = tupleType([conType("Int"), conType("Bool")]);
 * const result = checkPattern(state, pat, ty);
 * console.log("binds:", result.ok.length === 2);  // true
 * ```
 *
 * @example Match inference
 * ```ts
 * import { freshState, addType, inferType, matchTerm, tuplePattern, varPattern, tupleTerm, conTerm, tupleType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 *
 * const scrut = tupleTerm([conTerm("1", conType("Int"))]);
 * const pat = tuplePattern([varPattern("x")]);
 * const match = matchTerm(scrut, [[pat, varTerm("x")]]);
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
 * const pat = tuplePattern([varPattern("x"), varPattern("y")]);  // 2 elems
 * const ty = tupleType([conType("Int")]);  // 1 elem
 * const result = checkPattern(state, pat, ty);
 * console.log("mismatch:", "type_mismatch" in result.err);  // true
 * ```
 *
 * @see {@link checkPattern} Tuple validation
 * @see {@link matchTerm} Case usage
 * @see {@link tupleType} Matching type
 */
export const tuplePattern = (elements: Pattern[]): Pattern => ({
  tuple: elements,
});

/**
 * Unit type `()` (zero-arity tuple, inhabited by one value).
 *
 * **Purpose**: Terminal object. Used in empty variants (`None`), enums.
 *
 * @example Pretty-print
 * ```ts
 * import { unitType, showType } from "system-f-omega";
 *
 * console.log("unit:", showType(unitType));  // "()"
 * ```
 *
 * @example Enum None case
 * ```ts
 * import { freshState, addEnum, normalizeType, appType, conType, unitType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", unitType]]).ok;
 *
 * const optBool = appType(conType("Option"), conType("Bool"));
 * const expanded = normalizeType(state, optBool);
 * console.log("None:", showType(expanded));  // "<None: ⊥ | ...>"
 * ```
 *
 * @example Tuple extension
 * ```ts
 * import { tupleType, unitType, conType, showType } from "system-f-omega";
 *
 * const extended = tupleType([conType("Int"), unitType]);
 * console.log("extended:", showType(extended));  // "(Int, ())"
 * ```
 *
 * @see {@link unitValue} Unit value
 * @see {@link tupleType} General tuples
 */
export const unitType: Type = { tuple: [] };

/**
 * Unit value `{}` (empty tuple, sole inhabitant of `unitType`).
 *
 * **Purpose**: Terminal value. Used in empty injections (`None = {}`).
 *
 * @example Pretty-print
 * ```ts
 * import { unitValue, showTerm } from "system-f-omega";
 *
 * console.log("unit val:", showTerm(unitValue));  // "()"
 * ```
 *
 * @example Inference
 * ```ts
 * import { freshState, inferType, unitValue, showType } from "system-f-omega";
 *
 * const state = freshState();
 * const result = inferType(state, unitValue);
 * console.log("inferred:", showType(result.ok));  // "()"
 * ```
 *
 * @example Enum injection
 * ```ts
 * import { freshState, addEnum, inferType, injectTerm, unitValue, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }]]).ok;
 *
 * const noneBool = injectTerm("None", unitValue, appType(conType("Option"), conType("Bool")));
 * const result = inferType(state, noneBool);
 * console.log("None:", showType(result.ok));  // "Option<Bool>"
 * ```
 *
 * @see {@link unitType} Unit type
 * @see {@link injectTerm} Empty variant payload
 */
export const unitValue: Term = { tuple: [] };

/**
 * Constructs term binding `{ term: { name, type } }`.
 *
 * **Purpose**: Binds value names to types in context.
 *
 * @param name - Term name (`"x"`)
 * @param type - Type
 * @returns Binding
 *
 * @example Basic construction
 * ```ts
 * import { termBinding, conType, showBinding } from "system-f-omega";
 *
 * const bind = termBinding("x", conType("Int"));
 * console.log(showBinding(bind));  // "Term: x = Int"
 * ```
 *
 * @example Context usage
 * ```ts
 * import { freshState, termBinding, conType, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * const ctx = state.ctx.concat([termBinding("x", conType("Int"))]);
 * console.log(showContext(ctx));  // "Term: x = Int"
 * ```
 *
 * @example addTerm equivalent
 * ```ts
 * import { freshState, addType, addTerm, conTerm, conType, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "x", conTerm("42", conType("Int"))).ok;
 * console.log(showContext(state.ctx));  // "...\nTerm: x = Int"
 * ```
 *
 * @see {@link addTerm} Stateful adder
 * @see {@link typeBinding} Type counterpart
 */
export const termBinding = (name: string, type: Type) => ({
  term: { name, type },
});

/**
 * Constructs type binding `{ type: { name, kind } }`.
 *
 * **Purpose**: Binds type constructors/kind vars in context.
 *
 * @param name - Type name (`"Int"`)
 * @param kind - Kind (`*`, `*→*`)
 * @returns Binding
 *
 * @example Basic construction
 * ```ts
 * import { typeBinding, starKind, showBinding } from "system-f-omega";
 *
 * const bind = typeBinding("Int", starKind);
 * console.log(showBinding(bind));  // "Type: Int = *"
 * ```
 *
 * @example Context usage
 * ```ts
 * import { freshState, typeBinding, starKind, showContext } from "system-f-omega";
 *
 * const state = freshState();
 * const ctx = state.ctx.concat([typeBinding("Int", starKind)]);
 * console.log(showContext(ctx));  // "Type: Int = *"
 * ```
 *
 * @example addType equivalent
 * ```ts
 * import { freshState, addType, typeBinding, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * console.log(showContext(state.ctx));  // "Type: Int = *"
 * ```
 *
 * @see {@link addType} Stateful adder
 * @see {@link termBinding} Term counterpart
 */
export const typeBinding = (name: string, kind: Kind) => ({
  type: { name, kind },
});

/**
 * Constructs type alias binding for context.
 *
 * **Purpose**: Parametric aliases: `Id<A> = A`. Used in `addTypeAlias`.
 *
 * @param name - Alias name (`"Id"`)
 * @param params - Param names `["A"]`
 * @param kinds - Param kinds `[starKind]`
 * @param body - Right-hand side
 * @returns Alias binding
 *
 * @example Basic alias
 * ```ts
 * import { typeAliasBinding, varType, starKind, showBinding } from "system-f-omega";
 *
 * const idAlias = typeAliasBinding("Id", ["A"], [starKind], varType("A"));
 * console.log(showBinding(idAlias));  // "Type Alias: Id<A::*> = A"
 * ```
 *
 * @example Context + expansion
 * ```ts
 * import { freshState, addTypeAlias, normalizeType, appType, conType, typeAliasBinding, varType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 *
 * const idInt = appType({ con: "Id" }, conType("Int"));
 * const expanded = normalizeType(state, idInt);
 * console.log("expanded:", showType(expanded));  // "Int"
 * ```
 *
 * @example Multi-param
 * ```ts
 * import { typeAliasBinding, tupleType, varType, starKind, showBinding } from "system-f-omega";
 *
 * const pairAlias = typeAliasBinding("Pair", ["A", "B"], [starKind, starKind], tupleType([varType("A"), varType("B")]));
 * console.log(showBinding(pairAlias));  // "Type Alias: Pair<A::*,B::*> = (A, B)"
 * ```
 *
 * @see {@link addTypeAlias} Stateful adder
 * @see {@link normalizeType} Expands aliases
 * @see {@link appType} Alias application
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
 * Constructs trait definition binding for context.
 *
 * **Purpose**: Defines interfaces: `trait Eq<A::*>: eq : A → Bool`.
 * Used in `addTraitDef`.

 * @param name - Trait name (`"Eq"`)
 * @param type_param - Type param (`"A"`)
 * @param kind - Param kind
 * @param methods - Signatures `[[name, type], ...]`
 * @returns TraitDef binding
 *
 * @example Basic trait
 * ```ts
 * import { traitDefBinding, starKind, arrowType, varType, showBinding } from "system-f-omega";
 *
 * const eqDef = traitDefBinding("Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))]
 * ]);
 * console.log(showBinding({ trait_def: eqDef }));
 * // "Trait: Eq = TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * @example Context usage (addTraitDef equivalent)
 * ```ts
 * import { freshState, addType, addTraitDef, showContext, starKind, arrowType, varType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))]
 * ]).ok;
 * console.log(showContext(state.ctx));
 * // "...\nTrait: Eq = TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * @example HKT trait
 * ```ts
 * import { traitDefBinding, arrowKind, starKind, arrowType, varType, showBinding } from "system-f-omega";
 *
 * const functorDef = traitDefBinding("Functor", "F", arrowKind(starKind, starKind), [
 *   ["map", arrowType(varType("F"), varType("F"))]
 * ]);
 * console.log(showBinding({ trait_def: functorDef }));
 * // "Trait: Functor = TraitDef (Functor F = (* → *)\n  map : (F → F))"
 * ```
 *
 * @example Multi-method
 * ```ts
 * import { traitDefBinding, starKind, arrowType, varType, showBinding } from "system-f-omega";
 *
 * const ordDef = traitDefBinding("Ord", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))],
 *   ["lt", arrowType(varType("A"), varType("Bool"))]
 * ]);
 * console.log(showBinding({ trait_def: ordDef }));
 * // "Trait: Ord = TraitDef (Ord A = *\n  eq : (A → Bool)\n  lt : (A → Bool))"
 * ```
 *
 * @see {@link addTraitDef} Stateful adder
 * @see {@link showTraitDef} Pretty-printer
 * @see {@link traitImplBinding} Implementations
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
 * Constructs trait impl binding for context.
 *
 * **Purpose**: Registers `trait` impl for `type` with `dict`. Used in `addTraitImpl`.
 *
 * @param trait - Trait name (`"Eq"`)
 * @param type - Impl type (`Int`)
 * @param dict - Dictionary term
 * @returns Impl binding
 *
 * @example Basic construction
 * ```ts
 * import { traitImplBinding, dictTerm, conType, showBinding } from "system-f-omega";
 *
 * const impl = traitImplBinding("Eq", conType("Int"), dictTerm("Eq", conType("Int"), []));
 * console.log(showBinding(impl));  // "Impl: Eq = dict Eq<Int> { }: Int"
 * ```
 *
 * @example Context usage (addTraitImpl equivalent)
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * const impl = traitImplBinding("Eq", conType("Int"), dict);
 * state.ctx.push(impl);
 * console.log(showContext(state.ctx));
 * // "...\nImpl: Eq = dict Eq<Int> { eq = λx:Int.true }: Int"
 * ```
 *
 * @example Resolution usage
 * ```ts
 * import { freshState, addType, addTraitDef, traitImplBinding, dictTerm, checkTraitImplementation, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state.ctx.push(traitImplBinding("Eq", conType("Int"), dict));
 *
 * const result = checkTraitImplementation(state, "Eq", conType("Int"));
 * console.log("resolved:", "ok" in result);  // true
 * ```
 *
 * @see {@link addTraitImpl} Stateful adder
 * @see {@link checkTraitImplementation} Uses impls
 * @see {@link dictTerm} Dictionary construction
 */
export const traitImplBinding = (trait: string, type: Type, dict: Term) => ({
  trait_impl: { trait, type, dict },
});

/**
 * Constructs dictionary binding `{ dict: { name, trait, type } }`.
 *
 * **Purpose**: Binds dict var to trait+type in context (trait_lam env).
 * Used in `addDict`.

 * @param name - Dict var (`"eqInt"`)
 * @param trait - Trait name (`"Eq"`)
 * @param type - Type param (`Int`)
 * @returns Dict binding
 *
 * @example Basic construction
 * ```ts
 * import { dictBinding, conType, showBinding } from "system-f-omega";
 *
 * const dictBind = dictBinding("eqInt", "Eq", conType("Int"));
 * console.log(showBinding(dictBind));  // "Dict: eqInt = Trait Eq : Int"
 * ```
 *
 * @example Context usage (addDict equivalent)
 * ```ts
 * import { freshState, addType, addDict, dictTerm, conTerm, conType, starKind, showContext } from "system-f-omega";
 * import { arrowType, lamTerm, varTerm } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * const dt = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addDict(state, "eqInt", dt).ok;
 * console.log(showContext(state.ctx));
 * // "...\nDict: eqInt = Trait Eq : Int"
 * ```
 *
 * @example Trait method lookup
 * ```ts
 * import { freshState, addType, addTraitDef, dictBinding, inferType, traitMethodTerm, conType, starKind, arrowType, varType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * state.ctx.push(dictBinding("eqInt", "Eq", conType("Int")));
 *
 * const method = traitMethodTerm({ var: "eqInt" }, "eq");
 * const result = inferType(state, method);
 * console.log("method:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @see {@link addDict} Stateful adder
 * @see {@link traitMethodTerm} Uses dict bindings
 * @see {@link inferTraitMethodType} Lookup
 */
export const dictBinding = (name: string, trait: string, type: Type) => ({
  dict: { name, trait, type },
});

/**
 * Constructs enum definition binding for context.
 *
 * **Purpose**: Defines ADTs: `enum Option<T::*>: None | Some(T)`.
 * Used in `addEnum`.

 * @param name - Enum name (`"Option"`)
 * @param kind - Enum kind (`* → *`)
 * @param params - Param names `["T"]`
 * @param variants - Cases `[[label, scheme], ...]`
 * @param recursive - Recursive? (defaults `false`)
 * @returns Enum binding
 *
 * @example Basic non-recursive
 * ```ts
 * import { enumDefBinding, tupleType, conType, starKind, showBinding } from "system-f-omega";
 *
 * const optionDef = enumDefBinding("Option", arrowKind(starKind, starKind), ["T"], [
 *   ["None", tupleType([])],
 *   ["Some", conType("T")]
 * ]);
 * console.log(showBinding({ enum: optionDef }));
 * // "Enum: Option = { name: 'Option', kind: (* → *), params: ['T'], ... }"
 * ```
 *
 * @example Recursive list
 * ```ts
 * import { enumDefBinding, tupleType, appType, conType, varType, starKind, showBinding } from "system-f-omega";
 * import { arrowKind } from "system-f-omega";
 *
 * const listDef = enumDefBinding("List", arrowKind(starKind, starKind), ["T"], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true);
 * console.log("recursive:", listDef.recursive);  // true
 * ```
 *
 * @example Context usage (addEnum equivalent)
 * ```ts
 * import { freshState, addType, addEnum, showContext, starKind } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Color", [], [], [["Red", { tuple: [] }]]).ok;
 * console.log(showContext(state.ctx));
 * // "...\nEnum: Color = { name: 'Color', ... }"
 * ```
 *
 * @example Normalization after enum
 * ```ts
 * import { freshState, addType, addEnum, normalizeType, appType, conType, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "Option", ["T"], [starKind], [["None", { tuple: [] }], ["Some", conType("T")]]).ok;
 *
 * const optInt = appType(conType("Option"), conType("Int"));
 * const expanded = normalizeType(state, optInt);
 * console.log("expanded:", showType(expanded));  // "<None: ⊥ | Some: Int>"
 * ```
 *
 * @see {@link addEnum} Stateful adder
 * @see {@link normalizeType} Expands enums
 * @see {@link variantType} Structural form
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
 * Renames free vars/cons/labels/traits via `ren` map (binder-safe).
 *
 * **Purpose**: Module import renaming, alpha-conversion. Skips bound vars.
 * Renames: vars/cons/labels/traits. Structural recurse.
 *
 * Used in module system (`importModule`).
 *
 * @param state - Checker state (unused)
 * @param ty - Input type
 * @param ren - Rename map `Map<old, new>`
 * @param bound - Bound vars set (defaults empty)
 * @returns Renamed type
 *
 * @example Basic var rename
 * ```ts
 * import { renameType, varType, arrowType, showType } from "system-f-omega";
 *
 * const ren = new Map([["a", "X"]]);
 * const ty = arrowType(varType("a"), varType("b"));
 * const renamed = renameType({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, ty, ren);
 * console.log(showType(renamed));  // "(X → b)"
 * ```
 *
 * @example Skip bound binder
 * ```ts
 * import { renameType, forallType, arrowType, varType, starKind, showType } from "system-f-omega";
 *
 * const ren = new Map([["a", "X"]]);
 * const bound = new Set(["a"]);
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * const renamed = renameType({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, poly, ren, bound);
 * console.log(showType(renamed));  // "∀a::*. (a → b)"
 * ```
 *
 * @example Record/variant labels
 * ```ts
 * import { renameType, recordType, variantType, showType } from "system-f-omega";
 * import { conType } from "system-f-omega";
 *
 * const ren = new Map([["x", "field"], ["Left", "L"]]);
 * const rec = recordType([["x", conType("Int")], ["y", conType("Bool")]]);
 * const renamedRec = renameType({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, rec, ren);
 * console.log(showType(renamedRec));  // "{field: Int, y: Bool}"
 *
 * const varn = variantType([["Left", conType("Int")], ["Right", conType("Bool")]]);
 * const renamedVarn = renameType({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, varn, ren);
 * console.log(showType(renamedVarn));  // "<L: Int | Right: Bool>"
 * ```
 *
 * @example Bounded forall traits
 * ```ts
 * import { renameType, boundedForallType, showType } from "system-f-omega";
 * import { varType, starKind } from "system-f-omega";
 *
 * const ren = new Map([["Eq", "PartialEq"]]);
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: varType("a") }], varType("a"));
 * const renamed = renameType({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, bounded, ren);
 * console.log(showType(renamed));  // "∀a::* where PartialEq<a>. a"
 * ```
 *
 * @see {@link importModule} Module renaming
 * @see {@link renameTerm} Term counterpart
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
 * Renames free vars/cons/labels/traits in term (binder-safe).
 *
 * **Purpose**: Module imports, alpha-conversion. Skips bound vars.
 * Renames: vars/cons/labels/traits/methods. Calls `renameType`.
 *
 * Used with `renameType` in `importModule`.
 *
 * @param state - Checker state (`renameType`)
 * @param term - Input term
 * @param ren - Rename map `Map<old,new>`
 * @param bound - Bound vars set (defaults empty)
 * @returns Renamed term
 *
 * @example Basic var rename
 * ```ts
 * import { renameTerm, varTerm, arrowType, showTerm, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const ren = new Map([["x", "y"]]);
 * const app = { app: { callee: varTerm("f"), arg: varTerm("x") } };
 * const renamed = renameTerm(state, app, ren);
 * console.log(showTerm(renamed));  // "(f y)"
 * ```
 *
 * @example Skip bound lambda
 * ```ts
 * import { freshState, renameTerm, lamTerm, varTerm, conType, showTerm } from "system-f-omega";
 *
 * const state = freshState();
 * const ren = new Map([["x", "y"]]);
 * const id = lamTerm("x", conType("Int"), varTerm("x"));
 * const renamed = renameTerm(state, id, ren);
 * console.log(showTerm(renamed));  // "λx:Int.x" (skipped!)
 * ```
 *
 * @example Record/trait labels
 * ```ts
 * import { renameTerm, recordTerm, dictTerm, showTerm } from "system-f-omega";
 * import { conTerm, conType, freshState } from "system-f-omega";
 *
 * const state = freshState();
 * const ren = new Map([["x", "field"], ["eq", "equals"]]);
 * const rec = recordTerm([["x", conTerm("1", conType("Int"))]]);
 * const renamedRec = renameTerm(state, rec, ren);
 * console.log(showTerm(renamedRec));  // "{field = 1}"
 *
 * const dict = dictTerm("Eq", conType("Int"), [["eq", conTerm("impl", conType("Bool"))]]);
 * const renamedDict = renameTerm(state, dict, ren);
 * console.log(showTerm(renamedDict));  // "dict Eq<Int> { equals = impl }"
 * ```
 *
 * @example Trait lambda (bounds)
 * ```ts
 * import { renameTerm, traitLamTerm, showTerm } from "system-f-omega";
 * import { freshState, starKind } from "system-f-omega";
 *
 * const state = freshState();
 * const ren = new Map([["Eq", "PartialEq"]]);
 * const traitLam = traitLamTerm("d", "Eq", "Self", starKind, [{ trait: "Eq", type: { var: "Self" } }], { var: "body" });
 * const renamed = renameTerm(state, traitLam, ren);
 * console.log(showTerm(renamed));  // "ΛSelf::* where PartialEq<Self>. body"
 * ```
 *
 * @see {@link renameType} Type counterpart
 * @see {@link importModule} Module renaming
 * @see {@link renamePattern} Pattern counterpart
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
 * Renames free vars/cons/labels in pattern (binder-safe).
 *
 * **Purpose**: Module imports. Skips wildcards, binds vars.
 *
 * @param state - Checker state (`renameType`)
 * @param pat - Input pattern
 * @param ren - Rename map `Map<old,new>`
 * @param bound - Bound vars set
 * @returns Renamed pattern
 *
 * @example Var rename
 * ```ts
 * import { renamePattern, varPattern, showPattern } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["x", "y"]]);
 * const bound = new Set();
 * const renamed = renamePattern(state, varPattern("x"), ren, bound);
 * console.log(showPattern(renamed));  // "y"
 * ```
 *
 * @example Con/record labels
 * ```ts
 * import { renamePattern, conPattern, recordPattern, showPattern } from "system-f-omega";
 * import { freshState, conType } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["None", "Empty"], ["x", "field"]]);
 * const bound = new Set();
 *
 * const conRen = renamePattern(state, conPattern("None", conType("Unit")), ren, bound);
 * console.log(showPattern(conRen));  // "Empty"
 *
 * const recRen = renamePattern(state, recordPattern([["x", varPattern("a")]]), ren, bound);
 * console.log(showPattern(recRen));  // "{field: a}"
 * ```
 *
 * @example Variant/tuple nested
 * ```ts
 * import { renamePattern, variantPattern, tuplePattern, showPattern } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["Cons", "Node"], ["hd", "head"]]);
 * const bound = new Set();
 *
 * const varRen = renamePattern(state, variantPattern("Cons", varPattern("hd")), ren, bound);
 * console.log(showPattern(varRen));  // "Node(head)"
 *
 * const tupRen = renamePattern(state, tuplePattern([varPattern("hd"), varPattern("tl")]), ren, bound);
 * console.log(showPattern(tupRen));  // "(head, tl)"
 * ```
 *
 * @example Wildcard no-op
 * ```ts
 * import { renamePattern, wildcardPattern, showPattern } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["x", "y"]]);
 * const bound = new Set();
 * const renamed = renamePattern(state, wildcardPattern(), ren, bound);
 * console.log(showPattern(renamed));  // "_"
 * ```
 *
 * @see {@link renameType} Type counterpart
 * @see {@link renameTerm} Term counterpart
 * @see {@link importModule} Module usage
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
 * Renames binding identifiers for module imports (all variants).
 *
 * **Purpose**: Applies `ren` map to bindings in `importModule`.
 * Renames: names/params/traits/methods/types. Calls `renameType/Term`.

 * @param state - Checker state (`renameType`)
 * @param b - Input binding
 * @param ren - Rename map `Map<old,new>`
 * @returns Renamed binding
 *
 * @example Term/type bindings
 * ```ts
 * import { renameBinding, termBinding, typeBinding, showBinding } from "system-f-omega";
 * import { conType, starKind } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["x", "y"], ["Int", "Number"]]);
 *
 * const termB = renameBinding(state, termBinding("x", conType("Int")), ren);
 * console.log(showBinding(termB));  // "Term: y = Number"
 *
 * const typeB = renameBinding(state, typeBinding("Int", starKind), ren);
 * console.log(showBinding(typeB));  // "Type: Number = *"
 * ```
 *
 * @example TraitDef/impl
 * ```ts
 * import { renameBinding, traitDefBinding, traitImplBinding, showBinding } from "system-f-omega";
 * import { starKind, arrowType, varType, dictTerm, conType, freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["Eq", "PartialEq"], ["eq", "equals"]]);
 *
 * const traitD = renameBinding(state, traitDefBinding("Eq", "A", starKind, [["eq", arrowType(varType("A"), varType("Bool"))]]), ren);
 * console.log(showBinding({ trait_def: traitD }));
 * // "Trait: PartialEq = TraitDef (PartialEq A = *\n  equals : (A → Bool))"
 *
 * const impl = renameBinding(state, traitImplBinding("Eq", conType("Int"), dictTerm("Eq", conType("Int"), [])), ren);
 * console.log(showBinding(impl));  // "Impl: PartialEq = dict Eq<Int> { }: Int"
 * ```
 *
 * @example Dict/enum/alias
 * ```ts
 * import { renameBinding, dictBinding, enumDefBinding, typeAliasBinding, showBinding } from "system-f-omega";
 * import { starKind, tupleType, conType, freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const ren = new Map([["eqInt", "equalsInt"], ["Color", "Colour"], ["RGB", "Id"]]);
 *
 * const dictB = renameBinding(state, dictBinding("eqInt", "Eq", conType("Int")), ren);
 * console.log(showBinding(dictB));  // "Dict: equalsInt = Trait Eq : Int"
 *
 * const enumB = renameBinding(state, enumDefBinding("Color", starKind, [], [["Red", tupleType([])]]), ren);
 * console.log("enum renamed:", enumB.enum!.name);  // "Colour"
 *
 * const aliasB = renameBinding(state, typeAliasBinding("RGB", ["A"], [starKind], conType("A")), ren);
 * console.log(showBinding(aliasB));  // "Type Alias: Id<A::*> = A"
 * ```
 *
 * @see {@link importModule} Module importer
 * @see {@link renameType} Type renamer
 * @see {@link renameTerm} Term renamer
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
 * Computes free names in `type` (binder-respecting).
 *
 * **Purpose**: Dependency analysis for imports/renaming.
 * Collects: typeVars/cons/traits/labels. Skips bound ∀/λ/μ.
 *
 * @param _state - Unused
 * @param ty - Input type
 * @param bound - Bound vars (defaults empty)
 * @returns `{ typeVars/traits/typeCons/labels: Set<string> }`
 *
 * @example Basic vars/cons
 * ```ts
 * import { computeFreeTypes, arrowType, varType, conType } from "system-f-omega";
 *
 * const ty = arrowType(varType("a"), appType(conType("List"), varType("b")));
 * const free = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, ty);
 * console.log("vars:", Array.from(free.typeVars));  // ["a", "b"]
 * console.log("cons:", Array.from(free.typeCons));  // ["List"]
 * ```
 *
 * @example Bound forall (skips binder)
 * ```ts
 * import { computeFreeTypes, forallType, arrowType, varType, starKind } from "system-f-omega";
 *
 * const poly = forallType("a", starKind, arrowType(varType("a"), varType("b")));
 * const free = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, poly);
 * console.log("free vars:", Array.from(free.typeVars));  // ["b"] (a bound)
 * ```
 *
 * @example Data + traits
 * ```ts
 * import { computeFreeTypes, recordType, variantType, boundedForallType } from "system-f-omega";
 * import { varType, conType, starKind } from "system-f-omega";
 *
 * const rec = recordType([["x", varType("a")], ["y", conType("Int")]]);
 * const freeRec = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, rec);
 * console.log("labels:", Array.from(freeRec.labels));  // ["x", "y"]
 * console.log("vars:", Array.from(freeRec.typeVars));  // ["a"]
 *
 * const bounded = boundedForallType("a", starKind, [{ trait: "Eq", type: varType("a") }], varType("b"));
 * const freeBound = computeFreeTypes({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, bounded);
 * console.log("traits:", Array.from(freeBound.traits));  // ["Eq"]
 * ```
 *
 * @internal Dependency analysis
 * @see {@link importModule} Uses for deps
 * @see {@link collectTypeVars} Vars only
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
 * Computes free names in `pat`: vars/constructors/labels.
 *
 * **Purpose**: Pattern dependency analysis for imports.
 * No binders (collects all vars).
 *
 * @param _state - Unused
 * @param pat - Input pattern
 * @returns `{ vars/constructors/labels: Set<string> }`
 *
 * @example Basic vars/cons
 * ```ts
 * import { computeFreePatterns, varPattern, conPattern } from "system-f-omega";
 *
 * const vars = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, varPattern("x"));
 * console.log("vars:", Array.from(vars.vars));  // ["x"]
 *
 * const cons = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, conPattern("None", { con: "Unit" }));
 * console.log("cons:", Array.from(cons.constructors));  // ["None"]
 * ```
 *
 * @example Nested record/variant
 * ```ts
 * import { computeFreePatterns, recordPattern, variantPattern, varPattern } from "system-f-omega";
 *
 * const rec = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, recordPattern([["x", varPattern("a")]]));
 * console.log("labels:", Array.from(rec.labels));  // ["x"]
 * console.log("vars:", Array.from(rec.vars));      // ["a"]
 *
 * const varn = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, variantPattern("Cons", varPattern("hd")));
 * console.log("labels:", Array.from(varn.labels));  // ["Cons"]
 * console.log("vars:", Array.from(varn.vars));      // ["hd"]
 * ```
 *
 * @example Tuple/wildcard empty
 * ```ts
 * import { computeFreePatterns, tuplePattern, varPattern, wildcardPattern } from "system-f-omega";
 *
 * const tup = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, tuplePattern([varPattern("a"), varPattern("b")]));
 * console.log("tuple vars:", Array.from(tup.vars));  // ["a", "b"]
 *
 * const wc = computeFreePatterns({ ctx: [], meta: { counter: 0, kinds: new Map(), solutions: new Map() } }, wildcardPattern());
 * console.log("wildcard empty:", wc.vars.size === 0);  // true
 * ```
 *
 * @internal Pattern dependency analysis
 * @see {@link computeFreeTypes} Type counterpart
 * @see {@link importModule} Uses for deps
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
 * Computes free names in `term` (binder-respecting).
 *
 * **Purpose**: Dependency analysis for imports/renaming.
 * Collects: terms/cons/traits/dicts/labels + type vars/cons.
 * Calls `computeFreeTypes`/`computeFreePatterns`.
 *
 * @param state - Checker state (`computeFreeTypes`)
 * @param term - Input term
 * @param bound - Bound term vars (defaults empty)
 * @returns `{ terms/cons/traits/dicts/labels/typeVars/typeCons: Set }`
 *
 * @example Basic terms/cons
 * ```ts
 * import { computeFreeTerms, varTerm, conTerm } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const app = { app: { callee: varTerm("f"), arg: conTerm("42", { con: "Int" }) } };
 * const free = computeFreeTerms(state, app);
 * console.log("terms:", Array.from(free.terms));     // ["f"]
 * console.log("cons:", Array.from(free.constructors));  // ["42"]
 * ```
 *
 * @example Binder skip (lam/let)
 * ```ts
 * import { computeFreeTerms, lamTerm, letTerm, varTerm, conTerm } from "system-f-omega";
 * import { freshState, conType } from "./helpers.js";
 *
 * const state = freshState();
 * const lam = lamTerm("x", conType("Int"), varTerm("y"));
 * const freeLam = computeFreeTerms(state, lam);
 * console.log("lam terms:", Array.from(freeLam.terms));  // ["y"] (x bound)
 *
 * const letE = letTerm("x", conTerm("1", conType("Int")), varTerm("x"));
 * const freeLet = computeFreeTerms(state, letE);
 * console.log("let terms:", Array.from(freeLet.terms));  // [] (x bound)
 * ```
 *
 * @example Traits/dicts/labels
 * ```ts
 * import { computeFreeTerms, dictTerm, traitMethodTerm, recordTerm } from "system-f-omega";
 * import { freshState, conType } from "./helpers.js";
 *
 * const state = freshState();
 * const dict = dictTerm("Eq", conType("Int"), [["eq", { var: "impl" }]]);
 * const freeDict = computeFreeTerms(state, dict);
 * console.log("traits:", Array.from(freeDict.traits));  // ["Eq"]
 * console.log("labels:", Array.from(freeDict.labels));  // ["eq"]
 *
 * const method = traitMethodTerm(dict, "lt");
 * const freeMethod = computeFreeTerms(state, method);
 * console.log("method labels:", Array.from(freeMethod.labels));  // ["lt"]
 * ```
 *
 * @example Match patterns
 * ```ts
 * import { computeFreeTerms, matchTerm, recordPattern, varPattern } from "system-f-omega";
 * import { freshState } from "./helpers.js";
 *
 * const state = freshState();
 * const match = {
 *   match: {
 *     scrutinee: { var: "rec" },
 *     cases: [[recordPattern([["x", varPattern("a")]]), { var: "a" }]]
 *   }
 * };
 * const freeMatch = computeFreeTerms(state, match);
 * console.log("match terms:", Array.from(freeMatch.terms));  // ["rec"]
 * console.log("pat vars:", Array.from(freeMatch.labels));    // ["x"]
 * ```
 *
 * @internal Dependency analysis
 * @see {@link computeFreeTypes} Type names
 * @see {@link computeFreePatterns} Pat names
 * @see {@link importModule} Uses for deps
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
 * Imports module `from` into `into` (deps + renaming + topo-sort).
 *
 * **Purpose**: Module system:
 * 1. Collect deps (`roots` + transitive).
 * 2. Check root conflicts.
 * 3. Auto-rename deps (`allowOverrides` or fresh names).
 * 4. Topo-sort → rename → append/merge.
 *
 * Errors: `circular_import`, `duplicate_binding`.
 *
 * @param args.from - Source state
 * @param args.into - Target state
 * @param args.roots - Root names
 * @param args.aliases - User renames (optional)
 * @param args.allowOverrides - Replace conflicts (optional)
 * @returns New state or error
 *
 * @example Success: Simple import
 * ```ts
 * import { freshState, addType, addTerm, importModule, starKind, conType, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 * from = addTerm(from, "x", { con: { name: "42", type: conType("Int") } }).ok;
 *
 * let into = freshState();
 * into = addType(into, "Bool", starKind).ok;
 *
 * const result = importModule({ from, into, roots: ["Int", "x"] });
 * console.log("imported:", "ok" in result);
 * console.log(showContext(result.ok.ctx));
 * // "...Type: Bool = *\nType: Int = *\nTerm: x = Int"
 * ```
 *
 * @example User aliases
 * ```ts
 * import { freshState, addType, importModule, starKind, conType, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int32", starKind).ok;
 *
 * let into = freshState();
 * const result = importModule({
 *   from,
 *   into,
 *   roots: ["Int32"],
 *   aliases: { types: { "Int32": "Int" } }
 * });
 * console.log("aliased:", "ok" in result);
 * console.log(showContext(result.ok.ctx));
 * // "Type: Int = *"
 * ```
 *
 * @example Auto-rename conflict (deps)
 * ```ts
 * import { freshState, addType, importModule, starKind, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;  // Dep
 * from.ctx.push({ type: { name: "Conflict", kind: starKind } });  // Root + dep
 *
 * let into = freshState();
 * into = addType(into, "Conflict", starKind).ok;  // Conflicts dep
 *
 * const result = importModule({ from, into, roots: ["Conflict"] });
 * console.log("renamed:", "ok" in result);
 * console.log("new Int:", result.ok.ctx.find(b => b.type?.name === "Int"));  // Exists
 * console.log("dep Int:", result.ok.ctx.find(b => b.type?.name === "Int_1"));  // Renamed
 * ```
 *
 * @example Duplicate root error
 * ```ts
 * import { freshState, addType, importModule, starKind } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;  // Duplicate
 *
 * const result = importModule({ from, into, roots: ["Int"] });
 * console.log("duplicate err:", "duplicate_binding" in result.err);  // true
 * ```
 *
 * @example allowOverrides merges
 * ```ts
 * import { freshState, addType, importModule, starKind, showContext } from "system-f-omega";
 *
 * let from = freshState();
 * from = addType(from, "Int", starKind).ok;  // Override target
 *
 * let into = freshState();
 * into = addType(into, "Int", starKind).ok;
 *
 * const result = importModule({ from, into, roots: ["Int"], allowOverrides: true });
 * console.log("overridden:", "ok" in result);
 * console.log(showContext(result.ok.ctx));  // Single Int
 * ```
 *
 * @see {@link collectDependencies} Dep collection
 * @see {@link renameBinding} Applies renames
 * @see {@link topoSortBindings} Ordering
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
 * Collects transitive dependencies from `roots` (DFS + cycle detection).
 *
 * **Purpose**: Module deps: `roots` → all referenced names.
 * Detects cycles via visiting stack.
 *
 * @param state - Source state
 * @param roots - Root binding names
 * @returns Dep set or `circular_import`
 *
 * @example Success: Transitive chain
 * ```ts
 * import { freshState, addType, addTypeAlias, collectDependencies, starKind, varType, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "A", starKind).ok;  // Root
 * state = addType(state, "B", starKind).ok;  // A deps B
 * state = addType(state, "C", starKind).ok;  // B deps C
 * state.ctx.push({ type_alias: { name: "AliasA", params: [], kinds: [], body: conType("B") } });  // A → AliasA → B
 * state.ctx.push({ type_alias: "AliasB", params: [], kinds: [], body: conType("C") });
 *
 * const result = collectDependencies(state, ["A"]);
 * console.log("deps:", Array.from(result.ok));  // ["A", "AliasA", "B", "AliasB", "C"]
 * ```
 *
 * @example Cycle error
 * ```ts
 * import { freshState, addType, addTypeAlias, collectDependencies, starKind, conType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "A", starKind).ok;
 * state.ctx.push({ type_alias: { name: "AliasA", params: [], kinds: [], body: conType("A") } });  // A → AliasA → A (cycle)
 *
 * const result = collectDependencies(state, ["A"]);
 * console.log("cycle:", "circular_import" in result.err);  // true
 * ```
 *
 * @example Missing binding (silent)
 * ```ts
 * import { freshState, collectDependencies } from "system-f-omega";
 *
 * const state = freshState();
 * const result = collectDependencies(state, ["Missing"]);
 * console.log("missing ok:", "ok" in result && result.ok.size === 0);  // true
 * ```
 *
 * @internal Module dep collector
 * @see {@link importModule} Uses deps
 * @see {@link bindingDependencies} Single binding deps
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
 * Adds term binding after inferring its type.
 *
 * **Purpose**: REPL-style: `let x = term` → infer + bind.
 * Errors from `inferType`/`addBinding`.

 * @param state - Checker state
 * @param name - Binding name
 * @param term - Term to bind
 * @returns New state or error
 *
 * @example Success: Constant
 * ```ts
 * import { freshState, addType, addTerm, conTerm, conType, starKind, showContext, inferType, varTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "fortyTwo", conTerm("42", conType("Int"))).ok;
 *
 * const result = inferType(state, varTerm("fortyTwo"));
 * console.log("added:", "ok" in result);  // true
 * console.log("type:", showType(result.ok));  // "Int"
 * console.log("ctx:", showContext(state.ctx));  // "Term: fortyTwo = Int"
 * ```
 *
 * @example Success: Lambda
 * ```ts
 * import { freshState, addType, addTerm, lamTerm, varTerm, conType, starKind, showContext, inferType, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTerm(state, "id", lamTerm("x", conType("Int"), varTerm("x"))).ok;
 *
 * console.log("ctx:", showContext(state.ctx));  // "Term: id = (Int → Int)"
 * ```
 *
 * @example Failure: Unbound var
 * ```ts
 * import { freshState, addTerm, varTerm, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addTerm(state, "bad", varTerm("missing"));
 * console.log("error:", showError(result.err));  // "Unbound identifier: missing"
 * ```
 *
 * @see {@link inferType} Infers type
 * @see {@link termBinding} Creates binding
 * @see {@link addBinding} Adds to ctx
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
 * Adds type constructor binding (no kind inference).
 *
 * **Purpose**: Binds type names to kinds: `Int :: *`, `List :: * → *`.
 * Errors only on duplicates.

 * @param state - Checker state
 * @param name - Type name (`"Int"`)
 * @param kind - Kind (`*`, `*→*`)
 * @returns New state or error
 *
 * @example Success: Primitive type
 * ```ts
 * import { freshState, addType, starKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * console.log(showContext(state.ctx));  // "Type: Int = *"
 * ```
 *
 * @example Success: HKT constructor
 * ```ts
 * import { freshState, addType, starKind, arrowKind, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "List", arrowKind(starKind, starKind)).ok;
 * console.log(showContext(state.ctx));  // "Type: List = (* → *)"
 * ```
 *
 * @example Failure: Duplicate
 * ```ts
 * import { freshState, addType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const result = addType(state, "Int", starKind);
 * console.log("duplicate:", showError(result.err));  // "Duplicate binding for 'Int'..."
 * ```
 *
 * @example Usage: Type in inference
 * ```ts
 * import { freshState, addType, inferType, conTerm, starKind, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * const result = inferType(state, conTerm("42", { con: "Int" }));
 * console.log("inferred:", showType(result.ok));  // "Int"
 * ```
 *
 * @see {@link typeBinding} Creates binding
 * @see {@link addBinding} Adds to ctx
 * @see {@link checkKind} Uses bindings
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
 * Adds parametric type alias after kind-checking body.
 *
 * **Purpose**: Defines aliases: `type Id<A> = A`. Recursive ctx includes self.
 * Errors: unbound/kind mismatch in body.
 *
 * @param state - Checker state
 * @param name - Alias name (`"Id"`)
 * @param params - Param names `["A"]`
 * @param kinds - Param kinds `[starKind]`
 * @param body - RHS type
 * @returns New state or error
 *
 * @example Success: Basic alias
 * ```ts
 * import { freshState, addType, addTypeAlias, starKind, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Id", ["A"], [starKind], varType("A")).ok;
 * console.log(showContext(state.ctx));
 * // "...\nType Alias: Id<A::*> = A"
 * ```
 *
 * @example Success: Recursive alias
 * ```ts
 * import { freshState, addType, addTypeAlias, starKind, muType, tupleType, varType, appType, conType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTypeAlias(state, "Stream", ["A"], [starKind],
 *   muType("self", tupleType([varType("A"), appType(conType("Stream"), varType("A"))]))
 * ).ok;
 * console.log("recursive ok:", "ok" in state);  // true
 * ```
 *
 * @example Failure: Unbound var
 * ```ts
 * import { freshState, addTypeAlias, starKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addTypeAlias(state, "Bad", ["A"], [starKind], varType("B"));
 * console.log("unbound:", showError(result.err));  // "Unbound identifier: B"
 * ```
 *
 * @example Failure: Wrong body kind
 * ```ts
 * import { freshState, addTypeAlias, starKind, lamType, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addTypeAlias(state, "Bad", ["A"], [starKind],
 *   lamType("X", starKind, varType("X"))  // * → * (not *)
 * );
 * console.log("kind err:", showError(result.err));  // "Kind mismatch..."
 * ```
 *
 * @see {@link typeAliasBinding} Creates binding
 * @see {@link normalizeType} Expands aliases
 * @see {@link checkKind} Validates body
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
 * Adds enum definition after kind-checking variants (recursive-aware).
 *
 * **Purpose**: Defines ADTs: `enum Option<T>: None | Some(T)`.
 * - Computes kind (`params → *`).
 * - Validates fields `:: *` (self ctx).
 * - Detects self-refs → `recursive`.
 * Errors: kind/unbound/dup.

 * @param state - Checker state
 * @param name - Enum name
 * @param params - Param names/kinds
 * @param variants - Cases `[[label, scheme], ...]`
 * @param recursive - Assume recursive (defaults `true`)
 * @returns New state or error
 *
 * @example Success: Non-recursive enum
 * ```ts
 * import { freshState, addType, addEnum, starKind, showContext } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Unit", starKind).ok;
 * state = addEnum(state, "Color", [], [], [
 *   ["Red", tupleType([])],
 *   ["Blue", tupleType([])]
 * ]).ok;
 * console.log("added:", showContext(state.ctx));  // "Enum: Color = ..."
 * ```
 *
 * @example Success: Recursive list
 * ```ts
 * import { freshState, addType, addEnum, starKind, varType, appType, conType, showContext } from "system-f-omega";
 * import { tupleType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addEnum(state, "List", ["T"], [starKind], [
 *   ["Nil", tupleType([])],
 *   ["Cons", tupleType([conType("T"), appType(conType("List"), varType("T"))])]
 * ], true).ok;
 * console.log("recursive:", state.ctx.find(b => b.enum?.recursive));  // true
 * ```
 *
 * @example Failure: Wrong variant kind
 * ```ts
 * import { freshState, addEnum, starKind, showError } from "system-f-omega";
 * import { lamType, varType } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addEnum(state, "Bad", ["T"], [starKind], [
 *   ["Case", lamType("X", starKind, varType("X"))]  // * → * (not *)
 * ]);
 * console.log("kind err:", showError(result.err));  // "Kind mismatch... in enum Bad variant Case"
 * ```
 *
 * @example Failure: Unbound in variant
 * ```ts
 * import { freshState, addEnum, starKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addEnum(state, "Bad", ["T"], [starKind], [["Case", varType("Missing")]]);
 * console.log("unbound:", showError(result.err));  // "Unbound identifier: Missing"
 * ```
 *
 * @example Failure: Duplicate enum
 * ```ts
 * import { freshState, addEnum, starKind, tupleType, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addEnum(state, "Color", [], [], [["Red", tupleType([])]]).ok;
 * const result = addEnum(state, "Color", [], [], [["Blue", tupleType([])]]);
 * console.log("duplicate:", showError(result.err));  // "Duplicate binding for 'Color'..."
 * ```
 *
 * @see {@link enumDefBinding} Creates binding
 * @see {@link normalizeType} Expands enums
 * @see {@link checkKind} Validates fields
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
 * Adds trait definition after kind-checking methods `:: *`.
 *
 * **Purpose**: Defines interfaces: `trait Eq<A>: eq : A → Bool`.
 * Validates methods in extended ctx (`typeParam` bound).
 * Errors: unbound/kind/dup.

 * @param state - Checker state
 * @param name - Trait name (`"Eq"`)
 * @param typeParam - Param (`"A"`)
 * @param kind - Param kind
 * @param methods - Signatures `[[name, type], ...]`
 * @returns New state or error
 *
 * @example Success: Basic trait
 * ```ts
 * import { freshState, addType, addTraitDef, starKind, arrowType, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [
 *   ["eq", arrowType(varType("A"), varType("Bool"))]
 * ]).ok;
 * console.log(showContext(state.ctx));
 * // "...\nTrait: Eq = TraitDef (Eq A = *\n  eq : (A → Bool))"
 * ```
 *
 * @example Success: HKT trait
 * ```ts
 * import { freshState, addType, addTraitDef, starKind, arrowKind, arrowType, varType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Functor", "F", arrowKind(starKind, starKind), [
 *   ["map", arrowType(varType("F"), varType("F"))]
 * ]).ok;
 * console.log(showContext(state.ctx));
 * // "...\nTrait: Functor = TraitDef (Functor F = (* → *)\n  map : (F → F))"
 * ```
 *
 * @example Failure: Wrong method kind
 * ```ts
 * import { freshState, addTraitDef, starKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addTraitDef(state, "Bad", "A", starKind, [["m", varType("A")]]);
 * console.log("kind err:", showError(result.err));  // "Kind mismatch..."
 * ```
 *
 * @example Failure: Unbound in method
 * ```ts
 * import { freshState, addTraitDef, starKind, varType, showError } from "system-f-omega";
 *
 * const state = freshState();
 * const result = addTraitDef(state, "Bad", "A", starKind, [["m", varType("Missing")]]);
 * console.log("unbound:", showError(result.err));  // "Unbound identifier: Missing"
 * ```
 *
 * @example Failure: Duplicate trait
 * ```ts
 * import { freshState, addTraitDef, starKind, arrowType, varType, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(varType("A"), varType("Bool"))]]).ok;
 * const result = addTraitDef(state, "Eq", "A", starKind, [["eq", varType("Bool")]]);
 * console.log("duplicate:", showError(result.err));  // "Duplicate binding for 'Eq'..."
 * ```
 *
 * @see {@link traitDefBinding} Creates binding
 * @see {@link checkKind} Validates methods
 * @see {@link addBinding} Adds to ctx
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
 * Adds trait impl after validating dictionary.
 *
 * **Purpose**: Registers `trait` impl for `type` via `dict`.
 * Calls `inferDictType` → `traitImplBinding` → `addBinding`.
 * Errors: dict validation, dup.

 * @param state - Checker state
 * @param trait - Trait name (`"Eq"`)
 * @param type - Impl type (`Int`)
 * @param dict - Dictionary term
 * @returns New state or error
 *
 * @example Success: Valid impl
 * ```ts
 * import { freshState, addType, addTraitDef, addTraitImpl, dictTerm, conType, lamTerm, varTerm, conTerm, starKind, arrowType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dict = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addTraitImpl(state, "Eq", conType("Int"), dict).ok;
 * console.log(showContext(state.ctx));
 * // "...\nImpl: Eq = dict Eq<Int> { eq = λx:Int.true }: Int"
 * ```
 *
 * @example Failure: Missing method
 * ```ts
 * import { freshState, addType, addTraitDef, addTraitImpl, dictTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")], ["lt", conType("Bool")]]).ok;
 * const badDict = dictTerm("Eq", conType("Int"), [["eq", conType("Int")]]);
 * const result = addTraitImpl(state, "Eq", conType("Int"), badDict);
 * console.log("missing:", showError(result.err));  // "Missing method 'lt'..."
 * ```
 *
 * @example Failure: Wrong dict trait/type
 * ```ts
 * import { freshState, addType, addTraitDef, addTraitImpl, dictTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")]]).ok;
 * const wrongDict = dictTerm("WrongTrait", conType("String"), [["eq", conType("Bool")]]);
 * const result = addTraitImpl(state, "Eq", conType("Int"), wrongDict);
 * console.log("wrong dict:", showError(result.err));  // Dict validation error
 * ```
 *
 * @see {@link inferDictType} Validates dict
 * @see {@link traitImplBinding} Creates binding
 * @see {@link addBinding} Adds to ctx
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
 * Adds dictionary binding after inferring dict type.
 *
 * **Purpose**: Binds dict var: `let eqInt = dict Eq<Int> { ... }`.
 * Calls `inferType(dict)` → `dictBinding`.
 * Errors from inference/dup.

 * @param state - Checker state
 * @param name - Dict var (`"eqInt"`)
 * @param dict - DictTerm
 * @returns New state or error
 *
 * @example Success: Basic dict
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, conType, lamTerm, varTerm, conTerm, starKind, arrowType, showContext } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dt = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addDict(state, "eqInt", dt).ok;
 * console.log(showContext(state.ctx));
 * // "...\nDict: eqInt = Trait Eq : Int"
 * ```
 *
 * @example Inference after add
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, inferType, traitMethodTerm, conType, starKind, arrowType, lamTerm, varTerm, conTerm, showType } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addType(state, "Bool", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", arrowType(conType("A"), conType("Bool"))]]).ok;
 * const dt = dictTerm("Eq", conType("Int"), [["eq", lamTerm("x", conType("Int"), conTerm("true", conType("Bool")))]]);
 * state = addDict(state, "eqInt", dt).ok;
 *
 * const method = traitMethodTerm({ var: "eqInt" }, "eq");
 * const result = inferType(state, method);
 * console.log("method:", showType(result.ok));  // "(Int → Bool)"
 * ```
 *
 * @example Failure: Missing method
 * ```ts
 * import { freshState, addType, addTraitDef, addDict, dictTerm, conType, starKind, showError } from "system-f-omega";
 *
 * let state = freshState();
 * state = addType(state, "Int", starKind).ok;
 * state = addTraitDef(state, "Eq", "A", starKind, [["eq", conType("Bool")], ["lt", conType("Bool")]]).ok;
 * const badDict = dictTerm("Eq", conType("Int"), [["eq", conType("Int")]]);
 * const result = addDict(state, "bad", badDict);
 * console.log("missing:", showError(result.err));  // "Missing method 'lt'..."
 * ```
 *
 * @see {@link inferType} Infers dict
 * @see {@link dictBinding} Creates binding
 * @see {@link addBinding} Adds to ctx
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
