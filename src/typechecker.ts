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
  TraitDef,
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
import { err, ok } from "./types.js";

export const typeEq = (left: Type, right: Type): TypeEqConstraint => ({
  type_eq: { left, right },
});
export const kindEq = (left: Kind, right: Kind): KindEqConstraint => ({
  kind_eq: { left, right },
});
export const hasKind = (ty: Type, kind: Kind, state: TypeCheckerState) => ({
  has_kind: { ty, kind, state },
});
export const hasType = (term: Term, ty: Type, state: TypeCheckerState) => ({
  has_type: { term, ty, state },
});

export type InferMode =
  | { infer: null } // Infer type arguments
  | { check: Type }; // Check against expected type

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

export const starKind: Kind = { star: null };
export const neverType = { never: null };

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

export const isMetaVar = (type: Type): type is MetaType => "evar" in type;

export function freshMetaVar(env: MetaEnv, kind: Kind = starKind): MetaType {
  const name = `?${env.counter++}`;
  env.kinds.set(name, kind);
  return { evar: name };
}

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

// Recurse, substitute into body, then tyapp the outer fresh
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

export function isAssignableTo(
  state: TypeCheckerState,
  from: Type,
  to: Type,
): boolean {
  if (isBottom(state, from)) return true; // ⊥ <: anything
  if (isBottom(state, to)) return isBottom(state, from); // anything <: ⊥ only if ⊥
  return typesEqual(state, from, to); // Otherwise, equality
}

// Show patterns for debugging
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

// Extract all variable bindings from a pattern
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

// Pretty printing
export function showKind(k: Kind): string {
  if ("star" in k) return "*";
  if ("arrow" in k)
    return `(${showKind(k.arrow.from)} → ${showKind(k.arrow.to)})`;
  return "unknown";
}

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

// Verify all trait constraints are satisfied
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

// Updated checkExhaustive
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

// Check if a pattern matches a type and extract bindings
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

// Updated checkRecordPattern
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

export function substituteType(
  target: string,
  replacement: Type,
  inType: Type,
  avoidInfinite: Set<string> = new Set(),
): Type {
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

export const isStarKind = (kind: Kind) => "star" in kind;

export const kindsEqual = (left: Kind, right: Kind): boolean =>
  ("star" in left && "star" in right) ||
  ("arrow" in left &&
    "arrow" in right &&
    kindsEqual(left.arrow.from, right.arrow.from) &&
    kindsEqual(left.arrow.to, right.arrow.to));

// Updated checkKind function
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

export function unifyMetaVar(
  state: TypeCheckerState,
  evar: string,
  ty: Type,
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  // Follow existing solution if solved
  if (state.meta.solutions.has(evar)) {
    const existing = state.meta.solutions.get(evar)!;
    return unifyTypes(state, existing, ty, worklist, subst); // Recursive unify
  }

  // Check if ty contains evar (occurs)
  if (occursCheckEvar(state.meta, evar, ty)) {
    return err({ cyclic: evar });
  }

  // Bind locally first (for this unification), then solve globally later if needed
  // (Or solve globally immediately if no local subst conflicts)
  const currentSubstTy = applySubstitution(state, subst, ty); // Apply local subst to ty
  subst.set(evar, currentSubstTy); // Bind in subst (allows propagation)
  return ok(null);
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

export function unifyKinds(left: Kind, right: Kind): Result<TypingError, null> {
  if (kindsEqual(left, right)) return ok(null);
  return err({ kind_mismatch: { expected: left, actual: right } });
}

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

// Bidirectional type checking - check a term against an expected type
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

// ./src/typechecker.ts (cont.)
// Typing judgment: Γ ⊢ e : τ
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

function inferUnfoldType(state: TypeCheckerState, term: UnfoldTerm) {
  const termType = inferType(state, term.unfold);
  if ("err" in termType) return termType;

  if (!("mu" in termType.ok)) return err({ not_a_function: termType.ok });

  const unfoldedType = substituteType(
    termType.ok.mu.var,
    termType.ok,
    termType.ok.mu.body,
    new Set([termType.ok.mu.var]),
  );

  return ok(unfoldedType);
}

function inferFoldType(state: TypeCheckerState, term: FoldTerm) {
  const muKind = checkKind(state, term.fold.type);
  if ("err" in muKind) return muKind;

  if (!("mu" in term.fold.type))
    return err({
      type_mismatch: { expected: term.fold.type, actual: term.fold.type },
    });

  const unfoldedTypeSubstituded = substituteType(
    term.fold.type.mu.var,
    term.fold.type,
    term.fold.type.mu.body,
    new Set([term.fold.type.mu.var]),
  );

  const unfoldedType = normalizeType(state, unfoldedTypeSubstituded);

  const termType = inferType(state, term.fold.term);
  if ("err" in termType) return termType;

  if (!isAssignableTo(state, termType.ok, unfoldedType))
    return err({
      type_mismatch: {
        expected: unfoldedType,
        actual: termType.ok,
      },
    });

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

// NEW Helper: Check injected value against field type (handles unit, single, tuple/multi-field)
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

// Helper to extract spine args (left-assoc nested apps)
// Replace existing getSpineArgs function
export function getSpineArgs(ty: Type): Type[] {
  const args: Type[] = [];
  let current = ty;
  while ("app" in current) {
    args.unshift(current.app.arg);
    current = current.app.func;
  }
  return args;
}

// Add new helper to get the spine head (the constructor)
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

  for (const required of requiredMethods)
    if (!providedMethods.has(required))
      return err({
        missing_method: { trait: term.dict.trait, method: required },
      });

  // Bind 'self' to dictType in a local method context for each impl inference
  const methodCtx: Context = [
    ...state.ctx,
    { term: { name: "self", type: dictType } },
  ];

  for (const [methodName, methodImpl] of term.dict.methods) {
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
 * Convert a structural variant into a higher‑order type constructor (λ form)
 * guided by the given `selfKind`.
 *
 * Example:
 *   variant = <Left: a | Right: b>
 *   selfKind = * → * → *
 *   =>
 *     λt0::* . λt1::* . <Left: t0 | Right: t1>
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

// Helper to collect unbound meta variables from a type
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

// Worklist constraint solver
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

// Top-level type checking function
export const typecheck = inferType;

// Type checking with constraint solving (for more complex scenarios)
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

// Update the normalizeType function
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
      if (enumBinding && "enum" in enumBinding) {
        const def = enumBinding.enum;
        const spineArgs = getSpineArgs(ty);
        if (spineArgs.length === def.params.length) {
          const structuralVariant: [string, Type][] = [];
          for (const [label, fieldScheme] of def.variants) {
            let instField = fieldScheme;
            for (let i = 0; i < def.params.length; i++) {
              instField = substituteType(
                def.params[i]!,
                spineArgs[i]!,
                instField,
                seen,
              );
            }
            structuralVariant.push([
              label,
              normalizeType(state, instField, seen),
            ]);
          }
          return { variant: structuralVariant };
        }
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

// When you encounter a polymorphic value in application position:
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

// Helper to calculate the arity of a kind
export function kindArity(kind: Kind): number {
  if ("star" in kind) return 0;

  let acc = 0;
  while ("arrow" in kind) {
    acc += 1;
    kind = kind.arrow.to;
  }

  return acc;
}

// Helper to check if type has unbound metas
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

// Helper to collect type variables from a type
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

export function computeStrippedKind(
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

export function stripAppsByArity(
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

export const arrowKind = (from: Kind, to: Kind): Kind => ({
  arrow: { from, to },
});

// Type Constructors:
export const varType = (name: string): VarType => ({ var: name });
export const arrowType = (from: Type, to: Type): Type => ({
  arrow: { from, to },
});
export const forallType = (name: string, kind: Kind, body: Type) => ({
  forall: { var: name, kind, body },
});
export const appType = (func: Type, arg: Type) => ({ app: { func, arg } });
export const lamType = (name: string, kind: Kind, body: Type) => ({
  lam: { var: name, kind, body },
});
export const conType = (con: string) => ({ con });
export const recordType = (record: [string, Type][]) => ({ record });
export const variantType = (variant: [string, Type][]) => ({ variant });
export const muType = (var_name: string, body: Type): Type => ({
  mu: { var: var_name, body },
});
export const tupleType = (elements: Type[]): Type => ({ tuple: elements });
export const boundedForallType = (
  name: string,
  kind: Kind,
  constraints: TraitConstraint[],
  body: Type,
): Type => ({
  bounded_forall: { var: name, kind, constraints, body },
});

// Term Constructors:
export const varTerm = (name: string) => ({ var: name });
export const lamTerm = (arg: string, type: Type, body: Term) => ({
  lam: { arg, type, body },
});
export const appTerm = (callee: Term, arg: Term) => ({ app: { callee, arg } });
export const tylamTerm = (name: string, kind: Kind, body: Term) => ({
  tylam: { var: name, kind, body },
});
export const tyappTerm = (term: Term, type: Type) => ({
  tyapp: { term, type },
});
export const conTerm = (name: string, type: Type) => ({ con: { name, type } });
export const recordTerm = (record: [string, Term][]) => ({ record });
export const projectTerm = (record: Term, label: string) => ({
  project: { record, label },
});
export const injectTerm = (label: string, value: Term, variant_type: Type) => ({
  inject: { label, value, variant_type },
});
export const matchTerm = (scrutinee: Term, cases: [Pattern, Term][]): Term => ({
  match: { scrutinee, cases },
});
export const foldTerm = (type: Type, term: Term): Term => ({
  fold: { type, term },
});
export const unfoldTerm = (term: Term): Term => ({
  unfold: term,
});
export const tupleTerm = (elements: Term[]): Term => ({ tuple: elements });
export const tupleProjectTerm = (tuple: Term, index: number): Term => ({
  tuple_project: { tuple, index },
});
export const letTerm = (name: string, value: Term, body: Term): Term => ({
  let: { name, value, body },
});
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
export const traitAppTerm = (term: Term, type: Type, dicts: Term[]): Term => ({
  trait_app: { term, type, dicts },
});

export const dictTerm = (
  trait: string,
  type: Type,
  methods: [string, Term][],
): Term => ({
  dict: { trait, type, methods },
});

export const traitMethodTerm = (dict: Term, method: string): Term => ({
  trait_method: { dict, method },
});

// Pattern Constructors
export const varPattern = (name: string): Pattern => ({ var: name });
export const wildcardPattern = (): Pattern => ({ wildcard: null });
export const conPattern = (name: string, type: Type): Pattern => ({
  con: { name, type },
});
export const recordPattern = (fields: [string, Pattern][]): Pattern => ({
  record: fields,
});
export const variantPattern = (label: string, pattern: Pattern): Pattern => ({
  variant: { label, pattern },
});
export const tuplePattern = (elements: Pattern[]): Pattern => ({
  tuple: elements,
});

export const unitType: Type = { tuple: [] };
export const unitValue: Term = { tuple: [] };

export const showContext = (context: Context) =>
  context.map((t) => showBinding(t)).join("\n");

export const showTraitDef = (t: TraitDef) => {
  return `TraitDef (${t.name} ${t.type_param} = ${showKind(t.kind)}\n${t.methods.map((y) => `  ${y[0]} : ${showType(y[1])}`).join("\n")})`;
};

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

export const termBinding = (name: string, type: Type) => ({
  term: { name, type },
});
export const typeBinding = (name: string, kind: Kind) => ({
  type: { name, kind },
});
export const typeAliasBinding = (
  name: string,
  params: string[],
  kinds: Kind[],
  body: Type,
) => ({
  type_alias: { name, params, kinds, body },
});
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

export const traitImplBinding = (trait: string, type: Type, dict: Term) => ({
  trait_impl: { trait, type, dict },
});

export const dictBinding = (name: string, trait: string, type: Type) => ({
  dict: { name, trait, type },
});
export const enumDefBinding = (
  name: string,
  kind: Kind,
  params: string[],
  variants: [string, FieldScheme][],
) => ({
  enum: { name, kind, params, variants },
});

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
  if ("trait_impl" in b) return b.trait_impl.trait;
  if ("type_alias" in b) return b.type_alias.name;
  if ("enum" in b) return b.enum.name;
  return "<unknown>";
}

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
