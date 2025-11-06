// ./src/typechecker.ts
import type {
  AppTerm,
  AppType,
  ArrowType,
  Binding,
  BoundedForallType,
  ConPattern,
  Constraint,
  ConTerm,
  ConType,
  Context,
  DictTerm,
  FoldTerm,
  ForallType,
  InjectTerm,
  Kind,
  KindEqConstraint,
  LamTerm,
  LamType,
  LetTerm,
  MatchTerm,
  MuType,
  Pattern,
  ProjectTerm,
  RecordPattern,
  RecordTerm,
  RecordType,
  Result,
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
  TypeEqConstraint,
  TypingError,
  UnfoldTerm,
  VariantType,
  VarTerm,
  VarType,
} from "./types.js";
import { err, ok } from "./types.js";

export const typeEq = (left: Type, right: Type): TypeEqConstraint => ({
  type_eq: { left, right },
});
export const kindEq = (left: Kind, right: Kind): KindEqConstraint => ({
  kind_eq: { left, right },
});
export const hasKind = (ty: Type, kind: Kind, context: Context) => ({
  has_kind: { ty, kind, context },
});
export const hasType = (term: Term, ty: Type, context: Context) => ({
  has_type: { term, ty, context },
});

export type Worklist = Constraint[];
export type Substitution = Map<string, Type>;

export type InferMode =
  | { infer: null } // Infer type arguments
  | { check: Type }; // Check against expected type

export function inferTypeWithMode(
  context: Context,
  term: Term,
  mode: InferMode,
): Result<TypingError, Type> {
  // Delegate based on mode
  if ("check" in mode) {
    const result = checkType(context, term, mode.check);
    if ("ok" in result) return ok(result.ok.type);
    return result;
  }
  return inferType(context, term);
}

export type MetaVar = { meta: number };

export const starKind: Kind = { star: null };
export const neverType = { never: null };
let mvarCount = 0;
const metaVarSolutions = new Map<number, Type>();

// Helper: Create a temporary string-keyed subst from global meta solutions
// Maps "?N" (string var names) to their solved Types
export function getMetaSubstitution(): Substitution {
  const subst = new Map<string, Type>();
  for (const [id, solvedType] of metaVarSolutions.entries())
    subst.set(`?${id}`, solvedType);

  return subst;
}

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

export const metaKind = new Map<string, Kind>();

export const isMetaVar = (type: Type): type is VarType =>
  "var" in type && metaKind.has(type.var);

export function freshMetaVar(): VarType {
  const varType = { var: `?${mvarCount++}` };
  metaKind.set(varType.var, starKind);
  return varType;
}

export const isBottom = (type: Type) => "never" in normalizeType(type);

export function solveMetaVar(
  metaVar: string,
  solution: Type,
): Result<TypingError, null> {
  if (metaVarSolutions.has(parseInt(metaVar.slice(1), 10))) {
    const existing = metaVarSolutions.get(parseInt(metaVar.slice(1), 10))!;
    if (!typesEqual(existing, solution))
      return err({ type_mismatch: { expected: existing, actual: solution } });
  } else {
    metaVarSolutions.set(parseInt(metaVar.slice(1), 10), solution);
  }
  return ok(null);
}

// Recurse, substitute into body, then tyapp the outer fresh
export function instantiateTerm(
  term: Term,
  fresh: () => Type = freshMetaVar,
  context: Context = [], // Optional: for occurs-check/augment rigid vars if needed
): Term {
  // Recurse first: Instantiate inner tytams (post-order)
  let instBody = term;
  if ("tylam" in term) {
    // For this tytam: Instantiate the body first (inner first)
    instBody = instantiateTerm(term.tylam.body, fresh, context);
    // Now, create fresh for this level and substitute it into the (already-instantiated) body
    const freshType = fresh();
    const subst = new Map<string, Type>([[term.tylam.var, freshType]]);
    // Apply substitution to the body term (updates embedded types like lam.type; recurses on subterms)
    instBody = applySubstitutionToTerm(
      subst,
      instBody,
      new Set([term.tylam.var]),
    );
    // Return as tyapp: Apply the fresh type to the substituted body
    return tyapp_term(instBody, freshType);
  }

  // Recurse on non-tylam cases (e.g., app, lam, match, inject, dict, etc.)
  // Use the existing applySubstitutionToTerm pattern, but since no subst here, just recurse structurally
  if ("app" in term)
    return appTerm(
      instantiateTerm(term.app.callee, fresh, context),
      instantiateTerm(term.app.arg, fresh, context),
    );
  if ("lam" in term)
    return lamTerm(
      term.lam.arg,
      instantiate(term.lam.type, fresh),
      instantiateTerm(term.lam.body, fresh, context),
    );
  if ("tyapp" in term)
    return tyapp_term(
      instantiateTerm(term.tyapp.term, fresh, context),
      instantiate(term.tyapp.type, fresh),
    );
  if ("match" in term)
    return matchTerm(
      instantiateTerm(term.match.scrutinee, fresh, context),
      term.match.cases.map(([pattern, body]) => [
        pattern, // Patterns don't have types to instantiate (structural only)
        instantiateTerm(body, fresh, context),
      ]),
    );
  if ("inject" in term)
    return injectTerm(
      term.inject.label,
      instantiateTerm(term.inject.value, fresh, context),
      instantiate(term.inject.variant_type, fresh), // Instantiate variant type
    );

  if ("dict" in term) {
    return dictTerm(
      term.dict.trait,
      instantiate(term.dict.type, fresh),
      term.dict.methods.map(([name, impl]) => [
        name,
        instantiateTerm(impl, fresh, context),
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
        type: instantiate(c.type, fresh),
      })),
      instantiateTerm(t.body, fresh, context),
    );
  }
  // Instantiate inner body, but don't substitute "Self" (constrained separately)
  // Add similar recursion for fold, unfold, record, project, tuple, let, etc. (structural)
  if ("record" in term)
    return recordTerm(
      term.record.map(([label, field]) => [
        label,
        instantiateTerm(field, fresh, context),
      ]),
    );

  if ("let" in term)
    return letTerm(
      term.let.name,
      instantiateTerm(term.let.value, fresh, context),
      instantiateTerm(term.let.body, fresh, context),
    );

  if ("tuple" in term)
    return tupleTerm(term.tuple.map((t) => instantiateTerm(t, fresh, context)));

  // Default: Recurse on any unrecognized (exhaustive on known constructors)
  return term;
}

export function instantiate(
  type: Type,
  fresh: () => Type = freshMetaVar,
): Type {
  if ("forall" in type) {
    const fv = fresh();
    const instantiatedBody = substituteType(
      type.forall.var,
      fv,
      type.forall.body,
    );
    return instantiate(instantiatedBody, fresh);
  }

  if ("bounded_forall" in type) {
    const fv = fresh();

    // Instantiate constraints
    const instBody = substituteType(
      type.bounded_forall.var,
      fv,
      type.bounded_forall.body,
    );
    // Recurse (ignore constraints for now; assume provided externally)
    return instantiate(instBody, fresh);
  }

  return type;
}

export function subsumes(
  context: Context,
  general: Type, // Supertype (e.g., t_ok)
  specific: Type, // Subtype (e.g., ⊥)
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  // Instantiate foralls in general
  const instGeneral = instantiate(general);

  // Early bottom check: if specific is ⊥, always succeed (⊥ <: anything)
  if (isBottom(specific)) {
    const genKind = checkKind(context, instGeneral, true);
    if ("err" in genKind || !isStarKind(genKind.ok))
      return err({
        type_mismatch: { expected: instGeneral, actual: specific },
      });

    return ok(null);
  }

  // NEW: If general is ⊥, then specific must also be ⊥ (already checked above)
  if (isBottom(instGeneral)) {
    return err({
      type_mismatch: { expected: instGeneral, actual: specific },
    });
  }

  // Otherwise, standard unification
  return unifyTypes(instGeneral, specific, worklist, subst);
}

export function isAssignableTo(from: Type, to: Type): boolean {
  if (isBottom(from)) return true; // ⊥ <: anything
  if (isBottom(to)) return isBottom(from); // anything <: ⊥ only if ⊥
  return typesEqual(from, to); // Otherwise, equality
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
  subst: Substitution,
  term: Term,
  avoidFree: Set<string> = new Set(),
): Term {
  // Apply substitution to the types within the term structure

  if ("var" in term) return term;
  if ("lam" in term) return applySubstitutionToLamTerm(subst, term, avoidFree);
  if ("app" in term) return applySubstitutionToAppTerm(subst, term, avoidFree);
  if ("tylam" in term)
    return applySubstitutionToTyLamTerm(subst, term, avoidFree);
  if ("tyapp" in term)
    return applySubstitutionToTyAppTerm(subst, term, avoidFree);
  if ("con" in term) return applySubstitutionToConTerm(term, subst, avoidFree);
  if ("dict" in term)
    return applySubstitutionToDictTerm(subst, term, avoidFree);
  if ("trait_lam" in term)
    return applySubstitutionToTraitLamTerm(subst, term, avoidFree);
  if ("trait_app" in term)
    return applySubstitutionToTraitAppTerm(subst, term, avoidFree);
  if ("trait_method" in term)
    return applySubstitutionToTraitMethodTerm(subst, term, avoidFree);
  if ("let" in term) return applySubstitutionToLetTerm(subst, term, avoidFree);
  if ("match" in term)
    return applySubstitutionToMatchTerm(subst, term, avoidFree);
  if ("record" in term)
    return applySubstitutionToRecordTerm(term, subst, avoidFree);
  if ("project" in term)
    return applySubstitutionToProjectTerm(subst, term, avoidFree);
  if ("inject" in term)
    return applySubstitutionToInjectTerm(term, subst, avoidFree);
  if ("tuple" in term)
    return applySubstitutionToTupleTerm(term, subst, avoidFree);
  if ("tuple_project" in term)
    return applySubstitutionToTupleProject(subst, term, avoidFree);
  if ("fold" in term)
    return applySubstitutionToFoldTerm(subst, term, avoidFree);
  if ("unfold" in term)
    return applySubstitutionToUnfoldTerm(subst, term, avoidFree);
  // For other term constructors, recurse on subterms
  return term;
}

function applySubstitutionToUnfoldTerm(
  subst: Substitution,
  term: UnfoldTerm,
  avoidFree: Set<string>,
) {
  return unfoldTerm(applySubstitutionToTerm(subst, term.unfold, avoidFree));
}

function applySubstitutionToFoldTerm(
  subst: Substitution,
  term: FoldTerm,
  avoidFree: Set<string>,
) {
  return foldTerm(
    applySubstitution(subst, term.fold.type, avoidFree),
    applySubstitutionToTerm(subst, term.fold.term, avoidFree),
  );
}

function applySubstitutionToTupleProject(
  subst: Substitution,
  term: TupleProjectTerm,
  avoidFree: Set<string>,
) {
  return tupleProjectTerm(
    applySubstitutionToTerm(subst, term.tuple_project.tuple, avoidFree),
    term.tuple_project.index,
  );
}

function applySubstitutionToTupleTerm(
  term: TupleTerm,
  subst: Substitution,
  avoidFree: Set<string>,
) {
  return tupleTerm(
    term.tuple.map((t) => applySubstitutionToTerm(subst, t, avoidFree)),
  );
}

function applySubstitutionToInjectTerm(
  term: InjectTerm,
  subst: Substitution,
  avoidFree: Set<string>,
) {
  return injectTerm(
    term.inject.label,
    applySubstitutionToTerm(subst, term.inject.value, avoidFree),
    applySubstitution(subst, term.inject.variant_type, avoidFree),
  );
}

function applySubstitutionToProjectTerm(
  subst: Substitution,
  term: ProjectTerm,
  avoidFree: Set<string>,
) {
  return projectTerm(
    applySubstitutionToTerm(subst, term.project.record, avoidFree),
    term.project.label,
  );
}

function applySubstitutionToRecordTerm(
  term: RecordTerm,
  subst: Substitution,
  avoidFree: Set<string>,
) {
  return recordTerm(
    term.record.map(([label, field]) => [
      label,
      applySubstitutionToTerm(subst, field, avoidFree),
    ]),
  );
}

function applySubstitutionToMatchTerm(
  subst: Substitution,
  term: MatchTerm,
  avoidFree: Set<string>,
) {
  return matchTerm(
    applySubstitutionToTerm(subst, term.match.scrutinee, avoidFree),
    term.match.cases.map(([pattern, body]) => [
      pattern, // Patterns don't contain types that need substitution
      applySubstitutionToTerm(subst, body, avoidFree),
    ]),
  );
}

function applySubstitutionToLetTerm(
  subst: Substitution,
  term: LetTerm,
  avoidFree: Set<string>,
) {
  return letTerm(
    term.let.name,
    applySubstitutionToTerm(subst, term.let.value, avoidFree),
    applySubstitutionToTerm(subst, term.let.body, avoidFree),
  );
}

function applySubstitutionToTraitMethodTerm(
  subst: Substitution,
  term: TraitMethodTerm,
  avoidFree: Set<string>,
) {
  return traitMethodTerm(
    applySubstitutionToTerm(subst, term.trait_method.dict, avoidFree),
    term.trait_method.method,
  );
}

function applySubstitutionToTraitAppTerm(
  subst: Substitution,
  term: TraitAppTerm,
  avoidFree: Set<string>,
) {
  return {
    trait_app: {
      term: applySubstitutionToTerm(subst, term.trait_app.term, avoidFree),
      type: applySubstitution(subst, term.trait_app.type, avoidFree),
      dicts: term.trait_app.dicts.map((dict) =>
        applySubstitutionToTerm(subst, dict, avoidFree),
      ),
    },
  };
}

function applySubstitutionToTraitLamTerm(
  subst: Substitution,
  term: TraitLamTerm,
  avoidFree: Set<string>,
) {
  {
    const newSubst = new Map(subst);
    newSubst.delete(term.trait_lam.type_var);

    const newConstraints = term.trait_lam.constraints.map((constraint) => ({
      ...constraint,
      type: applySubstitution(newSubst, constraint.type, avoidFree),
    }));

    return {
      trait_lam: {
        ...term.trait_lam,
        constraints: newConstraints,
        body: applySubstitutionToTerm(newSubst, term.trait_lam.body, avoidFree),
      },
    };
  }
}

function applySubstitutionToDictTerm(
  subst: Substitution,
  term: DictTerm,
  avoidFree: Set<string>,
) {
  return dictTerm(
    term.dict.trait,
    applySubstitution(subst, term.dict.type, avoidFree),
    term.dict.methods.map(([name, methodTerm]) => [
      name,
      applySubstitutionToTerm(subst, methodTerm, avoidFree),
    ]),
  );
}

function applySubstitutionToConTerm(
  term: ConTerm,
  subst: Substitution,
  avoidFree: Set<string>,
) {
  return conTerm(
    term.con.name,
    applySubstitution(subst, term.con.type, avoidFree),
  );
}

function applySubstitutionToTyAppTerm(
  subst: Substitution,
  term: TyAppTerm,
  avoidFree: Set<string>,
) {
  return tyapp_term(
    applySubstitutionToTerm(subst, term.tyapp.term, avoidFree),
    applySubstitution(subst, term.tyapp.type, avoidFree),
  );
}

function applySubstitutionToTyLamTerm(
  subst: Substitution,
  term: TyLamTerm,
  avoidFree: Set<string>,
) {
  const newSubst = new Map(subst);
  newSubst.delete(term.tylam.var);

  return tylamTerm(
    term.tylam.var,
    term.tylam.kind,
    applySubstitutionToTerm(newSubst, term.tylam.body, avoidFree),
  );
}

function applySubstitutionToAppTerm(
  subst: Substitution,
  term: AppTerm,
  avoidFree: Set<string>,
) {
  return appTerm(
    applySubstitutionToTerm(subst, term.app.callee, avoidFree),
    applySubstitutionToTerm(subst, term.app.arg, avoidFree),
  );
}

function applySubstitutionToLamTerm(
  subst: Substitution,
  term: LamTerm,
  avoidFree: Set<string>,
) {
  return lamTerm(
    term.lam.arg,
    applySubstitution(subst, term.lam.type, avoidFree),
    applySubstitutionToTerm(subst, term.lam.body, avoidFree),
  );
}

export function checkTraitImplementation(
  ctx: Context,
  trait: string,
  type: Type,
): Result<TypingError, Term> {
  const normalizedType = normalizeType(type, ctx);

  // First, look for exact match
  const impl = ctx.find(
    (b) =>
      "trait_impl" in b &&
      b.trait_impl.trait === trait &&
      typesEqual(b.trait_impl.type, normalizedType),
  );

  if (impl && "trait_impl" in impl) return ok(impl.trait_impl.dict);

  const polymorphicImpls = ctx.filter(
    (b) => "trait_impl" in b && b.trait_impl.trait === trait,
  );

  for (const polyImpl of polymorphicImpls) {
    if ("trait_impl" in polyImpl && polyImpl.trait_impl.dict) {
      const implType = polyImpl.trait_impl.type;

      // Fully normalize BOTH types by beta-reducing all applications
      // This turns ((λt.λu.variant) l) r) into <variant with l, r>
      // and λt.λu.variant into λt.λu.variant (stays as is)

      const normalizedImpl = normalizeType(implType, ctx);
      const normalizedTarget = normalizeType(normalizedType, ctx);

      // Now instantiate the impl (replaces any forall-bound vars with metas)
      const instImplTy = instantiate(normalizedImpl);

      // For the target, if it's a lambda that needs to be applied to match the impl's level,
      // apply it to fresh metas
      let matchingTarget = normalizedTarget;

      // Check if target is still a lambda while impl is not
      if ("lam" in matchingTarget && !("lam" in instImplTy)) {
        // Apply the lambda to fresh metas until it matches the impl's structure

        while ("lam" in matchingTarget) {
          const fv = freshMetaVar();
          matchingTarget = normalizeType(
            substituteType(matchingTarget.lam.var, fv, matchingTarget.lam.body),
            ctx,
          );
        }
      }

      // Try to unify
      const worklist: Worklist = [];
      const subst = new Map<string, Type>();

      const unifyRes = unifyTypes(instImplTy, matchingTarget, worklist, subst);

      if ("ok" in unifyRes) {
        const solveRes = solveConstraints(worklist, subst);

        if ("ok" in solveRes) {
          // Successfully unified - instantiate and substitute into the dict
          const instantiatedDict = instantiateTerm(polyImpl.trait_impl.dict);
          const finalDict = applySubstitutionToTerm(
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
  context: Context,
  constraints: TraitConstraint[],
): Result<TypingError, Term[]> {
  const dicts: Term[] = [];

  for (const constraint of constraints) {
    const result = checkTraitImplementation(
      context,
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
  patterns: Pattern[],
  type: Type,
  ctx: Context,
): Result<TypingError, null> {
  const normType = normalizeType(type, ctx);

  // Nominal check
  if ("app" in normType && "con" in normType.app.func) {
    const conName = normType.app.func.con;
    const spineArgs = getSpineArgs(normType);

    const enumBinding = ctx.find((b) => "enum" in b && b.enum.name === conName);
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
  pattern: Pattern,
  type: Type,
  ctx: Context,
): Result<TypingError, Context> {
  // Variable pattern binds the whole value
  if ("var" in pattern) return ok([{ term: { name: pattern.var, type } }]);

  // Wildcard matches anything, no bindings
  if ("wildcard" in pattern) return ok([]);

  if ("variant" in pattern) {
    if ("mu" in type) {
      const unfolded = substituteType(type.mu.var, type, type.mu.body);
      return checkPattern(pattern, unfolded, ctx);
    }

    const normType = normalizeType(type);

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
      return checkPattern(pattern.variant.pattern, caseType[1], ctx);
    }

    // Nominal
    if ("app" in normType || "con" in normType) {
      const head = "con" in normType ? normType : getSpineHead(normType);
      if (!("con" in head)) return err({ not_a_variant: type });

      const conName = head.con;
      const spineArgs = "con" in normType ? [] : getSpineArgs(normType);

      const enumBinding = ctx.find(
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
      fieldType = normalizeType(fieldType);

      return checkPattern(pattern.variant.pattern, fieldType, ctx);
    }

    return err({ not_a_variant: type });
  }

  // Existing cases (con, record, tuple, etc.)
  if ("con" in pattern) return checkConPattern(pattern, type, ctx);
  if ("record" in pattern) return checkRecordPattern(pattern, type, ctx);
  if ("tuple" in pattern) return checkTuplePattern(pattern, type, ctx);

  // Fallback: No bindings
  return ok([]);
}

function checkTuplePattern(
  pattern: TuplePattern,
  type: Type,
  context: Context,
) {
  // Allow ⊥
  if (!("tuple" in type) && !isBottom(type)) return err({ not_a_tuple: type });

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
    const subResult = checkPattern(subPattern, elementType, context);
    if ("err" in subResult) return subResult;
    bindings.push(...subResult.ok);
  }
  return ok(bindings);
}

const checkConPattern = (
  pattern: ConPattern,
  type: Type,
  _context: Context,
) => {
  return isAssignableTo(pattern.con.type, type)
    ? ok([])
    : err({ type_mismatch: { expected: type, actual: pattern.con.type } });
};

// Helper (add if not already present)
const first = <T, U>(tuple: [T, U]) => tuple[0];

// Updated checkRecordPattern
function checkRecordPattern(
  pattern: RecordPattern,
  type: Type,
  context: Context,
): Result<TypingError, Context> {
  // Handle bottom type: ⊥ matches any record pattern (unreachable code paths, etc.)
  if (isBottom(type)) {
    // Extract bindings from subpatterns (but types are arbitrary since ⊥ <: anything)
    const bindings: Context = [];
    for (const [label, subPattern] of pattern.record) {
      // For bottom, bind subpattern vars to a fresh meta or unit (safe)
      const subResult = checkPattern(subPattern, unitType, context); // Or freshMetaVar()
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
    const subResult = checkPattern(subPattern, fieldType, context);
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
  context: Context,
  type: Type,
  lenient: boolean = false,
): Result<TypingError, Kind> {
  if ("var" in type) return checkVarKind(context, type, lenient);

  if ("con" in type) return checkConKind(context, type, lenient);

  if ("never" in type) return ok(starKind);
  if ("arrow" in type) return checkArrowKind(context, type, lenient);
  if ("forall" in type) return checkForallKind(context, type, lenient);
  if ("bounded_forall" in type)
    return checkBoundedForallKind(context, type, lenient);
  if ("lam" in type) return checkLamKind(context, type, lenient);
  if ("app" in type) return checkAppKind(context, type, lenient);
  if ("record" in type) return checkRecordKind(context, type, lenient);
  if ("variant" in type) return checkVariantKind(context, type, lenient);
  if ("mu" in type) return checkMuKind(context, type, lenient);
  if ("tuple" in type) return checkTupleKind(context, type, lenient);

  throw new Error(`Unknown type: ${Object.keys(type)[0]}`);
}

function checkConKind(context: Context, type: ConType, lenient: boolean) {
  // Lookup kind in context (like vars) for user-defined type constructors
  // (e.g., Option :: * → *)
  const binding = context.find((b) => "type" in b && b.type.name === type.con);
  if (binding && "type" in binding) return ok(binding.type.kind);

  // Unbound con: Error if strict, else assume * for lenient
  // (e.g., forward refs in subtyping)
  return lenient ? ok(starKind) : err({ unbound: type.con });
}

function checkTupleKind(context: Context, type: TupleType, lenient: boolean) {
  // All element types must have kind *
  for (const elemType of type.tuple) {
    const elemKind = checkKind(context, elemType, lenient);
    if ("err" in elemKind) return elemKind;
    if (!isStarKind(elemKind.ok))
      return err({
        kind_mismatch: { expected: starKind, actual: elemKind.ok },
      });
  }
  return ok(starKind);
}

function checkMuKind(context: Context, type: MuType, lenient: boolean) {
  // μα.τ has kind * if τ has kind * in context extended with α::*
  const extendedContext: Context = [
    { type: { name: type.mu.var, kind: starKind } },
    ...context,
  ];

  const bodyKind = checkKind(extendedContext, type.mu.body, lenient);
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({
      kind_mismatch: { expected: starKind, actual: bodyKind.ok },
    });

  return ok(starKind);
}

function checkVariantKind(
  context: Context,
  type: VariantType,
  lenient: boolean,
) {
  // All case types must have kind *
  for (const [_, caseType] of type.variant) {
    const caseKind = checkKind(context, caseType, lenient);
    if ("err" in caseKind) return caseKind;

    if (!isBottom(caseType) && !isStarKind(caseKind.ok)) {
      return err({
        kind_mismatch: { expected: starKind, actual: caseKind.ok },
      });
    }
  }

  return ok(starKind);
}
function checkRecordKind(context: Context, type: RecordType, lenient: boolean) {
  // All field types must have kind *
  for (const [_, fieldType] of type.record) {
    const fieldKind = checkKind(context, fieldType, lenient);
    if ("err" in fieldKind) return fieldKind;

    if (!isStarKind(fieldKind.ok))
      return err({
        kind_mismatch: { expected: starKind, actual: fieldKind.ok },
      });
  }

  return ok(starKind);
}

function checkAppKind(context: Context, type: AppType, lenient: boolean) {
  const funcKind = checkKind(context, type.app.func, lenient);
  if ("err" in funcKind) return funcKind;

  const argKind = checkKind(context, type.app.arg, lenient);
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

function checkLamKind(context: Context, type: LamType, lenient: boolean) {
  const extendedContext: Context = [
    { type: { name: type.lam.var, kind: type.lam.kind } },
    ...context,
  ];

  const bodyKind = checkKind(extendedContext, type.lam.body, lenient);
  if ("err" in bodyKind) return bodyKind;

  return ok(arrow_kind(type.lam.kind, bodyKind.ok));
}

function checkBoundedForallKind(
  context: Context,
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
    ...context,
  ];

  // Check that all constraint types are well-kinded
  for (const constraint of type.bounded_forall.constraints) {
    const constraintKind = checkKind(extendedContext, constraint.type, lenient);
    if ("err" in constraintKind) return constraintKind;

    if (!isStarKind(constraintKind.ok))
      return err({
        kind_mismatch: {
          expected: starKind,
          actual: constraintKind.ok,
        },
      });
  }

  const bodyKind = checkKind(
    extendedContext,
    type.bounded_forall.body,
    lenient,
  );
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: bodyKind.ok } });

  return ok(starKind);
}

function checkVarKind(context: Context, type: VarType, lenient: boolean) {
  if (metaKind.has(type.var)) return ok(metaKind.get(type.var)!);

  const binding = context.find((b) => "type" in b && b.type.name === type.var);
  if (binding && "type" in binding) {
    return ok(binding.type.kind);
  }
  // For subtyping/bottom checks, assume unbound vars have kind * (safe assumption)
  if (lenient) return ok(starKind);
  // Strict mode: unbound is an error
  return err({ unbound: type.var });
}

function checkArrowKind(context: Context, type: ArrowType, lenient: boolean) {
  const fromKind = checkKind(context, type.arrow.from, lenient);
  if ("err" in fromKind) return fromKind;

  const toKind = checkKind(context, type.arrow.to, lenient);
  if ("err" in toKind) return toKind;

  // Both operands must have kind *
  if (!isStarKind(fromKind.ok) || !isStarKind(toKind.ok))
    return err({
      kind_mismatch: { expected: starKind, actual: fromKind.ok },
    });

  return ok(starKind);
}

function checkForallKind(context: Context, type: ForallType, lenient: boolean) {
  const extendedContext: Context = [
    { type: { name: type.forall.var, kind: type.forall.kind } },
    ...context,
  ];

  const bodyKind = checkKind(extendedContext, type.forall.body, lenient);
  if ("err" in bodyKind) return bodyKind;

  if (!isStarKind(bodyKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: bodyKind.ok } });

  return ok(starKind);
}

function typesEqualSpine(left: Type, right: Type): boolean {
  const lArgs = getSpineArgs(left);
  const rArgs = getSpineArgs(right);
  if (lArgs.length !== rArgs.length) return false;
  for (let i = 0; i < lArgs.length; i++) {
    if (!typesEqual(lArgs[i]!, rArgs[i]!)) return false;
  }
  return true;
}

export function typesEqual(left: Type, right: Type): boolean {
  left = normalizeType(left);
  right = normalizeType(right);

  if ("var" in left && "var" in right && left.var === right.var) return true;

  if ("con" in left && "con" in right && left.con === right.con) return true;

  if (
    "app" in left &&
    "con" in left.app.func &&
    "app" in right &&
    "con" in right.app.func
  ) {
    if (left.app.func.con !== right.app.func.con) return false;
    return typesEqualSpine(left, right); // Pairwise
  }

  if ("never" in left && "never" in right) return true;

  if (
    "arrow" in left &&
    "arrow" in right &&
    typesEqual(left.arrow.from, right.arrow.from) &&
    typesEqual(left.arrow.to, right.arrow.to)
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
    return typesEqual(left.forall.body, renamedBody);
  }

  if ("lam" in left && "lam" in right) {
    const r = right as { lam: { var: string; kind: Kind; body: Type } };
    if (!kindsEqual(left.lam.kind, r.lam.kind)) return false;

    // Alpha‑equivalence: rename RHS variable
    const renamedBody = alphaRename(r.lam.var, left.lam.var, r.lam.body);
    return typesEqual(left.lam.body, renamedBody);
  }

  if ("app" in left && "app" in right) {
    const r = right as { app: { func: Type; arg: Type } };
    return (
      typesEqual(left.app.func, r.app.func) &&
      typesEqual(left.app.arg, r.app.arg)
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

      if (!typesEqual(lc.type, renamedConstraintType)) return false;
    }
    const renamedBody = alphaRename(
      right.bounded_forall.var,
      left.bounded_forall.var,
      right.bounded_forall.body,
    );
    return typesEqual(left.bounded_forall.body, renamedBody);
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
        leftCases.find((t) => t[0] === label)![1],
        rightCases.find((t) => t[0] === label)![1],
      ),
    );
  }

  if ("mu" in left && "mu" in right) {
    // μα.τ₁ = μβ.τ₂ if τ₁ = τ₂[β/α]
    const renamedBody = alphaRename(right.mu.var, left.mu.var, right.mu.body);
    return typesEqual(left.mu.body, renamedBody);
  }

  if ("tuple" in left && "tuple" in right) {
    if (left.tuple.length !== right.tuple.length) return false;

    return left.tuple.every((leftElem, i) =>
      typesEqual(leftElem, right.tuple[i]!),
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
  left: Type,
  right: Type,
  worklist: Worklist,
  subst: Substitution,
  context: Context = [],
): Result<TypingError, null> {
  left = normalizeType(left, context);
  right = normalizeType(right, context);

  if (typesEqual(left, right)) {
    return ok(null);
  }

  if (
    "mu" in left &&
    "var" in left.mu.body &&
    left.mu.body.var === left.mu.var
  ) {
    return err({ cyclic: left.mu.var });
  }
  if (
    "mu" in right &&
    "var" in right.mu.body &&
    right.mu.body.var === right.mu.var
  )
    return err({ cyclic: right.mu.var });

  if (isBottom(left) && isBottom(normalizeType(right))) return ok(null);

  if (isBottom(left)) {
    // ⊥ <: right? Check right :: *
    const rightKind = checkKind([], right, true); // Empty ctx for base kind check
    if ("err" in rightKind || !isStarKind(rightKind.ok))
      return err({ type_mismatch: { expected: right, actual: left } });

    return ok(null);
  }

  if (isBottom(right))
    // Unification is asymmetric: left ~ ⊥ only if left is also ⊥
    // (since non-bottom types are not subtypes of bottom)
    return isBottom(left)
      ? ok(null)
      : err({ type_mismatch: { expected: right, actual: left } });

  const leftRigid = "var" in left && !isMetaVar(left);
  const rightRigid = "var" in right && !isMetaVar(right);

  if (leftRigid && rightRigid)
    return typesEqual(left, right)
      ? ok(null)
      : err({ type_mismatch: { expected: left, actual: right } });

  if (leftRigid) {
    // Check for cycles with rigid variables
    if ("var" in left && occursCheck(left.var, right))
      return err({ cyclic: left.var });

    if ("var" in right && isMetaVar(right))
      return unifyVariable(right.var, left, subst);

    return err({ type_mismatch: { expected: left, actual: right } });
  }

  if (rightRigid) return unifyTypes(right, left, worklist, subst);

  // Variable cases
  if ("var" in left) return unifyVariable(left.var, right, subst);

  if ("var" in right) return unifyVariable(right.var, left, subst);

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
    const enumBinding = context.find(
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
      ) {
        return err({ type_mismatch: { expected: left, actual: right } });
      }

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
    return unifyTypes(right, left, worklist, subst, context); // Swap
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
  if ("arrow" in left && "arrow" in right && isBottom(left.arrow.from)) {
    // Bottom domain matches anything, so only unify codomains
    worklist.push(typeEq(left.arrow.to, right.arrow.to));

    // Note: We might want to collect τ₁ as a constraint for α if needed,
    // but for now just succeed since ⊥ is a valid subtype
    return ok(null);
  }

  // Symmetric case: functions with bottom domain on right
  if ("arrow" in left && "arrow" in right && isBottom(right.arrow.from)) {
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

export function unifyVariable(
  varName: string,
  type: Type,
  subst: Substitution,
): Result<TypingError, null> {
  if (subst.has(varName)) {
    const existing = subst.get(varName)!;
    return typesEqual(existing, type)
      ? ok(null)
      : err({ type_mismatch: { expected: existing, actual: type } });
  }

  // var ~ var (tautology)
  if ("var" in type && type.var === varName) return ok(null);

  if (isBottom(type)) {
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
  subst: Substitution,
  type: Type,
  visited = new Set<string>(),
): Type {
  if ("var" in type) {
    // Cycle detection, return the variable unchanged
    if (visited.has(type.var)) return type;

    const replacement = subst.get(type.var);
    if (!replacement) return type;

    // Add to visited set and recursively substitute
    const newVisited = new Set(visited);
    newVisited.add(type.var);
    return applySubstitution(subst, replacement, newVisited);
  }

  if ("con" in type) return type;

  if ("arrow" in type)
    return arrowType(
      applySubstitution(subst, type.arrow.from),
      applySubstitution(subst, type.arrow.to),
    );

  if ("forall" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.forall.var);
    return forallType(
      type.forall.var,
      type.forall.kind,
      applySubstitution(newSubst, type.forall.body),
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
        type: applySubstitution(subst, c.type),
      })),
      applySubstitution(newSubst, type.bounded_forall.body),
    );
  }

  if ("lam" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.lam.var);
    return {
      lam: {
        var: type.lam.var,
        kind: type.lam.kind,
        body: applySubstitution(newSubst, type.lam.body),
      },
    };
  }

  if ("app" in type) {
    return appType(
      applySubstitution(subst, type.app.func),
      applySubstitution(subst, type.app.arg),
    );
  }

  if ("record" in type) {
    const record: [string, Type][] = [];
    for (const [label, fieldType] of type.record)
      record.push([label, applySubstitution(subst, fieldType)]);
    return { record };
  }

  if ("variant" in type) {
    const variant: [string, Type][] = [];
    for (const [label, caseType] of type.variant)
      variant.push([label, applySubstitution(subst, caseType)]);
    return { variant };
  }

  if ("mu" in type) {
    const newSubst = new Map(subst);
    newSubst.delete(type.mu.var);
    return muType(type.mu.var, applySubstitution(newSubst, type.mu.body));
  }

  if ("tuple" in type)
    return tupleType(type.tuple.map((t) => applySubstitution(subst, t)));

  return type;
}

// Bidirectional type checking - check a term against an expected type
export function checkType(
  context: Context,
  term: Term,
  expectedType: Type,
): Result<TypingError, { type: Type; subst: Substitution }> {
  // Check kind of expected type
  const kindResult = checkKind(context, expectedType);
  if ("err" in kindResult) return kindResult;

  // Lambda: check against arrow type
  if ("lam" in term && "arrow" in expectedType) {
    // Unify the lambda's declared parameter type with the expected domain
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const domainUnify = unifyTypes(
      term.lam.type,
      expectedType.arrow.from,
      worklist,
      subst,
    );
    if ("err" in domainUnify) return domainUnify;

    const solveRes = solveConstraints(worklist, subst);
    if ("err" in solveRes) return solveRes;

    // Populate global meta variable solutions
    for (const [varName, soln] of solveRes.ok.entries()) {
      if (metaKind.has(varName)) {
        const globalSolve = solveMetaVar(varName, soln);
        if ("err" in globalSolve) return globalSolve;
      }
    }

    // Apply substitution to get the resolved domain type
    let effectiveFromType = applySubstitution(
      solveRes.ok,
      expectedType.arrow.from,
    );

    if (isBottom(expectedType.arrow.from)) effectiveFromType = freshMetaVar();

    const extendedContext: Context = [
      ...context,
      { term: { name: term.lam.arg, type: effectiveFromType } },
    ];

    const bodyCheckRes = checkType(
      extendedContext,
      term.lam.body,
      applySubstitution(solveRes.ok, expectedType.arrow.to),
    );
    if ("err" in bodyCheckRes) return bodyCheckRes;

    const mergedSubst = mergeSubsts(solveRes.ok, bodyCheckRes.ok.subst);

    let finalType: Type = applySubstitution(mergedSubst, expectedType);
    if (isBottom(expectedType.arrow.from))
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
      ...context,
      { type: { name: term.tylam.var, kind: term.tylam.kind } },
    ];

    // Alpha-rename expected type if necessary
    const renamedExpected = alphaRename(
      expectedType.forall.var,
      term.tylam.var,
      expectedType.forall.body,
    );

    const bodyResult = checkType(
      extendedContext,
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

      if (!typesEqual(termConstraint.type, renamedConstraintType))
        return err({
          type_mismatch: {
            expected: renamedConstraintType,
            actual: termConstraint.type,
          },
        });
    }

    const extendedContext: Context = [
      ...context,
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
      extendedContext,
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

      const fieldResult = checkType(context, fieldTerm, expectedFieldType);
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
        context,
        term.tuple[i]!,
        expectedType.tuple[i]!,
      );
      if ("err" in elementResult) return elementResult;
    }

    return ok({ type: expectedType, subst: new Map() });
  }

  // Injection: check value against variant case type
  if ("inject" in term) {
    const variantType = normalizeType(expectedType);

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

    const valueResult = checkType(context, term.inject.value, caseType[1]);
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

    const termResult = checkType(context, term.fold.term, unfoldedType);
    if ("err" in termResult) return termResult;

    return ok({ type: expectedType, subst: new Map() });
  }

  // Subsumption: infer and check if compatible
  const inferredType = inferType(context, term);
  if ("err" in inferredType) return inferredType;

  let polyInferred = inferredType.ok;
  if ("forall" in polyInferred && !("forall" in expectedType)) {
    // Instantiate poly to match expected
    polyInferred = instantiate(polyInferred);
    // Unify with expected (solves metas)
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(polyInferred, expectedType, worklist, subst);
    if ("err" in unifyRes) {
      // Original subsumption as fallback
      const subsumesRes = subsumes(
        context,
        inferredType.ok,
        expectedType,
        [],
        new Map(),
      );
      if ("err" in subsumesRes) return subsumesRes;
    } else {
      const solveRes = solveConstraints(worklist, subst);
      if ("err" in solveRes) return solveRes;
      polyInferred = applySubstitution(solveRes.ok, polyInferred);
    }
  }

  // Proceed with subsumption
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const subsumesResult = subsumes(
    context,
    expectedType,
    polyInferred,
    worklist,
    subst,
  );
  if ("err" in subsumesResult) return subsumesResult;

  const solveResult = solveConstraints(worklist, subst);
  if ("err" in solveResult) return solveResult;

  const finalSubst = solveResult.ok;
  for (const [varName, soln] of finalSubst.entries()) {
    if (metaKind.has(varName)) {
      const globalSolve = solveMetaVar(varName, soln);
      if ("err" in globalSolve) return globalSolve;
    }
  }

  const resolvedExpected = applySubstitution(finalSubst, expectedType);

  let finalInferred = polyInferred;
  if (!isAssignableTo(polyInferred, resolvedExpected)) {
    finalInferred = applySubstitution(finalSubst, polyInferred);
    return err({
      type_mismatch: { expected: resolvedExpected, actual: finalInferred },
    });
  }

  return ok({ type: resolvedExpected, subst: finalSubst });
}

// ./src/typechecker.ts (cont.)
// Typing judgment: Γ ⊢ e : τ
export function inferType(ctx: Context, term: Term): Result<TypingError, Type> {
  if ("var" in term) return inferVarType(ctx, term);
  if ("con" in term) return ok(term.con.type);
  if ("lam" in term) return inferLamType(ctx, term);
  if ("app" in term) return inferAppType(ctx, term);
  if ("let" in term) return inferLetType(ctx, term);
  if ("tylam" in term) return inferTylamType(ctx, term);
  if ("tyapp" in term) return inferTyappType(ctx, term);
  if ("dict" in term) return inferDictType(ctx, term);
  if ("trait_lam" in term) return inferTraitLamType(ctx, term);
  if ("trait_app" in term) return inferTraitAppType(ctx, term);
  if ("trait_method" in term) return inferTraitMethodType(ctx, term);
  if ("record" in term) return inferRecordType(ctx, term);
  if ("project" in term) return inferProjectType(ctx, term);
  if ("inject" in term) return inferInjectType(ctx, term);
  if ("match" in term) return inferMatchType(ctx, term);
  if ("fold" in term) return inferFoldType(ctx, term);
  if ("unfold" in term) return inferUnfoldType(ctx, term);
  if ("tuple" in term) return inferTupleType(ctx, term);
  if ("tuple_project" in term) return inferTupleProjectType(ctx, term);

  throw new Error(`Unknown term: ${Object.keys(term)[0]}`);
}

function inferTupleProjectType(ctx: Context, term: TupleProjectTerm) {
  const tupleType = inferType(ctx, term.tuple_project.tuple);
  if ("err" in tupleType) return tupleType;

  if (!("tuple" in tupleType.ok)) return err({ not_a_tuple: tupleType.ok });

  const index = term.tuple_project.index;
  if (index < 0 || index >= tupleType.ok.tuple.length) {
    return err({
      tuple_index_out_of_bounds: {
        tuple: tupleType.ok,
        index,
      },
    });
  }

  return ok(tupleType.ok.tuple[index]!);
}

function inferTupleType(ctx: Context, term: TupleTerm) {
  const elementTypes: Type[] = [];

  for (const element of term.tuple) {
    const elementType = inferType(ctx, element);
    if ("err" in elementType) return elementType;

    elementTypes.push(elementType.ok);
  }

  return ok(tupleType(elementTypes));
}

function inferUnfoldType(ctx: Context, term: UnfoldTerm) {
  const termType = inferType(ctx, term.unfold);
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

function inferFoldType(ctx: Context, term: FoldTerm) {
  const muKind = checkKind(ctx, term.fold.type);
  if ("err" in muKind) return muKind;

  if (!("mu" in term.fold.type))
    return err({
      type_mismatch: { expected: term.fold.type, actual: term.fold.type },
    });

  const unfoldedType = substituteType(
    term.fold.type.mu.var,
    term.fold.type,
    term.fold.type.mu.body,
    new Set([term.fold.type.mu.var]),
  );

  const termType = inferType(ctx, term.fold.term);
  if ("err" in termType) return termType;

  if (!isAssignableTo(termType.ok, unfoldedType))
    return err({
      type_mismatch: {
        expected: unfoldedType,
        actual: termType.ok,
      },
    });

  return ok(term.fold.type);
}

function inferMatchType(ctx: Context, term: MatchTerm) {
  const scrutineeType = inferType(ctx, term.match.scrutinee);
  if ("err" in scrutineeType) return scrutineeType;
  let normalizedScrutinee = normalizeType(scrutineeType.ok);
  if ("mu" in normalizedScrutinee) {
    // Automatically unfold folded values when pattern matching
    normalizedScrutinee = substituteType(
      normalizedScrutinee.mu.var,
      normalizedScrutinee,
      normalizedScrutinee.mu.body,
    );
  }

  const patterns = term.match.cases.map((c) => c[0]);
  const exhaustCheck = checkExhaustive(patterns, normalizedScrutinee, ctx);
  if ("err" in exhaustCheck) return exhaustCheck;

  let commonType: Type | null = null;

  for (const [pat, bod] of term.match.cases) {
    const patternResult = checkPattern(pat, normalizedScrutinee, ctx); // Now handles nominal
    if ("err" in patternResult) return patternResult;

    const extendedCtx = [...ctx, ...patternResult.ok];

    const bodyType = inferType(extendedCtx, bod);
    if ("err" in bodyType) return bodyType;

    let instBodyType = instantiate(bodyType.ok);
    instBodyType = normalizeType(instBodyType);

    if (commonType === null) {
      commonType = instBodyType;
    } else {
      // Use subsumes (subtype check) instead of unifyTypes to allow ⊥ <: commonType
      // This handles unreachable arms: ⊥ from unreachable() <: t_ok]
      const worklist: Worklist = [];
      const subst = new Map<string, Type>();

      // First, try subsuming new arm into the common (instBodyType <: commonType)
      // If that fails, try reverse (commonType <: instBodyType) for bidirectional subtyping
      let subsumesRes = subsumes(
        extendedCtx, // Use extended context for better binding resolution
        instBodyType, // New arm type
        commonType, // Existing common type
        worklist,
        subst,
      );

      if ("err" in subsumesRes) {
        // Fallback: Try commonType <: instBodyType (e.g., if common is ⊥ and new is t_ok)
        subst.clear(); // Clear previous subst
        worklist.length = 0; // Clear worklist
        subsumesRes = subsumes(
          extendedCtx,
          commonType, // Existing
          instBodyType, // New
          worklist,
          subst,
        );
      }

      if ("err" in subsumesRes) {
        // If neither direction works, fall back to unification (strict equality) and error
        const unifyRes = unifyTypes(commonType, instBodyType, worklist, subst);
        if ("err" in unifyRes) return unifyRes;
      }

      const solveRes = solveConstraints(worklist, subst);
      if ("err" in solveRes) return solveRes;

      // Update common to the least upper bound (LUB) or just apply subst to common
      // For simplicity, apply to commonType; in full system, compute LUB if needed
      commonType = applySubstitution(solveRes.ok, commonType!);
    }
  }

  // Ensure overall match is monotype (no generalization here)
  return ok(normalizeType(commonType!));
}

function inferInjectType(
  ctx: Context,
  term: InjectTerm,
): Result<TypingError, Type> {
  const variantType = normalizeType(term.inject.variant_type); // e.g., app({con: "Option"}, {var: "t"})

  // Case 1: Nominal enum (app with con head, e.g., Option<t>, Either<l, r>)
  if ("app" in variantType || "con" in variantType) {
    const head = "con" in variantType ? variantType : getSpineHead(variantType);
    if ("con" in head) {
      const conName = head.con;
      const spineArgs = "con" in variantType ? [] : getSpineArgs(variantType);
      // Lookup enum definition in context
      const enumBinding = ctx.find(
        (b) => "enum" in b && b.enum.name === conName,
      );
      if (!enumBinding || !("enum" in enumBinding))
        return err({ not_a_variant: variantType });
      const def = enumBinding.enum; // {name: "Option", params: ["t"], variants: [["Some", {var: "t"}]]}

      // Check arity: Spine args must match param count
      if (spineArgs.length !== def.params.length)
        return err({
          kind_mismatch: { expected: def.kind, actual: starKind },
        });

      const label = term.inject.label; // "Some" or "Left"
      const variantEntry = def.variants.find(([l]) => l === label); // Lookup by label
      if (!variantEntry)
        return err({
          invalid_variant_label: { variant: variantType, label },
        });

      // Instantiate the field scheme with spine args
      // Field scheme is unbound (e.g., {var: "t"} or {tuple: [{var: "t1"}, {var: "t2"}]} for multi-field)
      let expectedFieldType: Type = variantEntry[1]; // Unbound scheme
      for (let i = 0; i < def.params.length; i++) {
        const paramName = def.params[i]!; // "t" or "l"/"r"
        const concreteArg = spineArgs[i]!; // {var: "t"} or {var: "l"}
        expectedFieldType = substituteType(
          paramName,
          concreteArg,
          expectedFieldType,
        );
      }
      expectedFieldType = normalizeType(expectedFieldType); // Beta-reduce if needed

      // Check the injected value against the field type
      // Handles single value, unit (zero fields), or tuple (multi-fields)
      const valueCheck = checkInjectValue(
        term.inject.value,
        expectedFieldType,
        ctx,
      );

      return "err" in valueCheck ? valueCheck : ok(variantType);
    }
  }

  // Case 2: Structural variant (legacy/fallback, e.g., {variant: [["Some", {var: "t"}]]})
  if ("variant" in variantType) {
    const caseEntry = variantType.variant.find(
      ([l]) => l === term.inject.label,
    );
    if (!caseEntry)
      return err({
        invalid_variant_label: {
          variant: variantType,
          label: term.inject.label,
        },
      });

    const expectedFieldType = caseEntry[1]; // e.g., {var: "t"}
    const valueCheck = checkInjectValue(
      term.inject.value,
      expectedFieldType,
      ctx,
    );

    return "err" in valueCheck ? valueCheck : ok(variantType);
  }

  // Neither nominal nor structural: Fail
  return err({ not_a_variant: variantType });
}

// NEW Helper: Check injected value against field type (handles unit, single, tuple/multi-field)
function checkInjectValue(
  value: Term,
  expectedFieldType: Type,
  ctx: Context,
): Result<TypingError, { valueType: Type }> {
  if (isBottom(expectedFieldType)) {
    // Bottom field: Always OK (unreachable variant)
    return ok({ valueType: neverType });
  }

  // Case: Zero fields (unit variant, e.g., None)
  if ("tuple" in expectedFieldType && expectedFieldType.tuple.length === 0) {
    // Value should be unit {} or wildcard-ish
    if (!("tuple" in value) || value.tuple.length !== 0) {
      const inferred = inferType(ctx, value);
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
    const valueType = inferType(ctx, value);
    if ("err" in valueType) return valueType;

    const checkRes = checkType(ctx, value, expectedFieldType);
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
        actual: { tuple: value.tuple.map(() => freshMetaVar()) },
      },
    });
  }

  const valueType: Type = { tuple: [] };
  for (let i = 0; i < value.tuple.length; i++) {
    const valueElem = value.tuple[i]!;
    const expectedElemType = expectedFieldType.tuple[i]!;

    const elemType = inferType(ctx, valueElem);
    if ("err" in elemType) return elemType;

    const checkRes = checkType(ctx, valueElem, expectedElemType);
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

function inferProjectType(ctx: Context, term: ProjectTerm) {
  const recordType = inferType(ctx, term.project.record);
  if ("err" in recordType) return recordType;

  if (!("record" in recordType.ok)) return err({ not_a_record: recordType.ok });

  const fieldType = recordType.ok.record.find(
    (t) => t[0] === term.project.label,
  );
  if (!fieldType) {
    return err({
      missing_field: {
        record: recordType.ok,
        label: term.project.label,
      },
    });
  }

  return ok(fieldType[1]);
}

function inferRecordType(ctx: Context, term: RecordTerm) {
  const record: [string, Type][] = [];

  for (const [label, fieldTerm] of term.record) {
    const fieldType = inferType(ctx, fieldTerm);
    if ("err" in fieldType) return fieldType;

    record.push([label, fieldType.ok]);
  }

  return ok({ record });
}

function inferTraitMethodType(ctx: Context, term: TraitMethodTerm) {
  const dictType = inferType(ctx, term.trait_method.dict);
  if ("err" in dictType) return dictType;

  // Check if the dictionary is a variable bound in context
  const dictTerm = term.trait_method.dict;

  if ("var" in dictTerm) {
    // dictTerm is a VarTerm
    const dictBinding = ctx.find(
      (b) => "dict" in b && b.dict.name === dictTerm.var,
    );

    if (dictBinding && "dict" in dictBinding) {
      // Look up the trait definition
      const traitDef = ctx.find(
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
    const traitDef = ctx.find(
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
    return inferType(ctx, methodImpl[1]);
  }
  return err({
    type_mismatch: {
      expected: { con: "Dictionary" },
      actual: dictType.ok,
    },
  });
}

function inferTraitAppType(ctx: Context, term: TraitAppTerm) {
  const termType = inferType(ctx, term.trait_app.term);
  if ("err" in termType) return termType;

  if (!("bounded_forall" in termType.ok))
    return err({
      type_mismatch: {
        expected: termType.ok,
        actual: term.trait_app.type,
      },
    });

  // Check that the type argument has the expected kind
  const argKind = checkKind(ctx, term.trait_app.type);
  if ("err" in argKind) return argKind;
  const bounded_forall = termType.ok.bounded_forall;
  if (!kindsEqual(bounded_forall.kind, argKind.ok))
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
      type: substituteType(bounded_forall.var, term.trait_app.type, c.type),
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
  const dictsResult = checkTraitConstraints(ctx, instantiatedConstraints);
  if ("err" in dictsResult) return dictsResult;

  // Type check each provided dictionary
  for (let i = 0; i < term.trait_app.dicts.length; i++) {
    const providedDict = term.trait_app.dicts[i]!;
    const dictType = inferType(ctx, providedDict);
    if ("err" in dictType) return dictType;

    // Verify it's actually a dictionary for the right trait/type
    if ("dict" in providedDict) {
      const constraint = instantiatedConstraints[i]!;
      if (
        providedDict.dict.trait !== constraint.trait ||
        !typesEqual(providedDict.dict.type, constraint.type)
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

function inferTraitLamType(ctx: Context, term: TraitLamTerm) {
  // Add type variable to context
  const extendedContext: Context = [
    ...ctx,
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
  const traitDef = ctx.find(
    (b) => "trait_def" in b && b.trait_def.name === term.trait_lam.trait,
  );

  if (!traitDef || !("trait_def" in traitDef))
    return err({ unbound: term.trait_lam.trait });

  const bodyType = inferType(extendedContext, term.trait_lam.body);
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

function inferDictType(ctx: Context, term: DictTerm) {
  const traitDef = ctx.find(
    (b) => "trait_def" in b && b.trait_def.name === term.dict.trait,
  );

  if (!traitDef || !("trait_def" in traitDef))
    return err({ unbound: term.dict.trait });

  const dictType = term.dict.type;
  const typeKindResult = checkKind(ctx, dictType); // Full kind for basic well-formedness
  if ("err" in typeKindResult) return typeKindResult;

  // Compute STRIPPED partial kind (e.g., Option<t> → Option : * → *)
  const strippedResult = computeStrippedKind(dictType, [], ctx);
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
  const partialDictType = stripAppsByArity(dictType, strippedArity, ctx);

  const requiredMethods = new Set(traitDef.trait_def.methods.map((m) => m[0]));
  const providedMethods = new Set(term.dict.methods.map((m) => m[0]));

  for (const required of requiredMethods)
    if (!providedMethods.has(required))
      return err({
        missing_method: { trait: term.dict.trait, method: required },
      });

  // Bind 'self' to dictType in a local method context for each impl inference
  const methodCtx = [...ctx, { term: { name: "self", type: dictType } }];

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

    const implType = inferType(methodCtx, methodImpl);
    if ("err" in implType) return implType;

    // Subsumption: allow impl to provide the expected type (handles instantiation)
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(
      normalizeType(expectedMethodType), // Normalize both sides
      normalizeType(implType.ok),
      worklist,
      subst,
    );

    // Always solve the worklist after subsumes
    if ("err" in unifyRes) {
      // Solve any constraints from unification, then error if failed
      const solveRes = solveConstraints(worklist, subst);
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
    const solveRes = solveConstraints(worklist, subst);
    // Propagate if constraints fail (rare here)
    if ("err" in solveRes) return solveRes;

    // Apply subst to verify (optional, for safety)
    const resolvedImpl = applySubstitution(solveRes.ok, implType.ok);
    if (
      !typesEqual(
        normalizeType(resolvedImpl),
        normalizeType(expectedMethodType),
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

function inferTyappType(ctx: Context, term: TyAppTerm) {
  const termType = inferType(ctx, term.tyapp.term);
  if ("err" in termType) return termType;

  if (!("forall" in termType.ok))
    return err({
      type_mismatch: {
        expected: termType.ok,
        actual: term.tyapp.type,
      },
    });

  const argKind = checkKind(ctx, term.tyapp.type);
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

function inferTylamType(context: Context, term: TyLamTerm) {
  const extendedContext: Context = [
    { type: { name: term.tylam.var, kind: term.tylam.kind } },
    ...context,
  ];

  const bodyType = inferType(extendedContext, term.tylam.body);
  if ("err" in bodyType) return bodyType;

  return ok(forallType(term.tylam.var, term.tylam.kind, bodyType.ok));
}

function inferLetType(context: Context, term: LetTerm) {
  const valueType = inferType(context, term.let.value);
  if ("err" in valueType) return valueType;

  const extendedContext: Context = [
    { term: { name: term.let.name, type: valueType.ok } },
    ...context,
  ];

  return inferType(extendedContext, term.let.body);
}

function inferAppType(context: Context, term: AppTerm) {
  const calleeInferred = inferType(context, term.app.callee);
  if ("err" in calleeInferred) return calleeInferred;

  const argInferred = inferType(context, term.app.arg);
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
    const fv = freshMetaVar();
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
      const fv = freshMetaVar();
      body = substituteType(body.forall.var, fv, body.forall.body);
    }

    if (!("arrow" in body)) return err({ not_a_function: instantiatedCallee });

    const expectedParamType = body.arrow.from;

    // Try to infer Self from the argument
    const selfType = inferSelfFromArgument(
      argInferred.ok,
      expectedParamType,
      instantiatedCallee.bounded_forall.var,
      instantiatedCallee.bounded_forall.kind,
      context,
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
    const dictsResult = checkTraitConstraints(context, constraints);
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
        freshMetaVar(),
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
  const argCheckRes = checkType(context, term.app.arg, paramType);
  if ("err" in argCheckRes) {
    const worklist: Worklist = [];
    const subst = new Map<string, Type>();
    const unifyRes = unifyTypes(argInferred.ok, paramType, worklist, subst);
    if ("err" in unifyRes) return argCheckRes;

    const solveRes = solveConstraints(worklist, subst);
    if ("err" in solveRes) return solveRes;

    const resolvedResultType = applySubstitution(solveRes.ok, resultTypeBase);
    return ok(resolvedResultType);
  }

  const { subst: localSubst } = argCheckRes.ok;
  const mergedSubst = mergeSubsts(localSubst, getMetaSubstitution());
  let resultType = applySubstitution(mergedSubst, resultTypeBase);
  resultType = normalizeType(resultType);

  return ok(resultType);
}

function inferSelfFromArgument(
  argType: Type,
  expectedType: Type,
  selfVar: string,
  selfKind: Kind,
  ctx: Context,
): Result<TypingError, Type> {
  const normArg = normalizeType(argType);
  const normExpected = normalizeType(expectedType);

  // If expected is (Self t), extract constructor from arg
  if ("app" in normExpected && "var" in normExpected.app.func) {
    if (normExpected.app.func.var === selfVar) {
      // For variants like <Left: I32 | Right: ?14>,
      // reconstruct as Either<I32> by finding the enum def
      if ("variant" in normArg) {
        // Try to find which enum this variant belongs to
        const etype = findEnumForVariant(normArg, ctx);
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
function findEnumForVariant(variantType: Type, ctx: Context): Type | null {
  if (!("variant" in variantType)) return null;

  // Get the variant labels
  const labels = new Set(variantType.variant.map(([label]) => label));

  // Search context for an enum type that has exactly these variants
  for (const binding of ctx) {
    if ("type" in binding) {
      const typeEntry = ctx.find(
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

function inferLamType(ctx: Context, term: LamTerm) {
  const argKind = checkKind(ctx, term.lam.type);
  if ("err" in argKind) return argKind;

  if (!isStarKind(argKind.ok))
    return err({ kind_mismatch: { expected: starKind, actual: argKind.ok } });

  const extendedContext: Context = [
    { term: { name: term.lam.arg, type: term.lam.type } },
    ...ctx,
  ];

  const bodyType = inferType(extendedContext, term.lam.body);
  if ("err" in bodyType) return bodyType;

  return ok(arrowType(term.lam.type, bodyType.ok));
}

function inferVarType(ctx: Context, term: VarTerm) {
  // Check for term binding
  const termBinding = ctx.find((b) => "term" in b && b.term.name === term.var);
  if (termBinding && "term" in termBinding) return ok(termBinding.term.type);

  // Check for dict binding
  const dictBinding = ctx.find((b) => "dict" in b && b.dict.name === term.var);
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
export function getUnboundMetas(ty: Type, metas = new Set<string>()): string[] {
  if ("var" in ty && ty.var.startsWith("?")) {
    if (!metaVarSolutions.has(parseInt(ty.var.slice(1), 10))) metas.add(ty.var);
  } else if ("app" in ty) {
    getUnboundMetas(ty.app.func, metas);
    getUnboundMetas(ty.app.arg, metas);
  } else if ("arrow" in ty) {
    getUnboundMetas(ty.arrow.from, metas);
    getUnboundMetas(ty.arrow.to, metas);
  } else if ("tuple" in ty) for (const t of ty.tuple) getUnboundMetas(t, metas);
  else if ("record" in ty)
    for (const [, t] of ty.record) getUnboundMetas(t, metas);
  else if ("variant" in ty)
    for (const [, t] of ty.variant) getUnboundMetas(t, metas);

  return Array.from(metas);
}

// Worklist constraint solver
export function solveConstraints(
  worklist: Worklist,
  subst: Substitution = new Map(),
): Result<TypingError, Substitution> {
  while (worklist.length > 0) {
    const result = processConstraint(worklist.shift()!, worklist, subst);
    if ("err" in result) return result;
  }

  return ok(subst);
}

export function processConstraint(
  constraint: Constraint,
  worklist: Worklist,
  subst: Substitution,
): Result<TypingError, null> {
  if ("type_eq" in constraint) {
    return unifyTypes(
      normalizeType(applySubstitution(subst, constraint.type_eq.left)),
      normalizeType(applySubstitution(subst, constraint.type_eq.right)),
      worklist,
      subst,
    );
  }

  if ("kind_eq" in constraint)
    return unifyKinds(constraint.kind_eq.left, constraint.kind_eq.right);

  if ("has_kind" in constraint) {
    const type = applySubstitution(subst, constraint.has_kind.ty);
    const kindResult = checkKind(constraint.has_kind.context, type);

    if ("err" in kindResult) return kindResult;

    worklist.push(kindEq(kindResult.ok, constraint.has_kind.kind));

    return ok(null);
  }

  if ("has_type" in constraint) {
    const typeResult = inferType(
      constraint.has_type.context,
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
  ctx: Context,
  term: Term,
): Result<TypingError, Type> {
  const worklist: Worklist = [hasType(term, { var: "$result" }, ctx)];

  const subst = new Map<string, Type>();
  const result = solveConstraints(worklist, subst);

  if ("err" in result) return result;

  const resultType = subst.get("$result");
  if (!resultType) return inferType(ctx, term);

  return ok(resultType);
}

// Update the normalizeType function
export function normalizeType(
  ty: Type,
  context: Context = [],
  seen = new Set<string>(),
): Type {
  // Simple cycle detection (use var names or JSON.stringify for safety)
  if ("var" in ty && seen.has(ty.var)) return ty;
  const newSeen = "var" in ty ? new Set(seen).add(ty.var) : seen;

  if ("var" in ty || "con" in ty || "never" in ty) return ty;

  if ("app" in ty) {
    const head = getSpineHead(ty);
    if ("con" in head) {
      const enumName = head.con;
      const enumBinding = context.find(
        (b) => "enum" in b && b.enum.name === enumName,
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
              normalizeType(instField, context, seen),
            ]);
          }
          return { variant: structuralVariant };
        }
      }
    }
  }

  // For app - normalize func FIRST, then check for lam reduction
  if ("app" in ty) {
    const normFunc = normalizeType(ty.app.func, context, newSeen);
    if ("lam" in normFunc) {
      // Beta-reduce: [arg / var] body
      const substituted = substituteType(
        normFunc.lam.var,
        ty.app.arg,
        normFunc.lam.body,
      );
      return normalizeType(substituted, context, newSeen); // Recurse to fold further
    }
    // No beta: form normalized app
    const normArg = normalizeType(ty.app.arg, context, newSeen);
    return { app: { func: normFunc, arg: normArg } };
  }

  // Recurse on compounds
  if ("arrow" in ty)
    return arrowType(
      normalizeType(ty.arrow.from, context, newSeen),
      normalizeType(ty.arrow.to, context, newSeen),
    );

  if ("forall" in ty)
    return forallType(
      ty.forall.var,
      ty.forall.kind,
      normalizeType(ty.forall.body, context, newSeen),
    );

  if ("bounded_forall" in ty)
    return boundedForallType(
      ty.bounded_forall.var,
      ty.bounded_forall.kind,
      ty.bounded_forall.constraints.map((c) => ({
        trait: c.trait,
        type: normalizeType(c.type, context, newSeen),
      })),
      normalizeType(ty.bounded_forall.body, context, newSeen),
    );

  if ("lam" in ty)
    return lamType(
      ty.lam.var,
      ty.lam.kind,
      normalizeType(ty.lam.body, context, newSeen),
    );

  if ("record" in ty)
    return recordType(
      ty.record.map(([l, f]) => [l, normalizeType(f, context, newSeen)]),
    );

  if ("variant" in ty)
    return variantType(
      ty.variant.map(([l, c]) => [l, normalizeType(c, context, newSeen)]),
    );

  if ("mu" in ty) {
    if (newSeen.has(ty.mu.var)) return ty;
    const muSeen = new Set(newSeen).add(ty.mu.var);
    return muType(ty.mu.var, normalizeType(ty.mu.body, context, muSeen));
  }

  if ("tuple" in ty)
    return tupleType(ty.tuple.map((t) => normalizeType(t, context, newSeen)));

  return ty; // Fallback
}
export function instantiateWithTraits(
  ctx: Context,
  ty: Type,
): Result<TypingError, { type: Type; dicts: Term[] }> {
  // Only bother for bounded forall
  if (!("bounded_forall" in ty)) return ok({ type: ty, dicts: [] });

  const bound = ty.bounded_forall;

  // Instantiate the type variable with a fresh meta variable
  const fresh = freshMetaVar();

  // Substitute fresh into constraints BEFORE checking
  const instantiatedConstraints = bound.constraints.map((c) => ({
    trait: c.trait,
    type: substituteType(bound.var, fresh, c.type),
  }));

  // Now check constraints with the instantiated type
  const dictsResult = checkTraitConstraints(ctx, instantiatedConstraints);
  if ("err" in dictsResult) return dictsResult;

  // Substitute fresh into body
  const body = substituteType(bound.var, fresh, bound.body);

  // Return the substituted type plus the dict terms we found
  return ok({ type: body, dicts: dictsResult.ok });
}

// When you encounter a polymorphic value in application position:
export function autoInstantiate(
  ctx: Context,
  term: Term,
): Result<TypingError, { term: Term; type: Type }> {
  const termType = inferType(ctx, term);
  if ("err" in termType) return termType;

  let accTerm = term;
  let accType = termType.ok;

  // Auto-apply type arguments
  while ("forall" in accType) {
    const fv = freshMetaVar();
    accTerm = tyapp_term(accTerm, fv);
    accType = substituteType(accType.forall.var, fv, accType.forall.body);
  }

  // Auto-apply trait dictionaries
  while ("bounded_forall" in accType) {
    const instantiateRes = instantiateWithTraits(ctx, accType);
    if ("err" in instantiateRes) return instantiateRes;

    accTerm = traitAppTerm(accTerm, freshMetaVar(), instantiateRes.ok.dicts);
    accType = instantiateRes.ok.type;
  }

  return ok({ term: accTerm, type: accType });
}

export function resolveMetaVars(ty: Type): Type {
  if ("var" in ty && isMetaVar(ty)) {
    const solution = metaVarSolutions.get(parseInt(ty.var.slice(1), 10));
    return solution ? resolveMetaVars(solution) : ty;
  }

  if ("arrow" in ty)
    return arrowType(
      resolveMetaVars(ty.arrow.from),
      resolveMetaVars(ty.arrow.to),
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
export function hasUnboundMetas(type: Type): boolean {
  if (
    "var" in type &&
    isMetaVar(type) &&
    !metaVarSolutions.has(parseInt(type.var.slice(1), 10))
  ) {
    return true;
  }
  // Recurse on subterms...
  if ("app" in type)
    return hasUnboundMetas(type.app.func) || hasUnboundMetas(type.app.arg);
  if ("arrow" in type)
    return hasUnboundMetas(type.arrow.from) || hasUnboundMetas(type.arrow.to);
  if ("tuple" in type) return type.tuple.some(hasUnboundMetas);
  if ("record" in type)
    return type.record.some(([, ty]) => hasUnboundMetas(ty));
  if ("variant" in type)
    return type.variant.some(([, ty]) => hasUnboundMetas(ty));
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
  type: Type,
  strippableVars: string[], // e.g., ["r", "u"] for impl params
  ctx: Context, // For kind checks
): Result<TypingError, { stripped: number; kind: Kind }> {
  let current = normalizeType(type, ctx); // Start normalized
  let stripped = 0;

  // Peel trailing apps if arg is strippable var
  while ("app" in current) {
    const arg = current.app.arg;
    if ("var" in arg && strippableVars.includes(arg.var)) {
      // Kind check (as before)
      const argKindRes = checkKind(ctx, arg);
      if ("err" in argKindRes) return err(argKindRes.err);

      const funcKindRes = checkKind(ctx, current.app.func);
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
  const finalKindRes = checkKind(ctx, current);
  return "err" in finalKindRes
    ? finalKindRes
    : ok({ stripped, kind: finalKindRes.ok });
}

export function stripAppsByArity(
  type: Type,
  arity: number,
  ctx: Context,
): Type {
  let acc = normalizeType(type, ctx);
  for (let i = 0; i < arity; i++) {
    if ("app" in acc) {
      // Only strip if arg is bound var (as in computeStrippedKind)
      const arg = acc.app.arg;
      if (
        "var" in arg &&
        ctx.some((b) => "type" in b && b.type.name === arg.var)
      ) {
        acc = acc.app.func;
      } else break; // Cannot strip further
    } else break;
  }
  return acc;
}

export const arrow_kind = (from: Kind, to: Kind): Kind => ({
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
export const tyapp_term = (term: Term, type: Type) => ({
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
};
