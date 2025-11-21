import {
  appTerm,
  dictTerm,
  foldTerm,
  inferType,
  injectTerm,
  lamTerm,
  recordTerm,
  tupleTerm,
  unitType,
  varTerm,
} from "./typechecker.js";

import {
  type AppTerm,
  type DictTerm,
  type Environment,
  type EvalConfig,
  type EvalResult,
  err,
  type FoldTerm,
  type InjectTerm,
  type LetTerm,
  type MatchTerm,
  ok,
  type Pattern,
  type ProjectTerm,
  type RecordTerm,
  type Result,
  showType,
  type Term,
  type TraitMethodTerm,
  type TupleProjectTerm,
  type TupleTerm,
  type Type,
  type TypeCheckerState,
  type UnfoldTerm,
  type Value,
  type VarTerm,
} from "./types.js";
export function evaluate(
  term: Term,
  context: TypeCheckerState,
  config: EvalConfig = { strict: true, maxSteps: 1000 },
): EvalResult {
  const env = new Map<string, Value>();
  return evaluateWithEnv(term, env, context, config, 0);
}

function evaluateWithEnv(
  term: Term,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  // Prevent infinite loops
  if (steps > config.maxSteps) {
    return err("Evaluation exceeded maximum steps");
  }

  // Handle different term types
  if ("var" in term) {
    return evaluateVar(term, context, env);
  }

  if ("lam" in term) {
    return ok({ vlam: { param: term.lam.arg, body: term.lam.body, env } });
  }

  if ("app" in term) {
    return evaluateApp(term, env, context, config, steps);
  }

  if ("record" in term) {
    return evaluateRecord(term, env, context, config, steps);
  }

  if ("project" in term) {
    return evaluateProject(term, env, context, config, steps);
  }

  if ("tuple" in term) {
    return evaluateTuple(term, env, context, config, steps);
  }

  if ("tuple_project" in term) {
    return evaluateTupleProject(term, env, context, config, steps);
  }

  if ("inject" in term) {
    return evaluateInject(term, env, context, config, steps);
  }

  if ("match" in term) {
    return evaluateMatch(term, env, context, config, steps);
  }

  if ("fold" in term) {
    return evaluateFold(term, env, context, config, steps);
  }

  if ("unfold" in term) {
    return evaluateUnfold(term, env, context, config, steps);
  }

  if ("let" in term) {
    return evaluateLet(term, env, context, config, steps);
  }

  if ("con" in term) {
    return ok({ vvar: term.con.name });
  }

  if ("dict" in term) {
    return evaluateDict(term, env, context, config, steps);
  }

  if ("trait_method" in term) {
    return evaluateTraitMethod(term, env, context, config, steps);
  }

  // Type-level constructs are erased during evaluation
  if (
    "tylam" in term ||
    "tyapp" in term ||
    "trait_lam" in term ||
    "trait_app" in term
  ) {
    // These don't affect runtime values
    return err("Type-level construct cannot be evaluated to a value");
  }

  return err(`Unknown term type: ${Object.keys(term)[0]}`);
}

function evaluateVar(
  term: VarTerm,
  ctx: TypeCheckerState,
  env: Environment,
): EvalResult {
  const value = env.get(term.var);
  if (!value) return err(`Unbound variable: ${term.var}`);
  // Force lazy thunks automatically during lookup (for call-by-need)
  return "vthunk" in value
    ? evaluateWithEnv(
        value.vthunk.term,
        value.vthunk.env,
        ctx,
        { strict: true, maxSteps: 1000 },
        0,
      )
    : ok(value);
}

function evaluateApp(
  term: AppTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  // Evaluate function
  const funcResult = evaluateWithEnv(
    term.app.callee,
    env,
    context,
    config,
    steps,
  );
  if ("err" in funcResult) return funcResult;

  // Evaluate argument if in strict mode
  let argValue: Value;
  if (config.strict) {
    const argResult = evaluateWithEnv(
      term.app.arg,
      env,
      context,
      config,
      steps + 1,
    );
    if ("err" in argResult) return argResult;
    argValue = argResult.ok;
  } else {
    // In lazy mode, create a thunk
    argValue = { vthunk: { term: term.app.arg, env } };
  }

  // Apply function to argument
  if ("vlam" in funcResult.ok) {
    const newEnv = new Map(funcResult.ok.vlam.env);
    newEnv.set(funcResult.ok.vlam.param, argValue);
    return evaluateWithEnv(
      funcResult.ok.vlam.body,
      newEnv,
      context,
      config,
      steps + 1,
    );
  }

  return err("Cannot apply non-function value");
}

function evaluateRecord(
  term: RecordTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const record: Record<string, Value> = {};

  for (const [label, fieldTerm] of term.record) {
    const fieldResult = evaluateWithEnv(
      fieldTerm,
      env,
      context,
      config,
      steps + 1,
    );
    if ("err" in fieldResult) return fieldResult;
    record[label] = fieldResult.ok;
  }

  return ok({ vrecord: record });
}

function evaluateProject(
  term: ProjectTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const recordResult = evaluateWithEnv(
    term.project.record,
    env,
    context,
    config,
    steps,
  );
  if ("err" in recordResult) return recordResult;

  if ("vrecord" in recordResult.ok) {
    const fieldValue = recordResult.ok.vrecord[term.project.label];
    if (!fieldValue) {
      return err(`Record has no field: ${term.project.label}`);
    }
    return ok(fieldValue);
  }

  return err("Cannot project from non-record value");
}

function evaluateTuple(
  term: TupleTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const values: Value[] = [];

  for (const element of term.tuple) {
    const elemResult = evaluateWithEnv(
      element,
      env,
      context,
      config,
      steps + 1,
    );
    if ("err" in elemResult) return elemResult;
    values.push(elemResult.ok);
  }

  return ok({ vtuple: values });
}

function evaluateTupleProject(
  term: TupleProjectTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const tupleResult = evaluateWithEnv(
    term.tuple_project.tuple,
    env,
    context,
    config,
    steps,
  );
  if ("err" in tupleResult) return tupleResult;

  if ("vtuple" in tupleResult.ok) {
    const index = term.tuple_project.index;
    if (index < 0 || index >= tupleResult.ok.vtuple.length) {
      return err(`Tuple index out of bounds: ${index}`);
    }
    return ok(tupleResult.ok.vtuple[index]!);
  }

  return err("Cannot project from non-tuple value");
}

function evaluateInject(
  term: InjectTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const valueResult = evaluateWithEnv(
    term.inject.value,
    env,
    context,
    config,
    steps,
  );
  if ("err" in valueResult) return valueResult;

  return ok({ vvariant: { label: term.inject.label, value: valueResult.ok } });
}

function evaluateMatch(
  term: MatchTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  // Evaluate the scrutinee
  const scrutineeResult = evaluateWithEnv(
    term.match.scrutinee,
    env,
    context,
    config,
    steps,
  );
  if ("err" in scrutineeResult) return scrutineeResult;

  // Try to match each pattern
  for (const [pattern, body] of term.match.cases) {
    const matchResult = matchPattern(pattern, scrutineeResult.ok, env);
    if ("ok" in matchResult) {
      return evaluateWithEnv(body, matchResult.ok, context, config, steps + 1);
    }
  }

  return err("No matching pattern in match expression");
}

function evaluateFold(
  term: FoldTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const valueResult = evaluateWithEnv(
    term.fold.term,
    env,
    context,
    config,
    steps,
  );
  if ("err" in valueResult) return valueResult;

  return ok({ vfold: { type: term.fold.type, value: valueResult.ok } });
}

function evaluateUnfold(
  term: UnfoldTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const termResult = evaluateWithEnv(term.unfold, env, context, config, steps);
  if ("err" in termResult) return termResult;

  if ("vfold" in termResult.ok) {
    return ok(termResult.ok.vfold.value);
  }

  return err("Cannot unfold non-folded value");
}

function evaluateLet(
  term: LetTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  // Evaluate the bound value
  const valueResult = evaluateWithEnv(
    term.let.value,
    env,
    context,
    config,
    steps,
  );
  if ("err" in valueResult) return valueResult;

  // Extend environment with the new binding
  const newEnv = new Map(env);
  newEnv.set(term.let.name, valueResult.ok);

  // Evaluate the body with the extended environment
  return evaluateWithEnv(term.let.body, newEnv, context, config, steps + 1);
}

function evaluateDict(
  term: DictTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const methods = new Map<string, Value>();

  for (const [name, methodTerm] of term.dict.methods) {
    const methodResult = evaluateWithEnv(
      methodTerm,
      env,
      context,
      config,
      steps + 1,
    );
    if ("err" in methodResult) return methodResult;
    methods.set(name, methodResult.ok);
  }

  return ok({
    vdict: { trait: term.dict.trait, type: term.dict.type, methods },
  });
}

function evaluateTraitMethod(
  term: TraitMethodTerm,
  env: Environment,
  context: TypeCheckerState,
  config: EvalConfig,
  steps: number,
): EvalResult {
  const dictResult = evaluateWithEnv(
    term.trait_method.dict,
    env,
    context,
    config,
    steps,
  );
  if ("err" in dictResult) return dictResult;

  if ("vdict" in dictResult.ok) {
    const method = dictResult.ok.vdict.methods.get(term.trait_method.method);
    if (!method) {
      return err(`Dictionary has no method: ${term.trait_method.method}`);
    }
    return ok(method);
  }

  return err("Cannot call method on non-dictionary value");
}

function matchPattern(
  pattern: Pattern,
  value: Value,
  env: Environment,
): Result<string, Environment> {
  if ("var" in pattern) {
    const newEnv = new Map(env);
    newEnv.set(pattern.var, value);
    return ok(newEnv);
  }

  if ("wildcard" in pattern) {
    return ok(env);
  }

  if ("variant" in pattern) {
    if ("vvariant" in value && value.vvariant.label === pattern.variant.label) {
      return matchPattern(pattern.variant.pattern, value.vvariant.value, env);
    }
    return err("Pattern mismatch");
  }

  if ("record" in pattern) {
    if (!("vrecord" in value)) return err("Pattern mismatch");

    let newEnv = env;
    for (const [label, subPattern] of pattern.record) {
      const fieldValue = value.vrecord[label];
      if (!fieldValue) return err("Pattern mismatch");

      const matchResult = matchPattern(subPattern, fieldValue, newEnv);
      if ("err" in matchResult) return matchResult;
      newEnv = matchResult.ok;
    }
    return ok(newEnv);
  }

  if ("tuple" in pattern) {
    if (!("vtuple" in value) || value.vtuple.length !== pattern.tuple.length) {
      return err("Pattern mismatch");
    }

    let newEnv = env;
    for (let i = 0; i < pattern.tuple.length; i++) {
      const matchResult = matchPattern(
        pattern.tuple[i]!,
        value.vtuple[i]!,
        newEnv,
      );
      if ("err" in matchResult) return matchResult;
      newEnv = matchResult.ok;
    }
    return ok(newEnv);
  }

  return err("Unsupported pattern type");
}

export function showValue(value: Value): string {
  if ("vvar" in value) return value.vvar;
  if ("vlam" in value) return `λ${value.vlam.param}. ...`;
  if ("vapp" in value)
    return `(${showValue(value.vapp.func)} ${showValue(value.vapp.arg)})`;
  if ("vrecord" in value) {
    const fields = Object.entries(value.vrecord)
      .map(([label, fieldValue]) => `${label} = ${showValue(fieldValue)}`)
      .join(", ");
    return `{${fields}}`;
  }
  if ("vvariant" in value) {
    return `<${value.vvariant.label}=${showValue(value.vvariant.value)}>`;
  }
  if ("vtuple" in value) {
    const elements = value.vtuple.map(showValue).join(", ");
    return `(${elements})`;
  }
  if ("vfold" in value) {
    return `fold[${showType(value.vfold.type)}](${showValue(value.vfold.value)})`;
  }
  if ("vdict" in value) {
    const methods = Array.from(value.vdict.methods.entries())
      .map(([name, method]) => `${name} = ${showValue(method)}`)
      .join(", ");
    return `dict ${value.vdict.trait}<${showType(value.vdict.type)}> { ${methods} }`;
  }
  return "unknown value";
}

// Utility to convert a Value back to a Term (useful for testing)
export function valueToTerm(value: Value): Term {
  if ("vvar" in value) return varTerm(value.vvar);
  if ("vlam" in value)
    return lamTerm(value.vlam.param, unitType, value.vlam.body);
  if ("vapp" in value)
    return appTerm(valueToTerm(value.vapp.func), valueToTerm(value.vapp.arg));
  if ("vrecord" in value) {
    const record: [string, Term][] = Object.entries(value.vrecord).map(
      ([label, fieldValue]) => [label, valueToTerm(fieldValue)],
    );
    return recordTerm(record);
  }
  if ("vvariant" in value) {
    return injectTerm(
      value.vvariant.label,
      valueToTerm(value.vvariant.value),
      unitType,
    );
  }
  if ("vtuple" in value) {
    return tupleTerm(value.vtuple.map(valueToTerm));
  }
  if ("vfold" in value) {
    return foldTerm(value.vfold.type, valueToTerm(value.vfold.value));
  }
  if ("vdict" in value) {
    const methods: [string, Term][] = Array.from(
      value.vdict.methods.entries(),
    ).map(([name, method]) => [name, valueToTerm(method)]);
    return dictTerm(value.vdict.trait, value.vdict.type, methods);
  }
  return varTerm("unknown");
}

export function typecheckAndEvaluate(
  term: Term,
  context: TypeCheckerState,
  config: EvalConfig = { strict: true, maxSteps: 1000 },
): Result<string, { type: Type; value: Value }> {
  // First typecheck the term
  const typeResult = inferType(context, term);
  if ("err" in typeResult) {
    return err(`Type error: ${JSON.stringify(typeResult.err)}`);
  }

  // Then evaluate the term
  const evalResult = evaluate(term, context, config);
  if ("err" in evalResult) {
    return err(`Evaluation error: ${evalResult.err}`);
  }

  return ok({ type: typeResult.ok, value: evalResult.ok });
}

export function evaluateTerms(
  terms: Term[],
  context: TypeCheckerState,
  config: EvalConfig = { strict: true, maxSteps: 1000 },
): Result<string, Value[]> {
  const results: Value[] = [];
  const currentEnv = new Map<string, Value>();

  for (const term of terms) {
    const result = evaluateWithEnv(term, currentEnv, context, config, 0);
    if ("err" in result) {
      return err(`Error evaluating term: ${result.err}`);
    }
    results.push(result.ok);

    // For top-level terms, we might want to update the environment
    // This depends on your specific requirements
    // For example, if the term is a let-binding, we could extract its binding
  }

  return ok(results);
}

// Alternative: Evaluate terms independently
export function evaluateTermsIndependently(
  terms: Term[],
  context: TypeCheckerState,
  config: EvalConfig = { strict: true, maxSteps: 1000 },
): Result<string, { term: Term; value: Value }[]> {
  const results: { term: Term; value: Value }[] = [];

  for (const term of terms) {
    const result = evaluate(term, context, config);
    if ("err" in result) {
      return err(`Error evaluating term: ${result.err}`);
    }
    results.push({ term, value: result.ok });
  }

  return ok(results);
}

// Handling of type-level constructs during evaluation
export function eraseTypes(term: Term): Term {
  // This function removes type-level constructs that don't affect runtime behavior
  if ("tylam" in term) {
    return eraseTypes(term.tylam.body);
  }

  if ("tyapp" in term) {
    return eraseTypes(term.tyapp.term);
  }

  if ("trait_lam" in term) {
    return eraseTypes(term.trait_lam.body);
  }

  if ("trait_app" in term) {
    return eraseTypes(term.trait_app.term);
  }

  // Recursively erase types in subterms
  if ("app" in term) {
    return appTerm(eraseTypes(term.app.callee), eraseTypes(term.app.arg));
  }

  if ("lam" in term) {
    return lamTerm(term.lam.arg, unitType, eraseTypes(term.lam.body));
  }

  // Add other cases as needed

  return term;
}

// Handling of primitive operations
export function evaluatePrimitive(
  op: string,
  args: Value[],
): Result<string, Value> {
  // This would implement primitive operations like arithmetic, boolean ops, etc.
  // Depends on what primitives you want to support

  switch (op) {
    case "add":
      if (args.length !== 2) return err("add expects 2 arguments");
      // Implementation for addition
      return err("add not implemented");
    case "eq":
      if (args.length !== 2) return err("eq expects 2 arguments");
      // Implementation for equality
      return err("eq not implemented");
    // Add other primitives
    default:
      return err(`Unknown primitive: ${op}`);
  }
}
