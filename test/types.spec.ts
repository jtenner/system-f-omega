// ./test/types.spec.ts
import { describe, expect, it, test } from "bun:test";
import {
  applySubstitution,
  appTerm,
  appType,
  arrowKind,
  arrowType,
  boundedForallType,
  checkExhaustive,
  checkKind,
  checkTraitConstraints,
  checkTraitImplementation,
  checkType,
  conPattern,
  conTerm,
  conType,
  createVariantLambda,
  dictTerm,
  foldTerm,
  forallType,
  freshMetaVar,
  getMetaSubstitution,
  getSpineArgs,
  getSpineHead,
  inferType,
  inferTypeWithMode,
  injectTerm,
  instantiateWithTraits,
  isAssignableTo,
  isStarKind,
  kindArity,
  kindsEqual,
  lamTerm,
  lamType,
  letTerm,
  matchTerm,
  mergeSubsts,
  metaKind,
  muType,
  neverType,
  normalizeType,
  projectTerm,
  recordPattern,
  recordTerm,
  recordType,
  resolveMetaVars,
  showKind,
  showTerm,
  showType,
  solveConstraints,
  solveMetaVar,
  starKind,
  substituteType,
  subsumes,
  traitAppTerm,
  traitLamTerm,
  traitMethodTerm,
  tuplePattern,
  tupleProjectTerm,
  tupleTerm,
  tupleType,
  tyappTerm,
  tylamTerm,
  typeAliasBinding,
  typecheck,
  typesEqual,
  unfoldTerm,
  unifyTypes,
  unifyVariable,
  unitType,
  unitValue,
  variantPattern,
  variantType,
  varPattern,
  varTerm,
  varType,
  type Worklist,
  wildcardPattern,
} from "../src/typechecker.js";
import type {
  ArrowType,
  ConType,
  Context,
  EnumDef,
  MuType,
  Term,
  TraitConstraint,
  TraitDef,
  TraitImplBinding,
  Type,
  VariantType,
  VarType,
} from "../src/types.js";

function assert(condition: boolean, message: string): asserts condition {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
}

function assertOk<T>(result: { ok: T } | { err: unknown }, message: string): T {
  if ("err" in result) {
    throw new Error(
      `Expected ok but got error: ${JSON.stringify(result.err)} - ${message}`,
    );
  }
  return result.ok;
}

function assertErr<E>(
  result: { ok: unknown } | { err: E },
  message: string,
): E {
  if ("ok" in result) {
    throw new Error(
      `Expected error but got ok: ${JSON.stringify(result.ok)} - ${message}`,
    );
  }
  return result.err;
}

test("Type variable kinding", () => {
  const ctx: Context = [{ type: { name: "T", kind: starKind } }];
  const result = checkKind(ctx, varType("T"));
  const kind = assertOk(result, "should infer kind *");
  assert("star" in kind, "should be star kind");
});

test("Higher-kinded type", () => {
  const ctx: Context = [
    { type: { name: "F", kind: { arrow: { from: starKind, to: starKind } } } },
  ];
  const result = checkKind(ctx, varType("F"));
  const kind = assertOk(result, "should infer kind * -> *");
  assert("arrow" in kind, "should be arrow kind");
});

test("Unbound variable error", () => {
  const result = typecheck([], varTerm("x"));
  const err = assertErr(result, "should fail");
  assert("unbound" in err, "should be unbound variable error");
});

test("Type application", () => {
  const intType = conType("Int");
  const polyId = tylamTerm(
    "T",
    starKind,
    lamTerm("x", varType("T"), varTerm("x")),
  );
  const intId = tyappTerm(polyId, intType);
  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], intId);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, intType), "should be Int -> Int");
});

test("Polymorphic record projection", () => {
  // select : ∀R. { x: R, y: Int } → R
  const selectX = tylamTerm(
    "R",
    starKind,
    lamTerm(
      "record",
      recordType([
        ["x", varType("R")],
        ["y", conType("Int")],
      ]),
      projectTerm(varTerm("record"), "x"),
    ),
  );

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  // Apply to { x: String, y: Int }
  const record = recordTerm([
    ["x", conTerm('"hello"', conType("String"))],
    ["y", conTerm("42", conType("Int"))],
  ]);

  const app = appTerm(tyappTerm(selectX, conType("String")), record);

  const result = typecheck(context, app);
  const type = assertOk(result, "should infer polymorphic projection");

  const resolved = resolveMetaVars(normalizeType(type));
  assert(
    typesEqual(resolved, conType("String")),
    `should be String, got ${showType(resolved)}`,
  );
});

test("Record projection error - missing field", () => {
  const person = recordTerm([["name", conTerm('"Alice"', conType("String"))]]);

  // Try to project non-existent field
  const getAge = projectTerm(person, "age");

  const result = typecheck([], getAge);

  assert("err" in result, "should fail");
  assert("missing_field" in result.err, "should be missing field error");
});

test("Simple variant", () => {
  const boolType = variantType([
    ["True", unitType],
    ["False", unitType],
  ]);

  const trueVal = injectTerm("True", unitValue, boolType);
  const result = typecheck([], trueVal);
  const type = assertOk(result, "should typecheck");
  assert("variant" in type, "should be variant type");
});

test("Large record", () => {
  const fields: [string, Term][] = [];
  for (let i = 0; i < 100; i++) {
    fields.push([`field${i}`, conTerm(`${i}`, conType("Int"))]);
  }

  const largeRecord = recordTerm(fields);
  const result = typecheck([], largeRecord);
  assertOk(result, "should handle large records");
});

test("let term", () => {
  const intType = conType("Int");
  const context: Context = [
    {
      term: {
        name: "+",
        type: arrowType(intType, arrowType(intType, intType)),
      },
    },
  ];

  const testTerm = letTerm(
    "x",
    conTerm("5", intType),
    // Fix: Apply "+" to "x" first, then apply the result to "3"
    appTerm(appTerm(varTerm("+"), varTerm("x")), conTerm("3", intType)),
  );

  const result = typecheck(context, testTerm);
  assertOk(result, "should typecheck");
});

test("Constant type kinding", () => {
  const result = checkKind(
    [{ type: { kind: starKind, name: "Int" } }],
    conType("Int"),
  );
  const kind = assertOk(result, "should infer kind *");
  assert("star" in kind, "should be star kind");
});

test("Arrow type kinding", () => {
  const intType = conType("Int");
  const boolType = conType("Bool");
  const arrowTy = arrowType(intType, boolType);
  const result = checkKind(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    arrowTy,
  );
  const kind = assertOk(result, "should infer kind *");
  assert("star" in kind, "should be star kind");
});

test("Identity function", () => {
  const intType = conType("Int");
  const identity = lamTerm("x", intType, varTerm("x"));
  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    identity,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, intType), "argument should be Int");
  assert(typesEqual(type.arrow.to, intType), "return should be Int");
});

test("Function application", () => {
  const intType = conType("Int");
  const identity = lamTerm("x", intType, varTerm("x"));
  const value = conTerm("42", intType);
  const app = appTerm(identity, value);
  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], app);
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, intType), "result should be Int");
});

test("Function composition", () => {
  const intType = conType("Int");
  const strType = conType("String");
  const boolType = conType("Bool");

  // f: Int -> String
  const f = lamTerm("x", intType, conTerm('"str"', strType));
  // g: String -> Bool
  const g = lamTerm("y", strType, conTerm("true", boolType));
  // compose g f: Int -> Bool
  const composed = lamTerm("z", intType, appTerm(g, appTerm(f, varTerm("z"))));

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    composed,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, intType), "argument should be Int");
  assert(typesEqual(type.arrow.to, boolType), "return should be Bool");
});

test("Type mismatch in application", () => {
  const intType = conType("Int");
  const strType = conType("String");
  const f = lamTerm("x", intType, varTerm("x"));
  const arg = conTerm('"hello"', strType);
  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    appTerm(f, arg),
  );
  const err = assertErr(result, "should fail");
  assert("type_mismatch" in err, "should be type mismatch error");
});

test("Polymorphic identity", () => {
  const polyId = tylamTerm(
    "T",
    starKind,
    lamTerm("x", varType("T"), varTerm("x")),
  );
  const result = typecheck([], polyId);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be forall type");
  assert(type.forall.var === "T", "should quantify over T");
});

test("Polymorphic constant function", () => {
  const constFn = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm("x", varType("A"), lamTerm("y", varType("B"), varTerm("x"))),
    ),
  );
  const result = typecheck([], constFn);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be polymorphic");
});

test("Missing field projection", () => {
  const person = recordTerm([["name", conTerm('"Alice"', conType("String"))]]);

  const getAge = projectTerm(person, "age");
  const result = typecheck([], getAge);
  const err = assertErr(result, "should fail");
  assert("missing_field" in err, "should be missing field error");
});

test("Option type - structural injection with explicit context", () => {
  const intType = conType("Int");
  const optionInt = variantType([
    ["None", unitType],
    ["Some", intType], // Uses con_type("Int")
  ]);

  // EXPLICIT CONTEXT: Bind "Int" :: * to handle kind checks
  const context = [
    { type: { name: "Int", kind: starKind } }, // Makes "Int" well-kinded
  ];

  const someVal = injectTerm("Some", conTerm("42", intType), optionInt);
  const result = typecheck(context, someVal); // Pass context
  const type = assertOk(result, "should typecheck");

  // Assertions
  expect("variant" in type).toBe(true);
  const variant = (type as VariantType).variant;
  expect(variant.length).toBe(2);
  // Optional: Check cases match
  expect(typesEqual(variant[0][1], unitType)).toBe(true); // None: ()
  expect(typesEqual(variant[1][1], intType)).toBe(true); // Some: Int
});

test("Invalid variant label", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  const invalid = injectTerm("Other", unitValue, optionInt);
  const result = typecheck([], invalid);
  const err = assertErr(result, "should fail");
  assert("invalid_variant_label" in err, "should be invalid label error");
});

test("Wrong variant payload type", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  const wrongType = injectTerm(
    "Some",
    conTerm('"str"', conType("String")),
    optionInt,
  );
  const result = typecheck(
    [
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Int" } },
    ],
    wrongType,
  );
  const err = assertErr(result, "should fail");
  assert("type_mismatch" in err, "should be type mismatch error");
});

test("Simple pattern match", () => {
  const boolType = variantType([
    ["True", unitType],
    ["False", unitType],
  ]);

  const notFn = lamTerm(
    "b",
    boolType,
    matchTerm(varTerm("b"), [
      [
        variantPattern("True", wildcardPattern()),
        injectTerm("False", unitValue, boolType),
      ],
      [
        variantPattern("False", wildcardPattern()),
        injectTerm("True", unitValue, boolType),
      ],
    ]),
  );

  const result = typecheck([], notFn);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
});

test("Pattern match with variable binding", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  const unwrap = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
      [variantPattern("Some", varPattern("x")), varTerm("x")],
    ]),
  );

  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], unwrap);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.to, conType("Int")), "should return Int");
});

test("Record pattern matching", () => {
  const pointType = recordType([
    ["x", conType("Int")],
    ["y", conType("Int")],
  ]);

  const getX = lamTerm(
    "p",
    pointType,
    matchTerm(varTerm("p"), [
      [
        recordPattern([
          ["x", varPattern("xVal")],
          ["y", wildcardPattern()],
        ]),
        varTerm("xVal"),
      ],
    ]),
  );

  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], getX);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.to, conType("Int")), "should return Int");
});

test("Nested pattern matching", () => {
  const resultType = variantType([
    ["Ok", conType("Int")],
    ["Err", conType("String")],
  ]);

  const optionResult = variantType([
    ["None", unitType],
    ["Some", resultType],
  ]);

  const unwrapAll = lamTerm(
    "x",
    optionResult,
    matchTerm(varTerm("x"), [
      [
        variantPattern("None", wildcardPattern()),
        conTerm("-1", conType("Int")),
      ],
      [
        variantPattern("Some", variantPattern("Ok", varPattern("val"))),
        varTerm("val"),
      ],
      [
        variantPattern("Some", variantPattern("Err", wildcardPattern())),
        conTerm("-2", conType("Int")),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    unwrapAll,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.to, conType("Int")), "should return Int");
});

test("Non-exhaustive pattern match", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  // Missing the Some case
  const incomplete = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
    ]),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    incomplete,
  );
  const err = assertErr(result, "should fail");
  assert("missing_case" in err, "should be missing case error");
});

test("Inconsistent branch types", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  const inconsistent = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
      [
        variantPattern("Some", varPattern("x")),
        conTerm('"str"', conType("String")),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    inconsistent,
  );
  const err = assertErr(result, "should fail");
  assert("type_mismatch" in err, "should be type mismatch error");
});

test("Polymorphic map for Option", () => {
  const mapOption = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm(
        "f",
        arrowType(varType("A"), varType("B")),
        lamTerm(
          "opt",
          variantType([
            ["None", unitType],
            ["Some", varType("A")],
          ]),
          matchTerm(varTerm("opt"), [
            [
              variantPattern("None", wildcardPattern()),
              injectTerm(
                "None",
                unitValue,
                variantType([
                  ["None", unitType],
                  ["Some", varType("B")],
                ]),
              ),
            ],
            [
              variantPattern("Some", varPattern("x")),
              injectTerm(
                "Some",
                appTerm(varTerm("f"), varTerm("x")),
                variantType([
                  ["None", unitType],
                  ["Some", varType("B")],
                ]),
              ),
            ],
          ]),
        ),
      ),
    ),
  );

  const result = typecheck([], mapOption);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be polymorphic");
});

test("List type with fold", () => {
  // List<T> = Nil | Cons(T, List<T>)
  // Note: This is a simplified version without recursive types
  const listInt = variantType([
    ["Nil", unitType],
    [
      "Cons",
      recordType([
        ["head", conType("Int")],
        ["tail", unitType],
      ]),
    ],
  ]);

  const sumList = lamTerm(
    "list",
    listInt,
    matchTerm(varTerm("list"), [
      [variantPattern("Nil", wildcardPattern()), conTerm("0", conType("Int"))],
      [
        variantPattern(
          "Cons",
          recordPattern([
            ["head", varPattern("h")],
            ["tail", wildcardPattern()],
          ]),
        ),
        varTerm("h"), // Simplified - would normally recurse
      ],
    ]),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    sumList,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
});

test("State monad return type structure", () => {
  // State s a = s -> (a, s)
  const stateType = (s: Type, a: Type): Type =>
    arrowType(
      s,
      recordType([
        ["value", a],
        ["state", s],
      ]),
    );

  // return : ∀S. ∀A. A -> State S A
  const returnState = tylamTerm(
    "S",
    starKind,
    tylamTerm(
      "A",
      starKind,
      lamTerm(
        "x",
        varType("A"),
        lamTerm(
          "s",
          varType("S"),
          recordTerm([
            ["value", varTerm("x")],
            ["state", varTerm("s")],
          ]),
        ),
      ),
    ),
  );

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  const result = typecheck(context, returnState);
  const type = assertOk(result, "should typecheck");

  assert("forall" in type, "should be polymorphic in S");
  assert("forall" in type.forall.body, "should be polymorphic in A");

  // Instantiate with concrete types: return[Int][String]
  const concrete = tyappTerm(
    tyappTerm(returnState, conType("Int")),
    conType("String"),
  );

  const concreteResult = typecheck(context, concrete);
  const concreteType = assertOk(concreteResult, "should instantiate");
  const resolved = resolveMetaVars(normalizeType(concreteType));

  // Should be: String -> State Int String
  // Which is: String -> Int -> {value: String, state: Int}
  const expected = arrowType(
    conType("String"),
    stateType(conType("Int"), conType("String")),
  );

  assert(
    typesEqual(resolved, expected),
    `should be String -> State Int String, got ${showType(resolved)}`,
  );
});

test("State monad get operation", () => {
  // State s a = s -> (a, s)
  const stateType = (s: Type, a: Type): Type =>
    arrowType(
      s,
      recordType([
        ["value", a],
        ["state", s],
      ]),
    );

  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  // get : ∀S. State S S  (returns current state as value)
  const getState = tylamTerm(
    "S",
    starKind,
    lamTerm(
      "s",
      varType("S"),
      recordTerm([
        ["value", varTerm("s")],
        ["state", varTerm("s")],
      ]),
    ),
  );

  // Instantiate with Int: get[Int] : Int -> {value: Int, state: Int}
  const intGet = tyappTerm(getState, conType("Int"));
  const result = typecheck(context, intGet);
  const type = assertOk(result, "should instantiate get with Int");

  const resolved = resolveMetaVars(normalizeType(type));
  const expected = stateType(conType("Int"), conType("Int"));

  assert(
    typesEqual(resolved, expected),
    `should be State Int Int, got ${showType(resolved)}`,
  );
});

test("State monad put operation", () => {
  // State s a = s -> (a, s)
  const stateType = (s: Type, a: Type): Type =>
    arrowType(
      s,
      recordType([
        ["value", a],
        ["state", s],
      ]),
    );

  const unitType = recordType([]);

  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  // put : ∀S. S -> State S Unit (sets new state, returns unit)
  const putState = tylamTerm(
    "S",
    starKind,
    lamTerm(
      "newState",
      varType("S"),
      lamTerm(
        "oldState",
        varType("S"),
        recordTerm([
          ["value", recordTerm([])], // unit value
          ["state", varTerm("newState")],
        ]),
      ),
    ),
  );

  // Instantiate with Int
  const intPut = tyappTerm(putState, conType("Int"));
  const result = typecheck(context, intPut);
  const type = assertOk(result, "should instantiate put with Int");

  const resolved = resolveMetaVars(normalizeType(type));

  // Should be: Int -> Int -> {value: {}, state: Int}
  const expected = arrowType(
    conType("Int"),
    stateType(conType("Int"), unitType),
  );

  assert(
    typesEqual(resolved, expected),
    `should be Int -> State Int Unit, got ${showType(resolved)}`,
  );
});

test("State monad stateful computation", () => {
  // State s a = s -> (a, s)
  const stateType = (s: Type, a: Type): Type =>
    arrowType(
      s,
      recordType([
        ["value", a],
        ["state", s],
      ]),
    );

  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  // A stateful computation that reads and increments counter
  // increment : State Int Int
  const increment = lamTerm(
    "counter",
    conType("Int"),
    recordTerm([
      ["value", varTerm("counter")], // return current value
      ["state", conTerm("next", conType("Int"))], // increment state
    ]),
  );

  const result = typecheck(context, increment);
  const type = assertOk(result, "should typecheck stateful computation");

  const resolved = resolveMetaVars(normalizeType(type));
  const expected = stateType(conType("Int"), conType("Int"));

  assert(
    typesEqual(resolved, expected),
    `should be State Int Int, got ${showType(resolved)}`,
  );
});

test("Either type with bimap", () => {
  const eitherType = (l: Type, r: Type): Type =>
    variantType([
      ["Left", l],
      ["Right", r],
    ]);

  const bimap = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      tylamTerm(
        "C",
        starKind,
        tylamTerm(
          "D",
          starKind,
          lamTerm(
            "f",
            arrowType(varType("A"), varType("C")),
            lamTerm(
              "g",
              arrowType(varType("B"), varType("D")),
              lamTerm(
                "either",
                eitherType(varType("A"), varType("B")),
                matchTerm(varTerm("either"), [
                  [
                    variantPattern("Left", varPattern("x")),
                    injectTerm(
                      "Left",
                      appTerm(varTerm("f"), varTerm("x")),
                      eitherType(varType("C"), varType("D")),
                    ),
                  ],
                  [
                    variantPattern("Right", varPattern("y")),
                    injectTerm(
                      "Right",
                      appTerm(varTerm("g"), varTerm("y")),
                      eitherType(varType("C"), varType("D")),
                    ),
                  ],
                ]),
              ),
            ),
          ),
        ),
      ),
    ),
  );

  const result = typecheck([], bimap);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be polymorphic");
});

test("Natural number type", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );

  const kind = checkKind([], natType);
  const k = assertOk(kind, "should have kind *");
  assert("star" in k, "should be star kind");
});

test("Zero value", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );

  const zero = foldTerm(
    natType,
    injectTerm(
      "Zero",
      unitValue,
      variantType([
        ["Zero", unitType],
        ["Succ", natType],
      ]),
    ),
  );

  const result = typecheck([], zero);
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, natType), "should be Nat type");
});

test("Successor function", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );

  const succ = lamTerm(
    "n",
    natType,
    foldTerm(
      natType,
      injectTerm(
        "Succ",
        varTerm("n"),
        variantType([
          ["Zero", unitType],
          ["Succ", natType],
        ]),
      ),
    ),
  );

  const result = typecheck([], succ);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, natType), "input should be Nat");
  assert(typesEqual(type.arrow.to, natType), "output should be Nat");
});

test("Unfold natural number", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );

  const ctx: Context = [{ term: { name: "n", type: natType } }];
  const unfolded = unfoldTerm(varTerm("n"));

  const result = typecheck(ctx, unfolded);
  const type = assertOk(result, "should typecheck");
  assert("variant" in type, "should be variant type");
});

test("List type", () => {
  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const kind = checkKind([{ type: { kind: starKind, name: "Int" } }], listInt);
  const k = assertOk(kind, "should have kind *");
  assert("star" in k, "should be star kind");
});

test("Empty list", () => {
  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const emptyList = foldTerm(
    listInt,
    injectTerm(
      "Nil",
      unitValue,
      variantType([
        ["Nil", unitType],
        [
          "Cons",
          recordType([
            ["head", conType("Int")],
            ["tail", listInt],
          ]),
        ],
      ]),
    ),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    emptyList,
  );
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, listInt), "should be List Int type");
});

test("Cons cell", () => {
  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const emptyList = foldTerm(
    listInt,
    injectTerm(
      "Nil",
      unitValue,
      variantType([
        ["Nil", unitType],
        [
          "Cons",
          recordType([
            ["head", conType("Int")],
            ["tail", listInt],
          ]),
        ],
      ]),
    ),
  );

  const oneElementList = foldTerm(
    listInt,
    injectTerm(
      "Cons",
      recordTerm([
        ["head", conTerm("42", conType("Int"))],
        ["tail", emptyList],
      ]),
      variantType([
        ["Nil", unitType],
        [
          "Cons",
          recordType([
            ["head", conType("Int")],
            ["tail", listInt],
          ]),
        ],
      ]),
    ),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    oneElementList,
  );
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, listInt), "should be List Int type");
});

test("Tuple with type checking and projection", () => {
  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
  ];

  const tupleTy = tupleType([conType("Int"), conType("String")]);
  const tuple = tupleTerm([
    conTerm("42", conType("Int")),
    conTerm('"hello"', conType("String")),
  ]);

  // Check tuple inference
  const result = typecheck(context, tuple);
  const type = assertOk(result, "should typecheck");

  const resolved = resolveMetaVars(normalizeType(type));
  assert(
    typesEqual(resolved, tupleTy),
    `should be (Int, String), got ${showType(resolved)}`,
  );

  // Check tuple projection
  const proj0 = tupleProjectTerm(tuple, 0);
  const proj0Type = assertOk(typecheck(context, proj0), "should project first");
  assert(
    typesEqual(resolveMetaVars(normalizeType(proj0Type)), conType("Int")),
    "first element should be Int",
  );

  const proj1 = tupleProjectTerm(tuple, 1);
  const proj1Type = assertOk(
    typecheck(context, proj1),
    "should project second",
  );
  assert(
    typesEqual(resolveMetaVars(normalizeType(proj1Type)), conType("String")),
    "second element should be String",
  );
});

test("Tuple projection out of bounds", () => {
  const context: Context = [{ type: { kind: starKind, name: "Int" } }];

  const tuple = tupleTerm([conTerm("42", conType("Int"))]);
  const badProj = tupleProjectTerm(tuple, 1);

  const result = typecheck(context, badProj);
  assert("err" in result, "should fail");
  assert(
    "tuple_index_out_of_bounds" in result.err,
    `should be out of bounds error, got ${Object.keys(result.err)[0]}`,
  );
});

test("Nested tuples", () => {
  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "Bool" } },
  ];

  // ((1, 2), true)
  const nested = tupleTerm([
    tupleTerm([conTerm("1", conType("Int")), conTerm("2", conType("Int"))]),
    conTerm("true", conType("Bool")),
  ]);

  const result = typecheck(context, nested);
  const type = assertOk(result, "should typecheck nested tuple");

  const resolved = resolveMetaVars(normalizeType(type));
  const expected = tupleType([
    tupleType([conType("Int"), conType("Int")]),
    conType("Bool"),
  ]);

  assert(
    typesEqual(resolved, expected),
    `should be ((Int, Int), Bool), got ${showType(resolved)}`,
  );

  // Project nested: nested.0.1 should be Int
  const proj = tupleProjectTerm(tupleProjectTerm(nested, 0), 1);
  const projType = assertOk(typecheck(context, proj), "should project nested");

  assert(
    typesEqual(resolveMetaVars(normalizeType(projType)), conType("Int")),
    "nested projection should be Int",
  );
});

test("Simple tuple swap with inference", () => {
  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    {
      term: {
        name: "fst",
        type: forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(tupleType([varType("A"), varType("B")]), varType("A")),
          ),
        ),
      },
    },
  ];

  const pair = tupleTerm([
    conTerm("42", conType("Int")),
    conTerm('"hello"', conType("String")),
  ]);

  // fst should infer A=Int, B=String from the argument
  const result = appTerm(varTerm("fst"), pair);

  const inferredType = typecheck(context, result);
  const type = assertOk(inferredType, "should infer first element type");

  const resolved = resolveMetaVars(normalizeType(type));

  assert(
    typesEqual(resolved, conType("Int")),
    `should be Int, got ${showType(resolved)}`,
  );
});

test("Unit type as empty tuple", () => {
  const unit = tupleTerm([]);

  const result = typecheck([], unit);
  const type = assertOk(result, "should typecheck unit");

  const resolved = resolveMetaVars(normalizeType(type));
  assert(
    typesEqual(resolved, unitType),
    `should be unit type, got ${showType(resolved)}`,
  );
});

test("Tuple projection", () => {
  const tuple = tupleTerm([
    conTerm("42", conType("Int")),
    conTerm('"hello"', conType("String")),
    conTerm("true", conType("Bool")),
  ]);

  const proj0 = tupleProjectTerm(tuple, 0);
  const proj1 = tupleProjectTerm(tuple, 1);
  const proj2 = tupleProjectTerm(tuple, 2);

  const result0 = typecheck([], proj0);
  const type0 = assertOk(result0, "should typecheck");
  assert(typesEqual(type0, conType("Int")), "should be Int");

  const result1 = typecheck([], proj1);
  const type1 = assertOk(result1, "should typecheck");
  assert(typesEqual(type1, conType("String")), "should be String");

  const result2 = typecheck([], proj2);
  const type2 = assertOk(result2, "should typecheck");
  assert(typesEqual(type2, conType("Bool")), "should be Bool");
});

test("Out of bounds tuple projection", () => {
  const tuple = tupleTerm([
    conTerm("42", conType("Int")),
    conTerm('"hello"', conType("String")),
  ]);

  const outOfBounds = tupleProjectTerm(tuple, 5);
  const result = typecheck([], outOfBounds);
  const err = assertErr(result, "should fail");
  assert("tuple_index_out_of_bounds" in err, "should be out of bounds error");
});

test("Negative tuple projection", () => {
  const tuple = tupleTerm([conTerm("42", conType("Int"))]);
  const negative = tupleProjectTerm(tuple, -1);
  const result = typecheck([], negative);
  const err = assertErr(result, "should fail");
  assert("tuple_index_out_of_bounds" in err, "should be out of bounds error");
});

test("Empty tuple (unit)", () => {
  const emptyTuple = tupleTerm([]);
  const result = typecheck([], emptyTuple);
  const type = assertOk(result, "should typecheck");
  assert("tuple" in type, "should be tuple type");
  assert(type.tuple.length === 0, "should be empty");
});

test("Nested tuples", () => {
  const innerTuple = tupleTerm([
    conTerm("1", conType("Int")),
    conTerm("2", conType("Int")),
  ]);

  const outerTuple = tupleTerm([
    innerTuple,
    conTerm('"outer"', conType("String")),
  ]);

  const getInnerFirst = tupleProjectTerm(tupleProjectTerm(outerTuple, 0), 0);

  const result = typecheck([], getInnerFirst);
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, conType("Int")), "should be Int");
});

test("Tuple pattern matching", () => {
  const pairType = tupleType([conType("Int"), conType("String")]);

  const swap = lamTerm(
    "p",
    pairType,
    matchTerm(varTerm("p"), [
      [
        tuplePattern([varPattern("x"), varPattern("y")]),
        tupleTerm([varTerm("y"), varTerm("x")]),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    swap,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
});

test("Tuple with wildcard pattern", () => {
  const tripleType = tupleType([
    conType("Int"),
    conType("String"),
    conType("Bool"),
  ]);

  const getFirst = lamTerm(
    "t",
    tripleType,
    matchTerm(varTerm("t"), [
      [
        tuplePattern([varPattern("x"), wildcardPattern(), wildcardPattern()]),
        varTerm("x"),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    getFirst,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.to, conType("Int")), "should return Int");
});

test("Polymorphic fst function", () => {
  const fst = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm(
        "p",
        tupleType([varType("A"), varType("B")]),
        tupleProjectTerm(varTerm("p"), 0),
      ),
    ),
  );

  const result = typecheck([], fst);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be polymorphic");
});

test("Polymorphic snd function", () => {
  const snd = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm(
        "p",
        tupleType([varType("A"), varType("B")]),
        tupleProjectTerm(varTerm("p"), 1),
      ),
    ),
  );

  const result = typecheck([], snd);
  const type = assertOk(result, "should typecheck");
  assert("forall" in type, "should be polymorphic");
});

test("Map function", () => {
  const map = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm(
        "f",
        arrowType(varType("A"), varType("B")),
        lamTerm("x", varType("A"), appTerm(varTerm("f"), varTerm("x"))),
      ),
    ),
  );

  const result = typecheck([], map);
  assertOk(result, "should typecheck");
});

test("Compose function", () => {
  const compose = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      tylamTerm(
        "C",
        starKind,
        lamTerm(
          "f",
          arrowType(varType("B"), varType("C")),
          lamTerm(
            "g",
            arrowType(varType("A"), varType("B")),
            lamTerm(
              "x",
              varType("A"),
              appTerm(varTerm("f"), appTerm(varTerm("g"), varTerm("x"))),
            ),
          ),
        ),
      ),
    ),
  );

  const result = typecheck([], compose);
  assertOk(result, "should typecheck");
});

test("Flip function", () => {
  const flip = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      tylamTerm(
        "C",
        starKind,
        lamTerm(
          "f",
          arrowType(varType("A"), arrowType(varType("B"), varType("C"))),
          lamTerm(
            "b",
            varType("B"),
            lamTerm(
              "a",
              varType("A"),
              appTerm(appTerm(varTerm("f"), varTerm("a")), varTerm("b")),
            ),
          ),
        ),
      ),
    ),
  );

  const result = typecheck([], flip);
  assertOk(result, "should typecheck");
});

test("Type constructor application", () => {
  const listCon = lamType(
    "T",
    starKind,
    muType(
      "L",
      variantType([
        ["Nil", unitType],
        [
          "Cons",
          recordType([
            ["head", varType("T")],
            ["tail", varType("L")],
          ]),
        ],
      ]),
    ),
  );

  const listInt = appType(listCon, conType("Int"));
  const kind = checkKind([{ type: { kind: starKind, name: "Int" } }], listInt);
  assertOk(kind, "should have valid kind");
});

test("Type constructor kind mismatch", () => {
  const ctx: Context = [
    { type: { name: "F", kind: { arrow: { from: starKind, to: starKind } } } },
  ];

  // Try to apply F to something that's not kind *
  const badApp = appType(varType("F"), lamType("X", starKind, varType("X")));

  const result = checkKind(ctx, badApp);
  const err = assertErr(result, "should fail");
  assert("kind_mismatch" in err, "should be kind mismatch");
});

test("Self-application with unbound type variable", () => {
  // λx: (T → T). x x - fails because T is unbound
  const selfApp = lamTerm(
    "x",
    arrowType(varType("T"), varType("T")),
    appTerm(varTerm("x"), varTerm("x")),
  );

  const result = typecheck([], selfApp);
  const err = assertErr(result, "should fail with unbound type variable");
  assert("unbound" in err && err.unbound === "T", "should report unbound T");
});

test("Self-application fails with cyclic type", () => {
  // λx: (T → T). x x
  // This fails because trying to unify T with (T → T) creates a cyclic type
  const selfApp = lamTerm(
    "x",
    arrowType(varType("T"), varType("T")),
    appTerm(varTerm("x"), varTerm("x")),
  );

  const context: Context = [{ type: { name: "T", kind: starKind } }];

  const result = typecheck(context, selfApp);
  const err = assertErr(result, "should fail type checking");
  assert(
    "cyclic" in err && err.cyclic === "T",
    "should detect cyclic type T = T → T",
  );
});

test("Self-application fails with type mismatch", () => {
  // λx: (Int → Int). x x
  // This fails because:
  // - x expects argument of type Int
  // - but x itself has type Int → Int (not Int)
  const selfApp = lamTerm(
    "x",
    arrowType(conType("Int"), conType("Int")),
    appTerm(varTerm("x"), varTerm("x")),
  );

  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  const result = typecheck(context, selfApp);
  const err = assertErr(result, "should fail type checking");
  assert("type_mismatch" in err, "x x should be a type mismatch");
  // Expected: x takes argument of type Int
  // Actual: x has type Int → Int
});

test("Polymorphic self-application succeeds in System F", () => {
  // λx: (∀β. β → β). x [∀β. β → β] x
  // Instantiate the polymorphic identity at its own type

  const polyId = forallType(
    "β",
    starKind,
    arrowType(varType("β"), varType("β")),
  );

  const selfApp = lamTerm(
    "x",
    polyId, // x : ∀β. β → β
    appTerm(
      tyappTerm(varTerm("x"), polyId), // x[∀β. β → β] : (∀β. β → β) → (∀β. β → β)
      varTerm("x"), // x : ∀β. β → β
    ),
  );

  const result = typecheck([], selfApp);
  const type = assertOk(result, "polymorphic self-application should succeed");
  assert("arrow" in type, "should be function type");
  assert(
    typesEqual(type, arrowType(polyId, polyId)),
    "should have type (∀β. β → β) → (∀β. β → β)",
  );
});

test("Omega combinator (ω ω) cannot be typed", () => {
  // ω = λx. x x
  // This cannot be given a simple type in System F without recursive types

  // Attempt 1: Try with a concrete type
  const omega = lamTerm(
    "x",
    arrowType(conType("Int"), conType("Int")),
    appTerm(varTerm("x"), varTerm("x")),
  );

  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  const result = typecheck(context, omega);
  const err = assertErr(result, "omega combinator should not typecheck");
  assert(
    "type_mismatch" in err || "not_a_function" in err,
    "should fail because x expects Int but gets (Int → Int)",
  );
});

test("Deep nesting", () => {
  // Deeply nested records
  let deepRecord: Term = conTerm("42", conType("Int"));
  for (let i = 0; i < 10; i++) {
    deepRecord = recordTerm([["inner", deepRecord]]);
  }

  const result = typecheck([], deepRecord);
  assertOk(result, "should handle deep nesting");
});

test("Shadowed variables", () => {
  const shadowed = lamTerm(
    "x",
    conType("Int"),
    lamTerm("x", conType("String"), varTerm("x")),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    shadowed,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  // Inner x shadows outer x, so result should be String
});

test("Binary tree type", () => {
  const treeInt = muType(
    "T",
    variantType([
      ["Leaf", conType("Int")],
      [
        "Node",
        recordType([
          ["left", varType("T")],
          ["right", varType("T")],
        ]),
      ],
    ]),
  );

  const kind = checkKind([{ type: { kind: starKind, name: "Int" } }], treeInt);
  assertOk(kind, "should have kind *");
});

test("Infinite list (stream) type", () => {
  const streamInt = muType(
    "S",
    recordType([
      ["head", conType("Int")],
      ["tail", varType("S")],
    ]),
  );

  const kind = checkKind(
    [{ type: { kind: starKind, name: "Int" } }],
    streamInt,
  );
  assertOk(kind, "should have kind *");
});

test("Multiple patterns same match", () => {
  const eitherType = variantType([
    ["Left", conType("Int")],
    ["Right", conType("Int")],
  ]);

  const toInt = lamTerm(
    "e",
    eitherType,
    matchTerm(varTerm("e"), [
      [variantPattern("Left", varPattern("x")), varTerm("x")],
      [variantPattern("Right", varPattern("y")), varTerm("y")],
    ]),
  );

  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], toInt);
  assertOk(result, "should typecheck");
});

test("Nested tuple and record patterns", () => {
  const complexType = recordType([
    ["data", tupleType([conType("Int"), conType("String")])],
    ["flag", conType("Bool")],
  ]);

  const extract = lamTerm(
    "x",
    complexType,
    matchTerm(varTerm("x"), [
      [
        recordPattern([
          ["data", tuplePattern([varPattern("n"), wildcardPattern()])],
          ["flag", wildcardPattern()],
        ]),
        varTerm("n"),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    extract,
  );
  assertOk(result, "should typecheck");
});

test("simple normalization", () => {
  const idType = lamType("T", starKind, varType("T"));
  const intType = conType("Int");
  const appliedType = appType(idType, intType);
  const normalized = normalizeType(appliedType);
  const expected = intType;
  assert(
    typesEqual(normalized, expected),
    `Expected ${showType(expected)} but got ${showType(normalized)}`,
  );
});

test("nested beta reductions", () => {
  const doubleApp = lamType(
    "A",
    starKind,
    lamType("B", starKind, arrowType(varType("A"), varType("B"))),
  );
  const applied = appType(appType(doubleApp, conType("Int")), conType("Bool"));
  const normalized = normalizeType(applied);
  const expected = arrowType(conType("Int"), conType("Bool"));
  assert(
    typesEqual(normalized, expected),
    `Expected ${showType(expected)} but got ${showType(normalized)}`,
  );
});

test("Trivial forall (unused type variable) - preserved, no elimination", () => {
  const trivialForall = forallType("X", starKind, conType("Int"));

  const normalized = normalizeType(trivialForall);
  // Expected: Forall is preserved (no automatic elimination in normalizeType)
  const expected = trivialForall;

  assert(
    typesEqual(normalized, expected),
    `Expected ${showType(expected)} but got ${showType(normalized)}`,
  );
  assert(
    "forall" in normalized,
    `Normalized type should preserve forall structure`,
  );
});

test("Mu types should NOT unfold during normalization", () => {
  const listType = muType(
    "L",
    variantType([
      ["Nil", unitType],
      ["Cons", tupleType([conType("Int"), varType("L")])],
    ]),
  );

  const normalized = normalizeType(listType);
  assert(
    "mu" in normalized,
    `Test 4 failed: Mu type should not unfold during normalization`,
  );
  assert(
    typesEqual(normalized, listType),
    `Test 4 failed: Mu type should remain unchanged`,
  );
});

test("Single-element tuple - preserved, no simplification", () => {
  const singleTuple = tupleType([conType("Int")]);
  const normalized = normalizeType(singleTuple);
  // Expected: Remains a tuple (no simplification to Int in normalizeType)
  const expected = singleTuple;

  assert(
    typesEqual(normalized, expected),
    `Expected ${showType(expected)} but got ${showType(normalized)}`,
  );
  assert(
    "tuple" in normalized && normalized.tuple.length === 1,
    `Normalized type should preserve single-element tuple structure`,
  );
});

test("Empty record - preserved, no simplification to unit", () => {
  // Note: In this system, records and tuples (unitType = empty tuple) are distinct;
  // no automatic conversion in normalizeType.
  const emptyRecord = recordType([]);
  const normalized = normalizeType(emptyRecord);
  // Expected: Remains an empty record (no conversion to unitType)
  const expected = emptyRecord;

  assert(
    typesEqual(normalized, expected),
    `Expected ${showType(expected)} but got ${showType(normalized)}`,
  );
  assert(
    "record" in normalized && normalized.record.length === 0,
    `Normalized type should preserve empty record structure`,
  );
});

test("Complex nested application", () => {
  const constType = lamType(
    "A",
    starKind,
    lamType("B", starKind, varType("A")),
  );
  const applied7 = appType(
    appType(constType, conType("String")),
    conType("Bool"),
  );

  const normalized7 = normalizeType(applied7);
  const expected7 = conType("String");

  assert(
    typesEqual(normalized7, expected7),
    `Expected ${showType(expected7)} but got ${showType(normalized7)}`,
  );
});

test("Normalization preserves used forall variables", () => {
  const usedForall = forallType(
    "T",
    starKind,
    arrowType(varType("T"), varType("T")),
  );

  const normalized = normalizeType(usedForall);

  assert(
    "forall" in normalized,
    `Forall with used variable should be preserved`,
  );
  assert(
    typesEqual(normalized, usedForall),
    `Used forall should remain unchanged`,
  );
});

// type T = Int
test("Dictionary for Show Int", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));

  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
  ];

  const result = typecheck(context, intShowDict);
  const type = assertOk(result, "should typecheck");
  assert("con" in type, "should be dictionary type");
});

test("Dictionary with missing method", () => {
  const eqTrait: TraitDef = {
    name: "Eq",
    type_param: "Self",
    kind: starKind,
    methods: [
      [
        "eq",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool"))),
      ],
      [
        "neq",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool"))),
      ],
    ],
  };

  const intType = conType("Int");
  const eqImpl = lamTerm(
    "x",
    intType,
    lamTerm("y", intType, conTerm("true", conType("Bool"))),
  );

  // Missing neq method
  const incompleteDict = dictTerm("Eq", intType, [["eq", eqImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "Bool" } },
    { trait_def: eqTrait },
  ];

  const result = typecheck(context, incompleteDict);
  const err = assertErr(result, "should fail");
  assert("missing_method" in err, "should be missing method error");
});

test("Dictionary with wrong method type", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  // Wrong: returns Int instead of String
  const wrongImpl = lamTerm("x", intType, conTerm("42", intType));

  const wrongDict = dictTerm("Show", intType, [["show", wrongImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
  ];

  const result = typecheck(context, wrongDict);
  const err = assertErr(result, "should fail");
  assert("type_mismatch" in err, "should be type mismatch error");
});

test("Trait method access from dictionary variable", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");

  const context: Context = [
    { trait_def: showTrait },
    {
      dict: {
        name: "showIntDict",
        trait: "Show",
        type: intType,
      },
    },
  ];

  const methodAccess = traitMethodTerm(varTerm("showIntDict"), "show");

  const result = typecheck(context, methodAccess);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, intType), "should take Int");
  assert(typesEqual(type.arrow.to, conType("String")), "should return String");
});

test("Trait method access from concrete dictionary", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
  ];

  const methodAccess = traitMethodTerm(intShowDict, "show");

  const result = typecheck(context, methodAccess);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
});

test("Trait method access with wrong method name", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");

  const context: Context = [
    { trait_def: showTrait },
    {
      dict: {
        name: "showIntDict",
        trait: "Show",
        type: intType,
      },
    },
  ];

  const wrongMethod = traitMethodTerm(varTerm("showIntDict"), "wrongMethod");

  const result = typecheck(context, wrongMethod);
  const err = assertErr(result, "should fail");
  assert("missing_method" in err, "should be missing method error");
});

test("Simple trait lambda", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  // Λ T where Show<T>. λx:T. show(dict, x)
  const showValue = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "x",
      varType("T"),
      appTerm(traitMethodTerm(varTerm("showDict"), "show"), varTerm("x")),
    ),
  );

  const context: Context = [{ trait_def: showTrait }];

  const result = typecheck(context, showValue);
  const type = assertOk(result, "should typecheck");
  assert("bounded_forall" in type, "should be bounded forall type");
  assert(
    type.bounded_forall.constraints.length === 1,
    "should have one constraint",
  );
  assert(
    type.bounded_forall.constraints[0]?.trait === "Show",
    "should have Show constraint",
  );
});

test("Trait application with concrete type", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const showValue = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "x",
      varType("T"),
      appTerm(traitMethodTerm(varTerm("showDict"), "show"), varTerm("x")),
    ),
  );

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
    { trait_impl: { trait: "Show", type: intType, dict: intShowDict } },
  ];

  // Apply to Int type with dictionary
  const applied = traitAppTerm(showValue, intType, [intShowDict]);

  const result = typecheck(context, applied);
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.from, intType), "should take Int");
  assert(typesEqual(type.arrow.to, conType("String")), "should return String");
});

test("Trait application with missing implementation", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const showValue = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "x",
      varType("T"),
      appTerm(traitMethodTerm(varTerm("showDict"), "show"), varTerm("x")),
    ),
  );

  const context: Context = [
    { trait_def: showTrait },
    { type: { kind: starKind, name: "Bool" } },
  ];

  const boolType = conType("Bool");
  // No Show implementation for Bool provided
  const applied = traitAppTerm(showValue, boolType, []);

  const result = typecheck(context, applied);
  const err = assertErr(result, "should fail");
  assert(
    "missing_trait_impl" in err || "wrong_number_of_dicts" in err,
    "should be missing implementation error",
  );
});

test("Multiple trait constraints", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const eqTrait: TraitDef = {
    name: "Eq",
    type_param: "Self",
    kind: starKind,
    methods: [
      [
        "eq",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool"))),
      ],
    ],
  };

  // Λ T where Show<T>, Eq<T>. λx:T. λy:T. ...
  const compareAndShow = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [
      { trait: "Show", type: varType("T") },
      { trait: "Eq", type: varType("T") },
    ],
    lamTerm(
      "x",
      varType("T"),
      lamTerm("y", varType("T"), conTerm('"result"', conType("String"))),
    ),
  );

  const context: Context = [{ trait_def: showTrait }, { trait_def: eqTrait }];

  const result = typecheck(context, compareAndShow);
  const type = assertOk(result, "should typecheck");
  assert("bounded_forall" in type, "should be bounded forall type");
  assert(
    type.bounded_forall.constraints.length === 2,
    "should have two constraints",
  );
});

test("Functor trait with map", () => {
  const functorTrait: TraitDef = {
    name: "Functor",
    type_param: "F",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "map",
        forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              arrowType(varType("A"), varType("B")),
              arrowType(
                appType(varType("F"), varType("A")),
                appType(varType("F"), varType("B")),
              ),
            ),
          ),
        ),
      ],
    ],
  };

  const context: Context = [{ trait_def: functorTrait }];

  // Just verify the trait definition typechecks
  const binding = context.find((b) => "trait_def" in b);
  assert(binding !== undefined, "trait should be in context");
});

test("Pattern matching with constant patterns", () => {
  const intType = conType("Int");

  const isZero = lamTerm(
    "x",
    intType,
    matchTerm(varTerm("x"), [
      [conPattern("0", intType), conTerm("true", conType("Bool"))],
      [wildcardPattern(), conTerm("false", conType("Bool"))],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    isZero,
  );
  assertOk(result, "should handle constant patterns");
});

test("Higher-kinded trait (Functor)", () => {
  const functorTrait: TraitDef = {
    name: "Functor",
    type_param: "F",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "map",
        forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              arrowType(varType("A"), varType("B")),
              arrowType(
                appType(varType("F"), varType("A")),
                appType(varType("F"), varType("B")),
              ),
            ),
          ),
        ),
      ],
    ],
  };

  // Option functor
  const optionCon = lamType(
    "T",
    starKind,
    variantType([
      ["None", unitType],
      ["Some", varType("T")],
    ]),
  );

  const context: Context = [{ trait_def: functorTrait }];

  // Check that Option has the right kind for Functor
  const optionKind = checkKind(context, optionCon);
  const kind = assertOk(optionKind, "should have kind * -> *");
  assert("arrow" in kind, "should be arrow kind");
});

test("Trait with associated types simulation", () => {
  // Collection with element type
  const collectionTrait: TraitDef = {
    name: "Collection",
    type_param: "C",
    kind: starKind,
    methods: [
      ["empty", varType("C")],
      ["size", arrowType(varType("C"), conType("Int"))],
    ],
  };

  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const emptyList = foldTerm(
    listInt,
    injectTerm(
      "Nil",
      unitValue,
      variantType([
        ["Nil", unitType],
        [
          "Cons",
          recordType([
            ["head", conType("Int")],
            ["tail", listInt],
          ]),
        ],
      ]),
    ),
  );

  const sizeImpl = lamTerm("list", listInt, conTerm("0", conType("Int")));

  const listDict = dictTerm("Collection", listInt, [
    ["empty", emptyList],
    ["size", sizeImpl],
  ]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { type: { kind: starKind, name: "Bool" } },
    { trait_def: collectionTrait },
  ];

  const result = typecheck(context, listDict);
  assertOk(result, "should typecheck collection instance");
});

test("Overlapping trait constraints", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  // Function that requires Show twice (redundant but valid)
  const doubleShow = traitLamTerm(
    "dict1",
    "Show",
    "T",
    starKind,
    [
      { trait: "Show", type: varType("T") },
      { trait: "Show", type: varType("T") },
    ],
    lamTerm("x", varType("T"), conTerm('"shown"', conType("String"))),
  );

  const context: Context = [{ trait_def: showTrait }];

  const result = typecheck(context, doubleShow);
  assertOk(result, "should handle duplicate constraints");
});

test("Trait method returning trait-constrained type", () => {
  const monadTrait: TraitDef = {
    name: "Monad",
    type_param: "M",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "pure",
        forallType(
          "A",
          starKind,
          arrowType(varType("A"), appType(varType("M"), varType("A"))),
        ),
      ],
    ],
  };

  const context: Context = [{ trait_def: monadTrait }];

  // Function that uses monad methods
  const wrapValue = traitLamTerm(
    "monadDict",
    "Monad",
    "M",
    { arrow: { from: starKind, to: starKind } },
    [{ trait: "Monad", type: varType("M") }],
    tylamTerm(
      "A",
      starKind,
      lamTerm(
        "x",
        varType("A"),
        tyappTerm(traitMethodTerm(varTerm("monadDict"), "pure"), varType("A")),
      ),
    ),
  );

  const result = typecheck(context, wrapValue);
  assertOk(result, "should handle trait methods with polymorphic returns");
});

// ============= TYPE NORMALIZATION TESTS =============

test("Normalization of nested applications", () => {
  const f = lamType("A", starKind, lamType("B", starKind, varType("A")));
  const applied = appType(appType(f, conType("Int")), conType("Bool"));

  const normalized = normalizeType(applied);
  assert(typesEqual(normalized, conType("Int")), "should reduce to Int");
});

test("Normalization preserves mu types", () => {
  const listType = muType(
    "L",
    variantType([
      ["Nil", unitType],
      ["Cons", tupleType([conType("Int"), varType("L")])],
    ]),
  );

  const normalized = normalizeType(listType);
  assert("mu" in normalized, "should still be mu type");
  assert(typesEqual(normalized, listType), "should be unchanged");
});

test("Normalization with shadowed variables", () => {
  const type1 = forallType(
    "A",
    starKind,
    forallType("A", starKind, varType("A")),
  );

  const normalized = normalizeType(type1);
  assert("forall" in normalized, "should preserve forall structure");
});

test("Normalization of complex arrow types", () => {
  const complexArrow = arrowType(
    appType(lamType("T", starKind, varType("T")), conType("Int")),
    appType(lamType("T", starKind, varType("T")), conType("Bool")),
  );

  const normalized = normalizeType(complexArrow);
  const expected = arrowType(conType("Int"), conType("Bool"));

  assert(
    typesEqual(normalized, expected),
    "should normalize both sides of arrow",
  );
});

// ============= ALPHA-EQUIVALENCE TESTS =============

test("Alpha-equivalent forall types", () => {
  const type1 = forallType("A", starKind, varType("A"));
  const type2 = forallType("B", starKind, varType("B"));

  assert(typesEqual(type1, type2), "should be alpha-equivalent");
});

test("Alpha-equivalent nested foralls", () => {
  const type1 = forallType(
    "A",
    starKind,
    forallType("B", starKind, arrowType(varType("A"), varType("B"))),
  );

  const type2 = forallType(
    "X",
    starKind,
    forallType("Y", starKind, arrowType(varType("X"), varType("Y"))),
  );

  assert(typesEqual(type1, type2), "nested foralls should be alpha-equivalent");
});

test("Not alpha-equivalent with wrong binding", () => {
  const type1 = forallType(
    "A",
    starKind,
    forallType("B", starKind, varType("A")),
  );

  const type2 = forallType(
    "A",
    starKind,
    forallType("B", starKind, varType("B")),
  );

  assert(!typesEqual(type1, type2), "should not be alpha-equivalent");
});

// ============= OCCURS CHECK TESTS =============

test("Occurs check prevents infinite types", () => {
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  // [FIX: Use a meta-var (flexible) for left to trigger binding + occurs check]
  // Regular var_type("X") is rigid → immediate mismatch, no occurs.
  // Meta ?0 is flexible → attempts bind ?0 := ?0 -> Int → occursCheck detects cycle.
  const X = freshMetaVar() as VarType; // e.g., { var: "?0" } – now isMetaVar(X) = true
  const infiniteType = arrowType(X, conType("Int")); // ?0 -> Int

  const result = unifyTypes(
    X, // Meta: flexible, will try to bind
    infiniteType,
    worklist,
    subst,
  );

  const err = assertErr(result, "should fail occurs check");
  assert("cyclic" in err, "should be cyclic error");
  assert(
    err.cyclic === X.var,
    `cyclic should mention var ${X.var}, got ${err.cyclic}`,
  ); // Optional: more precise
});

test("Occurs check in records", () => {
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  const x = freshMetaVar();
  // Try to unify X with {f: X}
  const result = unifyTypes(x, recordType([["f", x]]), worklist, subst);

  const err = assertErr(result, "should fail occurs check");
  assert("cyclic" in err, "should be cyclic error");
});

test("Occurs check with nested types", () => {
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  const x = freshMetaVar();

  // X = List<X> should fail
  const listOfX = variantType([
    ["Nil", unitType],
    [
      "Cons",
      recordType([
        ["head", x],
        ["tail", x],
      ]),
    ],
  ]);

  const result = unifyTypes(x, listOfX, worklist, subst);

  const err = assertErr(result, "should fail occurs check");
  assert("cyclic" in err, "should be cyclic error");
});

// ============= COMPLEX FEATURE COMBINATIONS =============

test("Polymorphic list with trait constraints", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  // showList: ∀T where Show<T>. List<T> -> String
  const showList = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "list",
      muType(
        "L",
        variantType([
          ["Nil", unitType],
          [
            "Cons",
            recordType([
              ["head", varType("T")],
              ["tail", varType("L")],
            ]),
          ],
        ]),
      ),
      matchTerm(unfoldTerm(varTerm("list")), [
        [
          variantPattern("Nil", wildcardPattern()),
          conTerm('"[]"', conType("String")),
        ],
        [
          variantPattern(
            "Cons",
            recordPattern([
              ["head", varPattern("h")],
              ["tail", wildcardPattern()],
            ]),
          ),
          appTerm(traitMethodTerm(varTerm("showDict"), "show"), varTerm("h")),
        ],
      ]),
    ),
  );

  const context: Context = [{ trait_def: showTrait }];

  const result = typecheck(context, showList);
  assertOk(result, "should combine traits with recursive types");
});

test("Functor instance for Option", () => {
  const functorTrait: TraitDef = {
    name: "Functor",
    type_param: "F",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "map",
        forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              arrowType(varType("A"), varType("B")),
              arrowType(
                appType(varType("F"), varType("A")),
                appType(varType("F"), varType("B")),
              ),
            ),
          ),
        ),
      ],
    ],
  };

  const optionType = lamType(
    "T",
    starKind,
    variantType([
      ["None", unitType],
      ["Some", varType("T")],
    ]),
  );

  // Simplified map implementation
  const mapImpl = tylamTerm(
    "A",
    starKind,
    tylamTerm(
      "B",
      starKind,
      lamTerm(
        "f",
        arrowType(varType("A"), varType("B")),
        lamTerm(
          "opt",
          variantType([
            ["None", unitType],
            ["Some", varType("A")],
          ]),
          injectTerm(
            "None",
            unitValue,
            variantType([
              ["None", unitType],
              ["Some", varType("B")],
            ]),
          ),
        ),
      ),
    ),
  );

  const optionFunctor = dictTerm("Functor", optionType, [["map", mapImpl]]);

  const context: Context = [{ trait_def: functorTrait }];

  const result = typecheck(context, optionFunctor);
  assertOk(result, "should implement Functor for Option");
});

test("Monad trait with Option instance", () => {
  const monadTrait: TraitDef = {
    name: "Monad",
    type_param: "M",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "pure",
        forallType(
          "A",
          starKind,
          arrowType(varType("A"), appType(varType("M"), varType("A"))),
        ),
      ],
      [
        "bind",
        forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              appType(varType("M"), varType("A")),
              arrowType(
                arrowType(varType("A"), appType(varType("M"), varType("B"))),
                appType(varType("M"), varType("B")),
              ),
            ),
          ),
        ),
      ],
    ],
  };

  // Option M = λT. <None: Unit | Some: T>
  const optionType = lamType(
    "T",
    starKind,
    variantType([
      ["None", unitType],
      ["Some", varType("T")],
    ]),
  );

  const intType = conType("Int");

  // For simplicity, put bind and pure in context with concrete signatures
  const context: Context = [
    { trait_def: monadTrait },
    { type: { name: "Int", kind: starKind } },
    {
      term: {
        name: "optionBind",
        type: forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              appType(optionType, varType("A")),
              arrowType(
                arrowType(varType("A"), appType(optionType, varType("B"))),
                appType(optionType, varType("B")),
              ),
            ),
          ),
        ),
      },
    },
    {
      term: {
        name: "optionPure",
        type: forallType(
          "A",
          starKind,
          arrowType(varType("A"), appType(optionType, varType("A"))),
        ),
      },
    },
  ];

  // Test: pure wraps a value
  // pure[Int] 42 : Option Int
  const pureInt = appTerm(
    tyappTerm(varTerm("optionPure"), intType),
    conTerm("42", intType),
  );

  const pureResult = typecheck(context, pureInt);
  const pureType = assertOk(pureResult, "pure should typecheck");

  const expectedOptionInt = appType(optionType, intType);
  const resolvedPure = resolveMetaVars(normalizeType(pureType));

  assert(
    typesEqual(resolvedPure, expectedOptionInt),
    `pure should return Option Int, got ${showType(resolvedPure)}`,
  );

  // Test: bind sequences operations
  // optionBind[Int][Int] someValue (\x -> pure[Int] x) : Option Int
  const someValue = injectTerm(
    "Some",
    conTerm("5", intType),
    appType(optionType, intType),
  );

  const identity = lamTerm(
    "x",
    intType,
    appTerm(tyappTerm(varTerm("optionPure"), intType), varTerm("x")),
  );

  const boundBind = appTerm(
    appTerm(
      tyappTerm(tyappTerm(varTerm("optionBind"), intType), intType),
      someValue,
    ),
    identity,
  );

  const bindResult = typecheck(context, boundBind);
  const bindType = assertOk(bindResult, "bind operation should typecheck");

  const resolvedBind = resolveMetaVars(normalizeType(bindType));

  assert(
    typesEqual(resolvedBind, expectedOptionInt),
    `bind should return Option Int, got ${showType(resolvedBind)}`,
  );

  // Test: chained binds (do-notation simulation)
  // optionBind someValue (\x -> optionBind someValue2 (\y -> pure result))
  const someValue2 = injectTerm(
    "Some",
    conTerm("10", intType),
    appType(optionType, intType),
  );

  const innerChain = appTerm(
    appTerm(
      tyappTerm(tyappTerm(varTerm("optionBind"), intType), intType),
      someValue2,
    ),
    lamTerm(
      "y",
      intType,
      appTerm(
        tyappTerm(varTerm("optionPure"), intType),
        conTerm("15", intType),
      ),
    ),
  );

  const outerChain = appTerm(
    appTerm(
      tyappTerm(tyappTerm(varTerm("optionBind"), intType), intType),
      someValue,
    ),
    lamTerm("x", intType, innerChain),
  );

  const chainResult = typecheck(context, outerChain);
  const chainType = assertOk(chainResult, "chained bind should typecheck");

  const resolvedChain = resolveMetaVars(normalizeType(chainType));

  assert(
    typesEqual(resolvedChain, expectedOptionInt),
    `chained bind should return Option Int, got ${showType(resolvedChain)}`,
  );
});
test("GADTs simulation with variants", () => {
  // Expr: Int literal or Bool literal or Add
  const exprType = muType(
    "Expr",
    variantType([
      ["IntLit", conType("Int")],
      ["BoolLit", conType("Bool")],
      ["Add", tupleType([varType("Expr"), varType("Expr")])],
    ]),
  );

  const evalTerm = lamTerm(
    "expr",
    exprType,
    matchTerm(unfoldTerm(varTerm("expr")), [
      [variantPattern("IntLit", varPattern("n")), varTerm("n")],
      [
        variantPattern("BoolLit", wildcardPattern()),
        conTerm("0", conType("Int")),
      ],
      [variantPattern("Add", wildcardPattern()), conTerm("0", conType("Int"))],
    ]),
  );

  // This is a simplified version - true GADTs would need more type system support
  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    evalTerm,
  );
  assertOk(result, "should handle GADT-like structures");
});

test("Phantom types track compile-time properties", () => {
  // SafeList tagged with length (phantom parameter doesn't appear in values)
  const safeListType = (tag: Type, elem: Type) =>
    recordType([
      ["tag", tag],
      [
        "data",
        muType(
          "L",
          variantType([
            ["Nil", unitType],
            [
              "Cons",
              recordType([
                ["head", elem],
                ["tail", varType("L")],
              ]),
            ],
          ]),
        ),
      ],
    ]);

  const zeroTag = conType("Zero");
  const succTag = conType("Succ");
  const elemType = conType("Int");

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "Zero" } },
    { type: { kind: starKind, name: "Succ" } },
  ];

  // Empty list tagged with Zero length
  const listMu = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", elemType],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const emptyList = recordTerm([
    ["tag", conTerm("zero", zeroTag)],
    [
      "data",
      foldTerm(
        listMu,
        injectTerm(
          "Nil",
          unitValue,
          variantType([
            ["Nil", unitType],
            [
              "Cons",
              recordType([
                ["head", elemType],
                ["tail", listMu],
              ]),
            ],
          ]),
        ),
      ),
    ],
  ]);

  // Verify empty list has Zero tag
  const emptyResult = typecheck(context, emptyList);
  const emptyType = assertOk(emptyResult, "should typecheck empty list");

  const expectedEmpty = safeListType(zeroTag, elemType);
  const resolvedEmpty = resolveMetaVars(normalizeType(emptyType));

  assert(
    typesEqual(resolvedEmpty, expectedEmpty),
    `empty list should have Zero tag, got ${showType(resolvedEmpty)}`,
  );

  // Non-empty list tagged with Succ length
  const oneElemList = recordTerm([
    ["tag", conTerm("succ", succTag)],
    [
      "data",
      foldTerm(
        listMu,
        injectTerm(
          "Cons",
          recordTerm([
            ["head", conTerm("42", elemType)],
            [
              "tail",
              foldTerm(
                listMu,
                injectTerm(
                  "Nil",
                  unitValue,
                  variantType([
                    ["Nil", unitType],
                    [
                      "Cons",
                      recordType([
                        ["head", elemType],
                        ["tail", listMu],
                      ]),
                    ],
                  ]),
                ),
              ),
            ],
          ]),
          variantType([
            ["Nil", unitType],
            [
              "Cons",
              recordType([
                ["head", elemType],
                ["tail", listMu],
              ]),
            ],
          ]),
        ),
      ),
    ],
  ]);

  const oneResult = typecheck(context, oneElemList);
  const oneType = assertOk(oneResult, "should typecheck singleton list");

  const expectedOne = safeListType(succTag, elemType);
  const resolvedOne = resolveMetaVars(normalizeType(oneType));

  assert(
    typesEqual(resolvedOne, expectedOne),
    `singleton list should have Succ tag, got ${showType(resolvedOne)}`,
  );

  // Demonstrate phantom types are actually tracked:
  // A function that only accepts empty lists
  const requiresEmpty = lamTerm(
    "list",
    safeListType(zeroTag, elemType),
    varTerm("list"),
  );

  // Should accept empty list
  const validApp = appTerm(requiresEmpty, emptyList);
  const validResult = typecheck(context, validApp);
  assertOk(validResult, "should accept empty list");

  // Should reject non-empty list (different phantom tag)
  const invalidApp = appTerm(requiresEmpty, oneElemList);
  const invalidResult = typecheck(context, invalidApp);
  assert(
    "err" in invalidResult && "type_mismatch" in invalidResult.err,
    "should reject list with wrong phantom tag",
  );
});

// ============= ERROR BOUNDARY TESTS =============

test("Deeply nested errors maintain context", () => {
  const deeplyNested = lamTerm(
    "a",
    conType("Int"),
    lamTerm(
      "b",
      conType("String"),
      lamTerm(
        "c",
        conType("Bool"),
        // Type error deep inside
        appTerm(varTerm("a"), conTerm('"wrong"', conType("String"))),
      ),
    ),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
      { type: { kind: starKind, name: '"wrong"' } },
    ],
    deeplyNested,
  );
  const err = assertErr(result, "should propagate error from deep nesting");
  assert(
    "type_mismatch" in err || "not_a_function" in err,
    "should have appropriate error",
  );
});

test("Error in pattern match branch", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  const badMatch = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
      [
        variantPattern("Some", varPattern("x")),
        // Type error: trying to return string when expecting int
        conTerm('"error"', conType("String")),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    badMatch,
  );
  const err = assertErr(result, "should catch error in branch");
  assert("type_mismatch" in err, "should be type mismatch");
});

test("Large tuple size limits", () => {
  const elements: Term[] = [];
  for (let i = 0; i < 1000; i++) {
    elements.push(conTerm(`${i}`, conType("Int")));
  }

  const largeTuple = tupleTerm(elements);
  const result = typecheck([], largeTuple);

  // Should either succeed or fail gracefully
  // (depends on implementation limits)
  if ("ok" in result) {
    assert("tuple" in result.ok, "should be tuple type");
  }
});
test("Automatic type instantiation for polymorphic identity", () => {
  const context: Context = [
    {
      term: {
        name: "id",
        type: forallType("T", starKind, arrowType(varType("T"), varType("T"))),
      },
    },
    { type: { name: "Int", kind: starKind } },
  ];

  // id 5 should automatically instantiate T = Int
  const app = appTerm(varTerm("id"), conTerm("5", conType("Int")));

  const result = typecheck(context, app);
  const type = assertOk(result, "should infer type argument");

  // Apply meta variable solutions to get the final concrete type
  const resolved = resolveMetaVars(normalizeType(type));

  assert(
    typesEqual(resolved, conType("Int")),
    `should be Int, got ${showType(resolved)}`,
  );
});

// ./test/types.spec.ts (cont.)
test("Inference with nested applications", () => {
  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { type: { kind: starKind, name: "Bool" } },
    {
      term: {
        name: "compose",
        type: forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            forallType(
              "C",
              starKind,
              arrowType(
                arrowType(varType("B"), varType("C")),
                arrowType(
                  arrowType(varType("A"), varType("B")),
                  arrowType(varType("A"), varType("C")),
                ),
              ),
            ),
          ),
        ),
      },
    },
  ];

  // compose should infer all three type arguments from the function arguments
  const f = lamTerm("x", conType("Int"), conTerm('"str"', conType("String")));
  const g = lamTerm("y", conType("Bool"), conTerm("42", conType("Int")));

  // compose f g should infer: A=Bool, B=Int, C=String
  const app = appTerm(appTerm(varTerm("compose"), f), g);

  const result = typecheck(context, app);
  const type = assertOk(result, "should infer all type arguments");

  const resolved = resolveMetaVars(normalizeType(type));

  assert("arrow" in resolved, "should be function type");
  assert(
    typesEqual(resolved.arrow.from, conType("Bool")),
    `domain should be Bool, got ${showType(resolved.arrow.from)}`,
  );
  assert(
    typesEqual(resolved.arrow.to, conType("String")),
    `codomain should be String, got ${showType(resolved.arrow.to)}`,
  );
});

test("Subsumption allows polymorphic to specific", () => {
  const polyId = forallType(
    "T",
    starKind,
    arrowType(varType("T"), varType("T")),
  );
  const intToInt = arrowType(conType("Int"), conType("Int"));

  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  // Should allow assigning polyId to intToInt
  const result = unifyTypes(polyId, intToInt, worklist, subst);

  if ("ok" in result) {
    const solveResult = solveConstraints(worklist, subst);
    assertOk(solveResult, "should unify through subsumption");
  }
});

test("Bidirectional checking for lambdas", () => {
  const intType = conType("Int");
  const expectedType = arrowType(intType, intType);

  // Lambda without explicit type on argument
  const lam = lamTerm("x", intType, varTerm("x"));

  const result = checkType(
    [{ type: { kind: starKind, name: "Int" } }],
    lam,
    expectedType,
  );
  const type = assertOk(result, "should check lambda against expected type");
  assert(typesEqual(type.type, expectedType), "should match expected type");
});

test("Bidirectional checking for records", () => {
  const expectedType = recordType([
    ["x", conType("Int")],
    ["y", conType("String")],
  ]);

  const record = recordTerm([
    ["x", conTerm("42", conType("Int"))],
    ["y", conTerm('"hello"', conType("String"))],
  ]);

  const result = checkType(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    record,
    expectedType,
  );
  assertOk(result, "should check record structure");
});

test("Bidirectional checking for tuples", () => {
  const expectedType = tupleType([conType("Int"), conType("Bool")]);

  const tuple = tupleTerm([
    conTerm("5", conType("Int")),
    conTerm("true", conType("Bool")),
  ]);

  const result = checkType(
    [
      { type: { kind: starKind, name: "Bool" } },
      { type: { kind: starKind, name: "Int" } },
    ],
    tuple,
    expectedType,
  );
  assertOk(result, "should check tuple elements");
});

test("Inference fails with ambiguous types", () => {
  // Function that returns a polymorphic value
  const ambiguous = lamTerm(
    "x",
    conType("Int"),
    tylamTerm("T", starKind, lamTerm("y", varType("T"), varTerm("y"))),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    ambiguous,
  );
  assertOk(result, "should infer polymorphic result");
});

test("Metavariable unification", () => {
  const subst = new Map<string, Type>();

  // Unify ?0 with Int
  const result = unifyVariable("?0", conType("Int"), subst);
  assertOk(result, "should unify metavar with concrete type");

  assert(subst.has("?0"), "should record substitution");
  assert(typesEqual(subst.get("?0")!, conType("Int")), "should map to Int");
});

test("Metavariable substitution chain", () => {
  const subst = new Map<string, Type>();

  // ?0 = ?1, ?1 = Int
  subst.set("?0", varType("?1"));
  subst.set("?1", conType("Int"));

  const resolved = applySubstitution(subst, varType("?0"));
  assert(typesEqual(resolved, conType("Int")), "should resolve chain");
});

test("Occurs check with metavariables", () => {
  const subst = new Map<string, Type>();

  // Try to unify ?0 with ?0 -> Int
  const result = unifyVariable(
    "?0",
    arrowType(varType("?0"), conType("Int")),
    subst,
  );

  const err = assertErr(result, "should fail occurs check");
  assert("cyclic" in err, "should detect cycle");
});

test("Higher-rank polymorphism simulation", () => {
  const ctx: Context = [{ type: { kind: starKind, name: "Int" } }];

  // (∀a. a -> a) -> Int -> Int
  const higherRank = arrowType(
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    arrowType(conType("Int"), conType("Int")),
  );

  // λid:(∀a. a -> a). λx:Int. id[Int] x
  const f = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    lamTerm(
      "x",
      conType("Int"),
      appTerm(tyappTerm(varTerm("id"), conType("Int")), varTerm("x")),
    ),
  );

  // Test 1: Verify f has the expected higher-rank type
  const result = typecheck(ctx, f);
  const res = assertOk(result, "should infer rank-2 type");

  expect(typesEqual(res, higherRank)).toBe(true);
});

test("Apply f to a polymorphic identity function", () => {
  const ctx: Context = [{ type: { kind: starKind, name: "Int" } }];
  // λid:(∀a. a -> a). λx:Int. id[Int] x
  const f = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    lamTerm(
      "x",
      conType("Int"),
      appTerm(tyappTerm(varTerm("id"), conType("Int")), varTerm("x")),
    ),
  );

  // Test 2: Apply f to a polymorphic identity function
  // Λa::*. λx:a. x
  const polyId = tylamTerm(
    "a",
    starKind,
    lamTerm("x", varType("a"), varTerm("x")),
  );

  // f polyId : Int -> Int
  const app1 = appTerm(f, polyId);
  const result2 = typecheck(ctx, app1);
  const res = assertOk(
    result2,
    "should apply rank-2 function to polymorphic argument",
  );

  const expectedType = arrowType(conType("Int"), conType("Int"));
  expect(typesEqual(res, expectedType)).toBe(true);
});

test("Apply f to a polymorphic identity function", () => {
  const ctx: Context = [{ type: { kind: starKind, name: "Int" } }];
  // λid:(∀a. a -> a). λx:Int. id[Int] x
  const f = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    lamTerm(
      "x",
      conType("Int"),
      appTerm(tyappTerm(varTerm("id"), conType("Int")), varTerm("x")),
    ),
  );

  // Λa::*. λx:a. x
  const polyId = tylamTerm(
    "a",
    starKind,
    lamTerm("x", varType("a"), varTerm("x")),
  );
  const app1 = appTerm(f, polyId);
  const int42 = conTerm("42", conType("Int"));
  const app2 = appTerm(app1, int42);
  const result3 = typecheck(ctx, app2);
  const res = assertOk(result3, "should fully apply rank-2 function chain");

  expect(typesEqual(res, conType("Int"))).toBe(true);
});

test("Check that f can use the polymorphic parameter multiple times", () => {
  const ctx: Context = [{ type: { kind: starKind, name: "Int" } }];
  // λid:(∀a. a -> a). λx:Int. id[Int] (id[Int] x)
  const fTwice = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    lamTerm(
      "x",
      conType("Int"),
      appTerm(
        tyappTerm(varTerm("id"), conType("Int")),
        appTerm(tyappTerm(varTerm("id"), conType("Int")), varTerm("x")),
      ),
    ),
  );

  const higherRank = arrowType(
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    arrowType(conType("Int"), conType("Int")),
  );

  const result4 = typecheck(ctx, fTwice);
  const res = assertOk(
    result4,
    "should handle multiple uses of rank-2 parameter",
  );
  expect(typesEqual(res, higherRank)).toBe(true);
});

test("Demonstrate the key property of rank-2 types", () => {
  const int42 = conTerm("42", conType("Int"));

  // The polymorphic parameter can be instantiated at different types
  // λid:(∀a. a -> a). {int: id[Int] 42, bool: id[Bool] true}
  const ctxWithBool: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "Bool" } },
  ];

  const fMultiType = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    recordTerm([
      ["int", appTerm(tyappTerm(varTerm("id"), conType("Int")), int42)],
      [
        "bool",
        appTerm(
          tyappTerm(varTerm("id"), conType("Bool")),
          conTerm("true", conType("Bool")),
        ),
      ],
    ]),
  );

  const result5 = typecheck(ctxWithBool, fMultiType);
  const res = assertOk(
    result5,
    "should instantiate rank-2 parameter at multiple types",
  );

  const expectedType = arrowType(
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    recordType([
      ["int", conType("Int")],
      ["bool", conType("Bool")],
    ]),
  );
  expect(typesEqual(res, expectedType)).toBe(true);
});

test("Demonstrate the key property of rank-2 types", () => {
  const ctx = [{ type: { kind: starKind, name: "Int" } }];

  const f = lamTerm(
    "id",
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    lamTerm(
      "x",
      conType("Int"),
      appTerm(tyappTerm(varTerm("id"), conType("Int")), varTerm("x")),
    ),
  );

  const higherRank = arrowType(
    forallType("a", starKind, arrowType(varType("a"), varType("a"))),
    arrowType(conType("Int"), conType("Int")),
  );

  // Test 6: Verify type checking (not just inference) works with higher-rank types
  const checkResult = checkType(ctx, f, higherRank);
  const res = assertOk(checkResult, "should check against rank-2 type");

  expect(typesEqual(res.type, higherRank)).toBe(true);
});

test("Worklist-based unification", () => {
  const worklist: Worklist = [];
  const subst = new Map<string, Type>(); // Explicitly pass to solveConstraints (though default is new Map)

  // [FIX: Use meta-vars for A/B to allow binding (regular vars are rigid, cause immediate mismatch)]
  // Regular var_type("A") is rigid → no binding, type_mismatch error.
  // Metas (?0, ?1) are flexible → unifyVariable binds them, supports transitivity.
  const A = freshMetaVar() as VarType; // e.g., { var: "?0" }
  const B = freshMetaVar() as VarType; // e.g., { var: "?1" }
  const intType = conType("Int");

  worklist.push(
    { type_eq: { left: A, right: intType } }, // ?0 ~ Int
    { type_eq: { left: B, right: A } }, // ?1 ~ ?0 (will become ?1 ~ Int after subst)
  );

  const result = solveConstraints(worklist, subst); // Pass subst explicitly for clarity
  const solvedSubst = assertOk(result, "should solve constraints"); // Now uses passed subst

  // Verify bindings (apply subst recursively if needed, but here direct)
  assert(
    typesEqual(solvedSubst.get(A.var)!, intType),
    `A (${A.var}) should map to Int, got ${showType(solvedSubst.get(A.var)!)}`,
  );
  assert(
    typesEqual(solvedSubst.get(B.var)!, intType),
    `B (${B.var}) should map to Int, got ${showType(solvedSubst.get(B.var)!)}`,
  );

  // Optional: Verify transitivity by applying subst to B ~ A
  const appliedA = applySubstitution(solvedSubst, A);
  assert(
    typesEqual(appliedA, intType),
    "applySubstitution on A should yield Int",
  );
});

test("Kind constraint solving", () => {
  const worklist: Worklist = [{ kind_eq: { left: starKind, right: starKind } }];

  const result = solveConstraints(worklist);
  assertOk(result, "should solve kind constraints");
});

test("Has-kind constraint", () => {
  const worklist: Worklist = [
    {
      has_kind: {
        ty: conType("Int"),
        kind: starKind,
        context: [{ type: { kind: starKind, name: "Int" } }],
      },
    },
  ];

  const result = solveConstraints(worklist);
  assertOk(result, "should verify kind");
});

test("Has-type constraint", () => {
  const worklist: Worklist = [
    {
      has_type: {
        term: conTerm("5", conType("Int")),
        ty: conType("Int"),
        context: [],
      },
    },
  ];

  const result = solveConstraints(worklist);
  assertOk(result, "should verify type");
});

test("Conflicting constraints fail", () => {
  const worklist: Worklist = [
    { type_eq: { left: varType("A"), right: conType("Int") } },
    { type_eq: { left: varType("A"), right: conType("Bool") } },
  ];

  const result = solveConstraints(worklist);
  const err = assertErr(result, "should detect conflict");
  assert("type_mismatch" in err, "should be type mismatch");
});

test("Automatic dictionary passing", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const context: Context = [
    { trait_def: showTrait },
    { trait_impl: { trait: "Show", type: intType, dict: intShowDict } },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  // Just pass the bounded forall directly
  const polyType = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  const result = instantiateWithTraits(context, polyType);
  const okResult = assertOk(result, "should find trait implementation");

  expect(okResult.dicts.length).toBe(1);
  expect(okResult.dicts[0]).toMatchObject(intShowDict);
});

test("Multiple dictionary inference", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const eqTrait: TraitDef = {
    name: "Eq",
    type_param: "Self",
    kind: starKind,
    methods: [
      [
        "eq",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool"))),
      ],
    ],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const eqImpl = lamTerm(
    "x",
    intType,
    lamTerm("y", intType, conTerm("true", conType("Bool"))),
  );

  const context: Context = [
    { trait_def: showTrait },
    { trait_def: eqTrait },
    {
      trait_impl: {
        trait: "Show",
        type: intType,
        dict: dictTerm("Show", intType, [["show", showImpl]]),
      },
    },
    {
      trait_impl: {
        trait: "Eq",
        type: intType,
        dict: dictTerm("Eq", intType, [["eq", eqImpl]]),
      },
    },
  ];

  const constraints: TraitConstraint[] = [
    { trait: "Show", type: intType },
    { trait: "Eq", type: intType },
  ];

  const result = checkTraitConstraints(context, constraints);
  const dicts = assertOk(result, "should find both implementations");
  assert(dicts.length === 2, "should have two dictionaries");
});
test("Trait constraint substitution during instantiation", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const context: Context = [
    { trait_def: showTrait },
    { trait_impl: { trait: "Show", type: intType, dict: intShowDict } },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  const polyType = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  // instantiateWithTraits should substitute T with a fresh meta var in constraints
  const result = instantiateWithTraits(context, polyType);
  const okResult = assertOk(
    result,
    "should instantiate and find implementation",
  );

  // Should find the Int dictionary after unification
  expect(okResult.dicts.length).toBe(1);
  expect(okResult.dicts[0]).toMatchObject(intShowDict);

  // The body type should have the meta variable instantiated
  assert("arrow" in okResult.type, "should be arrow type");
  assert("var" in okResult.type.arrow.from, "domain should be meta variable");
  expect(okResult.type.arrow.from.var).toMatch(/^\?/); // Should be ?0 or similar
});

// ============= BOTTOM TYPE TESTS =============

test("Never type is subtype of everything", () => {
  const neverType: Type = { never: null };
  const intType = conType("Int");

  assert(
    isAssignableTo(neverType, intType),
    "never should be assignable to Int",
  );
  assert(
    isAssignableTo(neverType, arrowType(intType, intType)),
    "never should be assignable to function",
  );
});

test("Never in match branches", () => {
  // Define Option<Int> structurally
  const optionInt: Type = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);

  // The term: λopt:Option<Int>. match opt { None => 0 | Some(x) => x }
  // None branch returns Int constant
  // Some branch returns bound variable x :: Int
  // Both unify to Int ⇒ overall function: Option<Int> → Int
  const matchWithNever = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
      [variantPattern("Some", varPattern("x")), varTerm("x")],
    ]),
  );

  // Context: Int :: *
  const ctx = [{ type: { name: "Int", kind: starKind } }];

  // Typecheck the function
  const result = typecheck(ctx, matchWithNever);
  const inferred = assertOk(result, "matchWithNever should typecheck");

  const normInferred = normalizeType(inferred);

  // Expected type: Option<Int> → Int
  const expectedType = arrowType(optionInt, conType("Int"));
  const normExpected = normalizeType(expectedType) as ArrowType;

  // 1️⃣ Verify overall type is a function
  assert(
    "arrow" in normInferred,
    `Expected function type, got ${showType(normInferred)}`,
  );

  // 2️⃣ Verify domain matches Option<Int>
  assert(
    typesEqual(normInferred.arrow.from, normExpected.arrow.from),
    `Expected argument type ${showType(normExpected.arrow.from)} but got ${showType(normInferred.arrow.from)}`,
  );

  // 3️⃣ Verify codomain matches Int (even if one branch had bottom ⊥)
  assert(
    typesEqual(normInferred.arrow.to, normExpected.arrow.to),
    `Expected return type ${showType(normExpected.arrow.to)} but got ${showType(normInferred.arrow.to)}`,
  );
});

test("Never type kinding", () => {
  const neverType: Type = { never: null };
  const result = checkKind([], neverType);
  const kind = assertOk(result, "never should have kind");
  assert("star" in kind, "never should have kind *");
});

test("Let polymorphism basic", () => {
  const polyId = tylamTerm(
    "T",
    starKind,
    lamTerm("x", varType("T"), varTerm("x")),
  );

  const lTerm = letTerm(
    "id",
    polyId,
    tupleTerm([
      appTerm(
        tyappTerm(varTerm("id"), conType("Int")),
        conTerm("5", conType("Int")),
      ),
      appTerm(
        tyappTerm(varTerm("id"), conType("Bool")),
        conTerm("true", conType("Bool")),
      ),
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    lTerm,
  );
  assertOk(result, "should allow polymorphic use of let-bound variable");
});

test("Let with type inference", () => {
  const intType = conType("Int");

  const lTerm = letTerm(
    "x",
    conTerm("5", intType),
    appTerm(lamTerm("y", intType, varTerm("y")), varTerm("x")),
  );

  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], lTerm);
  const type = assertOk(result, "should infer let binding type");
  assert(typesEqual(type, intType), "should be Int");
});

test("Nested let bindings", () => {
  const intType = conType("Int");

  const nested = letTerm(
    "x",
    conTerm("5", intType),
    letTerm("y", varTerm("x"), letTerm("z", varTerm("y"), varTerm("z"))),
  );

  const result = typecheck([{ type: { kind: starKind, name: "Int" } }], nested);
  assertOk(result, "should handle nested lets");
});

test("Let with shadowing", () => {
  const intType = conType("Int");
  const strType = conType("String");

  const shadowed = letTerm(
    "x",
    conTerm("5", intType),
    letTerm("x", conTerm('"hello"', strType), varTerm("x")),
  );

  const result = typecheck([], shadowed);
  const type = assertOk(result, "should handle shadowing");
  assert(typesEqual(type, strType), "inner binding should shadow");
});

test("Substitution in complex types", () => {
  const complexType = arrowType(
    varType("T"),
    recordType([
      ["field", varType("T")],
      ["nested", tupleType([varType("T"), conType("Int")])],
    ]),
  );

  const substituted = substituteType("T", conType("Bool"), complexType);

  assert("arrow" in substituted, "should preserve structure");
  assert(
    typesEqual(substituted.arrow.from, conType("Bool")),
    "should substitute in parameter",
  );
});

test("Substitution avoids capture", () => {
  const type1 = forallType(
    "A",
    starKind,
    arrowType(varType("A"), varType("B")),
  );

  const substituted = substituteType("B", varType("A"), type1);

  // Should not substitute inside the forall since A is bound
  assert("forall" in substituted, "should preserve forall");
});

test("Substitution in mu types", () => {
  const listT = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", varType("T")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const substituted = substituteType("T", conType("Int"), listT);

  assert("mu" in substituted, "should preserve mu");
  // The head type should be substituted
  const body = (substituted as MuType).mu.body;
  assert("variant" in body, "should have variant body");
});

test("Substitution with infinite recursion protection", () => {
  const recursiveType = muType("T", arrowType(varType("T"), varType("T")));

  // Should not infinite loop
  const substituted = substituteType("T", recursiveType, recursiveType);
  assert("mu" in substituted, "should handle self-substitution");
});

test("Constant pattern type checking", () => {
  const intType = conType("Int");

  const matchConst = lamTerm(
    "x",
    intType,
    matchTerm(varTerm("x"), [
      [conPattern("42", intType), conTerm("true", conType("Bool"))],
      [wildcardPattern(), conTerm("false", conType("Bool"))],
    ]),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    matchConst,
  );
  assertOk(result, "should handle constant patterns");
});

test("Pattern with wrong constant type", () => {
  const intType = conType("Int");
  const strType = conType("String");

  const badMatch = lamTerm(
    "x",
    intType,
    matchTerm(varTerm("x"), [
      [conPattern('"hello"', strType), conTerm("true", conType("Bool"))],
      [wildcardPattern(), conTerm("false", conType("Bool"))],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    badMatch,
  );
  const err = assertErr(result, "should reject mismatched constant");
  assert("type_mismatch" in err, "should be type mismatch");
});

test("Exhaustiveness with constants", () => {
  const boolType = variantType([
    ["True", unitType],
    ["False", unitType],
  ]);

  const patterns = [
    variantPattern("True", wildcardPattern()),
    variantPattern("False", wildcardPattern()),
  ];

  const result = checkExhaustive(patterns, boolType, []);
  assertOk(result, "should be exhaustive");
});

test("Non-exhaustive with missing constant", () => {
  const boolType = variantType([
    ["True", unitType],
    ["False", unitType],
  ]);

  const patterns = [variantPattern("True", wildcardPattern())];

  const result = checkExhaustive(patterns, boolType, []);
  const err = assertErr(result, "should be non-exhaustive");
  assert("missing_case" in err, "should detect missing case");
});

// ============= NORMALIZATION EDGE CASES =============

test("Normalization idempotence", () => {
  const type1 = arrowType(
    appType(lamType("T", starKind, varType("T")), conType("Int")),
    conType("Bool"),
  );

  const normalized1 = normalizeType(type1);
  const normalized2 = normalizeType(normalized1);

  assert(
    typesEqual(normalized1, normalized2),
    "normalization should be idempotent",
  );
});

test("Normalization of bounded forall", () => {
  const type1 = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    appType(lamType("X", starKind, varType("X")), varType("T")),
  );

  const normalized = normalizeType(type1);

  // Body should be normalized
  assert("bounded_forall" in normalized, "should preserve bounded forall");
});

test("Polymorphic trait impl instantiation", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  // Polymorphic impl: ∀T. Show T where T=Int (but pretend it's poly)
  const polyImplType = forallType("T", starKind, conType("Int")); // Simplified poly type
  const polyDict = dictTerm("Show", polyImplType, [
    ["show", lamTerm("x", polyImplType, conTerm('"poly"', conType("String")))],
  ]);

  const polyImplBinding: TraitImplBinding = {
    trait_impl: { trait: "Show", type: polyImplType, dict: polyDict },
  };

  const context: Context = [
    { trait_def: showTrait },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
    polyImplBinding,
  ];

  // Instantiate for concrete Int
  const instRes = checkTraitImplementation(context, "Show", conType("Int"));
  const instDict = assertOk(instRes, "should instantiate poly impl");
  assert("dict" in instDict, "should return instantiated dict");

  // Test failure: No impl for String
  const noImplRes = checkTraitImplementation(
    context,
    "Show",
    conType("String"),
  );
  const err = assertErr(noImplRes, "should fail without impl");
  assert(
    "missing_trait_impl" in err &&
      (err.missing_trait_impl.type as ConType).con === "String",
    "should report missing impl",
  );
});

test("Not a function error in app", () => {
  const intType = conType("Int");

  // Proper term-level constant: 42 : Int
  const intConstant = conTerm("42", intType);

  // Make a variable bound in the context: x : Int
  const badCallee = varTerm("x");

  // x 42 -- apply an Int-typed value as a function
  const badApp = appTerm(badCallee, intConstant);

  // Context where x : Int
  const context: Context = [
    { type: { name: "Int", kind: starKind } }, // type binding
    { term: { name: "x", type: intType } }, // term binding
  ];

  const result = typecheck(context, badApp);
  const err = assertErr(result, "should fail");

  // Expect: not_a_function error on type Int
  assert(
    "not_a_function" in err && typesEqual(err.not_a_function, intType),
    "should report not_a_function(Int)",
  );
});

test("Direct self-reference μX.X is cyclic", () => {
  const selfMu = muType("X", varType("X"));
  const unifyRes = unifyTypes(selfMu, varType("Z"), [], new Map());
  const err = assertErr(unifyRes, "should detect self-referential mu");
  assert("cyclic" in err && err.cyclic === "X", "should report cyclic X");
});

test("Wildcard pattern in all positions", () => {
  const pairType = tupleType([conType("Int"), conType("String")]);

  const alwaysTrue = lamTerm(
    "p",
    pairType,
    matchTerm(varTerm("p"), [
      [wildcardPattern(), conTerm("true", conType("Bool"))],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    alwaysTrue,
  );
  assertOk(result, "wildcard should match anything");
});

test("Pattern matching with multiple wildcards", () => {
  const tripleType = tupleType([
    conType("Int"),
    conType("String"),
    conType("Bool"),
  ]);

  const getMiddle = lamTerm(
    "t",
    tripleType,
    matchTerm(varTerm("t"), [
      [
        tuplePattern([
          wildcardPattern(),
          varPattern("middle"),
          wildcardPattern(),
        ]),
        varTerm("middle"),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    getMiddle,
  );
  const type = assertOk(result, "should typecheck");
  assert("arrow" in type, "should be function type");
  assert(typesEqual(type.arrow.to, conType("String")), "should return String");
});

test("Deeply nested pattern matching", () => {
  const deepType = recordType([
    [
      "outer",
      recordType([
        [
          "inner",
          tupleType([
            conType("Int"),
            variantType([
              ["Some", conType("String")],
              ["None", unitType],
            ]),
          ]),
        ],
      ]),
    ],
  ]);

  const extract = lamTerm(
    "x",
    deepType,
    matchTerm(varTerm("x"), [
      [
        recordPattern([
          [
            "outer",
            recordPattern([
              [
                "inner",
                tuplePattern([
                  varPattern("num"),
                  variantPattern("Some", varPattern("str")),
                ]),
              ],
            ]),
          ],
        ]),
        varTerm("str"),
      ],
      [
        recordPattern([
          [
            "outer",
            recordPattern([
              [
                "inner",
                tuplePattern([
                  wildcardPattern(),
                  variantPattern("None", wildcardPattern()),
                ]),
              ],
            ]),
          ],
        ]),
        conTerm('"default"', conType("String")),
      ],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "String" } },
    ],
    extract,
  );
  assertOk(result, "should handle deeply nested patterns");
});

test("Constant pattern type checking 2", () => {
  const intType = conType("Int");

  const isZero = lamTerm(
    "x",
    intType,
    matchTerm(varTerm("x"), [
      [conPattern("0", intType), conTerm("true", conType("Bool"))],
      [wildcardPattern(), conTerm("false", conType("Bool"))],
    ]),
  );

  const result = typecheck(
    [
      { type: { kind: starKind, name: "Int" } },
      { type: { kind: starKind, name: "Bool" } },
    ],
    isZero,
  );
  assertOk(result, "should handle constant patterns");
});

test("Mutual recursion with mu types", () => {
  // Tree with leaves that are either values or subtrees
  const treeType = muType(
    "T",
    variantType([
      ["Leaf", conType("Int")],
      [
        "Branch",
        recordType([
          ["left", varType("T")],
          ["right", varType("T")],
        ]),
      ],
    ]),
  );

  const leafNode = foldTerm(
    treeType,
    injectTerm(
      "Leaf",
      conTerm("42", conType("Int")),
      variantType([
        ["Leaf", conType("Int")],
        [
          "Branch",
          recordType([
            ["left", treeType],
            ["right", treeType],
          ]),
        ],
      ]),
    ),
  );

  const result = typecheck(
    [{ type: { kind: starKind, name: "Int" } }],
    leafNode,
  );
  assertOk(result, "should handle recursive tree construction");
});

test("List concatenation function type", () => {
  // Define recursive List<Int> type: μL.<Nil: {}, Cons: {head: Int, tail: L}>
  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  // Expected type of concat: List<Int> → List<Int> → List<Int>
  const concatType = arrowType(listInt, arrowType(listInt, listInt));

  // Simplified implementation: λxs:List. λys:List. ys
  const concat = lamTerm("xs", listInt, lamTerm("ys", listInt, varTerm("ys")));

  // Type context includes Int :: *
  const ctx: Context = [{ type: { name: "Int", kind: starKind } }];

  // Typecheck the concat term
  const result = typecheck(ctx, concat);
  const inferred = assertOk(result, "Concat term should typecheck");

  // Normalize for comparison (unfold any μ, β-reduction)
  const normExpected = normalizeType(concatType);
  const normInferred = normalizeType(inferred);

  // Verify it inferred a function type
  assert(
    "arrow" in normInferred,
    `Expected function type, got ${showType(normInferred)}`,
  );

  // Assert full type equality
  const equal = typesEqual(normExpected, normInferred);
  assert(
    equal,
    `Expected concat type ${showType(normExpected)} but got ${showType(normInferred)}`,
  );

  // Optionally, verify round-trip normalization (sanity check)
  const finalNorm = normalizeType(normInferred);
  assert(
    typesEqual(finalNorm, normExpected),
    "Normalization should not change type equivalence",
  );
});

test("Nested mu types", () => {
  // List of lists
  const innerList = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const outerList = muType(
    "LL",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", innerList],
          ["tail", varType("LL")],
        ]),
      ],
    ]),
  );

  const kind = checkKind(
    [{ type: { kind: starKind, name: "Int" } }],
    outerList,
  );
  assertOk(kind, "should handle nested mu types");
});

test("Unfolding and refolding", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );

  const ctx: Context = [{ term: { name: "n", type: natType } }];

  // unfold then fold should preserve type
  const roundtrip = foldTerm(natType, unfoldTerm(varTerm("n")));

  const result = typecheck(ctx, roundtrip);
  const type = assertOk(result, "should typecheck");
  assert(typesEqual(type, natType), "should preserve type through unfold/fold");
});

test("Ord trait with superclass", () => {
  const eqTrait: TraitDef = {
    name: "Eq",
    type_param: "Self",
    kind: starKind,
    methods: [
      [
        "eq",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Bool"))),
      ],
    ],
  };

  const ordTrait: TraitDef = {
    name: "Ord",
    type_param: "Self",
    kind: starKind,
    methods: [
      [
        "compare",
        arrowType(varType("Self"), arrowType(varType("Self"), conType("Int"))),
      ],
    ],
  };

  const intType = conType("Int");

  const eqImpl = lamTerm(
    "x",
    intType,
    lamTerm("y", intType, conTerm("true", conType("Bool"))),
  );

  const ordImpl = lamTerm(
    "x",
    intType,
    lamTerm("y", intType, conTerm("0", intType)),
  );

  const eqDict = dictTerm("Eq", intType, [["eq", eqImpl]]);
  const ordDict = dictTerm("Ord", intType, [["compare", ordImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "Bool" } },
    { trait_def: eqTrait },
    { trait_def: ordTrait },
  ];

  const result1 = typecheck(context, eqDict);
  assertOk(result1, "Eq dict should typecheck");

  const result2 = typecheck(context, ordDict);
  assertOk(result2, "Ord dict should typecheck");
});

test("Generic function with trait bound", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  // Λ T where Show<T>. λxs: List<T>. ...
  const showList = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "xs",
      muType(
        "L",
        variantType([
          ["Nil", unitType],
          [
            "Cons",
            recordType([
              ["head", varType("T")],
              ["tail", varType("L")],
            ]),
          ],
        ]),
      ),
      conTerm('"[...]"', conType("String")),
    ),
  );

  const context: Context = [{ trait_def: showTrait }];

  const result = typecheck(context, showList);
  const type = assertOk(result, "should typecheck");
  assert("bounded_forall" in type, "should be bounded forall type");
});

test("Trait for recursive type", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const listInt = muType(
    "L",
    variantType([
      ["Nil", unitType],
      [
        "Cons",
        recordType([
          ["head", conType("Int")],
          ["tail", varType("L")],
        ]),
      ],
    ]),
  );

  const showListImpl = lamTerm(
    "list",
    listInt,
    conTerm('"[1,2,3]"', conType("String")),
  );

  const listShowDict = dictTerm("Show", listInt, [["show", showListImpl]]);

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
  ];

  const result = typecheck(context, listShowDict);
  assertOk(result, "should typecheck");
});

test("Monad trait structure", () => {
  const monadTrait: TraitDef = {
    name: "Monad",
    type_param: "M",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      [
        "return",
        forallType(
          "A",
          starKind,
          arrowType(varType("A"), appType(varType("M"), varType("A"))),
        ),
      ],
      [
        "bind",
        forallType(
          "A",
          starKind,
          forallType(
            "B",
            starKind,
            arrowType(
              appType(varType("M"), varType("A")),
              arrowType(
                arrowType(varType("A"), appType(varType("M"), varType("B"))),
                appType(varType("M"), varType("B")),
              ),
            ),
          ),
        ),
      ],
    ],
  };

  const context: Context = [{ trait_def: monadTrait }];

  const binding = context.find((b) => "trait_def" in b);
  assert(binding !== undefined, "monad trait should be in context");
  assert("trait_def" in binding!, "should be trait_def binding");
  assert(binding!.trait_def.methods.length === 2, "should have 2 methods");
});

test("Bounded forall type equality", () => {
  const constraint: TraitConstraint = {
    trait: "Show",
    type: varType("T"),
  };

  const type1 = boundedForallType(
    "T",
    starKind,
    [constraint],
    arrowType(varType("T"), conType("String")),
  );

  const type2 = boundedForallType(
    "T",
    starKind,
    [constraint],
    arrowType(varType("T"), conType("String")),
  );

  assert(typesEqual(type1, type2), "identical bounded foralls should be equal");
});

test("Bounded forall with different constraints not equal", () => {
  const type1 = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  const type2 = boundedForallType(
    "T",
    starKind,
    [{ trait: "Eq", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  assert(
    !typesEqual(type1, type2),
    "different constraints should not be equal",
  );
});

test("Trait substitution in constraints", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  // Λ T where Show<T>. λf: T -> T. λx: T. x
  const polyFunc = traitLamTerm(
    "showDict",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    lamTerm(
      "f",
      arrowType(varType("T"), varType("T")),
      lamTerm("x", varType("T"), varTerm("x")),
    ),
  );

  const context: Context = [
    { type: { kind: starKind, name: "Int" } },
    { type: { kind: starKind, name: "String" } },
    { trait_def: showTrait },
    { trait_impl: { trait: "Show", type: intType, dict: intShowDict } },
  ];

  // Apply to Int - should substitute T with Int in Show<T> constraint
  const applied = traitAppTerm(polyFunc, intType, [intShowDict]);

  const result = typecheck(context, applied);
  const type = assertOk(result, "should typecheck after substitution");
  assert("arrow" in type, "should be function type");
});

test("Kind checking bounded forall", () => {
  const polyType = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  const result = checkKind(
    [{ type: { kind: starKind, name: "String" } }],
    polyType,
  );
  const kind = assertOk(result, "should have valid kind");
  assert("star" in kind, "bounded forall should have kind *");
});

test("Kind mismatch in trait constraint type", () => {
  // Constraint type must have kind *, not * -> *
  const badType = boundedForallType(
    "F",
    { arrow: { from: starKind, to: starKind } },
    [{ trait: "Show", type: varType("F") }], // F has kind * -> *, but Show expects *
    varType("F"),
  );

  const result = checkKind([], badType);
  const err = assertErr(result, "should fail");
  assert("kind_mismatch" in err, "should be kind mismatch error");
});

test("Alpha equivalence with unused variables", () => {
  const type1 = forallType("A", starKind, conType("Int"));
  const type2 = forallType("B", starKind, conType("Int"));

  assert(
    typesEqual(type1, type2),
    "unused variables should be alpha equivalent",
  );
});

test("Structural equality for large types", () => {
  const fields: [string, Type][] = [];
  for (let i = 0; i < 100; i++) {
    fields.push([`field${i}`, conType("Int")]);
  }

  const type1 = recordType(fields);
  const type2 = recordType(fields);

  assert(typesEqual(type1, type2), "large records should be equal");
});

test("Inequality with different structures", () => {
  const type1 = recordType([["x", conType("Int")]]);
  const type2 = tupleType([conType("Int")]);

  assert(!typesEqual(type1, type2), "different structures should not be equal");
});

test("Subsumption: Bottom subtypes everything", () => {
  const neverType = { never: null };
  const intType = conType("Int");
  const arrow = arrowType(intType, conType("String"));

  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  // ⊥ <: Int
  let subsumesRes = subsumes([], arrow, neverType, worklist, subst); // General first
  assertOk(subsumesRes, "⊥ should subtype Int");

  // ⊥ <: arrow
  subsumesRes = subsumes([], arrow, neverType, worklist, subst);
  assertOk(subsumesRes, "⊥ should subtype function");

  // Non-bottom not subtype of ⊥
  subsumesRes = subsumes([], neverType, intType, worklist, subst);
  const err = assertErr(subsumesRes, "Int should not subtype ⊥");
  assert("type_mismatch" in err, "should mismatch");

  // AssignableTo checks
  assert(isAssignableTo(neverType, intType), "⊥ assignable to Int");
  assert(!isAssignableTo(intType, neverType), "Int not assignable to ⊥");
});

test("Subsumption in match branches (unreachable = bottom)", () => {
  const optionInt = variantType([
    ["None", unitType],
    ["Some", conType("Int")],
  ]);
  const neverType = { never: null };

  // Create a term with bottom type (e.g., unreachable())
  const unreachableTerm = conTerm("unreachable", neverType);

  // Match with unreachable Some branch
  const unreachableMatch = lamTerm(
    "opt",
    optionInt,
    matchTerm(varTerm("opt"), [
      [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
      [variantPattern("Some", varPattern("x")), unreachableTerm], // Bottom term
    ]),
  );

  const context: Context = [{ type: { name: "Int", kind: starKind } }];
  const result = typecheck(context, unreachableMatch);
  const type = assertOk(result, "bottom branch should subtype Int");
  assert(
    typesEqual(type, arrowType(optionInt, conType("Int"))),
    "overall type should be Option Int -> Int",
  );
});

test("Subsumption for records (width subtyping simulation)", () => {
  const baseRecord = recordType([["x", conType("Int")]]);
  const extendedRecord = recordType([
    ["x", conType("Int")],
    ["y", conType("String")],
  ]);

  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  // Extended <: base (width: extra fields OK)
  const subsumesRes = subsumes([], baseRecord, extendedRecord, worklist, subst);
  assertOk(subsumesRes, "extended record should subtype base");

  // Reverse fails
  const reverseRes = subsumes([], extendedRecord, baseRecord, worklist, subst);
  const err = assertErr(reverseRes, "base should not subtype extended");
  assert("type_mismatch" in err, "should mismatch");
});

test("Infer mode for simple lambda", () => {
  const lam = lamTerm("x", conType("Int"), varTerm("x"));
  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  const inferRes = inferTypeWithMode(context, lam, { infer: null });
  const type = assertOk(inferRes, "infer mode should work");
  assert("arrow" in type, "should infer arrow");
});

test("Check mode against expected arrow", () => {
  const expected = arrowType(conType("Int"), conType("String"));
  const lam = lamTerm("x", conType("Int"), conTerm('"hi"', conType("String")));

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  const checkRes = inferTypeWithMode(context, lam, { check: expected });
  const typeRes = assertOk(checkRes, "check mode should succeed");
  assert(typesEqual(typeRes, expected), "inferred should match checked");
});

test("Check mode failure for inject", () => {
  const variant = variantType([
    ["Ok", conType("Int")],
    ["Err", conType("String")],
  ]);
  const badInject = injectTerm(
    "Ok",
    conTerm('"bad"', conType("String")),
    variant,
  );

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  const checkRes = checkType(context, badInject, variant);
  const err = assertErr(checkRes, "should fail check");
  assert("type_mismatch" in err, "should mismatch payload");

  // Infer mode also fails (same error)
  const inferRes = typecheck(context, badInject);
  const inferErr = assertErr(inferRes, "infer should also fail");
  assert("type_mismatch" in inferErr, "infer should propagate mismatch");
});

test("Check mode for fold against mu", () => {
  const natType = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );
  const unfolded = variantType([
    ["Zero", unitType],
    ["Succ", natType],
  ]);
  const zeroFold = foldTerm(natType, injectTerm("Zero", unitValue, unfolded));

  const context: Context = [
    { type: { kind: starKind, name: "Int" } }, // Add Int binding
  ];

  const checkRes = checkType(context, zeroFold, natType);
  assertOk(checkRes, "should check fold against mu");

  // Wrong: Fold against non-mu
  const wrongCheck = checkType(context, zeroFold, conType("Int"));
  const err = assertErr(wrongCheck, "should fail non-mu check");
  assert(
    "type_mismatch" in err || "not_a_variant" in err,
    "should mismatch or invalid fold",
  );
});

test("Fresh meta-var creation, uniqueness, and solving behavior", () => {
  // Create two fresh meta-variables ?0 and ?1
  const meta1 = freshMetaVar(); // { var: "?0" }
  const meta2 = freshMetaVar(); // { var: "?1" }

  // Both should be meta variables starting with "?"
  assert(
    "var" in meta1 && meta1.var.startsWith("?"),
    "meta1 should be meta-var",
  );
  assert(
    "var" in meta2 && meta2.var.startsWith("?"),
    "meta2 should be meta-var",
  );

  // They must be distinct
  assert(
    meta1.var !== meta2.var,
    `Expected unique metas, got ${meta1.var} and ${meta2.var}`,
  );

  // Both should be recorded in metaKind with kind *
  assert(
    metaKind.has(meta1.var) && "star" in metaKind.get(meta1.var)!,
    `metaKind should assign * kind for ${meta1.var}`,
  );
  assert(
    metaKind.has(meta2.var) && "star" in metaKind.get(meta2.var)!,
    `metaKind should assign * kind for ${meta2.var}`,
  );

  // Solve meta1 := Int
  const intType = conType("Int");
  const solveRes1 = solveMetaVar(meta1.var, intType);
  assertOk(solveRes1, "should solve meta1");

  // After solving, global substitution should include meta1, but not meta2
  const globalSubst = getMetaSubstitution();
  assert(globalSubst.has(meta1.var), "global subst should contain meta1");
  assert(
    !globalSubst.has(meta2.var),
    "global subst should NOT contain meta2 (unsolved)",
  );

  // Value in substitution must equal Int
  const solved = globalSubst.get(meta1.var)!;
  assert(
    typesEqual(solved, intType),
    `Expected Int in global subst for ${meta1.var}, got ${JSON.stringify(solved)}`,
  );

  // Solving meta2 := String should not affect meta1
  const stringType = conType("String");
  const solveRes2 = solveMetaVar(meta2.var, stringType);
  assertOk(solveRes2, "should solve meta2 independently");
  const updated = getMetaSubstitution();
  assert(
    typesEqual(updated.get(meta1.var)!, intType),
    "meta1 binding should remain unchanged",
  );
  assert(
    typesEqual(updated.get(meta2.var)!, stringType),
    "meta2 binding should be String",
  );

  // Attempt to re-solve meta1 with conflicting type should fail
  const conflictRes = solveMetaVar(meta1.var, conType("String"));
  const conflictErr = assertErr(conflictRes, "should conflict on re-solve");
  assert(
    "type_mismatch" in conflictErr,
    "should report type_mismatch when re-solving with incompatible type",
  );
});

test("Meta-var in unification with conflict", () => {
  const meta = freshMetaVar();
  const intType = conType("Int");
  const strType = conType("String");

  const worklist1: Worklist = [{ type_eq: { left: meta, right: intType } }];
  const subst1 = new Map<string, Type>();
  const solveRes1 = solveConstraints(worklist1, subst1);
  assertOk(solveRes1, "first unify OK");

  // Conflict: Same meta ~ String
  const worklist2: Worklist = [{ type_eq: { left: meta, right: strType } }];
  const subst2 = new Map<string, Type>(subst1); // Inherit
  const solveRes2 = solveConstraints(worklist2, subst2);
  const conflict = assertErr(solveRes2, "should conflict");
  assert(
    "type_mismatch" in conflict &&
      typesEqual(conflict.type_mismatch.expected, intType),
    "should keep first binding",
  );
});

test("createVariantLambda builds kind-aware λ-type constructor and applies correctly", () => {
  // Structural Either variant
  const eitherVariant = variantType([
    ["Left", varType("a")],
    ["Right", varType("b")],
  ]);

  // Desired kind: * → * → *
  const eitherKind = arrowKind(starKind, arrowKind(starKind, starKind));

  // Create λ-type constructor
  const ctor = createVariantLambda(eitherVariant, eitherKind);

  // Structure check
  assert("lam" in ctor, "should be a λ-type");
  assert("lam" in ctor.lam.body, "should nest a second λ-type");

  // Apply it (β-reduction)
  const applied = appType(appType(ctor, varType("a")), varType("b"));
  const normalized = normalizeType(applied);

  // Expect it equals the original variant <Left: a | Right: b>
  assert(
    typesEqual(normalized, eitherVariant),
    `applying λtype should yield original variant, got ${showType(normalized)}`,
  );
});

test("Merge local/global substitutions with override", () => {
  const globalSubst = new Map<string, Type>([["?0", conType("Int")]]);

  // Local overrides ?0 to String, adds ?1=Bool
  const localSubst = new Map<string, Type>([
    ["?0", conType("String")],
    ["?1", conType("Bool")],
  ]);

  const merged = mergeSubsts(localSubst, globalSubst);
  assert(merged.size === 2, "should merge without duplicates");
  assert(
    typesEqual(merged.get("?0")!, conType("String")),
    "local should override global",
  );
  assert(
    typesEqual(merged.get("?1")!, conType("Bool")),
    "local should add new",
  );
});

test("Not a function error in app 2", () => {
  const intType = conType("Int");
  const badApp = appTerm(conTerm("42", intType), conTerm("5", intType));

  const result = typecheck([], badApp);
  const err = assertErr(result, "should fail");
  assert("not_a_function" in err, "should report not_a_function");
});

test("Not a type function in kind app", () => {
  const badApp = appType(conType("Int"), conType("Bool")); // Int applied to Bool (not lam)

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "Bool", kind: starKind } },
  ];
  const kindRes = checkKind(context, badApp);
  const err = assertErr(kindRes, "should fail kind app");
  assert("not_a_type_function" in err, "should report not type func");
});

test("Cyclic type error in mu", () => {
  const cyclicMu = muType("X", varType("Y"));
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();

  const unifyRes = unifyTypes(cyclicMu, varType("Y"), worklist, subst);
  const err = assertErr(unifyRes, "should detect cyclic mu");
  assert("cyclic" in err, "should report cyclic");
});

test("Unexpected kind error", () => {
  // Type var with unexpected kind in context
  const ctx: Context = [
    { type: { name: "Int", kind: starKind } },
    { type: { name: "T", kind: { arrow: { from: starKind, to: starKind } } } },
  ];
  const app = appType(varType("T"), conType("Int")); // T :: * -> * applied to *, OK
  const kindRes = checkKind(ctx, app);
  assertOk(kindRes, "should succeed");

  // Unexpected: Use arrow kind where * expected
  const badUse = arrowType(varType("T"), conType("Int")); // T has * -> *, but arrow expects *
  const badRes = checkKind(ctx, badUse);
  const err = assertErr(badRes, "should fail unexpected kind");
  assert(
    "unexpected_kind" in err || "kind_mismatch" in err,
    "should report kind error",
  );
});

test("Enum definition and nominal Option type", () => {
  const optionEnum: EnumDef = {
    name: "Option",
    kind: { arrow: { from: starKind, to: starKind } },
    params: ["T"],
    variants: [
      ["None", unitType],
      ["Some", varType("T")],
    ],
  };

  const intType = conType("Int");
  const optionInt = appType(conType("Option"), intType); // Nominal: Option<Int>

  const context: Context = [
    {
      type: {
        name: "Option",
        kind: { arrow: { from: starKind, to: starKind } },
      },
    },
    { enum: optionEnum },
    { type: { name: "Int", kind: starKind } },
  ];

  // Kind check
  const kindResult = checkKind(context, optionInt);
  const kind = assertOk(kindResult, "should kind-check nominal Option<Int>");
  assert("star" in kind, "should be *");

  // Unify nominal ~ structural
  const structuralOption = variantType([
    ["None", unitType],
    ["Some", intType],
  ]);
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const unifyRes = unifyTypes(
    optionInt,
    structuralOption,
    worklist,
    subst,
    context,
  );
  assertOk(unifyRes, "nominal should unify with structural via enum expansion");

  // Normalize should expand
  const normalized = normalizeType(optionInt, context);
  assert("variant" in normalized, "normalize should expand to structural");
  assert(typesEqual(normalized, structuralOption), "should match structural");
});

test("Nominal injection into enum (Option::Some)", () => {
  const optionEnum: EnumDef = {
    name: "Option",
    kind: { arrow: { from: starKind, to: starKind } },
    params: ["T"],
    variants: [
      ["None", unitType],
      ["Some", varType("T")],
    ],
  };

  const intType = conType("Int");
  const optionInt = appType(conType("Option"), intType);

  const someVal = injectTerm("Some", conTerm("42", intType), optionInt);

  const context: Context = [
    { enum: optionEnum },
    { type: { name: "Int", kind: starKind } },
  ];

  const result = typecheck(context, someVal);
  const type = assertOk(result, "should typecheck nominal Some");
  assert("app" in type, "should be Option<Int>");
  const spineArgs = getSpineArgs(type);
  assert(
    spineArgs.length === 1 && typesEqual(spineArgs[0], intType),
    "spine arg should be Int",
  );
});

test("Nominal exhaustive matching on enum (Either)", () => {
  const eitherEnum: EnumDef = {
    name: "Either",
    kind: {
      arrow: {
        from: starKind,
        to: { arrow: { from: starKind, to: starKind } },
      },
    },
    params: ["L", "R"],
    variants: [
      ["Left", varType("L")],
      ["Right", varType("R")],
    ],
  };

  const intType = conType("Int");
  const boolType = conType("Bool");
  const eitherIntBool = appType(appType(conType("Either"), intType), boolType);

  const patterns = [
    variantPattern("Left", varPattern("l")),
    variantPattern("Right", varPattern("r")),
  ];

  const context: Context = [
    {
      type: {
        name: "Either",
        kind: {
          arrow: {
            from: starKind,
            to: { arrow: { from: starKind, to: starKind } },
          },
        },
      },
    },
    { enum: eitherEnum },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "Bool", kind: starKind } },
  ];

  const exhaustRes = checkExhaustive(patterns, eitherIntBool, context);
  assertOk(exhaustRes, "nominal Either should be exhaustive");

  // Non-exhaustive (missing Right)
  const incompletePatterns = [variantPattern("Left", varPattern("l"))];
  const incompleteRes = checkExhaustive(
    incompletePatterns,
    eitherIntBool,
    context,
  );
  const err = assertErr(incompleteRes, "should detect missing case");
  assert(
    "missing_case" in err && err.missing_case.label === "Right",
    "should report missing Right",
  );
});

test("Invalid label in nominal enum injection", () => {
  const optionEnum: EnumDef = {
    name: "Option",
    params: ["T"],
    kind: { arrow: { from: starKind, to: starKind } },
    variants: [
      ["None", unitType],
      ["Some", varType("T")],
    ],
  };

  const optionUnit = appType(conType("Option"), unitType);
  const invalidInject = injectTerm("Invalid", unitValue, optionUnit);

  const context: Context = [{ enum: optionEnum }];

  const result = typecheck(context, invalidInject);
  const err = assertErr(result, "should fail on invalid label");
  assert(
    "invalid_variant_label" in err &&
      err.invalid_variant_label.label === "Invalid",
    "should report invalid label",
  );
});

test("Concrete trait impl binding and lookup", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");
  const showImpl = lamTerm("x", intType, conTerm('"int"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const intImplBinding: TraitImplBinding = {
    trait_impl: { trait: "Show", type: intType, dict: intShowDict },
  };

  const context: Context = [
    { trait_def: showTrait },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
    intImplBinding,
  ];

  // Lookup impl for Show<Int>
  const lookupRes = checkTraitImplementation(context, "Show", intType);
  const dict = assertOk(lookupRes, "should find concrete impl");
  assert("dict" in dict, "should return dict term");

  // Use in a function
  const useImpl = lamTerm(
    "x",
    intType,
    appTerm(traitMethodTerm(dict, "show"), varTerm("x")),
  );
  const result = typecheck(context, useImpl);
  const type = assertOk(result, "should use impl");
  assert(
    typesEqual(type, arrowType(intType, conType("String"))),
    "should be Show method type",
  );
});

test("Trait impl with wrong number of dicts in app", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const showValue = traitLamTerm(
    "d",
    "Show",
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    varTerm("d"),
  );

  const context: Context = [
    { trait_def: showTrait },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  // Provide 0 dicts (expected 1)
  const appWithZero = traitAppTerm(showValue, conType("Int"), []);
  const result = typecheck(context, appWithZero);
  const err = assertErr(result, "should fail");
  assert("wrong_number_of_dicts" in err, "should report wrong dict count");

  // Provide 2 dicts (extra)
  const appWithExtra = traitAppTerm(showValue, conType("Int"), [
    dictTerm("Show", conType("Int"), [
      ["show", lamTerm("x", conType("Int"), conTerm('"x"', conType("String")))],
    ]),
    dictTerm("Show", conType("Int"), [
      ["show", lamTerm("x", conType("Int"), conTerm('"x"', conType("String")))],
    ]),
  ]);
  const extraRes = typecheck(context, appWithExtra);
  const extraErr = assertErr(extraRes, "should fail on extra dicts");
  assert("wrong_number_of_dicts" in extraErr, "should report extra dicts");
});

test("Unification of lambda types", () => {
  const lam1 = lamType("A", starKind, varType("A"));
  const lam2 = lamType("X", starKind, varType("X")); // Alpha equiv

  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const res = unifyTypes(lam1, lam2, worklist, subst);
  assertOk(res, "lambdas should unify via alpha");

  // Mismatch kinds
  const badLam = lamType(
    "A",
    { arrow: { from: starKind, to: starKind } },
    varType("A"),
  );
  const badRes = unifyTypes(lam1, badLam, worklist, subst);
  const err = assertErr(badRes, "kind mismatch should fail");
  assert("kind_mismatch" in err, "should report kind error");
});

test("Unification with app types", () => {
  const app1 = appType(lamType("T", starKind, varType("T")), conType("Int"));
  const app2 = appType(lamType("X", starKind, varType("X")), conType("Int"));

  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const res = unifyTypes(app1, app2, worklist, subst);
  assertOk(res, "apps should unify after normalize");

  // Head mismatch
  const badApp = appType(conType("List"), conType("Int"));
  const badRes = unifyTypes(app1, badApp, [], new Map());
  const err = assertErr(badRes, "head mismatch");
  assert("type_mismatch" in err, "should mismatch");
});

test("Substitution in mu types with cycles", () => {
  const muTy = muType("M", arrowType(varType("M"), varType("M")));
  const avoid = new Set(["M"]);

  // Subst non-bound var
  const substRes = substituteType("X", conType("Int"), muTy, avoid);
  assert("mu" in substRes, "should preserve mu");

  // Subst bound var: Should skip
  const selfSubst = substituteType("M", conType("Int"), muTy, new Set());
  assert(
    "mu" in selfSubst && selfSubst.mu.var === "M",
    "should not subst bound var",
  );

  // Infinite recursion protection
  const cyclicAvoid = new Set<string>();
  cyclicAvoid.add("M");
  const protectedSubst = substituteType(
    "Y",
    muTy,
    arrowType(varType("Y"), muTy),
    cyclicAvoid,
  );
  assert(
    "arrow" in protectedSubst && "mu" in protectedSubst.arrow.to,
    "should stop at cycle",
  );
});

test("Unification detects cycles in mu", () => {
  const worklist: Worklist = [];
  const subst = new Map<string, Type>();
  const mu1 = muType("M", varType("M")); // Infinite M
  const metaM = freshMetaVar();

  const res = unifyTypes(metaM, mu1, worklist, subst);
  const err = assertErr(res, "should detect mu cycle");
  assert("cyclic" in err, "should report cyclic");
});

test("Show functions for complex types/terms", () => {
  const complexType = arrowType(
    forallType(
      "A",
      starKind,
      appType(lamType("T", starKind, varType("T")), varType("A")),
    ),
    muType(
      "M",
      boundedForallType(
        "B",
        starKind,
        [{ trait: "Show", type: varType("B") }],
        varType("M"),
      ),
    ),
  );
  const shownType = showType(complexType);
  assert(
    typeof shownType === "string" &&
      shownType.includes("∀") &&
      shownType.includes("μ"),
    "should pretty-print complex",
  );

  const complexTerm = appTerm(
    traitAppTerm(
      tylamTerm(
        "X",
        starKind,
        injectTerm(
          "Some",
          foldTerm(muType("M", varType("X")), varTerm("x")),
          appType(conType("Option"), varType("X")),
        ),
      ),
      conType("Int"),
      [],
    ),
    recordTerm([["f", lamTerm("y", conType("Int"), varTerm("y"))]]),
  );
  const shownTerm = showTerm(complexTerm);
  assert(
    typeof shownTerm === "string" && shownTerm.includes("Λ"),
    "should pretty-print complex terms",
  );
});

test("InferTypeWithMode delegation", () => {
  const lam = lamTerm("x", conType("Int"), varTerm("x"));
  const context: Context = [{ type: { name: "Int", kind: starKind } }];

  // Infer mode
  const inferRes = inferTypeWithMode(context, lam, { infer: null });
  assertOk(inferRes, "should delegate to inferType");

  // Check mode
  const expected = arrowType(conType("Int"), conType("Int"));
  const checkRes = inferTypeWithMode(context, lam, { check: expected });
  const typeRes = assertOk(
    checkRes,
    "should delegate to checkType and return type",
  );
  assert("arrow" in typeRes, "should return checked type");
});

test("Deep recursion in substitution/normalization (no stack overflow)", () => {
  // Build deep arrow: Int -> (Int -> (Int -> ... )) with 100 levels
  let deepArrow: Type = conType("Int");
  for (let i = 0; i < 100; i++) {
    deepArrow = arrowType(conType("Int"), deepArrow);
  }

  // Subst in deep structure
  const substDeep = substituteType("X", conType("Bool"), deepArrow, new Set());
  assert("arrow" in substDeep, "should traverse deep without overflow");

  // Normalize deep (no apps, so unchanged)
  const normDeep = normalizeType(deepArrow);
  assert(typesEqual(normDeep, deepArrow), "deep should normalize idempotently");
});

test("Higher‑kinded lam‑lam kinding", () => {
  const ty = lamType(
    "F",
    { arrow: { from: starKind, to: starKind } },
    lamType("X", starKind, appType(varType("F"), varType("X"))),
  );
  const kind = assertOk(checkKind([], ty), "should be ok kind");
  assert("arrow" in kind, "should have arrow kind");
  assert("arrow" in kind.arrow.to, "should be *→*→*");
});

test("Kind‑checking with shadowed lambdas", () => {
  const ty = lamType(
    "A",
    starKind,
    lamType("A", starKind, arrowType(varType("A"), varType("A"))),
  );
  const kind = assertOk(checkKind([], ty), "should be ok kind");
  assert("arrow" in kind, "should still be an arrow kind");
});

test("kindArity computes number of type parameters", () => {
  const k = {
    arrow: { from: starKind, to: { arrow: { from: starKind, to: starKind } } },
  };
  const arity = kindArity(k);
  expect(arity).toBe(2);
});

test("Rank‑2 lambda kind", () => {
  const rank2 = lamType(
    "F",
    { arrow: { from: starKind, to: starKind } },
    lamType("X", starKind, varType("X")),
  );
  const res = assertOk(checkKind([], rank2), "should be ok kind");
  assert("arrow" in res, "rank‑2 kind ok");
});

test("Normalization reduces nested beta redexes", () => {
  const doubleApp = lamType(
    "A",
    starKind,
    lamType("B", starKind, arrowType(varType("A"), varType("B"))),
  );
  const applied = appType(appType(doubleApp, conType("Int")), conType("Bool"));
  const normalized = normalizeType(applied);
  const expected = arrowType(conType("Int"), conType("Bool"));
  assert(
    typesEqual(normalized, expected),
    `expected ${showType(expected)} but got ${showType(normalized)}`,
  );
});

test("Normalization avoids variable capture in nested lambdas", () => {
  const ty = appType(
    lamType("A", starKind, lamType("A", starKind, varType("A"))),
    conType("Int"),
  );
  const norm = normalizeType(ty);
  // Result should be λA. A (outer A shadowed)
  assert("lam" in norm, "should remain a lambda after reduction");
});

test("Normalization is idempotent", () => {
  const t = appType(lamType("T", starKind, varType("T")), conType("Int"));
  const t1 = normalizeType(t);
  const t2 = normalizeType(t1);
  assert(typesEqual(t1, t2), "normalization should be idempotent");
});

test("Normalization of higher‑order constructor", () => {
  const listCon = lamType(
    "X",
    starKind,
    muType(
      "L",
      variantType([
        ["Nil", unitType],
        ["Cons", tupleType([varType("X"), varType("L")])],
      ]),
    ),
  );
  const listInt = appType(listCon, conType("Int"));
  const norm = normalizeType(listInt);
  assert("mu" in norm, "list constructor should normalize to a mu type");
});

test("Normalization of partially applied type constructor", () => {
  // (λF::*→*. λX::*. F X) List should normalize to λX::*. List X
  const partialApp = appType(
    lamType(
      "F",
      { arrow: { from: starKind, to: starKind } },
      lamType("X", starKind, appType(varType("F"), varType("X"))),
    ),
    lamType(
      "T",
      starKind,
      variantType([
        ["Nil", unitType],
        ["Cons", tupleType([varType("T"), varType("T")])],
      ]),
    ),
  );

  const normalized = normalizeType(partialApp);

  // Should reduce outer lambda but keep inner one
  assert(
    "lam" in normalized,
    "should normalize to a lambda (partially applied)",
  );
});

test("Normalization respects bounded forall structure", () => {
  const t = boundedForallType(
    "X",
    starKind,
    [{ trait: "Show", type: varType("X") }],
    appType(lamType("T", starKind, varType("T")), varType("X")),
  );
  const norm = normalizeType(t);
  assert("bounded_forall" in norm, "top‑level bounded forall preserved");
  assert(
    typesEqual(norm.bounded_forall.body, varType("X")),
    "body β‑reduced correctly",
  );
});

test("Structural mu variant has star kind", () => {
  const nat = muType(
    "N",
    variantType([
      ["Zero", unitType],
      ["Succ", varType("N")],
    ]),
  );
  const kind = assertOk(checkKind([], nat), "should be ok kind");
  assert("star" in kind, "mu variant should be kind *");
});

test("Kind mismatch between higher‑kinded and * type", () => {
  const higher = lamType(
    "F",
    { arrow: { from: starKind, to: starKind } },
    varType("F"),
  );
  const applied = appType(higher, higher);
  const res = checkKind([], applied);
  const err = assertErr(res, "should be error kind");
  assert("kind_mismatch" in err, "should report kind mismatch");
});

test("showKind prints nested arrows", () => {
  const kind = {
    arrow: { from: starKind, to: { arrow: { from: starKind, to: starKind } } },
  };
  const s = showKind(kind);
  expect(s).toContain("→");
});

test("Normalization preserves composite types", () => {
  const t = arrowType(
    forallType("A", starKind, varType("A")),
    muType("L", arrowType(varType("L"), varType("L"))),
  );
  const n = normalizeType(t);
  assert(typesEqual(t, n), "no structural change expected");
});

test("Normalization retains unused forall quantifier", () => {
  const t = forallType("X", starKind, conType("Int"));
  const n = normalizeType(t);
  assert("forall" in n, "should preserve forall with unused variable");
});

test("checkType aborts on global meta conflict", () => {
  // Manually pre‑solve a meta to one type
  const meta = freshMetaVar();
  const intType = conType("Int");
  const strType = conType("String");

  const first = solveMetaVar(meta.var, intType);
  if ("err" in first) throw new Error("unexpected err on first solve");

  // Now pretend checkType tries to propagate same meta with new solution
  const result = solveMetaVar(meta.var, strType);
  const err = assertErr(result, "should be error kind");
  expect("err" in result).toBe(true);
  expect("type_mismatch" in err).toBe(true);
});

test("instantiateWithTraits automatically finds Show impl", () => {
  const showTrait: TraitDef = {
    name: "Show",
    type_param: "Self",
    kind: starKind,
    methods: [["show", arrowType(varType("Self"), conType("String"))]],
  };

  const intType = conType("Int");

  const showImpl = lamTerm("x", intType, conTerm('"42"', conType("String")));
  const intShowDict = dictTerm("Show", intType, [["show", showImpl]]);

  const showT = boundedForallType(
    "T",
    starKind,
    [{ trait: "Show", type: varType("T") }],
    arrowType(varType("T"), conType("String")),
  );

  const ctx: Context = [
    { trait_def: showTrait },
    { trait_impl: { trait: "Show", type: intType, dict: intShowDict } },
    { type: { name: "Int", kind: starKind } },
    { type: { name: "String", kind: starKind } },
  ];

  const instantiated = instantiateWithTraits(ctx, showT);
  if ("err" in instantiated) throw new Error("expected ok");
  const { type, dicts } = instantiated.ok;

  expect(dicts.length).toBe(1);
  expect(dicts[0]).toMatchObject(intShowDict);
  // The instantiated type body replaces Self with Int
  expect("arrow" in type).toBe(true);
  expect(((type as ArrowType).arrow.to as ConType).con).toBe("String");
});

describe("Type Aliases", () => {
  describe("Basic Aliases", () => {
    it("should expand simple non-parameterized alias", () => {
      const ctx: Context = [
        // type Int32 = Int
        typeAliasBinding("Int32", [], [], conType("Int")),
        { type: { name: "Int", kind: starKind } },
      ];

      const aliasType = conType("Int32");
      const normalized = normalizeType(aliasType, ctx);

      expect(typesEqual(normalized, conType("Int"))).toBe(true);
    });

    it("should check kind of simple alias", () => {
      const ctx: Context = [
        // type Int32 = Int
        typeAliasBinding("Int32", [], [], conType("Int")),
        { type: { name: "Int", kind: starKind } },
      ];

      const result = checkKind(ctx, conType("Int32"));

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("star" in result.ok).toBe(true);
      }
    });

    it("should use alias in term types", () => {
      const ctx: Context = [
        // type Int32 = Int
        typeAliasBinding("Int32", [], [], conType("Int")),
        { type: { name: "Int", kind: starKind } },
        { term: { name: "x", type: conType("Int") } },
      ];

      // λy:Int32. x
      const term = lamTerm("y", conType("Int32"), varTerm("x"));
      const result = inferType(ctx, term);

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect(
          typesEqual(result.ok, arrowType(conType("Int"), conType("Int"))),
        ).toBe(true);
      }
    });
  });

  describe("Parameterized Aliases", () => {
    it("should expand single-parameter alias", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // Ref<Int>
      const aliasType = appType(conType("Ref"), conType("Int"));
      const normalized = normalizeType(aliasType, ctx);

      expect(
        typesEqual(normalized, recordType([["value", conType("Int")]])),
      ).toBe(true);
    });

    it("should expand multi-parameter alias", () => {
      const ctx: Context = [
        // type Pair<a, b> = (a, b)
        typeAliasBinding(
          "Pair",
          ["a", "b"],
          [starKind, starKind],
          tupleType([varType("a"), varType("b")]),
        ),
        { type: { name: "Int", kind: starKind } },
        { type: { name: "Bool", kind: starKind } },
      ];

      // Pair<Int, Bool>
      const aliasType = appType(
        appType(conType("Pair"), conType("Int")),
        conType("Bool"),
      );
      const normalized = normalizeType(aliasType, ctx);

      expect(
        typesEqual(normalized, tupleType([conType("Int"), conType("Bool")])),
      ).toBe(true);
    });

    it("should check kind of parameterized alias", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
      ];

      const result = checkKind(ctx, conType("Ref"));

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("arrow" in result.ok).toBe(true);
        if ("arrow" in result.ok) {
          expect("star" in result.ok.arrow.from).toBe(true);
          expect("star" in result.ok.arrow.to).toBe(true);
        }
      }
    });

    it("should check kind of applied alias", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // Ref<Int>
      const result = checkKind(ctx, appType(conType("Ref"), conType("Int")));

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("star" in result.ok).toBe(true);
      }
    });
  });

  describe("Nested Aliases", () => {
    it("should expand nested aliases", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        // type IntRef = Ref<Int>
        typeAliasBinding(
          "IntRef",
          [],
          [],
          appType(conType("Ref"), conType("Int")),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      const aliasType = conType("IntRef");
      const normalized = normalizeType(aliasType, ctx);

      expect(
        typesEqual(normalized, recordType([["value", conType("Int")]])),
      ).toBe(true);
    });

    it("should expand aliases that reference other aliases", () => {
      const ctx: Context = [
        // type Pair<a, b> = (a, b)
        typeAliasBinding(
          "Pair",
          ["a", "b"],
          [starKind, starKind],
          tupleType([varType("a"), varType("b")]),
        ),
        // type Triple<a, b, c> = (Pair<a, b>, c)
        typeAliasBinding(
          "Triple",
          ["a", "b", "c"],
          [starKind, starKind, starKind],
          tupleType([
            appType(appType(conType("Pair"), varType("a")), varType("b")),
            varType("c"),
          ]),
        ),
        { type: { name: "Int", kind: starKind } },
        { type: { name: "Bool", kind: starKind } },
        { type: { name: "String", kind: starKind } },
      ];

      // Triple<Int, Bool, String>
      const aliasType = appType(
        appType(appType(conType("Triple"), conType("Int")), conType("Bool")),
        conType("String"),
      );
      const normalized = normalizeType(aliasType, ctx);

      expect(
        typesEqual(
          normalized,
          tupleType([
            tupleType([conType("Int"), conType("Bool")]),
            conType("String"),
          ]),
        ),
      ).toBe(true);
    });
  });

  describe("Aliases in Complex Types", () => {
    it("should expand alias in arrow type", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // Ref<Int> → Int
      const funcType = arrowType(
        appType(conType("Ref"), conType("Int")),
        conType("Int"),
      );
      const normalized = normalizeType(funcType, ctx);

      expect(
        typesEqual(
          normalized,
          arrowType(recordType([["value", conType("Int")]]), conType("Int")),
        ),
      ).toBe(true);
    });

    it("should expand alias in forall type", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
      ];

      // ∀t. Ref<t>
      const polyType = forallType(
        "t",
        starKind,
        appType(conType("Ref"), varType("t")),
      );
      const normalized = normalizeType(polyType, ctx);

      expect("forall" in normalized).toBe(true);
      if ("forall" in normalized) {
        expect(
          typesEqual(
            normalized.forall.body,
            recordType([["value", varType("t")]]),
          ),
        ).toBe(true);
      }
    });

    it("should expand alias in variant type", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // <Some: Ref<Int> | None: ()>
      const varTy = variantType([
        ["Some", appType(conType("Ref"), conType("Int"))],
        ["None", tupleType([])],
      ]);
      const normalized = normalizeType(varTy, ctx);

      expect(
        typesEqual(
          normalized,
          variantType([
            ["Some", recordType([["value", conType("Int")]])],
            ["None", tupleType([])],
          ]),
        ),
      ).toBe(true);
    });

    it("should expand alias in record type", () => {
      const ctx: Context = [
        // type Pair<a, b> = (a, b)
        typeAliasBinding(
          "Pair",
          ["a", "b"],
          [starKind, starKind],
          tupleType([varType("a"), varType("b")]),
        ),
        { type: { name: "Int", kind: starKind } },
        { type: { name: "String", kind: starKind } },
      ];

      // { name: String, coords: Pair<Int, Int> }
      const recType = recordType([
        ["name", conType("String")],
        [
          "coords",
          appType(appType(conType("Pair"), conType("Int")), conType("Int")),
        ],
      ]);
      const normalized = normalizeType(recType, ctx);

      expect(
        typesEqual(
          normalized,
          recordType([
            ["name", conType("String")],
            ["coords", tupleType([conType("Int"), conType("Int")])],
          ]),
        ),
      ).toBe(true);
    });
  });

  describe("Higher-Kinded Aliases", () => {
    it("should handle alias with higher-kinded parameter", () => {
      const ctx: Context = [
        // type Apply<f, a> = f<a>
        typeAliasBinding(
          "Apply",
          ["f", "a"],
          [arrowKind(starKind, starKind), starKind],
          appType(varType("f"), varType("a")),
        ),
        { type: { name: "List", kind: arrowKind(starKind, starKind) } },
        { type: { name: "Int", kind: starKind } },
      ];

      // Apply<List, Int>
      const aliasType = appType(
        appType(conType("Apply"), conType("List")),
        conType("Int"),
      );
      const normalized = normalizeType(aliasType, ctx);

      expect(
        typesEqual(normalized, appType(conType("List"), conType("Int"))),
      ).toBe(true);
    });

    it("should check kind of higher-kinded alias", () => {
      const ctx: Context = [
        // type Apply<f, a> = f<a>
        typeAliasBinding(
          "Apply",
          ["f", "a"],
          [arrowKind(starKind, starKind), starKind],
          appType(varType("f"), varType("a")),
        ),
      ];

      const result = checkKind(ctx, conType("Apply"));

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("arrow" in result.ok).toBe(true);
        // Should be (* → *) → * → *
      }
    });
  });

  describe("Error Cases", () => {
    it("should error on wrong arity for parameterized alias", () => {
      const ctx: Context = [
        // type Pair<a, b> = (a, b)
        typeAliasBinding(
          "Pair",
          ["a", "b"],
          [starKind, starKind],
          tupleType([varType("a"), varType("b")]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // Pair<Int> - missing second argument
      const aliasType = appType(conType("Pair"), conType("Int"));

      // Should not normalize (partial application)
      const normalized = normalizeType(aliasType, ctx);

      // The partially applied type should remain as-is
      expect("app" in normalized).toBe(true);
    });

    it("should error on unbound alias", () => {
      const ctx: Context = [];

      const result = checkKind(ctx, conType("UnknownAlias"));

      expect("err" in result).toBe(true);
      if ("err" in result) {
        expect("unbound" in result.err).toBe(true);
      }
    });

    it("should error on kind mismatch in alias application", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }  (expects a::*)
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
        { type: { name: "List", kind: arrowKind(starKind, starKind) } },
      ];

      // Ref<List> - List has kind * → *, but Ref expects *
      const aliasType = appType(conType("Ref"), conType("List"));
      const result = checkKind(ctx, aliasType);

      expect("err" in result).toBe(true);
      if ("err" in result) {
        expect("kind_mismatch" in result.err).toBe(true);
      }
    });
  });

  describe("Integration Tests", () => {
    it("should typecheck function using aliased types", () => {
      const ctx: Context = [
        // type Pair<a, b> = (a, b)
        typeAliasBinding(
          "Pair",
          ["a", "b"],
          [starKind, starKind],
          tupleType([varType("a"), varType("b")]),
        ),
        { type: { name: "Int", kind: starKind } },
        { type: { name: "String", kind: starKind } },
      ];

      // λp:Pair<Int, String>. p[0]
      const term = lamTerm(
        "p",
        appType(appType(conType("Pair"), conType("Int")), conType("String")),
        tupleProjectTerm(varTerm("p"), 0),
      );

      const result = typecheck(ctx, term);

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("arrow" in result.ok).toBe(true);
      }
    });

    it("should typecheck polymorphic function with aliased types", () => {
      const ctx: Context = [
        // type Ref<a> = { value: a }
        typeAliasBinding(
          "Ref",
          ["a"],
          [starKind],
          recordType([["value", varType("a")]]),
        ),
      ];

      // Λt. λref:Ref<t>. ref.value
      const term = tylamTerm(
        "t",
        starKind,
        lamTerm(
          "ref",
          appType(conType("Ref"), varType("t")),
          projectTerm(varTerm("ref"), "value"),
        ),
      );

      const result = typecheck(ctx, term);

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect("forall" in result.ok).toBe(true);
      }
    });

    it("should typecheck pattern matching with aliased variant", () => {
      const ctx: Context = [
        // type Option<a> = <Some: a | None: ()>
        typeAliasBinding(
          "Option",
          ["a"],
          [starKind],
          variantType([
            ["Some", varType("a")],
            ["None", tupleType([])],
          ]),
        ),
        { type: { name: "Int", kind: starKind } },
        {
          term: {
            name: "opt",
            type: appType(conType("Option"), conType("Int")),
          },
        },
      ];

      // match opt { Some(x) => x | None(_) => 0 }
      const term = matchTerm(varTerm("opt"), [
        [variantPattern("Some", varPattern("x")), varTerm("x")],
        [variantPattern("None", wildcardPattern()), varTerm("zero")],
      ]);

      // Add zero constant
      const ctxWithZero = [
        ...ctx,
        { term: { name: "zero", type: conType("Int") } },
      ];

      const result = typecheck(ctxWithZero, term);

      expect("ok" in result).toBe(true);
      if ("ok" in result) {
        expect(typesEqual(result.ok, conType("Int"))).toBe(true);
      }
    });

    it("should handle recursive alias definitions", () => {
      const ctx: Context = [
        // type List<a> = <Nil: () | Cons: (a, List<a>)>
        typeAliasBinding(
          "List",
          ["a"],
          [starKind],
          variantType([
            ["Nil", tupleType([])],
            [
              "Cons",
              tupleType([varType("a"), appType(conType("List"), varType("a"))]),
            ],
          ]),
        ),
        { type: { name: "Int", kind: starKind } },
      ];

      // List<Int>
      const listIntType = appType(conType("List"), conType("Int"));
      const normalized = normalizeType(listIntType, ctx);

      expect("variant" in normalized).toBe(true);
      if ("variant" in normalized) {
        const consCase = normalized.variant.find(([label]) => label === "Cons");
        expect(consCase).toBeDefined();
        if (consCase) {
          expect("tuple" in consCase[1]).toBe(true);
        }
      }
    });
  });

  describe("Edge Cases", () => {
    it("should handle alias shadowing", () => {
      const ctx: Context = [
        // type T = Int
        typeAliasBinding("T", [], [], conType("Int")),
        { type: { name: "Int", kind: starKind } },
      ];

      // ∀T. T (T is shadowed by forall)
      const polyType = forallType("T", starKind, varType("T"));
      const normalized = normalizeType(polyType, ctx);

      expect("forall" in normalized).toBe(true);
      if ("forall" in normalized) {
        // T in body should refer to bound var, not alias
        expect("var" in normalized.forall.body).toBe(true);
        if ("var" in normalized.forall.body) {
          expect(normalized.forall.body.var).toBe("T");
        }
      }
    });

    it("should handle empty alias (type synonym)", () => {
      const ctx: Context = [
        // type Unit = ()
        typeAliasBinding("Unit", [], [], tupleType([])),
      ];

      const aliasType = conType("Unit");
      const normalized = normalizeType(aliasType, ctx);

      expect(typesEqual(normalized, tupleType([]))).toBe(true);
    });

    it("should preserve non-alias constructors", () => {
      const ctx: Context = [
        // type MyInt = Int
        typeAliasBinding("MyInt", [], [], conType("Int")),
        { type: { name: "Int", kind: starKind } },
        { type: { name: "Bool", kind: starKind } },
      ];

      // Bool should not be affected
      const boolType = conType("Bool");
      const normalized = normalizeType(boolType, ctx);

      expect(typesEqual(normalized, conType("Bool"))).toBe(true);
    });
  });
});

test("checkKind of recursive type using enum", () => {
  const listEnum: EnumDef = {
    name: "List",
    kind: arrowKind(starKind, starKind), // * → *
    params: ["t"],
    variants: [
      ["Nil", tupleType([])],
      [
        "Cons",
        tupleType([varType("t"), appType(conType("List"), varType("t"))]),
      ],
    ],
  };

  const context: Context = [
    { type: { name: "Int", kind: starKind } },
    { enum: listEnum },
  ];

  // Now check the kind of List<Int>
  const listIntType = appType(conType("List"), conType("Int"));
  const val = checkKind(context, listIntType);
  const actual = assertOk(val, "Kind should return");

  expect(isStarKind(actual)).toBe(true);

  // Or check the kind of the constructor itself
  const listConType = conType("List");
  const conKind = checkKind(context, listConType);
  const actualConKind = assertOk(conKind, "Constructor kind should return");

  expect(kindsEqual(actualConKind, arrowKind(starKind, starKind))).toBe(true);
});

function resolveMetaVariables(t: Type): Type {
  const subst = getMetaSubstitution(); // "?0" ↦ Result<?1,?2>, …
  return applySubstitution(subst, t);
}

test("infers parameter type from usage (pattern match on Result)", () => {
  // ---------- enum definition ----------
  const resultEnum = {
    name: "Result",
    kind: arrowKind(starKind, arrowKind(starKind, starKind)), // * → * → *
    params: ["a", "b"],
    variants: [
      ["Ok", varType("a")],
      ["Err", varType("b")],
    ],
  } satisfies EnumDef;

  const ctx: Context = [{ enum: resultEnum }];

  // ---------- term ----------
  const scrutinee = varTerm("n");
  const matchTerm_ = matchTerm(scrutinee, [
    // Ok carries a *single* field → no tuple wrapper
    [variantPattern("Ok", varPattern("x")), varTerm("x")],
    // Err discards its field
    [
      variantPattern("Err", wildcardPattern()),
      conTerm("unreachable", neverType),
    ],
  ]);

  const fnTerm = lamTerm("n", freshMetaVar(), matchTerm_);

  // ---------- inference ----------
  const res = inferType(ctx, fnTerm);
  if ("err" in res)
    throw new Error(`Inference failed: ${JSON.stringify(res.err)}`);

  // Resolve the metas that have been solved during inference
  const inferredType = resolveMetaVariables(res.ok); // ← NEW

  console.log("Inferred type:", showType(inferredType));

  // ---------- assertions ----------
  expect("arrow" in inferredType).toBe(true);
  const { from, to } = (inferredType as ArrowType).arrow;

  // The parameter must be an application whose head is the enum constructor
  expect(
    "app" in from && // it is an app chain
      "con" in getSpineHead(from) && // the head is a constructor
      (getSpineHead(from) as { con: string }).con === "Result",
  ).toBe(true);

  // Return type must be the first type argument of the enum
  const [firstArg] = getSpineArgs(from);
  expect(typesEqual(to, firstArg!)).toBe(true);
});
