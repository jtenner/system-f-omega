import { describe, expect, it } from "bun:test";
import { evaluate, showValue, typecheckAndEvaluate } from "../src/eval.js";
import {
  appTerm,
  arrowType,
  conTerm,
  dictTerm,
  foldTerm,
  injectTerm,
  lamTerm,
  letTerm,
  matchTerm,
  muType,
  projectTerm,
  recordTerm,
  starKind,
  traitMethodTerm,
  tupleProjectTerm,
  tupleTerm,
  tupleType,
  unfoldTerm,
  unitType,
  unitValue,
  variantPattern,
  variantType,
  varPattern,
  varTerm,
  varType,
} from "../src/typechecker.ts"; // Adjust path if needed
import {
  freshState,
  type Result,
  showType,
  type Term,
  type Type,
} from "../src/types.js";

const expectOk = <T>(val: Result<unknown, T>) => {
  if ("err" in val) console.error(val.err);
  expect("ok" in val).toBe(true);
  return (val as { ok: T }).ok;
};

const expectErr = <T>(val: Result<T, unknown>) => {
  if ("ok" in val) console.error(val.ok);
  expect("err" in val).toBe(true);
  return (val as { err: T }).err;
};

describe("Interpreter", () => {
  it("evaluates identity function application", () => {
    const term: Term = appTerm(
      lamTerm("x", unitType, varTerm("x")),
      conTerm("hello", unitType),
    );
    const result = expectOk(
      evaluate(term, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(showValue(result)).toBe("hello");
  });

  it("evaluates record projection", () => {
    const term: Term = projectTerm(
      recordTerm([["f", conTerm("42", unitType)]]),
      "f",
    );
    const result = expectOk(
      evaluate(term, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(showValue(result)).toBe("42");
  });

  it("evaluates tuple projection", () => {
    const term: Term = tupleProjectTerm(
      tupleTerm([conTerm("1", unitType), conTerm("2", unitType)]),
      0,
    );
    const result = expectOk(
      evaluate(term, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(showValue(result)).toBe("1");
  });

  it("evaluates variant injection and match", () => {
    const variant: Term = injectTerm("Left", conTerm("5", unitType), unitType);
    const match: Term = matchTerm(variant, [
      [variantPattern("Left", varPattern("x")), varTerm("x")],
      [variantPattern("Right", varPattern("y")), varTerm("y")],
    ]);
    const result = expectOk(
      evaluate(match, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(showValue(result)).toBe("5");
  });

  it("evaluates let binding", () => {
    const term: Term = letTerm("x", conTerm("10", unitType), varTerm("x"));
    const result = expectOk(
      evaluate(term, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(showValue(result)).toBe("10");
  });

  it("evaluates fold/unfold", () => {
    const muT: Type = muType(
      "L",
      variantType([
        ["Nil", unitType],
        ["Cons", tupleType([varType("L"), unitType])],
      ]),
    );
    const nil: Term = foldTerm(muT, injectTerm("Nil", unitValue, muT));
    const unfolded = unfoldTerm(nil);
    const result = expectOk(
      evaluate(unfolded, freshState(), { strict: true, maxSteps: 100 }),
    );
    expect(showValue(result)).toContain("Nil"); // Or equivalent
  });

  it("errors on unbound variable during evaluation", () => {
    const term: Term = varTerm("unknown");
    const result = expectErr(
      evaluate(term, freshState(), { strict: true, maxSteps: 100 }),
    );

    expect(result).toContain("Unbound variable");
  });

  it("errors on max steps exceeded", () => {
    // Infinite loop example: (\x -> x x) (\x -> x x)
    const omega = appTerm(
      lamTerm("x", unitType, appTerm(varTerm("x"), varTerm("x"))),
      lamTerm("x", unitType, appTerm(varTerm("x"), varTerm("x"))),
    );
    const result = expectErr(
      evaluate(omega, freshState(), { strict: true, maxSteps: 5 }),
    );

    expect(result).toContain("exceeded maximum steps");
  });
});

describe("Integration: Typecheck + Evaluate", () => {
  it("typechecks and evaluates simple app successfully", () => {
    const ctx = freshState();
    const term: Term = appTerm(
      lamTerm("x", unitType, varTerm("x")),
      conTerm("world", unitType),
    );
    const result = expectOk(typecheckAndEvaluate(term, ctx));

    expect(showType(result.type)).toBe("()"); // Unit
    expect(showValue(result.value)).toBe("world");
  });

  it("fails typecheck before evaluation", () => {
    const ctx = freshState();
    const term: Term = appTerm(
      conTerm("1", varType("Int")),
      conTerm("true", varType("Bool")),
    );
    const result = expectErr(typecheckAndEvaluate(term, ctx));

    expect(result).toContain("Type error");
  });

  it("handles trait method evaluation (simple dict)", () => {
    const ctx = freshState([
      { type: { kind: starKind, name: "String" } },
      { type: { kind: starKind, name: "Int" } },
      {
        trait_def: {
          name: "Show",
          type_param: "T",
          kind: starKind,
          methods: [["show", arrowType(varType("T"), varType("String"))]],
        },
      },
    ]);
    const dict: Term = dictTerm("Show", varType("Int"), [
      ["show", lamTerm("x", varType("Int"), conTerm("int", varType("String")))],
    ]);
    const methodCall: Term = appTerm(
      traitMethodTerm(dict, "show"),
      conTerm("42", varType("Int")),
    );
    const result = expectOk(typecheckAndEvaluate(methodCall, ctx));
    // Assuming showType(varType("String")) === "String"
    expect(showType(result.type)).toBe("String");
    // Evaluation applies the lam in the dict method, yielding "int"
    expect(showValue(result.value)).toBe("int");
  });
});
