// tests/append_context.test.ts
import { expect, test } from "bun:test";
import {
  addEnum,
  addTerm,
  addTraitDef,
  addTraitImpl,
  addType,
  addTypeAlias,
  appType,
  arrowKind,
  arrowType,
  conTerm,
  conType,
  dictTerm,
  forallType,
  matchTerm,
  showError,
  starKind,
  tuplePattern,
  tupleType,
  typesEqual,
  variantPattern,
  varPattern,
  varTerm,
  varType,
  wildcardPattern,
} from "../src/typechecker.ts";
import type { Result, TypeCheckerState, TypingError } from "../src/types.ts";
import { freshState } from "./helpers.ts";

function unwrap<T>(t: Result<TypingError, T>, message: string) {
  if ("err" in t) console.log(showError(t.err));
  expect("ok" in t, message).toBe(true);
  return (t as { ok: T }).ok;
}

test("addTypeAlias: accepts valid type alias", () => {
  const st = addType(freshState(), "Int", starKind);
  expect("ok" in st).toBeTrue();
  const res = addTypeAlias(
    (st as { ok: TypeCheckerState }).ok,
    "MyAlias",
    ["A"],
    [starKind],
    arrowType(varType("A"), conType("Int")),
  );
  console.log(res);
  expect("ok" in res && res.ok.ctx.length > 0).toBe(true);
  const ta = (res as { ok: TypeCheckerState }).ok.ctx.find(
    (t) => "type_alias" in t && t.type_alias.name === "MyAlias",
  );
  expect(ta).toBeTruthy();
});

test("addTypeAlias: rejects wrong kind", () => {
  const st = freshState();

  // body uses a free type variable B :: *, but B is not bound
  const res = addTypeAlias(st, "Bad", ["A"], [starKind], varType("B"));

  expect("err" in res).toBe(true);
});

test("addEnum: simple Option<T>", () => {
  const st = freshState();

  const res = addEnum(
    st,
    "Option",
    ["T"],
    [starKind],
    [
      ["None", tupleType([])], // ()
      ["Some", varType("T")],
    ],
  );

  expect(
    "ok" in res &&
      res.ok.ctx.length === 1 &&
      "enum" in res.ok.ctx[0] &&
      res.ok.ctx[0].enum.name === "Option",
  ).toBeTrue();
});

test("addEnum: rejects enum when variant type has wrong kind", () => {
  const st = freshState();

  const res = addEnum(
    st,
    "BadEnum",
    ["T"],
    [starKind],
    [
      ["Case", { lam: { var: "X", kind: starKind, body: varType("X") } }], // kind = * -> *
    ],
  );

  expect("err" in res).toBe(true);
});

test("addTerm: adding simple constant", () => {
  const st = freshState();

  const t = conTerm("42", conType("Int"));

  const res = addTerm(st, "x", t);
  expect(
    "ok" in res &&
      res.ok.ctx.length === 1 &&
      "term" in res.ok.ctx[0] &&
      typesEqual(res.ok, res.ok.ctx[0].term.type, conType("Int")),
  ).toBe(true);
});

test("addTerm: rejects invalid term", () => {
  const st = freshState();

  // Type mismatch - 42 : Int, but usage requires something else
  const t = {
    lam: {
      arg: "x",
      type: conType("Bool"),
      body: conTerm("42", conType("Int")),
    },
  };

  const res = addTerm(st, "bad", t);
  expect("err" in res).toBe(true);
});

test("addTraitDef: basic Eq<A>", () => {
  const st = unwrap(
    addType(freshState(), "Bool", starKind),
    "Bool should be definable",
  );

  const res = addTraitDef(st, "Eq", "A", starKind, [
    ["eq", arrowType(varType("A"), arrowType(varType("A"), varType("Bool")))],
  ]);

  console.log(res);
  expect("ok" in res).toBe(true);
});

test("addTraitDef: rejects method with wrong kind", () => {
  const st = freshState();

  const res = addTraitDef(st, "T", "F", arrowKind(starKind, starKind), [
    ["m", varType("F")], // method type must be *, not * -> *
  ]);

  expect("err" in res).toBe(true);
});

test("addTraitImpl: simple implementation", () => {
  let st = freshState();
  // add definition for String first
  st = unwrap(addType(st, "String", starKind), "String should be definable");
  st = unwrap(addType(st, "Int", starKind), "Int should be definable");
  // First add trait def: Show<A> { show : A -> String }
  st = unwrap(
    addTraitDef(st, "Show", "A", starKind, [
      ["show", arrowType(varType("A"), conType("String"))],
    ]),
    "Show should be definable",
  );

  // Implement for Int
  const dt = dictTerm("Show", conType("Int"), [
    [
      "show",
      conTerm("toStringInt", arrowType(conType("Int"), conType("String"))),
    ],
  ]);

  const res = addTraitImpl(st, "Show", conType("Int"), dt);
  console.log(res);
  expect("ok" in res).toBe(true);
});

test("addTraitImpl: polymorphic List functor implementation", () => {
  let st = freshState();

  // List :: * -> *
  st = unwrap(
    addType(st, "List", arrowKind(starKind, starKind)),
    "List definable",
  );
  st = unwrap(addType(st, "Int", starKind), "Int definable");

  // Functor<F> { map : ∀A.∀B.(A→B) → F<A> → F<B> }
  st = unwrap(
    addTraitDef(st, "Functor", "F", arrowKind(starKind, starKind), [
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
    ]),
    "Functor definable",
  );

  // Correct polymorphic implementation of map
  const polyMapImpl = conTerm(
    "mapList",
    forallType(
      "A",
      starKind,
      forallType(
        "B",
        starKind,
        arrowType(
          arrowType(varType("A"), varType("B")),
          arrowType(
            appType(conType("List"), varType("A")),
            appType(conType("List"), varType("B")),
          ),
        ),
      ),
    ),
  );

  const dt = dictTerm("Functor", conType("List"), [["map", polyMapImpl]]);

  const res = addTraitImpl(st, "Functor", conType("List"), dt);

  if ("err" in res) console.log(showError(res.err));
  expect("ok" in res).toBe(true);
});

test("addTraitImpl: Ord impl missing method", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int definable");
  st = unwrap(addType(st, "Bool", starKind), "Bool definable");

  st = unwrap(
    addTraitDef(st, "Ord", "A", starKind, [
      ["eq", arrowType(varType("A"), arrowType(varType("A"), varType("Bool")))],
      ["lt", arrowType(varType("A"), arrowType(varType("A"), varType("Bool")))],
    ]),
    "Ord definable",
  );

  // Missing lt!
  const dt = dictTerm("Ord", conType("Int"), [
    [
      "eq",
      conTerm(
        "eqInt",
        arrowType(conType("Int"), arrowType(conType("Int"), conType("Bool"))),
      ),
    ],
  ]);

  const res = addTraitImpl(st, "Ord", conType("Int"), dt);
  expect("err" in res).toBe(true);
});

test("enum + recursive List + match + mu", () => {
  let st = freshState();

  st = unwrap(addType(st, "Int", starKind), "Int definable");

  // Define enum List<T> = Nil | Cons(T, List<T>)
  st = unwrap(
    addEnum(
      st,
      "List",
      ["T"],
      [starKind],
      [
        ["Nil", tupleType([])],
        [
          "Cons",
          tupleType([varType("T"), appType(conType("List"), varType("T"))]),
        ],
      ],
      true,
    ),
    "List definable",
  );

  // A match expression:
  // match xs {
  //   Nil => 0
  //   Cons(x, _) => x
  // }
  const scrutinee = conTerm("Nil", appType(conType("List"), conType("Int")));

  const term = matchTerm(scrutinee, [
    [variantPattern("Nil", tuplePattern([])), conTerm("0", conType("Int"))],
    [
      variantPattern(
        "Cons",
        tuplePattern([varPattern("x"), wildcardPattern()]),
      ),
      varTerm("x"),
    ],
  ]);

  const res = addTerm(st, "headOrZero", term);
  console.log(res);
  expect("ok" in res).toBe(true);
});
