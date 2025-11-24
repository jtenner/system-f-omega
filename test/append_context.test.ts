// tests/append_context.test.ts

import { expect, test } from "bun:test";
import {
  addDict,
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
  lamTerm,
  matchTerm,
  muType,
  starKind,
  tuplePattern,
  tupleType,
  typeCheck,
  typesEqual,
  variantPattern,
  varPattern,
  varTerm,
  varType,
  wildcardPattern,
} from "../src/typechecker.ts";
import {
  type EnumDefBinding,
  freshState,
  type Result,
  showError,
  type TypeBinding,
  type TypingError,
} from "../src/types.ts";

function unwrap<T>(t: Result<TypingError, T>, message: string) {
  if ("err" in t) console.log(showError(t.err));
  expect("ok" in t, message).toBe(true);
  return (t as { ok: T }).ok;
}

test("addType: basic primitive", () => {
  const st = addType(freshState(), "Bool", starKind);
  expect("ok" in st).toBe(true);
  const state = unwrap(st, "Bool added");
  const binding = state.ctx.find((b) => "type" in b && b.type.name === "Bool");
  expect(binding).toBeTruthy();
  expect("type" in binding!).toBe(true);
  expect((binding as TypeBinding).type.kind).toStrictEqual({ star: null });
});

test("addType: duplicate fails", () => {
  const st1 = unwrap(addType(freshState(), "Int", starKind), "First Int");

  const st2 = addType(st1, "Int", starKind);
  expect("err" in st2 && "duplicate_binding" in st2.err).toBe(true);
});

test("addTypeAlias: accepts valid type alias", () => {
  const st = unwrap(addType(freshState(), "Int", starKind), "Int added.");

  const res = unwrap(
    addTypeAlias(st, "Id", ["A"], [starKind], varType("A")),
    "Id alias added.",
  );
  const ta = res.ctx.find(
    (t) => "type_alias" in t && t.type_alias.name === "Id",
  );
  expect(
    ta && "type_alias" in ta && ta.type_alias.params[0] === "A",
  ).toBeTruthy();
});

test("addTypeAlias: rejects unbound param", () => {
  const res = addTypeAlias(
    freshState(),
    "Bad",
    ["A"],
    [starKind],
    varType("B"),
  );
  expect("err" in res && "unbound" in res.err).toBe(true);
});

test("addTypeAlias: recursive alias (mu)", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  const res = addTypeAlias(
    st,
    "Stream",
    ["A"],
    [starKind],
    muType(
      "self",
      tupleType([varType("A"), appType(conType("Stream"), varType("A"))]),
    ),
  );
  unwrap(res, "Recursive Stream alias");
});

test("addEnum: simple Option<T>", () => {
  const st = freshState();
  const res = unwrap(
    addEnum(
      st,
      "Option",
      ["T"],
      [starKind],
      [
        ["None", tupleType([])],
        ["Some", varType("T")],
      ],
    ),
    "Option added",
  );
  expect(
    "enum" in res.ctx[0] &&
      res.ctx[0].enum.name === "Option" &&
      res.ctx[0].enum.recursive === false,
  ).toBe(true);
});

test("addEnum: non-recursive explicit false", () => {
  const st = unwrap(
    addType(freshState(), "Int", starKind),
    "Non-recursive enum",
  );
  const res = unwrap(
    addEnum(
      st,
      "NonRecEnum",
      [],
      [],
      [["Only", conType("Int")]],
      false, // explicit non-recursive
    ),
    "Non-recursive enum",
  );
  console.log(res.ctx);
  expect("enum" in res.ctx[1]).toBeTrue();
  expect((res.ctx[1] as EnumDefBinding).enum.recursive).toBe(false);
});

test("addEnum: recursive List<T> self-ref", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  const res = unwrap(
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
    "Recursive List",
  );
  expect(res.ctx.find((b) => "enum" in b)?.enum?.recursive).toBe(true);
});

test("addEnum: rejects wrong variant kind", () => {
  const res = addEnum(
    freshState(),
    "Bad",
    ["T"],
    [starKind],
    [["Case", { lam: { var: "X", kind: starKind, body: varType("X") } }]],
  );
  expect("err" in res && "kind_mismatch" in res.err).toBe(true);
});

test("addTerm: simple constant", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  const res = unwrap(
    addTerm(st, "fortyTwo", conTerm("42", conType("Int"))),
    "Constant added",
  );
  expect("term" in res.ctx[1] && res.ctx[1].term.name).toBe("fortyTwo");
});

test("addTerm: lambda", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  const res = addTerm(st, "id", lamTerm("x", conType("Int"), varTerm("x")));
  unwrap(res, "Lambda added");
});

test("addTerm: match on enum", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  st = unwrap(
    addEnum(
      st,
      "Option",
      ["T"],
      [starKind],
      [
        ["None", tupleType([])],
        ["Some", varType("T")],
      ],
    ),
    "Option",
  );
  const term = matchTerm(
    conTerm("xs", appType(conType("Option"), conType("Int"))),
    [
      [varPattern("x"), varTerm("x")], // wildcard-like
    ],
  );
  const res = addTerm(st, "unwrapOrX", term);
  unwrap(res, "Match added");
});

test("addTerm: rejects unbound var", () => {
  const res = addTerm(freshState(), "bad", varTerm("missing"));
  expect("err" in res && "unbound" in res.err).toBe(true);
});

test("addDict: basic dictionary", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  st = unwrap(addType(st, "Bool", starKind), "Bool");
  st = unwrap(
    addTraitDef(st, "Eq", "A", starKind, [
      ["eq", arrowType(varType("A"), conType("Bool"))],
    ]),
    "Eq trait",
  );
  const dt = dictTerm("Eq", conType("Int"), [
    ["eq", conTerm("eqInt", arrowType(conType("Int"), conType("Bool")))],
  ]);
  const res = unwrap(addDict(st, "intEq", dt), "Dict added");

  expect(
    res.ctx.find((b) => "dict" in b && b.dict.name === "intEq"),
  ).toBeTruthy();
});

test("addDict: rejects unbound trait", () => {
  const dt = dictTerm("MissingTrait", conType("Int"), [
    ["eq", conTerm("x", conType("Int"))],
  ]);
  const res = addDict(freshState(), "bad", dt);
  expect("err" in res && "unbound" in res.err).toBe(true);
});

test("addTraitDef: basic", () => {
  const st = unwrap(addType(freshState(), "Bool", starKind), "Bool");
  const res = addTraitDef(st, "Eq", "A", starKind, [
    ["eq", arrowType(varType("A"), arrowType(varType("A"), varType("Bool")))],
  ]);
  unwrap(res, "Eq trait def");
});

test("addTraitDef: HKT Functor", () => {
  const st = unwrap(
    addType(freshState(), "List", arrowKind(starKind, starKind)),
    "List HKT",
  );
  const res = addTraitDef(st, "Functor", "F", arrowKind(starKind, starKind), [
    [
      "map",
      // Proper HKT-applied form ∀A. F<A> → F<A> :: *
      forallType(
        "A",
        starKind,
        arrowType(
          appType(varType("F"), varType("A")),
          appType(varType("F"), varType("A")),
        ),
      ),
    ],
  ]);
  unwrap(res, "Functor HKT trait");
});

test("addTraitDef: rejects wrong method kind", () => {
  const st = freshState();
  // Method type with kind * → * (not *)
  const badMethodType = {
    lam: { var: "X", kind: starKind, body: varType("X") },
  };
  const res = addTraitDef(st, "Bad", "A", starKind, [["m", badMethodType]]);
  expect("err" in res && "kind_mismatch" in res.err).toBe(true);
});

test("addTraitImpl: requires trait def exists", () => {
  const st = unwrap(addType(freshState(), "Int", starKind), "Int");
  const dt = dictTerm("Eq", conType("Int"), [
    ["eq", conTerm("x", conType("Int"))],
  ]);
  const res = addTraitImpl(st, "Eq", conType("Int"), dt);
  expect("err" in res).toBe(true); // No Eq trait def
});

test("addTraitImpl: simple success", () => {
  let st = freshState();
  st = unwrap(addType(st, "String", starKind), "String");
  st = unwrap(addType(st, "Int", starKind), "Int");
  st = unwrap(
    addTraitDef(st, "Show", "A", starKind, [
      ["show", arrowType(varType("A"), conType("String"))],
    ]),
    "Show",
  );
  const dt = dictTerm("Show", conType("Int"), [
    ["show", conTerm("toString", arrowType(conType("Int"), conType("String")))],
  ]);
  unwrap(addTraitImpl(st, "Show", conType("Int"), dt), "Int Show impl");
});

test("addTraitImpl: missing method fails", () => {
  let st = freshState();
  st = unwrap(addType(st, "Bool", starKind), "Bool");
  st = unwrap(
    addTraitDef(st, "Ord", "A", starKind, [
      ["eq", arrowType(varType("A"), varType("Bool"))],
      ["lt", arrowType(varType("A"), varType("Bool"))],
    ]),
    "Ord",
  );
  const dt = dictTerm("Ord", conType("Bool"), [
    ["eq", conTerm("x", conType("Bool"))],
  ]); // Missing lt
  expect("err" in addTraitImpl(st, "Ord", conType("Bool"), dt)).toBe(true);
});

test("addTraitImpl: extra method allowed", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  st = unwrap(
    addTraitDef(st, "Show", "A", starKind, [
      ["show", arrowType(varType("A"), conType("Int"))],
    ]),
    "Show",
  );
  const dt = dictTerm("Show", conType("Int"), [
    ["show", conTerm("x", arrowType(conType("Int"), conType("Int")))],
    ["extra", conTerm("y", conType("Int"))], // Extra OK
  ]);
  unwrap(addTraitImpl(st, "Show", conType("Int"), dt), "Extra method OK");
});

test("enum + recursive List + match + mu", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int definable");
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
  const scrutinee = conTerm("xs", appType(conType("List"), conType("Int")));
  const term = matchTerm(scrutinee, [
    [varPattern("x"), conTerm("0", conType("Int"))],
    [
      variantPattern(
        "Cons",
        tuplePattern([varPattern("x"), wildcardPattern()]),
      ),
      varTerm("x"),
    ],
  ]);
  unwrap(addTerm(st, "headOrZero", term), "Match on recursive List");
});

// NEW: Test typechecking after adding bindings
test("typecheck uses new bindings", () => {
  let st = freshState();
  st = unwrap(addType(st, "Int", starKind), "Int");
  st = unwrap(
    addEnum(
      st,
      "Option",
      ["T"],
      [starKind],
      [
        ["None", tupleType([])],
        ["Some", varType("T")],
      ],
    ),
    "Option",
  );
  const term = conTerm("someInt", appType(conType("Option"), conType("Int")));
  const inferred = unwrap(typeCheck(st, term), "Inferred Option<Int>");
  expect(
    typesEqual(st, inferred, appType(conType("Option"), conType("Int"))),
  ).toBe(true);
});
