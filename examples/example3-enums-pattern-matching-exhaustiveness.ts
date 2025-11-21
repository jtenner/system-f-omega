// example3.mjs
import {
  addEnum,
  addType,
  appType,
  checkExhaustive,
  conTerm,
  conType,
  freshState,
  inferType,
  injectTerm,
  matchTerm,
  showContext,
  showTerm,
  showType,
  starKind,
  tupleType,
  unwrap,
  variantPattern,
  varPattern,
  varTerm,
  wildcardPattern,
} from "../src";

async function main() {
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(addType(state, "Bool", starKind));
  state = unwrap(
    addEnum(
      state,
      "Option",
      ["T"],
      [starKind],
      [
        ["None", tupleType([])],
        ["Some", conType("T")],
      ],
    ),
  );
  console.log("Context:\n", showContext(state.ctx));

  // Enum app
  const optInt = appType(conType("Option"), conType("Int"));
  console.log("\nOption<Int>:", showType(optInt));

  // Injection
  const some42 = injectTerm("Some", conTerm("42", conType("Int")), optInt);
  const someType = unwrap(inferType(state, some42));
  console.log("\nSome(42):", showTerm(some42));
  console.log("Type:", showType(someType)); // "Option<Int>"

  // Match (exhaustive)
  const match = matchTerm(some42, [
    [variantPattern("None", wildcardPattern()), conTerm("0", conType("Int"))],
    [variantPattern("Some", varPattern("x")), varTerm("x")],
  ]);
  const matchType = unwrap(inferType(state, match));
  console.log("\nMatch:", showTerm(match));
  console.log("Type:", showType(matchType)); // "Int"

  // Exhaustiveness check
  try {
    unwrap(
      checkExhaustive(
        state,
        [
          variantPattern("None", wildcardPattern()),
          variantPattern("Some", varPattern("x")),
        ],
        optInt,
      ),
    );
    console.log("\nExhaustive: ✅");
  } catch (e) {
    console.log("\nExhaustive: ❌", (e as Error).message);
  }
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
