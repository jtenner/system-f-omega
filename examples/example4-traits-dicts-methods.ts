// example4.mjs
import {
  addDict,
  addTraitDef,
  addTraitImpl,
  addType,
  arrowType,
  conTerm,
  conType,
  dictTerm,
  freshState,
  inferType,
  lamTerm,
  showContext,
  showType,
  starKind,
  traitMethodTerm,
  unwrap,
} from "../src";

async function main() {
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(addType(state, "Bool", starKind));
  state = unwrap(
    addTraitDef(state, "Eq", "A", starKind, [
      ["eq", arrowType(conType("A"), arrowType(conType("A"), conType("Bool")))],
    ]),
  );
  console.log("Context:\n", showContext(state.ctx));

  // Eq<Int> dict
  const eqDict = dictTerm("Eq", conType("Int"), [
    [
      "eq",
      lamTerm(
        "x",
        conType("Int"),
        lamTerm("y", conType("Int"), conTerm("true", conType("Bool"))),
      ),
    ],
  ]);
  state = unwrap(addTraitImpl(state, "Eq", conType("Int"), eqDict));
  state = unwrap(addDict(state, "eqInt", eqDict));

  // Method access
  const eqMethod = traitMethodTerm({ var: "eqInt" }, "eq");
  const eqMethodType = unwrap(inferType(state, eqMethod));
  console.log("\neqInt.eq →", showType(eqMethodType)); // "(Int → (Int → Bool))"

  console.log("\nFull context:\n", showContext(state.ctx));
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
