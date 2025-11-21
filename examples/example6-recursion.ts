// example6.mjs
import {
  addEnum,
  addType,
  appType,
  conType,
  foldTerm,
  freshState,
  inferType,
  injectTerm,
  showContext,
  showTerm,
  showType,
  starKind,
  tupleType,
  unfoldTerm,
  unwrap,
} from "../src";

async function main() {
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(
    addEnum(
      state,
      "List",
      ["T"],
      [starKind],
      [
        ["Nil", tupleType([])],
        [
          "Cons",
          tupleType([conType("T"), appType(conType("List"), { var: "T" })]),
        ],
      ],
      true,
    ),
  ); // recursive=true
  console.log("Context:\n", showContext(state.ctx));

  // List<Int> normalizes to μ
  const listInt = appType(conType("List"), conType("Int"));
  console.log("\nList<Int>:", showType(listInt));

  // Nil injection + fold
  const nil = injectTerm("Nil", { tuple: [] }, listInt);
  const foldedNil = foldTerm(listInt, nil);
  const foldedType = unwrap(inferType(state, foldedNil));
  console.log("\nfold Nil:", showTerm(foldedNil));
  console.log("Type:", showType(foldedType)); // "List<Int>"

  // Unfold
  const unfolded = unfoldTerm(foldedNil);
  const unfoldedType = unwrap(inferType(state, unfolded));
  console.log("\nunfold →", showType(unfoldedType)); // "(⊥, List<Int>)"
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
