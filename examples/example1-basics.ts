// example1-basics.mjs
import {
  addType,
  appTerm,
  arrowType,
  checkType,
  conTerm,
  conType,
  freshState,
  inferType,
  lamTerm,
  showContext,
  showType,
  starKind,
  unwrap,
  varTerm, // Add unwrapvarTerm
} from "../src";

async function main() {
  let state = freshState(); // Fresh always ok
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(addType(state, "Bool", starKind));
  console.log("Context:\n", showContext(state.ctx));

  // Lambda inference
  const id = lamTerm("x", conType("Int"), varTerm("x"));
  const idType = unwrap(inferType(state, id));
  console.log("\nλx:Int.x →", showType(idType)); // "(Int → Int)"

  // App inference
  const app = appTerm(id, conTerm("42", conType("Int")));
  const appType = unwrap(inferType(state, app));
  console.log("\napp →", showType(appType)); // "Int"

  // Check against expected
  const expected = arrowType(conType("Int"), conType("Bool"));
  // This throws an error because `Bool` mismatches `Int`
  const checkRes = unwrap(checkType(state, id, expected));
  console.log("\nCheck λx:Int.x ⇐ Int→Bool →", showType(checkRes.type)); // "(Int → Bool)"
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
