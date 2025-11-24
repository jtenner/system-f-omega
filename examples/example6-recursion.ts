// example6.mjs
import {
  addType,
  conTerm,
  conType,
  foldTerm,
  freshState,
  inferType,
  muType,
  showContext,
  showTerm,
  showType,
  starKind,
  tupleTerm,
  tupleType,
  unfoldTerm,
  unwrap,
  varType,
} from "../src";

async function main() {
  // 1. Set up basic types
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  console.log("Context:\n", showContext(state.ctx));

  // 2. Define a concrete recursive list type:
  //    μL. (Int, L)
  const intListMu = muType("L", tupleType([conType("Int"), varType("L")]));
  console.log("\nList μ type:", showType(intListMu)); // "μL.(Int, L)"

  // 3. Build a value matching the unfolded body: (Int, μL.(Int, L))
  //    Here, we'll use a dummy tail: foldedNil (defined after fold below)
  const dummyTail = conTerm("nil", intListMu); // Pretend we had a proper list; typechecker only sees IntList type

  const head = conTerm("1", conType("Int"));
  const consTuple = tupleTerm([head, dummyTail]);

  // 4. fold[μL.(Int, L)]((1, dummyTail))
  const folded = foldTerm(intListMu, consTuple);
  const foldedType = unwrap(inferType(state, folded));
  console.log("\nfold:", showTerm(folded));
  console.log("fold type:", showType(foldedType)); // μL.(Int, L)

  // 5. unfold(folded) : (Int, μL.(Int, L))
  const unfolded = unfoldTerm(folded);
  const unfoldedType = unwrap(inferType(state, unfolded));
  console.log("\nunfold:", showTerm(unfolded));
  console.log("unfold type:", showType(unfoldedType)); // "(Int, μL.(Int, L))"
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
