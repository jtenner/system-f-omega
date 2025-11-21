import {
  addType,
  conTerm,
  conType,
  freshState,
  inferType,
  projectTerm,
  recordTerm,
  showContext,
  showTerm,
  showType,
  starKind,
  tupleProjectTerm,
  tupleTerm,
  unwrap,
} from "../src";

async function main() {
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(addType(state, "Bool", starKind));
  console.log("Context:\n", showContext(state.ctx));

  // Record
  const person = recordTerm([
    ["name", conTerm("Alice", conType("String"))],
    ["age", conTerm("30", conType("Int"))],
  ]);
  const personType = unwrap(inferType(state, person));
  console.log("\nRecord:", showTerm(person));
  console.log("Type:", showType(personType)); // "{name: String, age: Int}"

  // Projection
  const ageProj = projectTerm(person, "age");
  const ageType = unwrap(inferType(state, ageProj));
  console.log("\nage →", showType(ageType)); // "Int"

  // Tuple
  const pair = tupleTerm([
    conTerm("1", conType("Int")),
    conTerm("true", conType("Bool")),
  ]);
  const pairType = unwrap(inferType(state, pair));
  console.log("\nTuple:", showTerm(pair));
  console.log("Type:", showType(pairType)); // "(Int, Bool)"

  // Tuple projection
  const proj0 = tupleProjectTerm(pair, 0);
  const proj0Type = unwrap(inferType(state, proj0));
  console.log("\nproj[0] →", showType(proj0Type)); // "Int"
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
