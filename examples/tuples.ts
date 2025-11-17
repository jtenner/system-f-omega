import {
  tupleTerm,
  tupleProjectTerm,
  inferType,
  showType,
  conTerm,
  conType,
  Context,
  state,
} from "../src";

// Tuple: #(42, true)
const pair = tupleTerm([
  conTerm("42", conType("Int")),
  conTerm("true", conType("Bool")),
]);

const ctx = state();

// Infer type of tuple
const pairType = inferType(ctx, pair);
if ("err" in pairType) throw new Error(JSON.stringify(pairType.err, null, 2));

console.log("Tuple Type:");
console.log(showType(pairType.ok));

// Project element 0
const firstProj = tupleProjectTerm(pair, 0);
const firstType = inferType(ctx, firstProj);
if ("err" in firstType) throw new Error(JSON.stringify(firstType.err, null, 2));

console.log("\nProjection Type:");
console.log(showType(firstType.ok));