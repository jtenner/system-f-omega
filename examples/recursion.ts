import {
  Context,
  muType,
  variantType,
  tupleType,
  conType,
  unitType,
  foldTerm,
  unfoldTerm,
  injectTerm,
  inferType,
  showType,
} from "../src";

// μList.<Nil: (), Cons: (Int, List)>
const ListType = muType(
  "List",
  variantType([
    ["Nil", unitType],
    ["Cons", tupleType([conType("Int"), { var: "List" }])],
  ]),
);

const ctx: Context = [];

// fold[List](<Nil = ()>)
const nilVal = injectTerm("Nil", { tuple: [] }, ListType);
const foldedNil = foldTerm(ListType, nilVal);

const foldedType = inferType(ctx, foldedNil);
if ("err" in foldedType) throw new Error(JSON.stringify(foldedType.err, null, 2));

console.log("Folded List value:");
console.log(showType(foldedType.ok));

// unfold(foldedNil)
const unfolded = unfoldTerm(foldedNil);
const unfoldedType = inferType(ctx, unfolded);
if ("err" in unfoldedType) throw new Error(JSON.stringify(unfoldedType.err, null, 2));

console.log("\nUnfolded Type:");
console.log(showType(unfoldedType.ok));