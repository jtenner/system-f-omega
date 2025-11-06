import {
  Context,
  injectTerm,
  matchTerm,
  variantPattern,
  varPattern,
  wildcardPattern,
  conTerm,
  conType,
  appType,
  inferType,
  showType,
  EnumDefBinding,
} from "../src";

// Define Option<a> enum
const OptionEnum: EnumDefBinding = {
  enum: {
    name: "Option",
    kind: { arrow: { from: { star: null }, to: { star: null } } },
    params: ["a"],
    variants: [
      ["Some", { var: "a" }],
      ["None", { tuple: [] }],
    ],
  },
};

// Context with enum definition
const ctx: Context = [{ enum: OptionEnum.enum }];

// <Some = 42> as Option<Int>
const optionIntType = appType(conType("Option"), conType("Int"));
const some42 = injectTerm("Some", conTerm("42", conType("Int")), optionIntType);

// Infer type
const someType = inferType(ctx, some42);
if ("err" in someType) throw new Error(JSON.stringify(someType.err, null, 2));

console.log("Option Injection:");
console.log(showType(someType.ok));

// Match expression
const matchExpr = matchTerm(some42, [
  [variantPattern("Some", varPattern("x")), conTerm("true", conType("Bool"))],
  [variantPattern("None", wildcardPattern()), conTerm("false", conType("Bool"))],
]);

// Infer match type
const matchType = inferType(ctx, matchExpr);
if ("err" in matchType) throw new Error(JSON.stringify(matchType.err, null, 2));

console.log("\nMatch Expression Type:");
console.log(showType(matchType.ok));