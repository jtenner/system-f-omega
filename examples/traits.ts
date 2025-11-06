
import {
  Context,
  traitMethodTerm,
  dictTerm,
  lamTerm,
  varTerm,
  conType,
  arrowType,
  inferType,
  showType,
  starKind,
  TraitDefBinding,
} from "../src";

// Trait definition: Eq<Self> with eq : Self → Self → Bool
const eqTrait: TraitDefBinding = {
  trait_def: {
    name: "Eq",
    type_param: "Self",
    kind: { arrow: { from: starKind, to: starKind } },
    methods: [
      ["eq", arrowType(conType("Self"), arrowType(conType("Self"), conType("Bool")))],
    ],
  },
};

// Implementation (dictionary) for Eq<Int>
const eqIntDict = dictTerm("Eq", conType("Int"), [
  [
    "eq",
    lamTerm(
      "x",
      conType("Int"),
      lamTerm("y", conType("Int"), varTerm("true")),
    ),
  ],
]);

// Context includes trait def + implementation
const ctx: Context = [
  eqTrait,
  { trait_impl: { trait: "Eq", type: conType("Int"), dict: eqIntDict } },
];

// Access the method eq from the dictionary
const eqAccess = traitMethodTerm(varTerm("d"), "eq");

// Show dictionary type directly
const dictType = inferType(ctx, eqIntDict);
if ("err" in dictType) throw new Error(JSON.stringify(dictType.err, null, 2));

console.log("Dictionary Type:");
console.log(showType(dictType.ok));

// Demonstrate direct trait lookup via method term
const app = traitMethodTerm(eqIntDict, "eq");
const appType = inferType(ctx, app);
if ("err" in appType) throw new Error(JSON.stringify(appType.err, null, 2));

console.log("\nTrait method type:");
console.log(showType(appType.ok));