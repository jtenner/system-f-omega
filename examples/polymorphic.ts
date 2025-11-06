
import {
  inferType,
  showType,
  starKind,
  varType,
  tylamTerm,
  lamTerm,
  varTerm,
  tyapp_term,
  conType,
  Context,
} from "../src";

// Γ = · (empty context)
const ctx: Context = [];

// Λa::* . λx:a. x
const idPoly = tylamTerm(
  "a",
  starKind,
  lamTerm("x", varType("a"), varTerm("x")),
);

// Type inference
const idType = inferType(ctx, idPoly);
if ("err" in idType) throw new Error(JSON.stringify(idType.err, null, 2));

console.log("Polymorphic identity function:");
console.log(showType(idType.ok)); // ∀a::*.(a → a)

// Apply it to Int: (Λa. λx:a. x) [Int]
const appId = tyapp_term(idPoly, conType("Int"));
const appType = inferType(ctx, appId);
if ("err" in appType) throw new Error(JSON.stringify(appType.err, null, 2));

console.log("\nAfter type application:");
console.log(showType(appType.ok)); // Int → Int