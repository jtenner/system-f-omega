// example5.mjs
import {
  addType,
  arrowType,
  checkType,
  conType,
  forallType,
  freshState,
  inferType,
  lamTerm,
  showContext,
  showType,
  starKind,
  tyappTerm,
  tylamTerm,
  unwrap,
  varTerm,
  varType,
} from "../src";

async function main() {
  let state = freshState();
  state = unwrap(addType(state, "Int", starKind));
  state = unwrap(addType(state, "Bool", starKind));
  console.log("Context:\n", showContext(state.ctx));

  // Polymorphic id
  const polyId = tylamTerm(
    "a",
    starKind,
    lamTerm("x", varType("a"), varTerm("x")),
  );
  const polyType = unwrap(inferType(state, polyId));
  console.log("\nΛa.λx:a.x →", showType(polyType)); // "∀a::*. (a → a)"

  // Monomorphize
  const idInt = tyappTerm(polyId, conType("Int"));
  const idIntType = unwrap(inferType(state, idInt));
  console.log("\n[id]Int →", showType(idIntType)); // "(Int → Int)"

  // Check against forall
  const expected = forallType(
    "a",
    starKind,
    arrowType(varType("a"), varType("a")),
  );
  const checkRes = unwrap(checkType(state, polyId, expected));
  console.log("\nCheck ⇐ ∀a.a→a: ✅", showType(checkRes.type));
}

main().catch((e) => {
  console.error("Error:", e.message);
  process.exit(1);
});
