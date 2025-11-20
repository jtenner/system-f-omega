import { describe, expect, it } from "bun:test";
import {
  arrowType,
  conType,
  enumDefBinding,
  importModule,
  normalizeType,
  showError,
  showType,
  starKind,
  termBinding,
  traitDefBinding,
  typeAliasBinding,
  typeBinding,
  typesEqual,
} from "../src/typechecker.js";
import {
  type Binding,
  state,
  type Type,
  type TypeCheckerState,
  type TypingError,
} from "../src/types.js";

// Helpers
function ctx(...bindings: Binding[]) {
  return state(bindings);
}

function expectTypeEqual(state: TypeCheckerState, left: Type, right: Type) {
  const normLeft = normalizeType(state, left); // Assume normalizeType if needed
  const normRight = normalizeType(state, right);
  if (!typesEqual(state, normLeft, normRight)) {
    throw new Error(
      `Types not equal:\n  Left:  ${showType(normLeft)}\n  Right: ${showType(normRight)}`,
    );
  }
  return true;
}

// Test Suite
describe("Module Imports", () => {
  it("basic import - simple type", () => {
    const A = ctx(typeBinding("T", starKind));
    const B = ctx();

    const res = importModule({ from: A, into: B, roots: ["T"] });
    expect(
      "ok" in res && res.ok.ctx.some((b) => "type" in b && b.type.name === "T"),
    ).toBe(true);
  });

  it("basic import - type alias", () => {
    const A = ctx(typeAliasBinding("Int32", [], [], conType("I32")));
    const B = ctx();

    const res = importModule({ from: A, into: B, roots: ["Int32"] });
    expect(
      "ok" in res &&
        res.ok.ctx.some(
          (b) => "type_alias" in b && b.type_alias.name === "Int32",
        ),
    ).toBe(true);
  });

  it("basic import - term with alias", () => {
    const A = ctx(
      typeAliasBinding("I32", [], [], conType("Int")),
      termBinding("add", arrowType(conType("I32"), conType("I32"))),
    );
    const B = ctx();

    const res = importModule({ from: A, into: B, roots: ["add"] });
    expect("ok" in res).toBe(true);

    const C = (res as { ok: TypeCheckerState }).ok;
    const add = C.ctx.find((b) => "term" in b && b.term.name === "add");
    expect(
      add &&
        "term" in add &&
        expectTypeEqual(
          C,
          add!.term.type,
          arrowType(conType("Int"), conType("Int")),
        ),
    ).toBeTrue();
  });

  describe("Root Conflicts", () => {
    it("root conflict - type", () => {
      const A = ctx(typeBinding("T", starKind));
      const B = ctx(typeBinding("T", starKind)); // Conflicts

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"],
        allowOverrides: false,
      });

      expect(
        "err" in res &&
          "duplicate_binding" in res.err &&
          res.err.duplicate_binding.name === "T",
      ).toBe(true);
    });

    it("root conflict resolved by user alias", () => {
      const A = ctx(typeBinding("T", starKind));
      const B = ctx(typeBinding("T", starKind)); // Conflicts

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"],
        aliases: { types: { T: "T2" } },
        allowOverrides: false,
      });

      expect(
        "ok" in res &&
          res.ok.ctx.some((b) => "type" in b && b.type.name === "T2"),
      ).toBe(true);
    });

    it("root override allowed", () => {
      const A = ctx(typeBinding("T", starKind));
      const B = ctx(typeBinding("T", starKind)); // Will be overridden

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"],
        allowOverrides: true,
      });
      // Check that A's binding replaced B's (order reversed or use showBinding)

      expect(
        "ok" in res &&
          res.ok.ctx.filter((b) => "type" in b && b.type.name === "T")
            .length === 1,
      ).toBe(true); // Override succeeded
    });
  });

  describe("Dependency Auto-Renaming", () => {
    it("hidden dependency auto-renamed (no root conflict)", () => {
      const A = ctx(
        // Hidden dep: U
        typeBinding("U", starKind),
        // Root: T depends on U
        termBinding("T", arrowType(conType("U"), conType("U"))),
      );
      const B = ctx(
        // Conflicts with hidden "U"
        typeBinding("U", starKind),
      );

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"], // Root "T" doesn't conflict
        allowOverrides: false,
      });
      expect("err" in res).toBe(false);

      const C = (res as { ok: TypeCheckerState }).ok;
      // U got auto-renamed (e.g., to U_1)
      expect(C.ctx.some((b) => "type" in b && b.type.name.includes("U_"))).toBe(
        true,
      );
      // T imported successfully
      const t = C.ctx.find((b) => "term" in b && b.term.name === "T")!;
      // t's type uses the renamed U, but semantically it's correct
      expect("term" in t && showType(t.term.type)).toContain("U_"); // Or use typesEqual if normalized
    });

    it("dependency conflict with root success - error if root conflicts", () => {
      const A = ctx(
        typeBinding("U", starKind), // Hidden
        termBinding("T", conType("U")), // Root depends on U
      );
      const B = ctx(
        typeBinding("T", starKind), // Conflicts with root "T"
        typeBinding("U", starKind), // Would auto-rename, but root fails first
      );

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"],
        allowOverrides: false,
      });

      expect(
        "err" in res &&
          "duplicate_binding" in res.err &&
          res.err.duplicate_binding.name === "T",
      ).toBe(true);

      // Success case: no root conflict
      const B2 = ctx(typeBinding("U", starKind)); // Only dep conflict
      const res2 = importModule({
        from: A,
        into: B2,
        roots: ["T"],
        allowOverrides: false,
      });
      expect("err" in res2).toBe(false); // U auto-renamed to U_1
    });
  });

  describe("Circular Imports", () => {
    it("detect circular import - simple cycle", () => {
      const A = ctx(
        typeAliasBinding("A", [], [], conType("B")),
        typeAliasBinding("B", [], [], conType("A")),
      );

      const res = importModule({
        from: A,
        into: ctx(),
        roots: ["A"],
      });

      expect(
        "err" in res &&
          "circular_import" in res.err &&
          res.err.circular_import.cycle.includes("A"),
      ).toBe(true);
    });

    it("circular import - no error if cycle not reached", () => {
      const A = ctx(
        // Unrelated chain: C → D (no cycle)
        typeAliasBinding("C", [], [], conType("D")),
        typeAliasBinding("D", [], [], conType("Int")), // Terminates (Int is primitive)

        // Isolated cycle that's NOT reachable from "C" (intentionally unrelated)
        typeAliasBinding("X", [], [], conType("Y")), // Separate cycle: X → Y → Z → X
        typeAliasBinding("Y", [], [], conType("Z")),
        typeAliasBinding("Z", [], [], conType("X")),
      );

      const res = importModule({
        from: A,
        into: ctx(),
        roots: ["C"], // Reaches only C → D → Int (no cycle)
      });

      expect("err" in res).toBe(false); // Cycle X→Y→Z→X not reached

      // Verify only relevant deps imported (C, D, but not X,Y,Z cycle)
      const C = (res as { ok: TypeCheckerState }).ok;
      expect(
        C.ctx.some((b) => "type_alias" in b && b.type_alias?.name === "C"),
      ).toBe(true);
      expect(
        C.ctx.some((b) => "type_alias" in b && b.type_alias?.name === "D"),
      ).toBe(true);
      // Cycle not imported (not reachable)
      expect(
        C.ctx.some((b) => "type_alias" in b && b.type_alias?.name === "X"),
      ).toBe(false);
    });
  });

  describe("Complex Imports: Traits, Enums, Aliases", () => {
    it("import enum with variants", () => {
      const A = ctx(
        enumDefBinding(
          "Option",
          starKind, // * → * (one param, simplified)
          ["T"],
          [
            ["None", { tuple: [] }],
            ["Some", conType("T")],
          ],
        ),
      );
      const B = ctx();

      const res = importModule({ from: A, into: B, roots: ["Option"] });
      expect("err" in res).toBe(false);
      const e = (res as { ok: TypeCheckerState }).ok.ctx.find(
        (b) => "enum" in b,
      );
      expect(e).toBeDefined();
      expect(e!.enum.variants.map((v) => v[0])).toEqual(["None", "Some"]);
    });

    it("import trait definition", () => {
      const A = ctx(
        traitDefBinding("Show", "Self", starKind, [
          ["toString", arrowType(conType("Self"), conType("String"))],
        ]),
      );
      const B = ctx();

      const res = importModule({ from: A, into: B, roots: ["Show"] });
      expect("err" in res).toBe(false);
      const t = (res as { ok: TypeCheckerState }).ok.ctx.find(
        (b) => "trait_def" in b,
      );
      expect(t).toBeDefined();
      expect(t!.trait_def.name).toBe("Show");
    });

    it("import alias that depends on imported type", () => {
      const A = ctx(
        typeBinding("Int", starKind),
        typeAliasBinding(
          "Vec",
          ["N"],
          [starKind],
          arrowType(conType("N"), conType("Int")),
        ),
      );
      const B = ctx();

      const res = importModule({ from: A, into: B, roots: ["Vec"] });
      expect("err" in res).toBe(false);
      // Dependency "Int" also imported
      expect(
        (res as { ok: TypeCheckerState }).ok.ctx.some(
          (b) => "type" in b && b.type.name === "Int",
        ),
      ).toBe(true);
    });

    it("user alias renames enum variant labels", () => {
      const A = ctx(
        enumDefBinding(
          "Color",
          starKind,
          [],
          [
            ["Red", { tuple: [] }],
            ["Blue", { tuple: [] }],
          ],
        ),
      );
      const B = ctx();

      const res = importModule({
        from: A,
        into: B,
        roots: ["Color"],
        aliases: { labels: { Red: "Crimson", Blue: "Azure" } },
      });
      expect("err" in res).toBe(false);
      const e = (res as { ok: TypeCheckerState }).ok.ctx.find(
        (b) => "enum" in b,
      )!.enum;
      const labels = e.variants.map((v) => v[0]);
      expect(labels).toEqual(["Crimson", "Azure"]);
    });
  });

  describe("allowOverrides Behavior", () => {
    it("allowOverrides replaces existing root", () => {
      const A = ctx(typeBinding("T", starKind));
      const B = ctx(typeBinding("T", starKind)); // Existing T

      const res = importModule({
        from: A,
        into: B,
        roots: ["T"],
        allowOverrides: true,
      });
      expect("err" in res).toBe(false);
      // Only one T (overridden)
      const ts = (res as { ok: TypeCheckerState }).ok.ctx.filter(
        (b) => "type" in b && b.type.name === "T",
      );
      expect(ts.length).toBe(1);
    });

    it("allowOverrides on non-conflicting import", () => {
      const A = ctx(typeBinding("U", starKind)); // No conflict
      const B = ctx();

      const res = importModule({
        from: A,
        into: B,
        roots: ["U"],
        allowOverrides: true, // Irrelevant here
      });

      expect("ok" in res && res.ok.ctx.length === 1).toBe(true); // Just appended
    });
  });

  describe("Error Pretty-Printing", () => {
    it("pretty-print duplicate binding", () => {
      const A = ctx(typeBinding("T", starKind));
      const B = ctx(typeBinding("T", starKind));

      const res = importModule({ from: A, into: B, roots: ["T"] });
      expect("err" in res).toBe(true);
      const msg = showError((res as { err: TypingError }).err);
      expect(msg).toContain("Duplicate binding for 'T'");
      expect(msg).toContain("Existing:");
      expect(msg).toContain("Incoming:");
    });

    it("pretty-print circular import", () => {
      const A = ctx(
        typeAliasBinding("A", [], [], conType("B")),
        typeAliasBinding("B", [], [], conType("A")),
      );

      const res = importModule({ from: A, into: ctx(), roots: ["A"] });
      expect("err" in res).toBe(true);
      const msg = showError((res as { err: TypingError }).err);
      expect(msg).toContain("Circular import detected");
      expect(msg).toContain("Cycle: A → B");
    });
  });
});
