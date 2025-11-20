// tests/helpers.ts
import type { TypeCheckerState } from "../src/types.js";

export function freshState(): TypeCheckerState {
  return {
    ctx: [],
    meta: { counter: 0, solutions: new Map(), kinds: new Map() },
  };
}
