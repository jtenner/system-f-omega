// Trait constraint
export type TraitConstraint = {
  trait: string;
  type: Type;
};

// Add to Type union
export type BoundedForallType = {
  bounded_forall: {
    var: string;
    kind: Kind;
    constraints: TraitConstraint[];
    body: Type;
  };
};

// Kinds (types of types)
export type StarKind = { star: null };
export type ArrowKind = { arrow: { from: Kind; to: Kind } };
export type Kind =
  | StarKind // * (base kind for proper types)
  | ArrowKind; // κ₁ → κ₂

// Pattern expressions for match cases
export type VarPattern = { var: string };
export type WildcardPattern = { wildcard: null };
export type ConPattern = { con: { name: string; type: Type } };
export type RecordPattern = { record: [string, Pattern][] };
export type VariantPattern = { variant: { label: string; pattern: Pattern } };
export type TuplePattern = { tuple: Pattern[] };
export type Pattern =
  | VarPattern // x - bind variable
  | WildcardPattern // _ - match anything
  | ConPattern // literal constant
  | RecordPattern // { l1: p1, l2: p2 }
  | VariantPattern // Label(pattern)
  | TuplePattern; // #(...patterns)

// Types
export type VarType = { var: string };
export type ArrowType = { arrow: { from: Type; to: Type } };
export type ForallType = { forall: { var: string; kind: Kind; body: Type } };
export type AppType = { app: { func: Type; arg: Type } };
export type LamType = { lam: { var: string; kind: Kind; body: Type } };
export type ConType = { con: string };
export type RecordType = { record: [string, Type][] };
export type VariantType = { variant: [string, Type][] };
export type MuType = { mu: { var: string; body: Type } };
export type TupleType = { tuple: Type[] };
export type NeverType = { never: null };
export type MetaType = { evar: string };
export type Type =
  | MetaType // meta type variable
  | VarType // type variable α
  | ArrowType // τ₁ → τ₂
  | ForallType // ∀α::κ.τ
  | AppType // type application F τ
  | BoundedForallType // trait type
  | LamType // λα::κ.τ
  | ConType // type constant (Int, Bool, etc.)
  | RecordType // {l₁:τ₁, l₂:τ₂, ...}
  | VariantType // <l₁:τ₁ | l₂:τ₂ | ...>
  | MuType // μα.τ - recursive type  List<t> -> { Cons(t, List<t>), Nil }
  | TupleType // tuples
  | NeverType; // bottom type (⊥)

// Terms
export type VarTerm = { var: string };
export type LamTerm = { lam: { arg: string; type: Type; body: Term } };
export type AppTerm = { app: { callee: Term; arg: Term } };
export type TyLamTerm = { tylam: { var: string; kind: Kind; body: Term } };
export type TyAppTerm = { tyapp: { term: Term; type: Type } };
export type ConTerm = { con: { name: string; type: Type } };
export type LetTerm = { let: { name: string; value: Term; body: Term } };
export type RecordTerm = { record: [string, Term][] };
export type ProjectTerm = { project: { record: Term; label: string } };
export type InjectTerm = {
  inject: { label: string; value: Term; variant_type: Type };
};
export type MatchTerm = {
  match: { scrutinee: Term; cases: [Pattern, Term][] };
};
export type FoldTerm = { fold: { type: Type; term: Term } };
export type UnfoldTerm = { unfold: Term };
export type TupleTerm = { tuple: Term[] };
export type TupleProjectTerm = {
  tuple_project: { tuple: Term; index: number };
};
// Trait dictionary (evidence of implementation)
export type DictTerm = {
  dict: {
    trait: string;
    type: Type;
    methods: [string, Term][]; // method implementations
  };
};

// Access trait method with evidence
export type TraitMethodTerm = {
  trait_method: {
    dict: Term; // dictionary/evidence
    method: string;
  };
};
// Lambda that takes trait evidence
export type TraitLamTerm = {
  trait_lam: {
    trait_var: string; // dict variable name
    trait: string;
    type_var: string;
    kind: Kind;
    constraints: TraitConstraint[];
    body: Term;
  };
};
// Application with trait evidence
export type TraitAppTerm = {
  trait_app: {
    term: Term;
    type: Type;
    dicts: Term[]; // evidence for each constraint
  };
};
export type Term =
  | AppTerm // e₁ e₂
  | ConTerm // constants with their types
  | DictTerm // trait dict
  | FoldTerm // fold: τ[μα.τ/α] → μα.τ
  | InjectTerm // <l=e> as T
  | LamTerm // λx:τ.e
  | LetTerm
  | MatchTerm // match e { l₁(x₁) => e₁ | l₂(x₂) => e₂ }
  | ProjectTerm // e.l
  | RecordTerm // {l₁=e₁, l₂=e₂, ...}
  | TraitAppTerm // trat application
  | TraitLamTerm // trait lambda
  | TraitMethodTerm // trait method
  | TupleProjectTerm // tuple[0]
  | TupleTerm // tuple: #(l₁, l₂, ...)
  | TyAppTerm // e [τ]
  | TyLamTerm // Λα::κ.e
  | UnfoldTerm // unfold: μα.τ → τ[μα.τ/α]
  | VarTerm; // variable x

// Context entries for type checking
export type TermBinding = { term: { name: string; type: Type } };
export type TypeBinding = { type: { name: string; kind: Kind } };
export type TypeAliasBinding = {
  type_alias: { name: string; params: string[]; kinds: Kind[]; body: Type };
};
// Trait definition - defines required methods
export type TraitDef = {
  name: string;
  type_param: string; // e.g., "Self"
  kind: Kind;
  methods: [string, Type][]; // method name -> method type
};
export type TraitDefBinding = {
  trait_def: TraitDef;
};

export type TraitImplBinding = {
  trait_impl: {
    trait: string;
    type: Type;
    dict: Term; // dictionary term
  };
};

export type DictBinding = {
  dict: {
    name: string; // dictionary variable
    trait: string;
    type: Type;
  };
};

export type EnumDef = {
  name: string; // e.g., "Either"
  kind: Kind; // e.g., * → * → * (for two params)
  params: string[]; // param var names, e.g., ["t", "u"]
  variants: [string, FieldScheme][]; // variant label → field scheme (with param vars unbound)
};
export type FieldScheme = Type; // e.g., { var: "t" } for Left, unit for None
export type EnumDefBinding = { enum: EnumDef };

export type Binding =
  | TermBinding // x : τ
  | TypeBinding // α :: κ
  | TraitDefBinding // trait definition
  | TraitImplBinding // trait impl
  | DictBinding // dict binding
  | EnumDefBinding // enums
  | TypeAliasBinding; // Type Alias
export type Context = Binding[];
export type MetaEnv = {
  solutions: Map<string, Type>; // evar -> Type
  kinds: Map<string, Kind>; // evar -> Kind
  counter: number;
};
export type TypeCheckerState = {
  meta: MetaEnv;
  ctx: Context;
};
export type ImportAliases = {
  traits?: Record<string, string>;
  types?: Record<string, string>;
  terms?: Record<string, string>;
  labels?: Record<string, string>;
};

export const state = (ctx: Context = []): TypeCheckerState =>
  ({
    ctx,
    meta: {
      solutions: new Map(),
      kinds: new Map(),
      counter: 0,
    },
  }) satisfies TypeCheckerState;

export type UnboundTypeError = { unbound: string };
export type KindMismatchTypeError = {
  kind_mismatch: { expected: Kind; actual: Kind };
};
export type TypeMismatchTypeError = {
  type_mismatch: { expected: Type; actual: Type };
};
export type NotAFunctionTypeError = { not_a_function: Type };
export type NotATypeFunctionTypeError = { not_a_type_function: Type };
export type CyclicTypeError = { cyclic: string };
export type NotARecordTypeError = { not_a_record: Type };
export type MissingFieldTypeError = {
  missing_field: { record: Type; label: string };
};
export type NotAVariantTypeError = { not_a_variant: Type };
export type InvalidVariantTypeError = {
  invalid_variant_label: { variant: Type; label: string };
};
export type MissingCaseTypeError = { missing_case: { label: string } };
export type ExtraCaseTypeError = { extra_case: { label: string } };
export type NotATupleTypeError = { not_a_tuple: Type };
export type TupleIndexOutofBoundsTypeError = {
  tuple_index_out_of_bounds: { tuple: Type; index: number };
};
export type MissingTraitImplError = {
  missing_trait_impl: { trait: string; type: Type };
};
export type MissingMethodError = {
  missing_method: { trait: string; method: string };
};
export type WrongNumberOfDictsError = {
  wrong_number_of_dicts: { expected: number; actual: number };
};
export type UnexpectedKindError = {
  unexpected_kind: { name: string; kind: Kind };
};
export type CircularImportError = {
  circular_import: { name: string; cycle: string[] };
};
export type DuplicateBindingError = {
  duplicate_binding: {
    name: string;
    existing: Binding;
    incoming: Binding;
  };
};
export type TypingError =
  | CircularImportError
  | CyclicTypeError
  | DuplicateBindingError
  | ExtraCaseTypeError
  | InvalidVariantTypeError
  | KindMismatchTypeError
  | MissingCaseTypeError
  | MissingFieldTypeError
  | MissingMethodError
  | MissingTraitImplError
  | NotAFunctionTypeError
  | NotARecordTypeError
  | NotATupleTypeError
  | NotATypeFunctionTypeError
  | NotAVariantTypeError
  | TupleIndexOutofBoundsTypeError
  | TypeMismatchTypeError
  | UnboundTypeError
  | UnexpectedKindError
  | WrongNumberOfDictsError;

export type TypeEqConstraint = { type_eq: { left: Type; right: Type } };
export type KindEqConstraint = { kind_eq: { left: Kind; right: Kind } };
export type HasKindConstraint = {
  has_kind: { ty: Type; kind: Kind; state: TypeCheckerState };
};
export type HasTypeConstraint = {
  has_type: { term: Term; ty: Type; state: TypeCheckerState };
};
export type Constraint =
  | TypeEqConstraint
  | KindEqConstraint
  | HasKindConstraint
  | HasTypeConstraint;

export type Value =
  | { vvar: string }
  | { vlam: { param: string; body: Term; env: Environment } }
  | { vapp: { func: Value; arg: Value } }
  | { vrecord: Record<string, Value> }
  | { vvariant: { label: string; value: Value } }
  | { vtuple: Value[] }
  | { vfold: { type: Type; value: Value } }
  | { vdict: { trait: string; type: Type; methods: Map<string, Value> } }
  | { vthunk: { term: Term; env: Environment } };

// Environment for variable bindings
export type Environment = Map<string, Value>;

// Evaluation result
export type EvalResult = Result<string, Value>; // Using string for error messages

// Configuration for evaluation
export type EvalConfig = {
  strict: boolean; // true for call-by-value, false for call-by-name
  maxSteps: number; // for preventing infinite loops
};

export type Result<TErr, TOk> = { ok: TOk } | { err: TErr };

export type FreeTypeNames = {
  typeVars: Set<string>;
  typeCons: Set<string>;
  traits: Set<string>;
  labels: Set<string>; // variant or record labels
};
export type FreePatternNames = {
  vars: Set<string>;
  constructors: Set<string>;
  labels: Set<string>;
};
export type FreeTermNames = {
  terms: Set<string>;
  constructors: Set<string>;
  traits: Set<string>;
  dicts: Set<string>;
  labels: Set<string>;
  typeVars: Set<string>;
  typeCons: Set<string>;
};

export type Worklist = Constraint[];
export type Substitution = Map<string, Type>;

export const ok = <T>(val: T) => ({ ok: val });
export const err = <T>(val: T) => ({ err: val });
