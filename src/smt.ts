import { Primitives as P, CharUtil as CU } from "parsecco";

export interface Expr {
  /**
   * Emit a formula string for this expression. Generally, this
   * formula should be an application and not a declaration.
   * Use a decl getter property for declarations.
   */
  formula: string;
}

export interface Sort {
  /**
   * Emit a sort name for this expression.
   */
  name: string;

  /**
   * Get the singleton sort instance.
   */
  sort: Sort;
}

/**
 * Some SMT helpers.
 */
export module SMT {
  export class And implements Expr {
    public readonly clauses: Expr[];

    /**
     * Represents a nested conjunction in SMTLIB.
     * @param clauses A set of SMTLIB clauses as a string array.
     */
    constructor(clauses: Expr[]) {
      this.clauses = clauses;
    }

    private static andH(clauses: Expr[]): string {
      if (clauses.length === 0) {
        return "";
      } else if (clauses.length === 1) {
        return clauses[0].formula;
      } else {
        return (
          "(and " +
          clauses[0].formula +
          " " +
          SMT.And.andH(clauses.slice(1)) +
          ")"
        );
      }
    }

    public get formula(): string {
      return SMT.And.andH(this.clauses);
    }
  }

  export class Or implements Expr {
    public readonly clauses: Expr[];

    /**
     * Represents a nested disjunction in SMTLIB.
     * @param clauses A set of SMTLIB clauses as a string array.
     */
    constructor(clauses: Expr[]) {
      this.clauses = clauses;
    }

    private static orH(clauses: Expr[]): string {
      if (clauses.length === 0) {
        return "";
      } else if (clauses.length === 1) {
        return clauses[0].formula;
      } else {
        return (
          "(or " + clauses[0].formula + " " + SMT.Or.orH(clauses.slice(1)) + ")"
        );
      }
    }

    public get formula(): string {
      return SMT.Or.orH(this.clauses);
    }
  }

  export class Not implements Expr {
    public readonly clause: Expr;

    /**
     * Represents negation in SMTLIB.
     * @param clause An SMTLIB clause.
     */
    constructor(clause: Expr) {
      this.clause = clause;
    }

    public get formula(): string {
      return "(not " + this.clause.formula + ")";
    }
  }

  export class Equals implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents an equality constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(= " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class Plus implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents an addition constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(+ " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class Minus implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents a subtraction constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(- " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class LessThan implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents a less-than constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(< " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class LessThanOrEqual implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents a less-than-or-equal-to constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(<= " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class GreaterThan implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents a greater-than constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(> " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class GreaterThanOrEqual implements Expr {
    public readonly term1: Expr;
    public readonly term2: Expr;

    /**
     * Represents a greater-than-or-equal constraint in SMTLIB.
     * @param term1 An SMTLIB clause.
     * @param term2 An SMTLIB clause.
     */
    constructor(term1: Expr, term2: Expr) {
      this.term1 = term1;
      this.term2 = term2;
    }

    public get formula(): string {
      return "(>= " + this.term1.formula + " " + this.term2.formula + ")";
    }
  }

  export class IfThenElse implements Expr {
    public readonly cond: Expr;
    public readonly whenTrue: Expr;
    public readonly whenFalse: Expr;

    /**
     * Represents a less-than constraint in SMTLIB.
     * @param cond A boolean expression.
     * @param whenTrue Value when true.
     * @param whenFalse Value when false.
     */
    constructor(cond: Expr, whenTrue: Expr, whenFalse: Expr) {
      this.cond = cond;
      this.whenTrue = whenTrue;
      this.whenFalse = whenFalse;
    }

    public get formula(): string {
      return (
        "(ite " +
        this.cond.formula +
        " " +
        this.whenTrue.formula +
        " " +
        this.whenFalse.formula +
        ")"
      );
    }
  }

  export class Assert implements Expr {
    public readonly clause: Expr;

    /**
     * Represents an assertion in SMTLIB.
     * @param clause An SMTLIB expression.
     */
    constructor(clause: Expr) {
      this.clause = clause;
    }

    public get formula(): string {
      return "(assert " + this.clause.formula + ")";
    }
  }

  export class FunctionDeclaration implements Expr {
    public readonly name: string;
    public readonly paramSortList: Sort[];
    public readonly returnSort: Sort;

    /**
     * Represents an SMTLIB function declaration.
     * @param name The name of the function.
     * @param paramSortList A list of sorts.
     * @param returnSort The return sort of the function.
     */
    constructor(name: string, paramSortList: Sort[], returnSort: Sort) {
      this.name = name;
      this.paramSortList = paramSortList;
      this.returnSort = returnSort;
    }

    public get formula(): string {
      const paramStr =
        "(" + this.paramSortList.map((s) => s.name).join(" ") + ")";
      return (
        "(declare-fun " +
        this.name +
        " " +
        paramStr +
        " " +
        this.returnSort.name +
        ")"
      );
    }
  }

  export class FunctionDefinition implements Expr {
    public readonly name: string;
    public readonly parameterList: SMT.ArgumentDeclaration[];
    public readonly returnSort: Sort;
    public readonly impl: Expr;

    /**
     * Represents an SMTLIB function definition.
     * @param name The name of the function.
     * @param parameterList A list of associations between parameter names and their sorts.
     * @param returnSort The return sort of the function.
     * @param impl An SMTLIB implementation expression.
     */
    constructor(
      name: string,
      parameterList: SMT.ArgumentDeclaration[],
      returnSort: Sort,
      impl: Expr
    ) {
      this.name = name;
      this.parameterList = parameterList;
      this.returnSort = returnSort;
      this.impl = impl;
    }

    public get formula(): string {
      const sortAssnsStr =
        "(" +
        this.parameterList
          .map((arg) => "(" + arg.name + " " + arg.sort.name + ")")
          .join(" ") +
        ")";
      return (
        "(define-fun " +
        this.name +
        " " +
        sortAssnsStr +
        " " +
        this.returnSort.name +
        " " +
        this.impl.formula +
        ")"
      );
    }
  }

  export class DataTypeDeclaration implements Expr {
    public readonly name: string;
    public readonly impl: Expr;

    /**
     * Represents an SMTLIB algebraic datatype definition.
     * @param name The name of the datatype (sort).
     * @param impl An SMTLIB implementation expression.
     */
    constructor(name: string, impl: Expr) {
      this.name = name;
      this.impl = impl;
    }

    public get formula(): string {
      return "(declare-datatype " + this.name + " (" + this.impl.formula + "))";
    }
  }

  export class ConstantDeclaration implements Expr {
    public readonly name: string;
    public readonly sort: Sort;

    /**
     * Represents an SMTLIB constant of the given sort.
     * @param name The name of the constant.
     * @param sort The name of the sort.
     */
    constructor(name: string, sort: Sort) {
      this.name = name;
      this.sort = sort;
    }

    public get formula(): string {
      return "(declare-const " + this.name + " " + this.sort.name + ")";
    }
  }

  export class ArgumentDeclaration implements Expr {
    public readonly name: string;
    public readonly sort: Sort;

    /**
     * Represents an SMTLIB argument of the given sort.
     * @param name The name of the argument.
     * @param sort The name of the sort.
     */
    constructor(name: string, sort: Sort) {
      this.name = name;
      this.sort = sort;
    }

    public get formula(): string {
      return "(" + this.name + " " + this.sort.name + ")";
    }
  }

  export class Apply implements Expr {
    public readonly name: string;
    public readonly args: Expr[];

    /**
     * Represents an SMTLIB function application.
     * @param name The name of the funciton.
     * @param args Function arguments.
     */
    constructor(name: string, args: Expr[]) {
      this.name = name;
      this.args = args;
    }

    public get formula(): string {
      return (
        "(" + this.name + " " + this.args.map((a) => a.formula).join(" ") + ")"
      );
    }
  }

  export class Var implements Expr {
    public readonly name: string;

    /**
     * Represents a variable use in SMTLIB.
     * @param name
     */
    constructor(name: string) {
      this.name = name;
    }

    public get formula(): string {
      return this.name;
    }
  }

  export class IsSatisfiable implements Expr {
    public value: boolean;

    /**
     * Represents whether a set of constraints is satisfiable.
     * @param value
     */
    constructor(value: boolean) {
      this.value = value;
    }

    public get formula(): string {
      return this.value ? "sat" : "unsat";
    }

    public static get parser(): P.IParser<IsSatisfiable> {
      const p = P.choice(P.str("sat"))(P.str("unsat"));
      return P.pipe<CU.CharStream, IsSatisfiable>(p)((res) => {
        const value = res.toString() === "sat";
        return new IsSatisfiable(value);
      });
    }
  }

  export class CheckSatisfiable implements Expr {
    /**
     * Represents a Z3 check-sat command.
     */
    constructor() {}

    public get formula(): string {
      return "(check-sat)";
    }
  }

  export class GetModel implements Expr {
    constructor() {}

    /**
     * Represents a Z3 get-model command.
     */
    public get formula(): string {
      return "(get-model)";
    }
  }

  // Built-in SMT sorts

  /**
   * Int sort.
   */
  export class Int implements Sort, Expr {
    public value: number = 0;
    private static sortInstance: Sort = new Int(0);

    public get sort(): Sort {
      return SMT.Int.sortInstance;
    }

    public static get sort(): Sort {
      return SMT.Int.sortInstance;
    }

    public get name(): string {
      return "Int";
    }

    public get formula(): string {
      return this.value.toString();
    }

    constructor(n: number) {
      this.value = n;
    }
  }

  /**
   * Bool sort.
   */
  export class Bool implements Expr, Sort {
    public value: boolean = true;
    private static sortInstance: Sort = new Bool(true);

    public get sort(): Sort {
      return SMT.Bool.sortInstance;
    }

    public static get sort(): Sort {
      return SMT.Bool.sortInstance;
    }

    public get name(): string {
      return "Bool";
    }

    public get formula(): string {
      return this.value.toString();
    }

    constructor(b: boolean) {
      this.value = b;
    }
  }

  const grammar = IsSatisfiable.parser;

  /**
   * Parses an input string into an SMTLIB AST. Throws
   * an exception if parsing fails.
   * @param s A string.
   */
  export function parse(s: string): Expr {
    const input = new CU.CharStream(s);
    const outcome = grammar(input);
    switch (outcome.tag) {
      case "success":
        return outcome.result;
      case "failure":
        throw new Error(outcome.error_msg);
    }
  }
}
