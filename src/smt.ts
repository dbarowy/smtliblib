/**
 * ©2021 Daniel W. Barowy (Williams College/Microsoft Research)
 * The SMT module defines a collection of SMTLIB AST node
 * constructors as well as parsing functions for those
 * nodes.  Parser users should call the user-friendly top-level
 * `SMT.parse` function, or if interfacing directly with
 * combinators is desired, the top-level `grammar` function.
 * All SMTLIB objects can be rendered into SMTLIB strings
 * using the `formula` property/method.
 * This library provides core SMTLIB functionality, but
 * it is currently not complete.  Patches welcome.
 */
import { Primitives as P, CharUtil as CU } from "parsecco";

interface JSONObject {
  [key: string]: any;
}

/**
 * exprs is the top-level parser in the grammar.
 */
export let [exprs, exprsImpl] = P.recParser<Expr[]>();

/**
 * expr is a basic expression.
 */
export let [expr, exprImpl] = P.recParser<Expr>();

/**
 * Parses a T optionally preceded and succeeded by whitespace.
 * @param p
 * @returns
 */
function pad<T>(p: P.IParser<T>): P.IParser<T> {
  return P.between<CU.CharStream, CU.CharStream, T>(P.ws)(P.ws)(p);
}

/**
 * Parses a T mandatorily preceded and succeeded by whitespace.
 * @param p
 * @returns
 */
function pad1<T>(p: P.IParser<T>): P.IParser<T> {
  return P.between<CU.CharStream, CU.CharStream, T>(P.ws1)(P.ws1)(p);
}

/**
 * Parses a T optionally preceded by whitespace.
 * @param p
 * @returns
 */
function padL<T>(p: P.IParser<T>): P.IParser<T> {
  return P.right<CU.CharStream, T>(P.ws)(p);
}

/**
 * Parses a T mandatorily preceded by whitespace.
 * @param p
 * @returns
 */
function padL1<T>(p: P.IParser<T>): P.IParser<T> {
  return P.right<CU.CharStream, T>(P.ws1)(p);
}

/**
 * Parses a T optionally succeeded by whitespace.
 * @param p
 * @returns
 */
function padR<T>(p: P.IParser<T>): P.IParser<T> {
  return P.left<T, CU.CharStream>(p)(P.ws);
}

/**
 * Parses a T mandatorily succeeded by whitespace.
 * @param p
 * @returns
 */
function padR1<T>(p: P.IParser<T>): P.IParser<T> {
  return P.left<T, CU.CharStream>(p)(P.ws1);
}

/**
 * Parses anything surrounded by parens, with optional whitespace padding.
 * @param p
 * @returns
 */
function par<T>(p: P.IParser<T>): P.IParser<T> {
  return P.between<CU.CharStream, CU.CharStream, T>(padR(P.char("(")))(
    padL(P.char(")"))
  )(p);
}

/**
 * Parses at least one `p`, followed by repeated sequences of `sep` and `p`.
 * In BNF: `p (sep p)*`.
 * @param p A parser
 * @param sep A separator
 */
function sepBy1<T>(p: P.IParser<T>) {
  return (sep: P.IParser<any>) => {
    return P.pipe2<T, T[], T[]>(
      // parse the one
      // P.right<CU.CharStream, T>(PP.Comma)(p)
      p
    )(
      // then the many
      P.many(P.right<any, T>(sep)(p))
    )(
      // then combine them
      (a, bs) => [a].concat(bs)
    );
  };
}

/**
 * Parses `p` followed by repeated sequences of `sep` and `p`, zero or
 * more times.
 * In BNF: `p (sep p)*`.
 * @param p A parser
 * @param sep A separator
 */
function sepBy<T>(p: P.IParser<T>) {
  return (sep: P.IParser<any>) => {
    return P.choice(
      // parse as many as possible
      sepBy1(p)(sep)
    )(
      // but none is also OK
      P.result<T[]>([])
    );
  };
}

/**
 * A parser that constructs an arbitrary AST node from an op
 * string and a sequence of expressions.  E.g., `(or expr1 ... exprn)`.
 * @param op The operation string.
 * @param ctor A constructor lambda.
 * @returns
 */
function opParser<T>(op: string, ctor: (es: Expr[]) => T): P.IParser<T> {
  return par(
    P.right<CU.CharStream, T>(
      // the op
      padR(P.str(op))
    )(
      // the expression list
      P.pipe<Expr[], T>(sepBy(expr)(P.ws))((es) => ctor(es))
    )
  );
}

/**
 * Pretty-printer helper.  Takes an op and an array
 * of clauses and produces a string like `(op <expr1> ... <exprn>)`
 * @param op The operation
 * @param clauses Expression array
 * @returns
 */
function opPretty(op: string, clauses: Expr[]): string {
  if (clauses.length === 0) {
    return "";
  } else if (clauses.length === 1) {
    return clauses[0].formula;
  } else {
    return (
      "(" +
      op +
      " " +
      clauses[0].formula +
      " " +
      opPretty(op, clauses.slice(1)) +
      ")"
    );
  }
}

export interface Expr {
  /**
   * Emit a formula string for this expression. Generally, this
   * formula should be an application and not a declaration.
   * Use a decl getter property for declarations.
   */
  formula: string;

  /**
   * Returns the current expression as a JSON object.
   */
  serialized: object;
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

  /**
   * Returns the current expression as a JSON object.
   */
  serialized: object;
}

/**
 * Some SMT helpers.
 */
export namespace SMT {
  // splitting this into two pieces for readability
  const __identifier = P.pipe2<CU.CharStream, CU.CharStream[], CU.CharStream>(
    // prefix
    P.choices(P.upper, P.lower)
  )(
    // suffix
    P.many(
      P.choices(
        P.upper,
        P.lower,
        P.digit,
        P.char("-"),
        P.char("_"),
        P.char("!")
      )
    )
  )((c, cs) => {
    const cs2 = [c].concat(cs);
    return cs2.reduce((acc, cur) => acc.concat(cur));
  });

  /**
   * Parses a valid identifier.
   */
  export const identifier = P.bind<CU.CharStream, CU.CharStream>(__identifier)(
    (id) =>
      reservedWords.has(id.toString())
        ? P.zero<CU.CharStream>("Invalid use of reserved word.")
        : P.result(id)
  );

  const reservedWords = new Set(["true", "false", "sat", "unsat"]);

  export class And implements Expr {
    public readonly clauses: Expr[];

    /**
     * Represents a nested conjunction in SMTLIB.
     * @param clauses A set of SMTLIB clauses as a string array.
     */
    constructor(clauses: Expr[]) {
      this.clauses = clauses;
    }

    public get formula(): string {
      return opPretty("and", this.clauses);
    }

    public static get parser(): P.IParser<And> {
      return opParser("and", (es) => new And(es));
    }

    public get serialized(): object {
      return {
        type: "And",
        clauses: this.clauses.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): And {
      return new And(
        (json["clauses"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
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

    public get formula(): string {
      return opPretty("or", this.clauses);
    }

    public static get parser(): P.IParser<Or> {
      return opParser("or", (es) => new Or(es));
    }

    public get serialized(): object {
      return {
        type: "Or",
        clauses: this.clauses.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): Or {
      return new Or(
        (json["clauses"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
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

    public static get parser(): P.IParser<Not> {
      return par(
        P.right<CU.CharStream, Not>(padR(P.str("not")))(
          P.pipe<Expr, Not>(expr)((e) => new Not(e))
        )
      );
    }

    public get serialized(): object {
      return {
        type: "Not",
        clause: this.clause.serialized,
      };
    }

    public static deserialize(json: JSONObject): Not {
      return new Not(deserializeExpr(json["clause"]));
    }
  }

  export class Equals implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents an equality constraint in SMTLIB.
     * @param terms An array of SMTLIB terms.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty("=", this.terms);
    }

    public static get parser(): P.IParser<Equals> {
      return opParser("=", (es) => new Equals(es));
    }

    public get serialized(): object {
      return {
        type: "Equals",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): Equals {
      return new Equals(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class Plus implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents an addition constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty("+", this.terms);
    }

    public static get parser(): P.IParser<Plus> {
      return opParser("+", (es) => new Plus(es));
    }

    public get serialized(): object {
      return {
        type: "Plus",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): Plus {
      return new Plus(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class Minus implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents a subtraction constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty("-", this.terms);
    }

    public static get parser(): P.IParser<Minus> {
      return opParser("-", (es) => new Minus(es));
    }

    public get serialized(): object {
      return {
        type: "Minus",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): Minus {
      return new Minus(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class LessThan implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents a less-than constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty("<", this.terms);
    }

    public static get parser(): P.IParser<LessThan> {
      return opParser("<", (es) => new LessThan(es));
    }

    public get serialized(): object {
      return {
        type: "LessThan",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): LessThan {
      return new LessThan(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class LessThanOrEqual implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents a less-than-or-equal constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty("<=", this.terms);
    }

    public static get parser(): P.IParser<LessThanOrEqual> {
      return opParser("<=", (es) => new LessThanOrEqual(es));
    }

    public get serialized(): object {
      return {
        type: "LessThanOrEqual",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): LessThanOrEqual {
      return new LessThanOrEqual(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class GreaterThan implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents a greater-than constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty(">", this.terms);
    }

    public static get parser(): P.IParser<GreaterThan> {
      return opParser(">", (es) => new GreaterThan(es));
    }

    public get serialized(): object {
      return {
        type: "GreaterThan",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): GreaterThan {
      return new GreaterThan(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class GreaterThanOrEqual implements Expr {
    public readonly terms: Expr[];

    /**
     * Represents a greater-than-or-equal constraint in SMTLIB.
     * @param terms An array of SMTLIB clauses.
     */
    constructor(terms: Expr[]) {
      this.terms = terms;
    }

    public get formula(): string {
      return opPretty(">=", this.terms);
    }

    public static get parser(): P.IParser<GreaterThanOrEqual> {
      return opParser(">=", (es) => new GreaterThanOrEqual(es));
    }

    public get serialized(): object {
      return {
        type: "GreaterThanOrEqual",
        terms: this.terms.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): GreaterThanOrEqual {
      return new GreaterThanOrEqual(
        (json["terms"] as JSONObject[]).map((t) => deserializeExpr(t))
      );
    }
  }

  export class Let implements Expr {
    public readonly bindings: [Var, Expr][];
    public readonly body: Expr;

    /**
     * Represents a let expression.
     * @param bindings A set of variable-expression bindings.
     * @param body The expression in which the set of bindings is valid.
     */
    constructor(bindings: [Var, Expr][], body: Expr) {
      this.bindings = bindings;
      this.body = body;
    }

    public get serialized(): object {
      return {
        type: "Let",
        bindings: this.bindings.map(([v, e]) => [v.serialized, e.serialized]),
        body: this.body.serialized,
      };
    }

    public static deserialize(json: JSONObject): Let {
      return new Let(
        (json["bindings"] as [JSONObject, JSONObject][]).map(([v, e]) => [
          Var.deserialize(v),
          deserializeExpr(e),
        ]),
        deserializeExpr(json["body"])
      );
    }

    public get formula(): string {
      return (
        "(let (" +
        this.bindings.map(
          ([v, expr]) => "(" + v.formula + " " + expr.formula + ")"
        ) +
        ") " +
        this.body.formula +
        ")"
      );
    }

    public static get parser(): P.IParser<Let> {
      return P.pipe<[[Var, Expr][], Expr], Let>(
        par(
          P.right<CU.CharStream, [[Var, Expr][], Expr]>(
            // first a function name
            padR1(P.str("let"))
          )(
            P.seq<[Var, Expr][], Expr>(
              // then parens
              par(
                // then pairs of bindings
                sepBy1<[Var, Expr]>(
                  // inside even more parens
                  par(
                    P.seq<Var, Expr>(
                      // a variable name
                      padR1(Var.parser)
                    )(
                      // an arbitrary expression
                      expr
                    )
                  )
                )(
                  // binding pair separator
                  P.ws1
                )
              )
            )(
              // and finally, the body
              padL(expr)
            )
          )
        )
      )(([bindings, body]) => new Let(bindings, body));
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

    public get serialized(): object {
      return {
        type: "IfThenElse",
        cond: this.cond.serialized,
        whenTrue: this.whenTrue.serialized,
        whenFalse: this.whenFalse.serialized,
      };
    }

    public static deserialize(json: JSONObject): IfThenElse {
      return new IfThenElse(
        deserializeExpr(json["cond"]),
        deserializeExpr(json["whenTrue"]),
        deserializeExpr(json["whenFalse"])
      );
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

    public static get parser(): P.IParser<IfThenElse> {
      return par(
        P.right<CU.CharStream, IfThenElse>(
          // the ite
          padR1(P.str("ite"))
        )(
          P.pipe<[Expr, [Expr, Expr]], IfThenElse>(
            P.seq<Expr, [Expr, Expr]>(
              // the condition
              padR1(expr)
            )(
              P.seq<Expr, Expr>(
                // true clause
                padR1(expr)
              )(
                // false clause
                expr
              )
            )
          )(([cond, [etrue, efalse]]) => new IfThenElse(cond, etrue, efalse))
        )
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

    public get serialized(): object {
      return {
        type: "Assert",
        clause: this.clause.serialized,
      };
    }

    public static deserialize(json: JSONObject): Assert {
      return new Assert(deserializeExpr(json["clause"]));
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

    public get serialized(): object {
      return {
        type: "FunctionDeclaration",
        name: this.name,
        paramSortList: this.paramSortList.map((s) => s.serialized),
        returnSort: this.returnSort.serialized,
      };
    }

    public static deserialize(json: JSONObject): FunctionDeclaration {
      return new FunctionDeclaration(
        json["name"] as string,
        (json["name"] as JSONObject[]).map((s) => deserializeSort(s)),
        deserializeSort(json["returnSort"])
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

    public get serialized(): object {
      return {
        type: "FunctionDefinition",
        name: this.name,
        parameterList: this.parameterList.map((decl) => decl.serialized),
        returnSort: this.returnSort.serialized,
        impl: this.impl.serialized,
      };
    }

    public static deserialize(json: JSONObject): FunctionDefinition {
      return new FunctionDefinition(
        json["name"] as string,
        (json["parameterList"] as JSONObject[]).map((e) =>
          ArgumentDeclaration.deserialize(e)
        ),
        deserializeSort(json["returnSort"]),
        deserializeExpr(json["impl"])
      );
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

    public static get parser() {
      return par(
        P.pipe<
          [[[CU.CharStream, ArgumentDeclaration[]], Sort], Expr],
          FunctionDefinition
        >(
          // start: (((("define-fun",<name>), <args>),<sort>),<expr>)
          P.seq<[[CU.CharStream, ArgumentDeclaration[]], Sort], Expr>(
            // start: ((("define-fun",<name>), <args>),<sort>)
            P.seq<[CU.CharStream, ArgumentDeclaration[]], Sort>(
              // start: (("define-fun",<name>), <args>)
              P.seq<CU.CharStream, ArgumentDeclaration[]>(
                // start: ("define-fun",<name>)
                P.right<CU.CharStream, CU.CharStream>(
                  // first
                  P.str("define-fun")
                )(
                  // then the function name
                  padL1(identifier)
                ) // end: ("define-fun",<name>)
              )(
                // arguments
                padL1(ArgumentDeclaration.parser)
              ) // end: (("define-fun",<name>), <args>)
            )(
              // return sort
              padL1(sort)
            ) // end: ((("define-fun",<name>), <args>),<sort>)
          )(
            // function body
            padL1(expr)
          ) // end: (((("define-fun",<name>), <args>),<sort>),<expr>)
        )(
          ([[[name, args], sort], body]) =>
            new FunctionDefinition(name.toString(), args, sort, body)
        )
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

    public get serialized(): object {
      return {
        type: "DataTypeDeclaration",
        name: this.name,
        impl: this.impl.serialized,
      };
    }

    public static deserialize(json: JSONObject): DataTypeDeclaration {
      return new DataTypeDeclaration(
        json["name"] as string,
        deserializeExpr(json["impl"])
      );
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

    public get serialized(): object {
      return {
        type: "ConstantDeclaration",
        name: this.name,
        sort: this.sort.serialized,
      };
    }

    public static deserialize(json: JSONObject): ConstantDeclaration {
      return new ConstantDeclaration(
        json["name"] as string,
        deserializeSort(json["sort"])
      );
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

    public static get parser(): P.IParser<ArgumentDeclaration[]> {
      const declSingle = P.pipe<[CU.CharStream, Sort], ArgumentDeclaration>(
        P.between<CU.CharStream, CU.CharStream, [CU.CharStream, Sort]>(
          // opening paren
          P.left<CU.CharStream, CU.CharStream>(P.char("("))(P.ws)
        )(
          // closing paren
          P.left<CU.CharStream, CU.CharStream>(P.ws)(P.char(")"))
        )(
          // the part we care about
          P.seq<CU.CharStream, Sort>(
            // arg name
            P.left<CU.CharStream, CU.CharStream>(identifier)(P.ws)
          )(
            // sort name
            sort
          )
        )
      )(([name, sort]) => new ArgumentDeclaration(name.toString(), sort));

      return P.between<CU.CharStream, CU.CharStream, ArgumentDeclaration[]>(
        // opening paren
        P.left<CU.CharStream, CU.CharStream>(P.char("("))(P.ws)
      )(
        // closing paren
        P.left<CU.CharStream, CU.CharStream>(P.ws)(P.char(")"))
      )(
        // the part we care about
        P.many(P.left(declSingle)(P.ws))
      );
    }

    public get serialized(): object {
      return {
        type: "ArgumentDeclaration",
        name: this.name,
        sort: this.sort.serialized,
      };
    }

    public static deserialize(json: JSONObject): ArgumentDeclaration {
      return new ArgumentDeclaration(
        json["name"] as string,
        deserializeSort(json["sort"] as JSONObject)
      );
    }
  }

  export class FunctionApplication implements Expr {
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

    public static get parser(): P.IParser<FunctionApplication> {
      return P.pipe<[CU.CharStream, Expr[]], FunctionApplication>(
        P.between<CU.CharStream, CU.CharStream, [CU.CharStream, Expr[]]>(
          pad(P.char("("))
        )(pad(P.char(")")))(
          P.seq<CU.CharStream, Expr[]>(
            // first a function name
            padR(identifier)
          )(
            // then a list of arguments
            sepBy1(expr)(P.ws)
          )
        )
      )(([name, args]) => new FunctionApplication(name.toString(), args));
    }

    public get serialized(): object {
      return {
        type: "FunctionApplication",
        name: this.name,
        args: this.args.map((a) => a.serialized),
      };
    }

    public static deserialize(json: JSONObject): FunctionApplication {
      return new FunctionApplication(
        json["name"] as string,
        (json["args"] as JSONObject[]).map((e) => deserializeExpr(e))
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

    public static get parser(): P.IParser<Var> {
      return P.pipe<CU.CharStream, Var>(identifier)(
        (v) => new Var(v.toString())
      );
    }

    public get serialized(): object {
      return {
        type: "Var",
        name: this.name,
      };
    }

    public static deserialize(json: JSONObject): Var {
      return new Var(json["name"] as string);
    }
  }

  export class Model implements Expr {
    public readonly exprs: Expr[];

    /**
     * Represents a model definition in SMTLIB.
     * It just looks like a pair of parens, and can only
     * occur at the top level.
     * @param exprs A sequence of expressions.
     */
    constructor(exprs: Expr[]) {
      this.exprs = exprs;
    }

    public get formula(): string {
      return "(" + this.exprs.map((e) => e.formula).join("\n") + "\n)";
    }

    public static get parser(): P.IParser<Model> {
      return par(
        P.pipe<Expr[], Model>(sepBy1(expr)(P.ws))((es) => new Model(es))
      );
    }

    public get serialized(): object {
      return {
        type: "Model",
        exprs: this.exprs.map((e) => e.serialized),
      };
    }

    public static deserialize(json: JSONObject): Model {
      return new Model(
        (json["exprs"] as JSONObject[]).map((e) => deserializeExpr(e))
      );
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

    public get serialized(): object {
      return {
        type: "IsSatisfiable",
        value: this.value,
      };
    }

    public static deserialize(json: JSONObject): IsSatisfiable {
      return new IsSatisfiable(json["value"] as boolean);
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

    public get serialized(): object {
      return {
        type: "CheckSatisfiable",
      };
    }

    public static deserialize(json: JSONObject): CheckSatisfiable {
      return new CheckSatisfiable();
    }
  }

  export class GetModel implements Expr {
    /**
     * Represents a Z3 get-model command.
     */
    constructor() {}

    public get formula(): string {
      return "(get-model)";
    }

    public get serialized(): object {
      return {
        type: "GetModel",
      };
    }

    public static deserialize(json: JSONObject): GetModel {
      return new GetModel();
    }
  }

  // Built-in SMT sorts
  // FWIW, these do double-duty as sorts and as expressions.

  /**
   * Int sort.
   */
  export class Int implements Sort, Expr {
    public value: number;
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

    public static get valueParser(): P.IParser<Int> {
      return P.pipe<number, Int>(P.integer)((n) => new Int(n));
    }

    public static get sortParser(): P.IParser<Sort> {
      return P.pipe<CU.CharStream, Sort>(P.str("Int"))((b) => Int.sort);
    }

    public get serialized(): object {
      return {
        type: "Int",
        value: this.value,
      };
    }

    public static deserialize(json: JSONObject): Int {
      return new Int(json["value"] as number);
    }
  }

  /**
   * Bool sort.
   */
  export class Bool implements Expr, Sort {
    public value: boolean;
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

    public static get valueParser(): P.IParser<Bool> {
      return P.pipe<CU.CharStream, Bool>(
        P.choice(P.str("true"))(P.str("false"))
      )((tf) => {
        switch (tf.toString()) {
          case "true":
            return new Bool(true);
          default:
            return new Bool(false);
        }
      });
    }

    public static get sortParser(): P.IParser<Sort> {
      return P.pipe<CU.CharStream, Sort>(P.str("Bool"))((b) => Bool.sort);
    }

    public get serialized(): object {
      return {
        type: "Bool",
        value: this.value,
      };
    }

    public static deserialize(json: JSONObject): Bool {
      return new Bool(json["value"] as boolean);
    }
  }

  /**
   * Unknown sort
   */
  export class UserDefinedSort implements Sort {
    private static sortInstance: Sort = new UserDefinedSort("unknown");
    public name: string;
    public sort = UserDefinedSort.sortInstance;
    public static sort = UserDefinedSort.sortInstance;
    constructor(name: string) {
      this.name = name;
    }
    public static get sortParser(): P.IParser<Sort> {
      return P.pipe<CU.CharStream, Sort>(identifier)(
        (name) => new UserDefinedSort(name.toString())
      );
    }

    public static get valueParser(): P.IParser<UserDefinedSort> {
      throw new Error("Not implemented.");
    }

    public get serialized(): object {
      return {
        type: "UserDefinedSort",
        name: this.name,
      };
    }

    public static deserialize(json: JSONObject): UserDefinedSort {
      return new UserDefinedSort(json["name"]);
    }
  }

  const sort = P.choices(
    Int.sortParser,
    Bool.sortParser,
    UserDefinedSort.sortParser
  );

  /**
   * Core operations.
   */
  const ops = P.choices<Expr>(
    Not.parser,
    And.parser,
    Or.parser,
    Equals.parser,
    LessThan.parser,
    LessThanOrEqual.parser,
    GreaterThan.parser,
    GreaterThanOrEqual.parser,
    Plus.parser,
    Minus.parser
  );

  /**
   * Represents a collection of expressions.
   */
  exprsImpl.contents = sepBy1(P.choice<Expr>(expr)(Model.parser))(P.ws);

  /**
   * Represents the top-level grammar non-terminal.
   */
  const grammar: P.IParser<Expr[]> = P.left(
    // a bunch of expressions
    exprs
  )(
    // followed by some optional whitespace and then EOF
    padL(P.eof)
  );

  /**
   * Parses an arbitrarily complex expression.
   */
  exprImpl.contents = P.choices<Expr>(
    ops,
    Let.parser,
    FunctionApplication.parser,
    FunctionDefinition.parser,
    Var.parser,
    IsSatisfiable.parser,
    Bool.valueParser,
    Int.valueParser
  );

  /**
   * Parses an input string into an SMTLIB AST. Throws
   * an exception if parsing fails.
   * @param s A string.
   */
  export function parse(s: string): Expr[] {
    const input = new CU.CharStream(s);
    const outcome = grammar(input);
    switch (outcome.tag) {
      case "success":
        return outcome.result;
      case "failure":
        throw new Error("Not a valid SMTLIB program.");
    }
  }

  /**
   * Serializes an AST into JSON.
   * @param es An array of Exprs.
   * @returns A JSON object.
   */
  export function serialize(es: Expr[]): object {
    return es.map((e) => e.serialized);
  }

  export function deserialize(json: object): Expr[] {
    if (Array.isArray(json)) {
      const arr = json as JSONObject[];
      return arr.map((e) => deserializeExpr(e));
    } else {
      throw new Error(
        "Valid SMTLIB JSON object must be an outermost array of expressions."
      );
    }
  }

  function deserializeLiteral(json: JSONObject): Expr {
    try {
      switch (json["type"]) {
        case "Int":
          return Int.deserialize(json);
        case "Bool":
          return Bool.deserialize(json);
        default:
          throw new Error("Unrecognized sort '" + json["type"] + "'.");
      }
    } catch (e) {
      throw new Error(
        "Valid SMTLIB JSON object must have a 'type' field corresponding to an SMTLIB expression."
      );
    }
  }

  function deserializeSort(json: JSONObject): Sort {
    try {
      switch (json["type"]) {
        case "Int":
          return Int.deserialize(json);
        case "Bool":
          return Bool.deserialize(json);
        case "UserDefinedSort":
          return UserDefinedSort.deserialize(json);
        default:
          throw new Error("Unrecognized sort '" + json["type"] + "'.");
      }
    } catch (e) {
      throw new Error(
        "Valid SMTLIB JSON object must have a 'type' field corresponding to an SMTLIB expression."
      );
    }
  }

  function deserializeExpr(json: JSONObject): Expr {
    try {
      switch (json["type"]) {
        case "GetModel":
          return GetModel.deserialize(json);
        case "CheckSatisfiable":
          return CheckSatisfiable.deserialize(json);
        case "IsSatisfiable":
          return IsSatisfiable.deserialize(json);
        case "Model":
          return Model.deserialize(json);
        case "Var":
          return Var.deserialize(json);
        case "FunctionApplication":
          return FunctionApplication.deserialize(json);
        case "ArgumentDeclaration":
          return ArgumentDeclaration.deserialize(json);
        case "ConstantDeclaration":
          return ConstantDeclaration.deserialize(json);
        case "DataTypeDeclaration":
          return DataTypeDeclaration.deserialize(json);
        case "FunctionDefinition":
          return FunctionDefinition.deserialize(json);
        case "FunctionDeclaration":
          return FunctionDeclaration.deserialize(json);
        case "Assert":
          return Assert.deserialize(json);
        case "IfThenElse":
          return IfThenElse.deserialize(json);
        case "Let":
          return Let.deserialize(json);
        case "GreaterThanOrEqual":
          return GreaterThanOrEqual.deserialize(json);
        case "GreaterThan":
          return GreaterThan.deserialize(json);
        case "LessThanOrEqual":
          return LessThanOrEqual.deserialize(json);
        case "LessThan":
          return LessThan.deserialize(json);
        case "Minus":
          return Minus.deserialize(json);
        case "Plus":
          return Plus.deserialize(json);
        case "Equals":
          return Equals.deserialize(json);
        case "Not":
          return Not.deserialize(json);
        case "Or":
          return Or.deserialize(json);
        case "And":
          return And.deserialize(json);
        default:
          // is it a literal?
          try {
            return deserializeLiteral(json);
          } catch (e) {
            throw new Error("Unrecognized type '" + json["type"] + "'.");
          }
      }
    } catch (e) {
      throw new Error(
        "Valid SMTLIB JSON object must have a 'type' field corresponding to an SMTLIB expression: " +
          e.toString()
      );
    }
  }
}
