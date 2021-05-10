import { SMT } from "../src/smt";
import { CharUtil as CU } from "parsecco";
import { assert, expect } from "chai";
import "mocha";
import * as fs from "fs";

describe("Identifier", () => {
  it('should parse "foo"', () => {
    const input = new CU.CharStream("foo");
    const output = SMT.identifier(input);
    const expected = new CU.CharStream("foo");
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it('should parse "x!0"', () => {
    const input = new CU.CharStream("x!0");
    const output = SMT.identifier(input);
    const expected = new CU.CharStream("x!0");
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it('should fail on "2bad"', () => {
    const input = new CU.CharStream("2bad");
    const output = SMT.identifier(input);
    switch (output.tag) {
      case "success":
        assert.fail();
      case "failure":
        assert(true);
    }
  });
});

describe("IsSatisfiable", () => {
  it("should parse 'sat'", () => {
    const input = new CU.CharStream("sat");
    const output = SMT.IsSatisfiable.parser(input);
    const expected = new SMT.IsSatisfiable(true);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Bool", () => {
  it("should parse 'true'", () => {
    const input = new CU.CharStream("true");
    const output = SMT.Bool.valueParser(input);
    const expected = new SMT.Bool(true);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse 'false'", () => {
    const input = new CU.CharStream("false");
    const output = SMT.Bool.valueParser(input);
    const expected = new SMT.Bool(false);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Var", () => {
  it("should parse 'x'", () => {
    const input = new CU.CharStream("x");
    const output = SMT.Var.parser(input);
    const expected = new SMT.Var("x");
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Let", () => {
  it("should parse a basic let expression", () => {
    const input = new CU.CharStream("(let ((x 2)) 1)");
    const output = SMT.Let.parser(input);
    const expected = new SMT.Let(
      [[new SMT.Var("x"), new SMT.Int(2)]],
      new SMT.Int(1)
    );
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Equals", () => {
  it("should parse an = expression", () => {
    const input = new CU.CharStream("(= 1 2)");
    const output = SMT.Equals.parser(input);
    const expected = new SMT.Equals([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("And", () => {
  it("should parse a basic and expression", () => {
    const input = new CU.CharStream("(and (= 1 2) (= 2 1))");
    const output = SMT.And.parser(input);
    const expected = new SMT.And([
      new SMT.Equals([new SMT.Int(1), new SMT.Int(2)]),
      new SMT.Equals([new SMT.Int(2), new SMT.Int(1)]),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Or", () => {
  it("should parse a basic or expression", () => {
    const input = new CU.CharStream("(or (= 1 2) (= 2 1))");
    const output = SMT.Or.parser(input);
    const expected = new SMT.Or([
      new SMT.Equals([new SMT.Int(1), new SMT.Int(2)]),
      new SMT.Equals([new SMT.Int(2), new SMT.Int(1)]),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Plus", () => {
  it("should parse a basic + expression", () => {
    const input = new CU.CharStream("(+ 1 2)");
    const output = SMT.Plus.parser(input);
    const expected = new SMT.Plus([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Minus", () => {
  it("should parse a basic - expression", () => {
    const input = new CU.CharStream("(- 1 2)");
    const output = SMT.Minus.parser(input);
    const expected = new SMT.Minus([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("LessThan", () => {
  it("should parse a basic < expression", () => {
    const input = new CU.CharStream("(< 1 2)");
    const output = SMT.LessThan.parser(input);
    const expected = new SMT.LessThan([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("LessThanOrEqual", () => {
  it("should parse a basic <= expression", () => {
    const input = new CU.CharStream("(<= 1 2)");
    const output = SMT.LessThanOrEqual.parser(input);
    const expected = new SMT.LessThanOrEqual([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse something a little more complex", () => {
    // const input = new CU.CharStream(
    //   "(<= (x (upperleft x!0)) (x (bottomright x!1)))"
    // );
    const input = new CU.CharStream(
      "(<= (x (upperleft x!0)) (x (bottomright x!1)) ))"
    );
    const output = SMT.LessThanOrEqual.parser(input);
    const expected = new SMT.LessThanOrEqual([
      new SMT.FunctionApplication("x", [
        new SMT.FunctionApplication("upperleft", [new SMT.Var("x!0")]),
      ]),
      new SMT.FunctionApplication("x", [
        new SMT.FunctionApplication("bottomright", [new SMT.Var("x!1")]),
      ]),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("GreaterThan", () => {
  it("should parse a basic > expression", () => {
    const input = new CU.CharStream("(> 1 2)");
    const output = SMT.GreaterThan.parser(input);
    const expected = new SMT.GreaterThan([new SMT.Int(1), new SMT.Int(2)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("GreaterThanOrEqual", () => {
  it("should parse a basic >= expression", () => {
    const input = new CU.CharStream("(>= 1 2)");
    const output = SMT.GreaterThanOrEqual.parser(input);
    const expected = new SMT.GreaterThanOrEqual([
      new SMT.Int(1),
      new SMT.Int(2),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("IfThenElse", () => {
  it("should parse an ite expression", () => {
    const input = new CU.CharStream("(ite (= 1 2) false true)");
    const output = SMT.IfThenElse.parser(input);
    const expected = new SMT.IfThenElse(
      new SMT.Equals([new SMT.Int(1), new SMT.Int(2)]),
      new SMT.Bool(false),
      new SMT.Bool(true)
    );
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("ArgumentDeclaration", () => {
  it("should handle a basic argument declaration", () => {
    const input = new CU.CharStream("((x Bool))");
    const output = SMT.ArgumentDeclaration.parser(input);
    switch (output.tag) {
      case "success":
        expect(output.result[0].name).to.equal("x");
        expect(output.result[0].sort.name).to.equal("Bool");
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should handle a multiple argument declaration", () => {
    const input = new CU.CharStream("((x Bool) (y Column) (z Int))");
    const output = SMT.ArgumentDeclaration.parser(input);
    switch (output.tag) {
      case "success":
        expect(output.result[0].name).to.equal("x");
        expect(output.result[0].sort.name).to.equal("Bool");
        expect(output.result[1].name).to.equal("y");
        expect(output.result[1].sort.name).to.equal("Column");
        expect(output.result[2].name).to.equal("z");
        expect(output.result[2].sort.name).to.equal("Int");
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should handle a Z3-style argument declaration", () => {
    const input = new CU.CharStream("((x!0 Bool) (x!1 Column) (x!2 Int))");
    const output = SMT.ArgumentDeclaration.parser(input);
    switch (output.tag) {
      case "success":
        expect(output.result[0].name).to.equal("x!0");
        expect(output.result[0].sort.name).to.equal("Bool");
        expect(output.result[1].name).to.equal("x!1");
        expect(output.result[1].sort.name).to.equal("Column");
        expect(output.result[2].name).to.equal("x!2");
        expect(output.result[2].sort.name).to.equal("Int");
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should handle an empty declaration", () => {
    const input = new CU.CharStream("()");
    const output = SMT.ArgumentDeclaration.parser(input);
    switch (output.tag) {
      case "success":
        expect(output.result.length).to.equal(0);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("FunctionDefinition", () => {
  it("should parse a basic function definition", () => {
    const input = new CU.CharStream("(define-fun foo () Bool true)");
    const output = SMT.FunctionDefinition.parser(input);
    const expected = new SMT.FunctionDefinition(
      "foo",
      [],
      SMT.Bool.sort,
      new SMT.Bool(true)
    );
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse a basic function definition with args", () => {
    const input = new CU.CharStream(
      "(define-fun SomeComplicatedFunction ((x!0 Column) (x!1 Column)) Column 456)"
    );
    const output = SMT.FunctionDefinition.parser(input);
    const colSort = new SMT.PlaceholderSort("Column");
    const expected = new SMT.FunctionDefinition(
      "SomeComplicatedFunction",
      [
        new SMT.ArgumentDeclaration("x!0", colSort),
        new SMT.ArgumentDeclaration("x!1", colSort),
      ],
      colSort,
      new SMT.Int(456)
    );
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("FunctionApplication", () => {
  it("should parse a basic function application", () => {
    const input = new CU.CharStream("(x 1)");
    const output = SMT.FunctionApplication.parser(input);
    const expected = new SMT.FunctionApplication("x", [new SMT.Int(1)]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse a basic function application with a weird variable", () => {
    const input = new CU.CharStream("(upperleft x!0)");
    const output = SMT.FunctionApplication.parser(input);
    const expected = new SMT.FunctionApplication("upperleft", [
      new SMT.Var("x!0"),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse a slightly less basic function application", () => {
    const input = new CU.CharStream("(cell 1 9)");
    const output = SMT.FunctionApplication.parser(input);
    const expected = new SMT.FunctionApplication("cell", [
      new SMT.Int(1),
      new SMT.Int(9),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });

  it("should parse a nested function application", () => {
    const input = new CU.CharStream("(x (upperleft x!0))");
    const output = SMT.FunctionApplication.parser(input);
    const expected = new SMT.FunctionApplication("x", [
      new SMT.FunctionApplication("upperleft", [new SMT.Var("x!0")]),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Model", () => {
  it("should parse a model definition containing some expression", () => {
    const input = new CU.CharStream("((cell 1 9))");
    const output = SMT.Model.parser(input);
    const expected = new SMT.Model([
      new SMT.FunctionApplication("cell", [new SMT.Int(1), new SMT.Int(9)]),
    ]);
    switch (output.tag) {
      case "success":
        expect(output.result).to.eql(expected);
        break;
      case "failure":
        assert.fail();
    }
  });
});

describe("Grammar", () => {
  it("should parse 'sat'", () => {
    try {
      const output = SMT.parse("sat");
      const expected = [new SMT.IsSatisfiable(true)];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse 'unsat'", () => {
    try {
      const output = SMT.parse("unsat");
      const expected = [new SMT.IsSatisfiable(false)];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse 'true' as a Bool", () => {
    try {
      const output = SMT.parse("true");
      const expected = [new SMT.Bool(true)];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse 'truez' as a Var", () => {
    try {
      const output = SMT.parse("truez");
      const expected = [new SMT.Var("truez")];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse a valid multi-line program (fragment 1)", () => {
    const input = `
sat
(
  (define-fun c2 () Cell
    (cell 1 10))
)`.trim();
    try {
      const output = SMT.parse(input);
      const expected = [
        new SMT.IsSatisfiable(true),
        new SMT.Model([
          new SMT.FunctionDefinition(
            "c2",
            [],
            new SMT.PlaceholderSort("Cell"),
            new SMT.FunctionApplication("cell", [
              new SMT.Int(1),
              new SMT.Int(10),
            ])
          ),
        ]),
      ];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse a valid multi-line program (fragment 2)", () => {
    const input = `
  sat
  (
    (define-fun c2 () Cell
      (cell 1 10))
    (define-fun c1 () Cell
      (cell 1 9))
  )`.trim();
    try {
      const output = SMT.parse(input);
      const expected = [
        new SMT.IsSatisfiable(true),
        new SMT.Model([
          new SMT.FunctionDefinition(
            "c2",
            [],
            new SMT.PlaceholderSort("Cell"),
            new SMT.FunctionApplication("cell", [
              new SMT.Int(1),
              new SMT.Int(10),
            ])
          ),
          new SMT.FunctionDefinition(
            "c1",
            [],
            new SMT.PlaceholderSort("Cell"),
            new SMT.FunctionApplication("cell", [
              new SMT.Int(1),
              new SMT.Int(9),
            ])
          ),
        ]),
      ];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail();
    }
  });

  it("should parse a valid multi-line program (fragment 3)", () => {
    const input = `
sat
(
  (define-fun c2 () Cell
  (cell 1 10))
  (define-fun c1 () Cell
  (cell 1 9))
  (define-fun ccolleft ((x!0 Column) (x!1 Column)) Bool (let ((a!1 (not (<= (x (upperleft x!0)) (x (bottomright x!1)))))) (and (= (y (upperleft x!1)) (y (upperleft x!0))) (= (y (bottomright x!1)) (y (bottomright x!0))) a!1)))
)`.trim();
    try {
      const output = SMT.parse(input);
      const expected = [
        new SMT.IsSatisfiable(true),
        new SMT.Model([
          new SMT.FunctionDefinition(
            "c2",
            [],
            new SMT.PlaceholderSort("Cell"),
            new SMT.FunctionApplication("cell", [
              new SMT.Int(1),
              new SMT.Int(10),
            ])
          ),
          new SMT.FunctionDefinition(
            "c1",
            [],
            new SMT.PlaceholderSort("Cell"),
            new SMT.FunctionApplication("cell", [
              new SMT.Int(1),
              new SMT.Int(9),
            ])
          ),
          new SMT.FunctionDefinition(
            "ccolleft",
            [
              new SMT.ArgumentDeclaration(
                "x!0",
                new SMT.PlaceholderSort("Column")
              ),
              new SMT.ArgumentDeclaration(
                "x!1",
                new SMT.PlaceholderSort("Column")
              ),
            ],
            SMT.Bool.sort,
            new SMT.Let(
              [
                [
                  new SMT.Var("a!1"),
                  new SMT.Not(
                    new SMT.LessThanOrEqual([
                      new SMT.FunctionApplication("x", [
                        new SMT.FunctionApplication("upperleft", [
                          new SMT.Var("x!0"),
                        ]),
                      ]),
                      new SMT.FunctionApplication("x", [
                        new SMT.FunctionApplication("bottomright", [
                          new SMT.Var("x!1"),
                        ]),
                      ]),
                    ])
                  ),
                ],
              ],
              new SMT.And([
                new SMT.Equals([
                  new SMT.FunctionApplication("y", [
                    new SMT.FunctionApplication("upperleft", [
                      new SMT.Var("x!1"),
                    ]),
                  ]),
                  new SMT.FunctionApplication("y", [
                    new SMT.FunctionApplication("upperleft", [
                      new SMT.Var("x!0"),
                    ]),
                  ]),
                ]),
                new SMT.Equals([
                  new SMT.FunctionApplication("y", [
                    new SMT.FunctionApplication("bottomright", [
                      new SMT.Var("x!1"),
                    ]),
                  ]),
                  new SMT.FunctionApplication("y", [
                    new SMT.FunctionApplication("bottomright", [
                      new SMT.Var("x!0"),
                    ]),
                  ]),
                ]),
                new SMT.Var("a!1"),
              ])
            )
          ),
        ]),
      ];
      expect(output).to.eql(expected);
    } catch (e) {
      assert.fail(e);
    }
  });

  it("should parse all of the output from a real Z3 run (case 1)", () => {
    try {
      const input = fs.readFileSync("test/z3-model-output-test.smt", "utf8");
      const output = SMT.parse(input);
      assert(true);
    } catch (e) {
      console.log(e);
      assert.fail(e);
    }
  });

  it("should parse all of the output from a real Z3 run (case 2)", () => {
    try {
      const input = fs.readFileSync("test/z3-model-output-test-2.smt", "utf8");
      const output = SMT.parse(input);
      assert(true);
    } catch (e) {
      console.log(e);
      assert.fail(e);
    }
  });

  it("should parse all of the output from a real Z3 run (case 3)", () => {
    try {
      const input = fs.readFileSync("test/z3-model-output-test-3.smt", "utf8");
      const output = SMT.parse(input);
      assert(true);
    } catch (e) {
      console.log(e);
      assert.fail(e);
    }
  });
});
