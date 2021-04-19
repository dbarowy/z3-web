import { SMT } from "../src/smt";
import { CharUtil as CU } from "parsecco";
import { assert, expect } from "chai";
import "mocha";

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

describe("Grammar", () => {
  it("should parse 'sat'", () => {
    const output = SMT.parse("sat");
    const expected = [new SMT.IsSatisfiable(true)];
    expect(output).to.eql(expected);
  });

  it("should parse 'unsat'", () => {
    const output = SMT.parse("unsat");
    const expected = [new SMT.IsSatisfiable(false)];
    expect(output).to.eql(expected);
  });
});
