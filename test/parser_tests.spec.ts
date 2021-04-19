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
