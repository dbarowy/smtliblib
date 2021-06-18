import { SMT } from "../src/smt";
import { expect } from "chai";
import "mocha";

describe("Real", () => {
    it('should print whole numbers with one decimal place', () => {
      const r = new SMT.Real(1);
      expect(r.formula).to.eql("1.0");
    });

    it('should print numbers smaller than one with a leading zero', () => {
        const r = new SMT.Real(.1);
        expect(r.formula).to.eql("0.1");
    });

    it("should print numbers with a fraction with arbitrary precision", () => {
        const r = new SMT.Real(1.23456789);
        expect(r.formula).to.eql("1.23456789");
    })

    it("should print negative numbers with a fraction with arbitrary precision", () => {
        const r = new SMT.Real(-1.23456789);
        expect(r.formula).to.eql("-1.23456789");
    })
});