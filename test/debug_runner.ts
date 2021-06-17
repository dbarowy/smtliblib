import * as fs from 'fs';
import { exit } from 'process';
import { SMT } from "../src/smt";
// import * as beautify from "json-beautify";
const beautify = require("json-beautify");

if (process.argv.length != 3) {
  console.log("Usage:");
  console.log("\tnode debug_runner.js <file.smt>");
  exit(1);
}

const file = process.argv[2];

fs.readFile(file, 'utf8' , (err, data) => {
  if (err) {
    console.error(err)
    return
  }
  try {
    const output = SMT.parse(data);
    const s = beautify(SMT.serialize(output), null, 2, 80);
    console.log("Successful parse.");
    console.log(s);
  } catch (err) {
    console.log("Could not parse data.");
  }
})