import * as fs from 'fs';
import { SMT } from "../src/smt";

const file = process.argv[2];

fs.readFile(file, 'utf8' , (err, data) => {
  if (err) {
    console.error(err)
    return
  }
  try {
    const output = SMT.parse(data);
    console.log("Successful parse.");
  } catch (err) {
    console.log("Could not parse data.");
  }
})