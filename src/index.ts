import express from "express";
import cors from "cors";
import { spawnSync } from "child_process";
import { SMT } from "./smt";
import * as fs from "fs";

/**
 * This function
 * @param program
 * @returns
 */
function callZ3(program: string): string {
  const child = spawnSync("z3", ["-in"], { input: program });
  return child.stdout.toString();
}

/**
 * Start up Z3 and handle requests to and from the web using Express.
 */
function main() {
  const app = express();
  const port = 3456;

  app.use(cors()); // Allow CORS requests

  app.get("/", (req, res) => {
    if (!req.query.program) {
      console.log("Invalid program.");
    }

    // get user input
    const program = req.query.program as string;

    // for debugging
    console.log(program);

    // call Z3 with user input
    const output = callZ3(program);

    // for debugging
    console.log(output);

    // debug: save the string to a file
    fs.writeFileSync("z3Model.smt", output);

    // parse it
    try {
      const ast = SMT.parse(output);

      // make it JSON
      const json_ast = JSON.stringify(ast);

      // for debugging
      console.log(json_ast);

      // send it back to the user
      res.send(json_ast);
    } catch (e) {
      console.log(e);
    }
  });

  app.listen(port, () => {
    console.log(`Example application listening at http://localhost:${port}`);
  });
}

main();
