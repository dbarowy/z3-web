import express from "express";
import cors from "cors";
import { spawnSync } from "child_process";
import { SMT } from "./smt";

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
    // call Z3 with user input
    const program = req.query.program as string;
    const output = callZ3(program);

    // parse it
    const ast = SMT.parse(output);

    // send it back to the user
    res.send(JSON.stringify(ast));
  });

  app.listen(port, () => {
    console.log(`Example application listening at http://localhost:${port}`);
  });
}

main();
