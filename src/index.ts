import express from "express";
import util from "util";
import { spawn, spawnSync } from "child_process";

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

  app.get("/", (req, res) => {
    res.send(callZ3("(declare-const x Int) (check-sat) (get-model)"));
    // res.send("hello world!");
  });

  app.listen(port, () => {
    console.log(`Example application listening at http://localhost:${port}`);
  });
}

main();
