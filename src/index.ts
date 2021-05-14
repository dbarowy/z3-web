import express from "express";
import cors from "cors";
import { spawnSync } from "child_process";
import { SMT, Expr } from "smtliblib";
import { Dictionary } from "./dict";

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
  const z3stacks = new Dictionary<string[]>();
  let stacknum = 0;
  const MAX_STACKS = 10;

  app.use(cors()); // Allow CORS requests

  /**
   * Find a model for the given constraints.
   */
  app.get("/", (req, res) => {
    if (!req.query.program) {
      console.log("Invalid program.");
    }

    try {
      // get user input
      const program = req.query.program as string;

      // for debugging
      console.log(program);

      // call Z3 with user input
      const output = callZ3(program);

      // parse it
      const ast = SMT.parse(output);

      // make it JSON
      const json_ast = SMT.serialize(ast);

      // assign a stacknum
      const json_resp = { stacknum: stacknum, ast: json_ast };

      // put the original request into the save query stack
      z3stacks.put(stacknum.toString(), [program]);

      // if it's time to expire an old stack, do so
      if (z3stacks.contains((stacknum - 10).toString())) {
        z3stacks.del((stacknum - 10).toString());
      }

      // stringify
      const ast_str = JSON.stringify(json_resp);

      // bump stacknum
      stacknum++;

      // send it back to the user with a stack number
      res.send(ast_str);
    } catch (e) {
      console.log(e);
    }
  });

  /**
   * Find the next satisfying model by providing extra constraints.  The new
   * model is returned as a JSON-serialized AST.  The user is responsible
   * for providing something that makes sense logically-- the addition
   * is simply appended to previous constraints.
   */
  app.get("/next/:stacknum", (req, res) => {
    if (
      !req.params.stacknum ||
      !z3stacks.contains(req.params.stacknum) ||
      !req.query.negate
    ) {
      res.send("Invalid model iteration.");
    }

    try {
      // get saved context
      const stack = z3stacks.get(req.params.stacknum);

      // get latest addition
      const negation = req.query.negate as string;

      // convert saved context and latest addition into one big query string
      const program = stack.join("\n") + "\n" + negation;

      // for debugging
      console.log(program);

      // call Z3 with user input
      const output = callZ3(program);

      // parse it
      const ast = SMT.parse(output);

      // make it JSON
      const json_ast = SMT.serialize(ast);

      // push the latest addition onto the stack
      stack.push(negation);

      // stringify
      const ast_str = JSON.stringify(json_ast);

      // send it back to the user with a stack number
      res.send(ast_str);
    } catch (e) {
      console.log(e);
    }
  });

  app.get("/user/:id", function (req, res) {
    res.send("user " + req.params.id);
  });

  app.listen(port, () => {
    console.log(`Example application listening at http://localhost:${port}`);
  });
}

main();
