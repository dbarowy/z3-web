import express from "express";
import cors from "cors";
import { spawnSync } from "child_process";
import { SMT, Expr } from "smtliblib";
import { Dictionary } from "./dict";
import * as fs from "fs";
import https from "https";
import { exit } from "node:process";

// Set defaults here
class Opts {
  constructor(
    public use_tls: boolean = false,
    public cert_prv = "certs/z3web.key",
    public cert_pub = "certs/z3web.cert",
    public host = "localhost",
    public port = 3456
  ) {}
}

/**
 * This function calls Z3 on the command line and returns
 * the output as a string.
 * @param program An SMTLIB query.
 * @returns
 */
function callZ3(program: string): string {
  const child = spawnSync("z3", ["-in"], { input: program });
  return child.stdout.toString();
}

/**
 * Are the TLS certificates available? Prints a diagnostic
 * message if certs are missing.
 * @returns true iff both certificates are availabl
 */
function checkCertsAvailable(opts: Opts) {
  // are the certs installed?
  console.log(process.cwd());
  if (!fs.existsSync(opts.cert_prv)) {
    console.error(opts.cert_prv + " is missing");
  }
  if (!fs.existsSync(opts.cert_pub)) {
    console.error(opts.cert_pub + " is missing");
  }
  if (!fs.existsSync(opts.cert_prv) || !fs.existsSync(opts.cert_pub)) {
    console.error("Cannot start Z3 webservice.");
    console.error(
      "Please ensure that the following TLS certificates are available:"
    );
    console.error("Private key: " + opts.cert_prv);
    console.error("Public key: " + opts.cert_pub);
    console.error(
      "The /scripts/certgen.sh will generate and install these scripts for you."
    );

    return false;
  }
  return true;
}

function argParse(args: string[]): Opts {
  const opts = new Opts();
  for (const arg of args) {
    switch (arg) {
      case "--tls":
        opts.use_tls = true;
        break;
    }
  }
  return opts;
}

/**
 * Start up Z3 and handle requests to and from the web using Express.
 */
function main() {
  const app = express();
  const z3stacks = new Dictionary<string[]>();
  let stacknum = 0;
  const MAX_STACKS = 10;

  const opts = argParse(process.argv);

  if (opts.use_tls && !checkCertsAvailable(opts)) {
    exit(1);
  }

  app.use(cors()); // Allow CORS requests
  app.use(express.json({ limit: 1073741824 })); // set POST limit to 1GB

  /**
   * Find a model for the given constraints.
   */
  app.post("/", (req, res) => {
    console.log("HERE 1");

    if (!req.body.program) {
      console.log("Invalid program.");
      exit(1);
    }

    try {
      // get user input
      const program = req.body.program as string;

      // for debugging
      console.log("Query: \n" + program);

      // call Z3 with user input
      const output = callZ3(program);

      // parse it
      const ast = SMT.parse(output, false);

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
      const ast = SMT.parse(output, false);

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

  // optionally use TLS
  if (opts.use_tls) {
    https
      .createServer(
        {
          key: fs.readFileSync(opts.cert_prv),
          cert: fs.readFileSync(opts.cert_pub),
        },
        app
      )
      .listen(opts.port, function () {
        console.log(
          `Z3 web service listening on https://${opts.host}:${opts.port}`
        );
      });
  } else {
    app.listen(opts.port, () => {
      console.log(
        `Z3 web service listening on http://${opts.host}:${opts.port}`
      );
    });
  }
}

main();
