import express from "express";
import util from "util";
import { exec } from "child_process";

const exe = util.promisify(exec); // do magic JavaScript stuff

async function callZ3(program: string): Promise<string> {
  const { stdout, stderr } = await exe(
    "z3 -in < " + "TODO HERE STDIN HOWTO IN NODE?"
  );
  console.log("stdout:", stdout);
  console.log("stderr:", stderr);
  return stdout;
}

/**
 * Start up Z3 and handle requests to and from the web using Express.
 */
function main() {
  const app = express();
  const port = 3456;
  let i = 0;

  app.get("/", (req, res) => {
    res.send(i.toString());
    i++;
  });

  app.listen(port, () => {
    console.log(`Example application listening at http://localhost:${port}`);
  });
}

main();
