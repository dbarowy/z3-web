# z3-web

This project exposes a locally-installed Z3 instance as a web service.

## Installation

Run:

```
$ npm install
```

You will also need to ensure that [Z3 is installed locally](https://github.com/Z3Prover/z3/releases). It should be in the path of whatever shell you use to run `npm` below.

## Running

Run:

```
$ npm run start
```

The web service will listen on `http://localhost:3456` by default.

## Sending Requests to this Web Service

This service expects to receive queries via HTTP GET request. Your Z3 query should be encoded as a URL-encoded SMTLIBv2 string passed as the `program` parameter. For example,

The program

```
(check-sat)
```

can be sent to this service as:

```
http://localhost:3456/?program=%28check-sat%29%0A
```

## Development

If you want to modify this package, there is a debug mode that is very helpful. You should instead run:

```
$ npm run dev:debug
```

which will start up the web service with the `nodemon` monitor. There are two benefits to this:

1. `nodemon` will detect when your `.ts` code changes, recompile and restart the web service, and
2. it will run this code "breakpointable", and if you've configured VSCode to "auto-attach" to node processes launched from the VSCode terminal (this is the default behavior), then you can set breakpoints in VSCode and inspect the running state of the web service.

## Security Notes

The service does no filtering of queries of any kind, and it calls Z3 synchronously, so be warned: it's probably not secure and it's easy to stage a denial-of-service attack. If you need something for public deployment, this isn't it. I developed this wrapper to make research code possible.
