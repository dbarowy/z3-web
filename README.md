# z3-web

This project exposes a locally-installed Z3 instance as a web service.

## Installation

Run:

```
$ npm install
```

You will also need to ensure that [Z3 is installed locally](https://github.com/Z3Prover/z3/releases), and you also need a local copy of OpenSSL. Windows users can get OpenSSL by installing the [Git for Windows](https://git-scm.com/download/win) package, which includes an `openssl.exe` binary. Both `z3` and `openssl` need to be in the user's path.

### Generating SSL certificates

`z3-web` uses SSL by default, so in order to run it, you will need SSL certificates. It looks in the `certs` directory of the repository for two files, a private key called `certs/z3web.key` and a public key called `certs/z3web.cert`. You may generate these yourself, but for development purposes, a self-signed certificate suffices.

#### Windows 10

#### Mac OS

1. In the repository root, run `scripts/certgen.sh`.
2. Double-click the `certs/z3web.cert` file to open the Keychain Access program. You will be prompted to enter your password.
3. Double-click on the certificate just added. It will have a randomly-generated name like `3cb69473-50de-4bac-a7a9-3e0c272131b4`. If you're having trouble finding it, look for a certificate with an expiration date roughly one month from now.
4. Expand the `Trust` item and select `Always Trust` from the `When using this certificate` dropdown.

### Installing Z3

These should not be considered canonical Z3 installation instructions, but here's what works for me.

#### Windows 10

1. Download [the 64 bit release ZIP file](https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-win.zip) and unzip it to `C:\Program Files`.
2. Find the path of the `bin` folder in your Z3 installation path. For me, it is `C:\Program Files\z3-4.8.10-x64-win\bin`.
3. Open Explorer, right-click on `This PC` and select `Properties` and find the `Advanced system settings` link, which will bring up a `System Properties` dialog.
4. Click the `Environment Variables` button, select `Path` in the `User variables` pane, and click `Edit...`.
5. Click the `New` button and then paste your `bin` path into the text box.
6. Click `OK` to exit the edit window.
7. Click `OK` to exit the rest of the windows.

#### Mac OS

Z3 is available via [Homebrew](https://brew.sh/). If you have Homebrew installed, just run:

```
$ brew install z3
```

#### Linux

On Debian, Z3 is available via `apt`. Run:

```
$ sudo apt install z3
```

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
