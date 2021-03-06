# Simple SAT #

## Description ##
The Simple SAT (simple-sat) project is an minimal implementation of a SAT solver
for Boolean algebras.

## Getting Started ##
### Prerequisites ###
This package uses the git source control system and the stack build system.  For information on how to install these tools for your platform, please consult the following url:

[Haskell Stack Documentation](https://docs.haskellstack.org/en/stable/README/)

[GIT installation](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git)

You will also need a git-hub account in order to access the source
code repository.

### Installing ###
Run the following commands to download and install the HEAD version.

```bash
$ git clone git@github.com:dlewissandy/simple-sat.git
$ cd simple-sat
$ stack build
```
### Running the tests ###
You can run the unit tests from the command line using the following commands:
```bash
$ stack test
```

The unit-tests can be invoked with options that fine tune the test behavior.   For a complete list of testing options, you can invoke the following:
```bash
$ stack test --test-arguments "--help"
```

# Example Usage #
For example usage, please consult the code simple-sat source code in the app
folder, or execute the simple-sat application from the command line:

```bash
$ stack build
$ stack exec -- simple-sat queens4.logic
```
The example can be invoked with options that control the source file and output.
For a complete list of options, consult the program's help command:
```bash
$ stack exec -- simple-sat --help
```

# Contributing #
Please read [CONTRIBUTING.md](CONTRIBUTING.md) for details on our code of
conduct, and the process for submitting pull requests to us.                                                                                                 
