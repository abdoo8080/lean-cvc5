# Lean cvc5 FFI

## Overview

The Lean cvc5 is a Foreign Function Interface (FFI) library that provides a minimal interface to the
cvc5 solver in Lean. It was designed to support the needs of the
[lean-smt] tactic. The FFI allows Lean programs to interact
with cvc5 by calling its functions and accessing its API.

## Limitations

- Minimal interface to the cvc5 solver (contributions are welcome!)

## Getting Started

To use the cvc5 FFI in your project, add the following line to your list of dependencies in
`lakefile.lean`:

```lean
require smt from git "https://github.com/abdoo8080/lean-cvc5.git" @ "main"
```

## Building

Build this library by running the `init` script before `lake`-building:

```text
lake run init
[...]
lake build
[...]
```

## Contributing

Contributions to the Lean cvc5 FFI project are welcome! If you would like to contribute, please
follow these guidelines:

1. Fork the repository
2. Create a new branch for your feature or bug fix
    <!-- 3. Make your changes and ensure all tests pass -->
3. Submit a pull request with a clear description of your changes

[lean-smt]: https://github.com/ufmg-smite/lean-smt