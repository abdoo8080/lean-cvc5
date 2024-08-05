# Test framework

- [Test framework](#test-framework)
  - [Filtering](#filtering)
  - [Associated files](#associated-files)


Tests should be in (sub-directories of) the `Test` directory at the root of the package.

**NB**: `Test/Init.lean` is always ignored as it is assumed to contain boilerplate code for the
actual tests.

Run all tests with

```text
lake test
```

## Filtering

To run a subset of your tests, pass some string arguments to `lake test`. The test runner will then
only run tests that have one of these string arguments as a sub-string of its path.

For instance,

```text
lake test -- feature1 Feature2 
```

will only run tests with a path that has **either** `feature1` or `Feature2` as a substring, such as
`Test/feature1.lean`, `Test/feature1Test1.lean`, `Test/Feature2/test1.lean`, ...

where 

## Associated files

A given test file `Test/Path/myTest.lean` has two optional associated files that modify the
conditions for a test to succeed.

`Test/Path/myTest.out`: if present, then its (trimmed) content must match the (trimmed)
`stdout` of the test. If absent, the test's `stdout` must be empty.

`Test/Path/myTest.err`: if present, then its (trimmed) content must match the
(trimmed) `stderr` of the test; also, the test must produce a non-zero return code. If absent, the
test's `stderr` must be empty and the test must produce a successful return code (`0`).
