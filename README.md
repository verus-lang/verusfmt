# Verusfmt

An opinionated formatter for [Verus] code.

## Updating verusfmt

If you've installed a pre-built binary, you can update to the latest release using
```sh
verusfmt --update
```

## Installing and Using Verusfmt

We support multiple install methods. Get the [latest release](https://github.com/verus-lang/verusfmt/releases/latest) using:

- Pre-built binaries (recommended)

  + <details><summary>Linux/MacOS (click to expand)</summary>

    ```sh
    curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.sh | sh
    ```
    </details>

  + <details><summary>Windows (click to expand)</summary>

    ```sh
    powershell.exe -ExecutionPolicy RemoteSigned -c "irm https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.ps1 | iex"
    ```
    </details>

- <details><summary>cargo install (click to expand)</summary>

  ``` sh
  cargo install verusfmt --locked
  ```
  </details>

These will install the `verusfmt` binary. You can then run it on a file using:

``` sh
verusfmt foo.rs
```

See `verusfmt --help` for more options and details.

## Goals

1. Make it easier to read and contribute to [Verus] code by automatically
   formatting it in a consistent style (added bonus: eliminating soul-crushing
   arguments about style).
2. Produce acceptably "pretty" output.
3. Run fast!  `verusfmt` may be run in pre-submit scripts, CI, etc., so it can't
   be slow.
4. Keep the code reasonably simple. Pretty printers are [notoriously
   hard](https://journal.stuffwithstuff.com/2015/09/08/the-hardest-program-ive-ever-written/),
   so we try to take steps to reduce that difficulty, so that `verusfmt` can be
   updated and adapted with a reasonable amount of effort. 

### FAQ

1. Why not adapt [`rustfmt`] for [Verus] idioms?

    While Verus has Rust-like syntax, it necessarily also deviates from it to
    support its idioms naturally, and thus not only would the parser for
    `rustfmt` need updates, but also careful changes to the emitter would be
    needed to have code look natural. Additionally, since practically all Verus
    code is inside the `verus!{}` macro (and `rustfmt` does not easily support
    formatting even regular Rust inside macros), a non-trivial amount of effort
    would be required to perform the plumbing and maintenance required to
    support both formatting _outside_ the `verus!{}` macro (as Rust code), while
    also formatting Verus code _inside_ the macro.

1. Does `verusfmt` match [`rustfmt`] on code outside the `verus!{}` macro?

    Yes, by default, `verusfmt` handles code inside the `verus!{}` macro, and
    also runs `rustfmt` to handle code outside the macro. Neither should clash
    with the other or override each other's formatting changes. Thus, this
    makes it easier to incrementally verify small amounts of code inside a
    larger unverified Rust crate.  You can disable the invocation of `rustfmt`
    using `--verus-only`.

1. Why not build this as a feature of [Verus]?

    By the time Verus receives an AST from `rustc`, we've already lost
    information about whitespace and comments, meaning that we couldn't preserve
    the comments in the reformatted code. Plus, firing up all of `rustc` just to
    format some code seems heavyweight.

## Future Work
- Special handling for commonly used macros, like `println!`, `state_machine!`
- Enforce the [Rust naming policy](https://doc.rust-lang.org/beta/style-guide/advice.html#names)? 

## Non-Future Work
- We currently have no plans to sort `use` declarations the way [`rustfmt`] does
- We do not intend to parse code that [Verus] itself cannot parse.  Sometimes `verusfmt` 
  happens to parse such code, but that is unintentional and cannot be counted upon.
- Perfectly match the formatting produced by [`rustfmt`]
- Handle comments perfectly -- they're surprisingly hard!

## Design Overview

Our design is heavily influenced by the [Goals](#Goals) above.  Rather than
write everything from scratch ([a notoriously hard
undertaking](https://journal.stuffwithstuff.com/2015/09/08/the-hardest-program-ive-ever-written/)),
we use a parser-generator to read in Verus source code, and a pretty-printing
library to format it on the way out.  We try to keep each phase as performant
as possible, and we largely try to keep the formatter stateless, for
performance reasons but more importantly to try to keep the code reasonably
simple and easy to reason about.  Hence we sometimes deviate from Rust's style
guidelines for the sake of simplicity.

### Parsing

We define the syntax of Verus source code using [this
grammar](src/verus.pest), which is processed by the [Pest](https://pest.rs/)
parser generator, which relies on Parsing Expression Grammars
([PEG](https://en.wikipedia.org/wiki/Parsing_expression_grammar)s).  It
conveniently allows us to define our notion of whitespace and comments, which
the remaining rules can then ignore; Pest will handle them implicitly.  We
explicitly ignore the code outside the `verus!` macro, leaving it to
[`rustfmt`].  We prefer using explicit rules for string constants, since it
allows a more uniform style when formatting the code.  In some places, we have
multiple definitions for the same Verus construct, so that we can format it
differently depending on the context (see, e.g., `attr_core`).  Many of the
rules are designed to follow the corresponding description in [The Rust
Reference](https://doc.rust-lang.org/beta/reference/introduction.html).

### Formatting

Rather than try to format things ourselves, we rely on the
[pretty] crate, based on [Philip
Wadler's](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf)
design for a pretty printer.  The core idea is that you create a set of possible
code layouts, and the pretty printer then uses its internal heuristics to pick
the prettiest version.  Typically this means that we specify where, say, line breaks
can occur if the code needs to be placed on multiple lines, but you can also
use the `group` operator to say that for a particular code snippet, the pretty printer
should also consider placing everying in the group on a single line.

As much as possible, we try to keep the formatter simple by arranging for the 
formatting of a node to be computed by simply formatting each of its children.
Sometimes this requires splitting a node in the parser, so that we can format
the same item in two different ways, depending on its context.  Rust contexts
can be tricky to track dynamically (since Rust allows expressions in statements,
and statements in expression), so we try to keep the formatter stateless to reduce
the scope for errors.

## Contributing

We welcome contributions! Please read on for details.

We consider it a bug in `verusfmt` if you provide `verusfmt` with code
that [Verus] accepts and `verusfmt` produces code that Verus does not accept
or code that has different semantics from the original.  When this happens,
please open a GitHub issue with a minimal example of the offending code
before and after formatting.

If `verusfmt` produces valid code but you dislike the formatting, please open
a GitHub pull request with your proposed changes and rationale for those changes.
Please ensure that existing test cases still pass (see below for more details),
unless your goal is to change how some of those test cases are handled.  Please
also include new/updated tests that exercise your proposed changes.

### Tips for Developing a Fix or an Improvement

1. Write out a small example `.rs` file focusing on the specific thing you want
   to improve.  Test `verusfmt` on your reduced example to make sure the issue
   still manifests; running with `--check` is very helpful with this process.
   The smaller your example file, the easier subsequent steps will be.
2. When running with `--check`, you can also add `-dd` to see 2nd level debug
   output, which includes the parse tree.  Look through the parse tree and
   identify rules relevant to your particular example.
3. Once you find the relevant rule names, if the issue seems to be a misparse,
   jump over to `src/verus.pest` to find the relevant rule(s) and see if the
   grammar needs to be fixed or improved.
4. If the parsing is fine but the printing is an issue, then look for the
   relevant rule(s) in the `to_doc` function in `src/lib.rs`. This might be a
   bit difficult to understand immediately, so having the [pretty] docs handy
   is quite helpful.  Also, it is helpful to look at the relevant debug print
   (using `-d` or `-dd`), which gives a serialized version of the recursively
   expanded `doc`, right before it has been optimized, so figuring out which
   particular bit of it is not behaving as you like is quite helpful.
5. Attempt fixes until the small example succeeds.
6. Add the example into the tests---see the [Testing](#testing) section below.
7. If fixing the rule for your small example succeeds but breaks other tests,
   you may need to split the relevant rule in the parsing grammar into two
   separate cases, so that each case can be formatted independently.  See
   `comma_delimited_exprs_for_verus_clauses`  and
   `groupable_comma_delimited_exprs_for_verus_clauses`, for example.

## Testing

### Rust-like formatting

In general, we try to adhere to Rust's style guide.  Tests for such adherence live in
[tests/rustfmt-matching.rs](tests/rustfmt-matching.rs).  These tests will compare the output
of [`rustfmt`] to that of `verusfmt`.  You can run them via `cargo test`.

### Verus-like formatting

In various places, we deviate from Rust's style, either to simplify the
formatter or to handle [Verus]-specific syntax.  Tests for formatting such code
live in [tests/verus-consistency.rs](tests/verus-consistency.rs).  You can add
a new test or modify an existing one by writing/changing the input code.  The
test's correct answer is maintained via the [Insta testing framework](https://insta.rs).

Insta recommends installing the `cargo-insta` tool for an improved review experience:
```
cargo install cargo-insta
```

You can run the tests normally with `cargo test`, but it's often more convenient
to run the tests and review the results via:
```
cargo insta test
cargo insta review
```
or more succinctly:
```
cargo insta test --review
```


[Verus]: https://github.com/verus-lang/verus
[`rustfmt`]: https://github.com/rust-lang/rustfmt
[pretty]: https://crates.io/crates/pretty
