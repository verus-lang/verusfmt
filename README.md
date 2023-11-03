# Verusfmt

An opinionated formatter for [Verus] code.

## WARNING

Verusfmt is highly experimental code. Make backups of your files before trying
Verusfmt on them.

## Goals

1. Make it easier to read and contribute to [Verus] code by automatically
   formatting it in a consistent style (added bonus: eliminating soul-crushing
   arguments about style).
2. Produce acceptably "pretty" output.
3. Run fast!  Verusfmt may be run in pre-submit scripts, CI, etc., so it can't
   be slow.
4. Keep the code reasonably simple. Pretty printers are [notoriously
   hard](https://journal.stuffwithstuff.com/2015/09/08/the-hardest-program-ive-ever-written/),
   so we try to take steps to reduce that difficulty, so that Verusfmt can be
   updated and adapted with a reasonable amount of effort. 

### FAQ

1. Why not adapt [`rustfmt`] for [Verus] idioms?
 **TODO**: jayb

1. Why not build this as a feature of [Verus]?
By the time Verus receives an AST from `rustc`, we've already lost information
about whitespace and comments, meaning that we couldn't preserve the comments
in the reformatted code.  Plus, firing up all of `rustc` just to format some
code seems heavyweight.

## Future Work
- Special handling for commonly used macros, like `println!`, `state_machine!`
- In `record_expr_field_list` and `record_pat_field_list`, handle vanishing comma's interaction with `rest_pat`
- Enforce the [Rust naming policy](https://doc.rust-lang.org/beta/style-guide/advice.html#names)? 

## Non-Future Work
- We currently have no plans to sort `use` declarations the way [`rustfmt`] does
- Perfectly match the formatting produced by [`rustfmt`]

## Code Overview

**TODO**

## Contributing

## Testing

### Rust-like formatting

In general, we try to adhere to Rust's style guide.  Tests for such adherence live in
[tests/rustfmt-tests.rs](tests/rustfmt-tests.rs).  These tests will compare the output
of [rustfmt](https://github.com/rust-lang/rustfmt) to that of `verusfmt`.  You can run
them via `cargo test`.

### Verus-like formatting

In various places, we deviate from Rust's style, either to simplify the formatter
or to handle [Verus]-specific syntax.  Tests for formatting such code live in
[tests/snap-tests.rs](tests/snap-tests.rs).  You can add a new test or modify an
existing one by writing/changing the input code.  The test's correct answer is
maintained via the [Insta testing framework](https://insta.rs).

Insta recommends installing the `cargo-insta` tool for an improved review experience:
```
cargo install cargo-insta
```

You can run the tests normally with `cargo test`, but if we end up with
multiple snapshot assertions in a single test function, we might want to use
`cargo insta test` instead which collects all snapshot changes in one go.

You can run the tests and review the results via:
```
cargo insta test
cargo insta review
```
or more succinctly:
```
cargo insta test --review
```


[Verus](https://github.com/verus-lang/verus)
[`rustfmt`](https://github.com/rust-lang/rustfmt)
