# Unreleased

# v0.5.1

* Add support for `returns` clauses (see [verus#1283](https://github.com/verus-lang/verus/pull/1283))
* Add support for `assume_specification` (see [verus#1368](https://github.com/verus-lang/verus/pull/1368))

# v0.5.0

* Improve handling of inner-docstring comments (i.e., `///`-prefixed comments)

# v0.4.3

* Support handling of capturing macros (`macro_pat`) during pattern matches

# v0.4.2

* Improved handling of comments around clauses/stanzas
  - Each comment now maintains loyalty to the clause the user picked it to stay with, rather than automatically migrating to the previous clause in the presence of `assert ... by { ... }`-style constructs
* Support parsing for const generic literals
* Support parsing `opens_invariants` with specific concrete sets

# v0.4.1

* Minor fix to prevent panic on formatting files containing unbalanced parentheses in strings/chars/...

# v0.4.0

* Handle comments inside `&&&`/`|||`-bulleted blocks better

# v0.3.8

* Support dividing statement lists into clauses/stanzas

# v0.3.7

* Support attributes in `broadcast group`s

# v0.3.6

* Support parsing empty requires/ensures/... clauses

# v0.3.5

* Fix incorrect parsing of string literals containing "verus!{"
* Support automatic formatting of the `seq!` macro

# v0.3.4

* Support const generic arguments

# v0.3.3

* Introduce `--update` to update to latest Verusfmt easily
  - Only works on [pre-built binaries](https://github.com/verus-lang/verusfmt?tab=readme-ov-file#installing-and-using-verusfmt), the recommended way to install verusfmt.

# v0.3.2

* Support automatic formatting of the `calc!` macro
* Support for named iterators in `for` loops

# v0.3.1

* Support generic argument binding
  - Useful for associated type constraints, such as `trait Foo<T>: Bar<V = Baz<T>>`

# v0.3.0

* Support attributes on `broadcast group` items
* Improve styling of `broadcast use`s, ensuring trailing newline
* Add support for the `no_unwind` clause on functions

# v0.2.11

* Improve handling of `rustfmt.toml` for non-`verus!` code
  - Rather than picking up `rustfmt.toml` based on working directory, it is now picked up based on the file being formatted. This now matches the search that `rustfmt` itself does.

# v0.2.10

* Add support for `broadcast proof`, `broadcast group`, and `broadcast use` (see [verus#1022](https://github.com/verus-lang/verus/pull/1022))

# v0.2.9

* Add support for `invariant_except_break` clauses, recently added to Verus
* Support arbitrary permutation of clauses in loops, rather than a pre-specified order

# v0.2.8

* Add support for `for` loops with invariants, recently added to Verus
* Improve parsing of range expressions (e.g., `0..(1 + 2)`) that start "float-like"

# v0.2.7

* Improve `verus!{ ... }` macro collapsing inside indented contexts (#39)

# v0.2.6

* When running verusfmt on multiple files, continue attempting files even if one in the middle fails (#37)
* Fix collection of idempotency issues caused by rustfmt (#38)
  - rustfmt would modify code inside of `verus! { ... }` after verusfmt has already formatted it in certain cases
  - Verusfmt now prevents rustfmt from modifying code inside the Verus macro, through a collapse/expand operation  

# v0.2.5

* Fix `FnSpec` parsing
  - Despite Verus having deprecated `FnSpec` with the introduction of `spec_fn`, verusfmt still supports it for projects on older Verus
* Fix idempotency issue of macro-items inside `verus!` inside in-file `mod`ules
* Fix multi-line inline comment treatment
  - Only treat multi-line comments as inline if the entire comment is on a single line

# v0.2.4

* Move verusfmt to the verus-lang organization: https://github.com/verus-lang/verusfmt

# v0.2.3

* Don't drop "?" or "~" from type bounds

# v0.2.2

* Allow (bare) trigger attributes to be inline, rather than always on their own line

# v0.2.1

* Add support for new `spec_fn`
* Update handling for `fn_trait_types`
* Add support for `const` params
* Add support for `opens_invariants`
* Improve handling of complex self-params (e.g., `tracked '&a self`)
* Introduce `#[verusfmt::skip]` (#31)
* Add support for new `->` and `matches` expressions (#32)

# v0.2.0

* Reduce collapsing of various multiple single-line comments
* Fixed extra spaces in if-expressions with negation (#24)
* Fixed precedence for quantifiers and `&&&` and `|||` (#26)
* Handle macro call statements (#27)
* Improved handling of non-inline single-line comments (#28)

# v0.1.6

* Treat comments inside function signatures as inline by default

# v0.1.5

* Improved output for `--check`

# v0.1.4

Initial public release!
