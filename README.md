# Verusfmt

> "Where there's code, there's a way. And Verusfmt knows the best way."  
>   -- A satisfied Verusfmt user who wished to remain anonymous

An opinionated formatter for Verus code.

## WARNING

Verusfmt is highly experimental code. It can and _will_ eat your homework. Make
backups of your files before trying Verusfmt on them. Actually, it's a good idea
to make backups in general, and check those backups from time to time. Go do
that first.

## TESTING

The [Insta testing framework](https://insta.rs) recommends installing the `cargo-insta` tool for 
an improved review experience:
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

## FAQ

1. **What are the frequently asked questions about Verusfmt?**  
These are the frequently asked questions about Verusfmt.

1. **That doesn't seem like a useful question.**  
That doesn't seem like a question either.
