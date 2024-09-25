# Glob Macro

A small and simple crate that lets one apply a [`glob`](https://docs.rs/glob/latest/glob/) in a macro position.

## Usage

The main intended use case for this is to write tests that run over all files in some directory. For example:

```rs
#[glob("./path/to/**/*.inp")]
#[test]
fn test(path: &Path) {
    assert!(path.exists());
}
```
