
# IronFleet

Format:
```
cargo run -- ~/git/verus-systems-code/ironfleet-comparison/ironsht/src/{*.rs,verus_extra/*.rs}
```
Verify:
```
scons --verus-path=/Users/parno/git/verus/

```


# NR

Format:
```
cargo run -- ~/git/verus-systems-code/nr/verus-nr/src/{*.rs,spec/*.rs,exec/*.rs}
```

Verify:
```
verus-systems-code/nr/verus-nr $ verus --crate-type lib  src/lib.rs 
```

# mimalloc

Format:
```
cargo run -- ~/git/verus-systems-code/memory-allocators/verus-mimalloc/*rs
```
or to identify errors, run:
```
for f in ~/git/verus-systems-code/memory-allocators/verus-mimalloc/*rs; do cargo run -- $f || break ; done
```

Verify. First run the setup:
```
verus-systems-code/memory-allocators $ ./setup-libc-dependency.sh 
```
Then run:
```
verus-systems-code/memory-allocators/verus-mimalloc $ VERUS_SINGULAR_PATH=/opt/homebrew/bin/singular verus --rlimit 50 --extern libc=../build/liblibc.rlib lib.rs "$@" --triggers-silent -- -Zproc-macro-backtrace
```

# page table

Acquire:
```
git clone https://github.com/utaal/verified-nrkernel.git 
```

Format
```
for f in `find ~/git/verus-systems-code/verified-nrkernel/page-table -name "*rs" `; do cargo run  -- $f || break ; done
```

Verify:
```
~/git/verus-systems-code/verified-nrkernel/page-table $ VERUS_SINGULAR_PATH=/opt/homebrew/bin/singular verus main.rs 
```

# Verified Storage

Acquire:
```
git clone https://github.com/microsoft/verified-storage.git
```

Format:
```
for f in `ls ~/git/verus-systems-code/verified-storage/pmemlog/src/*.rs `; do cargo run  -- $f || break ; done
```

Verify:
```
~/git/verus-systems-code/verified-storage/pmemlog/src $ verus main.rs
```
