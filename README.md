# Build
```bash
cmake . -B build
cmake --build build
```
- This will generate `taint-analysis` binary in `./build/bin` directory.

# Execute
- For help, run `./build/bin/taint-analysis --help`
- Sample analysis
```bash
./build/bin/taint-analysis tee.elf.bc -f test/optee/syscalls.txt
```
  - This generates results in `/tmp/taint-logs/` directory

