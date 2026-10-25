# C8080

A C compiler targeting the wide Intel 8080 from [intel8080](../intel8080). It parses C, folds constants and emits assembly.

Supported: structs, unions, arrays, pointers, `float`/`double` (soft), `intN`/`uintN` of 1-2048 bits, a preprocessor and a standard library from [vulcanos](../vulcanos/stdlib). Type sizes: `int` 4 bytes, `long` 8 bytes, pointers 8 bytes. See [c.md](../vulcanide/docs/c.md) and [c-runtime.md](../vulcanide/docs/c-runtime.md).

## Build and use

Needs Java 17+. From the `qa` repo (cloned next to this one):

```powershell
..\qa\build.ps1                                    # writes builds\c8080.jar
java -jar builds\c8080.jar programs\c\add_demo.c add_demo.asm   # emit assembly
```

The jar only emits assembly. To link and run, use the [Vulcan IDE](../vulcanide) terminal or the [MCP server](../vulcan-mcp):

```text
vcc add_demo.c add.c -o program.exe
vload program.exe
```

## Example

`programs/c/add_demo.c`:

```c
#include <stdio.h>
#include "add.h"
int main() {
    int a = 70000, b = 30000;
    printf("%d %d\n", add(a, b), a * b);
    return 0;
}
```

Output: `100000 2100000000`.

## Layout

- `src/C8080` - lexer, parser, code generator, optimizer, runtime helpers
- `programs/c` - sample programs
