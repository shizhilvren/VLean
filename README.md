# vc

## Module code generation

- `vc/paser/`: Verilog syntax tree, tokens, and parsing rules.
- `vc/runtime/Signals.lean`: `Wire`, `Reg`, and `always` / `postedge` used by generated
	definitions. This module has no parser or metaprogramming dependencies.
- `vc/codegen/Verilog.lean`: port and assignment extraction, Lean definition
	generation, and the `verilog[...]` command elaborator. Imports the runtime.
- `vc/verilog.lean`: compatibility entry point importing the generator, without tests.
- `tests/verilog_runtime.lean`: standalone signal semantics checks importing only
	the runtime module.
- `tests/verilog_codegen.lean`: port checks, generated module examples, and
	`Dff_hold` / `Dff_posedge` proofs.
- `tests/verilog_parser.lean`: parser reduction examples.
- `tests/dff_waveform.lean`: stimuli for the generated D flip-flop and HTML waveforms.

Existing clients can continue to use `import vc.verilog`. Generator tests are
separate from the default `vc` library target. Run these commands from the
project root:

```console
lake build
lake build tests
lake env lean --run tests/dff_waveform.lean
```

For just the generator tests and waveform dependencies:

```console
lake build +tests.verilog_codegen
lake env lean --run tests/dff_waveform.lean
```

The waveform runner writes `tests/dff_waveform.html`.

Generate module definitions from ASCII Verilog using matching delimiters:

```lean
import vc.verilog

verilog "EOF" [
	module enabled_ff(input wire clk, en, data, output reg result);
		always @(posedge clk) begin
			if (en) result <= data;
		end
	endmodule
]"EOF"
```

The opening and closing strings must match. Whitespace, punctuation, and
parentheses inside the source are handled by the ASCII parser.
The command `verilog[ast]` accepts any expression of type `VL.source_text`,
including `verilog[ascii_apply "source_text" "EOF" [...]"EOF"]`.
Replace the old raw-source command `verilog[module ... endmodule]` with the
delimited form above.

The module generator supports single-bit identifiers, hierarchical-identifier
AST nodes containing a simple identifier, binary `0`/`1` constants, logical
negation, sequential blocks, nested `if`/`else`, and `posedge`/`negedge` events
combined with `or`. Missing branches hold the previous register value. Within
one block, the last executed assignment to a register wins; separate blocks
driving the same register are rejected.

Generated definitions use the discrete `Bool` runtime: registers start at
`false`, events are detected at step `n + 1`, and both conditions and right-hand
sides are sampled at step `n`. This also applies to reset conditions, and is
not Verilog delta-cycle or continuous-time asynchronous-reset simulation.
Dependencies must be input signals and assignment targets must be output regs.
Vectors, `x`/`z` constants, feedback, and nested event controls are rejected.
Undriven outputs retain the existing constant-`false` behavior.

Run the ASCII code generation behavior and diagnostic checks with:

```console
lake build tests.codegen_ascii
```

Code that only needs the signal types and sampling function can use
`import vc.runtime.Signals` without loading the Verilog parser or generator.
The dependency direction is `vc.verilog -> vc.codegen.Verilog -> vc.runtime.Signals`;
the generator also imports `vc.paser.*`.

## Embedded Verilog subset

`Vc.Basic` uses Lean `syntax` and `macro_rules` to translate single-bit
combinational Verilog expressions into `Wire := Nat -> Bool` values.

```lean
import Vc.Basic

def inputA : Wire := fun time => time % 2 == 1
def inputB : Wire := fun time => time % 4 >= 2

verilog assign sum = inputA ^ inputB;
verilog assign carry = inputA & inputB;

#eval visualize sum 0 3
#eval visualize (verilog[ ~inputA | inputB ]) 0 3
```

Supported expressions: Lean identifiers bound to wires, constants `0` and `1`,
parentheses, unary `!` and `~`, and binary `&`, `^`, and `|` (in descending
precedence). Binary operators associate to the left. Both unary operators
negate a single bit. A prefixed `verilog assign name = expression;` command
defines a Lean wire; `verilog[ expression ]` can be used directly as a term.

This is an embedded DSL, not a parser for external `.v` files. It does not yet
support modules, port declarations, vectors, four-state logic, arithmetic,
feedback, or `always` blocks. Wire references must already exist in Lean scope.

Run the waveform, precedence, diagnostic, and proof checks from this directory:

```console
lake env lean Vc/Basic.lean
lake env lean tests/file_verilog.lean
lake build
```