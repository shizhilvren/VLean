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

### Recursive statement generation

`statementTerm stmt target previous` recursively compiles a `VL.statement`
for one output into `StatementCode` (data signal, write-enable signal, and
optional event). Assignments replace the pending value; sequential blocks
thread this state through their statements in source order. Conditional
statements combine recursively generated branches using `Signals`' `if`
function. A missing branch preserves the incoming state rather than writing
zero. Timing-control statements attach an event and recursively compile
their body.

`code_gen_statement stmt target` starts with an empty pending write and returns
a Lean term for a `Reg`. Statements guaranteed to write the target use the
runtime `always` function with only the event signal as its condition.
Statements that may omit a write use a local structurally recursive register
expression: the event controls execution, and the data-path `if` selects the
pending value or the previous register value. No enabled-always runtime helper
is introduced. This entry point
requires an event; use `statementTerm` for a plain assignment or conditional
without an event. Both functions run in `Lean.Elab.Command.CommandElabM`.
The module generator uses these recursive functions for output generation;
the assignment list is retained only for dependency and driver validation.
Module port validation is not performed by the standalone statement API.
The previous-step sampling convention is unchanged.

Each statement result is bound once to a fresh local `let` variable containing
its data and write-enable signals. Subsequent statements refer to the pair's
projections instead of duplicating the earlier expressions. Conditions and
event signals also receive local bindings. Sequential overwrite is represented
by a new result variable; existing variables remain immutable. The final
register term shares all bindings in a single enclosing `let` chain.
The standalone `statementTerm` API returns closed expressions for each field,
so those fields can still be elaborated independently.

```console
lake build tests.statement_codegen tests.codegen_ascii
```

Run the ASCII code generation behavior and diagnostic checks with:

```console
lake build tests.codegen_ascii
```

### Asynchronous reset example

`tests/dff_async_reset.lean` contains an active-low asynchronous-reset Verilog
D flip-flop. All proofs concern the generated `AsyncReset.sampledDff` directly;
there is no separate reference implementation.
The proofs cover its recurrence, initialization, previous-step reset priority,
rising-edge capture, holding without an event, reset release, and constant
reset levels. The generator samples both reset conditions and data from the
previous step. Consequently, a falling reset edge loads previous-step data
instead of immediately clearing the output. `generated_reset_sampling_gap`
proves this limitation with a concrete counterexample.

```console
lake build tests.dff_async_reset
```

### Waveform visualization

Import `vc.tool.Waveform` to sample and display named `Wire` or `Reg` signals:

```lean
import vc.tool.Waveform

def showSignals (clock dataSignal result : Wire) : IO Unit := do
	let traces : List Waveform.Trace :=
		[("clk", clock), ("data", dataSignal), ("result", result)]
	IO.println (Waveform.renderText traces 16)
	Waveform.writeHtml "waveform.html" traces 16 0 "D flip-flop"
```

The arguments after the trace list are sample count and optional start time
(default `0`). `renderHtml` returns a self-contained HTML string with digital
waveforms and a sample table; `writeHtml` writes it to an existing directory.
`samples signal count start` returns the sampled Boolean values.

Run the tested asynchronous-reset example and open its generated HTML directly:

```console
lake build vc.tool.Waveform tests.dff_async_reset
lake env lean --run tests/waveform.lean
```

The output is `tests/async_reset_waveform.html`; it displays the generated
signal's actual behavior without changing the simulation semantics.

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