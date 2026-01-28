# Verilog/SystemVerilog Guidance

Apply when working with `.v`, `.sv`, `.vh`, `.svh` files or running Verilator.

## Documentation

All modules, wires, and registers require comments:

```systemverilog
// Module: counter
// Purpose: Simple up-counter with synchronous reset
module counter #(
    parameter WIDTH = 8  // Counter bit width
) (
    input  logic             clk,      // System clock
    input  logic             rst_n,    // Active-low reset
    output logic [WIDTH-1:0] count     // Current count value
);
```

## Naming Conventions

- Active-low signals: use `_n` suffix (e.g., `rst_n`, `chip_select_n`)
- Clocks: `clk` or `clk_<domain>`
- Use descriptive names over abbreviations

## always_ff: Simple Assignments Only

`always_ff` blocks must contain ONLY simple non-blocking assignments. No logic, no expressions - this ensures Verilator simulation matches synthesized behavior.

```systemverilog
// CORRECT - simple assignment
always_ff @(posedge clk) begin
    count <= count_next;
    state <= state_next;
end

// WRONG - logic in always_ff
always_ff @(posedge clk) begin
    count <= count + 1;           // Move to always_comb
    state <= enable ? RUNNING : IDLE;  // Move to always_comb
end
```

## always_comb: All Logic Here

All combinational logic belongs in `always_comb` blocks:

```systemverilog
always_comb begin
    count_next = count + 1;
    state_next = enable ? RUNNING : IDLE;
end
```

## Declarations

- One declaration per line
- Explicit bit widths on all literals
- Start files with `` `default_nettype none ``

```systemverilog
`default_nettype none

module example (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);

    logic [7:0] data_reg;    // Registered data
    logic [7:0] data_next;   // Next state value
    logic       valid;       // Data valid flag

    localparam logic [7:0] INIT_VAL = 8'd0;

endmodule

`default_nettype wire
```

## Testing with Verilator

Every module requires a testbench. Build and run with Verilator:

```bash
# Build testbench
verilator --binary -Wall module_tb.sv module.sv

# Run simulation
./obj_dir/Vmodule_tb
```

Testbench structure:

```systemverilog
module counter_tb;
    logic clk = 0;
    logic rst_n;
    logic [7:0] count;

    counter dut (
        .clk(clk),
        .rst_n(rst_n),
        .count(count)
    );

    always #5 clk = ~clk;

    initial begin
        rst_n = 0;
        #20 rst_n = 1;
        #100;
        $display("Test complete, count=%d", count);
        $finish;
    end
endmodule
```

## Verilator Linting

Run linting on all files and fix all warnings:

```bash
verilator --lint-only -Wall module.sv
```

- Fix all warnings - do not suppress with pragmas
- Key warnings: WIDTH (bit-width mismatch), UNUSED, UNDRIVEN

## Verilator Simulation Flags

Recommended flags for simulation builds:

```bash
verilator --binary \
    -Wall \
    -Wno-fatal \
    -j 0 \
    --assert \
    --timing \
    --trace-fst \
    --trace-structs \
    --main-top-name "-" \
    --x-assign unique \
    --x-initial unique \
    module_tb.sv module.sv
```

| Flag | Purpose |
| ---- | ------- |
| `-Wall` | Enable all warnings |
| `-Wno-fatal` | Don't exit on warnings (allows full report) |
| `-j 0` | Fully parallelized compilation |
| `--assert` | Enable SystemVerilog assertions |
| `--timing` | Enable timing constructs |
| `--trace-fst` | Dump waveforms as FST (compressed) |
| `--trace-structs` | Human-readable struct dumps |
| `--main-top-name "-"` | Remove extra TOP module wrapper |
| `--x-assign unique` | Replace X with random constant per-build |
| `--x-initial unique` | Randomly initialize uninitialized variables |
