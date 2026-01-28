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

`always_ff` blocks must contain ONLY simple non-blocking assignments. No logic, no expressions - this ensures Verilator simulation matches synthesized behavior. (Exception: memory inference patterns require conditional writes - see Memory Inference section.)

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
- Always use `begin`/`end` blocks for `if`, `else`, `case` items (prevents bugs when adding code later)

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

    always begin
        #5 clk = ~clk;
    end

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

## Module Instantiation

- One module per file, filename matches module name
- Always use named port connections (never positional)

```systemverilog
// CORRECT - named connections
counter #(
    .WIDTH(16)
) u_counter (
    .clk    (clk),
    .rst_n  (rst_n),
    .count  (count_value)
);

// WRONG - positional connections
counter u_counter (clk, rst_n, count_value);
```

## Avoiding Latches

Latches are inferred when signals aren't assigned in all paths. Prevent with:

- Default assignments at start of `always_comb`
- Use `unique case` or `priority case`
- Cover all cases including `default`

```systemverilog
always_comb begin
    // Default assignments first
    data_next = data_reg;
    valid_next = 1'b0;

    unique case (state)
        IDLE: begin
            data_next = 8'd0;
        end
        LOAD: begin
            data_next = data_in;
        end
        default: begin
            data_next = data_reg;
        end
    endcase
end
```

## Reset Handling

Use synchronous resets when possible. For external async resets, synchronize first.

```systemverilog
// Synchronous reset (preferred)
always_comb begin
    count_next = rst_n ? count + 1 : '0;
end

always_ff @(posedge clk) begin
    count <= count_next;
end

// Reset synchronizer for external async reset
logic [1:0] rst_sync;
always_ff @(posedge clk or negedge rst_async_n) begin
    if (!rst_async_n) begin
        rst_sync <= 2'b00;
    end else begin
        rst_sync <= {rst_sync[0], 1'b1};
    end
end
assign rst_n = rst_sync[1];
```

## FSM Patterns

Separate state register from next-state logic. Use enums for state encoding.

```systemverilog
typedef enum logic [1:0] {
    IDLE,
    RUN,
    DONE
} state_t;

state_t state;
state_t state_next;

// Next-state logic (combinational)
always_comb begin
    state_next = state;
    unique case (state)
        IDLE: begin
            if (start) begin
                state_next = RUN;
            end
        end
        RUN: begin
            if (finish) begin
                state_next = DONE;
            end
        end
        DONE: begin
            state_next = IDLE;
        end
        default: begin
            state_next = IDLE;
        end
    endcase
end

// State register (sequential)
always_ff @(posedge clk) begin
    state <= state_next;
end
```

## Clock Domain Crossing (CDC)

Single-bit signals: use 2-FF synchronizer. Multi-bit: use gray coding or handshake.

```systemverilog
// 2-FF synchronizer for single-bit CDC
logic [1:0] sync_reg;
logic       signal_sync;

always_ff @(posedge clk_dst) begin
    sync_reg <= {sync_reg[0], signal_src};
end
assign signal_sync = sync_reg[1];

// Gray code for multi-bit counters crossing domains
function automatic logic [WIDTH-1:0] bin2gray(input logic [WIDTH-1:0] bin);
    return bin ^ (bin >> 1);
endfunction
```

## Memory Inference

Use standard patterns for RAM/ROM inference by synthesis tools.

**Note:** Memory patterns are an exception to the "simple assignments only" rule for `always_ff`. Synthesis tools require these specific patterns to correctly infer RAM/ROM primitives.

```systemverilog
// Single-port RAM
logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

always_ff @(posedge clk) begin
    if (we) begin
        mem[addr] <= wdata;
    end
    rdata <= mem[addr];
end

// ROM (initialized memory)
logic [7:0] rom [0:255];
initial $readmemh("rom_data.hex", rom);

always_ff @(posedge clk) begin
    rdata <= rom[addr];
end
```

## Assertions (SVA)

Use assertions for verification. They're enabled with `--assert` in Verilator.

```systemverilog
// Immediate assertion
always_comb begin
    assert (count < MAX_COUNT) else $error("Count overflow");
end

// Concurrent assertions
property p_valid_handshake;
    @(posedge clk) disable iff (!rst_n)
    valid |-> ##[1:3] ready;
endproperty

assert property (p_valid_handshake)
    else $error("Handshake timeout");

// Cover property (for functional coverage)
cover property (@(posedge clk) state == DONE);
```
