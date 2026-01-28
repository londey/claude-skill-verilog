# claude-skill-verilog

A Claude Code skill providing coding style guidance for Verilog/SystemVerilog development.

## Overview

This skill enforces consistent coding standards focused on:

- **Simulation/synthesis consistency** - Keeping logic in `always_comb` and only simple assignments in `always_ff` ensures Verilator simulation matches synthesized hardware behavior
- **Verilator-first workflow** - All modules have testbenches built and run with Verilator
- **Readable, maintainable code** - Documentation requirements, explicit declarations, consistent naming

## Installation

Add this skill to your Claude Code configuration:

```json
{
  "skills": [
    "path/to/claude-skill-verilog/SKILL.md"
  ]
}
```

## Key Rules

| Rule | Rationale |
| ---- | --------- |
| Simple assignments in `always_ff` | Prevents simulation/synthesis mismatches |
| All logic in `always_comb` | Clear separation of combinational and sequential |
| One declaration per line | Readability and version control diffs |
| `_n` suffix for active-low | Consistent naming convention |
| `begin`/`end` on all blocks | Prevents bugs when adding code |
| Verilator `-Wall` linting | Catch issues early |

## Topics Covered

- Documentation comments
- Naming conventions
- `always_ff` / `always_comb` separation
- Declaration style
- Testbench structure
- Verilator linting and simulation flags
- Module instantiation
- Avoiding latches
- Reset handling (sync and async)
- FSM patterns
- Clock domain crossing (CDC)
- Memory inference (RAM/ROM)
- SystemVerilog assertions (SVA)

## References

Style guidance derived from:

- [lowRISC Verilog Coding Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md)
- [FPGACPU Verilog Coding Standard](https://fpgacpu.ca/fpga/verilog.html)
- [Project F - Verilog Lint with Verilator](https://projectf.io/posts/verilog-lint-with-verilator/)
- [ZipCPU Tutorials](https://zipcpu.com/tutorial/)
