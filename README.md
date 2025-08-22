This repository contains two projects.
# Project 1: Formal-Equivalence-of-two-RISCV-processor
This project proves the **architectural equivalence** between two open-source RV32I RISC‑V processors:

-  A **five-stage in-order pipelined** core with operand forwarding  
  ➤ https://github.com/AngeloJacobo/RISC-V  
-  A **minimal sequential** processor  
  ➤ https://github.com/BrunoLevy/learn-fpga/blob/master/FemtoRV/README.md  

The proof is conducted using **Cadence JasperGold**, where inductive properties are written to show that both cores produce **identical register states** across all RV32I instructions.

---

##  Project Goal

The goal is to write **inductive properties** that assert the following:

> If both processors begin executing the **same instruction** with the **same architectural register state**, and both reach the **next instruction boundary** after the instruction is committed, then the **register state must match again**.

If this holds for **each instruction type**, we conclude the cores are **functionally equivalent** at the architectural level.

---

##  Defining Equivalent Points

To write inductive properties, we define instruction **boundary points** (or checkpoints) in each processor:

-  **Sequential processor**:
  - Each instruction completes before the next begins.
  - A boundary is detected after **instruction fetch**, when the previous instruction's effects are complete.
  - A pulse (`seq_inst_start`) is generated to indicate a new instruction has started.

-  **Pipelined processor**:
  - Multiple instructions execute concurrently.
  - Architectural state updates happen at the **write-back (WB)** stage.
  - A pulse (`pipe_inst_start`) is generated when an instruction enters WB.
  - To track instruction flow, auxiliary **shift registers** monitor instructions across pipeline stages.

These equivalent points let us compare state across time and between architectures.

![Architecture Equivalence Diagram](https://raw.githubusercontent.com/mohammadmonjil/Formal-Equivalence-of-two-RISCV-processor/main/images/diagram.png)

---

## Operand Consistency in Pipelines

Due to **operand forwarding**, the pipelined ALU may use values updated by the prior instruction **before** they are committed to the register file.

To ensure the correct data path behavior, we assert:

```systemverilog
(pipe_rs1_alu == pipe_reg[pipe_rs1_addr_alu]) &&
(pipe_rs2_alu == pipe_reg[pipe_rs2_addr_alu])
```
**Where:**

- `pipe_rs*_alu`: ALU operand values  
- `pipe_rs*_addr_alu`: Source register addresses  
- `pipe_reg`: Register state after WB  

These constraints guarantee that forwarded values are logically correct.

---

## Sample Property (R‑Type Instruction)

```systemverilog
property eqv_on_R_type;
  @(posedge clk) disable iff (rst)
    pipe_inst_start && seq_inst_start &&
    (seq_instr == pipe_instr) &&
    (pipe_reg == seq_reg) &&
    valid_R_type &&

    (pipe_rs1_alu == pipe_reg[pipe_rs1_addr_alu]) &&
    (pipe_rs2_alu == pipe_reg[pipe_rs2_addr_alu])
  |-> ##4 (seq_reg == $past(pipe_reg, 3));
endproperty
```
- `valid_R_type`: Signal indicating a valid R-type instruction  
- `##4`: Delay accounts for sequential processor latency (4 cycles)  
- `$past(..., 3)`: Captures register state at the pipelined WB stage  

Similar properties are written for **I, S, B, U, and J** instruction types.

---

## Project Structure

- `formal_tb.sv`: Instantiates both cores and connects the monitor  
- `monitor`: Contains all formal properties and auxiliary tracking logic  
- `test.tcl`: TCL script to run JasperGold

## Result

✅ Proven architectural equivalence for all **RV32I** instruction types  
✅ Operand consistency verified through **forwarding checks**  
✅ Validated using **shift-register based tracking logic**

---

## Planned Extension

Expand this project to prove equivalence between an **out-of-order core** and the **sequential baseline**. 

# Project 2: Formal Verification of MUL/DIV/REM in Sequential RV32IM Processor

This project focuses on the **formal verification of MUL, DIV, and REM instructions** in a **sequential RV32IM RISC-V processor**, based on the [`core_uriscv`](https://github.com/ultraembedded/core_uriscv) design from UltraEmbedded.

---

## Overview

The multiplier/divisor unit in the original processor design was too complex to verify monolithically within the full processor core. To address this, the verification process was divided into two stages:

1. **Standalone Verification**:  
   The multiplier/divisor block was verified in isolation using expected inputs from the processor.
   
2. **Blackboxing & Assumptions**:  
   Once verified, the block was blackboxed, and **assumptions** were written on its output signals based on valid input-output relations. This abstraction enabled verification of the full processor’s control logic for the `MUL`, `DIV`, and `REM` instructions.

---


---

## Verification Strategy

### Stage 1: Verifying the Multiplier/Divisor Unit
- File: `mul_div_test.sv`
- Verified all corner cases and state transitions for:
  - `MUL`, `MULH`, `MULHU`, `MULHSU`
  - `DIV`, `DIVU`, `REM`, `REMU`
- Focused on checking correctness of results based on standard RISC-V behavior.

### Stage 2: Blackboxing with Assumptions
- File: `multiplier_assumptions.sv`
- Used `assume` properties on the outputs of the multiplier/divisor block
- This enabled faster convergence of formal proofs for the processor

### Stage 3: Processor-Level Instruction Verification
- File: `formal_tb.sv`
- Validated that the processor issues correct requests to the multiplier/divisor
- Checked the control path, state transitions, and correct retirement of results

---

## How to Run

1. Compile and run `mul_div_test.sv` to verify the standalone multiplier/divisor logic.
2. For full processor verification:
   - Replace the multiplier/divisor module with a blackbox.
   - Apply `multiplier_assumptions.sv`.
   - Run `formal_tb.sv` with appropriate top module.

---

## 📊 Results

- ✅ Correctness of all RISC-V M-extension instructions formally proven.
- ✅ Proper separation of datapath and control logic verification enabled tractable proof generation.
- ✅ Reused verified module assumptions to simplify processor-level verification.

---
