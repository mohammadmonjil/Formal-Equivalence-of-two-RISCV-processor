This repository contains two projects.
# Project 1: Formal-Equivalence-of-two-RISCV-processor
This project proves the **architectural equivalence** between two open-source RV32I RISC‑V processors:

-  A **five-stage in-order pipelined** core  
   https://github.com/AngeloJacobo/RISC-V  
-  A **minimal sequential** processor  
   https://github.com/BrunoLevy/learn-fpga/blob/master/FemtoRV/README.md  

The proof is conducted using **Cadence JasperGold**, where inductive properties are written to show that both cores produce **identical register states** across all RV32I instructions.

---

##  Project Goal

The goal is to write **inductive properties** that assert the following:

> If both processors begin executing the **same instruction** with the **same architectural register state**, and both reach the **next instruction boundary** after the instruction is committed, then the **register state must match again**.

If this holds for all instructions we can conclude the cores are **functionally equivalent** at the architectural level.

---

##  Defining Equivalent Points

To write inductive properties, we define instruction **boundary points** (or checkpoints) in each processor:

**Sequential processor**:
  - Each instruction completes before the next begins.
  - A boundary is detected after **instruction fetch**, when the previous instruction's effects are complete.
  - A pulse (`seq_instr_start`) is generated to indicate a new instruction has started.

**Pipelined processor**:
  - Multiple instructions execute concurrently.
  - Architectural state updates happen at the **write-back (WB)** stage.
  - A pulse (`pipe_instr_start`) is generated when an instruction enters WB.
  - To track instruction flow, auxiliary **shift registers** monitor instructions across pipeline stages.

These equivalent points let us compare state across time and between architectures. The next comparison point where we can check if the registers remain identical would be the next pulse of `seq_inst_start` and `pipe_inst_start`.

![Equivalence Diagram](https://github.com/mohammadmonjil/Formal-Equivalence-of-two-RISCV-processor/blob/main/images/Screenshot%20from%202025-08-24%2017-16-09.png?raw=true)

---
## Inductive Property
Let's assume `seq_reg[seq_instr_start]`, `seq_instr[seq_instr_start]` denotes values of registers and current instruction at time `seq_instr_start` and `pipe_reg[pipe_instr_start]` & `pipe_instr[pipe_instr_start]` denotes values of registers and current instruction at time pipe_instr_start. Similarly, we can define values for `next_seq_instr_start` and `next_pipe_instr_start`. Then the inductive property for equivalence for the processors can be stated as following:

```
    (seq_reg[seq_instr_start] == pipe_reg[pipe_instr_start]
                              &&
     seq_instr[seq_instr_start] == pipe_instr[pipe_instr_start])
                              implies
     seq_reg[next_seq_instr_start] == pipe_reg[next_pipe_instr_start]  

```
However, there is a subtle issue here due to pipelining. In sequential machine there is clear boundery between consequent instructions, an instruction starts after the previous one has completed. In pipelined machine, an instruction starts executing before the previous one has retired and updated registers. If there is data dependency between the current and previous instruction, the execution stage has must use updated register values which the previous instruction has not completed. This issue is resolved by pipeline stalling or operand forwarding. 

To account this issue, we must include one more condition in the consequent of our inductive property in order to make it equivalent with the sequential machine. We must make sure that the operands used in the ALU of the pipeline must match the updated registers due to previous instruction. To do this, we extract the operand values in EXECUTION stage and shift it along the pipeline stages using auxiliary shift registers. 

![Pipeline Equivalence](https://github.com/mohammadmonjil/Formal-Equivalence-of-two-RISCV-processor/blob/main/images/Screenshot%20from%202025-08-24%2023-50-13.png?raw=true)

Let's denote the source register rs_1 address of the current instruction as `rs1_addr` and the operand value extracted at the EXECUTION stage as `pipe_rs1_alu`. We can define similarly for the second source register rs2. Then we our inductive property becomes: 

```
    (seq_reg[seq_instr_start] == pipe_reg[pipe_instr_start]
                              &&
     seq_instr[seq_instr_start] == pipe_instr[pipe_instr_start]  
                              &&
     pipe_rs1_alu == pipe_reg[pipe_instr_start][rs1_addr]
                              &&
     pipe_rs2_alu == pipe_reg[pipe_instr_start][rs2_addr]))
                           implies
     seq_reg[next_seq_instr_start] == pipe_reg[next_pipe_instr_start]  

```

We can do case splitting based on instruction type and depending on the instruction type, the formulation might vary slightly.

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
- `valid_R_type`: A signal that continously tracks whether the current instruction (which is same for both machines) is a valid R-type instruction or not  
- `##4`: Accounts for the sequential processor taking 4 cycles to reach the next instruction start pulse for R type instruction. We can also do non-deterministic delay and wait for the instruction start pulse. However, putting fixed value makes the proof faster.   
- `$past(..., 3)`: Captures register state at the pipelined WB stage as in pipeline stage it takes 1 cycle to complete WB stage so we must register values 3 cycles back as we waited 4 cycles for the sequential machine to finish.

```systemverilog
      property eqv_on_load;
        @(posedge clk) disable iff (rst)
            pipe_inst_start && seq_inst_start &&
            (seq_instr == pipe_instr) &&
            (pipe_reg == seq_reg) &&
            (pipe_rs1_alu == pipe_reg[pipe_rs1_addr_alu]) &&
            is_valid_load_and_equal_mem
            |-> ##6 (ft_reg == $past(pc_reg, 5));
    endproperty
```
-`is_valid_load_and_equal_mem`: A signal that tracks if the current instruction is a valid load instruction and the memory contents in memories of both the processors pointed by address of the current instruction are same.
- `##6`: The sequential machine takes 6 cycles to complete the load instruction.
  
Load instruction get address by computing (rs1+imm) by the ALU in the EXECUTION stage. So we use only rs1 is the consequent.

Similar properties can be written for other instruction types.

---

## Project Structure

- `formal_tb.sv`: Instantiates both cores and connects the monitor  
- `monitor`: Contains all formal properties and auxiliary tracking logic  
- `test.tcl`: TCL script to run JasperGold

## Result

- Proven architectural equivalence for all **RV32I** instruction types  

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

1. Run `mul_div_test.sv` to verify the standalone multiplier/divisor logic.
2. For full processor verification:
   - Replace the multiplier/divisor module with a blackbox.
   - Apply `multiplier_assumptions.sv`.
   - Run `formal_tb.sv` with appropriate top module.

---

## Results

-  Correctness of all RISC-V M-extension instructions formally proven.
---
