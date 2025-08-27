clear -all

# Analyze your RTL and testbench
analyze -sv09 mul_div_test.sv uriscv_muldiv.v uriscv_defs.v

elaborate -top mul_div_test  -bbox_mul 192 -bbox_div 100 -bbox_mod 100

# Set clock and reset
clock clk_i
reset rst_i

prove -all
