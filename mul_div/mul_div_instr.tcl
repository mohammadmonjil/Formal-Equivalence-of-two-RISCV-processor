# clear -all

# # Analyze your RTL and testbench
# analyze -sv09 formal_tb.sv uriscv_csr.v   uriscv_muldiv.v tcm_mem_ram.v  uriscv_alu.v   uriscv_defs.v riscv_core.v  tcm_mem.v uriscv_branch.v uriscv_lsu.v multiplier_assumptions.sv divrem_always_constraints.sv
# analyze -sv09 -bbox_m  uriscv_muldiv

# elaborate -top formal_tb  
# #-bbox_mul 130 

# # Set clock and reset
# clock clk
# reset ~resetn

clear -all

# Analyze RTL + TB (no module-level blackboxing here)
analyze -sv09 \
  formal_tb.sv uriscv_csr.v  tcm_mem_ram.v \
  uriscv_alu.v uriscv_defs.v riscv_core.v tcm_mem.v \
  uriscv_branch.v uriscv_lsu.v \
  multiplier_assumptions.sv uriscv_muldiv.v\
   -bbox_m uriscv_muldiv

# Elaborate top and blackbox ONE instance by hierarchy
# (Use your exact path; example shown below)
elaborate -top formal_tb -bbox_mul 192 -bbox_div 133 -bbox_mod 133

# Clock / reset
clock clk
reset ~resetn

# Instruction memory setup for ft and pc memory
#assume {rst -> u_mem.u_ram.ram[0] == 32'h02800093}
#assume -reset {ft_mem_wmask == 4'h 0}
# assume -reset {ft_memory[0] == 32'h 02800093}
# assume -reset {ft_memory[1] == 32'h 0000a023}
# assume -reset {ft_memory[2] == 32'h 0000a103}
# assume -reset {ft_memory[3] == 32'h 00110113}
# assume -reset {ft_memory[4] == 32'h 0020a023}
# assume -reset {ft_memory[5] == 32'h ff5ff06f}

# assume -reset {u_mem.u_ram.ram[0] == 32'h02800093}
# assume -reset {u_mem.u_ram.ram[1] == 32'h0000a023}
# assume -reset {u_mem.u_ram.ram[2] == 32'h0000a103}
# assume -reset {u_mem.u_ram.ram[3] == 32'h00110113}
# assume -reset {u_mem.u_ram.ram[4] == 32'h0020a023}
# assume -reset {u_mem.u_ram.ram[5] == 32'hff5ff06f}

# set MEMSIZE 32
# # Zero out the rest
# for {set i 1} {$i < $MEMSIZE} {incr i} {
#     assume -reset [format {ft_memory[%d] == 32'h00000000} $i]
#     assume -reset [format {u_mem.u_ram.ram[%d] == 32'h00000000} $i]
# }

# set regfile_size 32
# for {set i 0} {$i < $regfile_size} {incr i} {
#     assume -reset [format {ft_CPU.RegisterBank[%d] == 32'h00000000} $i]
#     assume -reset [format {pc_CPU.reg_file[%d] == 32'h00000000} $i]
# }
# stopat pc_CPU.mem_i_inst_i


prove -all
