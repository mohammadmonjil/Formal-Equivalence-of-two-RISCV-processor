module multiplier_assumptions (
  input logic clk_i, rst_i, valid_i, inst_mul_i, inst_mulh_i, inst_mulhsu_i, inst_mulhu_i, inst_div_i, inst_divu_i, inst_rem_i, inst_remu_i, ready_o, stall_o,
  input logic [31:0] operand_ra_i, operand_rb_i, result_o
);


  wire mul_dec = inst_mul_i | inst_mulh_i | inst_mulhsu_i | inst_mulhu_i;
  wire div_dec = inst_div_i | inst_divu_i | inst_rem_i | inst_remu_i;
  wire any_dec = mul_dec | div_dec;

  // A "start" is when the DUT is being presented an op the block may accept.
  // Note: the DUT latches MUL even if stall_o=1, but protocol-wise, producers should obey stall.
  wire start   = valid_i & any_dec ;
  wire start_mul = start & mul_dec;
  wire start_div = start & div_dec;


  property when_starting_mul_ready_o_must_be_low_for_2_cycles;
    @(posedge clk_i) disable iff (rst_i)
    ( (start_mul ) |-> 
    !ready_o ##1 !ready_o); 
  endproperty

  assume property (when_starting_mul_ready_o_must_be_low_for_2_cycles);


  property when_starting_div_ready_o_must_be_low_for_32_cycles;
    @(posedge clk_i) disable iff (rst_i)
    ( (start_div ) |-> 
    !ready_o[*32]); 
  endproperty
  assume property (when_starting_div_ready_o_must_be_low_for_32_cycles);

endmodule

// Bind to multi_div
// bind formal_tb.pc_CPU.u_muldiv multiplier_assumptions multi_assume_inst (.*);

bind formal_tb.pc_CPU multiplier_assumptions mul_assump_inst (
  .clk_i         (clk_i),
  .rst_i         (rst_i),
  .valid_i       (opcode_valid_w & ~exception_w),    // connect these using full hierarchy path
  .inst_mul_i    (inst_mul_w),
  .inst_mulh_i   (inst_mulh_w),
  .inst_mulhsu_i (inst_mulhsu_w), 
  .inst_mulhu_i  (inst_mulhu_w), 
  .inst_div_i    (inst_div_w), 
  .inst_divu_i   (inst_divu_w), 
  .inst_rem_i    (inst_rem_w), 
  .inst_remu_i   (inst_remu_w), 
  .ready_o       (muldiv_ready_w), 
  .stall_o       (),
  .operand_ra_i  (rs1_val_w), 
  .operand_rb_i  (rs2_val_w), 
  .result_o      (muldiv_result_w)
);