module multiplier_assumptions (
  input logic clk_i, rst_i, valid_i, inst_mul_i, inst_mulh_i, inst_mulhsu_i, inst_mulhu_i, inst_div_i, inst_divu_i, inst_rem_i, inst_remu_i, ready_o, stall_o,
  input logic [31:0] operand_ra_i, operand_rb_i, result_o
);


  localparam logic [31:0] INT_MIN = 32'h8000_0000;
  localparam logic [31:0] ALL1    = 32'hFFFF_FFFF;
  // localparam int mul_delay = 2;
  // localparam

  function automatic [32:0] mul_uu(input logic [31:0] a, b);
      return (a+b);
  endfunction

  function automatic [63:0] mul_ss(input logic [31:0] a, b);
      return $signed({{32{a[31]}}, a}) * $signed({{32{1'b0}}, b});
  endfunction

  function automatic [63:0] mul_su(input logic [31:0] a, b);
  // signed a, unsigned b
      return $signed({{32{a[31]}}, a}) * $unsigned({{32{1'b0}}, b});
  endfunction

  // RISC-V DIV/REM semantics (RV32M), including corner cases
  function automatic [31:0] rv32_div_q(input logic [31:0] a, b, input bit signed_op);
    if (b == 32'd0)                      rv32_div_q = signed_op ? ALL1 : ALL1; // -1 == 0xFFFF_FFFF
    else if (signed_op && (a==INT_MIN) && (b==32'hFFFF_FFFF)) rv32_div_q = INT_MIN; // overflow
    else if (signed_op)                  rv32_div_q = $signed(a) / $signed(b);
    else                                 rv32_div_q = $unsigned(a) / $unsigned(b);
  endfunction

  function automatic [31:0] rv32_div_r(input logic [31:0] a, b, input bit signed_op);
    if (b == 32'd0)                      rv32_div_r = a;         // remainder = dividend
    else if (signed_op && (a==INT_MIN) && (b==32'hFFFF_FFFF)) rv32_div_r = 32'd0; // overflow
    else if (signed_op)                  rv32_div_r = $signed(a) % $signed(b);
    else                                 rv32_div_r = $unsigned(a) % $unsigned(b);
  endfunction

  wire mul_dec = inst_mul_i | inst_mulh_i | inst_mulhsu_i | inst_mulhu_i;
  wire div_dec = inst_div_i | inst_divu_i | inst_rem_i | inst_remu_i;
  wire any_dec = mul_dec | div_dec;

  // A "start" is when the DUT is being presented an op the block may accept.
  // Note: the DUT latches MUL even if stall_o=1, but protocol-wise, producers should obey stall.
  wire start   = valid_i & any_dec & ~stall_o;
  wire start_mul = start & mul_dec;
  wire start_div = start & div_dec;


  // General multiplication assumption
  property a_mul_lo;
    logic [31:0] expected;
    @(posedge clk_i) disable iff (rst_i)
    ( (start && inst_mul_i, expected = mul_uu(operand_ra_i, operand_rb_i)[31:0]) 
    |-> ##2 ready_o && (result_o == expected)   );

  endproperty

  assume property (a_mul_lo);

property a_mul_lo_1;
  @(posedge clk_i) disable iff (rst_i)
  ( (start && inst_mul_i ) |-> 
  !ready_o); 

endproperty

assume property (a_mul_lo_1);

property a_mul_lo_2;
  @(posedge clk_i) disable iff (rst_i)
  ( (start && inst_mul_i ) |=> 
  !ready_o); 
endproperty

assume property (a_mul_lo_2);


endmodule

// Bind to multi_div
// bind formal_tb.pc_CPU.u_muldiv multiplier_assumptions multi_assume_inst (.*);

bind formal_tb.pc_CPU multiplier_assumptions mul_assump_inst (
  .clk_i         (clk_i),
  .rst_i         (rst_i),
  .valid_i       (u_muldiv.valid_i),    // connect these using full hierarchy path
  .inst_mul_i    (u_muldiv.inst_mul_i),
  .inst_mulh_i   (u_muldiv.inst_mulh_i),
  .inst_mulhsu_i (u_muldiv.inst_mulhsu_i), 
  .inst_mulhu_i  (u_muldiv.inst_mulhu_i), 
  .inst_div_i    (u_muldiv.inst_div_i), 
  .inst_divu_i   (u_muldiv.inst_divu_i), 
  .inst_rem_i    (u_muldiv.inst_rem_i), 
  .inst_remu_i   (u_muldiv.inst_remu_i), 
  .ready_o       (u_muldiv.ready_o), 
  .stall_o       (u_muldiv.stall_o),
  .operand_ra_i  (u_muldiv.operand_ra_i), 
  .operand_rb_i  (u_muldiv.operand_rb_i), 
  .result_o      (u_muldiv.result_o)
);
