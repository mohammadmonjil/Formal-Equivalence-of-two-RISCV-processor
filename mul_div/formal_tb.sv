
`define FORMAL

module formal_tb(
    input clk,
    input resetn
    );
    
    localparam MEMSIZE = 32;
    
    //femto

	wire rst;	
	assign rst = !resetn;
	

	   

//-------------------------------------------------------------------------------------//
   wire          mem_i_rd_w;
   wire          mem_i_flush_w;
   wire          mem_i_invalidate_w;
   wire [ 31:0]  mem_i_pc_w;
   wire [ 31:0]  mem_d_addr_w;
   wire [ 31:0]  mem_d_data_wr_w;
   wire          mem_d_rd_w;
   wire [  3:0]  mem_d_wr_w;
   wire          mem_d_cacheable_w;
   wire [ 10:0]  mem_d_req_tag_w;
   wire          mem_d_invalidate_w;
   wire          mem_d_writeback_w;
   wire          mem_d_flush_w;
   wire          mem_i_accept_w;
   wire          mem_i_valid_w;
   wire          mem_i_error_w;
   wire [ 31:0]  mem_i_inst_w;
   wire [ 31:0]  mem_d_data_rd_w;
   wire          mem_d_accept_w;
   wire          mem_d_ack_w;
   wire          mem_d_error_w;
   wire [ 10:0]  mem_d_resp_tag_w;
   
   
   wire          pc_inst_done;
   wire          pc_inst_start;
   wire [ 31:0]  pc_pc;
   riscv_core
   pc_CPU
   //-----------------------------------------------------------------
   // Ports
   //-----------------------------------------------------------------
   (
       // Inputs
        .clk_i(clk)
       ,.rst_i(rst)
       ,.mem_d_data_rd_i(mem_d_data_rd_w)
       ,.mem_d_accept_i(mem_d_accept_w)
       ,.mem_d_ack_i(mem_d_ack_w)
       ,.mem_d_error_i(mem_d_error_w)
       ,.mem_d_resp_tag_i(mem_d_resp_tag_w)
       ,.mem_i_accept_i(mem_i_accept_w)
       ,.mem_i_valid_i(mem_i_valid_w)
       ,.mem_i_error_i(mem_i_error_w)
       ,.mem_i_inst_i(mem_i_inst_w)
    //    ,.mem_i_inst_i(32'h02c5d533)
       
       ,.intr_i(1'b0)
       ,.reset_vector_i(32'h00000000)
       ,.cpu_id_i('b0)
   
       // Outputs
       ,.mem_d_addr_o(mem_d_addr_w)
       ,.mem_d_data_wr_o(mem_d_data_wr_w)
       ,.mem_d_rd_o(mem_d_rd_w)
       ,.mem_d_wr_o(mem_d_wr_w)
       ,.mem_d_cacheable_o(mem_d_cacheable_w)
       ,.mem_d_req_tag_o(mem_d_req_tag_w)
       ,.mem_d_invalidate_o(mem_d_invalidate_w)
       ,.mem_d_writeback_o(mem_d_writeback_w)
       ,.mem_d_flush_o(mem_d_flush_w)
       ,.mem_i_rd_o(mem_i_rd_w)
       ,.mem_i_flush_o(mem_i_flush_w)
       ,.mem_i_invalidate_o(mem_i_invalidate_w)
       ,.mem_i_pc_o(mem_i_pc_w)
       `ifdef FORMAL

       ,.inst_start(pc_inst_start)
       `endif
   );
    
    tcm_mem
    u_mem
    (
        // Inputs
         .clk_i(clk)
        ,.rst_i(rst)
        ,.mem_i_rd_i(mem_i_rd_w)
        ,.mem_i_flush_i(mem_i_flush_w)
        ,.mem_i_invalidate_i(mem_i_invalidate_w)
        ,.mem_i_pc_i(mem_i_pc_w)
        ,.mem_d_addr_i(mem_d_addr_w)
        ,.mem_d_data_wr_i(mem_d_data_wr_w)
        ,.mem_d_rd_i(mem_d_rd_w)
        ,.mem_d_wr_i(mem_d_wr_w)
        ,.mem_d_cacheable_i(mem_d_cacheable_w)
        ,.mem_d_req_tag_i(mem_d_req_tag_w)
        ,.mem_d_invalidate_i(mem_d_invalidate_w)
        ,.mem_d_writeback_i(mem_d_writeback_w)
        ,.mem_d_flush_i(mem_d_flush_w)
    
        // Outputs
        ,.mem_i_accept_o(mem_i_accept_w)
        ,.mem_i_valid_o(mem_i_valid_w)
        ,.mem_i_error_o(mem_i_error_w)
        ,.mem_i_inst_o(mem_i_inst_w)
        ,.mem_d_data_rd_o(mem_d_data_rd_w)
        ,.mem_d_accept_o(mem_d_accept_w)
        ,.mem_d_ack_o(mem_d_ack_w)
        ,.mem_d_error_o(mem_d_error_w)
        ,.mem_d_resp_tag_o(mem_d_resp_tag_w)
    );
    
    
    reg [retire_width-1:0] pc_retired;
    
    always @(posedge clk or posedge rst)
    if (rst)
        pc_retired <= 0;
    else if (pc_inst_done)
        pc_retired <= pc_retired + 1;
    
    reg [31:0] pc_reg[32];

    genvar j;
    generate

        for (j = 0; j<32; j = j +1) begin
            
            if (j == 0) assign pc_reg[j] = 32'd0;
            else assign pc_reg[j] = pc_CPU.reg_file[j];
        end
    endgenerate
    
//aux code

    localparam int retire_width = 64;
    
    monitor #(.MEMSIZE(MEMSIZE)) u_monitor (
         .clk(clk)
        ,.rst(rst)
        ,.pc_reg(pc_reg)
        ,.pc_mem(u_mem.u_ram.ram)
        ,.pc_pc(pc_pc)
        ,.pc_inst_start(pc_inst_start)
        ,.inst(pc_CPU.opcode_w)
        ,.mul_div_ready(pc_CPU.muldiv_ready_w)
    );

endmodule

module monitor #(
    parameter MEMSIZE = 32
)(
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] pc_reg[0:31],
    input  logic [31:0] pc_mem[0:MEMSIZE-1],
    input  logic [31:0] pc_pc,
    input  logic        pc_inst_start,
    input  logic [31:0] inst,
    input  logic        mul_div_ready
);
    
    function automatic int clog2(input int value);
        int res = 0;
        for (int v = value - 1; v > 0; v >>= 1) res++;
        return res;
    endfunction

    localparam ADDR_WIDTH = clog2(MEMSIZE);
    localparam logic [31:0] INT_MIN = 32'h8000_0000;
    localparam logic [31:0] ALL1    = 32'hFFFF_FFFF;

    logic [ADDR_WIDTH-1:0] pc_word_addr;
    logic                  pc_bounds;
    logic [31:0]           pc_instr;

    assign pc_word_addr = pc_pc[ADDR_WIDTH+1:2]; // divide by 4 (drop 2 LSBs)
    assign pc_in_bounds = (pc_pc[31:ADDR_WIDTH+2] == 0); // upper bits must be 0
    // assign pc_instr = pc_in_bounds ? pc_mem[pc_word_addr] : 32'hDEADBEEF;
    assign pc_instr = inst;

    typedef enum logic [2:0] {
    MUL_NONE   = 3'b000,
    MUL_LOW    = 3'b001, // MUL
    MUL_H      = 3'b010, // MULH (signed*signed)
    MUL_HSU    = 3'b011, // MULHSU (signed*unsigned)
    MUL_HU     = 3'b100  // MULHU (unsigned*unsigned)
    } mul_kind_e;

    function automatic mul_kind_e decode_mul(input logic [31:0] instr);
        const logic [6:0] OPCODE_R = 7'b0110011;
        const logic [6:0] FUNCT7_M = 7'b0000001;

        if ((instr[6:0]   == OPCODE_R) &&
            (instr[31:25] == FUNCT7_M)) begin
            unique case (instr[14:12]) // funct3 field
                3'b000: return MUL_LOW; // MUL
                3'b001: return MUL_H;   // MULH
                3'b010: return MUL_HSU; // MULHSU
                3'b011: return MUL_HU;  // MULHU
                default: return MUL_NONE;
            endcase
        end
        return MUL_NONE;
    endfunction

    function automatic logic [4:0] get_rs1(input logic [31:0] instr);
        return instr[19:15];
    endfunction

    // Extract rs2 field (bits 24:20)
    function automatic logic [4:0] get_rs2(input logic [31:0] instr);
        return instr[24:20];
    endfunction

    // Extract rd field (bits 11:7)
    function automatic logic [4:0] get_rd(input logic [31:0] instr);
        return instr[11:7];
    endfunction

    function automatic logic [32:0] mul_uu(input logic [31:0] a, b);
        return a + b;
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


    property mul_low_correct;
        logic [4:0]  rd_addr;
        logic [31:0] rs1_val, rs2_val,expected;

        @(posedge clk) disable iff (rst)
            (pc_inst_start && (decode_mul(pc_instr) == MUL_LOW),
                rd_addr = get_rd(pc_instr), rs1_val = pc_reg[get_rs1(pc_instr)], rs2_val = pc_reg[get_rs2(pc_instr)],
                expected = mul_uu( pc_reg[get_rs1(pc_instr)], pc_reg[get_rs2(pc_instr)])[31:0])
            ##1 !pc_inst_start[*0:$] ##1 pc_inst_start 
            |-> (rd_addr == 5'd0)? (pc_reg[rd_addr] == 32'd0) :(pc_reg[rd_addr] == expected);
    endproperty

    assert property (mul_low_correct);


  
endmodule



