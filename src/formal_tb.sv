
`define FORMAL
`include "rv32i_header.vh"

module formal_tb(
    input clk,
    input resetn
    );
    
    localparam MEMSIZE = 32;
    localparam INSTSIZE = 6;
    
    //femto
    wire ft_mem_valid;
	wire ft_mem_instr;
	reg ft_mem_ready;
    wire ft_mem_rstrb;
	wire [31:0] ft_mem_addr;
	wire [31:0] ft_mem_wdata;
	wire [3:0] ft_mem_wmask;
	reg  [31:0] ft_mem_rdata;
	
	wire rst;
	wire ft_clk;
	wire pc_clk;
	reg ft_en;
	reg pc_en;
	
//	assign ft_clk = clk && ft_en;
//	assign pc_clk = clk && pc_en;
	assign ft_clk = clk;
	assign pc_clk = clk;	
	
	assign rst = !resetn;
	
    

   
   wire ft_inst_done;
   wire ft_inst_start;
   
	femtorv32 ft_CPU(
	      .clk(ft_clk),
	      .resetn(resetn),		 
	      .mem_addr(ft_mem_addr),
	      .mem_rdata(ft_mem_rdata),
	      .mem_rstrb(ft_mem_rstrb),
	      .mem_wdata(ft_mem_wdata),
	      .mem_wmask(ft_mem_wmask),
	      `ifdef FORMAL
	       .inst_done(ft_inst_done),
	       .inst_start(ft_inst_start)
	      `endif
	    
	   );

	reg [31:0] ft_memory [0:MEMSIZE-1]; // 1536 4-bytes words = 6 Kb of RAM in total

    integer i; 
	initial begin
		ft_memory[0] = 32'h 04000093; //       li      x1,64
		ft_memory[1] = 32'h 0000a023; //       sw      x0,0(x1)
		ft_memory[2] = 32'h 0000a103; // loop: lw      x2,0(x1)
		ft_memory[3] = 32'h 00110113;//       addi    x2,x2,1
		ft_memory[4] = 32'h 0020a023; //       sw      x2,0(x1)
		ft_memory[5] = 32'h ff5ff06f; //       j       <loop>
		
		for (i=6;i<MEMSIZE;i=i+1)
		   ft_memory[i] = 32'h 00000000;
	end

    always @(posedge ft_clk) begin
        if (!resetn) ;
        else begin
          if(ft_mem_rstrb) begin
              //if ((ft_mem_addr < MEMSIZE*4) && (ft_mem_addr > INSTSIZE*4))
              if (ft_mem_addr < MEMSIZE*4)
                  ft_mem_rdata <= ft_memory[ft_mem_addr >> 2];
              else
                  ft_mem_rdata <= 32'd0;
          end
          
      //      if ((ft_mem_addr < MEMSIZE*4) && (ft_mem_addr > INSTSIZE*4))
          if (ft_mem_addr < MEMSIZE*4)
              if(ft_mem_wmask[0]) ft_memory[ft_mem_addr >> 2][ 7:0 ] <= ft_mem_wdata[ 7:0 ];
              if(ft_mem_wmask[1]) ft_memory[ft_mem_addr >> 2][15:8 ] <= ft_mem_wdata[15:8 ];
              if(ft_mem_wmask[2]) ft_memory[ft_mem_addr >> 2][23:16] <= ft_mem_wdata[23:16];
              if(ft_mem_wmask[3]) ft_memory[ft_mem_addr >> 2][31:24] <= ft_mem_wdata[31:24];	
      end 
     end

//-------------------------------------------------------------------------------------//
    parameter MEMORY="memory.mem";
    parameter ZICSR_EXTENSION = 0;
    /******************************* MODIFY ****************************************/            
    
    
    rv32i_soc #(.PC_RESET(32'h00_00_00_00), .MEMORY_DEPTH(MEMSIZE*4), .CLK_FREQ_MHZ(100), .TRAP_ADDRESS(32'h00000004), .ZICSR_EXTENSION(ZICSR_EXTENSION)) uut (
        .i_clk(clk),
        .i_rst(!resetn)
        );
    
    reg [31:0] pc_reg[0:31];
    
    integer i;
    always @* begin
        pc_reg[0] = 32'b0; // x0 is always zero
        for (i = 1; i < 32; i = i + 1) begin
            pc_reg[i] = uut.m0.m0.base_regfile[i];
        end
    end
    
    reg [31:0] pc_mem[0:MEMSIZE-1];
    
    always @* begin
        for (i = 0; i < MEMSIZE; i = i + 1) begin
            pc_mem[i] = uut.m1.memory_regfile[i];
        end
    end
    
    
   monitor #(.MEMSIZE(MEMSIZE)) u_monitor (
        .clk(clk)
       ,.rst(rst)
       ,.pc_reg(pc_reg)
       ,.pc_mem(pc_mem)
       ,.ft_reg(ft_CPU.RegisterBank)
       ,.ft_pc(ft_CPU.PC)
       ,.pc_pc(uut.pc_pc)
       ,.ft_mem(ft_memory)
       ,.ft_inst_start(ft_inst_start)
       ,.pc_inst_start(uut.pc_inst_start)
       ,.pc_inst(uut.pc_inst)
       ,.pc_rs1_alu(uut.rs1_alu)
       ,.pc_rs2_alu(uut.rs2_alu)
       ,.pc_rs1_addr_alu(uut.rs1_addr_alu)
       ,.pc_rs2_addr_alu(uut.rs2_addr_alu)
   );

endmodule

module monitor #(
    parameter MEMSIZE = 32
)(
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] pc_reg[0:31],
    input  logic [31:0] ft_reg[0:31],
    input  logic [31:0] ft_mem[0:MEMSIZE-1],
    input  logic [31:0] pc_mem[0:MEMSIZE-1],
    input  logic [31:0] ft_pc,
    input  logic [31:0] pc_pc,
    // input  logic        inst_start,
    input  logic        pc_inst_start,
    input  logic        ft_inst_start,

    input logic [31:0]  pc_inst,
    input logic [31:0]  pc_rs1_alu,
    input logic [31:0]  pc_rs2_alu,
    input logic [4:0]   pc_rs1_addr_alu,
    input logic [4:0]   pc_rs2_addr_alu
);
    
    function automatic int clog2(input int value);
        int res = 0;
        for (int v = value - 1; v > 0; v >>= 1) res++;
        return res;
    endfunction

    localparam ADDR_WIDTH = clog2(MEMSIZE);

    logic [ADDR_WIDTH-1:0] ft_word_addr;
    logic                  ft_in_bounds;
    logic [31:0]           ft_instr;     

    assign ft_word_addr = ft_pc[ADDR_WIDTH+1:2]; // divide by 4 (drop 2 LSBs)
    assign ft_in_bounds = (ft_pc[31:ADDR_WIDTH+2] == 0); // upper bits must be 0
    assign ft_instr = ft_in_bounds ? ft_mem[ft_word_addr] : 32'hDEADBEEF;

    logic [ADDR_WIDTH-1:0] pc_word_addr;
    logic                  pc_bounds;
    logic [31:0]           pc_instr;

    assign pc_word_addr = pc_pc[ADDR_WIDTH+1:2]; // divide by 4 (drop 2 LSBs)
    assign pc_in_bounds = (pc_pc[31:ADDR_WIDTH+2] == 0); // upper bits must be 0
    // assign pc_instr = pc_in_bounds ? pc_mem[pc_word_addr] : 32'hDEADBEEF;
    assign pc_instr = pc_inst;


        // Decode fields
    logic [6:0]  opcode;
    logic [2:0]  funct3;
    logic [4:0]  rs1;
    logic signed [31:0] imm;
    logic [31:0] base_addr;
    logic [31:0] addr;
    logic [31:0] index;

    assign opcode     = ft_instr[6:0];
    assign funct3 = ft_instr[14:12];
    assign rs1 = ft_instr[19:15];
    assign imm = $signed(ft_instr[31:20]);
    assign base_addr = ft_reg[rs1];
    assign addr = base_addr + imm;
    assign index = addr >> 2;


    logic is_valid_load_and_equal_mem ;

    always @* begin
        is_valid_load_and_equal_mem = 0;
        if (opcode == 7'b0000011 && $signed(addr) >= 0) begin  // LOAD and addr >= 0
            case (funct3)
                3'b000, // LB
                3'b100: // LBU
                    if (index < MEMSIZE)
                        is_valid_load_and_equal_mem = (ft_mem[index] == pc_mem[index]);
    
                3'b001, // LH
                3'b101: // LHU
                    if (addr[0] == 1'b0 && index < MEMSIZE)
                        is_valid_load_and_equal_mem = (ft_mem[index] == pc_mem[index]);
    
                3'b010: // LW
                    if (addr[1:0] == 2'b00 && index < MEMSIZE)
                        is_valid_load_and_equal_mem = (ft_mem[index] == pc_mem[index]);
    
                default:
                    is_valid_load_and_equal_mem = 0;
            endcase
        end
    end

    
    property eqv_on_load;
        @(posedge clk) disable iff (rst)
            pc_inst_start && ft_inst_start && (ft_instr == pc_instr) && (pc_reg == ft_reg)  
            && is_valid_load_and_equal_mem
            |-> ##6 (ft_reg == $past(pc_reg, 5));
    endproperty

    assert property (eqv_on_load); 



    logic [6:0]  opcode  ; 
    logic [2:0]  funct3  ; 
    logic [6:0]  funct7  ; 

    assign opcode = ft_instr[6:0];
    assign funct3 = ft_instr[14:12];
    assign funct7 = ft_instr[31:25];

    logic valid_R_type;

    always @* begin
        valid_R_type = 0;
    
        if (opcode == 7'b0110011) begin
            case ({funct7, funct3})
                10'b0000000000,  // add
                10'b0100000000,  // sub
                10'b0000000001,  // sll
                10'b0000000010,  // slt
                10'b0000000011,  // sltu
                10'b0000000100,  // xor
                10'b0000000101,  // srl
                10'b0100000101,  // sra
                10'b0000000110,  // or
                10'b0000000111:  // and
                    valid_R_type = 1;
                default:
                    valid_R_type = 0;
            endcase
        end
    end

    property eqv_on_R_type;
        @(posedge clk) disable iff (rst)
            pc_inst_start && ft_inst_start && (ft_instr == pc_instr) && (pc_reg == ft_reg)  && (ft_instr_cnt > 5) && (pc_instr_cnt > 10)
            && valid_R_type 
            && (pc_rs1_alu == pc_reg[pc_rs1_addr_alu]) && (pc_rs2_alu == pc_reg[pc_rs2_addr_alu])
            // 
            |->  ##4 (ft_reg == $past(pc_reg, 3));
    endproperty

    assert property (eqv_on_R_type); 

    property correct_alu_operand;
        @(posedge clk) disable iff (rst)
            pc_inst_start 
            |-> (pc_rs1_alu == pc_reg[pc_rs1_addr_alu]) && (pc_rs2_alu == pc_reg[pc_rs2_addr_alu]);
    endproperty

    assert property (correct_alu_operand); 

    logic [10:0] ft_instr_cnt;
    logic [10:0] pc_instr_cnt;

    always @(posedge clk) begin
        if (rst) begin
            ft_instr_cnt <= 0;
            pc_instr_cnt <= 0;
        end
        else begin
          if(ft_inst_start) ft_instr_cnt <= ft_instr_cnt + 1;
          else if (pc_inst_start) pc_instr_cnt <= pc_instr_cnt + 1; 
          end
     end

     cover property (@(posedge clk) ft_instr_cnt > 10);
     cover property (@(posedge clk) pc_instr_cnt > 10);


//     function automatic logic is_aligned_load_lw(input logic [31:0] instr, input logic [31:0] regfile [0:31]);
//     logic [6:0] opcode;
//     logic [2:0] funct3;
//     logic [4:0] rs1;
//     logic signed [11:0] imm;
//     logic [31:0] base, addr;
    
//     opcode = instr[6:0];
//     funct3 = instr[14:12];
//     rs1    = instr[19:15];
//     imm    = $signed(instr[31:20]);
//     base   = regfile[rs1];
//     addr   = base + imm;
    
//     return (opcode == 7'b0000011 && funct3 == 3'b010 && addr[1:0] == 2'b00);
// endfunction

// property eqv_on_load;
//     @(posedge clk) disable iff (rst)
//         pc_inst_start && ft_inst_start &&
//         (ft_instr == pc_instr) &&
//         (pc_reg == ft_reg) &&
//         is_valid_load_and_equal_mem(ft_instr, ft_reg, ft_mem, pc_mem) &&
//         is_aligned_load_lw(ft_instr, ft_reg)
//         |-> ##6 (ft_reg == $past(pc_reg, 5));
// endproperty


    // function automatic logic compare_word_at_63_div_4
    // (
    //     input logic [31:0] pc_mem [0:MEMSIZE-1],
    //     input logic [31:0] ft_mem [0:MEMSIZE-1]
    // );
    //     localparam int MEMSIZE = 32;
    //     logic [31:0] index;

    //     index = 63 >> 2;  // index = 15

    //     if (index < MEMSIZE)
    //         compare_word_at_63_div_4 = (pc_mem[index] == ft_mem[index]);
    //     else
    //         compare_word_at_63_div_4 = 0;  // Out-of-bounds access protection
    // endfunction

    // property eqv_on_ld;
 
    //     @(posedge clk) disable iff (rst)
    //         pc_inst_start && ft_inst_start && (ft_instr == 32'h 040faf83) && (pc_instr == 32'h 040faf83) && (pc_reg == ft_reg) && (pc_reg[31] == 32'd0)&& (ft_reg[31] == 32'd0)&& (compare_word_at_63_div_4 (ft_mem, pc_mem)) 
    //         |-> ##6 (ft_reg == $past(pc_reg, 5));
    // endproperty

    // assert property (eqv_on_ld); 
    // property eqv_on_ld;
 
    //     @(posedge clk) disable iff (rst)
    //         pc_inst_start && ft_inst_start && (ft_instr == 32'h3fc00093) && (pc_instr == 32'h3fc00093) && (pc_reg == ft_reg) 
    //         |-> ##4 (ft_reg == $past(pc_reg, 3));
    // endproperty

    //    assert property (eqv_on_ld); 
    // endproperty

    // property eqv_on_addi;
 
    //     @(posedge clk) disable iff (rst)
    //         pc_inst_start && ft_inst_start && (ft_instr == 32'h 00110113) && (pc_instr == 32'h 00110113) && (pc_reg == ft_reg) 
    //         |-> ##4 (ft_reg == $past(pc_reg, 3));
    // endproperty
    // // endproperty

    // assert property (eqv_on_addi); 
    
    // genvar i;
    // generate
    // for (i = 0; i < MEMSIZE; i++) begin : gen_mem_assumption
    //     assume property (@(posedge clk) ft_mem[i] == pc_mem[i]);
    // end
    // endgenerate


    // assume property (mems_equal);


endmodule
