module cpu(input rst_n, clk, input [31:0] imem_insn, inout [31:0] dmem_data, output
dmem_wen, output [31:0] imem_addr, dmem_addr);
wire ALUSrc, MemtoReg, MemRead, MemWrite, Branch, id_ex_RegWrite, Zero;

ex_mem_RegWrite, mem_wb_RegWrite, stall, ex_mem_MemtoReg, mem_wb_MemtoReg,
wb_RegWrite;

wire [1:0] ALUOp; 
wire [1:0]forwardA_sig;
wire [1:0] forwardB_sig;
wire [3:0] ALUCtl;
wire [4:0] rs1, rs2, id_ex_rd, ex_mem_rd, mem_wb_rd, reg_addr;

wire [31:0] rd1, rd2, imm_val, ALU_result, target, dmem_data_cpu, mem_wb_ALU_result,
write_data;

reg [15:0] clk_counter;

fetch fetch_cycle
(.rst_n(rst_n), .clk(clk), .Branch(Branch), .Zero(Zero), .stall(stall),
.target(target), .imem_addr(imem_addr));

decode decode_cycle
(.rst_n(rst_n), .clk(clk), .stall(stall), .wb_RegWrite(wb_RegWrite),
.reg_addr(reg_addr),
.imem_insn(imem_insn), .wd(write_data),
.ALUSrc(ALUSrc), .MemtoReg(MemtoReg), .MemRead(MemRead),
.MemWrite(MemWrite), .Branch(Branch), .id_ex_RegWrite(id_ex_RegWrite),
.ALUOp(ALUOp), .ALUCtl(ALUCtl),
.rs1(rs1), .rs2(rs2), .id_ex_rd(id_ex_rd),
.rd1(rd1), .rd2(rd2), .imm_val(imm_val));

execute execute_cycle
(.rst_n(rst_n), .clk(clk), .Branch(Branch), .ALUSrc(ALUSrc),
.id_ex_RegWrite(id_ex_RegWrite), .id_ex_MemtoReg(MemtoReg), .stall(stall),
.ALUOp(ALUOp), .forwardA_ex(forwardA_sig), .forwardB_ex(forwardB_sig),
.ctl(ALUCtl),
.id_ex_rd(id_ex_rd),
.rd1(rd1), .rd2(rd2), .imm_val(imm_val), .imem_addr(imem_addr), .imem_insn(imem_insn),
.wb_result(write_data),
.Zero(Zero), .ex_mem_RegWrite(ex_mem_RegWrite),
.ex_mem_MemtoReg(ex_mem_MemtoReg),
.ex_mem_rd(ex_mem_rd),
.ALU_result(ALU_result), .target(target));

memory memory_cycle
(.rst_n(rst_n), .clk(clk), .ex_mem_RegWrite(ex_mem_RegWrite),
.ex_mem_MemtoReg(ex_mem_MemtoReg),
.ex_mem_rd(ex_mem_rd),
.ex_mem_ALU_result(ALU_result),
.mem_wb_RegWrite(mem_wb_RegWrite), .mem_wb_MemtoReg(mem_wb_MemtoReg),
.mem_wb_rd(mem_wb_rd),
.mem_wb_ALU_result(mem_wb_ALU_result));

write_back write_back_cycle
(.rst_n(rst_n), .clk(clk), .MemtoReg(mem_wb_MemtoReg),
.mem_wb_RegWrite(mem_wb_RegWrite),
.mem_wb_rd(mem_wb_rd),
.read_data(32'd0), .mem_wb_ALU_result(mem_wb_ALU_result),
.wb_RegWrite(wb_RegWrite),
.reg_addr(reg_addr),
.write_data(write_data));

hazard_detection_unit hazard
(.id_ex_MemRead(MemRead), .ex_mem_RegWrite(ex_mem_RegWrite),
.id_ex_RegWrite(id_ex_RegWrite), .mem_wb_RegWrite(mem_wb_RegWrite),
.wb_RegWrite(wb_RegWrite),
.rs1(imem_insn[19:15]), .rs2(imem_insn[24:20]), .id_ex_rd(id_ex_rd),
.ex_mem_rd(ex_mem_rd), .mem_wb_rd(mem_wb_rd), .reg_addr(reg_addr),
.stall(stall));

forward_unit forward
(.ex_mem_RegWrite(ex_mem_RegWrite), .wb_RegWrite(wb_RegWrite),
.rs1(rs1), .rs2(rs2), .ex_mem_rd(ex_mem_rd), .reg_addr(reg_addr),
.forwardA(forwardA_sig), .forwardB(forwardB_sig));

integer fd1, fd2;

initial begin
fd1 = $fopen("C:/Users/kur0neko/Downloads/cpu/cpu.srcs/sources_1/imports/Desktop/pc.txt", "w");
fd2 = $fopen("C:/Users/kur0neko/Downloads/cpu/cpu.srcs/sources_1/imports/Desktop/updates.txt", "w");
end

always @ (posedge clk or negedge rst_n) begin
if (~rst_n) begin
clk_counter <= 32'd1;
end
else begin
clk_counter <= clk_counter + 1;
$fwrite(fd1, "pc: %h\n", imem_addr);
$fwrite(fd2, "clk cycle %d | reg: %0d | write_data: %0h\n", clk_counter, reg_addr, write_data);
$display("clk cycle %d | write_data: %0h | reg %0d | forwarda: %0h, forwardb: %0h, stall: %0b | rs1: %0h | rs2: %0h | wb_RegWrite: %0h",
clk_counter, write_data, reg_addr, forwardA_sig, forwardB_sig, stall, imem_insn[19:15], imem_insn[24:20], wb_RegWrite);
end
end

endmodule

module fetch(input rst_n, clk, Branch, Zero, stall, input [31:0] target, output [31:0] imem_addr);
wire [31:0] PC, PCPlus4, PC_Next;

mux pc_mux(.a(PCPlus4), .b(target), .s(Branch && Zero), .c(PC_Next));
adder pc_adder(.a(PC), .b(32'h00000004), .c(PCPlus4));
pc pc(.clk(clk), .rst_n(rst_n), .stall(stall), .pc_next(PC_Next), .pc(PC));

assign imem_addr = PC;

endmodule

module mux(input s, input [31:0] a, b, output [31:0] c);
assign c = ~s ? a : b;
endmodule

module mux4_1
(input [1:0] s,
 input [31:0] a, b, c,
 output [31:0] d);
assign d = (s == 2'b01) ? b : (s == 2'b10) ? c : a;
// $display("rs: %0h, memwb: %0h, alu: %0h, pick: %0h, forward: %0h", a, b, c, d, s);
endmodule

module adder(input [31:0] a, b, output [31:0] c);
assign c = a + b;
endmodule

module pc(input clk, rst_n, stall, input [31:0] pc_next, output reg [31:0] pc);

always @(posedge clk or negedge rst_n)
begin
    if (~rst_n) 
        pc <= 32'h00000000;
    else if (~stall) 
        pc <= pc_next;
end

endmodule

module decode
(input rst_n, clk, stall, wb_RegWrite,
input [4:0] reg_addr,
input [31:0] imem_insn, wd,
output ALUSrc, MemtoReg, MemRead, MemWrite, Branch, id_ex_RegWrite,
output [1:0] ALUOp,
output [3:0] ALUCtl,
output [4:0] rs1, rs2, id_ex_rd,
output [31:0] rd1, rd2, imm_val);

wire ALUSrcD, MemtoRegD, RegWriteD, MemReadD, MemWriteD, BranchD;
wire [1:0] ALUOpD;
wire [3:0] ctl;
wire [31:0] rd1_d, rd2_d, imm_valD;

reg ALUSrc_reg, MemtoReg_reg, MemRead_reg, MemWrite_reg, Branch_reg, RegWrite_reg;
reg [1:0] ALUOp_reg;
reg [3:0] ctl_reg;
reg [4:0] rs1_reg, rs2_reg, id_ex_rd_reg;
reg [31:0] rd1_reg, rd2_reg, imm_val_reg;

register_file rf
(.rst_n(rst_n), .clk(clk), .RegWrite(wb_RegWrite),
.rr1(imem_insn[19:15]), .rr2(imem_insn[24:20]), .wr(reg_addr),
.wd(wd),
.rd1(rd1_d), .rd2(rd2_d));

control_unit cu
(.opcode(imem_insn[6:0]),
.ALUSrc(ALUSrcD), .MemtoReg(MemtoRegD), .RegWrite(RegWriteD),
.MemRead(MemReadD), .MemWrite(MemWriteD), .Branch(BranchD),
.ALUOp(ALUOpD));

alu_control alu_control
(.ALUOp(ALUOpD),
.Funct3(imem_insn[14:12]),
.Funct7(imem_insn[31:25]),
.op(ctl));

imm_gen imm_gen_module
(.imem_insn(imem_insn),
.imm_val(imm_valD));

always @ (posedge clk or negedge rst_n) begin
    if (~rst_n || stall) begin
        ALUSrc_reg <= 1'b0;
        MemtoReg_reg <= 1'b0;
        MemRead_reg <= 1'b0;
        MemWrite_reg <= 1'b0;
        Branch_reg <= 1'b0;
        RegWrite_reg <= 1'b0;
        ALUOp_reg <= 2'b00;
        ctl_reg <= 4'b0000;
        rs1_reg <= 5'b00000;
        rs2_reg <= 5'b00000;
        id_ex_rd_reg <= 5'b00000;
        rd1_reg <= 32'h00000000;
        rd2_reg <= 32'h00000000;
        imm_val_reg <= 32'h00000000;
    end
    else begin
        ALUSrc_reg <= ALUSrcD;
        MemtoReg_reg <= MemtoRegD;
        MemRead_reg <= MemReadD;
        MemWrite_reg <= MemWriteD;
        Branch_reg <= BranchD;
        RegWrite_reg <= RegWriteD;
        ALUOp_reg <= ALUOpD;
        ctl_reg <= ctl;
        rs1_reg <= imem_insn[19:15];
        rs2_reg <= imem_insn[24:20];
        id_ex_rd_reg <= imem_insn[11:7];
        rd1_reg <= rd1_d;
        rd2_reg <= rd2_d;
        imm_val_reg <= imm_valD;
    end
end

assign ALUSrc = ALUSrc_reg;
assign MemtoReg = MemtoReg_reg;
assign MemRead = MemRead_reg;
assign MemWrite = MemWrite_reg;
assign Branch = Branch_reg;
assign id_ex_RegWrite = RegWrite_reg;
assign ALUOp = ALUOp_reg;
assign ALUCtl = ctl_reg;
assign rs1 = rs1_reg;
assign rs2 = rs2_reg;
assign rd1 = rd1_reg;
assign rd2 = rd2_reg;
assign id_ex_rd = id_ex_rd_reg;
assign imm_val = imm_val_reg;
endmodule


module register_file
(input rst_n, clk, RegWrite,
 input [4:0] rr1, rr2, wr,
 input [31:0] wd,
 output [31:0] rd1, rd2);

 reg [31:0] register [31:0];
 integer i;

 always @ (posedge clk or negedge rst_n) begin
     if (~rst_n) begin
         for (i = 0; i < 32; i = i + 1) register[i] <= 0;
     end
     else if (RegWrite) begin
         register[wr] <= wd;
         //$display("wr: %0h, rd1: %0h, regval: %0h, reg5: %0h", wr, rd1, wd, register[5]);
     end
 end

 assign rd1 = register[rr1];
 assign rd2 = register[rr2];

endmodule

module control_unit
(input [6:0] opcode,
 output ALUSrc, MemtoReg, RegWrite, MemRead, MemWrite, Branch,
 output [1:0] ALUOp);

 wire [6:0] r_type, lw, sw, beq, i_type;
 assign r_type = 7'b0110011;
 assign lw = 7'b0000011;
 assign sw = 7'b0100011;
 assign beq = 7'b1100011;
 assign i_type = 7'b0010011;

 assign ALUSrc = (opcode == lw || opcode == sw || opcode == i_type);
 assign MemtoReg = (opcode == lw);
 assign RegWrite = (opcode == r_type || opcode == lw || opcode == i_type);
 assign MemRead = (opcode == lw);
 assign MemWrite = (opcode == sw);
 assign Branch = (opcode == beq);
 assign ALUOp[1] = (opcode == r_type || opcode == i_type);
 assign ALUOp[0] = (opcode == beq);

endmodule

module alu_control
(input [1:0] ALUOp,
 input [2:0] Funct3,
 input [6:0] Funct7,
 output [3:0] op);

 assign op[0] = ((ALUOp == 2'b10) && (Funct3 == 3'b110)) || // r/i-or
                ((ALUOp == 2'b10) && (Funct3 == 3'b100)) || // r/i-xor
                ((ALUOp == 2'b10) && (Funct3 == 3'b101) && (Funct7 == 7'b0000000)) || // r/i->>
                ((ALUOp == 2'b10) && (Funct3 == 3'b101) && (Funct7 == 7'b0100000)) || // r/i->>>
                ((ALUOp == 2'b01) && (Funct3 == 3'b001)) || // bne
                ((ALUOp == 2'b01) && (Funct3 == 3'b101)) || // bge
                ((ALUOp == 2'b01) && (Funct3 == 3'b111));  // bgeu

 assign op[1] = (ALUOp == 2'b00) || // sw/auipc/jalr-add
                ((ALUOp == 2'b10) && (Funct3 == 3'b000)) || // r/i-add
                ((ALUOp == 2'b10) && (Funct3 == 3'b100)) || // r/i-xor
                ((ALUOp == 2'b10) && (Funct7 == 7'b0100000) && (Funct3 == 3'b000)) || // r-sub
                ((ALUOp == 2'b10) && (Funct3 == 3'b101) && (Funct7 == 7'b0100000)) || // r/i->>>
                (ALUOp == 2'b11) || // jal/lui: return 1
                ((ALUOp == 2'b10) && (Funct3 == 3'b011)) || // sltiu, sltu: <u
                ((ALUOp == 2'b01) && (Funct3 == 3'b110)) || // blt
                ((ALUOp == 2'b01) && (Funct3 == 3'b111));  // bgeu

 assign op[2] = ((ALUOp == 2'b10) && (Funct3 == 3'b101) && (Funct7 == 7'b0000000)) || // r/i->>
                ((ALUOp == 2'b10) && (Funct3 == 3'b101) && (Funct7 == 7'b0100000)) || // r/i->>>
                ((ALUOp == 2'b10) && (Funct3 == 3'b001)) || // r/i-<<
                ((ALUOp == 2'b10) && (Funct7 == 7'b0100000) && (Funct3 == 3'b000)) || // r-sub
                ((ALUOp == 2'b10) && (Funct3 == 3'b010)) || // slti
                ((ALUOp == 2'b10) && (Funct3 == 3'b011)) || // sltiu
                ((ALUOp == 2'b01) && (Funct3 == 3'b110)) || // bltu
                ((ALUOp == 2'b01) && (Funct3 == 3'b100)) || // blt
                ((ALUOp == 2'b01) && (Funct3 == 3'b101)) || // bge
                ((ALUOp == 2'b01) && (Funct3 == 3'b111));  // bgeu

 assign op[3] = (ALUOp == 2'b01) || // bne, beq, blt, bge, bltu, bgeu
                (ALUOp == 2'b11) || // jal/lui: return 1
                ((ALUOp == 2'b10) && (Funct3 == 3'b010)) || // slti
                ((ALUOp == 2'b10) && (Funct3 == 3'b011));  // sltiu

endmodule

module imm_gen
(input [31:0] imem_insn,
 output logic [31:0] imm_val);

 wire [6:0] i_type;
 assign i_type = 7'b0010011;

 always_comb begin
     case(imem_insn[6:0])
         i_type:
             imm_val = {{20{imem_insn[31]}}, imem_insn[31:20]};
         default:
             imm_val = 32'h0;
     endcase
 end

endmodule

module execute
(input rst_n, clk, Branch, ALUSrc, id_ex_RegWrite, id_ex_MemtoReg, wb_RegWrite, stall,
 input [1:0] ALUOp, forwardA_ex, forwardB_ex,
 input [3:0] ctl,
 input [4:0] id_ex_rd,
 input [31:0] rd1, rd2, imm_val, imem_addr, imem_insn, wb_result, mem_wb_MemtoReg,
 output Zero, ex_mem_RegWrite, ex_mem_MemtoReg,
 output [4:0] ex_mem_rd,
 output [31:0] ALU_result, target);

 wire Zero_e;
 wire [31:0] operand, ALU_result_e, target_e, a_src, b_src;

 reg ex_mem_RegWrite_reg, Zero_reg, ex_mem_MemtoReg_reg;
 reg [4:0] ex_mem_rd_reg;
 reg [31:0] ALU_result_reg, target_reg;

mux alu_mux(.s(ALUSrc), .a(b_src), .b(imm_val), .c(operand));

alu alu
(.ctl(ctl),
 .a(rd1), .b(operand),
 .Zero(Zero_e),
 .ALU_result(ALU_result_e));

adder target_adder (.a(imem_addr), .b(imm_val << 1), .c(target_e));

always @ (posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        Zero_reg <= 1'b0;
        ex_mem_RegWrite_reg <= 1'b0;
        ex_mem_MemtoReg_reg <= 1'b0;
        ex_mem_rd_reg <= 5'b00000;
        ALU_result_reg <= 32'd0;
        target_reg <= 32'd0;
    end
    else begin
        Zero_reg <= Zero_e;
        ex_mem_RegWrite_reg <= id_ex_RegWrite;
        ex_mem_MemtoReg_reg <= id_ex_MemtoReg;
        ex_mem_rd_reg <= id_ex_rd;
        ALU_result_reg <= ALU_result_e;
        target_reg <= target_e;
    end
end

assign ALU_result = ALU_result_reg;
assign target = target_reg;
assign ex_mem_rd = ex_mem_rd_reg;
assign ex_mem_MemtoReg = ex_mem_MemtoReg_reg;
assign Zero = Zero_reg;
assign ex_mem_RegWrite = ex_mem_RegWrite_reg;

endmodule

module alu
(input [3:0] ctl,
 input [31:0] a, b,
 output Zero,
 output reg [31:0] ALU_result);

 assign Zero = (ALU_result == 0);

 always @ (*) begin
     case(ctl)
         0: ALU_result = a & b;
         1: ALU_result = a | b;
         2: ALU_result = $signed(a) + $signed(b);
         6: ALU_result = $signed(a) - $signed(b);
         7: ALU_result = $signed(a) < $signed(b) ? 32'd1 : 32'd0;
         12: ALU_result = ~(a | b);
         default:
             ALU_result = 32'd0;
     endcase
 end

endmodule

module memory
(input rst_n, clk, ex_mem_RegWrite, ex_mem_MemtoReg,
 input [4:0] ex_mem_rd,
 input [31:0] ex_mem_ALU_result,
 output mem_wb_RegWrite, mem_wb_MemtoReg,
 output [4:0] mem_wb_rd,
 output [31:0] mem_wb_ALU_result);

 reg mem_wb_RegWrite_reg, mem_wb_MemtoReg_reg;
 reg [4:0] mem_wb_rd_reg;
 reg [31:0] mem_wb_ALU_result_reg;

 always @ (posedge clk or negedge rst_n) begin
     if (~rst_n) begin
         mem_wb_RegWrite_reg <= 1'b0;
         mem_wb_MemtoReg_reg <= 1'b0;
         mem_wb_rd_reg <= 5'b00000;
         mem_wb_ALU_result_reg <= 32'd0;
     end
     else begin
         mem_wb_RegWrite_reg <= ex_mem_RegWrite;
         mem_wb_MemtoReg_reg <= ex_mem_MemtoReg;
         mem_wb_rd_reg <= ex_mem_rd;
         mem_wb_ALU_result_reg <= ex_mem_ALU_result;
     end
 end

 assign mem_wb_RegWrite = mem_wb_RegWrite_reg;
 assign mem_wb_MemtoReg = mem_wb_MemtoReg_reg;
 assign mem_wb_rd = mem_wb_rd_reg;
 assign mem_wb_ALU_result = mem_wb_ALU_result_reg;

endmodule

module write_back
(input rst_n, clk, MemtoReg, mem_wb_RegWrite,
 input [4:0] mem_wb_rd,
 input [31:0] read_data, mem_wb_ALU_result,
 output wb_RegWrite,
 output [4:0] reg_addr,
 output [31:0] write_data);

 wire [31:0] write_data_w;

 reg wb_RegWrite_reg;
 reg [4:0] reg_addr_reg;
 reg [31:0] write_data_reg;

 mux write_back_mux(.s(MemtoReg), .a(mem_wb_ALU_result), .b(read_data),
 .c(write_data_w));

 always @ (posedge clk or negedge rst_n) begin
     if (~rst_n) begin
         wb_RegWrite_reg <= 1'b0;
         reg_addr_reg <= 5'b00000;
         write_data_reg <= 32'd0;
     end
     else begin
         wb_RegWrite_reg <= mem_wb_RegWrite;
         reg_addr_reg <= mem_wb_rd;
         write_data_reg <= write_data_w;
     end
 end

 assign wb_RegWrite = wb_RegWrite_reg;
 assign reg_addr = reg_addr_reg;
 assign write_data = write_data_reg;

endmodule

module mux(input s, input [31:0] a, b, output [31:0] c);
 assign c = ~s ? a : b;
endmodule

module mux4_1
(input [1:0] s,
 input [31:0] a, b, c,
 output [31:0] d);

 assign d = (s == 2'b01) ? b : (s == 2'b10) ? c : a;

endmodule

module hazard_detection_unit
(input id_ex_MemRead, ex_mem_RegWrite, id_ex_RegWrite, mem_wb_RegWrite,
 wb_RegWrite,
 input [4:0] rs1, rs2, id_ex_rd, ex_mem_rd, mem_wb_rd, reg_addr,
 output reg stall);

 always @ (*) begin
     if (id_ex_RegWrite &&
         ((id_ex_rd == rs1) || (id_ex_rd == rs2))) begin
         stall = 1;
     end
     else if (ex_mem_RegWrite &&
         ((ex_mem_rd == rs1) || (ex_mem_rd == rs2))) begin
         stall = 1;
     end
     else if (mem_wb_RegWrite &&
         ((mem_wb_rd == rs1) || (mem_wb_rd == rs2))) begin
         stall = 1;
     end
     else if (wb_RegWrite &&
         ((reg_addr == rs1) || (reg_addr == rs2))) begin
         stall = 1;
     end
     else if (id_ex_MemRead &&
         ((id_ex_rd == rs1) || (id_ex_rd == rs2))) begin
         stall = 1;
     end
     else begin
         stall = 0;
     end
 end

endmodule

module forward_unit
(input ex_mem_RegWrite, wb_RegWrite,
 input [4:0] rs1, rs2, ex_mem_rd, reg_addr,
 output [1:0] forwardA, forwardB);

 //think of these as if and else-if statements
 assign forwardA = ((ex_mem_RegWrite) && (ex_mem_rd != 0) && (ex_mem_rd == rs1)) ?
                   2'b10 :
                   ((wb_RegWrite) && (reg_addr != 0) && (reg_addr == rs1)) ? 2'b01 : 2'b00;

 assign forwardB = ((ex_mem_RegWrite) && (ex_mem_rd != 0) && (ex_mem_rd == rs2)) ?
                   2'b10 :
                   ((wb_RegWrite) && (reg_addr != 0) && (reg_addr == rs2)) ? 2'b01 : 2'b00;

 // $display("ex_mem_RegWrite: %0h | mem_wb_RegWrite: %0h | rs1: %0h | rs2: %0h |
 // ex_mem_rd: %0h | mem_wb_rd: %0h", ex_mem_RegWrite, mem_wb_RegWrite, rs1, rs2,
 // ex_mem_rd, mem_wb_rd);

endmodule
