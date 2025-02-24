`timescale 1ns / 1ps

module cpu(rst_n, clk, imem_addr, imem_insn, dmem_addr, dmem_data, dmem_wen);

    input rst_n, clk; // active low reset, clock
    output [31:0] imem_addr; // Instruction memory address
    input [31:0] imem_insn; // Instruction from instruction memory
    output [31:0] dmem_addr; // Data memory address
    inout [31:0] dmem_data; // Data to/from memory
    output dmem_wen; // Write enable for data memory (1 for Store, 0 for Load)
    
    reg [31:0] pc, new_pc = 0; // program counter
    
    // IF: Instruction fetch from memory
    reg [31:0] instruction;    // instruction (fetch output)
    
    fetch f(rst_n, pc, imem_insn, new_pc, imem_addr, instruction);
    
    always @(posedge clk) begin 
        if(!rst_n) begin
            pc <= 0;
        end else begin
            pc <= new_pc;
        end
    end

    // ID: Instruction decode & register read
    reg [4:0] rs1, rs2, rd; // rd - destination
    //reg branch, mem_read, mem_to_reg, mem_write, reg_write, alu_src;
    reg [1:0] alu_op;
    reg [31:0] read_data_one, read_data_two, imm;
    decode d(rst_n, instruction, rs1, rs2, rd, alu_op, read_data_one, read_data_two, imm);
    
    // EX: Execute operation or calculate address
    reg [31:0] alu_result;
    execute e(rst_n, read_data_one, read_data_two, alu_op, alu_result);

    // MEM and WB not needed
    // MEM: Access memory operand
    // WB: Write result back to register
    
    always @ (posedge clk) begin
        integer h1;
        h1 = $fopen("trace_pc.txt");
        $fwrite(h1, "%h\n", pc);
    end

endmodule

module fetch(rst, clk, pc, imem_insn, new_pc, imem_addr, instruction);
    input rst, clk;
    input [31:0] pc, imem_insn;
    output reg [31:0] new_pc, imem_addr, instruction;
        
    always @(posedge clk) begin
    if(!rst) begin
        imem_addr <= 0;
    end else begin
        instruction = rst ? imem_insn : 0;
        new_pc = pc + 4;
        imem_addr = pc; 
        end
    end   
endmodule

//Basic Test Pass
//module decode(instruction, rs1, rs2, rd, branch, mem_read, mem_to_reg, mem_write, reg_write, alu_src,
//            alu_op, read_data_one, read_data_two);
module decode (rst, clk, instruction, rs1, rs2, rd, alu_op, read_data_one, read_data_two,imm);
    input [31:0] instruction;
    input rst, clk;
    output reg [4:0] rs1, rs2, rd;
    output reg [31:0] read_data_one, read_data_two, imm;
    // output reg branch, mem_read, mem_to_reg, mem_write, alu_src, reg_write;
    output reg [1:0] alu_op;
    
    reg [6:0] opcode;
    reg [2:0]  func3;
    
    always @(posedge clk) begin
    if(!rst) begin
        read_data_one <= 0;
        read_data_two <= 0;
    end else begin
        opcode = instruction[6:0];
        rd = instruction[11:7];
        func3 = instruction[14:12];
        rs1 = instruction[19:15];
        imm = instruction[31:20];
        case (opcode) 
        7'b0010011: begin
            if(func3 == 3'b000) begin
                alu_op = 2'b00; 
            end
        end
        default: begin
            alu_op = 4'b11; //no operator 
        end
        endcase
        read_data_one = rs1;
        read_data_two = imm;    
        end  
    end
endmodule

module execute(rst, clk, alu_op, input1, input2, result);
    input [1:0] alu_op;
    input rst, clk;
    input [31:0] input1, input2;
    output reg [31:0] result;

    always @(posedge clk) begin
    if(!rst) begin
        result <= 0;
    end else if (alu_op == 2'b0) begin
        result = input1 + input2; 
    end
end    
endmodule



