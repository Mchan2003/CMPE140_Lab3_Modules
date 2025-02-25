module control_unit(
    input wire rst_n,
    input wire clk,
    input wire [6:0] opcode,
    output reg branch,
    output reg memRead,
    output reg memToReg,
    output reg [1:0] ALUOp,
    output reg memWrite,
    output reg ALUSrc,
    output reg regWrite   
);
always @ (posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b00000000;
    end
    case(opcode)
        //R-Type
        7'b0110011: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b00010001;
        //I-Type
        7'b0010011: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b00000011;
        //I-Type (Load)
        7'b0000011: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b01100011;
        //S-Type
        7'b0100011: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b00x00110;
        //B-Type
        7'b1100011: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b10x01000;
        //U-Type
        7'b0110111: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b00011011;
        //J-Type
        7'b1101111: {branch, memRead, memToReg, ALUOp, memWrite, ALUSrc, regWrite} <= 8'b000xx011;
    endcase
end
endmodule