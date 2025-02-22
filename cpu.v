`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/17/2025 09:50:41 AM
// Design Name: 
// Module Name: cpu
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module cpu(
    input rst_n,
    input clk,
    output [31:0] imem_addr,
    input [31:0] imem_insn,
    output [31:0] dmem_addr,
    inout [31:0] dmem_data,
    output dmem_wen 
    );
    
    reg [31:0] pc;
    assign pc = imem_insn;
    always @ (posedge clk)begin
        pc = pc + 4
    end
    
    //Fetch
    //Decode
    //Execute
    //Memory Access
    //Write Back
    
endmodule
