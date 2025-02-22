module instruction_memory(
    input rst_n,
    input clk,
    input rsi1, 
    input rsi2,
    input data,
    input rdi,
    input we,
    output rsi1,
    output rsi2
);
reg [31:0] register [31:0];

assign rs1 = register[rsi1];
assign rs2 = register[rsi2];

always @ (posedge clk)
begin
    if(we) begin
        register[rdi] <= data;
    end
end


endmodule
