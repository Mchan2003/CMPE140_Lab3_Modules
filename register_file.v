module register_file(
    input wire rst_n,
    input wire clk,
    input wire [0:4] rs1, 
    input wire [0:4] rs2,
    input wire [0:4] rd,
    input wire [0:31] wd,
    input wire we,
    output wire [0:31] data_rs1,
    output wire [0:31] data_rs2
);
reg [31:0] register [31:0];

assign data_rs1 = register[rs1];
assign data_rs2 = register[rs2];

integer i;

always @ (posedge clk)
begin
    if (rst_n)begin
        for (i = 0; i < 32; i = i + 1) begin
            register[i] <= 32'b0;
        end    
    end
    if(we) begin
        register[rd] <= wd;
    end
end

endmodule
