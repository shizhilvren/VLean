module add_1bit (
    input wire a,
    input wire b,
    input wire clk,
    output reg sum,
    input reg cin,
);
    always @(posedge clk) begin
        sum <= a + b;
        cin <= a & b;
    end
endmodule