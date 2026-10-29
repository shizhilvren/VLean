
module dff_en (
    input wire clk,
    input wire in,
    input wire en,
    input wire reset,
    output reg out
);
    always @(posedge clk) begin
        if (en)
            out <= in;
    end
    always @(reset) begin
        if (!reset)
            out <= 0;
    end
endmodule

module dff_en_same (
    input wire clk,
    input wire in,
    input wire en,
    input wire reset,
    output reg out
);
    always @(posedge clk,  negedge reset) begin
        if (en)
            out <= in;
        if (!reset)
            out <= 0;
    end
endmodule
module dff_en_same_2 (
    input wire clk,
    input wire in,
    input wire en,
    input wire reset,
    output reg out
);
    always @(posedge clk,  negedge reset) begin
        if (en)
            out <= in;
        else if (!reset)
            out <= 0;
    end
endmodule


module dff_en_same_3 (
    input wire clk,
    input wire in,
    input wire en,
    input wire reset,
    output reg out
);
    reg out_1;
    always @(posedge clk) begin
        if (en)
            out_1 <= in;
    end
    reg out_2;
    always @(reset) begin
        if (!reset)
            out_2 <= 0;
        else
            out_2 = out_1;
    end
endmodule