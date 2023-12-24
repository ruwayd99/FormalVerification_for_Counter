/* File name: tb_top.sv */
module tb_top;

  // Inputs and outputs for the counter module
  reg clk;
  reg reset;
  wire [3:0] counter;
  wire overflow;

  // Instantiate the bit4counter module
  bit4counter bit4counter_inst (
    .clk(clk),
    .reset(reset),
    .counter(counter),
    .overflow(overflow)
  );
  
  bind bit4counter bit4counter_assertions DUT(
    .clk(clk),
    .reset(reset),
    .counter(counter),
    .overflow(overflow)
  );

endmodule: tb_top
