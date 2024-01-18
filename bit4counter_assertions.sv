/* File name: bit4counter_assertions.sv */
module bit4counter_assertions (
  input clk,
  input reset,
  output reg [3:0] counter,
  output reg overflow
);

  // Property declarations

  // Property to check if reset resets the counter
  property p_reset;
  @(posedge clk)
  reset |-> ##1 (counter == 4'b0000 && overflow == 0);
  endproperty

  // Property to check if the counter increments by 1
  property p_increment;
  @(posedge clk)
  (!reset && $past(counter) != 4'b1111) |-> ##1 (counter == $past(counter) + 4'b0001 && overflow == 0);
endproperty

  // Property to check if the counter overflows
  property p_overflow;
  @(posedge clk)
  (!reset && $past(counter) == 4'b1111) |-> ##1 (counter == 4'b0000 && overflow == 1);
endproperty
  
  // Assertion block to check the properties
  initial begin
    // Apply the properties in simulation
    assert property (p_counter) else $fatal("Assertion reset_resets_counter failed");
      assert property (p_property) else $fatal("Assertion combined_property failed");
      assert property (p_overflow) else $fatal("Assertion counter_overflow failed");
  end

endmodule: bit4counter_assertions
