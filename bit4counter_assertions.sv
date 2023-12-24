/* File name: bit4counter_assertions.sv */
module bit4counter_assertions (
  input clk,
  input reset,
  output reg [3:0] counter,
  output reg overflow
);

  // Property declarations

  // Property to check if reset resets the counter
  property reset_resets_counter;
    @(posedge clk) disable iff (!reset)
    counter == 4'b0000;
  endproperty

  // Property to check if the counter increments by 1
  property combined_property;
  @(posedge clk) disable iff (reset || counter == 4'b1111)
  (
    counter == $past(counter) + 1 &&
    overflow == 0
  );
  endproperty

  // Property to check if the counter overflows
  property counter_overflow;
    @(posedge clk) disable iff (reset || counter != 4'b1111)
    overflow == 1;
  endproperty

  // Assertion block to check the properties
  initial begin
    // Apply the properties in simulation
    assert property (reset_resets_counter) else $fatal("Assertion reset_resets_counter failed");
    assert property (combined_property) else $fatal("Assertion combined_property failed");
    assert property (counter_overflow) else $fatal("Assertion counter_overflow failed");
  end

endmodule: bit4counter_assertions
