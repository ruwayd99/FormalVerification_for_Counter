module bit4counter(clk, reset, counter, overflow);

input clk, reset;
output [3:0] counter;
output reg overflow;

reg [3:0] counter;

always_ff @(posedge clk, posedge reset)
begin
    //set counter and overflow to 0 if reset is 1
    if (reset) begin
        counter <= 0;
        overflow <= 0;
    end
    else begin
        //set overflow to 1 if counter is 15 and set counter back to 0 again
        if (counter == 4'b1111) begin
            counter <= 0;
            overflow <= 1;
        end
        //increment counter by 1 if counter is not 15 and overflow is 0
        else begin
            counter <= counter + 1;
            overflow <= 0;
        end
    end
end

endmodule
