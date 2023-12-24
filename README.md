# Formal Verification for 4 bit counter with overflow

This repository contains system verilog files for a counter, for the assertions to verify the module and a top module that combines everything. I will explain every file one by one

# 4-Bit Counter with Overflow (counter.sv)

## Overview

The `bit4counter` module is a 4-bit counter with an overflow signal. It increments its count on each rising edge of the clock (`clk`) signal, except when a reset (`reset`) signal is asserted. The counter resets to zero when the reset signal is active. When the counter reaches its maximum value (15 in 4-bit representation), it triggers an overflow condition, and the counter is reset to zero.

## Module Interface

### Inputs

- `clk`: Clock signal (positive edge-triggered).
- `reset`: Reset signal. When asserted, the counter is reset to zero.
  
### Outputs

- `counter`: 4-bit output representing the counter value.
- `overflow`: Overflow signal. It is asserted when the counter reaches its maximum value.

## Behavior

The behavior of the `bit4counter` module can be summarized as follows:

1. **Reset Operation:**
   - When the `reset` signal is asserted (`reset == 1`), the counter is set to zero, and the overflow signal is de-asserted.

2. **Increment Operation:**
   - On each rising edge of the clock signal (`clk`), the counter is incremented by one, but only if the reset signal is not asserted.
   
3. **Overflow Condition:**
   - When the counter reaches its maximum value (15 in 4-bit representation), the overflow signal is asserted, and the counter is reset to zero in the next clock cycle.

# Assertions for 4-Bit Counter with Overflow (bit4counter_assertions.sv)

## Overview

The `bit4counter_assertions` module contains assertions to formally verify the behavior of the 4-bit counter with overflow (`bit4counter`) module. It includes properties that check the reset operation, counter incrementation, and overflow conditions.

## Module Interface

### Inputs

- `clk`: Clock signal (positive edge-triggered).
- `reset`: Reset signal.
  
### Outputs

- `counter`: 4-bit output representing the counter value.
- `overflow`: Overflow signal.

## Assertions

### 1. Reset Resets Counter

```verilog
property reset_resets_counter;
  @(posedge clk) disable iff (!reset)
  counter == 4'b0000;
endproperty
A1: assert property (reset_resets_counter) else $fatal("Assertion reset_resets_counter failed");
```
### 2. Counter Incrementation and Overflow
```verilog
property combined_property;
  @(posedge clk) disable iff (reset || counter == 4'b1111)
  (
    counter == $past(counter) + 1 &&
    overflow == 0
  );
endproperty
A2: assert property (combined_property) else $fatal("Assertion combined_property failed");
```
### 2. Counter Overflow
```verilog
property counter_overflow;
  @(posedge clk) disable iff (reset || counter != 4'b1111)
  overflow == 1;
endproperty
A3: assert property (counter_overflow) else $fatal("Assertion counter_overflow failed");
```

# Testbench for 4-Bit Counter with Overflow (tb_top)

## Overview

The `tb_top` module serves as the testbench for the 4-bit counter with overflow (`bit4counter`) module. It instantiates the `bit4counter` module and provides inputs to observe its behavior. Additionally, it binds the `bit4counter_assertions` module to perform formal verification of the counter.

## Module Interface

### Inputs

- `clk`: Clock signal.
- `reset`: Reset signal.

### Outputs

- `counter`: 4-bit output representing the counter value.
- `overflow`: Overflow signal.

## Testbench Structure

The testbench consists of the following components:

1. **Clock and Reset Signals:**
   - `clk`: Clock signal.
   - `reset`: Reset signal.

2. **Counter Module Instantiation:**
   - `bit4counter_inst`: Instantiation of the 4-bit counter module (`bit4counter`).
     - Inputs:
       - `clk`: Clock signal.
       - `reset`: Reset signal.
     - Outputs:
       - `counter`: 4-bit counter output.
       - `overflow`: Overflow signal.

3. **Binding for Formal Verification:**
   - The `bit4counter_assertions` module is bound to the `bit4counter` instance (`DUT`) to perform formal verification.
