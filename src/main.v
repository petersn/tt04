// snprocessor

`define WORD_SIZE 16
`define MAIN_MEMORY_SIZE 64
`define ADDRESS_SIZE 10
`define REGISTER_COUNT 16
`define LOG_REG_COUNT 4

`define ERROR_CODE_INVALID_INSTRUCTION           4'd1
`define ERROR_CODE_INVALID_UNARY_OP              4'd2
`define ERROR_CODE_INVALID_SYSTEM_REGISTER_READ  4'd3
`define ERROR_CODE_INVALID_SYSTEM_REGISTER_WRITE 4'd4


module snproc(
  input wire clock,
  input wire assert_control_mode,
  input wire control_mode_execute,
  input wire control_mode_clock,
  input wire control_mode_data_in,
  output wire control_mode_data_out,
  // For communication with the user process we have two bits, setting the buffer states.
  output wire msg_to_snproc_full,
  output wire msg_from_snproc_available,
  output wire error_occurred

  /*
  input wire [`WORD_SIZE - 1 : 0] mem_reset_mode_bus_write,
  output wire [`WORD_SIZE - 1 : 0] mem_reset_mode_bus_read,
  output wire [`ADDRESS_SIZE - 1 : 0] mem_reset_mode_address,
  input wire reset_mode_zero_addr,
  input wire reset_mode_write_enable,
  input wire [`WORD_SIZE - 1 : 0] comm_reg_in,
  output wire [`WORD_SIZE - 1 : 0] comm_reg_out,
  output wire [20 : 0] error_code_wires
  */
);
  //wire internal_clock;
  //assign internal_clock = assert_control_mode ? control_mode_clock : clock;

  // Debugging information.
  reg error_occurred_state;
  reg [19:0] error_code;
  reg [`ADDRESS_SIZE - 1 : 0] error_instruction_pointer;
  assign error_occurred = error_occurred_state;
  //assign error_code_wires = {error_occurred, error_code};

  always @(posedge clock) begin
    // FIXME: Do replace.
    /*
    if (reset) begin
        error_occurred <= 0;
        error_code <= 0;
        error_instruction_pointer <= 0;
    end
    */
  end

  `define REPORT_ERROR(code) \
    error_occurred_state <= 1; \
    error_instruction_pointer <= `INST_PTR; \
    error_code <= {code, instruction_read};

  // Instruction pointer.
  //`define INST_PTR ip
  //reg [`ADDRESS_SIZE - 1 : 0] ip;
  `define INST_PTR register_file[15]

  reg [`WORD_SIZE - 1 : 0] comm_reg_in;
  reg comm_reg_in_full;
  reg [`WORD_SIZE - 1 : 0] comm_reg_out;
  reg comm_reg_out_full;

  assign msg_to_snproc_full = comm_reg_in_full;
  assign msg_from_snproc_available = comm_reg_out_full;

  // Main memory.
  reg [`WORD_SIZE - 1 : 0] main_memory[`MAIN_MEMORY_SIZE];
  reg [`WORD_SIZE - 1 : 0] mem_bus_read;
  reg [`WORD_SIZE - 1 : 0] mem_bus_write;
  reg [`WORD_SIZE - 1 : 0] instruction_read;
  //reg [`WORD_SIZE - 1 : 0] mem_reset_mode_bus_write;
  reg [`ADDRESS_SIZE - 1 : 0] mem_index_read;
  reg [`ADDRESS_SIZE - 1 : 0] mem_index_write;
  reg mem_write_enable;

  always @(posedge clock) begin
    if (mem_write_enable) begin
      main_memory[in_control_mode ? control_mode_mem_address : mem_index_write] <= mem_bus_write;
    end
    mem_bus_read <= main_memory[in_control_mode ? control_mode_mem_address : mem_index_read];
    instruction_read <= main_memory[`INST_PTR];
  end

  // Register file.
  reg [`WORD_SIZE - 1 : 0] register_file[`REGISTER_COUNT];
  /*
  reg [`WORD_SIZE - 1 : 0] reg_bus_a;
  reg [`WORD_SIZE - 1 : 0] reg_bus_b;
  reg [`WORD_SIZE - 1 : 0] reg_bus_w;
  reg [`LOG_REG_COUNT - 1 : 0] reg_index_a;
  reg [`LOG_REG_COUNT - 1 : 0] reg_index_b;
  reg [`LOG_REG_COUNT - 1 : 0] reg_index_w;
  reg reg_write_enable;

  always @(posedge clock) begin
    if (reg_write_enable) begin
      register_file[reg_index_w] <= reg_bus_w;
    end
    reg_bus_a <= register_file[reg_index_a];
    reg_bus_b <= register_file[reg_index_b];
  end
  */

  reg [23:0] control_mode_shift_register_in;
  reg [23:0] control_mode_shift_register_out;
  reg [`ADDRESS_SIZE - 1 : 0] control_mode_mem_address;
  reg [`WORD_SIZE - 1 : 0] mem_control_mode_bus_write;
  assign control_mode_data_out = control_mode_shift_register_out[0];

  wire [`LOG_REG_COUNT - 1 : 0] regA;
  wire [`LOG_REG_COUNT - 1 : 0] regB;
  wire [`LOG_REG_COUNT - 1 : 0] regC;
  wire [7:0] immediate_operand;
  assign regA = instruction_read[7:4];
  assign regB = instruction_read[11:8];
  assign regC = instruction_read[15:12];
  assign immediate_operand = instruction_read[15:8];

  reg deferred_load;
  reg [`LOG_REG_COUNT - 1 : 0] deferred_load_register;
  reg [47:0] clock_counter;
  reg flag_zero;
  reg flag_carry;
  reg flag_overflow;
  reg flag_sign;

  // These are supposed to get no flip-flops, and should be implemented as wires.
  reg condition_result;
  reg[`WORD_SIZE - 1 : 0] compare_subtract;

  reg in_control_mode;
  reg do_single_step;
  reg single_step_trapped;

  reg prev_control_mode_clock;
  wire control_mode_clock_rising_edge;
  assign control_mode_clock_rising_edge = control_mode_clock & ~prev_control_mode_clock;

  always @(posedge clock) begin
    mem_write_enable <= 0;
    prev_control_mode_clock <= control_mode_clock;
    in_control_mode <= assert_control_mode;

    // Implement control mode.
    if (in_control_mode) begin
      if (control_mode_clock_rising_edge) begin
        $display("Control mode: in=%b out=%b exec=%b", control_mode_shift_register_in, control_mode_shift_register_out, control_mode_execute);
        control_mode_shift_register_in <= {control_mode_data_in, control_mode_shift_register_in[23:1]};
        control_mode_shift_register_out <= {1'b0, control_mode_shift_register_out[23:1]};

        if (control_mode_execute) begin
          case (control_mode_shift_register_in[3:0])
            // Test constant.
            4'd0: begin
              $display("%c[92m  CONTROL: Test constant%c[0m", 27, 27);
              control_mode_shift_register_out <= 24'b101001011000000001111011;
            end
            // Read the error code and associated information.
            4'd1: begin
              $display("%c[92m  CONTROL: Read error%c[0m", 27, 27);
              control_mode_shift_register_out <= {4'b11, do_single_step, single_step_trapped, error_code};
            end
            // Read the error instruction pointer.
            4'd2: begin
              $display("%c[92m  CONTROL: Read error IP%c[0m", 27, 27);
              // FIXME: ADDRESS_SIZE
              control_mode_shift_register_out <= {14'b11010101000000, error_instruction_pointer};
            end
            // Read a register.
            4'd3: begin
              $display("%c[92m  CONTROL: Read reg%c[0m", 27, 27);
              control_mode_shift_register_out <= {8'b11111000, register_file[control_mode_shift_register_in[7:4]]};
            end
            // Write a register.
            4'd4: begin
              $display("%c[92m  CONTROL: Write reg%c[0m", 27, 27);
              register_file[control_mode_shift_register_in[7:4]] <= control_mode_shift_register_in[23:8];
              //control_mode_shift_register_out <= register_file[control_mode_shift_register_in[7:4]];
            end
            // Reset chip.
            4'd5: begin
              $display("%c[92m  CONTROL: Reset chip%c[0m", 27, 27);
              error_occurred_state <= 0;
              error_code <= 0;
              error_instruction_pointer <= 0;
              clock_counter <= 0;
              deferred_load <= 0;
              deferred_load_register <= 0;
              do_single_step <= 0;
              single_step_trapped <= 0;
              `INST_PTR <= 0;
              control_mode_shift_register_out <= 24'b111010101010101010101011;
            end
            // Read clock counter low.
            4'd6: begin
              $display("%c[92m  CONTROL: Read clock counter low%c[0m", 27, 27);
              control_mode_shift_register_out <= clock_counter[23:0];
            end
            // Read clock counter high.
            4'd7: begin
              $display("%c[92m  CONTROL: Read clock counter high%c[0m", 27, 27);
              control_mode_shift_register_out <= clock_counter[47:24];
            end

            // Set memory adjust address.
            4'd8: begin
              $display("%c[92m  CONTROL: Set mem adjust address%c[0m", 27, 27);
              // FIXME: ADDRESS_SIZE
              control_mode_mem_address <= control_mode_shift_register_in[13:4];
            end
            // Write to memory.
            4'd9: begin
              $display("%c[92m  CONTROL: Poke%c[0m", 27, 27);
              mem_bus_write <= control_mode_shift_register_in[23:8];
              mem_write_enable <= 1;
              //control_mode_mem_address <= control_mode_mem_address + control_mode_shift_register_in[5];
            end
            // Read from memory.
            4'd10: begin
              $display("%c[92m  CONTROL: Peek%c[0m", 27, 27);
              control_mode_shift_register_out <= {8'b11111110, mem_bus_read};
            end
            // Enable single stepping.
            4'd11: begin
              $display("%c[92m  CONTROL: Enable single-stepping%c[0m", 27, 27);
              do_single_step <= 1;
              single_step_trapped <= 0;
            end
            // Disable single stepping.
            4'd12: begin
              $display("%c[92m  CONTROL: Disable single-stepping%c[0m", 27, 27);
              do_single_step <= 0;
              single_step_trapped <= 0;
            end

            // Send message in.
            4'd13: begin
              $display("%c[92m  CONTROL: Send message to snproc%c[0m", 27, 27);
              comm_reg_in <= control_mode_shift_register_in[23:8];
              comm_reg_in_full <= 1;
            end

            // Read message out
            4'd14: begin
              $display("%c[92m  CONTROL: Read message from snproc%c[0m", 27, 27);
              control_mode_shift_register_out <= {8'b10000010, comm_reg_out};
              comm_reg_out_full <= 0;
            end

            default: begin
              control_mode_shift_register_out <= 24'b111111111111111111111111;
            end
          endcase
        end
      end
    end else if ((!error_occurred_state) && (!single_step_trapped)) begin
      // Implement logic to execute the core program.
      //$display("%c[91m  ---  [ip =%d] Got to execution%c[0m", 27, `INST_PTR, 27);
      clock_counter <= clock_counter + 1;
      `INST_PTR <= `INST_PTR + 1;

      mem_write_enable <= 0;
      deferred_load <= 0;

      if (do_single_step) begin
        single_step_trapped <= 1;
      end

      if (deferred_load) begin
        register_file[deferred_load_register] <= mem_bus_read;
      end

      //$display("%c[92mInstruction: %b%c[0m", 27, instruction_read[7:0], 27);

      case (instruction_read[3:0])
        4'b0000: begin
          $display("%c[91m  ---  [ip =%d] No-op%c[0m", 27, `INST_PTR, 27);
        end

        // Unary operations.
        4'b0001: begin
          case (regA)
            4'b0000: begin
              $display("%c[91m  ---  [ip =%d] Move: r[%d] = r[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= register_file[regC];
            end
            4'b0001: begin
              $display("%c[91m  ---  [ip =%d] Inc: r[%d] = r[%d] + 1%c[0m", 27, `INST_PTR, regB, regC, 27);
              if (register_file[regC][10:0] == 0) begin
                  $display("%c[91m  ---  [ip =%d] Inc: r[%d] = r[%d] + 1 (val = %d)%c[0m", 27, `INST_PTR, regB, regC, register_file[regC], 27);
              end
              register_file[regB] <= register_file[regC] + 1;
            end
            4'b0010: begin
              $display("%c[91m  ---  [ip =%d] Dec: r[%d] = r[%d] - 1%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= register_file[regC] - 1;
            end
            4'b0011: begin
              $display("%c[91m  ---  [ip =%d] Neg: r[%d] = -r[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= -register_file[regC];
            end
            4'b0100, 4'b0110: begin
              $display("%c[91m  ---  [ip =%d] Push: mem[r[%d]--] = r[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              mem_index_write <= register_file[regB];
              mem_write_enable <= 1;
              mem_bus_write <= register_file[regC];
              register_file[regB] <= register_file[regB] + (regA[1] ? 1 : -1);
            end
            4'b0101, 4'b0111: begin
              $display("%c[91m  ---  [ip =%d] Pop: r[%d] = mem[++r[%d]]%c[0m", 27, `INST_PTR, regB, regC, 27);
              mem_index_read <= register_file[regB] + (regA[1] ? -1 : +1);
              deferred_load <= 1;
              deferred_load_register <= regC;
              register_file[regB] <= register_file[regB] + (regA[1] ? -1 : +1);
            end
            4'b1000: begin
              $display("%c[91m  ---  [ip =%d] Take low: r[%d] = r[%d] & 0xff%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= {8'b00000000, register_file[regC][7:0]};
            end
            4'b1001: begin
              $display("%c[91m  ---  [ip =%d] Take high: r[%d] = (r[%d] >> 8) & 0xff%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= {8'b00000000, register_file[regC][15:8]};
            end

            // Read system register.
            4'b1010: begin
              $display("%c[91m  ---  [ip =%d] Read system reg: r[%d] = sys[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              case (regC)
                // Read flags register.
                4'b0000: register_file[regB] <= {12'b0000_0000_0000, flag_zero, flag_carry, flag_overflow, flag_sign};
                4'b0001: register_file[regB] <= clock_counter[15:0];
                4'b0010: begin
                  register_file[regB] <= comm_reg_in;
                  comm_reg_in_full <= 0;
                end
                4'b0011: register_file[regB] <= {15'd0, comm_reg_in_full};
                4'b0100: register_file[regB] <= {15'd0, comm_reg_out_full};
                default: begin
                  `REPORT_ERROR(`ERROR_CODE_INVALID_SYSTEM_REGISTER_READ)
                end
              endcase
            end

            // Write system register.
            4'b1011: begin
              $display("%c[91m  ---  [ip =%d] Write system reg: r[%d] = sys[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              case (regC)
                // Write flags register.
                4'b0000: begin
                  flag_sign     <= register_file[regB][0];
                  flag_overflow <= register_file[regB][1];
                  flag_carry    <= register_file[regB][2];
                  flag_zero     <= register_file[regB][3];
                end
                4'b0010: begin
                  comm_reg_out <= register_file[regB];
                  comm_reg_out_full <= 1;
                end
                default: begin
                  `REPORT_ERROR(`ERROR_CODE_INVALID_SYSTEM_REGISTER_WRITE)
                end
              endcase
            end

            4'b1100: begin
              $display("%c[91m  ---  [ip =%d] Booleanize: r[%d] = !!r[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              register_file[regB] <= register_file[regC] == 0 ? 0 : 1;
            end

            4'b1101: begin
              $display("%c[91m  ---  [ip =%d] Compare: r[%d] with r[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              compare_subtract = register_file[regB] - register_file[regC];
              flag_sign <= compare_subtract[15];
              flag_overflow <= register_file[regB][15] != compare_subtract[15];
              flag_carry <= register_file[regC] > register_file[regB];
              flag_zero <= register_file[regB] == register_file[regC];
            end

            //4'b0011: begin

            /*
            // Load simple constant.
            4'b1111: begin
              $display("%c[91m  ---  [ip =%d] Const: r[%d] = constants[%d]%c[0m", 27, `INST_PTR, regB, regC, 27);
              case (regC)
                4'b0000: register_file[regB] <=  0;
                4'b0001: register_file[regB] <=  1;
                4'b0010: register_file[regB] <=  2;
                4'b0011: register_file[regB] <=  4;
                4'b0100: register_file[regB] <=  8;
                4'b1001: register_file[regB] <= -1;
                4'b1010: register_file[regB] <= -2;
                4'b1011: register_file[regB] <= -4;
                4'b1100: register_file[regB] <= -8;
                default: begin
                  `REPORT_ERROR(ERROR_CODE_CONSTANT)
                end
              endcase
            end
            */

            default: begin
              `REPORT_ERROR(`ERROR_CODE_INVALID_UNARY_OP)
            end
          endcase
        end

        // Load zero or sign extended immediate.
        4'b0010, 4'b0011: begin
          if (instruction_read[0]) begin
            $display("%c[91m  ---  [ip =%d] Load sign-extended immediate: r[%d] = extend(%d)%c[0m", 27, `INST_PTR, regA, immediate_operand, 27);
            register_file[regA] <= {{8{immediate_operand[7]}}, immediate_operand};
          end else begin
            $display("%c[91m  ---  [ip =%d] Load immediate: r[%d] = %d%c[0m", 27, `INST_PTR, regA, immediate_operand, 27);
            register_file[regA] <= {8'd0, immediate_operand};
          end
        end
        // Load absolute.
        4'b0100: begin
          $display("%c[91m  ---  [ip =%d] Load absolute: r[%d] = mem[%d]%c[0m", 27, `INST_PTR, regA, immediate_operand, 27);
          mem_index_read <= instruction_read[15:4];
          deferred_load <= 1;
          deferred_load_register <= 0;
        end

        // Store absolute.
        4'b0101: begin
          $display("%c[91m  ---  [ip =%d] Store absolute: mem[%d] = r[%d]%c[0m", 27, `INST_PTR, immediate_operand, regA, 27);
          mem_index_write <= instruction_read[15:4];
          mem_write_enable <= 1;
          mem_bus_write <= register_file[0];
        end

        // Load.
        4'b0110: begin
          $display("%c[91m  ---  [ip =%d] Load: r[%d] = mem[r[%d] + %d]%c[0m", 27, `INST_PTR, regA, regB, regC + 1, 27);
          mem_index_read <= register_file[regB] + {{12{regC[3]}}, regC} + 1;
          deferred_load <= 1;
          deferred_load_register <= regA;
        end

        // Store.
        4'b0111: begin
          $display("%c[91m  ---  [ip =%d] Store: mem[r[%d] + %d] = r[%d]%c[0m", 27, `INST_PTR, regB, regC + 1, regA, 27);
          mem_index_write <= register_file[regB] + {{12{regC[3]}}, regC} + 1;
          mem_write_enable <= 1;
          mem_bus_write <= register_file[regA];
        end

        /*
        4'b0101: begin
          $display("%c[91m  ---  [ip =%d] Sub: r[%d] = r[%d] - r[%d]%c[0m", 27, `INST_PTR, regA, regB, regC, 27);
          register_file[regA] <= register_file[regB] - register_file[regC];
        end

        4'b0110: begin
          $display("%c[91m  ---  [ip =%d] And: r[%d] = r[%d] & r[%d]%c[0m", 27, `INST_PTR, regA, regB, regC, 27);
          register_file[regA] <= register_file[regB] & register_file[regC];
        end

        4'b0111: begin
          $display("%c[91m  ---  [ip =%d] Or: r[%d] = r[%d] | r[%d]%c[0m", 27, `INST_PTR, regA, regB, regC, 27);
          register_file[regA] <= register_file[regB] & register_file[regC];
        end
        */

        // Unconditional IP-relative jump.
        4'b1000: begin
          $display("%c[91m  ---  [ip =%d] Jump: ip=%0d%c[0m", 27, `INST_PTR, instruction_read[15:4], 27);
          `INST_PTR <= `INST_PTR + {{4{instruction_read[15]}}, instruction_read[15:4]};
        end
        // Conditional small IP-relative jump.
        4'b1001: begin
          $display("%c[91m  ---  [ip =%d] Cond jump: cond=%0d ip=%0d%c[0m",
            27, `INST_PTR, regA, instruction_read[15:8], 27
          );
          //*
          case (regA[2:0])
            // Jump if equal
            3'b000: condition_result = flag_sign;
            3'b001: condition_result = flag_overflow;
            3'b010: condition_result = flag_carry; // Jump if above
            3'b011: condition_result = flag_zero;
            //// Jump if not equal
            //4'b0001: condition_result = ~flag_zero;

            // Jump if above
            3'b100: condition_result = (~flag_carry) & (~flag_zero);
            //// Jump if below
            //3'b101: condition_result = flag_carry;

            //// Jump if above or equal
            //4'b0100: condition_result = ~flag_carry;
            //// Jump if below or equal
            //4'b0101: condition_result = flag_carry | flag_zero;

            // Jump if less
            3'b101: condition_result = flag_sign != flag_overflow;
            // Jump if greater
            3'b110: condition_result = (~flag_zero) & (flag_sign == flag_overflow);

            // Constant true.
            3'b111: condition_result = 1;

            //// Jump if less or equal
            //4'b1000: condition_result = flag_zero | (flag_sign != flag_overflow);
            //// Jump if greater or equal
            //4'b1001: condition_result = flag_sign == flag_overflow;
          endcase
          if (condition_result ^ regA[3]) begin
            `INST_PTR <= `INST_PTR + {{8{instruction_read[15]}}, instruction_read[15:8]};
          end
          // */
          /*
          if (flag) begin
            `INST_PTR <= `INST_PTR + {{4{instruction_read[15]}}, instruction_read[15:4]};
          end
          */
        end

        // Two-operand arithmetic
        4'b1010: begin
          case (regA)
            4'b0000: begin
              $display("%c[91m  ---  [ip =%d] Add: r[%d] = r[%d] + r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              {flag_carry, register_file[regB]} <= register_file[regB] + register_file[regC];
            end
            4'b0001: begin
              $display("%c[91m  ---  [ip =%d] Sub: r[%d] = r[%d] - r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              {flag_carry, register_file[regB]} <= register_file[regB] - register_file[regC];
            end
            4'b0010: begin
              $display("%c[91m  ---  [ip =%d] Add-carry: r[%d] = r[%d] + r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              {flag_carry, register_file[regB]} <= register_file[regB] + register_file[regC] + flag_carry;
            end
            4'b0011: begin
              $display("%c[91m  ---  [ip =%d] Sub-carry: r[%d] = r[%d] - r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              {flag_carry, register_file[regB]} <= register_file[regB] - register_file[regC] - flag_carry;
            end
            4'b0100: begin
              $display("%c[91m  ---  [ip =%d] And: r[%d] = r[%d] - r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] & register_file[regC];
            end
            4'b0101: begin
              $display("%c[91m  ---  [ip =%d] Or: r[%d] = r[%d] | r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] | register_file[regC];
            end
            4'b0110: begin
              $display("%c[91m  ---  [ip =%d] Xor: r[%d] = r[%d] ^ r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] ^ register_file[regC];
            end
            4'b0111: begin
              $display("%c[91m  ---  [ip =%d] Assemble word: r[%d] = (r[%d], r[%d])%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= {register_file[regC][7:0], register_file[regB][7:0]};
            end
            4'b1000: begin
              $display("%c[91m  ---  [ip =%d] Shift: r[%d] = r[%d] << r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] << register_file[regC];
            end
            4'b1001: begin
              $display("%c[91m  ---  [ip =%d] Shift: r[%d] = r[%d] >> r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] >> register_file[regC];
            end
            4'b1010: begin
              $display("%c[91m  ---  [ip =%d] Rotate: r[%d] = r[%d] <<< r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= {register_file[regB], register_file[regB]} >> (16 - register_file[regC]);
            end
            4'b1011: begin
              $display("%c[91m  ---  [ip =%d] Rotate: r[%d] = r[%d] >>> r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= {register_file[regB], register_file[regB]} >> register_file[regC];
            end
            4'b1100: begin
              $display("%c[91m  ---  [ip =%d] Shift: r[%d] = r[%d] (signed)>> r[%d]%c[0m", 27, `INST_PTR, regB, regB, regC, 27);
              register_file[regB] <= register_file[regB] >>> register_file[regC];
            end
          endcase
        end

        // sbkh instruction
        4'b1011: begin
          $display("%c[91m  ---  [ip =%d] sbkh: r[%d][15:8] = %d%c[0m", 27, `INST_PTR, regA, immediate_operand, 27);
          register_file[regA] <= {immediate_operand, register_file[regA][7:0]};
        end


        /*
        4'b1110: begin
          $display("%c[91m  ---  [ip =%d] !!! HALT time=%0d !!!%c[0m", 27, `INST_PTR, $time, 27);
          $stop;
        end

        // Debug register state.
        4'b1111: begin
          //DISABLEDISPLAYML::$display("%c[91m  ---  [ip =%d] Debug state: registers=[%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d] mem=[%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h]%c[0m",
          //  27, `INST_PTR,
          //  register_file[ 0], register_file[ 1], register_file[ 2], register_file[ 3],
          //  register_file[ 4], register_file[ 5], register_file[ 6], register_file[ 7],
          //  register_file[ 8], register_file[ 9], register_file[10], register_file[11],
          //  register_file[12], register_file[13], register_file[14], register_file[15],
          //  main_memory[ 0], main_memory[ 1], main_memory[ 2], main_memory[ 3],
          //  main_memory[ 4], main_memory[ 5], main_memory[ 6], main_memory[ 7],
          //  main_memory[ 8], main_memory[ 9], main_memory[10], main_memory[11],
          //  main_memory[12], main_memory[13], main_memory[14], main_memory[15],
          //  27
          //);
        end
        // */

        default: begin
          `REPORT_ERROR(`ERROR_CODE_INVALID_INSTRUCTION)
        end
      endcase
    end
  end

  /*
  always @(posedge clock or posedge reset) begin
    if (reset) begin
      //count <= 0;
      //for (i=0; i<=1024; i=i+1)
      //  save_state[i] <= 0;
      register_file[0] <= 0;
      main_memory[0] <= 0;
      main_memory[1] <= 1;
      $display("Initializing.");
    end
    else begin
      assign ip = register_file[`REGISTER_COUNT - 1];
      assign instruction = main_memory[ip];
      case (instruction[3:0])
        4'b0000: // Move
          register_file[instruction[11:8]] <= register_file[instruction[15:12]];
      endcase
    end
  end
  */

  /*
  initial begin
    $monitor(
      "[t=%5t rst=%d] registers=[%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d %0d] mem=[%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h]",
      $time, reset,
      register_file[ 0], register_file[ 1], register_file[ 2], register_file[ 3],
      register_file[ 4], register_file[ 5], register_file[ 6], register_file[ 7],
      register_file[ 8], register_file[ 9], register_file[10], register_file[11],
      register_file[12], register_file[13], register_file[14], register_file[15],
      main_memory[ 0], main_memory[ 1], main_memory[ 2], main_memory[ 3],
      main_memory[ 4], main_memory[ 5], main_memory[ 6], main_memory[ 7],
      main_memory[ 8], main_memory[ 9], main_memory[10], main_memory[11],
      main_memory[12], main_memory[13], main_memory[14], main_memory[15],
    );
  end
  // */

  always @* begin
    $display(
      "     %c[93m ===== [t=%5d] sign=%d overflow=%d carry=%d zero=%d =====%c[0m", 27, $time, flag_sign, flag_overflow, flag_carry, flag_zero, 27
    );
  end

  always @* begin
    $display(
      "     %c[95m ===== [t=%5d] error=%d code=%x =====%c[0m", 27, $time, error_occurred_state, error_code, 27
    );
  end

endmodule



module tt_um_lfsr (
    input  wire [7:0] ui_in,    // Dedicated inputs - connected to the input switches
    output wire [7:0] uo_out,   // Dedicated outputs - connected to the 7 segment display
    input  wire [7:0] uio_in,   // IOs: Bidirectional Input path
    output wire [7:0] uio_out,  // IOs: Bidirectional Output path
    output wire [7:0] uio_oe,   // IOs: Bidirectional Enable path (active high: 0=input, 1=output)
    input  wire       ena,      // will go high when the design is enabled
    input  wire       clk,      // clock
    input  wire       rst_n     // reset_n - low to reset
);
  // reg [7:0] lfsr;
  // always @(posedge clk) begin
  //   if (!rst_n) begin
  //     lfsr <= 8'b0000_0001;
  //   end else begin
  //     lfsr <= {lfsr[6:0], lfsr[7] ^ lfsr[3] ^ lfsr[2]};
  //   end
  // end

  // input wire clock,
  // input wire assert_control_mode,
  // input wire control_mode_execute,
  // input wire control_mode_clock,
  // input wire control_mode_data_in,
  // output wire control_mode_data_out,
  // // For communication with the user process we have two bits, setting the buffer states.
  // output wire msg_to_snproc_full,
  // output wire msg_from_snproc_available,
  // output wire error_occurred

  snproc snproc (
    .clock(clk),
    .assert_control_mode(ui_in[0]),
    .control_mode_execute(ui_in[1]),
    .control_mode_clock(ui_in[2]),
    .control_mode_data_in(ui_in[3]),
    .control_mode_data_out(uo_out[0]),
    .msg_to_snproc_full(uo_out[1]),
    .msg_from_snproc_available(uo_out[2]),
    .error_occurred(uo_out[3])
  );

  assign uo_out[7:4] = 4'b0000;
  assign uio_out = 8'h00;
  assign uio_oe = 8'h00;
endmodule
