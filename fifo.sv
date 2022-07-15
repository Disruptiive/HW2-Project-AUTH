module fifo #(parameter DATA_WIDTH = 16, FIFO_DEPTH = 16)(
    output logic fifo_full, fifo_empty, [DATA_WIDTH-1:0] fifo_data_out,
    input  logic rst, fifo_write, fifo_read, clk, [DATA_WIDTH-1:0] fifo_data_in);

    logic [$clog2(FIFO_DEPTH)-1:0] wr_ptr,rd_ptr;
    logic [$clog2(FIFO_DEPTH):0] cnt;
    logic [DATA_WIDTH-1:0] regs [0:FIFO_DEPTH-1];
    logic [1:0] state_info;
    
    always_ff @ (posedge clk, negedge rst) 
    begin
        if(!rst) 
        begin
            wr_ptr <= 0;
            rd_ptr <= 0;
            cnt <= 0;
            fifo_full <= 0;
            fifo_empty <= 1;
        end
        else
        begin
            case(state_info)
                2'b11: begin
                        if(cnt >= FIFO_DEPTH)
                        begin
                            fifo_data_out <= regs[rd_ptr];
                            regs[wr_ptr] <= fifo_data_in;
                            rd_ptr <= rd_ptr + 1;
                            wr_ptr <= wr_ptr + 1;
                            
                        end
                        else
                        begin
                            regs[wr_ptr] <= fifo_data_in;
                            fifo_data_out <= regs[rd_ptr];
                            wr_ptr <= wr_ptr + 1;
                            rd_ptr <= rd_ptr + 1;
                        end
                        fifo_empty <= (cnt == 0) ? 1:0;
                        fifo_full  <=  (cnt >= FIFO_DEPTH) ? 1:0;


                end
                2'b01: begin
                        if(cnt == 0) fifo_empty <= 1;
                        else 
                        begin
                            fifo_data_out <= regs[rd_ptr];
                            rd_ptr <= rd_ptr + 1;
                            cnt <= cnt - 1;
                            fifo_empty <= (cnt-1 == 0) ? 1:0;
                            fifo_full <= 0;
                        end
                        
                end 
                2'b10: begin
                        if(cnt >= FIFO_DEPTH) fifo_full  <= 1;
                        else
                        begin
                            regs[wr_ptr] <= fifo_data_in;
                            wr_ptr <= wr_ptr + 1;
                            cnt <= cnt + 1;
                            fifo_full  <=  (cnt+1 >= FIFO_DEPTH) ? 1:0;
                            fifo_empty <= 0;
                        end
                end
                default: continue;
            endcase
        end
    end

    always_comb begin : set_state
        state_info = {fifo_write,fifo_read};
    end 

endmodule