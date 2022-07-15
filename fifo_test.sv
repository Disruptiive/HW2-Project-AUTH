module fifo_test;

bit sys_fifo_full, sys_fifo_empty, sys_rst, sys_fifo_write, sys_fifo_read, sys_clk;
bit [15:0] sys_fifo_data_out, sys_fifo_data_in;

fifo #(16,16) fifo1 (.rst(sys_rst),.fifo_write(sys_fifo_write),.fifo_read(sys_fifo_read),.clk(sys_clk),.fifo_data_in(sys_fifo_data_in),.fifo_full(sys_fifo_full),.fifo_empty(sys_fifo_empty),.fifo_data_out(sys_fifo_data_out));

bind fifo fifo_property #(16,16) fifobound (.prst(rst), .pfifo_write(fifo_write), .pfifo_read(fifo_read), .pclk(clk), .pfifo_full(fifo_full), .pfifo_empty(fifo_empty), .pfifo_data_in(fifo_data_in), .pfifo_data_out(fifo_data_out), .pcnt(fifo.cnt), .pwr_ptr(fifo.wr_ptr), .prd_ptr(fifo.rd_ptr));

always #10 sys_clk = !sys_clk; 

initial
begin
    sys_rst = 1'b0;
    #5;  sys_fifo_data_in = 16'd10;
    #10; sys_rst = 1'b1; sys_fifo_read = 1'b1;
    #25; sys_fifo_read = 1'b0; sys_fifo_write = 1'b1;
    #10; sys_fifo_data_in = 16'd435;
    #15; sys_fifo_data_in = 16'd90;
    #20; sys_fifo_data_in = 16'd435;
    #20; sys_fifo_data_in = 16'd45;
    #20; sys_fifo_data_in = 16'd5;
    #20; sys_fifo_data_in = 16'd4435;
    #20; sys_fifo_data_in = 16'd1335;
    #20; sys_fifo_data_in = 16'd45535;
    #20; sys_fifo_data_in = 16'd5;
    #20; sys_fifo_data_in = 16'd0;
    #20; sys_fifo_data_in = 16'd10;
    #20; sys_fifo_data_in = 16'd100;
    #20; sys_fifo_data_in = 16'd2324;
    #20; sys_fifo_data_in = 16'd556;
    #20; sys_fifo_data_in = 16'd1415;
    #20; sys_fifo_data_in = 16'd20;
    #20; sys_fifo_data_in = 16'd0;
    #15; sys_fifo_read = 1'b1; 
    #20; sys_fifo_write = 1'b0;

    #200; sys_fifo_write = 1'b1;

    #20; sys_fifo_write = 1'b0;
    #40; sys_rst = 1'b0;
    #15; sys_rst = 1'b1;
end
endmodule