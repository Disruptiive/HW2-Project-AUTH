module counter_test;
bit  sys_rst, sys_ld_cnt, sys_updn_cnt, sys_count_enb, sys_clk;
bit [15:0] sys_data_in;
wire [15:0] sys_data_out;

counter counter1 (.data_out(sys_data_out), .data_in(sys_data_in), .rst(sys_rst), .ld_cnt(sys_ld_cnt), .updn_cnt(sys_updn_cnt), .count_enb(sys_count_enb), .clk(sys_clk));

bind counter counter_property counterbound(.pdata_out(data_out), .pdata_in(data_in), .prst(rst), .pld_cnt(ld_cnt), .pupdn_cnt(updn_cnt), .pcount_enb(count_enb), .pclk(clk));

always @(posedge sys_clk)
    $display($stime,,,"clk=%b data_in=%b data_out=%b,rst=%b,ld_cnt=%b,updn_cnt=%b,count_enb=%b",sys_clk,sys_data_in,sys_data_out,sys_rst,sys_ld_cnt,sys_updn_cnt,sys_count_enb,sys_clk);

always #10 sys_clk = !sys_clk; 

initial
begin
    sys_data_in = 16'd4;
    sys_rst = 1'b0;
    sys_ld_cnt = 1'b1;
    sys_updn_cnt = 1'b0;
    sys_count_enb = 1'b0;
    #2;   sys_rst = 1'b1;
    #5;   sys_ld_cnt = 1'b0;
    #10;  sys_ld_cnt = 1'b1; sys_updn_cnt = 1'b1;
    #10;  sys_count_enb = 1'b1;
    #2;   sys_rst = 1'b0; 
    #5;   sys_rst = 1'b1; sys_data_in = 16'd20; sys_ld_cnt = 1'b0;
    #20;  sys_ld_cnt = 1'b1; sys_count_enb = 1'b0; 
    #10;  sys_count_enb = 1'b1; sys_updn_cnt = 1'b1;
    #30;  sys_updn_cnt = 1'b0;
    #50;  sys_count_enb = 1'b0;
    #30;  sys_updn_cnt = 1'b1;
    #10;  sys_count_enb = 1'b1;
end
endmodule