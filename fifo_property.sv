module fifo_property #(parameter DATA_WIDTH = 16, FIFO_DEPTH = 16)(
    input prst, pfifo_write, pfifo_read, pclk, pfifo_full, pfifo_empty, [DATA_WIDTH-1:0] pfifo_data_in, [DATA_WIDTH-1:0] pfifo_data_out, [$clog2(FIFO_DEPTH):0] pcnt, [$clog2(FIFO_DEPTH)-1:0] pwr_ptr, [$clog2(FIFO_DEPTH)-1:0] prd_ptr
);

`ifdef reset
property pr1;
    @(negedge prst) 1'b1  |-> @(posedge pclk) (!pfifo_full && pfifo_empty && pcnt == 0);
endproperty
prstFifoFullEmpty: assert property (pr1) $display($stime,,,"\t\t %m Assertion1: PASS");
                                    else $display($stime,,,"\t\t %m Assertion1: FAIL"); 

`elsif empty_full
property pr1;
    @(posedge pclk) disable iff(!prst) pcnt == 0 |-> pfifo_empty == 1;
endproperty

property pr2;
    @(posedge pclk) disable iff(!prst) pcnt >= FIFO_DEPTH |->  pfifo_full == 1;
endproperty

pcntFifoEmpty: assert property (pr1) $display($stime,,,"\t\t %m Assertion1: PASS");
                                else $display($stime,,,"\t\t %m Assertion1: FAIL"); 

pcntFifoFull: assert property (pr2) $display($stime,,,"\t\t %m Assertion2: PASS");
                               else $display($stime,,,"\t\t %m Assertion2: FAIL"); 

`elsif read_write_invalid

property pr1;
    @(posedge pclk) disable iff(!prst) ((pcnt >= FIFO_DEPTH) && pfifo_write && !pfifo_read) |-> @(negedge pclk) $stable(pwr_ptr);
endproperty

property pr2;
   @(posedge pclk) disable iff(!prst)  ((pcnt == 0) && !pfifo_write && pfifo_read) |-> @(negedge pclk) $stable(prd_ptr);
endproperty

pwriteFull: assert property (pr1) $display($stime,,,"\t\t %m Assertion1: PASS");
                             else $display($stime,,,"\t\t %m Assertion1: FAIL"); 

preadEmpty: assert property (pr2) $display($stime,,,"\t\t %m Assertion2: PASS");
                             else $display($stime,,,"\t\t %m Assertion2: FAIL"); 
`endif 

endmodule