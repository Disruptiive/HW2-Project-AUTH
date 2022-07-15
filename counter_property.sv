module counter_property (
input prst, pld_cnt, pupdn_cnt, pcount_enb, pclk, [15:0] pdata_out, [15:0] pdata_in 
);

`ifdef reset
property pr1;
    @(negedge prst) 1'b1  |-> @(posedge pclk) pdata_out == 16'd0;
endproperty

prstPdataOut: assert property (pr1) $display($stime,,,"\t\t %m Assertion1: PASS");
                               else $display($stime,,,"\t\t %m Assertion1: FAIL"); 
`elsif count_stable
property pr2;
    @(posedge pclk) disable iff(!prst) (pld_cnt && !pcount_enb) |-> @(negedge pclk) $stable(pdata_out);
endproperty
pLdCountDataOut: assert property (pr2) $display($stime,,,"\t\t %m Assertion1: PASS");
                                  else $display($stime,,,"\t\t %m Assertion1: FAIL"); 

`elsif count_updown                   
property pr3;
    @(posedge pclk) disable iff(!prst) (pld_cnt && pcount_enb) |-> @(negedge pclk) ($past(pupdn_cnt)) ? (pdata_out == $past(pdata_out) + 16'd1) : (pdata_out == $past(pdata_out) - 16'd1);
endproperty


pLdCountDataOut2: assert property (pr3) $display($stime,,,"\t\t %m Assertion1: PASS");
                                  else $display($stime,,,"\t\t %m Assertion1: FAIL" ); 

`endif 
endmodule

