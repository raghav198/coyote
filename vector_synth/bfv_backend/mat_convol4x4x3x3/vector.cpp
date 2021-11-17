
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000000000000000001000001000", info);
    add_bitstring(bits, "000000000000001000000000000000000000", info);
    add_bitstring(bits, "000000000000100000000000000000000100", info);
    add_bitstring(bits, "000000000010100010000000010010000110", info);
    add_bitstring(bits, "000000000000000000000001000000000000", info);
    add_bitstring(bits, "000001000000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000010000", info);
    add_bitstring(bits, "000100000000000000000000000000000000", info);
    add_bitstring(bits, "000000000001000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000100000", info);
    add_bitstring(bits, "000000000000000000000010000000000000", info);
    add_bitstring(bits, "000000000000000001000000000000000000", info);
    add_bitstring(bits, "010000000000000000010000000000000000", info);
    add_bitstring(bits, "000000000000100000000000000010000000", info);
    add_bitstring(bits, "001000000000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000100000000000010000", info);
    add_bitstring(bits, "100000110000000100000000100000000000", info);
    add_bitstring(bits, "000000000000010000000000000000000001", info);
    add_bitstring(bits, "000000000000000000000100000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000000100", info);
    add_bitstring(bits, "000010000000000000000000000000000000", info);
    add_bitstring(bits, "000000000100000000001000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000010000000", info);
    add_bitstring(bits, "000000001000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000101000000", info);
    add_bitstring(bits, "000000000000100000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("1111011111000000001111111011111110001111111111111111111011111000111111111000110110000110101111111011", info);
    ts[2] = encrypt_input("111111111011011110111111011010110111111111111110111111111111111111111111110111101111111110110101111011011111111111111011111111101011111110111101111111111101111111110110101111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[38];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -19, gk, ss[0]); // __s0 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -28, gk, ss[2]); // __s2 = __v0 >> 28
    info.eval->rotate_rows(vs[0], -26, gk, ss[3]); // __s3 = __v0 >> 26
    info.eval->rotate_rows(vs[0], -27, gk, ss[4]); // __s4 = __v0 >> 27
    info.eval->rotate_rows(vs[0], -7, gk, ss[5]); // __s5 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -22, gk, ss[6]); // __s6 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -30, gk, ss[7]); // __s7 = __v0 >> 30
    info.eval->rotate_rows(vs[0], -6, gk, ss[8]); // __s8 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -8, gk, ss[9]); // __s9 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -35, gk, ss[10]); // __s10 = __v0 >> 35
    info.eval->rotate_rows(vs[0], -4, gk, ss[11]); // __s11 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -11, gk, ss[12]); // __s12 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -31, gk, ss[13]); // __s13 = __v0 >> 31
    info.eval->rotate_rows(vs[0], -1, gk, ss[14]); // __s14 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -15, gk, ss[15]); // __s15 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -17, gk, ss[16]); // __s16 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -21, gk, ss[17]); // __s17 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -10, gk, ss[18]); // __s18 = __v0 >> 10
    vs[1] = ts[2]; // vector load instr
    
    // __t4 = blend(__s3@100000110000000100000000100000000000, __s0@010000000000000000010000000000000000, __s4@001000000000000000000000000000000000, __s6@000100000000000000000000000000000000, __s1@000010000000000000000000000000000000, __s16@000001000000000000000000000000000000, __s18@000000001000000000000000000000000000, __s17@000000000100000000001000000000000000, __v0@000000000010100010000000010010000110, __s7@000000000001000000000000000000000000, __s15@000000000000010000000000000000000001, __s13@000000000000001000000000000000000000, __s10@000000000000000001000000000000000000, __s5@000000000000000000100000000000010000, __s14@000000000000000000000100000000000000, __s11@000000000000000000000010000000000000, __s8@000000000000000000000001000000000000, __s9@000000000000000000000000001000001000, __s2@000000000000000000000000000101000000, __s12@000000000000000000000000000000100000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9, t4_10, t4_11, t4_12, t4_13, t4_14, t4_15, t4_16, t4_17, t4_18, t4_19, t4_20;
    info.eval->multiply_plain(ss[3], bits["100000110000000100000000100000000000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["010000000000000000010000000000000000"], t4_2);
    info.eval->multiply_plain(ss[4], bits["001000000000000000000000000000000000"], t4_3);
    info.eval->multiply_plain(ss[6], bits["000100000000000000000000000000000000"], t4_4);
    info.eval->multiply_plain(ss[1], bits["000010000000000000000000000000000000"], t4_5);
    info.eval->multiply_plain(ss[16], bits["000001000000000000000000000000000000"], t4_6);
    info.eval->multiply_plain(ss[18], bits["000000001000000000000000000000000000"], t4_7);
    info.eval->multiply_plain(ss[17], bits["000000000100000000001000000000000000"], t4_8);
    info.eval->multiply_plain(vs[0], bits["000000000010100010000000010010000110"], t4_9);
    info.eval->multiply_plain(ss[7], bits["000000000001000000000000000000000000"], t4_10);
    info.eval->multiply_plain(ss[15], bits["000000000000010000000000000000000001"], t4_11);
    info.eval->multiply_plain(ss[13], bits["000000000000001000000000000000000000"], t4_12);
    info.eval->multiply_plain(ss[10], bits["000000000000000001000000000000000000"], t4_13);
    info.eval->multiply_plain(ss[5], bits["000000000000000000100000000000010000"], t4_14);
    info.eval->multiply_plain(ss[14], bits["000000000000000000000100000000000000"], t4_15);
    info.eval->multiply_plain(ss[11], bits["000000000000000000000010000000000000"], t4_16);
    info.eval->multiply_plain(ss[8], bits["000000000000000000000001000000000000"], t4_17);
    info.eval->multiply_plain(ss[9], bits["000000000000000000000000001000001000"], t4_18);
    info.eval->multiply_plain(ss[2], bits["000000000000000000000000000101000000"], t4_19);
    info.eval->multiply_plain(ss[12], bits["000000000000000000000000000000100000"], t4_20);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9, t4_10, t4_11, t4_12, t4_13, t4_14, t4_15, t4_16, t4_17, t4_18, t4_19, t4_20}, ts[4]);
    
    info.eval->multiply(vs[1], ts[4], vs[2]); // __v2 = __v1 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -12, gk, ss[19]); // __s19 = __v2 >> 12
    info.eval->rotate_rows(vs[2], -11, gk, ss[20]); // __s20 = __v2 >> 11
    info.eval->rotate_rows(vs[2], -31, gk, ss[21]); // __s21 = __v2 >> 31
    info.eval->rotate_rows(vs[2], -9, gk, ss[22]); // __s22 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -8, gk, ss[23]); // __s23 = __v2 >> 8
    info.eval->rotate_rows(vs[2], -7, gk, ss[24]); // __s24 = __v2 >> 7
    info.eval->rotate_rows(vs[2], -6, gk, ss[25]); // __s25 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -26, gk, ss[26]); // __s26 = __v2 >> 26
    info.eval->rotate_rows(vs[2], -23, gk, ss[27]); // __s27 = __v2 >> 23
    info.eval->rotate_rows(vs[2], -22, gk, ss[28]); // __s28 = __v2 >> 22
    info.eval->rotate_rows(vs[2], -18, gk, ss[29]); // __s29 = __v2 >> 18
    info.eval->rotate_rows(vs[2], -17, gk, ss[30]); // __s30 = __v2 >> 17
    info.eval->rotate_rows(vs[2], -35, gk, ss[31]); // __s31 = __v2 >> 35
    info.eval->rotate_rows(vs[2], -10, gk, ss[32]); // __s32 = __v2 >> 10
    info.eval->rotate_rows(vs[2], -27, gk, ss[33]); // __s33 = __v2 >> 27
    info.eval->rotate_rows(vs[2], -4, gk, ss[34]); // __s34 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -2, gk, ss[35]); // __s35 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -3, gk, ss[36]); // __s36 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -32, gk, ss[37]); // __s37 = __v2 >> 32
    
    // __t5 = blend(__s24@000000000000100000000000000000000000, __s32@000000000000000000000000000010000000, __s25@000000000000000000000000000000010000, __v2@000000000000000000000000000000000100)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[24], bits["000000000000100000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[32], bits["000000000000000000000000000010000000"], t5_2);
    info.eval->multiply_plain(ss[25], bits["000000000000000000000000000000010000"], t5_3);
    info.eval->multiply_plain(vs[2], bits["000000000000000000000000000000000100"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    
    // __t6 = blend(__s22@000000000000100000000000000000000000, __s23@000000000000000000000000000010000000, __s28@000000000000000000000000000000010000, __s21@000000000000000000000000000000000100)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[22], bits["000000000000100000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[23], bits["000000000000000000000000000010000000"], t6_2);
    info.eval->multiply_plain(ss[28], bits["000000000000000000000000000000010000"], t6_3);
    info.eval->multiply_plain(ss[21], bits["000000000000000000000000000000000100"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    info.eval->add(ts[5], ts[6], vs[3]); // __v3 = __t5 + __t6
    
    // __t7 = blend(__s25@000000000000100000000000000000000100, __v2@000000000000000000000000000010000000, __s23@000000000000000000000000000000010000)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(ss[25], bits["000000000000100000000000000000000100"], t7_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000000000000000010000000"], t7_2);
    info.eval->multiply_plain(ss[23], bits["000000000000000000000000000000010000"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->add(vs[3], ts[7], vs[4]); // __v4 = __v3 + __t7
    
    // __t8 = blend(__s20@000000000000100000000000000000000000, __s37@000000000000000000000000000010000000, __s30@000000000000000000000000000000010000, __s29@000000000000000000000000000000000100)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[20], bits["000000000000100000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[37], bits["000000000000000000000000000010000000"], t8_2);
    info.eval->multiply_plain(ss[30], bits["000000000000000000000000000000010000"], t8_3);
    info.eval->multiply_plain(ss[29], bits["000000000000000000000000000000000100"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    info.eval->add(vs[4], ts[8], vs[5]); // __v5 = __v4 + __t8
    
    // __t9 = blend(__s31@000000000000100000000000000000000000, __s30@000000000000000000000000000010000000, __s22@000000000000000000000000000000010000, __s35@000000000000000000000000000000000100)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[31], bits["000000000000100000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[30], bits["000000000000000000000000000010000000"], t9_2);
    info.eval->multiply_plain(ss[22], bits["000000000000000000000000000000010000"], t9_3);
    info.eval->multiply_plain(ss[35], bits["000000000000000000000000000000000100"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->add(vs[5], ts[9], vs[6]); // __v6 = __v5 + __t9
    
    // __t10 = blend(__s19@000000000000100000000000000010000000, __s27@000000000000000000000000000000010000, __s26@000000000000000000000000000000000100)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[19], bits["000000000000100000000000000010000000"], t10_1);
    info.eval->multiply_plain(ss[27], bits["000000000000000000000000000000010000"], t10_2);
    info.eval->multiply_plain(ss[26], bits["000000000000000000000000000000000100"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->add(vs[6], ts[10], vs[7]); // __v7 = __v6 + __t10
    
    // __t11 = blend(__s23@000000000000100000000000000000000000, __s20@000000000000000000000000000010000000, __s19@000000000000000000000000000000010000, __s36@000000000000000000000000000000000100)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[23], bits["000000000000100000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[20], bits["000000000000000000000000000010000000"], t11_2);
    info.eval->multiply_plain(ss[19], bits["000000000000000000000000000000010000"], t11_3);
    info.eval->multiply_plain(ss[36], bits["000000000000000000000000000000000100"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->add(vs[7], ts[11], vs[8]); // __v8 = __v7 + __t11
    
    // __t12 = blend(__s33@000000000000100000000000000000000000, __s34@000000000000000000000000000010000000, __s35@000000000000000000000000000000010000, __s24@000000000000000000000000000000000100)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[33], bits["000000000000100000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[34], bits["000000000000000000000000000010000000"], t12_2);
    info.eval->multiply_plain(ss[35], bits["000000000000000000000000000000010000"], t12_3);
    info.eval->multiply_plain(ss[24], bits["000000000000000000000000000000000100"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    info.eval->add(vs[8], ts[12], vs[9]); // __v9 = __v8 + __t12
    
    // __t13 = blend(__v2@000000000000100000000000000000000000, __s29@000000000000000000000000000010000000, __s37@000000000000000000000000000000010000, __s31@000000000000000000000000000000000100)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(vs[2], bits["000000000000100000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[29], bits["000000000000000000000000000010000000"], t13_2);
    info.eval->multiply_plain(ss[37], bits["000000000000000000000000000000010000"], t13_3);
    info.eval->multiply_plain(ss[31], bits["000000000000000000000000000000000100"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->add(vs[9], ts[13], vs[10]); // __v10 = __v9 + __t13
    return vs[10];
}
    