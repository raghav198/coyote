
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000110000000010", info);
    add_bitstring(bits, "000000100000011010001001", info);
    add_bitstring(bits, "000000001000000000000000", info);
    add_bitstring(bits, "010010000100000001000000", info);
    add_bitstring(bits, "000000001000000000000010", info);
    add_bitstring(bits, "001000000000000000000010", info);
    add_bitstring(bits, "000000000000000000000001", info);
    add_bitstring(bits, "000000000000001000000000", info);
    add_bitstring(bits, "100000000000000000000000", info);
    add_bitstring(bits, "010000000001010101000000", info);
    add_bitstring(bits, "000000000000000000000010", info);
    add_bitstring(bits, "000000000000110000000000", info);
    add_bitstring(bits, "000010000000000000000000", info);
    add_bitstring(bits, "000010000110101010000000", info);
    add_bitstring(bits, "000000000010001000000000", info);
    add_bitstring(bits, "000000000000000000000011", info);
    add_bitstring(bits, "000000000000000010000010", info);
    add_bitstring(bits, "100000101000000000000000", info);
    add_bitstring(bits, "000000000000001000000001", info);
    add_bitstring(bits, "000000000000000000101000", info);
    add_bitstring(bits, "000100000000000100000000", info);
    add_bitstring(bits, "000000000000000000000100", info);
    add_bitstring(bits, "001000000000000000000000", info);
    add_bitstring(bits, "000000010000000000000000", info);
    add_bitstring(bits, "000000000001100000100110", info);
    add_bitstring(bits, "000010000000000000000001", info);
    add_bitstring(bits, "000101000000000000010000", info);
    add_bitstring(bits, "000001001010000000000000", info);
    add_bitstring(bits, "000000000000000010000000", info);
    add_bitstring(bits, "000000001000001000000000", info);
    add_bitstring(bits, "000000100000000000000000", info);
    add_bitstring(bits, "000000000010000000000000", info);
    add_bitstring(bits, "000000110000000000000000", info);
    add_bitstring(bits, "000000000000000000010000", info);
    add_bitstring(bits, "001000001000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("000111111111111111111110111111111111111111100011111111111111111111011111111111111111011111111111111111110100111111111111111111100001111111111111111101100111111111111111111111111111111111111111100", info);
    ts[1] = encrypt_input("000111111111111111111110111111111111111111100011111111111111111111011111111111111111011111111111111111110100111111111111111111100001111111111111111101100111111111111111111111111111111111111111100", info);
    ts[2] = encrypt_input("000111111111111111110111111111111111111101111111111111111111111000011111111111111111111111111111111111110100111111111111111111100111111111111111111100111111111111111111110111111111111111111110000", info);
    ts[3] = encrypt_input("000111111111111111110111111111111111111101111111111111111111111000011111111111111111111111111111111111110100111111111111111111100111111111111111111100111111111111111111110111111111111111111110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[20];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -5, gk, ss[2]); // __s2 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -20, gk, ss[3]); // __s3 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -14, gk, ss[4]); // __s4 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -19, gk, ss[5]); // __s5 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -13, gk, ss[6]); // __s6 = __v0 >> 13
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -19, gk, ss[7]); // __s7 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -22, gk, ss[8]); // __s8 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -11, gk, ss[9]); // __s9 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -23, gk, ss[10]); // __s10 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -7, gk, ss[11]); // __s11 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -13, gk, ss[12]); // __s12 = __v1 >> 13
    
    // __t4 = blend(__s6@100000000000000000000000, __s3@010010000100000001000000, __s5@000100000000000100000000, __v0@000001001010000000000000, __s1@000000100000011010001001, __s0@000000000001100000100110, __s4@000000000000000000010000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7;
    info.eval->multiply_plain(ss[6], bits["100000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[3], bits["010010000100000001000000"], t4_2);
    info.eval->multiply_plain(ss[5], bits["000100000000000100000000"], t4_3);
    info.eval->multiply_plain(vs[0], bits["000001001010000000000000"], t4_4);
    info.eval->multiply_plain(ss[1], bits["000000100000011010001001"], t4_5);
    info.eval->multiply_plain(ss[0], bits["000000000001100000100110"], t4_6);
    info.eval->multiply_plain(ss[4], bits["000000000000000000010000"], t4_7);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7}, ts[4]);
    
    
    // __t5 = blend(__s12@100000101000000000000000, __s8@010000000001010101000000, __v1@000101000000000000010000, __s10@000010000110101010000000, __s11@000000000000000000101000, __s9@000000000000000000000100, __s7@000000000000000000000011)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7;
    info.eval->multiply_plain(ss[12], bits["100000101000000000000000"], t5_1);
    info.eval->multiply_plain(ss[8], bits["010000000001010101000000"], t5_2);
    info.eval->multiply_plain(vs[1], bits["000101000000000000010000"], t5_3);
    info.eval->multiply_plain(ss[10], bits["000010000110101010000000"], t5_4);
    info.eval->multiply_plain(ss[11], bits["000000000000000000101000"], t5_5);
    info.eval->multiply_plain(ss[9], bits["000000000000000000000100"], t5_6);
    info.eval->multiply_plain(ss[7], bits["000000000000000000000011"], t5_7);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -2, gk, ss[13]); // __s13 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -1, gk, ss[14]); // __s14 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -5, gk, ss[15]); // __s15 = __v2 >> 5
    info.eval->rotate_rows(vs[2], -19, gk, ss[16]); // __s16 = __v2 >> 19
    info.eval->rotate_rows(vs[2], -15, gk, ss[17]); // __s17 = __v2 >> 15
    
    // __t6 = blend(__s6@001000000000000000000000, __s0@000010000000000000000000, __s2@000000001000000000000010, __s5@000000000000000010000000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[6], bits["001000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["000010000000000000000000"], t6_2);
    info.eval->multiply_plain(ss[2], bits["000000001000000000000010"], t6_3);
    info.eval->multiply_plain(ss[5], bits["000000000000000010000000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__s8@001000001000000000000000, __v1@000010000000000000000000, __s9@000000000000000010000000, __s11@000000000000000000000010)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[8], bits["001000001000000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["000010000000000000000000"], t7_2);
    info.eval->multiply_plain(ss[9], bits["000000000000000010000000"], t7_3);
    info.eval->multiply_plain(ss[11], bits["000000000000000000000010"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s14@001000000000000000000000, __s13@000000110000000000000000, __v2@000000001000000000000000, __v3@000000000000000010000000, __s15@000000000000000000000010)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(ss[14], bits["001000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[13], bits["000000110000000000000000"], t8_2);
    info.eval->multiply_plain(vs[2], bits["000000001000000000000000"], t8_3);
    info.eval->multiply_plain(vs[3], bits["000000000000000010000000"], t8_4);
    info.eval->multiply_plain(ss[15], bits["000000000000000000000010"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    
    // __t9 = blend(__v3@001000001000000000000000, __v2@000000100000000000000000, __s17@000000010000000000000000, __s14@000000000000000010000010)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(vs[3], bits["001000001000000000000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["000000100000000000000000"], t9_2);
    info.eval->multiply_plain(ss[17], bits["000000010000000000000000"], t9_3);
    info.eval->multiply_plain(ss[14], bits["000000000000000010000010"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -6, gk, ss[18]); // __s18 = __v4 >> 6
    
    // __t10 = blend(__s14@000010000000000000000001, __s16@000000001000001000000000, __v3@000000000000000000000010)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[14], bits["000010000000000000000001"], t10_1);
    info.eval->multiply_plain(ss[16], bits["000000001000001000000000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["000000000000000000000010"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@000010000000000000000000, __v4@000000001000000000000010, __s15@000000000000001000000000, __v2@000000000000000000000001)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(vs[3], bits["000010000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["000000001000000000000010"], t11_2);
    info.eval->multiply_plain(ss[15], bits["000000000000001000000000"], t11_3);
    info.eval->multiply_plain(vs[2], bits["000000000000000000000001"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    info.eval->rotate_rows(vs[5], -6, gk, ss[19]); // __s19 = __v5 >> 6
    
    // __t12 = blend(__s13@001000000000000000000010, __v2@000000000010001000000000, __s14@000000000000110000000000, __s15@000000000000000000000001)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[13], bits["001000000000000000000010"], t12_1);
    info.eval->multiply_plain(vs[2], bits["000000000010001000000000"], t12_2);
    info.eval->multiply_plain(ss[14], bits["000000000000110000000000"], t12_3);
    info.eval->multiply_plain(ss[15], bits["000000000000000000000001"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__v4@001000000000000000000000, __s19@000000000010000000000000, __s18@000000000000110000000010, __v5@000000000000001000000001)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(vs[4], bits["001000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[19], bits["000000000010000000000000"], t13_2);
    info.eval->multiply_plain(ss[18], bits["000000000000110000000010"], t13_3);
    info.eval->multiply_plain(vs[5], bits["000000000000001000000001"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    return vs[6];
}
    