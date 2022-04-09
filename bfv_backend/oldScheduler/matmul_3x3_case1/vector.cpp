
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "101000000000000000", info);
    add_bitstring(bits, "000000000100100000", info);
    add_bitstring(bits, "000000110000000000", info);
    add_bitstring(bits, "001000000000000000", info);
    add_bitstring(bits, "000000100000000000", info);
    add_bitstring(bits, "000001000000000000", info);
    add_bitstring(bits, "000000000100000000", info);
    add_bitstring(bits, "000100000000000000", info);
    add_bitstring(bits, "001001001000000000", info);
    add_bitstring(bits, "000100001100000000", info);
    add_bitstring(bits, "001001000000100000", info);
    add_bitstring(bits, "100100000000000000", info);
    add_bitstring(bits, "100000000000000000", info);
    add_bitstring(bits, "000000000000100000", info);
    add_bitstring(bits, "100000001000000000", info);
    add_bitstring(bits, "001000000000100000", info);
    add_bitstring(bits, "001000001000000000", info);
    add_bitstring(bits, "000000010000000000", info);
    add_bitstring(bits, "001001010000100000", info);
    add_bitstring(bits, "000000010000100000", info);
    add_bitstring(bits, "000100010000000000", info);
    add_bitstring(bits, "000100010100000000", info);
    add_bitstring(bits, "000000001000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("11111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("11111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -1, gk, ss[2]); // __s2 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -17, gk, ss[3]); // __s3 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -16, gk, ss[4]); // __s4 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -15, gk, ss[5]); // __s5 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -11, gk, ss[6]); // __s6 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -9, gk, ss[7]); // __s7 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -7, gk, ss[8]); // __s8 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -13, gk, ss[9]); // __s9 = __v0 >> 13
    
    // __t2 = blend(__s4@100000000000000000, __s2@001000000000000000, __s1@000100000000000000, __s5@000001000000000000, __s8@000000100000000000, __s3@000000010000000000, __s6@000000001000000000, __s9@000000000000100000)
    ctxt t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8;
    info.eval->multiply_plain(ss[4], bits["100000000000000000"], t2_1);
    info.eval->multiply_plain(ss[2], bits["001000000000000000"], t2_2);
    info.eval->multiply_plain(ss[1], bits["000100000000000000"], t2_3);
    info.eval->multiply_plain(ss[5], bits["000001000000000000"], t2_4);
    info.eval->multiply_plain(ss[8], bits["000000100000000000"], t2_5);
    info.eval->multiply_plain(ss[3], bits["000000010000000000"], t2_6);
    info.eval->multiply_plain(ss[6], bits["000000001000000000"], t2_7);
    info.eval->multiply_plain(ss[9], bits["000000000000100000"], t2_8);
    info.eval->add_many({t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8}, ts[2]);
    
    
    // __t3 = blend(__s8@100000000000000000, __s4@001000000000100000, __s6@000100010000000000, __s2@000001000000000000, __s0@000000100000000000, __s5@000000001000000000)
    ctxt t3_1, t3_2, t3_3, t3_4, t3_5, t3_6;
    info.eval->multiply_plain(ss[8], bits["100000000000000000"], t3_1);
    info.eval->multiply_plain(ss[4], bits["001000000000100000"], t3_2);
    info.eval->multiply_plain(ss[6], bits["000100010000000000"], t3_3);
    info.eval->multiply_plain(ss[2], bits["000001000000000000"], t3_4);
    info.eval->multiply_plain(ss[0], bits["000000100000000000"], t3_5);
    info.eval->multiply_plain(ss[5], bits["000000001000000000"], t3_6);
    info.eval->add_many({t3_1, t3_2, t3_3, t3_4, t3_5, t3_6}, ts[3]);
    
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t4 = blend(__v0@101000000000000000, __s0@000100000000000000, __s3@000001000000000000, __s7@000000001000000000, __s2@000000000100000000, __s5@000000000000100000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(vs[0], bits["101000000000000000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["000100000000000000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["000001000000000000"], t4_3);
    info.eval->multiply_plain(ss[7], bits["000000001000000000"], t4_4);
    info.eval->multiply_plain(ss[2], bits["000000000100000000"], t4_5);
    info.eval->multiply_plain(ss[5], bits["000000000000100000"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6}, ts[4]);
    
    
    // __t5 = blend(__s6@100000000000000000, __s3@001000001000000000, __s8@000100000000000000, __s0@000001000000000000, __v0@000000000100100000)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[6], bits["100000000000000000"], t5_1);
    info.eval->multiply_plain(ss[3], bits["001000001000000000"], t5_2);
    info.eval->multiply_plain(ss[8], bits["000100000000000000"], t5_3);
    info.eval->multiply_plain(ss[0], bits["000001000000000000"], t5_4);
    info.eval->multiply_plain(vs[0], bits["000000000100100000"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s3@100000000000000000, __s0@001000000000000000, __s2@000100010000000000, __s8@000001000000000000, __s9@000000001000000000, __s1@000000000100000000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(ss[3], bits["100000000000000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["001000000000000000"], t6_2);
    info.eval->multiply_plain(ss[2], bits["000100010000000000"], t6_3);
    info.eval->multiply_plain(ss[8], bits["000001000000000000"], t6_4);
    info.eval->multiply_plain(ss[9], bits["000000001000000000"], t6_5);
    info.eval->multiply_plain(ss[1], bits["000000000100000000"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s7@100100000000000000, __s5@001000000000000000, __v0@000001000000000000, __s9@000000010000000000, __s2@000000001000000000, __s4@000000000100000000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6;
    info.eval->multiply_plain(ss[7], bits["100100000000000000"], t7_1);
    info.eval->multiply_plain(ss[5], bits["001000000000000000"], t7_2);
    info.eval->multiply_plain(vs[0], bits["000001000000000000"], t7_3);
    info.eval->multiply_plain(ss[9], bits["000000010000000000"], t7_4);
    info.eval->multiply_plain(ss[2], bits["000000001000000000"], t7_5);
    info.eval->multiply_plain(ss[4], bits["000000000100000000"], t7_6);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v3@100000000000000000, __v1@001001010000100000, __v2@000100001100000000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(vs[3], bits["100000000000000000"], t8_1);
    info.eval->multiply_plain(vs[1], bits["001001010000100000"], t8_2);
    info.eval->multiply_plain(vs[2], bits["000100001100000000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__v1@100000001000000000, __v2@001001000000100000, __v3@000100010100000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(vs[1], bits["100000001000000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["001001000000100000"], t9_2);
    info.eval->multiply_plain(vs[3], bits["000100010100000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    
    // __t10 = blend(__v2@100000000000000000, __v3@001001001000000000, __v1@000100000000000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[2], bits["100000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["001001001000000000"], t10_2);
    info.eval->multiply_plain(vs[1], bits["000100000000000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->add(ts[10], vs[4], vs[5]); // __v5 = __t10 + __v4
    
    // __t11 = blend(__s7@000000100000000000, __s6@000000000100000000, __s3@000000000000100000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(ss[7], bits["000000100000000000"], t11_1);
    info.eval->multiply_plain(ss[6], bits["000000000100000000"], t11_2);
    info.eval->multiply_plain(ss[3], bits["000000000000100000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    
    // __t12 = blend(__s1@000000100000000000, __s0@000000000100100000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[1], bits["000000100000000000"], t12_1);
    info.eval->multiply_plain(ss[0], bits["000000000100100000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[6]); // __v6 = __t11 * __t12
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t13 = blend(__v1@000000100000000000, __v6@000000000100000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[1], bits["000000100000000000"], t13_1);
    info.eval->multiply_plain(vs[6], bits["000000000100000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__v6@000000100000000000, __v4@000000000100000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[6], bits["000000100000000000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["000000000100000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->add(ts[13], ts[14], vs[7]); // __v7 = __t13 + __t14
    
    // __t15 = blend(__s6@000000100000000000, __s7@000000010000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[6], bits["000000100000000000"], t15_1);
    info.eval->multiply_plain(ss[7], bits["000000010000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    
    // __t16 = blend(__s2@000000100000000000, __s5@000000010000000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[2], bits["000000100000000000"], t16_1);
    info.eval->multiply_plain(ss[5], bits["000000010000000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    info.eval->multiply(ts[15], ts[16], vs[8]); // __v8 = __t15 * __t16
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t17 = blend(__v8@000000110000000000, __v6@000000000000100000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[8], bits["000000110000000000"], t17_1);
    info.eval->multiply_plain(vs[6], bits["000000000000100000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    
    // __t18 = blend(__v7@000000100000000000, __v4@000000010000100000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[7], bits["000000100000000000"], t18_1);
    info.eval->multiply_plain(vs[4], bits["000000010000100000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->add(ts[17], ts[18], vs[9]); // __v9 = __t17 + __t18
    return vs[9];
}
    