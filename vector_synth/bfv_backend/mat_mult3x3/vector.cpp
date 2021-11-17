
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000010000000000010000010", info);
    add_bitstring(bits, "000000000000000010000000000", info);
    add_bitstring(bits, "000010000000000000000000000", info);
    add_bitstring(bits, "000010000000010010000010000", info);
    add_bitstring(bits, "000000000000010000000000000", info);
    add_bitstring(bits, "000000000000000000010000010", info);
    add_bitstring(bits, "000000000000010010000000000", info);
    add_bitstring(bits, "000010000010000010000000000", info);
    add_bitstring(bits, "010000000000010000000010000", info);
    add_bitstring(bits, "000000010010000000010000000", info);
    add_bitstring(bits, "000000000000000000010010000", info);
    add_bitstring(bits, "000010010010000010000000000", info);
    add_bitstring(bits, "000010010000000010000000010", info);
    add_bitstring(bits, "000000000000000000010000000", info);
    add_bitstring(bits, "000000000010000000010000000", info);
    add_bitstring(bits, "000000010000000000000000000", info);
    add_bitstring(bits, "010000000010000000000000000", info);
    add_bitstring(bits, "000000000000010000010010000", info);
    add_bitstring(bits, "000010000000000010000000010", info);
    add_bitstring(bits, "000000000010000000000000000", info);
    add_bitstring(bits, "000000000000000000000000010", info);
    add_bitstring(bits, "000000000010000010000000000", info);
    add_bitstring(bits, "000010010000010010000010000", info);
    add_bitstring(bits, "010000000000000000000000010", info);
    add_bitstring(bits, "010000000000000000000000000", info);
    add_bitstring(bits, "000000010000010000010010000", info);
    add_bitstring(bits, "000000000000000000000010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("111101111111111111101111111111111111111011111110101101111011110101101111011110101101111011111101111111111111101111111111111101111111111", info);
    ts[2] = encrypt_input("000000000000000000110111111111111110111111111111110101111011110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -26, gk, ss[1]); // __s1 = __v0 >> 26
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -10, gk, ss[3]); // __s3 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -19, gk, ss[4]); // __s4 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -9, gk, ss[5]); // __s5 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -18, gk, ss[6]); // __s6 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -8, gk, ss[7]); // __s7 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -17, gk, ss[8]); // __s8 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -26, gk, ss[9]); // __s9 = __v1 >> 26
    
    // __t4 = blend(__s1@010000000000000000000000010, __v0@000010010010000010000000000, __s0@000000000000010000010010000)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[1], bits["010000000000000000000000010"], t4_1);
    info.eval->multiply_plain(vs[0], bits["000010010010000010000000000"], t4_2);
    info.eval->multiply_plain(ss[0], bits["000000000000010000010010000"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s7@010000000000000000000000000, __s5@000010000000000000000000000, __s3@000000010000000000000000000, __s6@000000000010000010000000000, __s4@000000000000010000000000000, __s2@000000000000000000010010000, __s9@000000000000000000000000010)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7;
    info.eval->multiply_plain(ss[7], bits["010000000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[5], bits["000010000000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[3], bits["000000010000000000000000000"], t5_3);
    info.eval->multiply_plain(ss[6], bits["000000000010000010000000000"], t5_4);
    info.eval->multiply_plain(ss[4], bits["000000000000010000000000000"], t5_5);
    info.eval->multiply_plain(ss[2], bits["000000000000000000010010000"], t5_6);
    info.eval->multiply_plain(ss[9], bits["000000000000000000000000010"], t5_7);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v0@010000000000010000000010000, __s0@000010010000000010000000010, __s1@000000000010000000010000000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[0], bits["010000000000010000000010000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["000010010000000010000000010"], t6_2);
    info.eval->multiply_plain(ss[1], bits["000000000010000000010000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s5@010000000000000000000000000, __s3@000010000000000000000000000, __s7@000000010000000000000000000, __s8@000000000010000000000000000, __s6@000000000000010000000000000, __s4@000000000000000010000000000, __s9@000000000000000000010000000, __v1@000000000000000000000010000, __s2@000000000000000000000000010)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8, t7_9;
    info.eval->multiply_plain(ss[5], bits["010000000000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[3], bits["000010000000000000000000000"], t7_2);
    info.eval->multiply_plain(ss[7], bits["000000010000000000000000000"], t7_3);
    info.eval->multiply_plain(ss[8], bits["000000000010000000000000000"], t7_4);
    info.eval->multiply_plain(ss[6], bits["000000000000010000000000000"], t7_5);
    info.eval->multiply_plain(ss[4], bits["000000000000000010000000000"], t7_6);
    info.eval->multiply_plain(ss[9], bits["000000000000000000010000000"], t7_7);
    info.eval->multiply_plain(vs[1], bits["000000000000000000000010000"], t7_8);
    info.eval->multiply_plain(ss[2], bits["000000000000000000000000010"], t7_9);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8, t7_9}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s0@010000000010000000000000000, __s1@000010010000010010000010000, __v0@000000000000000000010000010)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[0], bits["010000000010000000000000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["000010010000010010000010000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["000000000000000000010000010"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s3@010000000000000000000000000, __s7@000010000000000000000000000, __s5@000000010000000000000000000, __s4@000000000010000000000000000, __s8@000000000000010010000000000, __v1@000000000000000000010000010, __s9@000000000000000000000010000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7;
    info.eval->multiply_plain(ss[3], bits["010000000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[7], bits["000010000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[5], bits["000000010000000000000000000"], t9_3);
    info.eval->multiply_plain(ss[4], bits["000000000010000000000000000"], t9_4);
    info.eval->multiply_plain(ss[8], bits["000000000000010010000000000"], t9_5);
    info.eval->multiply_plain(vs[1], bits["000000000000000000010000010"], t9_6);
    info.eval->multiply_plain(ss[9], bits["000000000000000000000010000"], t9_7);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v4@010000000010000000000000000, __v3@000010000000000010000000010, __v2@000000010000010000010010000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[4], bits["010000000010000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["000010000000000010000000010"], t10_2);
    info.eval->multiply_plain(vs[2], bits["000000010000010000010010000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v2@010000000000000000000000010, __v4@000010000000010010000010000, __v3@000000010010000000010000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[2], bits["010000000000000000000000010"], t11_1);
    info.eval->multiply_plain(vs[4], bits["000010000000010010000010000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["000000010010000000010000000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v3@010000000000010000000010000, __v2@000010000010000010000000000, __v4@000000010000000000010000010)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[3], bits["010000000000010000000010000"], t12_1);
    info.eval->multiply_plain(vs[2], bits["000010000010000010000000000"], t12_2);
    info.eval->multiply_plain(vs[4], bits["000000010000000000010000010"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    info.eval->add(vs[5], ts[12], vs[6]); // __v6 = __v5 + __t12
    return vs[6];
}
    