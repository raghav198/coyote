
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000001000000000100000", info);
    add_bitstring(bits, "000000000000011000000000000", info);
    add_bitstring(bits, "000000000100000000100000000", info);
    add_bitstring(bits, "000000000000010000000100000", info);
    add_bitstring(bits, "000000000000000000000100000", info);
    add_bitstring(bits, "000000000100000000000000000", info);
    add_bitstring(bits, "000000000000000000000001000", info);
    add_bitstring(bits, "000000000000010000000101010", info);
    add_bitstring(bits, "000000000000000010100000000", info);
    add_bitstring(bits, "000000000000000010000000010", info);
    add_bitstring(bits, "000000000100001000100000010", info);
    add_bitstring(bits, "000000000000000010100100000", info);
    add_bitstring(bits, "000000000100000000000100000", info);
    add_bitstring(bits, "000000000100000010000000000", info);
    add_bitstring(bits, "000000000100000000100101010", info);
    add_bitstring(bits, "000000000001000000000000000", info);
    add_bitstring(bits, "000000000000000000000101010", info);
    add_bitstring(bits, "000000000101000010100000010", info);
    add_bitstring(bits, "000000000000001000000000000", info);
    add_bitstring(bits, "000000000001000000100001000", info);
    add_bitstring(bits, "000000000000010000100000000", info);
    add_bitstring(bits, "000000000000000000000000010", info);
    add_bitstring(bits, "000000000001000000000000010", info);
    add_bitstring(bits, "000000000101001010100000000", info);
    add_bitstring(bits, "000000000001011010000000000", info);
    add_bitstring(bits, "000000000000010000000000000", info);
    add_bitstring(bits, "000000000000010010000001000", info);
    add_bitstring(bits, "000000000001010000000000000", info);
    add_bitstring(bits, "000000000001001010000000000", info);
    add_bitstring(bits, "000000000000001000000001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("111111111111111111111111111111111111111111111111111011111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111110111111111111111111111111110111111111111111111111111010111111111111111111111111011111111111111111111111111011111111111111111111111111110111111111111111111111111010111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111010111111111111111111111111011111111111111111111111111110111111111111111111111111011", info);
    ts[1] = encrypt_input("111111111111111111111111111111111111111111111111111011111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111110111111111111111111111111110111111111111111111111111010111111111111111111111111011111111111111111111111111011111111111111111111111111110111111111111111111111111010111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111010111111111111111111111111011111111111111111111111111110111111111111111111111111011", info);
    ts[2] = encrypt_input("000000000011111111111111111111111111001111111111111111111111111110111111111111111111111111111111111111111111111111111111011111111111111111111111111101111111111111111111111111100011111111111111111111111101101111111111111111111111110100111111111111111111111111011", info);
    ts[3] = encrypt_input("000000000011111111111111111111111111001111111111111111111111111110111111111111111111111111111111111111111111111111111111011111111111111111111111111101111111111111111111111111100011111111111111111111111101101111111111111111111111110100111111111111111111111111011", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -11, gk, ss[0]); // __s0 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -8, gk, ss[1]); // __s1 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -7, gk, ss[2]); // __s2 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -21, gk, ss[3]); // __s3 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -22, gk, ss[4]); // __s4 = __v0 >> 22
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[5]); // __s5 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -26, gk, ss[6]); // __s6 = __v1 >> 26
    info.eval->rotate_rows(vs[1], -3, gk, ss[7]); // __s7 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -24, gk, ss[8]); // __s8 = __v1 >> 24
    info.eval->rotate_rows(vs[1], -22, gk, ss[9]); // __s9 = __v1 >> 22
    
    // __t4 = blend(__s2@000000000100001000100000010, __s3@000000000001000000000000000, __s1@000000000000010010000001000, __s0@000000000000000000000100000)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[2], bits["000000000100001000100000010"], t4_1);
    info.eval->multiply_plain(ss[3], bits["000000000001000000000000000"], t4_2);
    info.eval->multiply_plain(ss[1], bits["000000000000010010000001000"], t4_3);
    info.eval->multiply_plain(ss[0], bits["000000000000000000000100000"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__s8@000000000100000010000000000, __s5@000000000001000000100001000, __s6@000000000000010000000100000, __s9@000000000000001000000000000, __s7@000000000000000000000000010)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[8], bits["000000000100000010000000000"], t5_1);
    info.eval->multiply_plain(ss[5], bits["000000000001000000100001000"], t5_2);
    info.eval->multiply_plain(ss[6], bits["000000000000010000000100000"], t5_3);
    info.eval->multiply_plain(ss[9], bits["000000000000001000000000000"], t5_4);
    info.eval->multiply_plain(ss[7], bits["000000000000000000000000010"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s1@000000000100000000000100000, __s2@000000000001010000000000000, __s0@000000000000001000000001000, __s3@000000000000000010100000000, __v0@000000000000000000000000010)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5;
    info.eval->multiply_plain(ss[1], bits["000000000100000000000100000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["000000000001010000000000000"], t6_2);
    info.eval->multiply_plain(ss[0], bits["000000000000001000000001000"], t6_3);
    info.eval->multiply_plain(ss[3], bits["000000000000000010100000000"], t6_4);
    info.eval->multiply_plain(vs[0], bits["000000000000000000000000010"], t6_5);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5}, ts[6]);
    
    
    // __t7 = blend(__s9@000000000100000000000000000, __s8@000000000001000000000100000, __s7@000000000000010000100000000, __s6@000000000000001000000001000, __s5@000000000000000010000000010)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5;
    info.eval->multiply_plain(ss[9], bits["000000000100000000000000000"], t7_1);
    info.eval->multiply_plain(ss[8], bits["000000000001000000000100000"], t7_2);
    info.eval->multiply_plain(ss[7], bits["000000000000010000100000000"], t7_3);
    info.eval->multiply_plain(ss[6], bits["000000000000001000000001000"], t7_4);
    info.eval->multiply_plain(ss[5], bits["000000000000000010000000010"], t7_5);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v0@000000000100000000000000000, __s0@000000000001000000000000010, __s3@000000000000011000000000000, __s4@000000000000000010100100000, __s2@000000000000000000000001000)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(vs[0], bits["000000000100000000000000000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["000000000001000000000000010"], t8_2);
    info.eval->multiply_plain(ss[3], bits["000000000000011000000000000"], t8_3);
    info.eval->multiply_plain(ss[4], bits["000000000000000010100100000"], t8_4);
    info.eval->multiply_plain(ss[2], bits["000000000000000000000001000"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    
    // __t9 = blend(__s6@000000000101000010100000010, __s5@000000000000010000000000000, __s8@000000000000001000000001000, __s9@000000000000000000000100000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[6], bits["000000000101000010100000010"], t9_1);
    info.eval->multiply_plain(ss[5], bits["000000000000010000000000000"], t9_2);
    info.eval->multiply_plain(ss[8], bits["000000000000001000000001000"], t9_3);
    info.eval->multiply_plain(ss[9], bits["000000000000000000000100000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v2@000000000100000000100101010, __v4@000000000001011010000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[2], bits["000000000100000000100101010"], t10_1);
    info.eval->multiply_plain(vs[4], bits["000000000001011010000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v3@000000000101001010100000000, __v2@000000000000010000000000000, __v4@000000000000000000000101010)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[3], bits["000000000101001010100000000"], t11_1);
    info.eval->multiply_plain(vs[2], bits["000000000000010000000000000"], t11_2);
    info.eval->multiply_plain(vs[4], bits["000000000000000000000101010"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v4@000000000100000000100000000, __v2@000000000001001010000000000, __v3@000000000000010000000101010)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[4], bits["000000000100000000100000000"], t12_1);
    info.eval->multiply_plain(vs[2], bits["000000000001001010000000000"], t12_2);
    info.eval->multiply_plain(vs[3], bits["000000000000010000000101010"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    info.eval->add(ts[12], vs[5], vs[6]); // __v6 = __t12 + __v5
    return vs[6];
}
    