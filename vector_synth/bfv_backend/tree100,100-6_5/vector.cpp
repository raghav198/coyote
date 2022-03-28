
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10100000", info);
    add_bitstring(bits, "00001000", info);
    add_bitstring(bits, "00001010", info);
    add_bitstring(bits, "00000101", info);
    add_bitstring(bits, "01010000", info);
    add_bitstring(bits, "00000010", info);
    add_bitstring(bits, "00000100", info);
    add_bitstring(bits, "10000000", info);
    add_bitstring(bits, "00100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("011111110111111011010000", info);
    ts[2] = encrypt_input("111100110101111101101100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[16];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -5, gk, ss[3]); // __s3 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -1, gk, ss[4]); // __s4 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -6, gk, ss[5]); // __s5 = __v1 >> 6
    
    // __t4 = blend(__s2@10100000, __v0@01010000, __s1@00001010, __s0@00000101)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[2], bits["10100000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["01010000"], t4_2);
    info.eval->multiply_plain(ss[1], bits["00001010"], t4_3);
    info.eval->multiply_plain(ss[0], bits["00000101"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__v1@10100000, __s5@01010000, __s4@00001010, __s3@00000101)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(vs[1], bits["10100000"], t5_1);
    info.eval->multiply_plain(ss[5], bits["01010000"], t5_2);
    info.eval->multiply_plain(ss[4], bits["00001010"], t5_3);
    info.eval->multiply_plain(ss[3], bits["00000101"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -6, gk, ss[6]); // __s6 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -4, gk, ss[7]); // __s7 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -2, gk, ss[8]); // __s8 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -3, gk, ss[9]); // __s9 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -1, gk, ss[10]); // __s10 = __v2 >> 1
    
    // __t6 = blend(__s10@10000000, __s6@00001000, __s8@00000100, __s7@00000010)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[10], bits["10000000"], t6_1);
    info.eval->multiply_plain(ss[6], bits["00001000"], t6_2);
    info.eval->multiply_plain(ss[8], bits["00000100"], t6_3);
    info.eval->multiply_plain(ss[7], bits["00000010"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__s9@10000000, __v2@00001000, __s7@00000100, __s6@00000010)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[9], bits["10000000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["00001000"], t7_2);
    info.eval->multiply_plain(ss[7], bits["00000100"], t7_3);
    info.eval->multiply_plain(ss[6], bits["00000010"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[3]); // __v3 = __t6 + __t7
    info.eval->rotate_rows(vs[3], -2, gk, ss[11]); // __s11 = __v3 >> 2
    info.eval->rotate_rows(vs[3], -6, gk, ss[12]); // __s12 = __v3 >> 6
    info.eval->rotate_rows(vs[3], -1, gk, ss[13]); // __s13 = __v3 >> 1
    
    // __t8 = blend(__s11@00100000, __v3@00000010)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[11], bits["00100000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["00000010"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s12@00100000, __s13@00000010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[12], bits["00100000"], t9_1);
    info.eval->multiply_plain(ss[13], bits["00000010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -2, gk, ss[14]); // __s14 = __v4 >> 2
    info.eval->rotate_rows(vs[4], -6, gk, ss[15]); // __s15 = __v4 >> 6
    info.eval->add(ss[15], ss[14], vs[5]); // __v5 = __s15 + __s14
    return vs[5];
}
    