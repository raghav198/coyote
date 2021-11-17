
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000001001001001000000001001000", info);
    add_bitstring(bits, "00000000000000000000001000000000", info);
    add_bitstring(bits, "00000000000000000001000000000000", info);
    add_bitstring(bits, "00000001001000001000000001001000", info);
    add_bitstring(bits, "00000001001001001001000001001000", info);
    add_bitstring(bits, "10010111111110111011011101101000", info);
    add_bitstring(bits, "00000001001001001000001001001000", info);
    add_bitstring(bits, "00000000000001000000100010000001", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000000001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("11111001101101111111011111101101111111110101101111111110101111111110111101111111011111101111111111111111101111111110101111101111011111011110", info);
    ts[2] = encrypt_input("11111001111101111111110110111111111110110111111011111110101111011010110101111111111110111111011111111101111111111110111111101101111111011011", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[1]); // __s1 = __v1 >> 2
    
    // __t4 = blend(__v0@10010111111110111011011101101000, __s0@00000000000000000000000000000001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["10010111111110111011011101101000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000000000001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__v1@10010111111110111011011101101000, __s1@00000000000000000000000000000001)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[1], bits["10010111111110111011011101101000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000000000001"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -7, gk, ss[2]); // __s2 = __v2 >> 7
    info.eval->rotate_rows(vs[2], -2, gk, ss[3]); // __s3 = __v2 >> 2
    
    // __t6 = blend(__v0@00000000000001000000100010000001, __s0@00000000000000000001000000000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["00000000000001000000100010000001"], t6_1);
    info.eval->multiply_plain(ss[0], bits["00000000000000000001000000000000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__v1@00000000000001000000100010000001, __s1@00000000000000000001000000000000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["00000000000001000000100010000001"], t7_1);
    info.eval->multiply_plain(ss[1], bits["00000000000000000001000000000000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -2, gk, ss[4]); // __s4 = __v3 >> 2
    info.eval->rotate_rows(vs[3], -7, gk, ss[5]); // __s5 = __v3 >> 7
    
    // __t8 = blend(__v2@00000000000000000001000000000000, __v3@00000000000000000000000000000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["00000000000000000001000000000000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000000000000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v3@00000000000000000001000000000000, __v2@00000000000000000000000000000001)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["00000000000000000001000000000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000000000000001"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    
    // __t10 = blend(__v2@00000001001000001000000001001000, __v3@00000000000001000000000000000000, __s2@00000000000000000000001000000000, __v4@00000000000000000000000000000001)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(vs[2], bits["00000001001000001000000001001000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["00000000000001000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[2], bits["00000000000000000000001000000000"], t10_3);
    info.eval->multiply_plain(vs[4], bits["00000000000000000000000000000001"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s3@00000001001001001000000001001000, __v2@00000000000000000000001000000000, __s5@00000000000000000000000000000001)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(ss[3], bits["00000001001001001000000001001000"], t11_1);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000001000000000"], t11_2);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000000000000001"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v5@00000001001001001000001001001000, __v4@00000000000000000001000000000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["00000001001001001000001001001000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["00000000000000000001000000000000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__s2@00000001001001001001000001001000, __s4@00000000000000000000001000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[2], bits["00000001001001001001000001001000"], t13_1);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000001000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    return vs[6];
}
    