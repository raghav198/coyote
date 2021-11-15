
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00110000", info);
    add_bitstring(bits, "01110000", info);
    add_bitstring(bits, "01000000", info);
    add_bitstring(bits, "10000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1101011110111101101011011111111111111011", info);
    ts[2] = encrypt_input("110101101100111101111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[7];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[1]); // __s1 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -4, gk, ss[2]); // __s2 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -6, gk, ss[3]); // __s3 = __v1 >> 6
    
    // __t4 = blend(__s0@10000000, __v0@01110000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["10000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["01110000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s2@10000000, __v1@01000000, __s1@00110000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[2], bits["10000000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["01000000"], t5_2);
    info.eval->multiply_plain(ss[1], bits["00110000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v0@10000000, __s0@01110000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["10000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["01110000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__v1@10000000, __s2@01000000, __s3@00110000)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[1], bits["10000000"], t7_1);
    info.eval->multiply_plain(ss[2], bits["01000000"], t7_2);
    info.eval->multiply_plain(ss[3], bits["00110000"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v3@10000000, __v2@01110000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["10000000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["01110000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v2@10000000, __v3@01110000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["10000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["01110000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -7, gk, ss[4]); // __s4 = __v4 >> 7
    info.eval->rotate_rows(vs[4], -6, gk, ss[5]); // __s5 = __v4 >> 6
    info.eval->rotate_rows(vs[4], -5, gk, ss[6]); // __s6 = __v4 >> 5
    info.eval->multiply(ss[5], ss[6], vs[5]); // __v5 = __s5 * __s6
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(vs[4], ss[4], vs[6]); // __v6 = __v4 * __s4
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    return vs[7];
}
    