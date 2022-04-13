
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "00000010", info);
    add_bitstring(bits, "00001000", info);
    add_bitstring(bits, "10000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("111111000111111101", info);
    ts[1] = encrypt_input("110111000111111111", info);
    ts[2] = encrypt_input("001111111000", info);
    ts[3] = encrypt_input("00111111111000", info);
    ts[4] = encrypt_input("1110000000", info);
    ts[11] = encrypt_input("1110000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[5];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -7, gk, ss[1]); // __s1 = __v1 >> 7
    
    // __t5 = blend(__v1@00001000, __t4@10000000)
    ctxt t5_1;
    info.eval->multiply_plain(vs[1], bits["00001000"], t5_1);
    info.eval->add(t5_1, ts[4], ts[5]);
    
    
    // __t6 = blend(__v0@10000000, __s0@00001000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["10000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["00001000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[5], ts[6], vs[2]); // __v2 = __t5 + __t6
    info.eval->rotate_rows(vs[2], -4, gk, ss[2]); // __s2 = __v2 >> 4
    
    // __t7 = blend(__s1@00100000, __v0@00000010)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[1], bits["00100000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["00000010"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    
    // __t8 = blend(__v1@00100000, __s0@00000010)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[1], bits["00100000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["00000010"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[3]); // __v3 = __t7 * __t8
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -4, gk, ss[3]); // __s3 = __v3 >> 4
    
    // __t9 = blend(__s2@10000000, __s3@00100000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[2], bits["10000000"], t9_1);
    info.eval->multiply_plain(ss[3], bits["00100000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__s0@10000000, __v3@00100000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[0], bits["10000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["00100000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    info.eval->add(ts[9], ts[10], vs[4]); // __v4 = __t9 + __t10
    info.eval->rotate_rows(vs[4], -6, gk, ss[4]); // __s4 = __v4 >> 6
    info.eval->add(ts[11], vs[4], vs[5]); // __v5 = __t11 + __v4
    info.eval->multiply(vs[2], ss[4], vs[6]); // __v6 = __v2 * __s4
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[5], vs[6], vs[7]); // __v7 = __v5 + __v6
    return vs[7];
}
    