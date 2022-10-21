
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000010", info);
    add_bitstring(bits, "0000001101", info);
    add_bitstring(bits, "0000001000", info);
    add_bitstring(bits, "0000000111", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[1] = encrypt_input("111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[2] = encrypt_input("111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[3] = encrypt_input("111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[2]); // __v2 = __v0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -6, gk, ss[0]); // __s0 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -4, gk, ss[1]); // __s1 = __v2 >> 4
    
    // __t4 = blend(__v2@0000001101, __s0@0000000010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[2], bits["0000001101"], t4_1);
    info.eval->multiply_plain(ss[0], bits["0000000010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s0@0000001000, __s1@0000000111)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[0], bits["0000001000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["0000000111"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[3]); // __v3 = __t4 + __t5
    info.eval->rotate_rows(vs[3], -9, gk, ss[2]); // __s2 = __v3 >> 9
    info.eval->add(ss[0], vs[3], vs[4]); // __v4 = __s0 + __v3
    info.eval->rotate_rows(vs[4], -9, gk, ss[3]); // __s3 = __v4 >> 9
    
    // __t6 = blend(__v3@0000001000, __v2@0000000010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[3], bits["0000001000"], t6_1);
    info.eval->multiply_plain(vs[2], bits["0000000010"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__s3@0000001000, __v3@0000000010)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[3], bits["0000001000"], t7_1);
    info.eval->multiply_plain(vs[3], bits["0000000010"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[5]); // __v5 = __t6 + __t7
    info.eval->rotate_rows(vs[5], -2, gk, ss[4]); // __s4 = __v5 >> 2
    info.eval->add(ss[2], vs[5], vs[6]); // __v6 = __s2 + __v5
    info.eval->add(ss[4], vs[6], vs[7]); // __v7 = __s4 + __v6
    return vs[7];
}
    