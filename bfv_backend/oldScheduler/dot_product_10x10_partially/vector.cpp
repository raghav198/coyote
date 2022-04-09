
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0100010000", info);
    add_bitstring(bits, "0000010000", info);
    add_bitstring(bits, "0010000000", info);
    add_bitstring(bits, "0100000000", info);
    add_bitstring(bits, "0000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(7);
    ts[0] = encrypt_input("111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[1] = encrypt_input("111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[2] = encrypt_input("111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    ts[3] = encrypt_input("111111111111101101111111111111110111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111111111111111101101111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[2]); // __v2 = __v0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -2, gk, ss[0]); // __s0 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -6, gk, ss[1]); // __s1 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -7, gk, ss[2]); // __s2 = __v2 >> 7
    
    // __t4 = blend(__s1@0100010000, __s0@0010000000, __s2@0000100000)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[1], bits["0100010000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["0010000000"], t4_2);
    info.eval->multiply_plain(ss[2], bits["0000100000"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__v2@0100000000, __s1@0010000000, __s0@0000100000, __s2@0000010000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(vs[2], bits["0100000000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["0010000000"], t5_2);
    info.eval->multiply_plain(ss[0], bits["0000100000"], t5_3);
    info.eval->multiply_plain(ss[2], bits["0000010000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[3]); // __v3 = __t4 + __t5
    
    // __t6 = blend(__v2@0000100000, __s0@0000010000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[2], bits["0000100000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["0000010000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[6], vs[3], vs[4]); // __v4 = __t6 + __v3
    info.eval->rotate_rows(vs[4], -7, gk, ss[3]); // __s3 = __v4 >> 7
    info.eval->add(vs[3], ss[3], vs[5]); // __v5 = __v3 + __s3
    info.eval->rotate_rows(vs[5], -1, gk, ss[4]); // __s4 = __v5 >> 1
    info.eval->add(vs[5], ss[4], vs[6]); // __v6 = __v5 + __s4
    return vs[6];
}
    