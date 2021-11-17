
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10001000", info);
    add_bitstring(bits, "00100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("1111011111110101101111010110111111011111", info);
    ts[2] = encrypt_input("001101011110001101111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[7];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -6, gk, ss[1]); // __s1 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -5, gk, ss[2]); // __s2 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -7, gk, ss[3]); // __s3 = __v1 >> 7
    
    // __t4 = blend(__s2@10001000, __s3@00100010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[2], bits["10001000"], t4_1);
    info.eval->multiply_plain(ss[3], bits["00100010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(ss[0], ts[4], vs[2]); // __v2 = __s0 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t5 = blend(__s1@10001000, __v1@00100010)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[1], bits["10001000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["00100010"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(vs[0], ts[5], vs[3]); // __v3 = __v0 * __t5
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[3], vs[2], vs[4]); // __v4 = __v3 + __v2
    info.eval->rotate_rows(vs[4], -2, gk, ss[4]); // __s4 = __v4 >> 2
    info.eval->rotate_rows(vs[4], -6, gk, ss[5]); // __s5 = __v4 >> 6
    info.eval->rotate_rows(vs[4], -4, gk, ss[6]); // __s6 = __v4 >> 4
    info.eval->multiply(ss[4], ss[5], vs[5]); // __v5 = __s4 * __s5
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(vs[4], ss[6], vs[6]); // __v6 = __v4 * __s6
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    return vs[7];
}
    