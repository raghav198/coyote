
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00001010", info);
    add_bitstring(bits, "10100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("1101011011110101101111110111111111011111", info);
    ts[2] = encrypt_input("110101111011011111110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[1]); // __s1 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -3, gk, ss[2]); // __s2 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -7, gk, ss[3]); // __s3 = __v1 >> 7
    
    // __t4 = blend(__v1@10100000, __s1@00001010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[1], bits["10100000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["00001010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(vs[0], ts[4], vs[2]); // __v2 = __v0 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t5 = blend(__s3@10100000, __s2@00001010)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[3], bits["10100000"], t5_1);
    info.eval->multiply_plain(ss[2], bits["00001010"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ss[0], ts[5], vs[3]); // __v3 = __s0 * __t5
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[2], vs[3], vs[4]); // __v4 = __v2 + __v3
    return vs[4];
}
    