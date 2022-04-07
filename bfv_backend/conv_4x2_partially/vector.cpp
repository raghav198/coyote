
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100111", info);
    add_bitstring(bits, "011000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(5);
    ts[0] = encrypt_input("111111111111111111111111100111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("111111111111111111111111100111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111110", info);
    ts[3] = encrypt_input("111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[2];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -3, gk, ss[0]); // __s0 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    
    // __t4 = blend(__v0@100111, __s0@011000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["100111"], t4_1);
    info.eval->multiply_plain(ss[0], bits["011000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(ts[4], vs[1], vs[2]); // __v2 = __t4 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[1]); // __s1 = __v2 >> 1
    info.eval->add(vs[2], ss[1], vs[3]); // __v3 = __v2 + __s1
    return vs[3];
}
    