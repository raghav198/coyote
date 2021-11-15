
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(3);
    ts[0] = encrypt_input("110111111", info);
    ts[2] = encrypt_input("110111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[0];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[7]); // __v7 = __v0 * __v1
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -2, gk, vs[2]); // __v2 = __v7 >> 2
    info.eval->rotate_rows(vs[7], -1, gk, vs[3]); // __v3 = __v7 >> 1
    info.eval->add(vs[2], vs[3], vs[4]); // __v4 = __v2 + __v3
    info.eval->add(vs[7], vs[4], vs[6]); // __v6 = __v7 + __v4
    return vs[7];
}
    