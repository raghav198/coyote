
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(4);
    ts[0] = encrypt_input("101", info);
    ts[1] = encrypt_input("111", info);
    ts[2] = encrypt_input("111", info);
    ts[3] = encrypt_input("1001", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[3];
    ctxt ss[0];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(vs[0], ts[2], vs[1]); // __v1 = __v0 * __t2
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->multiply(vs[1], ts[3], vs[2]); // __v2 = __v1 * __t3
    info.eval->relinearize_inplace(vs[2], rk);
    return vs[2];
}
    