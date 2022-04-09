
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "0001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(4);
    ts[0] = encrypt_input("10110111111", info);
    ts[1] = encrypt_input("111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[3];
    ctxt ss[2];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    
    // __t2 = blend(__v0@0010, __s0@0001)
    ctxt t2_1, t2_2;
    info.eval->multiply_plain(vs[0], bits["0010"], t2_1);
    info.eval->multiply_plain(ss[0], bits["0001"], t2_2);
    info.eval->add(t2_1, t2_2, ts[2]);
    
    
    // __t3 = blend(__s0@0010, __v0@0001)
    ctxt t3_1, t3_2;
    info.eval->multiply_plain(ss[0], bits["0010"], t3_1);
    info.eval->multiply_plain(vs[0], bits["0001"], t3_2);
    info.eval->add(t3_1, t3_2, ts[3]);
    
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    info.eval->multiply(vs[1], ss[1], vs[2]); // __v2 = __v1 * __s1
    info.eval->relinearize_inplace(vs[2], rk);
    return vs[2];
}
    