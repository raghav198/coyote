
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01", info);
    add_bitstring(bits, "10", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("111111", info);
    ts[1] = encrypt_input("1111", info);
    ts[2] = encrypt_input("111111", info);
    ts[3] = encrypt_input("101101", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t4 = blend(__v1@10, __v0@01)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[1], bits["10"], t4_1);
    info.eval->multiply_plain(vs[0], bits["01"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__v0@10, __v1@01)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[0], bits["10"], t5_1);
    info.eval->multiply_plain(vs[1], bits["01"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[0]); // __s0 = __v2 >> 1
    info.eval->add(ss[0], vs[2], vs[3]); // __v3 = __s0 + __v2
    return vs[3];
}
    