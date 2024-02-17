
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
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("111110", info);
    ts[1] = encrypt_input("111110", info);
    ts[2] = encrypt_input("111111", info);
    ts[3] = encrypt_input("111111", info);
    ts[4] = encrypt_input("111111", info);
    ts[5] = encrypt_input("111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[1];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v0@10, __v1@01)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["10"], t6_1);
    info.eval->multiply_plain(vs[1], bits["01"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(vs[2], ts[6], vs[3]); // __v3 = __v2 + __t6
    
    // __t7 = blend(__v1@10, __v0@01)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["10"], t7_1);
    info.eval->multiply_plain(vs[0], bits["01"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[7], vs[3], vs[4]); // __v4 = __t7 + __v3
    info.eval->rotate_rows(vs[4], -1, gk, ss[0]); // __s0 = __v4 >> 1
    info.eval->add(ss[0], vs[4], vs[5]); // __v5 = __s0 + __v4
    return vs[5];
}
    