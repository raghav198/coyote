
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1110", info);
    ts[1] = encrypt_input("1110", info);
    ts[2] = encrypt_input("1110", info);
    ts[3] = encrypt_input("1110", info);
    ts[4] = encrypt_input("01011", info);
    ts[5] = encrypt_input("0110", info);
    ts[8] = encrypt_input("0111", info);
    ts[9] = encrypt_input("0111", info);
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
    
    // __t6 = blend(__v1@10, __t4@01)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["10"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@10, __t5@01)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["10"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    info.eval->multiply(vs[2], vs[3], vs[4]); // __v4 = __v2 * __v3
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[0]); // __s0 = __v4 >> 1
    info.eval->multiply(ss[0], vs[2], vs[5]); // __v5 = __s0 * __v2
    info.eval->relinearize_inplace(vs[5], rk);
    return vs[5];
}
    