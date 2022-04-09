
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1110", info);
    ts[1] = encrypt_input("1010", info);
    ts[2] = encrypt_input("01011", info);
    ts[3] = encrypt_input("0111", info);
    ts[4] = encrypt_input("0110", info);
    ts[5] = encrypt_input("0111", info);
    ts[6] = encrypt_input("1110", info);
    ts[7] = encrypt_input("10010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    
    // __t8 = blend(__v2@01, __t6@10)
    ctxt t8_1;
    info.eval->multiply_plain(vs[2], bits["01"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    
    // __t9 = blend(__v1@01, __t7@10)
    ctxt t9_1;
    info.eval->multiply_plain(vs[1], bits["01"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[0], vs[3], vs[4]); // __v4 = __v0 + __v3
    info.eval->rotate_rows(vs[4], -1, gk, ss[0]); // __s0 = __v4 >> 1
    info.eval->multiply(vs[3], ss[0], vs[5]); // __v5 = __v3 * __s0
    info.eval->relinearize_inplace(vs[5], rk);
    return vs[5];
}
    