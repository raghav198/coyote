
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10", info);
    add_bitstring(bits, "01", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("110", info);
    ts[1] = encrypt_input("1110", info);
    ts[2] = encrypt_input("111111", info);
    ts[3] = encrypt_input("1011011", info);
    ts[4] = encrypt_input("0111", info);
    ts[6] = encrypt_input("11111", info);
    ts[7] = encrypt_input("1110", info);
    ts[8] = encrypt_input("0101", info);
    ts[11] = encrypt_input("110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t5 = blend(__v0@10, __t4@01)
    ctxt t5_1;
    info.eval->multiply_plain(vs[0], bits["10"], t5_1);
    info.eval->add(t5_1, ts[4], ts[5]);
    
    info.eval->multiply(vs[1], ts[5], vs[2]); // __v2 = __v1 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(ts[6], vs[2], vs[3]); // __v3 = __t6 + __v2
    
    // __t9 = blend(__v3@01, __t7@10)
    ctxt t9_1;
    info.eval->multiply_plain(vs[3], bits["01"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    
    // __t10 = blend(__v3@10, __t8@01)
    ctxt t10_1;
    info.eval->multiply_plain(vs[3], bits["10"], t10_1);
    info.eval->add(t10_1, ts[8], ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[4]); // __v4 = __t9 * __t10
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[0]); // __s0 = __v4 >> 1
    info.eval->add(vs[4], ss[0], vs[5]); // __v5 = __v4 + __s0
    info.eval->multiply(ts[11], vs[5], vs[6]); // __v6 = __t11 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    