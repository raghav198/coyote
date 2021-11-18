
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
    ts[1] = encrypt_input("1100", info);
    ts[2] = encrypt_input("0111", info);
    ts[3] = encrypt_input("111111", info);
    ts[5] = encrypt_input("111110", info);
    ts[6] = encrypt_input("1100", info);
    ts[8] = encrypt_input("0101", info);
    ts[9] = encrypt_input("0111", info);
    ts[10] = encrypt_input("1110", info);
    ts[11] = encrypt_input("1010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@10, __t2@01)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["10"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->multiply(ts[4], ts[3], vs[1]); // __v1 = __t4 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t7 = blend(__v1@01, __t6@10)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["01"], t7_1);
    info.eval->add(t7_1, ts[6], ts[7]);
    
    info.eval->multiply(ts[5], ts[7], vs[2]); // __v2 = __t5 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(ts[10], vs[1], vs[4]); // __v4 = __t10 + __v1
    info.eval->add(vs[2], vs[4], vs[5]); // __v5 = __v2 + __v4
    info.eval->multiply(vs[2], vs[3], vs[6]); // __v6 = __v2 * __v3
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -1, gk, ss[0]); // __s0 = __v6 >> 1
    info.eval->add(vs[5], ss[0], vs[7]); // __v7 = __v5 + __s0
    info.eval->multiply(vs[7], ts[11], vs[8]); // __v8 = __v7 * __t11
    info.eval->relinearize_inplace(vs[8], rk);
    return vs[8];
}
    