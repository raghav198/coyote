
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "1001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("001110", info);
    ts[1] = encrypt_input("001110", info);
    ts[2] = encrypt_input("11100111", info);
    ts[3] = encrypt_input("10100111", info);
    ts[4] = encrypt_input("001100", info);
    ts[5] = encrypt_input("001010", info);
    ts[6] = encrypt_input("001100", info);
    ts[7] = encrypt_input("001110", info);
    ts[8] = encrypt_input("11100111", info);
    ts[11] = encrypt_input("10000", info);
    ts[12] = encrypt_input("111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[2];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->add(vs[2], ts[6], vs[3]); // __v3 = __v2 + __t6
    info.eval->add(vs[0], ts[7], vs[4]); // __v4 = __v0 + __t7
    
    // __t9 = blend(__v1@1001, __v3@0010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[1], bits["1001"], t9_1);
    info.eval->multiply_plain(vs[3], bits["0010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__v4@0010, __t8@1001)
    ctxt t10_1;
    info.eval->multiply_plain(vs[4], bits["0010"], t10_1);
    info.eval->add(t10_1, ts[8], ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[5]); // __v5 = __t9 * __t10
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -2, gk, ss[0]); // __s0 = __v5 >> 2
    info.eval->rotate_rows(vs[5], -1, gk, ss[1]); // __s1 = __v5 >> 1
    info.eval->add(ss[1], vs[5], vs[6]); // __v6 = __s1 + __v5
    info.eval->multiply(vs[6], ss[0], vs[7]); // __v7 = __v6 * __s0
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->add(ts[11], ts[12], vs[8]); // __v8 = __t11 + __t12
    info.eval->add(vs[8], vs[7], vs[9]); // __v9 = __v8 + __v7
    return vs[9];
}
    