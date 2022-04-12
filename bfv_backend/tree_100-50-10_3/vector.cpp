
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100", info);
    add_bitstring(bits, "001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("1110111", info);
    ts[1] = encrypt_input("1110111", info);
    ts[2] = encrypt_input("01110", info);
    ts[3] = encrypt_input("01110", info);
    ts[4] = encrypt_input("1111110", info);
    ts[5] = encrypt_input("0111111", info);
    ts[8] = encrypt_input("01110", info);
    ts[9] = encrypt_input("1110111", info);
    ts[10] = encrypt_input("11100", info);
    ts[11] = encrypt_input("01110", info);
    ts[12] = encrypt_input("01110", info);
    ts[13] = encrypt_input("01110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[2];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    
    // __t6 = blend(__v0@001, __t4@110)
    ctxt t6_1;
    info.eval->multiply_plain(vs[0], bits["001"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@100, __t5@011)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["100"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(vs[1], vs[2], vs[3]); // __v3 = __v1 + __v2
    info.eval->add(ts[8], vs[3], vs[4]); // __v4 = __t8 + __v3
    info.eval->multiply(vs[2], ts[9], vs[5]); // __v5 = __v2 * __t9
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -2, gk, ss[0]); // __s0 = __v5 >> 2
    info.eval->multiply(vs[5], ts[10], vs[6]); // __v6 = __v5 * __t10
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -1, gk, ss[1]); // __s1 = __v6 >> 1
    info.eval->multiply(ts[11], ss[1], vs[7]); // __v7 = __t11 * __s1
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->add(vs[7], ss[0], vs[8]); // __v8 = __v7 + __s0
    info.eval->add(ts[12], vs[8], vs[9]); // __v9 = __t12 + __v8
    info.eval->add(ts[13], vs[9], vs[10]); // __v10 = __t13 + __v9
    info.eval->add(vs[4], vs[10], vs[11]); // __v11 = __v4 + __v10
    return vs[11];
}
    