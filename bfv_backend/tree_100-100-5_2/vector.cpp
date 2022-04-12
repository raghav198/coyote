
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
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("111111", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("1110", info);
    ts[3] = encrypt_input("110111", info);
    ts[5] = encrypt_input("111111", info);
    ts[6] = encrypt_input("0101", info);
    ts[8] = encrypt_input("0111", info);
    ts[10] = encrypt_input("1100", info);
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
    
    // __t4 = blend(__v0@01, __t2@10)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["01"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->add(ts[4], ts[3], vs[1]); // __v1 = __t4 + __t3
    
    // __t7 = blend(__v1@10, __t6@01)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["10"], t7_1);
    info.eval->add(t7_1, ts[6], ts[7]);
    
    info.eval->multiply(ts[5], ts[7], vs[2]); // __v2 = __t5 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t9 = blend(__v0@10, __t8@01)
    ctxt t9_1;
    info.eval->multiply_plain(vs[0], bits["10"], t9_1);
    info.eval->add(t9_1, ts[8], ts[9]);
    
    info.eval->multiply(vs[2], ts[9], vs[3]); // __v3 = __v2 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t11 = blend(__v3@10, __v1@01)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[3], bits["10"], t11_1);
    info.eval->multiply_plain(vs[1], bits["01"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    
    // __t12 = blend(__v3@01, __t10@10)
    ctxt t12_1;
    info.eval->multiply_plain(vs[3], bits["01"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[4]); // __v4 = __t11 * __t12
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[0]); // __s0 = __v4 >> 1
    info.eval->multiply(ss[0], vs[4], vs[5]); // __v5 = __s0 * __v4
    info.eval->relinearize_inplace(vs[5], rk);
    return vs[5];
}
    