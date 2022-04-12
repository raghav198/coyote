
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
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("1110110", info);
    ts[1] = encrypt_input("111011", info);
    ts[2] = encrypt_input("001", info);
    ts[3] = encrypt_input("00111", info);
    ts[4] = encrypt_input("0011", info);
    ts[5] = encrypt_input("1110111", info);
    ts[7] = encrypt_input("00111", info);
    ts[8] = encrypt_input("11101", info);
    ts[10] = encrypt_input("11100", info);
    ts[11] = encrypt_input("1110111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[1];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->add(vs[0], ts[2], vs[1]); // __v1 = __v0 + __t2
    info.eval->add(ts[3], vs[1], vs[2]); // __v2 = __t3 + __v1
    info.eval->add(vs[2], ts[4], vs[3]); // __v3 = __v2 + __t4
    
    // __t6 = blend(__v0@100, __v3@001)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["100"], t6_1);
    info.eval->multiply_plain(vs[3], bits["001"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[4]); // __v4 = __t5 * __t6
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t9 = blend(__v4@100, __t7@001)
    ctxt t9_1;
    info.eval->multiply_plain(vs[4], bits["100"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->add(ts[9], ts[8], vs[5]); // __v5 = __t9 + __t8
    
    // __t12 = blend(__v4@001, __t10@100)
    ctxt t12_1;
    info.eval->multiply_plain(vs[4], bits["001"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    info.eval->multiply(ts[12], ts[11], vs[6]); // __v6 = __t12 * __t11
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t13 = blend(__v6@100, __v5@001)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[6], bits["100"], t13_1);
    info.eval->multiply_plain(vs[5], bits["001"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__v5@100, __v6@001)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[5], bits["100"], t14_1);
    info.eval->multiply_plain(vs[6], bits["001"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[7]); // __v7 = __t13 * __t14
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -1, gk, ss[0]); // __s0 = __v7 >> 1
    info.eval->multiply(ss[0], vs[7], vs[8]); // __v8 = __s0 * __v7
    info.eval->relinearize_inplace(vs[8], rk);
    return vs[8];
}
    