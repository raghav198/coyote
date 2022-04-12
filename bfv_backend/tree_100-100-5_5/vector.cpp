
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0100", info);
    add_bitstring(bits, "1000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(11);
    ts[0] = encrypt_input("111000", info);
    ts[1] = encrypt_input("110000", info);
    ts[2] = encrypt_input("0111111111", info);
    ts[3] = encrypt_input("0101111111", info);
    ts[4] = encrypt_input("111000", info);
    ts[5] = encrypt_input("011100", info);
    ts[10] = encrypt_input("110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[2];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[0]); // __s0 = __v1 >> 2
    
    // __t6 = blend(__v1@0100, __t4@1000)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["0100"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@1000, __t5@0100)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["1000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__v2@1000, __s0@0100)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["1000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["0100"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s0@1000, __v2@0100)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[0], bits["1000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["0100"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->multiply(vs[3], ts[10], vs[4]); // __v4 = __v3 * __t10
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[1]); // __s1 = __v4 >> 1
    info.eval->multiply(vs[3], ss[1], vs[5]); // __v5 = __v3 * __s1
    info.eval->relinearize_inplace(vs[5], rk);
    return vs[5];
}
    