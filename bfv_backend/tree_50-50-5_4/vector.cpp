
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000100", info);
    add_bitstring(bits, "000001", info);
    add_bitstring(bits, "100000", info);
    add_bitstring(bits, "001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("01110011111", info);
    ts[1] = encrypt_input("0111001111", info);
    ts[2] = encrypt_input("111011111100", info);
    ts[3] = encrypt_input("11101001100", info);
    ts[4] = encrypt_input("00011100", info);
    ts[5] = encrypt_input("11100000", info);
    ts[6] = encrypt_input("00111000", info);
    ts[9] = encrypt_input("00000101", info);
    ts[10] = encrypt_input("00011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[4];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->add(vs[1], ts[4], vs[2]); // __v2 = __v1 + __t4
    
    // __t7 = blend(__v1@001000, __v0@000001, __t5@100000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["001000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["000001"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    
    // __t8 = blend(__v1@100000, __s0@000001, __t6@001000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[1], bits["100000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["000001"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[6]}, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[3]); // __v3 = __t7 * __t8
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[3], ts[9], vs[4]); // __v4 = __v3 + __t9
    info.eval->rotate_rows(vs[4], -4, gk, ss[1]); // __s1 = __v4 >> 4
    
    // __t11 = blend(__v3@001000, __t10@000100)
    ctxt t11_1;
    info.eval->multiply_plain(vs[3], bits["001000"], t11_1);
    info.eval->add(t11_1, ts[10], ts[11]);
    
    
    // __t12 = blend(__s0@001000, __v2@000100)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[0], bits["001000"], t12_1);
    info.eval->multiply_plain(vs[2], bits["000100"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[5]); // __v5 = __t11 * __t12
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -4, gk, ss[2]); // __s2 = __v5 >> 4
    
    // __t13 = blend(__v3@100000, __s1@000100)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["100000"], t13_1);
    info.eval->multiply_plain(ss[1], bits["000100"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__s2@100000, __v5@000100)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[2], bits["100000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["000100"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[6]); // __v6 = __t13 * __t14
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -3, gk, ss[3]); // __s3 = __v6 >> 3
    info.eval->multiply(vs[6], ss[3], vs[7]); // __v7 = __v6 * __s3
    info.eval->relinearize_inplace(vs[7], rk);
    return vs[7];
}
    