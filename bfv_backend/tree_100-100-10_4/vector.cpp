
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00010010", info);
    add_bitstring(bits, "00010000", info);
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "10000100", info);
    add_bitstring(bits, "00000010", info);
    add_bitstring(bits, "00000001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("11100001110111", info);
    ts[1] = encrypt_input("1100001110111", info);
    ts[2] = encrypt_input("1111111111111101101110", info);
    ts[3] = encrypt_input("0111111111100110", info);
    ts[5] = encrypt_input("00111111001110", info);
    ts[7] = encrypt_input("0011100000", info);
    ts[10] = encrypt_input("0000000111", info);
    ts[11] = encrypt_input("000111000111", info);
    ts[12] = encrypt_input("001110001110", info);
    ts[15] = encrypt_input("0011100000", info);
    ts[16] = encrypt_input("0011100000", info);
    ts[17] = encrypt_input("0011100000", info);
    ts[18] = encrypt_input("0000001110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[4];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@10000100, __t3@01111010)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["10000100"], t4_1);
    info.eval->add(t4_1, ts[3], ts[4]);
    
    info.eval->multiply(ts[2], ts[4], vs[1]); // __v1 = __t2 * __t4
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[0]); // __s0 = __v1 >> 2
    
    // __t6 = blend(__v1@00100000, __s0@00010010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[1], bits["00100000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["00010010"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->multiply(ts[6], ts[5], vs[2]); // __v2 = __t6 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(vs[2], ss[0], vs[3]); // __v3 = __v2 + __s0
    
    // __t8 = blend(__v3@00100000, __v0@00000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["00100000"], t8_1);
    info.eval->multiply_plain(vs[0], bits["00000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s0@00000001, __t7@00100000)
    ctxt t9_1;
    info.eval->multiply_plain(ss[0], bits["00000001"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->add(vs[4], ts[10], vs[5]); // __v5 = __v4 + __t10
    
    // __t13 = blend(__v4@00100000, __v2@00000010, __t11@00010001)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[4], bits["00100000"], t13_1);
    info.eval->multiply_plain(vs[2], bits["00000010"], t13_2);
    info.eval->add_many({t13_1, t13_2, ts[11]}, ts[13]);
    
    
    // __t14 = blend(__v1@00010000, __v5@00000001, __t12@00100010)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[1], bits["00010000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["00000001"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[6]); // __v6 = __t13 * __t14
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -7, gk, ss[1]); // __s1 = __v6 >> 7
    info.eval->add(vs[2], vs[6], vs[7]); // __v7 = __v2 + __v6
    info.eval->rotate_rows(vs[7], -7, gk, ss[2]); // __s2 = __v7 >> 7
    info.eval->multiply(ss[1], vs[1], vs[8]); // __v8 = __s1 * __v1
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(ss[2], ts[15], vs[9]); // __v9 = __s2 + __t15
    info.eval->add(ts[16], vs[9], vs[10]); // __v10 = __t16 + __v9
    info.eval->add(vs[10], vs[6], vs[11]); // __v11 = __v10 + __v6
    info.eval->add(vs[11], ts[17], vs[12]); // __v12 = __v11 + __t17
    info.eval->rotate_rows(vs[12], -4, gk, ss[3]); // __s3 = __v12 >> 4
    info.eval->multiply(ss[3], vs[8], vs[13]); // __v13 = __s3 * __v8
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->multiply(vs[13], ts[18], vs[14]); // __v14 = __v13 * __t18
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(vs[6], vs[14], vs[15]); // __v15 = __v6 * __v14
    info.eval->relinearize_inplace(vs[15], rk);
    return vs[15];
}
    