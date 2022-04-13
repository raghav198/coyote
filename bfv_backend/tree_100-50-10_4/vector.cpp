
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01000", info);
    add_bitstring(bits, "00010", info);
    add_bitstring(bits, "00001", info);
    add_bitstring(bits, "10001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("000111111", info);
    ts[1] = encrypt_input("000111111", info);
    ts[2] = encrypt_input("1011110011", info);
    ts[3] = encrypt_input("111111000", info);
    ts[5] = encrypt_input("0001010", info);
    ts[6] = encrypt_input("101000111", info);
    ts[9] = encrypt_input("0101100111", info);
    ts[11] = encrypt_input("01100110", info);
    ts[12] = encrypt_input("011100111", info);
    ts[13] = encrypt_input("0111000", info);
    ts[16] = encrypt_input("1110000", info);
    ts[17] = encrypt_input("1110000", info);
    ts[18] = encrypt_input("1110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[13];
    ctxt ss[2];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    
    // __t4 = blend(__v0@00001, __t3@11000)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["00001"], t4_1);
    info.eval->add(t4_1, ts[3], ts[4]);
    
    info.eval->multiply(ts[2], ts[4], vs[1]); // __v1 = __t2 * __t4
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t7 = blend(__v1@10001, __t5@00010)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["10001"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    
    // __t8 = blend(__v0@00010, __t6@10001)
    ctxt t8_1;
    info.eval->multiply_plain(vs[0], bits["00010"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    info.eval->add(ts[7], ts[8], vs[2]); // __v2 = __t7 + __t8
    
    // __t10 = blend(__v1@01000, __v2@00001)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[1], bits["01000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["00001"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    info.eval->multiply(ts[10], ts[9], vs[3]); // __v3 = __t10 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(ts[11], ts[12], vs[4]); // __v4 = __t11 + __t12
    info.eval->add(vs[4], vs[3], vs[5]); // __v5 = __v4 + __v3
    
    // __t14 = blend(__v5@01000, __v4@00001)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[5], bits["01000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["00001"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v3@00001, __t13@01000)
    ctxt t15_1;
    info.eval->multiply_plain(vs[3], bits["00001"], t15_1);
    info.eval->add(t15_1, ts[13], ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[6]); // __v6 = __t14 * __t15
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -4, gk, ss[0]); // __s0 = __v6 >> 4
    info.eval->multiply(ss[0], vs[2], vs[7]); // __v7 = __s0 * __v2
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -2, gk, ss[1]); // __s1 = __v7 >> 2
    info.eval->multiply(ss[1], vs[2], vs[8]); // __v8 = __s1 * __v2
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(vs[8], ts[16], vs[9]); // __v9 = __v8 + __t16
    info.eval->multiply(vs[9], ss[0], vs[10]); // __v10 = __v9 * __s0
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->add(ts[17], ts[18], vs[11]); // __v11 = __t17 + __t18
    info.eval->add(vs[11], vs[10], vs[12]); // __v12 = __v11 + __v10
    return vs[12];
}
    