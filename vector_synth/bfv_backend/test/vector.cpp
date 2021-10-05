
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000001", info);
    add_bitstring(bits, "001000", info);
    add_bitstring(bits, "010000", info);
    add_bitstring(bits, "010010", info);
    add_bitstring(bits, "000010", info);
    add_bitstring(bits, "000011", info);
    add_bitstring(bits, "100101", info);
    add_bitstring(bits, "100000", info);
    add_bitstring(bits, "000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(23);
    ts[0] = encrypt_input("111011", info);
    ts[1] = encrypt_input("111011", info);
    ts[2] = encrypt_input("010010", info);
    ts[3] = encrypt_input("010010", info);
    ts[4] = encrypt_input("000101", info);
    ts[5] = encrypt_input("000111", info);
    ts[8] = encrypt_input("011000", info);
    ts[9] = encrypt_input("011000", info);
    ts[10] = encrypt_input("010101", info);
    ts[11] = encrypt_input("000110", info);
    ts[14] = encrypt_input("010000", info);
    ts[15] = encrypt_input("010000", info);
    ts[16] = encrypt_input("100100", info);
    ts[17] = encrypt_input("100001", info);
    ts[22] = encrypt_input("100000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[5];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    
    // __t6 = blend(__v0@010010, __t4@000101)
    ctxt t6_1;
    info.eval->multiply_plain(vs[0], bits["010010"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v1@010000, __t5@000111)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["010000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    
    // __t12 = blend(__v1@000010, __t10@010101)
    ctxt t12_1;
    info.eval->multiply_plain(vs[1], bits["000010"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    
    // __t13 = blend(__v3@010000, __v2@000001, __t11@000110)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["010000"], t13_1);
    info.eval->multiply_plain(vs[2], bits["000001"], t13_2);
    info.eval->add_many({t13_1, t13_2, ts[11]}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[4]); // __v4 = __t12 * __t13
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->add(ts[14], ts[15], vs[5]); // __v5 = __t14 + __t15
    
    // __t18 = blend(__v2@010000, __v0@000001, __t16@100100)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[2], bits["010000"], t18_1);
    info.eval->multiply_plain(vs[0], bits["000001"], t18_2);
    info.eval->add_many({t18_1, t18_2, ts[16]}, ts[18]);
    
    
    // __t19 = blend(__v5@010000, __v4@000100, __t17@100001)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[5], bits["010000"], t19_1);
    info.eval->multiply_plain(vs[4], bits["000100"], t19_2);
    info.eval->add_many({t19_1, t19_2, ts[17]}, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[6]); // __v6 = __t18 * __t19
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t20 = blend(__v0@100000, __v6@010000, __v3@001000, __v2@000100, __v4@000011)
    ctxt t20_1, t20_2, t20_3, t20_4, t20_5;
    info.eval->multiply_plain(vs[0], bits["100000"], t20_1);
    info.eval->multiply_plain(vs[6], bits["010000"], t20_2);
    info.eval->multiply_plain(vs[3], bits["001000"], t20_3);
    info.eval->multiply_plain(vs[2], bits["000100"], t20_4);
    info.eval->multiply_plain(vs[4], bits["000011"], t20_5);
    info.eval->add_many({t20_1, t20_2, t20_3, t20_4, t20_5}, ts[20]);
    
    
    // __t21 = blend(__v6@100101, __v4@010000, __v0@001000, __v2@000010)
    ctxt t21_1, t21_2, t21_3, t21_4;
    info.eval->multiply_plain(vs[6], bits["100101"], t21_1);
    info.eval->multiply_plain(vs[4], bits["010000"], t21_2);
    info.eval->multiply_plain(vs[0], bits["001000"], t21_3);
    info.eval->multiply_plain(vs[2], bits["000010"], t21_4);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[7]); // __v7 = __t20 + __t21
    info.eval->rotate_rows(vs[7], -4, gk, ss[0]); // __s0 = __v7 >> 4
    info.eval->rotate_rows(vs[7], -3, gk, ss[1]); // __s1 = __v7 >> 3
    info.eval->rotate_rows(vs[7], -2, gk, ss[2]); // __s2 = __v7 >> 2
    info.eval->rotate_rows(vs[7], -1, gk, ss[3]); // __s3 = __v7 >> 1
    info.eval->rotate_rows(vs[7], -5, gk, ss[4]); // __s4 = __v7 >> 5
    info.eval->multiply(ss[3], ss[4], vs[8]); // __v8 = __s3 * __s4
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(ts[22], ss[0], vs[9]); // __v9 = __t22 + __s0
    info.eval->multiply(ss[4], vs[9], vs[10]); // __v10 = __s4 * __v9
    info.eval->relinearize_inplace(vs[10], rk);
    return vs[10];
}
    