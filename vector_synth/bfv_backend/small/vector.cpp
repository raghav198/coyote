
#include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100100", info);
    add_bitstring(bits, "100010", info);
    add_bitstring(bits, "000101", info);
    add_bitstring(bits, "000010", info);
    add_bitstring(bits, "101001", info);
    add_bitstring(bits, "100000", info);
    add_bitstring(bits, "000001", info);
    add_bitstring(bits, "001000", info);
    add_bitstring(bits, "000110", info);
    add_bitstring(bits, "010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(24);
    ts[0] = encrypt_input("000010", info);
    ts[1] = encrypt_input("000010", info);
    ts[2] = encrypt_input("110111", info);
    ts[3] = encrypt_input("110111", info);
    ts[4] = encrypt_input("001010", info);
    ts[5] = encrypt_input("001010", info);
    ts[6] = encrypt_input("110110", info);
    ts[7] = encrypt_input("010000", info);
    ts[9] = encrypt_input("000011", info);
    ts[10] = encrypt_input("000011", info);
    ts[13] = encrypt_input("100100", info);
    ts[14] = encrypt_input("100101", info);
    ts[17] = encrypt_input("001000", info);
    ts[18] = encrypt_input("101001", info);
    ts[23] = encrypt_input("010000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[2];

    info.eval->add(ts[0], ts[1], vs[0]);      // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5

    // __t8 = blend(__v1@100100, __v0@000010, __t7@010000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[1], bits["100100"], t8_1);
    info.eval->multiply_plain(vs[0], bits["000010"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[7]}, ts[8]);

    info.eval->multiply(ts[6], ts[8], vs[3]); // __v3 = __t6 * __t8
    info.eval->relinearize_inplace(vs[3], rk);

    // __t11 = blend(__v3@010000, __t9@000011)
    ctxt t11_1;
    info.eval->multiply_plain(vs[3], bits["010000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);

    // __t12 = blend(__v1@010000, __t10@000011)
    ctxt t12_1;
    info.eval->multiply_plain(vs[1], bits["010000"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);

    info.eval->add(ts[11], ts[12], vs[4]); // __v4 = __t11 + __t12

    // __t15 = blend(__v1@000010, __v4@000001, __t13@100100)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[1], bits["000010"], t15_1);
    info.eval->multiply_plain(vs[4], bits["000001"], t15_2);
    info.eval->add_many({t15_1, t15_2, ts[13]}, ts[15]);

    // __t16 = blend(__v4@000010, __t14@100101)
    ctxt t16_1;
    info.eval->multiply_plain(vs[4], bits["000010"], t16_1);
    info.eval->add(t16_1, ts[14], ts[16]);

    info.eval->multiply(ts[15], ts[16], vs[5]); // __v5 = __t15 * __t16
    info.eval->relinearize_inplace(vs[5], rk);

    // __t19 = blend(__v5@100010, __v1@000001, __t17@001000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[5], bits["100010"], t19_1);
    info.eval->multiply_plain(vs[1], bits["000001"], t19_2);
    info.eval->add_many({t19_1, t19_2, ts[17]}, ts[19]);

    // __t20 = blend(__v2@000010, __t18@101001)
    ctxt t20_1;
    info.eval->multiply_plain(vs[2], bits["000010"], t20_1);
    info.eval->add(t20_1, ts[18], ts[20]);

    info.eval->multiply(ts[19], ts[20], vs[6]); // __v6 = __t19 * __t20
    info.eval->relinearize_inplace(vs[6], rk);

    // __t21 = blend(__v3@100000, __v2@001000, __v5@000101, __v6@000010)
    ctxt t21_1, t21_2, t21_3, t21_4;
    info.eval->multiply_plain(vs[3], bits["100000"], t21_1);
    info.eval->multiply_plain(vs[2], bits["001000"], t21_2);
    info.eval->multiply_plain(vs[5], bits["000101"], t21_3);
    info.eval->multiply_plain(vs[6], bits["000010"], t21_4);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4}, ts[21]);

    // __t22 = blend(__v6@101001, __v3@000110)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[6], bits["101001"], t22_1);
    info.eval->multiply_plain(vs[3], bits["000110"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);

    info.eval->add(ts[21], ts[22], vs[7]);        // __v7 = __t21 + __t22
    info.eval->rotate_rows(vs[7], -2, gk, ss[0]); // __s0 = __v7 >> 2
    info.eval->rotate_rows(vs[7], -1, gk, ss[1]); // __s1 = __v7 >> 1
    info.eval->multiply(ss[0], vs[7], vs[8]);     // __v8 = __s0 * __v7
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(ts[23], vs[4], vs[9]);      // __v9 = __t23 + __v4
    info.eval->multiply(ss[1], vs[9], vs[10]); // __v10 = __s1 * __v9
    info.eval->relinearize_inplace(vs[10], rk);

    return vs[10];
}
