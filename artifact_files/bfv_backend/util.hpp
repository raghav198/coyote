#pragma once

#include <chrono>
#include <memory>
#include <seal/seal.h>
using ctxt = seal::Ciphertext;
using ptxt = seal::Plaintext;

struct Keys
{
    seal::RelinKeys rk;
    seal::GaloisKeys gk;

    Keys(seal::KeyGenerator &keygen)
    {
        keygen.create_relin_keys(rk);
        keygen.create_galois_keys(gk);
    }
};

struct RuntimeContext
{
    std::unique_ptr<seal::BatchEncoder> batcher;
    std::unique_ptr<seal::Encryptor> enc;
    std::unique_ptr<seal::Decryptor> dec;
    std::unique_ptr<seal::Evaluator> eval;
    std::unique_ptr<Keys> keys;

    RuntimeContext(seal::EncryptionParameters params)
    {
        seal::SEALContext context(params);
        seal::KeyGenerator keygen(context);

        seal::SecretKey sk = keygen.secret_key();
        seal::PublicKey pk;
        keygen.create_public_key(pk);
        keys = std::make_unique<Keys>(keygen);

        enc = std::make_unique<seal::Encryptor>(context, pk);
        dec = std::make_unique<seal::Decryptor>(context, sk);
        eval = std::make_unique<seal::Evaluator>(context);
        batcher = std::make_unique<seal::BatchEncoder>(context);
    }
};

ptxt encode_bits(std::string bitstring, RuntimeContext &info);
ctxt encrypt_input(std::string bitstring, RuntimeContext &info);
void add_bitstring(std::map<std::string, ptxt> &bits, std::string bitstring, RuntimeContext &info);
