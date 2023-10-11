#pragma once

#include <openfhe.h>

#include <vector>
#include <unordered_map>
#include <utility>

template <typename value_type>
struct matrix
{
    int rows, cols;
    std::unordered_map<size_t, std::unordered_map<size_t, value_type>> data;
};

template <typename value_type>
struct input_handler
{
    std::unordered_map<std::string, value_type> scalars;
    std::unordered_map<std::string, std::vector<value_type>> vectors;
    std::unordered_map<std::string, matrix<value_type>> matrices;

    void add_scalar(std::string name, value_type value)
    {
        scalars[name] = value;
    }

    void add_vector(std::string name, std::vector<value_type> values)
    {
        vectors[name] = values;
    }

    void add_matrix(std::string name, std::vector<std::vector<value_type>> values)
    {
        matrices[name] = matrix<value_type>();
        matrices[name].rows = values.size();
        for (size_t row = 0; row < values.size(); row++) {
            for (size_t col = 0; col < values[row].size(); col++) {
                matrices[name].data[row][col] = values[row][col];
            }
        }
    }
    
    value_type get(std::string id)
    {
        size_t index_start, col_start;
        if ((index_start = id.find(':')) == std::string::npos) {
            return scalars[id];
        }
        if ((col_start = id.find(',', index_start)) == std::string::npos) {
            size_t index = std::stoi(id.substr(index_start + 1));
            return vectors[id.substr(0, index_start)][index];
        }

        auto row = id.substr(index_start + 1, col_start - index_start - 1);
        auto col = id.substr(col_start + 1);

        return matrices[id.substr(0, index_start)].data[std::stoi(row)][std::stoi(col)];
    }
};

using encoding = lbcrypto::DCRTPoly;

template <typename noise_t>
struct ckks_vector
{
    lbcrypto::Ciphertext<encoding> ctxt;
    noise_t noise;
};

template <typename eval_type>
struct circuit_eval
{
    virtual eval_type add(eval_type a, eval_type b) = 0;
    virtual eval_type sub(eval_type a, eval_type b) = 0;
    virtual eval_type mul(eval_type a, eval_type b) = 0;
    virtual eval_type rotate(eval_type val, int amount) = 0;
    virtual eval_type blend(std::vector<std::pair<eval_type, lbcrypto::Plaintext>> sources) = 0;
};

struct mul_depth_accumulator : public circuit_eval<int>
{
    int add(int a, int b) { return std::max(a, b); }
    int sub(int a, int b) { return std::max(a, b); }
    int mul(int a, int b) { return 1 + std::max(a, b); }
    int rotate(int val, int amount) { return val; }
    int blend(std::vector<std::pair<int, lbcrypto::Plaintext>> sources)
    {
        int max = 0;
        for (auto [depth, mask] : sources)
            max = std::max(max, depth);
        return max;
    }
};

template <typename noise_t, typename noise_acc_t>
struct CoyoteContext : public circuit_eval<ckks_vector<noise_t>>
{
    using ctxt_vec = ckks_vector<noise_t>;
    lbcrypto::CryptoContext<encoding> context;
    lbcrypto::KeyPair<encoding> keypair;

    CoyoteContext(lbcrypto::CCParams<lbcrypto::CryptoContextCKKSRNS> params) :
        context(lbcrypto::GenCryptoContext(params))
    {
        context->Enable(lbcrypto::PKE);
        context->Enable(lbcrypto::KEYSWITCH);
        context->Enable(lbcrypto::LEVELEDSHE);
        context->Enable(lbcrypto::FHE);

        keypair = context->KeyGen();
        context->EvalMultKeyGen(keypair.secretKey);
    }

    noise_acc_t noise_accumulator;

    ctxt_vec add(ctxt_vec a, ctxt_vec b);
    ctxt_vec sub(ctxt_vec a, ctxt_vec b);
    ctxt_vec mul(ctxt_vec a, ctxt_vec b);
    ctxt_vec rotate(ctxt_vec val, int amount);
    ctxt_vec blend(std::vector<std::pair<ctxt_vec, lbcrypto::Plaintext>> sources);

    ctxt_vec encrypt(std::vector<double> ptxt)
    {
        auto packed_ptxt = context->MakeCKKSPackedPlaintext(ptxt);
        packed_ptxt->SetLength(ptxt.size());
        return {
            .ctxt = context->Encrypt(keypair.publicKey, packed_ptxt)
        };
    }

    std::vector<double> decrypt(ctxt_vec ctxt, size_t length = -1)
    {
        lbcrypto::Plaintext result;
        context->Decrypt(keypair.secretKey, ctxt.ctxt, &result);
        if (length != -1) result->SetLength(length);
        return result->GetRealPackedValue();
    }
};

template struct CoyoteContext<int, mul_depth_accumulator>;