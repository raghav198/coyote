#include <iostream>
#include "runtime.hpp"

// #define MANUAL_TEST
#define COYOTE_RUNTIME_TEST

int main()
{
#ifdef MANUAL_TEST
    std::cout << "Manual test\n";
    lbcrypto::CCParams<lbcrypto::CryptoContextCKKSRNS> params;
    params.SetSecretKeyDist(lbcrypto::UNIFORM_TERNARY);
    
    auto context = lbcrypto::GenCryptoContext(params);

    context->Enable(lbcrypto::PKE);
    context->Enable(lbcrypto::KEYSWITCH);
    context->Enable(lbcrypto::LEVELEDSHE);
    context->Enable(lbcrypto::FHE);

    auto keypair = context->KeyGen();
    context->EvalMultKeyGen(keypair.secretKey);

    std::vector<double> x = {0.25, 0.5, 0.75, 1.0, 2.0, 4.0, 8.0, 16.0};
    auto ptxt = context->MakeCKKSPackedPlaintext(x);
    ptxt->SetLength(x.size());
    
    auto ctxt = context->Encrypt(keypair.publicKey, ptxt);

    std::cout << "Encoded: " << ptxt << "\n";
    std::cout << "Encrypted level: " << ctxt->GetLevel() << "\n";

    auto square = context->EvalSquare(ctxt);
    
    lbcrypto::Plaintext result;
    context->Decrypt(keypair.secretKey, square, &result);
    result->SetLength(x.size());

    std::cout << "Result: " << result << "\n";
#endif

#ifdef INPUT_HANDLER_TEST
    std::cout << "Input handler test\n";

    input_handler<double> handler;
    handler.add_matrix("matmul(A)", {
        {1, 2, 3},
        {4, 5, 6},
        {7, 8, 9}
    });
    handler.add_vector("matmul(b)", {-1, -2, -3});

    std::cout << "matmul(A):0,2 = " << handler.get("matmul(A):0,2") << "\n";
    std::cout << "matmul(b):1 = " << handler.get("matmul(b):1") << "\n";
#endif

#ifdef COYOTE_RUNTIME_TEST
    std::cout << "Coyote runtime test\n";

    lbcrypto::CCParams<lbcrypto::CryptoContextCKKSRNS> params;
    params.SetSecretKeyDist(lbcrypto::UNIFORM_TERNARY);

    CoyoteContext<int, mul_depth_accumulator> context(params);
    std::vector<double> x = {0.25, 0.5, 0.75, 1.0, 2.0, 4.0, 8.0, 16.0};
    
    auto ctxt = context.encrypt(x);
    auto square = context.mul(ctxt, ctxt);
    auto result = context.decrypt(square, x.size());

    std::cout << "[ ";
    for (auto val : result) std::cout << val << " ";
    std::cout << "]\n";



#endif

    return 0;
}