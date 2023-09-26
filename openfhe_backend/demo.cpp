#include <iostream>
#include <openfhe.h>
#include <vector>

int main()
{
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


    return 0;
    
}