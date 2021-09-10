#include "scalar.hpp"
#include "util.hpp"
#include "vector.hpp"
#include <chrono>

using _clock = std::chrono::high_resolution_clock;
using ms = std::chrono::milliseconds;
constexpr int ITERATIONS = 50;

int main()
{
    seal::EncryptionParameters params(seal::scheme_type::bfv);
    size_t poly_modulus_degree = 8192;
    params.set_poly_modulus_degree(poly_modulus_degree);
    params.set_coeff_modulus(seal::CoeffModulus::BFVDefault(poly_modulus_degree));
    params.set_plain_modulus(seal::PlainModulus::Batching(poly_modulus_degree, 20));

    RuntimeContext info(params);

    ScalarProgram scal;
    VectorProgram vec;

    auto start = _clock::now();
    for (int i = 0; i < ITERATIONS; i++)
        vec.run(info);
    auto end = _clock::now();
    std::cout << "Vector took " << std::chrono::duration_cast<ms>(end - start).count() << "ms\n";

    start = _clock::now();
    for (int i = 0; i < ITERATIONS; i++)
        scal.run(info);
    end = _clock::now();
    std::cout << "Scalar took " << std::chrono::duration_cast<ms>(end - start).count() << "ms\n";

    return 0;
}
