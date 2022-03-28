#include "scalar.hpp"
#include "util.hpp"
#include "vector.hpp"
#include <chrono>
#include <iostream>
#include <fstream>
#include <string>

using _clock = std::chrono::high_resolution_clock;
using ms = std::chrono::milliseconds;
constexpr int ITERATIONS = 50;

int main()
{ 
std::ofstream myfile("dot_product6x6.csv");
myfile << "VEC,ENC,RUN,ENC + RUN,SCAL,ENC,RUN,ENC + RUN,\n";
for (int runs = 0; runs < 50; runs++) {
    seal::EncryptionParameters params(seal::scheme_type::bfv);
    size_t poly_modulus_degree = 8192;
    params.set_poly_modulus_degree(poly_modulus_degree);
    params.set_coeff_modulus(seal::CoeffModulus::BFVDefault(poly_modulus_degree));
    params.set_plain_modulus(seal::PlainModulus::Batching(poly_modulus_degree, 20));

    RuntimeContext info(params);

    ScalarProgram scal(info);
    VectorProgram vec(info);

    long long   vector_enc_time = 0,
                vector_run_time = 0,
                scalar_enc_time = 0,
                scalar_run_time = 0;

    auto chkpoint = _clock::now();
    for (int i = 0; i < ITERATIONS; i++)
    {
        chkpoint = _clock::now();
        vec.setup();
        vector_enc_time += std::chrono::duration_cast<ms>(_clock::now() - chkpoint).count();
        chkpoint = _clock::now();
        vec.run();
        vector_run_time += std::chrono::duration_cast<ms>(_clock::now() - chkpoint).count();
    }
        

    // std::cout << "Vector took " << std::chrono::duration_cast<ms>(end - start).count() << "ms\n";
    std::cout << "Vector took (enc, run, enc + run) = (" 
            << vector_enc_time << ", " 
            << vector_run_time << ", " 
            << vector_enc_time + vector_run_time << ")\n";

    // start = _clock::now();
    for (int i = 0; i < ITERATIONS; i++)
    {
        chkpoint = _clock::now();
        scal.setup();
        scalar_enc_time += std::chrono::duration_cast<ms>(_clock::now() - chkpoint).count();
        chkpoint = _clock::now();
        scal.run();
        scalar_run_time += std::chrono::duration_cast<ms>(_clock::now() - chkpoint).count();
    }
    // end = _clock::now();
    // std::cout << "Scalar took " << std::chrono::duration_cast<ms>(end - start).count() << "ms\n";
    std::cout << "Scalar took (enc, run, enc + run) = (" 
            << scalar_enc_time << ", " 
            << scalar_run_time << ", " 
            << scalar_enc_time + scalar_run_time << ")\n";
    myfile << ("v," + std::to_string(vector_enc_time) + "," + std::to_string(vector_run_time) + "," + std::to_string(vector_run_time + vector_enc_time) + "," + "s," + std::to_string(scalar_enc_time) + "," + std::to_string(scalar_run_time) + "," + std::to_string(scalar_run_time + scalar_enc_time) + "," + "\n");
}
myfile.close();
return 0;

}
