#include <algorithm>

#include "runtime.hpp"

using ctxt_vec = ckks_vector<int>;

template <>
ctxt_vec CoyoteContext<int, mul_depth_accumulator>::add(ctxt_vec a, ctxt_vec b)
{
    return ctxt_vec {
        .ctxt = context->EvalAdd(a.ctxt, b.ctxt),
        .noise = noise_accumulator.add(a.noise, b.noise)
    };
}

template <>
ctxt_vec CoyoteContext<int, mul_depth_accumulator>::mul(ctxt_vec a, ctxt_vec b)
{
    return ctxt_vec {
        .ctxt = context->EvalMultAndRelinearize(a.ctxt, b.ctxt),
        .noise = noise_accumulator.mul(a.noise, b.noise)
    };
}

template <>
ctxt_vec CoyoteContext<int, mul_depth_accumulator>::sub(ctxt_vec a, ctxt_vec b)
{
    return ctxt_vec {
        .ctxt = context->EvalSub(a.ctxt, b.ctxt),
        .noise = noise_accumulator.sub(a.noise, b.noise)
    };
}

template <>
ctxt_vec CoyoteContext<int, mul_depth_accumulator>::rotate(ctxt_vec val, int amount)
{
    return ctxt_vec {
        .ctxt = context->EvalRotate(val.ctxt, -amount),
        .noise = noise_accumulator.rotate(val.noise, amount)
    };
}

template <>
ctxt_vec CoyoteContext<int, mul_depth_accumulator>::blend(std::vector<std::pair<ctxt_vec, lbcrypto::Plaintext>> sources)
{

    std::vector<lbcrypto::Ciphertext<encoding>> blended_sources(sources.size());
    int index = 0;
    
    for (auto [ctxt, mask] : sources) // TODO: replace this with a parallel for
        blended_sources[index++] = context->EvalMult(ctxt.ctxt, mask);

    std::vector<std::pair<int, lbcrypto::Plaintext>> source_noises;
    std::transform(sources.begin(), sources.end(), std::back_inserter(source_noises), [](std::pair<ctxt_vec, lbcrypto::Plaintext> source) {
        return std::make_pair(source.first.noise, source.second);
    });

    return ctxt_vec {
        .ctxt = context->EvalAddMany(blended_sources),
        .noise = noise_accumulator.blend(source_noises)
    };
}