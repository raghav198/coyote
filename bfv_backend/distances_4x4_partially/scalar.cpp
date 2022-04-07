
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 56;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"distances_4x4_partially(ys):2", "distances_4x4_partially(xs):1", "distances_4x4_partially(xs):0", "distances_4x4_partially(ys):3", "distances_4x4_partially(xs):2", "distances_4x4_partially(xs):3", "distances_4x4_partially(ys):1", "distances_4x4_partially(ys):0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["distances_4x4_partially(xs):0"];
    regs[1] = locs["distances_4x4_partially(ys):0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["distances_4x4_partially(ys):1"];
    info.eval->sub(regs[0], regs[5], regs[6]);
    info.eval->sub(regs[0], regs[5], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["distances_4x4_partially(ys):2"];
    info.eval->sub(regs[0], regs[9], regs[10]);
    info.eval->sub(regs[0], regs[9], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["distances_4x4_partially(ys):3"];
    info.eval->sub(regs[0], regs[13], regs[14]);
    info.eval->sub(regs[0], regs[13], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["distances_4x4_partially(xs):1"];
    info.eval->sub(regs[17], regs[1], regs[18]);
    info.eval->sub(regs[17], regs[1], regs[19]);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->sub(regs[17], regs[5], regs[21]);
    info.eval->sub(regs[17], regs[5], regs[22]);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->sub(regs[17], regs[9], regs[24]);
    info.eval->sub(regs[17], regs[9], regs[25]);
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->sub(regs[17], regs[13], regs[27]);
    info.eval->sub(regs[17], regs[13], regs[28]);
    info.eval->multiply(regs[27], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    regs[30] = locs["distances_4x4_partially(xs):2"];
    info.eval->sub(regs[30], regs[1], regs[31]);
    info.eval->sub(regs[30], regs[1], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->sub(regs[30], regs[5], regs[34]);
    info.eval->sub(regs[30], regs[5], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->sub(regs[30], regs[9], regs[37]);
    info.eval->sub(regs[30], regs[9], regs[38]);
    info.eval->multiply(regs[37], regs[38], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->sub(regs[30], regs[13], regs[40]);
    info.eval->sub(regs[30], regs[13], regs[41]);
    info.eval->multiply(regs[40], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    regs[43] = locs["distances_4x4_partially(xs):3"];
    info.eval->sub(regs[43], regs[1], regs[44]);
    info.eval->sub(regs[43], regs[1], regs[45]);
    info.eval->multiply(regs[44], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->sub(regs[43], regs[5], regs[47]);
    info.eval->sub(regs[43], regs[5], regs[48]);
    info.eval->multiply(regs[47], regs[48], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->sub(regs[43], regs[9], regs[50]);
    info.eval->sub(regs[43], regs[9], regs[51]);
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->sub(regs[43], regs[13], regs[53]);
    info.eval->sub(regs[43], regs[13], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[8]);
    answer.push_back(regs[12]);
    answer.push_back(regs[16]);
    answer.push_back(regs[20]);
    answer.push_back(regs[23]);
    answer.push_back(regs[26]);
    answer.push_back(regs[29]);
    answer.push_back(regs[33]);
    answer.push_back(regs[36]);
    answer.push_back(regs[39]);
    answer.push_back(regs[42]);
    answer.push_back(regs[46]);
    answer.push_back(regs[49]);
    answer.push_back(regs[52]);
    answer.push_back(regs[55]);
    return answer;
}
    