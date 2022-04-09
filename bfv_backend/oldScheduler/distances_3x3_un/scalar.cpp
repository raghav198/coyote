
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 33;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"distances_3x3_un(xs):2", "distances_3x3_un(xs):1", "distances_3x3_un(ys):0", "distances_3x3_un(ys):2", "distances_3x3_un(ys):1", "distances_3x3_un(xs):0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["distances_3x3_un(xs):0"];
    regs[1] = locs["distances_3x3_un(ys):0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["distances_3x3_un(ys):1"];
    info.eval->sub(regs[0], regs[5], regs[6]);
    info.eval->sub(regs[0], regs[5], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["distances_3x3_un(ys):2"];
    info.eval->sub(regs[0], regs[9], regs[10]);
    info.eval->sub(regs[0], regs[9], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["distances_3x3_un(xs):1"];
    info.eval->sub(regs[13], regs[1], regs[14]);
    info.eval->sub(regs[13], regs[1], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->sub(regs[13], regs[5], regs[17]);
    info.eval->sub(regs[13], regs[5], regs[18]);
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->sub(regs[13], regs[9], regs[20]);
    info.eval->sub(regs[13], regs[9], regs[21]);
    info.eval->multiply(regs[20], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    regs[23] = locs["distances_3x3_un(xs):2"];
    info.eval->sub(regs[23], regs[1], regs[24]);
    info.eval->sub(regs[23], regs[1], regs[25]);
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->sub(regs[23], regs[5], regs[27]);
    info.eval->sub(regs[23], regs[5], regs[28]);
    info.eval->multiply(regs[27], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->sub(regs[23], regs[9], regs[30]);
    info.eval->sub(regs[23], regs[9], regs[31]);
    info.eval->multiply(regs[30], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[8]);
    answer.push_back(regs[12]);
    answer.push_back(regs[16]);
    answer.push_back(regs[19]);
    answer.push_back(regs[22]);
    answer.push_back(regs[26]);
    answer.push_back(regs[29]);
    answer.push_back(regs[32]);
    return answer;
}
    