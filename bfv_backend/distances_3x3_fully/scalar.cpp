
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 39;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"distances_3x3_fully(ys):1", "distances_3x3_fully(xs):1", "distances_3x3_fully(xs):2", "distances_3x3_fully(xs):0", "distances_3x3_fully(ys):0", "distances_3x3_fully(ys):2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["distances_3x3_fully(xs):0"];
    regs[1] = locs["distances_3x3_fully(ys):0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["distances_3x3_fully(ys):1"];
    info.eval->sub(regs[0], regs[5], regs[6]);
    info.eval->sub(regs[0], regs[5], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["distances_3x3_fully(ys):2"];
    info.eval->sub(regs[0], regs[9], regs[10]);
    info.eval->sub(regs[0], regs[9], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["distances_3x3_fully(xs):1"];
    regs[14] = locs["distances_3x3_fully(ys):0"];
    info.eval->sub(regs[13], regs[14], regs[15]);
    info.eval->sub(regs[13], regs[14], regs[16]);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    regs[18] = locs["distances_3x3_fully(ys):1"];
    info.eval->sub(regs[13], regs[18], regs[19]);
    info.eval->sub(regs[13], regs[18], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["distances_3x3_fully(ys):2"];
    info.eval->sub(regs[13], regs[22], regs[23]);
    info.eval->sub(regs[13], regs[22], regs[24]);
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    regs[26] = locs["distances_3x3_fully(xs):2"];
    regs[27] = locs["distances_3x3_fully(ys):0"];
    info.eval->sub(regs[26], regs[27], regs[28]);
    info.eval->sub(regs[26], regs[27], regs[29]);
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    regs[31] = locs["distances_3x3_fully(ys):1"];
    info.eval->sub(regs[26], regs[31], regs[32]);
    info.eval->sub(regs[26], regs[31], regs[33]);
    info.eval->multiply(regs[32], regs[33], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    regs[35] = locs["distances_3x3_fully(ys):2"];
    info.eval->sub(regs[26], regs[35], regs[36]);
    info.eval->sub(regs[26], regs[35], regs[37]);
    info.eval->multiply(regs[36], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[8]);
    answer.push_back(regs[12]);
    answer.push_back(regs[17]);
    answer.push_back(regs[21]);
    answer.push_back(regs[25]);
    answer.push_back(regs[30]);
    answer.push_back(regs[34]);
    answer.push_back(regs[38]);
    return answer;
}
    