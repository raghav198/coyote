
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 68;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"distances_4x4_fully(xs):3", "distances_4x4_fully(ys):1", "distances_4x4_fully(xs):0", "distances_4x4_fully(ys):2", "distances_4x4_fully(ys):3", "distances_4x4_fully(ys):0", "distances_4x4_fully(xs):2", "distances_4x4_fully(xs):1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["distances_4x4_fully(xs):0"];
    regs[1] = locs["distances_4x4_fully(ys):0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["distances_4x4_fully(ys):1"];
    info.eval->sub(regs[0], regs[5], regs[6]);
    info.eval->sub(regs[0], regs[5], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["distances_4x4_fully(ys):2"];
    info.eval->sub(regs[0], regs[9], regs[10]);
    info.eval->sub(regs[0], regs[9], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["distances_4x4_fully(ys):3"];
    info.eval->sub(regs[0], regs[13], regs[14]);
    info.eval->sub(regs[0], regs[13], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["distances_4x4_fully(xs):1"];
    regs[18] = locs["distances_4x4_fully(ys):0"];
    info.eval->sub(regs[17], regs[18], regs[19]);
    info.eval->sub(regs[17], regs[18], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["distances_4x4_fully(ys):1"];
    info.eval->sub(regs[17], regs[22], regs[23]);
    info.eval->sub(regs[17], regs[22], regs[24]);
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    regs[26] = locs["distances_4x4_fully(ys):2"];
    info.eval->sub(regs[17], regs[26], regs[27]);
    info.eval->sub(regs[17], regs[26], regs[28]);
    info.eval->multiply(regs[27], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    regs[30] = locs["distances_4x4_fully(ys):3"];
    info.eval->sub(regs[17], regs[30], regs[31]);
    info.eval->sub(regs[17], regs[30], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    regs[34] = locs["distances_4x4_fully(xs):2"];
    regs[35] = locs["distances_4x4_fully(ys):0"];
    info.eval->sub(regs[34], regs[35], regs[36]);
    info.eval->sub(regs[34], regs[35], regs[37]);
    info.eval->multiply(regs[36], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    regs[39] = locs["distances_4x4_fully(ys):1"];
    info.eval->sub(regs[34], regs[39], regs[40]);
    info.eval->sub(regs[34], regs[39], regs[41]);
    info.eval->multiply(regs[40], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    regs[43] = locs["distances_4x4_fully(ys):2"];
    info.eval->sub(regs[34], regs[43], regs[44]);
    info.eval->sub(regs[34], regs[43], regs[45]);
    info.eval->multiply(regs[44], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    regs[47] = locs["distances_4x4_fully(ys):3"];
    info.eval->sub(regs[34], regs[47], regs[48]);
    info.eval->sub(regs[34], regs[47], regs[49]);
    info.eval->multiply(regs[48], regs[49], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    regs[51] = locs["distances_4x4_fully(xs):3"];
    regs[52] = locs["distances_4x4_fully(ys):0"];
    info.eval->sub(regs[51], regs[52], regs[53]);
    info.eval->sub(regs[51], regs[52], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    regs[56] = locs["distances_4x4_fully(ys):1"];
    info.eval->sub(regs[51], regs[56], regs[57]);
    info.eval->sub(regs[51], regs[56], regs[58]);
    info.eval->multiply(regs[57], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    regs[60] = locs["distances_4x4_fully(ys):2"];
    info.eval->sub(regs[51], regs[60], regs[61]);
    info.eval->sub(regs[51], regs[60], regs[62]);
    info.eval->multiply(regs[61], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    regs[64] = locs["distances_4x4_fully(ys):3"];
    info.eval->sub(regs[51], regs[64], regs[65]);
    info.eval->sub(regs[51], regs[64], regs[66]);
    info.eval->multiply(regs[65], regs[66], regs[67]);
    info.eval->relinearize_inplace(regs[67], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[8]);
    answer.push_back(regs[12]);
    answer.push_back(regs[16]);
    answer.push_back(regs[21]);
    answer.push_back(regs[25]);
    answer.push_back(regs[29]);
    answer.push_back(regs[33]);
    answer.push_back(regs[38]);
    answer.push_back(regs[42]);
    answer.push_back(regs[46]);
    answer.push_back(regs[50]);
    answer.push_back(regs[55]);
    answer.push_back(regs[59]);
    answer.push_back(regs[63]);
    answer.push_back(regs[67]);
    return answer;
}
    