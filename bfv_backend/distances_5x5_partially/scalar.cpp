
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 85;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"distances_5x5_partially(xs):3", "distances_5x5_partially(xs):0", "distances_5x5_partially(ys):2", "distances_5x5_partially(xs):2", "distances_5x5_partially(ys):4", "distances_5x5_partially(ys):0", "distances_5x5_partially(ys):1", "distances_5x5_partially(xs):1", "distances_5x5_partially(xs):4", "distances_5x5_partially(ys):3"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["distances_5x5_partially(xs):0"];
    regs[1] = locs["distances_5x5_partially(ys):0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["distances_5x5_partially(ys):1"];
    info.eval->sub(regs[0], regs[5], regs[6]);
    info.eval->sub(regs[0], regs[5], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["distances_5x5_partially(ys):2"];
    info.eval->sub(regs[0], regs[9], regs[10]);
    info.eval->sub(regs[0], regs[9], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["distances_5x5_partially(ys):3"];
    info.eval->sub(regs[0], regs[13], regs[14]);
    info.eval->sub(regs[0], regs[13], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["distances_5x5_partially(ys):4"];
    info.eval->sub(regs[0], regs[17], regs[18]);
    info.eval->sub(regs[0], regs[17], regs[19]);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    regs[21] = locs["distances_5x5_partially(xs):1"];
    info.eval->sub(regs[21], regs[1], regs[22]);
    info.eval->sub(regs[21], regs[1], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->sub(regs[21], regs[5], regs[25]);
    info.eval->sub(regs[21], regs[5], regs[26]);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->sub(regs[21], regs[9], regs[28]);
    info.eval->sub(regs[21], regs[9], regs[29]);
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->sub(regs[21], regs[13], regs[31]);
    info.eval->sub(regs[21], regs[13], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->sub(regs[21], regs[17], regs[34]);
    info.eval->sub(regs[21], regs[17], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    regs[37] = locs["distances_5x5_partially(xs):2"];
    info.eval->sub(regs[37], regs[1], regs[38]);
    info.eval->sub(regs[37], regs[1], regs[39]);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->sub(regs[37], regs[5], regs[41]);
    info.eval->sub(regs[37], regs[5], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->sub(regs[37], regs[9], regs[44]);
    info.eval->sub(regs[37], regs[9], regs[45]);
    info.eval->multiply(regs[44], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->sub(regs[37], regs[13], regs[47]);
    info.eval->sub(regs[37], regs[13], regs[48]);
    info.eval->multiply(regs[47], regs[48], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->sub(regs[37], regs[17], regs[50]);
    info.eval->sub(regs[37], regs[17], regs[51]);
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    regs[53] = locs["distances_5x5_partially(xs):3"];
    info.eval->sub(regs[53], regs[1], regs[54]);
    info.eval->sub(regs[53], regs[1], regs[55]);
    info.eval->multiply(regs[54], regs[55], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->sub(regs[53], regs[5], regs[57]);
    info.eval->sub(regs[53], regs[5], regs[58]);
    info.eval->multiply(regs[57], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->sub(regs[53], regs[9], regs[60]);
    info.eval->sub(regs[53], regs[9], regs[61]);
    info.eval->multiply(regs[60], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->sub(regs[53], regs[13], regs[63]);
    info.eval->sub(regs[53], regs[13], regs[64]);
    info.eval->multiply(regs[63], regs[64], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    info.eval->sub(regs[53], regs[17], regs[66]);
    info.eval->sub(regs[53], regs[17], regs[67]);
    info.eval->multiply(regs[66], regs[67], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    regs[69] = locs["distances_5x5_partially(xs):4"];
    info.eval->sub(regs[69], regs[1], regs[70]);
    info.eval->sub(regs[69], regs[1], regs[71]);
    info.eval->multiply(regs[70], regs[71], regs[72]);
    info.eval->relinearize_inplace(regs[72], rk);
    info.eval->sub(regs[69], regs[5], regs[73]);
    info.eval->sub(regs[69], regs[5], regs[74]);
    info.eval->multiply(regs[73], regs[74], regs[75]);
    info.eval->relinearize_inplace(regs[75], rk);
    info.eval->sub(regs[69], regs[9], regs[76]);
    info.eval->sub(regs[69], regs[9], regs[77]);
    info.eval->multiply(regs[76], regs[77], regs[78]);
    info.eval->relinearize_inplace(regs[78], rk);
    info.eval->sub(regs[69], regs[13], regs[79]);
    info.eval->sub(regs[69], regs[13], regs[80]);
    info.eval->multiply(regs[79], regs[80], regs[81]);
    info.eval->relinearize_inplace(regs[81], rk);
    info.eval->sub(regs[69], regs[17], regs[82]);
    info.eval->sub(regs[69], regs[17], regs[83]);
    info.eval->multiply(regs[82], regs[83], regs[84]);
    info.eval->relinearize_inplace(regs[84], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[8]);
    answer.push_back(regs[12]);
    answer.push_back(regs[16]);
    answer.push_back(regs[20]);
    answer.push_back(regs[24]);
    answer.push_back(regs[27]);
    answer.push_back(regs[30]);
    answer.push_back(regs[33]);
    answer.push_back(regs[36]);
    answer.push_back(regs[40]);
    answer.push_back(regs[43]);
    answer.push_back(regs[46]);
    answer.push_back(regs[49]);
    answer.push_back(regs[52]);
    answer.push_back(regs[56]);
    answer.push_back(regs[59]);
    answer.push_back(regs[62]);
    answer.push_back(regs[65]);
    answer.push_back(regs[68]);
    answer.push_back(regs[72]);
    answer.push_back(regs[75]);
    answer.push_back(regs[78]);
    answer.push_back(regs[81]);
    answer.push_back(regs[84]);
    return answer;
}
    