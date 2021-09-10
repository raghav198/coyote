
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 66;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"n", "m", "c", "e", "j", "i", "t", "v", "a", "b", "q", "f", "s", "x", "p", "o", "y", "r", "g", "d", "l", "z", "k", "u"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["q"], locs["u"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["u"], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(locs["v"], locs["o"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[2], locs["v"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[1], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["v"], locs["b"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(locs["i"], regs[5], regs[6]);
    info.eval->add(regs[6], locs["j"], regs[7]);
    info.eval->multiply(locs["l"], locs["k"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(locs["k"], locs["q"], regs[9]);
    info.eval->multiply(regs[8], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[7], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(locs["m"], locs["d"], regs[12]);
    info.eval->add(regs[11], regs[12], regs[13]);
    info.eval->multiply(locs["j"], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(regs[4], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["c"], locs["k"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[16], locs["n"], regs[17]);
    info.eval->add(regs[17], locs["g"], regs[18]);
    info.eval->add(locs["t"], locs["l"], regs[19]);
    info.eval->add(locs["j"], locs["a"], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[18], regs[21], regs[22]);
    info.eval->add(locs["y"], locs["v"], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(locs["p"], locs["c"], regs[25]);
    info.eval->add(locs["i"], locs["q"], regs[26]);
    info.eval->add(regs[26], locs["p"], regs[27]);
    info.eval->add(regs[25], regs[27], regs[28]);
    info.eval->multiply(locs["a"], locs["k"], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[29], locs["k"], regs[30]);
    info.eval->multiply(regs[28], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(regs[31], locs["f"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(locs["z"], locs["u"], regs[33]);
    info.eval->add(locs["s"], locs["b"], regs[34]);
    info.eval->multiply(regs[33], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(locs["x"], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(locs["j"], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(regs[32], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(locs["d"], locs["g"], regs[39]);
    info.eval->add(regs[39], locs["t"], regs[40]);
    info.eval->add(locs["c"], regs[40], regs[41]);
    info.eval->add(regs[41], locs["v"], regs[42]);
    info.eval->add(locs["q"], locs["a"], regs[43]);
    info.eval->multiply(regs[42], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->multiply(regs[38], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->multiply(locs["r"], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(locs["d"], locs["c"], regs[47]);
    info.eval->add(locs["g"], regs[47], regs[48]);
    info.eval->multiply(locs["b"], regs[48], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->multiply(locs["a"], locs["p"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(locs["k"], locs["x"], regs[51]);
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[52], locs["k"], regs[53]);
    info.eval->multiply(regs[53], locs["y"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(regs[49], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["a"], regs[55], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["f"], locs["e"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[57], locs["p"], regs[58]);
    info.eval->add(locs["c"], regs[58], regs[59]);
    info.eval->add(locs["a"], locs["e"], regs[60]);
    info.eval->add(regs[60], locs["l"], regs[61]);
    info.eval->add(locs["x"], locs["y"], regs[62]);
    info.eval->multiply(locs["o"], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->multiply(locs["t"], regs[63], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    info.eval->multiply(regs[61], regs[64], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[15]);
    answer.push_back(regs[24]);
    answer.push_back(regs[46]);
    answer.push_back(regs[56]);
    answer.push_back(regs[59]);
    answer.push_back(regs[65]);
    return answer;
}
    