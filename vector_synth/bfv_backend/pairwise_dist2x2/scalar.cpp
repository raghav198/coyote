
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 60;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"d:0", "b:1", "a:1", "a:0", "b:0", "c:1", "d:1", "c:0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["c:0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    regs[3] = locs["a:0"];
    regs[4] = locs["c:0"];
    info.eval->sub(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    regs[7] = locs["b:0"];
    regs[8] = locs["d:0"];
    info.eval->sub(regs[7], regs[8], regs[9]);
    regs[10] = locs["b:0"];
    regs[11] = locs["d:0"];
    info.eval->sub(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[6], regs[13], regs[14]);
    regs[15] = locs["a:0"];
    regs[16] = locs["c:1"];
    info.eval->sub(regs[15], regs[16], regs[17]);
    regs[18] = locs["a:0"];
    regs[19] = locs["c:1"];
    info.eval->sub(regs[18], regs[19], regs[20]);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["b:0"];
    regs[23] = locs["d:1"];
    info.eval->sub(regs[22], regs[23], regs[24]);
    regs[25] = locs["b:0"];
    regs[26] = locs["d:1"];
    info.eval->sub(regs[25], regs[26], regs[27]);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[21], regs[28], regs[29]);
    regs[30] = locs["a:1"];
    regs[31] = locs["c:0"];
    info.eval->sub(regs[30], regs[31], regs[32]);
    regs[33] = locs["a:1"];
    regs[34] = locs["c:0"];
    info.eval->sub(regs[33], regs[34], regs[35]);
    info.eval->multiply(regs[32], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    regs[37] = locs["b:1"];
    regs[38] = locs["d:0"];
    info.eval->sub(regs[37], regs[38], regs[39]);
    regs[40] = locs["b:1"];
    regs[41] = locs["d:0"];
    info.eval->sub(regs[40], regs[41], regs[42]);
    info.eval->multiply(regs[39], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[36], regs[43], regs[44]);
    regs[45] = locs["a:1"];
    regs[46] = locs["c:1"];
    info.eval->sub(regs[45], regs[46], regs[47]);
    regs[48] = locs["a:1"];
    regs[49] = locs["c:1"];
    info.eval->sub(regs[48], regs[49], regs[50]);
    info.eval->multiply(regs[47], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    regs[52] = locs["b:1"];
    regs[53] = locs["d:1"];
    info.eval->sub(regs[52], regs[53], regs[54]);
    regs[55] = locs["b:1"];
    regs[56] = locs["d:1"];
    info.eval->sub(regs[55], regs[56], regs[57]);
    info.eval->multiply(regs[54], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[51], regs[58], regs[59]);
    std::vector<ctxt> answer;
    answer.push_back(regs[14]);
    answer.push_back(regs[29]);
    answer.push_back(regs[44]);
    answer.push_back(regs[59]);
    return answer;
}
    