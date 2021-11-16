
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 48;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"c:0", "a:1", "d:1", "c:1", "d:0", "b:1", "b:0", "a:0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["c:0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    regs[3] = locs["a:0"];
    info.eval->sub(regs[3], regs[1], regs[4]);
    info.eval->multiply(regs[2], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["b:0"];
    regs[7] = locs["d:0"];
    info.eval->sub(regs[6], regs[7], regs[8]);
    regs[9] = locs["b:0"];
    info.eval->sub(regs[9], regs[7], regs[10]);
    info.eval->multiply(regs[8], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[5], regs[11], regs[12]);
    regs[13] = locs["a:0"];
    regs[14] = locs["c:1"];
    info.eval->sub(regs[13], regs[14], regs[15]);
    regs[16] = locs["a:0"];
    info.eval->sub(regs[16], regs[14], regs[17]);
    info.eval->multiply(regs[15], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    regs[19] = locs["b:0"];
    regs[20] = locs["d:1"];
    info.eval->sub(regs[19], regs[20], regs[21]);
    regs[22] = locs["b:0"];
    info.eval->sub(regs[22], regs[20], regs[23]);
    info.eval->multiply(regs[21], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[18], regs[24], regs[25]);
    regs[26] = locs["a:1"];
    info.eval->sub(regs[26], regs[1], regs[27]);
    regs[28] = locs["a:1"];
    info.eval->sub(regs[28], regs[1], regs[29]);
    info.eval->multiply(regs[27], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    regs[31] = locs["b:1"];
    info.eval->sub(regs[31], regs[7], regs[32]);
    regs[33] = locs["b:1"];
    info.eval->sub(regs[33], regs[7], regs[34]);
    info.eval->multiply(regs[32], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[30], regs[35], regs[36]);
    regs[37] = locs["a:1"];
    info.eval->sub(regs[37], regs[14], regs[38]);
    regs[39] = locs["a:1"];
    info.eval->sub(regs[39], regs[14], regs[40]);
    info.eval->multiply(regs[38], regs[40], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    regs[42] = locs["b:1"];
    info.eval->sub(regs[42], regs[20], regs[43]);
    regs[44] = locs["b:1"];
    info.eval->sub(regs[44], regs[20], regs[45]);
    info.eval->multiply(regs[43], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(regs[41], regs[46], regs[47]);
    std::vector<ctxt> answer;
    answer.push_back(regs[12]);
    answer.push_back(regs[25]);
    answer.push_back(regs[36]);
    answer.push_back(regs[47]);
    return answer;
}
    