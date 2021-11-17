
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 36;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:0", "b:1", "a:1", "a:0", "c:1", "d:1", "c:0", "d:0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["c:0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    info.eval->sub(regs[0], regs[1], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    regs[5] = locs["b:0"];
    regs[6] = locs["d:0"];
    info.eval->sub(regs[5], regs[6], regs[7]);
    info.eval->sub(regs[5], regs[6], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[4], regs[9], regs[10]);
    regs[11] = locs["c:1"];
    info.eval->sub(regs[0], regs[11], regs[12]);
    info.eval->sub(regs[0], regs[11], regs[13]);
    info.eval->multiply(regs[12], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    regs[15] = locs["d:1"];
    info.eval->sub(regs[5], regs[15], regs[16]);
    info.eval->sub(regs[5], regs[15], regs[17]);
    info.eval->multiply(regs[16], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[14], regs[18], regs[19]);
    regs[20] = locs["a:1"];
    info.eval->sub(regs[20], regs[1], regs[21]);
    info.eval->sub(regs[20], regs[1], regs[22]);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    regs[24] = locs["b:1"];
    info.eval->sub(regs[24], regs[6], regs[25]);
    info.eval->sub(regs[24], regs[6], regs[26]);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[23], regs[27], regs[28]);
    info.eval->sub(regs[20], regs[11], regs[29]);
    info.eval->sub(regs[20], regs[11], regs[30]);
    info.eval->multiply(regs[29], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->sub(regs[24], regs[15], regs[32]);
    info.eval->sub(regs[24], regs[15], regs[33]);
    info.eval->multiply(regs[32], regs[33], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(regs[31], regs[34], regs[35]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[19]);
    answer.push_back(regs[28]);
    answer.push_back(regs[35]);
    return answer;
}
    