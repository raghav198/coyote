
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 28;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:0,0", "a:1,1", "b:0,0", "a:0,1", "b:1,1", "b:1,0", "b:0,1", "a:1,0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0,0"];
    regs[1] = locs["b:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["a:0,1"];
    regs[4] = locs["b:1,0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["a:0,0"];
    regs[8] = locs["b:0,1"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    regs[10] = locs["a:0,1"];
    regs[11] = locs["b:1,1"];
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    regs[14] = locs["a:1,0"];
    regs[15] = locs["b:0,0"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["a:1,1"];
    regs[18] = locs["b:1,0"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    regs[21] = locs["a:1,0"];
    regs[22] = locs["b:0,1"];
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    regs[24] = locs["a:1,1"];
    regs[25] = locs["b:1,1"];
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[23], regs[26], regs[27]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[13]);
    answer.push_back(regs[20]);
    answer.push_back(regs[27]);
    return answer;
}
    