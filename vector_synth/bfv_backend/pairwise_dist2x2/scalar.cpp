
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 28;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:1", "d:1", "a:0", "b:0", "c:0", "c:1", "d:0", "a:1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->sub(locs["a:0"], locs["c:0"], regs[0]);
    info.eval->sub(locs["a:0"], locs["c:0"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->sub(locs["b:0"], locs["d:0"], regs[3]);
    info.eval->sub(locs["b:0"], locs["d:0"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->sub(locs["a:0"], locs["c:1"], regs[7]);
    info.eval->sub(locs["a:0"], locs["c:1"], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->sub(locs["b:0"], locs["d:1"], regs[10]);
    info.eval->sub(locs["b:0"], locs["d:1"], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->sub(locs["a:1"], locs["c:0"], regs[14]);
    info.eval->sub(locs["a:1"], locs["c:0"], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->sub(locs["b:1"], locs["d:0"], regs[17]);
    info.eval->sub(locs["b:1"], locs["d:0"], regs[18]);
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->sub(locs["a:1"], locs["c:1"], regs[21]);
    info.eval->sub(locs["a:1"], locs["c:1"], regs[22]);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->sub(locs["b:1"], locs["d:1"], regs[24]);
    info.eval->sub(locs["b:1"], locs["d:1"], regs[25]);
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
    