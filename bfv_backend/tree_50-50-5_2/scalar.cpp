
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 13;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"310", "809", "819", "505", "137", "965", "605", "786", "199", "782", "92", "918", "6", "924"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["505"], locs["782"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["605"], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(locs["965"], locs["92"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[2], locs["199"], regs[3]);
    info.eval->add(regs[1], regs[3], regs[4]);
    info.eval->multiply(regs[4], locs["809"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["918"], locs["137"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["6"], locs["819"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[8], locs["924"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["310"], locs["786"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[9], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[5], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[12]);
    return answer;
}
    