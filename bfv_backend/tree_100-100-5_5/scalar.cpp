
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 10;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"305", "413", "790", "132", "838", "346", "217", "880", "291", "895", "491"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["132"], locs["413"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["838"], locs["305"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["217"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[0], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["346"], locs["790"], regs[4]);
    info.eval->multiply(locs["895"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["291"], locs["491"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(regs[5], regs[6], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[7], locs["880"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[3], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    return answer;
}
    