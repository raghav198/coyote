
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 20;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"decision_tree(c23)", "decision_tree(o312)", "1", "decision_tree(c13)", "decision_tree(o231)", "decision_tree(o213)", "decision_tree(o321)", "decision_tree(o123)", "decision_tree(o132)", "decision_tree(c12)"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["decision_tree(c23)"], locs["decision_tree(o123)"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["1"], locs["decision_tree(c23)"], regs[1]);
    info.eval->multiply(locs["decision_tree(c13)"], locs["decision_tree(o132)"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["1"], locs["decision_tree(c13)"], regs[3]);
    info.eval->multiply(regs[3], locs["decision_tree(o312)"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[2], regs[4], regs[5]);
    info.eval->multiply(regs[1], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(regs[0], regs[6], regs[7]);
    info.eval->multiply(locs["decision_tree(c12)"], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(locs["1"], locs["decision_tree(c12)"], regs[9]);
    info.eval->multiply(locs["decision_tree(c13)"], locs["decision_tree(o213)"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs["1"], locs["decision_tree(c13)"], regs[11]);
    info.eval->multiply(locs["decision_tree(c23)"], locs["decision_tree(o231)"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs["1"], locs["decision_tree(c23)"], regs[13]);
    info.eval->multiply(regs[13], locs["decision_tree(o321)"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(regs[12], regs[14], regs[15]);
    info.eval->multiply(regs[11], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[10], regs[16], regs[17]);
    info.eval->multiply(regs[9], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[8], regs[18], regs[19]);
    std::vector<ctxt> answer;
    answer.push_back(regs[19]);
    return answer;
}
    