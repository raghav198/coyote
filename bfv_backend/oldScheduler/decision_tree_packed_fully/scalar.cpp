
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 31;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"1", "decision_tree_packed_fully(os):2", "decision_tree_packed_fully(os):5", "decision_tree_packed_fully(os):4", "decision_tree_packed_fully(os):0", "decision_tree_packed_fully(cs):1", "decision_tree_packed_fully(os):3", "decision_tree_packed_fully(os):1", "decision_tree_packed_fully(cs):0", "decision_tree_packed_fully(cs):2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["decision_tree_packed_fully(cs):0"];
    regs[1] = locs["decision_tree_packed_fully(cs):1"];
    regs[2] = locs["decision_tree_packed_fully(os):0"];
    info.eval->multiply(regs[1], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["1"], regs[1], regs[4]);
    regs[5] = locs["decision_tree_packed_fully(cs):2"];
    regs[6] = locs["decision_tree_packed_fully(os):1"];
    info.eval->multiply(regs[5], regs[6], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(locs["1"], regs[5], regs[8]);
    regs[9] = locs["decision_tree_packed_fully(os):4"];
    info.eval->multiply(regs[8], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[7], regs[10], regs[11]);
    info.eval->multiply(regs[4], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[3], regs[12], regs[13]);
    info.eval->multiply(regs[0], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["1"], regs[0], regs[15]);
    regs[16] = locs["decision_tree_packed_fully(cs):2"];
    regs[17] = locs["decision_tree_packed_fully(os):2"];
    info.eval->multiply(regs[16], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(locs["1"], regs[16], regs[19]);
    regs[20] = locs["decision_tree_packed_fully(cs):1"];
    regs[21] = locs["decision_tree_packed_fully(os):3"];
    info.eval->multiply(regs[20], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["1"], regs[20], regs[23]);
    regs[24] = locs["decision_tree_packed_fully(os):5"];
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[22], regs[25], regs[26]);
    info.eval->multiply(regs[19], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[18], regs[27], regs[28]);
    info.eval->multiply(regs[15], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[14], regs[29], regs[30]);
    std::vector<ctxt> answer;
    answer.push_back(regs[30]);
    return answer;
}
    