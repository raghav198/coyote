
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 60;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"max_value(c25)", "max_value(c35)", "max_value(o4)", "max_value(c23)", "max_value(c12)", "max_value(c24)", "max_value(o5)", "max_value(o2)", "max_value(c45)", "max_value(c34)", "max_value(c13)", "max_value(c15)", "max_value(o1)", "1", "max_value(o3)", "max_value(c14)"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["max_value(c15)"], locs["max_value(o1)"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["1"], locs["max_value(c15)"], regs[1]);
    info.eval->multiply(regs[1], locs["max_value(o5)"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[0], regs[2], regs[3]);
    info.eval->multiply(locs["max_value(c14)"], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(locs["1"], locs["max_value(c14)"], regs[5]);
    info.eval->multiply(locs["max_value(c45)"], locs["max_value(o4)"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["1"], locs["max_value(c45)"], regs[7]);
    info.eval->multiply(regs[7], locs["max_value(o5)"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[6], regs[8], regs[9]);
    info.eval->multiply(regs[5], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[4], regs[10], regs[11]);
    info.eval->multiply(locs["max_value(c13)"], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs["1"], locs["max_value(c13)"], regs[13]);
    info.eval->multiply(locs["max_value(c35)"], locs["max_value(o3)"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["1"], locs["max_value(c35)"], regs[15]);
    info.eval->multiply(regs[15], locs["max_value(o5)"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[14], regs[16], regs[17]);
    info.eval->multiply(locs["max_value(c34)"], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(locs["1"], locs["max_value(c34)"], regs[19]);
    info.eval->multiply(locs["max_value(c45)"], locs["max_value(o4)"], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(locs["1"], locs["max_value(c45)"], regs[21]);
    info.eval->multiply(regs[21], locs["max_value(o5)"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[20], regs[22], regs[23]);
    info.eval->multiply(regs[19], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[18], regs[24], regs[25]);
    info.eval->multiply(regs[13], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[12], regs[26], regs[27]);
    info.eval->multiply(locs["max_value(c12)"], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(locs["1"], locs["max_value(c12)"], regs[29]);
    info.eval->multiply(locs["max_value(c25)"], locs["max_value(o2)"], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(locs["1"], locs["max_value(c25)"], regs[31]);
    info.eval->multiply(regs[31], locs["max_value(o5)"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[30], regs[32], regs[33]);
    info.eval->multiply(locs["max_value(c24)"], regs[33], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(locs["1"], locs["max_value(c24)"], regs[35]);
    info.eval->multiply(locs["max_value(c45)"], locs["max_value(o4)"], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(locs["1"], locs["max_value(c45)"], regs[37]);
    info.eval->multiply(regs[37], locs["max_value(o5)"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[36], regs[38], regs[39]);
    info.eval->multiply(regs[35], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[34], regs[40], regs[41]);
    info.eval->multiply(locs["max_value(c23)"], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(locs["1"], locs["max_value(c23)"], regs[43]);
    info.eval->multiply(locs["max_value(c35)"], locs["max_value(o3)"], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(locs["1"], locs["max_value(c35)"], regs[45]);
    info.eval->multiply(regs[45], locs["max_value(o5)"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(regs[44], regs[46], regs[47]);
    info.eval->multiply(locs["max_value(c34)"], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(locs["1"], locs["max_value(c34)"], regs[49]);
    info.eval->multiply(locs["max_value(c45)"], locs["max_value(o4)"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(locs["1"], locs["max_value(c45)"], regs[51]);
    info.eval->multiply(regs[51], locs["max_value(o5)"], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[50], regs[52], regs[53]);
    info.eval->multiply(regs[49], regs[53], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[48], regs[54], regs[55]);
    info.eval->multiply(regs[43], regs[55], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(regs[42], regs[56], regs[57]);
    info.eval->multiply(regs[29], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[28], regs[58], regs[59]);
    std::vector<ctxt> answer;
    answer.push_back(regs[59]);
    return answer;
}
    