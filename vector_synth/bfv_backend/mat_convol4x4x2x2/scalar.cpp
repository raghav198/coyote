
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:1,2", "a:0,2", "b:1,0", "a:2,3", "a:0,1", "b:1,1", "a:0,3", "a:0,0", "a:2,1", "a:2,2", "a:2,0", "a:3,1", "a:3,3", "a:1,0", "a:1,1", "a:1,3", "b:0,0", "a:3,0", "b:0,1", "a:3,2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["b:0,0"], locs["a:0,0"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:0,1"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["b:1,0"], locs["a:1,0"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[2], regs[3], regs[4]);
    info.eval->multiply(locs["b:1,1"], locs["a:1,1"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[4], regs[5], regs[6]);
    info.eval->multiply(locs["b:0,0"], locs["a:0,1"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:0,2"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->multiply(locs["b:1,0"], locs["a:1,1"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[9], regs[10], regs[11]);
    info.eval->multiply(locs["b:1,1"], locs["a:1,2"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[11], regs[12], regs[13]);
    info.eval->multiply(locs["b:0,0"], locs["a:0,2"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:0,3"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[14], regs[15], regs[16]);
    info.eval->multiply(locs["b:1,0"], locs["a:1,2"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[16], regs[17], regs[18]);
    info.eval->multiply(locs["b:1,1"], locs["a:1,3"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->multiply(locs["b:0,0"], locs["a:1,0"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:1,1"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[21], regs[22], regs[23]);
    info.eval->multiply(locs["b:1,0"], locs["a:2,0"], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[23], regs[24], regs[25]);
    info.eval->multiply(locs["b:1,1"], locs["a:2,1"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->multiply(locs["b:0,0"], locs["a:1,1"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:1,2"], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[28], regs[29], regs[30]);
    info.eval->multiply(locs["b:1,0"], locs["a:2,1"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[30], regs[31], regs[32]);
    info.eval->multiply(locs["b:1,1"], locs["a:2,2"], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[32], regs[33], regs[34]);
    info.eval->multiply(locs["b:0,0"], locs["a:1,2"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:1,3"], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[35], regs[36], regs[37]);
    info.eval->multiply(locs["b:1,0"], locs["a:2,2"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[37], regs[38], regs[39]);
    info.eval->multiply(locs["b:1,1"], locs["a:2,3"], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[39], regs[40], regs[41]);
    info.eval->multiply(locs["b:0,0"], locs["a:2,0"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:2,1"], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[42], regs[43], regs[44]);
    info.eval->multiply(locs["b:1,0"], locs["a:3,0"], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[44], regs[45], regs[46]);
    info.eval->multiply(locs["b:1,1"], locs["a:3,1"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["b:0,0"], locs["a:2,1"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:2,2"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->multiply(locs["b:1,0"], locs["a:3,1"], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[51], regs[52], regs[53]);
    info.eval->multiply(locs["b:1,1"], locs["a:3,2"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->multiply(locs["b:0,0"], locs["a:2,2"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:2,3"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->multiply(locs["b:1,0"], locs["a:3,2"], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[58], regs[59], regs[60]);
    info.eval->multiply(locs["b:1,1"], locs["a:3,3"], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[60], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[13]);
    answer.push_back(regs[20]);
    answer.push_back(regs[27]);
    answer.push_back(regs[34]);
    answer.push_back(regs[41]);
    answer.push_back(regs[48]);
    answer.push_back(regs[55]);
    answer.push_back(regs[62]);
    return answer;
}
    