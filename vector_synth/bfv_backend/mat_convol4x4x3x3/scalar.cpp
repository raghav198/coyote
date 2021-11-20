
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 68;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:0,1", "a:3,2", "b:2,1", "a:2,2", "a:3,1", "a:0,2", "b:0,0", "a:2,3", "a:2,0", "a:0,0", "b:1,1", "a:2,1", "a:0,1", "b:1,2", "a:3,0", "b:0,2", "b:2,0", "a:0,3", "a:3,3", "a:1,0", "a:1,2", "a:1,3", "b:1,0", "a:1,1", "b:2,2"};
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
    info.eval->multiply(locs["b:0,2"], locs["a:0,2"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[2], regs[3], regs[4]);
    info.eval->multiply(locs["b:1,0"], locs["a:1,0"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[4], regs[5], regs[6]);
    info.eval->multiply(locs["b:1,1"], locs["a:1,1"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[6], regs[7], regs[8]);
    info.eval->multiply(locs["b:1,2"], locs["a:1,2"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[8], regs[9], regs[10]);
    info.eval->multiply(locs["b:2,0"], locs["a:2,0"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(locs["b:2,1"], locs["a:2,1"], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[12], regs[13], regs[14]);
    info.eval->multiply(locs["b:2,2"], locs["a:2,2"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[14], regs[15], regs[16]);
    info.eval->multiply(locs["b:0,0"], locs["a:0,1"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:0,2"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[17], regs[18], regs[19]);
    info.eval->multiply(locs["b:0,2"], locs["a:0,3"], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[19], regs[20], regs[21]);
    info.eval->multiply(locs["b:1,0"], locs["a:1,1"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[21], regs[22], regs[23]);
    info.eval->multiply(locs["b:1,1"], locs["a:1,2"], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[23], regs[24], regs[25]);
    info.eval->multiply(locs["b:1,2"], locs["a:1,3"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->multiply(locs["b:2,0"], locs["a:2,1"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[27], regs[28], regs[29]);
    info.eval->multiply(locs["b:2,1"], locs["a:2,2"], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[29], regs[30], regs[31]);
    info.eval->multiply(locs["b:2,2"], locs["a:2,3"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->multiply(locs["b:0,0"], locs["a:1,0"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:1,1"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(locs["b:0,2"], locs["a:1,2"], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(regs[36], regs[37], regs[38]);
    info.eval->multiply(locs["b:1,0"], locs["a:2,0"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->multiply(locs["b:1,1"], locs["a:2,1"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(regs[40], regs[41], regs[42]);
    info.eval->multiply(locs["b:1,2"], locs["a:2,2"], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[42], regs[43], regs[44]);
    info.eval->multiply(locs["b:2,0"], locs["a:3,0"], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[44], regs[45], regs[46]);
    info.eval->multiply(locs["b:2,1"], locs["a:3,1"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["b:2,2"], locs["a:3,2"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(regs[48], regs[49], regs[50]);
    info.eval->multiply(locs["b:0,0"], locs["a:1,1"], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->multiply(locs["b:0,1"], locs["a:1,2"], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[51], regs[52], regs[53]);
    info.eval->multiply(locs["b:0,2"], locs["a:1,3"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->multiply(locs["b:1,0"], locs["a:2,1"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(regs[55], regs[56], regs[57]);
    info.eval->multiply(locs["b:1,1"], locs["a:2,2"], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[57], regs[58], regs[59]);
    info.eval->multiply(locs["b:1,2"], locs["a:2,3"], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[59], regs[60], regs[61]);
    info.eval->multiply(locs["b:2,0"], locs["a:3,1"], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->add(regs[61], regs[62], regs[63]);
    info.eval->multiply(locs["b:2,1"], locs["a:3,2"], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    info.eval->add(regs[63], regs[64], regs[65]);
    info.eval->multiply(locs["b:2,2"], locs["a:3,3"], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(regs[65], regs[66], regs[67]);
    std::vector<ctxt> answer;
    answer.push_back(regs[16]);
    answer.push_back(regs[33]);
    answer.push_back(regs[50]);
    answer.push_back(regs[67]);
    return answer;
}
    