
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 75;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"c:2", "c:1", "c:0", "d:2", "a:0", "b:2", "a:1", "a:2", "d:0", "d:1", "b:0", "b:1"};
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
    regs[20] = locs["c:2"];
    info.eval->sub(regs[0], regs[20], regs[21]);
    info.eval->sub(regs[0], regs[20], regs[22]);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    regs[24] = locs["d:2"];
    info.eval->sub(regs[5], regs[24], regs[25]);
    info.eval->sub(regs[5], regs[24], regs[26]);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[23], regs[27], regs[28]);
    regs[29] = locs["a:1"];
    info.eval->sub(regs[29], regs[1], regs[30]);
    info.eval->sub(regs[29], regs[1], regs[31]);
    info.eval->multiply(regs[30], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    regs[33] = locs["b:1"];
    info.eval->sub(regs[33], regs[6], regs[34]);
    info.eval->sub(regs[33], regs[6], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[32], regs[36], regs[37]);
    info.eval->sub(regs[29], regs[11], regs[38]);
    info.eval->sub(regs[29], regs[11], regs[39]);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->sub(regs[33], regs[15], regs[41]);
    info.eval->sub(regs[33], regs[15], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->sub(regs[29], regs[20], regs[45]);
    info.eval->sub(regs[29], regs[20], regs[46]);
    info.eval->multiply(regs[45], regs[46], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->sub(regs[33], regs[24], regs[48]);
    info.eval->sub(regs[33], regs[24], regs[49]);
    info.eval->multiply(regs[48], regs[49], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(regs[47], regs[50], regs[51]);
    regs[52] = locs["a:2"];
    info.eval->sub(regs[52], regs[1], regs[53]);
    info.eval->sub(regs[52], regs[1], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    regs[56] = locs["b:2"];
    info.eval->sub(regs[56], regs[6], regs[57]);
    info.eval->sub(regs[56], regs[6], regs[58]);
    info.eval->multiply(regs[57], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[55], regs[59], regs[60]);
    info.eval->sub(regs[52], regs[11], regs[61]);
    info.eval->sub(regs[52], regs[11], regs[62]);
    info.eval->multiply(regs[61], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->sub(regs[56], regs[15], regs[64]);
    info.eval->sub(regs[56], regs[15], regs[65]);
    info.eval->multiply(regs[64], regs[65], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(regs[63], regs[66], regs[67]);
    info.eval->sub(regs[52], regs[20], regs[68]);
    info.eval->sub(regs[52], regs[20], regs[69]);
    info.eval->multiply(regs[68], regs[69], regs[70]);
    info.eval->relinearize_inplace(regs[70], rk);
    info.eval->sub(regs[56], regs[24], regs[71]);
    info.eval->sub(regs[56], regs[24], regs[72]);
    info.eval->multiply(regs[71], regs[72], regs[73]);
    info.eval->relinearize_inplace(regs[73], rk);
    info.eval->add(regs[70], regs[73], regs[74]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[19]);
    answer.push_back(regs[28]);
    answer.push_back(regs[37]);
    answer.push_back(regs[44]);
    answer.push_back(regs[51]);
    answer.push_back(regs[60]);
    answer.push_back(regs[67]);
    answer.push_back(regs[74]);
    return answer;
}
    