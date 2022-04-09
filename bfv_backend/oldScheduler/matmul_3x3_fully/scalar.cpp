
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 99;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"matmul_3x3_fully(a):2;0", "matmul_3x3_fully(a):2;1", "matmul_3x3_fully(b):0;2", "matmul_3x3_fully(b):1;2", "matmul_3x3_fully(b):0;0", "matmul_3x3_fully(a):1;0", "matmul_3x3_fully(a):0;0", "matmul_3x3_fully(a):0;1", "matmul_3x3_fully(b):0;1", "matmul_3x3_fully(b):2;1", "matmul_3x3_fully(b):1;1", "matmul_3x3_fully(a):0;2", "matmul_3x3_fully(a):1;1", "matmul_3x3_fully(a):1;2", "matmul_3x3_fully(b):1;0", "matmul_3x3_fully(a):2;2", "matmul_3x3_fully(b):2;2", "matmul_3x3_fully(b):2;0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["matmul_3x3_fully(a):0;0"];
    regs[1] = locs["matmul_3x3_fully(b):0;0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["matmul_3x3_fully(a):0;1"];
    regs[4] = locs["matmul_3x3_fully(b):1;0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["matmul_3x3_fully(a):0;2"];
    regs[7] = locs["matmul_3x3_fully(b):2;0"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["matmul_3x3_fully(a):0;0"];
    regs[12] = locs["matmul_3x3_fully(b):0;1"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["matmul_3x3_fully(a):0;1"];
    regs[15] = locs["matmul_3x3_fully(b):1;1"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["matmul_3x3_fully(a):0;2"];
    regs[18] = locs["matmul_3x3_fully(b):2;1"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->add(regs[13], regs[20], regs[21]);
    regs[22] = locs["matmul_3x3_fully(a):0;0"];
    regs[23] = locs["matmul_3x3_fully(b):0;2"];
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    regs[25] = locs["matmul_3x3_fully(a):0;1"];
    regs[26] = locs["matmul_3x3_fully(b):1;2"];
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    regs[28] = locs["matmul_3x3_fully(a):0;2"];
    regs[29] = locs["matmul_3x3_fully(b):2;2"];
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[27], regs[30], regs[31]);
    info.eval->add(regs[24], regs[31], regs[32]);
    regs[33] = locs["matmul_3x3_fully(a):1;0"];
    regs[34] = locs["matmul_3x3_fully(b):0;0"];
    info.eval->multiply(regs[33], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    regs[36] = locs["matmul_3x3_fully(a):1;1"];
    regs[37] = locs["matmul_3x3_fully(b):1;0"];
    info.eval->multiply(regs[36], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    regs[39] = locs["matmul_3x3_fully(a):1;2"];
    regs[40] = locs["matmul_3x3_fully(b):2;0"];
    info.eval->multiply(regs[39], regs[40], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(regs[38], regs[41], regs[42]);
    info.eval->add(regs[35], regs[42], regs[43]);
    regs[44] = locs["matmul_3x3_fully(a):1;0"];
    regs[45] = locs["matmul_3x3_fully(b):0;1"];
    info.eval->multiply(regs[44], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    regs[47] = locs["matmul_3x3_fully(a):1;1"];
    regs[48] = locs["matmul_3x3_fully(b):1;1"];
    info.eval->multiply(regs[47], regs[48], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    regs[50] = locs["matmul_3x3_fully(a):1;2"];
    regs[51] = locs["matmul_3x3_fully(b):2;1"];
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[49], regs[52], regs[53]);
    info.eval->add(regs[46], regs[53], regs[54]);
    regs[55] = locs["matmul_3x3_fully(a):1;0"];
    regs[56] = locs["matmul_3x3_fully(b):0;2"];
    info.eval->multiply(regs[55], regs[56], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    regs[58] = locs["matmul_3x3_fully(a):1;1"];
    regs[59] = locs["matmul_3x3_fully(b):1;2"];
    info.eval->multiply(regs[58], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    regs[61] = locs["matmul_3x3_fully(a):1;2"];
    regs[62] = locs["matmul_3x3_fully(b):2;2"];
    info.eval->multiply(regs[61], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(regs[60], regs[63], regs[64]);
    info.eval->add(regs[57], regs[64], regs[65]);
    regs[66] = locs["matmul_3x3_fully(a):2;0"];
    regs[67] = locs["matmul_3x3_fully(b):0;0"];
    info.eval->multiply(regs[66], regs[67], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    regs[69] = locs["matmul_3x3_fully(a):2;1"];
    regs[70] = locs["matmul_3x3_fully(b):1;0"];
    info.eval->multiply(regs[69], regs[70], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    regs[72] = locs["matmul_3x3_fully(a):2;2"];
    regs[73] = locs["matmul_3x3_fully(b):2;0"];
    info.eval->multiply(regs[72], regs[73], regs[74]);
    info.eval->relinearize_inplace(regs[74], rk);
    info.eval->add(regs[71], regs[74], regs[75]);
    info.eval->add(regs[68], regs[75], regs[76]);
    regs[77] = locs["matmul_3x3_fully(a):2;0"];
    regs[78] = locs["matmul_3x3_fully(b):0;1"];
    info.eval->multiply(regs[77], regs[78], regs[79]);
    info.eval->relinearize_inplace(regs[79], rk);
    regs[80] = locs["matmul_3x3_fully(a):2;1"];
    regs[81] = locs["matmul_3x3_fully(b):1;1"];
    info.eval->multiply(regs[80], regs[81], regs[82]);
    info.eval->relinearize_inplace(regs[82], rk);
    regs[83] = locs["matmul_3x3_fully(a):2;2"];
    regs[84] = locs["matmul_3x3_fully(b):2;1"];
    info.eval->multiply(regs[83], regs[84], regs[85]);
    info.eval->relinearize_inplace(regs[85], rk);
    info.eval->add(regs[82], regs[85], regs[86]);
    info.eval->add(regs[79], regs[86], regs[87]);
    regs[88] = locs["matmul_3x3_fully(a):2;0"];
    regs[89] = locs["matmul_3x3_fully(b):0;2"];
    info.eval->multiply(regs[88], regs[89], regs[90]);
    info.eval->relinearize_inplace(regs[90], rk);
    regs[91] = locs["matmul_3x3_fully(a):2;1"];
    regs[92] = locs["matmul_3x3_fully(b):1;2"];
    info.eval->multiply(regs[91], regs[92], regs[93]);
    info.eval->relinearize_inplace(regs[93], rk);
    regs[94] = locs["matmul_3x3_fully(a):2;2"];
    regs[95] = locs["matmul_3x3_fully(b):2;2"];
    info.eval->multiply(regs[94], regs[95], regs[96]);
    info.eval->relinearize_inplace(regs[96], rk);
    info.eval->add(regs[93], regs[96], regs[97]);
    info.eval->add(regs[90], regs[97], regs[98]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[21]);
    answer.push_back(regs[32]);
    answer.push_back(regs[43]);
    answer.push_back(regs[54]);
    answer.push_back(regs[65]);
    answer.push_back(regs[76]);
    answer.push_back(regs[87]);
    answer.push_back(regs[98]);
    return answer;
}
    