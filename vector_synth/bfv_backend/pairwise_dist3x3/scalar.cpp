
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 135;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"c:1", "b:0", "a:1", "c:0", "a:2", "b:2", "d:1", "a:0", "d:2", "b:1", "c:2", "d:0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["c:0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    regs[3] = locs["a:0"];
    regs[4] = locs["c:0"];
    info.eval->sub(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    regs[7] = locs["b:0"];
    regs[8] = locs["d:0"];
    info.eval->sub(regs[7], regs[8], regs[9]);
    regs[10] = locs["b:0"];
    regs[11] = locs["d:0"];
    info.eval->sub(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[6], regs[13], regs[14]);
    regs[15] = locs["a:0"];
    regs[16] = locs["c:1"];
    info.eval->sub(regs[15], regs[16], regs[17]);
    regs[18] = locs["a:0"];
    regs[19] = locs["c:1"];
    info.eval->sub(regs[18], regs[19], regs[20]);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["b:0"];
    regs[23] = locs["d:1"];
    info.eval->sub(regs[22], regs[23], regs[24]);
    regs[25] = locs["b:0"];
    regs[26] = locs["d:1"];
    info.eval->sub(regs[25], regs[26], regs[27]);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[21], regs[28], regs[29]);
    regs[30] = locs["a:0"];
    regs[31] = locs["c:2"];
    info.eval->sub(regs[30], regs[31], regs[32]);
    regs[33] = locs["a:0"];
    regs[34] = locs["c:2"];
    info.eval->sub(regs[33], regs[34], regs[35]);
    info.eval->multiply(regs[32], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    regs[37] = locs["b:0"];
    regs[38] = locs["d:2"];
    info.eval->sub(regs[37], regs[38], regs[39]);
    regs[40] = locs["b:0"];
    regs[41] = locs["d:2"];
    info.eval->sub(regs[40], regs[41], regs[42]);
    info.eval->multiply(regs[39], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[36], regs[43], regs[44]);
    regs[45] = locs["a:1"];
    regs[46] = locs["c:0"];
    info.eval->sub(regs[45], regs[46], regs[47]);
    regs[48] = locs["a:1"];
    regs[49] = locs["c:0"];
    info.eval->sub(regs[48], regs[49], regs[50]);
    info.eval->multiply(regs[47], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    regs[52] = locs["b:1"];
    regs[53] = locs["d:0"];
    info.eval->sub(regs[52], regs[53], regs[54]);
    regs[55] = locs["b:1"];
    regs[56] = locs["d:0"];
    info.eval->sub(regs[55], regs[56], regs[57]);
    info.eval->multiply(regs[54], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[51], regs[58], regs[59]);
    regs[60] = locs["a:1"];
    regs[61] = locs["c:1"];
    info.eval->sub(regs[60], regs[61], regs[62]);
    regs[63] = locs["a:1"];
    regs[64] = locs["c:1"];
    info.eval->sub(regs[63], regs[64], regs[65]);
    info.eval->multiply(regs[62], regs[65], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    regs[67] = locs["b:1"];
    regs[68] = locs["d:1"];
    info.eval->sub(regs[67], regs[68], regs[69]);
    regs[70] = locs["b:1"];
    regs[71] = locs["d:1"];
    info.eval->sub(regs[70], regs[71], regs[72]);
    info.eval->multiply(regs[69], regs[72], regs[73]);
    info.eval->relinearize_inplace(regs[73], rk);
    info.eval->add(regs[66], regs[73], regs[74]);
    regs[75] = locs["a:1"];
    regs[76] = locs["c:2"];
    info.eval->sub(regs[75], regs[76], regs[77]);
    regs[78] = locs["a:1"];
    regs[79] = locs["c:2"];
    info.eval->sub(regs[78], regs[79], regs[80]);
    info.eval->multiply(regs[77], regs[80], regs[81]);
    info.eval->relinearize_inplace(regs[81], rk);
    regs[82] = locs["b:1"];
    regs[83] = locs["d:2"];
    info.eval->sub(regs[82], regs[83], regs[84]);
    regs[85] = locs["b:1"];
    regs[86] = locs["d:2"];
    info.eval->sub(regs[85], regs[86], regs[87]);
    info.eval->multiply(regs[84], regs[87], regs[88]);
    info.eval->relinearize_inplace(regs[88], rk);
    info.eval->add(regs[81], regs[88], regs[89]);
    regs[90] = locs["a:2"];
    regs[91] = locs["c:0"];
    info.eval->sub(regs[90], regs[91], regs[92]);
    regs[93] = locs["a:2"];
    regs[94] = locs["c:0"];
    info.eval->sub(regs[93], regs[94], regs[95]);
    info.eval->multiply(regs[92], regs[95], regs[96]);
    info.eval->relinearize_inplace(regs[96], rk);
    regs[97] = locs["b:2"];
    regs[98] = locs["d:0"];
    info.eval->sub(regs[97], regs[98], regs[99]);
    regs[100] = locs["b:2"];
    regs[101] = locs["d:0"];
    info.eval->sub(regs[100], regs[101], regs[102]);
    info.eval->multiply(regs[99], regs[102], regs[103]);
    info.eval->relinearize_inplace(regs[103], rk);
    info.eval->add(regs[96], regs[103], regs[104]);
    regs[105] = locs["a:2"];
    regs[106] = locs["c:1"];
    info.eval->sub(regs[105], regs[106], regs[107]);
    regs[108] = locs["a:2"];
    regs[109] = locs["c:1"];
    info.eval->sub(regs[108], regs[109], regs[110]);
    info.eval->multiply(regs[107], regs[110], regs[111]);
    info.eval->relinearize_inplace(regs[111], rk);
    regs[112] = locs["b:2"];
    regs[113] = locs["d:1"];
    info.eval->sub(regs[112], regs[113], regs[114]);
    regs[115] = locs["b:2"];
    regs[116] = locs["d:1"];
    info.eval->sub(regs[115], regs[116], regs[117]);
    info.eval->multiply(regs[114], regs[117], regs[118]);
    info.eval->relinearize_inplace(regs[118], rk);
    info.eval->add(regs[111], regs[118], regs[119]);
    regs[120] = locs["a:2"];
    regs[121] = locs["c:2"];
    info.eval->sub(regs[120], regs[121], regs[122]);
    regs[123] = locs["a:2"];
    regs[124] = locs["c:2"];
    info.eval->sub(regs[123], regs[124], regs[125]);
    info.eval->multiply(regs[122], regs[125], regs[126]);
    info.eval->relinearize_inplace(regs[126], rk);
    regs[127] = locs["b:2"];
    regs[128] = locs["d:2"];
    info.eval->sub(regs[127], regs[128], regs[129]);
    regs[130] = locs["b:2"];
    regs[131] = locs["d:2"];
    info.eval->sub(regs[130], regs[131], regs[132]);
    info.eval->multiply(regs[129], regs[132], regs[133]);
    info.eval->relinearize_inplace(regs[133], rk);
    info.eval->add(regs[126], regs[133], regs[134]);
    std::vector<ctxt> answer;
    answer.push_back(regs[14]);
    answer.push_back(regs[29]);
    answer.push_back(regs[44]);
    answer.push_back(regs[59]);
    answer.push_back(regs[74]);
    answer.push_back(regs[89]);
    answer.push_back(regs[104]);
    answer.push_back(regs[119]);
    answer.push_back(regs[134]);
    return answer;
}
    