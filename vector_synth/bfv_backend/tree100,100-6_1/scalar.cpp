
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"422", "643", "230", "778", "149", "842", "440", "328", "785", "208", "644", "731", "521", "686", "1022", "983", "801", "267", "322", "806", "496", "210", "171", "172", "89", "246", "816", "669", "769", "214", "445", "402", "335", "160", "809", "754", "346", "833", "1020", "352", "384", "594", "931", "391", "184", "996", "1014", "710", "65", "859", "12", "602", "492", "753", "486", "36", "683", "113", "404", "771", "185", "444", "581"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["686"], locs["391"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["644"], locs["171"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["778"], locs["785"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["1014"], locs["328"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["322"], locs["806"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["753"], locs["160"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["669"], locs["492"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["246"], locs["594"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["983"], locs["809"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["710"], locs["210"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["422"], locs["931"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["801"], locs["346"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["12"], locs["185"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["771"], locs["65"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(locs["486"], locs["267"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["214"], locs["521"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["184"], locs["445"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(locs["816"], locs["496"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(locs["172"], locs["1022"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(locs["440"], locs["149"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["833"], locs["859"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["352"], locs["384"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["402"], locs["230"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["842"], locs["581"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->multiply(regs[37], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->multiply(locs["754"], locs["521"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["444"], locs["404"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->multiply(locs["731"], locs["113"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->multiply(locs["769"], locs["1020"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->multiply(locs["996"], locs["89"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(locs["683"], locs["335"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["36"], locs["208"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["643"], locs["602"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(regs[52], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    