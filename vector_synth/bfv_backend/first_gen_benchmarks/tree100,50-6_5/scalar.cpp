
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"406", "210", "71", "954", "609", "940", "528", "267", "717", "427", "757", "698", "225", "221", "507", "764", "523", "610", "592", "555", "699", "524", "965", "963", "363", "102", "740", "800", "1003", "286", "580", "833", "585", "789", "75", "793", "1019", "107", "219", "103", "667", "207", "261", "366", "120", "917", "817", "514", "679", "935", "443", "300", "709", "669", "767", "503", "937", "566", "638", "40", "564", "982"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["406"], locs["789"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["717"], locs["503"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["638"], locs["103"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["935"], locs["757"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->multiply(locs["669"], locs["937"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(locs["221"], locs["585"], regs[8]);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->multiply(locs["564"], locs["1019"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["965"], locs["800"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["963"], locs["40"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["300"], locs["580"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->add(locs["107"], locs["75"], regs[18]);
    info.eval->multiply(locs["286"], locs["740"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->add(regs[17], regs[20], regs[21]);
    info.eval->multiply(locs["427"], locs["917"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["261"], locs["793"], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(locs["366"], locs["210"], regs[25]);
    info.eval->add(locs["679"], locs["120"], regs[26]);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[14], regs[29], regs[30]);
    info.eval->add(locs["698"], locs["817"], regs[31]);
    info.eval->add(locs["1003"], locs["954"], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(locs["507"], locs["514"], regs[34]);
    info.eval->add(locs["219"], locs["935"], regs[35]);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["610"], locs["667"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["524"], locs["592"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->add(locs["937"], locs["609"], regs[41]);
    info.eval->add(locs["363"], locs["709"], regs[42]);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->add(locs["443"], locs["225"], regs[46]);
    info.eval->multiply(locs["555"], locs["940"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->add(locs["528"], locs["764"], regs[49]);
    info.eval->add(locs["833"], locs["566"], regs[50]);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->add(locs["767"], locs["982"], regs[53]);
    info.eval->multiply(locs["699"], locs["102"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["71"], locs["523"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["267"], locs["207"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(regs[52], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->add(regs[30], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    