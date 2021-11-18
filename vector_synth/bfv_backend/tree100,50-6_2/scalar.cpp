
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"934", "9", "936", "322", "180", "291", "75", "963", "161", "671", "689", "943", "799", "940", "304", "305", "756", "195", "777", "397", "98", "724", "249", "335", "468", "979", "130", "677", "248", "424", "375", "737", "556", "168", "365", "550", "983", "342", "366", "350", "581", "899", "394", "364", "67", "29", "136", "353", "509", "440", "125", "378", "432", "827", "94", "382", "1020", "835", "380", "557", "663"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["380"], locs["468"], regs[0]);
    info.eval->multiply(locs["29"], locs["248"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["94"], locs["195"], regs[3]);
    info.eval->multiply(locs["350"], locs["671"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->add(locs["365"], locs["161"], regs[7]);
    info.eval->multiply(locs["305"], locs["9"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->add(locs["98"], locs["335"], regs[10]);
    info.eval->add(locs["737"], locs["556"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["756"], locs["375"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["249"], locs["305"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(locs["1020"], locs["75"], regs[18]);
    info.eval->add(locs["432"], locs["366"], regs[19]);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["94"], locs["663"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["378"], locs["67"], regs[23]);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->multiply(locs["557"], locs["29"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["125"], locs["168"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->add(regs[14], regs[29], regs[30]);
    info.eval->multiply(locs["677"], locs["180"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(locs["353"], locs["581"], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(locs["364"], locs["550"], regs[34]);
    info.eval->multiply(locs["777"], locs["509"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->add(regs[33], regs[36], regs[37]);
    info.eval->multiply(locs["440"], locs["934"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(locs["963"], locs["689"], regs[39]);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["136"], locs["943"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["397"], locs["983"], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->add(locs["835"], locs["936"], regs[46]);
    info.eval->add(locs["940"], locs["899"], regs[47]);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(locs["979"], locs["291"], regs[49]);
    info.eval->add(locs["799"], locs["724"], regs[50]);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->multiply(locs["827"], locs["130"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(locs["424"], locs["304"], regs[54]);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->multiply(locs["394"], locs["382"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["342"], locs["322"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[30], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    