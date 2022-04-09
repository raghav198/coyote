
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"52", "53", "736", "751", "93", "498", "752", "1012", "731", "720", "910", "7", "409", "927", "854", "788", "976", "742", "69", "861", "665", "967", "517", "804", "781", "935", "194", "526", "95", "344", "137", "981", "936", "282", "228", "442", "1010", "286", "825", "470", "694", "35", "793", "309", "233", "940", "471", "361", "821", "828", "893", "290", "591", "114", "950", "130", "552", "127", "794", "303", "1015", "150", "222", "91"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["861"], locs["720"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["228"], locs["1012"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["893"], locs["731"], regs[3]);
    info.eval->multiply(locs["194"], locs["981"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["442"], locs["91"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(locs["781"], locs["409"], regs[8]);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->add(locs["927"], locs["736"], regs[10]);
    info.eval->add(locs["694"], locs["752"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["828"], locs["52"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(locs["751"], locs["821"], regs[16]);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["935"], locs["286"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["794"], locs["976"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->add(regs[17], regs[20], regs[21]);
    info.eval->multiply(locs["517"], locs["552"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["940"], locs["470"], regs[23]);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->multiply(locs["498"], locs["950"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["69"], locs["309"], regs[26]);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(locs["7"], locs["361"], regs[31]);
    info.eval->add(locs["95"], locs["936"], regs[32]);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->add(locs["591"], locs["233"], regs[34]);
    info.eval->add(locs["825"], locs["137"], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["910"], locs["303"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(locs["471"], locs["282"], regs[39]);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->multiply(locs["130"], locs["53"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["222"], locs["793"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->add(locs["967"], locs["127"], regs[46]);
    info.eval->multiply(locs["290"], locs["114"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["35"], locs["93"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(locs["1015"], locs["854"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->multiply(locs["804"], locs["1010"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(locs["788"], locs["742"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->add(locs["344"], locs["526"], regs[56]);
    info.eval->add(locs["665"], locs["150"], regs[57]);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    