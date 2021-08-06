$seed = 0;
while (++$seed) {
    `python3 vector_compiler.py $seed`;
    if ($? != 0) {
        print "Failure seed: $seed\n";
        last;
    }
}