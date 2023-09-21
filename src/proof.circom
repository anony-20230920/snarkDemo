pragma circom 2.0.0;

include "./circomlib/sha256/sha256_2.circom";
include "./circomlib/comparators.circom";

template nonDuplicate(nLength) {
    signal input in[nLength];

    component c[nLength * nLength];
    for (var i = 0; i < nLength; i++) {
        for (var j = i + 1; j < nLength; j++) {
            c[i * nLength + j] = IsEqual();
            c[i * nLength + j].in[0] <== in[i];
            c[i * nLength + j].in[1] <== in[j];
            // check that they are not equal
            c[i * nLength + j].out === 0;
        }
    }
}

template strictlyIncreasing(nLength) {
    signal input in[nLength];

    // range check
    component range_check[nLength];
    for (var i = 0; i < nLength; i++) {
        range_check[i] = Num2Bits(252);
        range_check[i].in <== in[i];
    }

    component lt[nLength - 1];
    for (var i = 0; i < nLength - 1; i++) {
        lt[i] = LessThan(252);
        lt[i].in[0] <== in[i];
        lt[i].in[1] <== in[i + 1];
        // check that they are strictly increasing
        lt[i].out === 1;
    }
}

// prove that there exists at least m different shares x_i \in (x_1, x_2, ..., x_n)
// such that sha256(header, x_i) < target, where header is the block header
// note that (1) m <= n (2)  x_1 < x_2 < ... < x_n
template shareProof(n) {
    signal input C;
    signal input content;
    signal input pk;
    signal input headerRoot;
    signal input target;
    signal input x[n];
    signal input m;

    // check that headerRoot, content, pk are in range 2^64
    component range_check_headerRoot = Num2Bits(64);
    range_check_headerRoot.in <== headerRoot;
    component range_check_content = Num2Bits(64);
    range_check_content.in <== content;
    component range_check_pk = Num2Bits(64);
    range_check_pk.in <== pk;

    // check that C = headerRoot || content || pk
    C === headerRoot * 2 ** 128 + content * 2 ** 64 + pk;

    // check that x_1 < x_2 < ... < x_n
    component inc_check = strictlyIncreasing(n);
    for (var i = 0; i < n; i++) {
        inc_check.in[i] <== x[i];
    }

    // range check for target
    component range_check_target = Num2Bits(252);
    range_check_target.in <== target;
    // range check for sha result
    component range_check_sha256_check[n];

    // compute sha256(C, x_i) for all i \in (1, 2, ..., n) and check that they are less than target
    component sha256_check[n];
    component target_check[n];
    var sum = 0;
    for (var i = 0; i < n; i++) {
        sha256_check[i] = Sha256_2();
        sha256_check[i].a <== C;
        sha256_check[i].b <== x[i];

        // range check
        range_check_sha256_check[i] = Num2Bits(252);
        range_check_sha256_check[i].in <== sha256_check[i].out;

        target_check[i] = LessThan(252);
        target_check[i].in[0] <== sha256_check[i].out;
        target_check[i].in[1] <== target;
        sum += target_check[i].out;
    }

    // range check
    component range_check_m_check = Num2Bits(252);
    range_check_m_check.in <== m;
    component range_check_sum_check = Num2Bits(252);
    range_check_sum_check.in <== sum;

    // check that there are at least m different shares
    component m_check = LessEqThan(252);
    m_check.in[0] <== m;
    m_check.in[1] <== sum;
    m_check.out === 1;
}

component main {public [headerRoot, pk, target, m]} = shareProof(10);