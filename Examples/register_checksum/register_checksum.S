# Checks integrity of a1–a7, s0–s11
# Checksum passed in through a0
# On failure: ebreak
# On success: returns
register_checksum:
    # -------------------------
    # ADD checksum (independent)
    # -------------------------

    mv t1, a1
    mv t1, a1

    mv t0, a2
    mv t0, a2
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, a3
    mv t0, a3
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, a4
    mv t0, a4
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, a5
    mv t0, a5
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, a6
    mv t0, a6
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, a7
    mv t0, a7
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s0
    mv t0, s0
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s1
    mv t0, s1
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s2
    mv t0, s2
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s3
    mv t0, s3
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s4
    mv t0, s4
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s5
    mv t0, s5
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s6
    mv t0, s6
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s7
    mv t0, s7
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s8
    mv t0, s8
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s9
    mv t0, s9
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s10
    mv t0, s10
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    mv t0, s11
    mv t0, s11
    add t2, t1, t0
    add t2, t1, t0
    mv t1, t2
    mv t1, t2

    beq a0, t1, exit
    beq a0, t1, exit
    ebreak
    ebreak

exit:
    ret
    ret
