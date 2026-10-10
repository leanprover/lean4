#ifndef RC_GRAPH_COUNTED_EDGE_MODEL_H
#define RC_GRAPH_COUNTED_EDGE_MODEL_H

/* Included after each harness's model state and CHECK definition. */
static uint32_t random32(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

static void model_release(unsigned i) {
    CHECK(live[i]);
    if (counts[i] > 1) {
        --counts[i];
    } else if (counts[i] == 1) {
        live[i] = false;
        CHECK(top < N);
        stack[top++] = i;
    } else if (counts[i] != 0 && counts[i] > LEAN_RC_STICKY_DROP) {
        ++counts[i];
        if (counts[i] == 0) {
            live[i] = false;
            CHECK(top < N);
            stack[top++] = i;
        }
    }
}

static void model_drop(unsigned root, unsigned trace_capacity) {
    model_release(root);
    while (top) {
        unsigned i = stack[--top];
        for (unsigned f = 0; f < degree[i]; ++f)
            if (edges[i][f] >= 0) model_release((unsigned)edges[i][f]);
        CHECK(expected_n < trace_capacity);
        expected[expected_n++] = i;
    }
}

#endif
