/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
*/
#include <lean/lean.h>
#include <cstddef>
#include <cstdint>

#if defined(LEAN_WASI)

namespace {

constexpr uint32_t ui_magic = 0x4c554931;
constexpr uint32_t ui_version = 1;
constexpr uint32_t max_effects = 512;

struct UiEffectRecord {
    uint32_t opcode;
    uint32_t id;
    uint32_t parent;
    uint32_t index;
    uint32_t payload0;
    uint32_t payload1;
    uint32_t text_ptr;
    uint32_t text_len;
};

struct UiBatchHeader {
    uint32_t magic;
    uint32_t version;
    uint32_t header_size;
    uint32_t record_size;
    uint32_t count;
    uint32_t records_ptr;
    uint32_t overflowed;
    uint32_t reserved;
};

static_assert(sizeof(UiEffectRecord) == 32);
static_assert(sizeof(UiBatchHeader) == 32);

UiEffectRecord effects[max_effects];
UiBatchHeader batch { ui_magic, ui_version, sizeof(UiBatchHeader), sizeof(UiEffectRecord), 0,
    static_cast<uint32_t>(reinterpret_cast<uintptr_t>(effects)), 0, 0 };
lean_object * strings[max_effects];
uint32_t string_count = 0;
lean_object * fiber = nullptr;
lean_object * model = nullptr;

void clear_strings() {
    for (uint32_t i = 0; i < string_count; ++i) lean_dec(strings[i]);
    string_count = 0;
}

}

extern "C" {

LEAN_EXPORT uint32_t lean_ui_clear_effects(uint32_t world) {
    clear_strings();
    batch.count = 0;
    batch.overflowed = 0;
    return world;
}

LEAN_EXPORT uint32_t lean_ui_push_effect(uint32_t world, uint32_t opcode, uint32_t id,
        uint32_t parent, uint32_t index, uint32_t payload0, uint32_t payload1,
        b_lean_obj_arg text) {
    if (batch.count >= max_effects || string_count >= max_effects) {
        batch.overflowed = 1;
        return world;
    }
    lean_inc(text);
    strings[string_count++] = text;
    size_t size = lean_string_size(text);
    effects[batch.count++] = { opcode, id, parent, index, payload0, payload1,
        static_cast<uint32_t>(reinterpret_cast<uintptr_t>(lean_string_cstr(text))),
        size == 0 ? 0 : static_cast<uint32_t>(size - 1) };
    return world;
}

LEAN_EXPORT uint32_t lean_ui_batch_ptr(uint32_t) {
    return static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&batch));
}

LEAN_EXPORT lean_object * lean_ui_load_fiber(uint32_t) {
    if (!fiber) return lean_box(0);
    lean_inc(fiber);
    return fiber;
}

LEAN_EXPORT uint32_t lean_ui_store_fiber(uint32_t world, b_lean_obj_arg value) {
    if (fiber) lean_dec(fiber);
    lean_inc(value);
    fiber = value;
    return world;
}

LEAN_EXPORT lean_object * lean_ui_load_model(uint32_t) {
    if (!model) return lean_box(0);
    lean_inc(model);
    return model;
}

LEAN_EXPORT uint32_t lean_ui_store_model(uint32_t world, b_lean_obj_arg value) {
    if (model) lean_dec(model);
    lean_inc(value);
    model = value;
    return world;
}

}

#endif
