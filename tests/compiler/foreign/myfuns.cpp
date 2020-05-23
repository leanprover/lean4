#include <lean/object.h>
#include <lean/io.h>

struct S {
    unsigned    m_x;
    unsigned    m_y;
    std::string m_s;
    S(unsigned x, unsigned y, char const * s):m_x(x), m_y(y), m_s(s) {}
};

static void S_finalize(void * obj) {
    delete static_cast<S*>(obj);
}

static void S_foreach(void *, b_lean_obj_arg) {
    // do nothing since `S` does not contain nested Lean objects
}

static lean_external_class * g_S_class = nullptr;

static inline lean_object * S_to_lean(S * s) {
    if (g_S_class == nullptr) {
        g_S_class = lean_register_external_class(S_finalize, S_foreach);
    }
    return lean_alloc_external(g_S_class, s);
}

static inline S const * to_S(b_lean_obj_arg s) {
    return static_cast<S *>(lean_get_external_data(s));
}

extern "C" lean_object * lean_mk_S(uint32_t x, uint32_t y, b_lean_obj_arg s) {
    return S_to_lean(new S(x, y, lean_string_cstr(s)));
}

extern "C" uint32_t lean_S_add_x_y(b_lean_obj_arg s) {
    return to_S(s)->m_x + to_S(s)->m_y;
}

extern "C" lean_object * lean_S_string(b_lean_obj_arg s) {
    return lean::mk_string(to_S(s)->m_s);
}

static S g_s(0, 0, "");

extern "C" lean_object * lean_S_global_append(b_lean_obj_arg str, lean_object /* w */) {
    g_s.m_s += lean_string_cstr(str);
    return lean::set_io_result(lean_box(0));
}

extern "C" lean_object * lean_S_global_string(lean_object /* w */) {
    return lean::set_io_result(lean::mk_string(g_s.m_s));
}

extern "C" lean_object * lean_S_update_global(b_lean_obj_arg s, lean_object /* w */) {
    g_s.m_x = to_S(s)->m_x;
    g_s.m_y = to_S(s)->m_y;
    g_s.m_s = to_S(s)->m_s;
    return lean::set_io_result(lean_box(0));
}
