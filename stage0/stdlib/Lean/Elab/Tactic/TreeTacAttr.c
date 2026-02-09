// Lean compiler output
// Module: Lean.Elab.Tactic.TreeTacAttr
// Imports: public import Lean.Meta.Tactic.Simp
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static const lean_string_object l_initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
static const lean_string_object l_initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
static const lean_string_object l_initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tree_tac"};
static const lean_object* l_initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 155, 163, 92, 201, 101, 200, 86)}};
static const lean_object* l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
static const lean_string_object l_initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "simp theorems used by internal DTreeMap lemmas"};
static const lean_object* l_initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
static const lean_string_object l_initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "treeTacExt"};
static const lean_object* l_initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 184, 101, 226, 90, 97, 138, 170)}};
static const lean_object* l_initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_ = (const lean_object*)&l_initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value;
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_treeTacExt;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_));
x_5 = l_Lean_Meta_registerSimpAttr(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_TreeTacAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_treeTacExt = lean_io_result_get_value(res);
lean_mark_persistent(l_treeTacExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
