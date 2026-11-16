// Lean compiler output
// Module: Lean.Compiler.LCNF.WithPtrEq
// Imports: public import Lean.Meta.Basic import Lean.Meta.InferType import Lean.Meta.WHNF
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "withPtrEq"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 231, 189, 13, 165, 136, 244, 219)}};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to compile definition, `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "` cannot be used at type"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nbecause "};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 219, .m_capacity = 219, .m_length = 218, .m_data = "` is implemented by a pointer equality check, which is only correct if pointer-equal values are equal. This is not the case for values that contain types or type formers, since these are erased at runtime. Therefore, `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__18_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` can only be used at types for which the compiler can check that their values do not contain types or type formers; in particular, it cannot be used polymorphically."};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__22 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__22_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "In `unsafe` code, `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__26 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__26_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withPtrEqUnsafe"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__28 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__28_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(192, 117, 75, 220, 77, 248, 41, 200)}};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__29 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__29_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` can be used instead."};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__32 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__32_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__36 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__36_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " (in field `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__38 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__38_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` of constructor `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__40 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__40_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`)"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__42 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__42_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "it contains values of type"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__44 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__44_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\nwhich"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__46 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__46_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "values of this type"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__48 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__48_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "cannot be checked since the type does not reduce to an inductive type, a function type or a quotient"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "are erased at runtime"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "cannot be checked since `"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is a type variable"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4;
static const lean_array_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "cannot be checked since the constructor `"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not accessible"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__5_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2(void){
_start:
{
uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = 0;
v___x_54_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__1));
v___x_55_ = l_Lean_MessageData_ofConstName(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__3));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2);
v___x_60_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__4);
v___x_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__6));
v___x_64_ = l_Lean_stringToMessageData(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__7);
v___x_66_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__5);
v___x_67_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__9));
v___x_70_ = l_Lean_stringToMessageData(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__11));
v___x_73_ = l_Lean_stringToMessageData(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__13));
v___x_76_ = l_Lean_stringToMessageData(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__15));
v___x_79_ = l_Lean_stringToMessageData(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2);
v___x_81_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__16);
v___x_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__18));
v___x_85_ = l_Lean_stringToMessageData(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__19);
v___x_87_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__17);
v___x_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__2);
v___x_90_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__20);
v___x_91_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__22));
v___x_94_ = l_Lean_stringToMessageData(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__23);
v___x_96_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__21);
v___x_97_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__24);
v___x_99_ = l_Lean_MessageData_note(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__26));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30(void){
_start:
{
uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = 0;
v___x_107_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__29));
v___x_108_ = l_Lean_MessageData_ofConstName(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__30);
v___x_110_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__27);
v___x_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__32));
v___x_114_ = l_Lean_stringToMessageData(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__33);
v___x_116_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__31);
v___x_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__34);
v___x_119_ = l_Lean_MessageData_hint_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__36));
v___x_122_ = l_Lean_stringToMessageData(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__38));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__40));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__42));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__44));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__46));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__48));
v___x_140_ = l_Lean_stringToMessageData(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(lean_object* v_type_141_, lean_object* v_reason_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_rootType_150_; lean_object* v_field_x3f_151_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_173_; 
v_rootType_150_ = lean_ctor_get(v_a_143_, 0);
v_field_x3f_151_ = lean_ctor_get(v_a_143_, 1);
if (lean_obj_tag(v_field_x3f_151_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = lean_expr_eqv(v_type_141_, v_rootType_150_);
if (v___x_194_ == 0)
{
goto v___jp_188_;
}
else
{
lean_object* v___x_195_; 
lean_dec_ref(v_type_141_);
v___x_195_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__49);
v___y_173_ = v___x_195_;
goto v___jp_172_;
}
}
else
{
goto v___jp_188_;
}
v___jp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_155_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__8);
lean_inc_ref(v_rootType_150_);
v___x_156_ = l_Lean_indentExpr(v_rootType_150_);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__10);
v___x_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___y_153_);
v___x_161_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__12);
v___x_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_reason_142_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___y_154_);
v___x_165_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__14);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__25);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__35);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg(v___x_170_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_171_;
}
v___jp_172_:
{
if (lean_obj_tag(v_field_x3f_151_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__37);
v___y_153_ = v___y_173_;
v___y_154_ = v___x_174_;
goto v___jp_152_;
}
else
{
lean_object* v_val_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_val_175_ = lean_ctor_get(v_field_x3f_151_, 0);
v_fst_176_ = lean_ctor_get(v_val_175_, 0);
v_snd_177_ = lean_ctor_get(v_val_175_, 1);
v___x_178_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__39);
lean_inc(v_snd_177_);
v___x_179_ = l_Lean_MessageData_ofName(v_snd_177_);
v___x_180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__41);
v___x_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = 0;
lean_inc(v_fst_176_);
v___x_184_ = l_Lean_MessageData_ofConstName(v_fst_176_, v___x_183_);
v___x_185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_182_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__43);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___y_153_ = v___y_173_;
v___y_154_ = v___x_187_;
goto v___jp_152_;
}
}
v___jp_188_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__45);
v___x_190_ = l_Lean_indentExpr(v_type_141_);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___closed__47);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___y_173_ = v___x_193_;
goto v___jp_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg___boxed(lean_object* v_type_196_, lean_object* v_reason_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_196_, v_reason_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported(lean_object* v_00_u03b1_206_, lean_object* v_type_207_, lean_object* v_reason_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_207_, v_reason_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___boxed(lean_object* v_00_u03b1_217_, lean_object* v_type_218_, lean_object* v_reason_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported(v_00_u03b1_217_, v_type_218_, v_reason_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0(lean_object* v_00_u03b1_228_, lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___redArg(v_msg_229_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0___boxed(lean_object* v_00_u03b1_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported_spec__0(v_00_u03b1_238_, v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__0));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(lean_object* v_type_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___closed__1);
v___x_260_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_251_, v___x_259_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck___boxed(lean_object* v_type_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0(lean_object* v_k_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v_b_273_, lean_object* v_c_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_275_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
v___x_280_ = lean_apply_9(v_k_270_, v_b_273_, v_c_274_, v___y_271_, v___y_272_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, lean_box(0));
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0___boxed(lean_object* v_k_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v_b_284_, lean_object* v_c_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0(v_k_281_, v___y_282_, v___y_283_, v_b_284_, v_c_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg(lean_object* v_type_292_, lean_object* v_maxFVars_x3f_293_, lean_object* v_k_294_, uint8_t v_cleanupAnnotations_295_, uint8_t v_whnfType_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___f_304_; lean_object* v___x_305_; 
lean_inc(v___y_298_);
lean_inc_ref(v___y_297_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_304_, 0, v_k_294_);
lean_closure_set(v___f_304_, 1, v___y_297_);
lean_closure_set(v___f_304_, 2, v___y_298_);
v___x_305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_292_, v_maxFVars_x3f_293_, v___f_304_, v_cleanupAnnotations_295_, v_whnfType_296_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_305_) == 0)
{
return v___x_305_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___boxed(lean_object* v_type_314_, lean_object* v_maxFVars_x3f_315_, lean_object* v_k_316_, lean_object* v_cleanupAnnotations_317_, lean_object* v_whnfType_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_326_; uint8_t v_whnfType_boxed_327_; lean_object* v_res_328_; 
v_cleanupAnnotations_boxed_326_ = lean_unbox(v_cleanupAnnotations_317_);
v_whnfType_boxed_327_ = lean_unbox(v_whnfType_318_);
v_res_328_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg(v_type_314_, v_maxFVars_x3f_315_, v_k_316_, v_cleanupAnnotations_boxed_326_, v_whnfType_boxed_327_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4(lean_object* v_00_u03b1_329_, lean_object* v_type_330_, lean_object* v_maxFVars_x3f_331_, lean_object* v_k_332_, uint8_t v_cleanupAnnotations_333_, uint8_t v_whnfType_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg(v_type_330_, v_maxFVars_x3f_331_, v_k_332_, v_cleanupAnnotations_333_, v_whnfType_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___boxed(lean_object* v_00_u03b1_343_, lean_object* v_type_344_, lean_object* v_maxFVars_x3f_345_, lean_object* v_k_346_, lean_object* v_cleanupAnnotations_347_, lean_object* v_whnfType_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_356_; uint8_t v_whnfType_boxed_357_; lean_object* v_res_358_; 
v_cleanupAnnotations_boxed_356_ = lean_unbox(v_cleanupAnnotations_347_);
v_whnfType_boxed_357_ = lean_unbox(v_whnfType_348_);
v_res_358_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4(v_00_u03b1_343_, v_type_344_, v_maxFVars_x3f_345_, v_k_346_, v_cleanupAnnotations_boxed_356_, v_whnfType_boxed_357_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11___redArg(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
return v_x_359_;
}
else
{
lean_object* v_key_361_; lean_object* v_value_362_; lean_object* v_tail_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_386_; 
v_key_361_ = lean_ctor_get(v_x_360_, 0);
v_value_362_ = lean_ctor_get(v_x_360_, 1);
v_tail_363_ = lean_ctor_get(v_x_360_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_386_ == 0)
{
v___x_365_ = v_x_360_;
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_tail_363_);
lean_inc(v_value_362_);
lean_inc(v_key_361_);
lean_dec(v_x_360_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v_fold_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_367_ = lean_array_get_size(v_x_359_);
v___x_368_ = l_Lean_Expr_hash(v_key_361_);
v___x_369_ = 32ULL;
v___x_370_ = lean_uint64_shift_right(v___x_368_, v___x_369_);
v_fold_371_ = lean_uint64_xor(v___x_368_, v___x_370_);
v___x_372_ = 16ULL;
v___x_373_ = lean_uint64_shift_right(v_fold_371_, v___x_372_);
v___x_374_ = lean_uint64_xor(v_fold_371_, v___x_373_);
v___x_375_ = lean_uint64_to_usize(v___x_374_);
v___x_376_ = lean_usize_of_nat(v___x_367_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_sub(v___x_376_, v___x_377_);
v___x_379_ = lean_usize_land(v___x_375_, v___x_378_);
v___x_380_ = lean_array_uget_borrowed(v_x_359_, v___x_379_);
lean_inc(v___x_380_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 2, v___x_380_);
v___x_382_ = v___x_365_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_key_361_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_value_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___x_380_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_array_uset(v_x_359_, v___x_379_, v___x_382_);
v_x_359_ = v___x_383_;
v_x_360_ = v_tail_363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8___redArg(lean_object* v_i_387_, lean_object* v_source_388_, lean_object* v_target_389_){
_start:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_get_size(v_source_388_);
v___x_391_ = lean_nat_dec_lt(v_i_387_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_source_388_);
lean_dec(v_i_387_);
return v_target_389_;
}
else
{
lean_object* v_es_392_; lean_object* v___x_393_; lean_object* v_source_394_; lean_object* v_target_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_es_392_ = lean_array_fget(v_source_388_, v_i_387_);
v___x_393_ = lean_box(0);
v_source_394_ = lean_array_fset(v_source_388_, v_i_387_, v___x_393_);
v_target_395_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11___redArg(v_target_389_, v_es_392_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_i_387_, v___x_396_);
lean_dec(v_i_387_);
v_i_387_ = v___x_397_;
v_source_388_ = v_source_394_;
v_target_389_ = v_target_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3___redArg(lean_object* v_data_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_nbuckets_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_400_ = lean_array_get_size(v_data_399_);
v___x_401_ = lean_unsigned_to_nat(2u);
v_nbuckets_402_ = lean_nat_mul(v___x_400_, v___x_401_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_box(0);
v___x_405_ = lean_mk_array(v_nbuckets_402_, v___x_404_);
v___x_406_ = lean_array_propagate_mark(v_data_399_, v___x_405_);
v___x_407_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8___redArg(v___x_403_, v_data_399_, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_tail_412_; uint8_t v___x_413_; 
v_key_411_ = lean_ctor_get(v_x_409_, 0);
v_tail_412_ = lean_ctor_get(v_x_409_, 2);
v___x_413_ = lean_expr_eqv(v_key_411_, v_a_408_);
if (v___x_413_ == 0)
{
v_x_409_ = v_tail_412_;
goto _start;
}
else
{
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg___boxed(lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(v_a_415_, v_x_416_);
lean_dec(v_x_416_);
lean_dec_ref(v_a_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2___redArg(lean_object* v_m_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_size_422_; lean_object* v_buckets_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v_fold_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v_bkt_437_; uint8_t v___x_438_; 
v_size_422_ = lean_ctor_get(v_m_419_, 0);
v_buckets_423_ = lean_ctor_get(v_m_419_, 1);
v___x_424_ = lean_array_get_size(v_buckets_423_);
v___x_425_ = l_Lean_Expr_hash(v_a_420_);
v___x_426_ = 32ULL;
v___x_427_ = lean_uint64_shift_right(v___x_425_, v___x_426_);
v_fold_428_ = lean_uint64_xor(v___x_425_, v___x_427_);
v___x_429_ = 16ULL;
v___x_430_ = lean_uint64_shift_right(v_fold_428_, v___x_429_);
v___x_431_ = lean_uint64_xor(v_fold_428_, v___x_430_);
v___x_432_ = lean_uint64_to_usize(v___x_431_);
v___x_433_ = lean_usize_of_nat(v___x_424_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_usize_land(v___x_432_, v___x_435_);
v_bkt_437_ = lean_array_uget_borrowed(v_buckets_423_, v___x_436_);
v___x_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(v_a_420_, v_bkt_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_buckets_423_);
lean_inc(v_size_422_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_m_419_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_460_ = lean_ctor_get(v_m_419_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_m_419_, 0);
lean_dec(v_unused_461_);
v___x_440_ = v_m_419_;
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_m_419_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_459_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_size_x27_443_; lean_object* v___x_444_; lean_object* v_buckets_x27_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_442_ = lean_unsigned_to_nat(1u);
v_size_x27_443_ = lean_nat_add(v_size_422_, v___x_442_);
lean_dec(v_size_422_);
lean_inc(v_bkt_437_);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v_a_420_);
lean_ctor_set(v___x_444_, 1, v_b_421_);
lean_ctor_set(v___x_444_, 2, v_bkt_437_);
v_buckets_x27_445_ = lean_array_uset(v_buckets_423_, v___x_436_, v___x_444_);
v___x_446_ = lean_unsigned_to_nat(4u);
v___x_447_ = lean_nat_mul(v_size_x27_443_, v___x_446_);
v___x_448_ = lean_unsigned_to_nat(3u);
v___x_449_ = lean_nat_div(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_array_get_size(v_buckets_x27_445_);
v___x_451_ = lean_nat_dec_le(v___x_449_, v___x_450_);
lean_dec(v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v_val_452_; lean_object* v___x_454_; 
v_val_452_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3___redArg(v_buckets_x27_445_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_val_452_);
lean_ctor_set(v___x_440_, 0, v_size_x27_443_);
v___x_454_ = v___x_440_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_size_x27_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_val_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_buckets_x27_445_);
lean_ctor_set(v___x_440_, 0, v_size_x27_443_);
v___x_457_ = v___x_440_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_x27_443_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_buckets_x27_445_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_dec(v_b_421_);
lean_dec_ref(v_a_420_);
return v_m_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0___redArg(lean_object* v_a_462_, lean_object* v_b_463_){
_start:
{
lean_object* v_array_464_; lean_object* v_start_465_; lean_object* v_stop_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_479_; 
v_array_464_ = lean_ctor_get(v_a_462_, 0);
v_start_465_ = lean_ctor_get(v_a_462_, 1);
v_stop_466_ = lean_ctor_get(v_a_462_, 2);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_462_);
if (v_isSharedCheck_479_ == 0)
{
v___x_468_ = v_a_462_;
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_stop_466_);
lean_inc(v_start_465_);
lean_inc(v_array_464_);
lean_dec(v_a_462_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_lt(v_start_465_, v_stop_466_);
if (v___x_470_ == 0)
{
lean_del_object(v___x_468_);
lean_dec(v_stop_466_);
lean_dec(v_start_465_);
lean_dec_ref(v_array_464_);
return v_b_463_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_start_465_, v___x_471_);
lean_inc_ref(v_array_464_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_472_);
v___x_474_ = v___x_468_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_array_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_stop_466_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_array_fget(v_array_464_, v_start_465_);
lean_dec(v_start_465_);
lean_dec_ref(v_array_464_);
v___x_476_ = lean_array_push(v_b_463_, v___x_475_);
v_a_462_ = v___x_474_;
v_b_463_ = v___x_476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg(lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_buckets_482_; lean_object* v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v_fold_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_buckets_482_ = lean_ctor_get(v_m_480_, 1);
v___x_483_ = lean_array_get_size(v_buckets_482_);
v___x_484_ = l_Lean_Expr_hash(v_a_481_);
v___x_485_ = 32ULL;
v___x_486_ = lean_uint64_shift_right(v___x_484_, v___x_485_);
v_fold_487_ = lean_uint64_xor(v___x_484_, v___x_486_);
v___x_488_ = 16ULL;
v___x_489_ = lean_uint64_shift_right(v_fold_487_, v___x_488_);
v___x_490_ = lean_uint64_xor(v_fold_487_, v___x_489_);
v___x_491_ = lean_uint64_to_usize(v___x_490_);
v___x_492_ = lean_usize_of_nat(v___x_483_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_sub(v___x_492_, v___x_493_);
v___x_495_ = lean_usize_land(v___x_491_, v___x_494_);
v___x_496_ = lean_array_uget_borrowed(v_buckets_482_, v___x_495_);
v___x_497_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(v_a_481_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg___boxed(lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg(v_m_498_, v_a_499_);
lean_dec_ref(v_a_499_);
lean_dec_ref(v_m_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg(lean_object* v_type_502_, lean_object* v_k_503_, uint8_t v_cleanupAnnotations_504_, uint8_t v_whnfType_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___f_513_; lean_object* v___x_514_; 
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
v___f_513_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_513_, 0, v_k_503_);
lean_closure_set(v___f_513_, 1, v___y_506_);
lean_closure_set(v___f_513_, 2, v___y_507_);
v___x_514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_502_, v___f_513_, v_cleanupAnnotations_504_, v_whnfType_505_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_514_) == 0)
{
return v___x_514_;
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg___boxed(lean_object* v_type_523_, lean_object* v_k_524_, lean_object* v_cleanupAnnotations_525_, lean_object* v_whnfType_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_534_; uint8_t v_whnfType_boxed_535_; lean_object* v_res_536_; 
v_cleanupAnnotations_boxed_534_ = lean_unbox(v_cleanupAnnotations_525_);
v_whnfType_boxed_535_ = lean_unbox(v_whnfType_526_);
v_res_536_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg(v_type_523_, v_k_524_, v_cleanupAnnotations_boxed_534_, v_whnfType_boxed_535_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = l_Lean_maxRecDepthErrorMessage;
v___x_543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__3);
v___x_545_ = l_Lean_MessageData_ofFormat(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__4);
v___x_547_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__2));
v___x_548_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg(lean_object* v_ref_549_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___closed__5);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_ref_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg___boxed(lean_object* v_ref_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg(v_ref_554_);
return v_res_556_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__0));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0(lean_object* v_type_560_, lean_object* v_x_561_, lean_object* v_codomain_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_Expr_isSort(v_codomain_562_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec_ref(v_type_560_);
lean_inc_ref(v___y_567_);
v___x_571_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(v_codomain_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1);
v___x_573_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_560_, v___x_572_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; 
lean_dec_ref_known(v___x_573_, 1);
lean_inc_ref(v___y_567_);
v___x_574_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(v_codomain_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_574_;
}
else
{
lean_dec_ref(v_codomain_562_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___boxed(lean_object* v_type_575_, lean_object* v_x_576_, lean_object* v_codomain_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0(v_type_575_, v_x_576_, v_codomain_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v_x_576_);
return v_res_585_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__0));
v___x_588_ = l_Lean_stringToMessageData(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__2));
v___x_591_ = l_Lean_stringToMessageData(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4(void){
_start:
{
lean_object* v___x_592_; lean_object* v_dummy_593_; 
v___x_592_ = lean_box(0);
v_dummy_593_ = l_Lean_Expr_sort___override(v___x_592_);
return v_dummy_593_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__0));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__2));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0___boxed(lean_object* v_head_602_, lean_object* v___x_603_, lean_object* v_fields_604_, lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0(v_head_602_, v___x_603_, v_fields_604_, v_x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v_x_605_);
lean_dec_ref(v_fields_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg(uint8_t v___x_614_, lean_object* v_type_615_, lean_object* v_us_616_, lean_object* v_params_617_, lean_object* v_as_x27_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
if (lean_obj_tag(v_as_x27_618_) == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_type_615_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_619_);
return v___x_627_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_630_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v_env_646_; lean_object* v___x_647_; 
v_head_628_ = lean_ctor_get(v_as_x27_618_, 0);
v_tail_629_ = lean_ctor_get(v_as_x27_618_, 1);
v___x_630_ = lean_box(0);
lean_inc_n(v_head_628_, 2);
v___f_644_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_644_, 0, v_head_628_);
lean_closure_set(v___f_644_, 1, v___x_630_);
v___x_645_ = lean_st_ref_get(v___y_625_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v___x_647_ = l_Lean_Environment_find_x3f(v_env_646_, v_head_628_, v___x_614_);
if (lean_obj_tag(v___x_647_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_673_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_673_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_673_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_673_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
if (lean_obj_tag(v_val_648_) == 6)
{
lean_object* v_val_652_; lean_object* v_toConstantVal_653_; lean_object* v_numFields_654_; lean_object* v_levelParams_655_; lean_object* v_type_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_val_652_ = lean_ctor_get(v_val_648_, 0);
lean_inc_ref(v_val_652_);
lean_dec_ref_known(v_val_648_, 1);
v_toConstantVal_653_ = lean_ctor_get(v_val_652_, 0);
lean_inc_ref(v_toConstantVal_653_);
v_numFields_654_ = lean_ctor_get(v_val_652_, 4);
lean_inc(v_numFields_654_);
lean_dec_ref(v_val_652_);
v_levelParams_655_ = lean_ctor_get(v_toConstantVal_653_, 1);
lean_inc(v_levelParams_655_);
v_type_656_ = lean_ctor_get(v_toConstantVal_653_, 2);
lean_inc_ref(v_type_656_);
lean_dec_ref(v_toConstantVal_653_);
v___x_657_ = l_Lean_Expr_instantiateLevelParams(v_type_656_, v_levelParams_655_, v_us_616_);
lean_dec(v_levelParams_655_);
lean_dec_ref(v_type_656_);
v___x_658_ = l_Lean_Meta_instantiateForall(v___x_657_, v_params_617_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_numFields_654_);
v___x_661_ = v___x_650_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_numFields_654_);
v___x_661_ = v_reuseFailAlloc_664_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__4___redArg(v_a_659_, v___x_661_, v___f_644_, v___x_614_, v___x_614_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
v_as_x27_618_ = v_tail_629_;
v_b_619_ = v___x_630_;
goto _start;
}
else
{
lean_dec_ref(v_type_615_);
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_numFields_654_);
lean_del_object(v___x_650_);
lean_dec_ref(v___f_644_);
lean_dec_ref(v_type_615_);
v_a_665_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_658_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_658_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_del_object(v___x_650_);
lean_dec(v_val_648_);
lean_dec_ref(v___f_644_);
v___y_632_ = v___y_620_;
v___y_633_ = v___y_621_;
v___y_634_ = v___y_622_;
v___y_635_ = v___y_623_;
v___y_636_ = v___y_624_;
v___y_637_ = v___y_625_;
goto v___jp_631_;
}
}
}
else
{
lean_dec(v___x_647_);
lean_dec_ref(v___f_644_);
v___y_632_ = v___y_620_;
v___y_633_ = v___y_621_;
v___y_634_ = v___y_622_;
v___y_635_ = v___y_623_;
v___y_636_ = v___y_624_;
v___y_637_ = v___y_625_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__1);
lean_inc(v_head_628_);
v___x_639_ = l_Lean_MessageData_ofConstName(v_head_628_, v___x_614_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___closed__3);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_615_, v___x_642_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive(lean_object* v_type_674_, lean_object* v_val_675_, lean_object* v_us_676_, lean_object* v_args_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_toConstantVal_685_; lean_object* v_numParams_686_; lean_object* v_numIndices_687_; lean_object* v_ctors_688_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_toConstantVal_685_ = lean_ctor_get(v_val_675_, 0);
lean_inc_ref(v_toConstantVal_685_);
v_numParams_686_ = lean_ctor_get(v_val_675_, 1);
lean_inc(v_numParams_686_);
v_numIndices_687_ = lean_ctor_get(v_val_675_, 2);
lean_inc(v_numIndices_687_);
v_ctors_688_ = lean_ctor_get(v_val_675_, 4);
lean_inc(v_ctors_688_);
lean_dec_ref(v_val_675_);
v___x_720_ = lean_array_get_size(v_args_677_);
v___x_721_ = lean_nat_add(v_numParams_686_, v_numIndices_687_);
lean_dec(v_numIndices_687_);
v___x_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_inc_ref(v_type_674_);
v___x_723_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_674_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_dec_ref_known(v___x_723_, 1);
v___y_690_ = v_a_678_;
v___y_691_ = v_a_679_;
v___y_692_ = v_a_680_;
v___y_693_ = v_a_681_;
v___y_694_ = v_a_682_;
v___y_695_ = v_a_683_;
goto v___jp_689_;
}
else
{
lean_dec(v_ctors_688_);
lean_dec(v_numParams_686_);
lean_dec_ref(v_toConstantVal_685_);
lean_dec_ref(v_args_677_);
lean_dec(v_us_676_);
lean_dec_ref(v_type_674_);
return v___x_723_;
}
}
else
{
v___y_690_ = v_a_678_;
v___y_691_ = v_a_679_;
v___y_692_ = v_a_680_;
v___y_693_ = v_a_681_;
v___y_694_ = v_a_682_;
v___y_695_ = v_a_683_;
goto v___jp_689_;
}
v___jp_689_:
{
lean_object* v_name_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_params_700_; lean_object* v___x_701_; lean_object* v_key_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_name_696_ = lean_ctor_get(v_toConstantVal_685_, 0);
lean_inc(v_name_696_);
lean_dec_ref(v_toConstantVal_685_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_Array_toSubarray___redArg(v_args_677_, v___x_697_, v_numParams_686_);
v___x_699_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___closed__0));
v_params_700_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0___redArg(v___x_698_, v___x_699_);
lean_inc(v_us_676_);
v___x_701_ = l_Lean_Expr_const___override(v_name_696_, v_us_676_);
v_key_702_ = l_Lean_mkAppN(v___x_701_, v_params_700_);
v___x_703_ = lean_st_ref_get(v___y_691_);
v___x_704_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg(v___x_703_, v_key_702_);
lean_dec(v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_705_ = lean_st_ref_take(v___y_691_);
v___x_706_ = lean_box(0);
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2___redArg(v___x_705_, v_key_702_, v___x_706_);
v___x_708_ = lean_st_ref_put(v___y_691_, v___x_707_);
v___x_709_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg(v___x_704_, v_type_674_, v_us_676_, v_params_700_, v_ctors_688_, v___x_706_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v_ctors_688_);
lean_dec_ref(v_params_700_);
lean_dec(v_us_676_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v___x_709_, 0);
lean_dec(v_unused_717_);
v___x_711_ = v___x_709_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_709_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_706_);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_706_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
return v___x_709_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_key_702_);
lean_dec_ref(v_params_700_);
lean_dec(v_ctors_688_);
lean_dec(v_us_676_);
lean_dec_ref(v_type_674_);
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(lean_object* v_type_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_toCold_735_; lean_object* v_currRecDepth_736_; lean_object* v_ref_737_; uint16_t v_optionFlags_738_; uint8_t v_suppressElabErrors_739_; uint8_t v_checkDeprecated_740_; uint8_t v_isRecordingDeps_741_; lean_object* v_maxRecDepth_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_toCold_735_ = lean_ctor_get(v_a_732_, 0);
lean_inc_ref(v_toCold_735_);
v_currRecDepth_736_ = lean_ctor_get(v_a_732_, 1);
lean_inc(v_currRecDepth_736_);
v_ref_737_ = lean_ctor_get(v_a_732_, 2);
lean_inc(v_ref_737_);
v_optionFlags_738_ = lean_ctor_get_uint16(v_a_732_, sizeof(void*)*3);
v_suppressElabErrors_739_ = lean_ctor_get_uint8(v_a_732_, sizeof(void*)*3 + 2);
v_checkDeprecated_740_ = lean_ctor_get_uint8(v_a_732_, sizeof(void*)*3 + 3);
v_isRecordingDeps_741_ = lean_ctor_get_uint8(v_a_732_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_732_);
v_maxRecDepth_742_ = lean_ctor_get(v_toCold_735_, 3);
lean_inc_ref(v_type_727_);
v___f_743_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___boxed), 10, 1);
lean_closure_set(v___f_743_, 0, v_type_727_);
v___x_744_ = l_Lean_instInhabitedExpr;
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_nat_dec_eq(v_maxRecDepth_742_, v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_eq(v_currRecDepth_736_, v_maxRecDepth_742_);
if (v___x_819_ == 0)
{
goto v___jp_745_;
}
else
{
lean_object* v___x_820_; 
lean_dec_ref(v___f_743_);
lean_dec(v_currRecDepth_736_);
lean_dec_ref(v_toCold_735_);
lean_dec_ref(v_type_727_);
v___x_820_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg(v_ref_737_);
return v___x_820_;
}
}
else
{
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_currRecDepth_736_, v___x_746_);
lean_dec(v_currRecDepth_736_);
v___x_748_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_748_, 0, v_toCold_735_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
lean_ctor_set(v___x_748_, 2, v_ref_737_);
lean_ctor_set_uint16(v___x_748_, sizeof(void*)*3, v_optionFlags_738_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*3 + 2, v_suppressElabErrors_739_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*3 + 3, v_checkDeprecated_740_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*3 + 4, v_isRecordingDeps_741_);
lean_inc_ref(v_type_727_);
v___x_749_ = l_Lean_Meta_isProp(v_type_727_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_808_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_808_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_808_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_808_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = lean_unbox(v_a_750_);
if (v___x_754_ == 0)
{
uint8_t v___x_755_; lean_object* v___x_756_; 
lean_del_object(v___x_752_);
v___x_755_ = 1;
lean_inc(v_a_733_);
lean_inc_ref(v___x_748_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc_ref(v_type_727_);
v___x_756_ = lean_whnf(v_type_727_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
switch(lean_obj_tag(v_a_757_))
{
case 3:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref_known(v_a_757_, 1);
lean_dec(v_a_750_);
lean_dec_ref(v___f_743_);
v___x_758_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___lam__0___closed__1);
v___x_759_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_727_, v___x_758_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_759_;
}
case 7:
{
uint8_t v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_type_727_);
v___x_760_ = lean_unbox(v_a_750_);
lean_dec(v_a_750_);
v___x_761_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg(v_a_757_, v___f_743_, v___x_760_, v___x_755_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_761_;
}
default: 
{
lean_object* v___x_762_; 
lean_dec_ref(v___f_743_);
v___x_762_ = l_Lean_Expr_getAppFn(v_a_757_);
switch(lean_obj_tag(v___x_762_))
{
case 1:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_a_757_);
lean_dec(v_a_750_);
v___x_763_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__1);
v___x_764_ = l_Lean_MessageData_ofExpr(v___x_762_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__3);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_throwUnsupported___redArg(v_type_727_, v___x_767_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_768_;
}
case 4:
{
lean_object* v_declName_769_; lean_object* v_us_770_; lean_object* v_nargs_771_; lean_object* v_dummy_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_env_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v_declName_769_ = lean_ctor_get(v___x_762_, 0);
lean_inc_n(v_declName_769_, 2);
v_us_770_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_us_770_);
lean_dec_ref_known(v___x_762_, 2);
v_nargs_771_ = l_Lean_Expr_getAppNumArgs(v_a_757_);
v_dummy_772_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4, &l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4_once, _init_l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__4);
lean_inc(v_nargs_771_);
v___x_773_ = lean_mk_array(v_nargs_771_, v_dummy_772_);
v___x_774_ = lean_nat_sub(v_nargs_771_, v___x_746_);
lean_dec(v_nargs_771_);
v___x_775_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_757_, v___x_773_, v___x_774_);
v___x_776_ = lean_st_ref_get(v_a_733_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc_ref(v_env_777_);
lean_dec(v___x_776_);
v___x_778_ = lean_unbox(v_a_750_);
lean_dec(v_a_750_);
v___x_779_ = l_Lean_Environment_find_x3f(v_env_777_, v_declName_769_, v___x_778_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_val_780_; 
v_val_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref_known(v___x_779_, 1);
switch(lean_obj_tag(v_val_780_))
{
case 5:
{
lean_object* v_val_781_; lean_object* v___x_782_; 
lean_dec(v_declName_769_);
v_val_781_ = lean_ctor_get(v_val_780_, 0);
lean_inc_ref(v_val_781_);
lean_dec_ref_known(v_val_780_, 1);
v___x_782_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive(v_type_727_, v_val_781_, v_us_770_, v___x_775_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_782_;
}
case 4:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_dec_ref_known(v_val_780_, 1);
lean_dec(v_us_770_);
v___x_783_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___closed__6));
v___x_784_ = lean_name_eq(v_declName_769_, v___x_783_);
lean_dec(v_declName_769_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v___x_775_);
v___x_785_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_array_get_size(v___x_775_);
v___x_787_ = lean_unsigned_to_nat(2u);
v___x_788_ = lean_nat_dec_eq(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec_ref(v___x_775_);
v___x_789_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec_ref(v_type_727_);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get(v___x_744_, v___x_775_, v___x_790_);
lean_dec_ref(v___x_775_);
v_type_727_ = v___x_791_;
v_a_732_ = v___x_748_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_793_; 
lean_dec(v_val_780_);
lean_dec_ref(v___x_775_);
lean_dec(v_us_770_);
lean_dec(v_declName_769_);
v___x_793_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_793_;
}
}
}
else
{
lean_object* v___x_794_; 
lean_dec(v___x_779_);
lean_dec_ref(v___x_775_);
lean_dec(v_us_770_);
lean_dec(v_declName_769_);
v___x_794_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_794_;
}
}
default: 
{
lean_object* v___x_795_; 
lean_dec_ref(v___x_762_);
lean_dec(v_a_757_);
lean_dec(v_a_750_);
v___x_795_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_throwStuck(v_type_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v___x_748_, v_a_733_);
lean_dec_ref_known(v___x_748_, 3);
return v___x_795_;
}
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_a_750_);
lean_dec_ref_known(v___x_748_, 3);
lean_dec_ref(v___f_743_);
lean_dec_ref(v_type_727_);
v_a_796_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_756_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_756_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_dec(v_a_750_);
lean_dec_ref_known(v___x_748_, 3);
lean_dec_ref(v___f_743_);
lean_dec_ref(v_type_727_);
v___x_804_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_804_);
v___x_806_ = v___x_752_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref_known(v___x_748_, 3);
lean_dec_ref(v___f_743_);
lean_dec_ref(v_type_727_);
v_a_809_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_749_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_749_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3(lean_object* v_a_821_, lean_object* v_as_822_, size_t v_sz_823_, size_t v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_824_, v_sz_823_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_a_821_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_825_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_835_ = lean_box(0);
v_a_836_ = lean_array_uget_borrowed(v_as_822_, v_i_824_);
v___x_837_ = l_Lean_Expr_fvarId_x21(v_a_836_);
v___x_838_ = l_Lean_FVarId_getUserName___redArg(v___x_837_, v___y_828_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v_rootType_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v_rootType_840_ = lean_ctor_get(v___y_826_, 0);
lean_inc(v_a_821_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_a_821_);
lean_ctor_set(v___x_841_, 1, v_a_839_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_inc_ref(v_rootType_840_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_rootType_840_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
lean_inc(v_a_836_);
v___x_844_ = lean_infer_type(v_a_836_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
lean_inc_ref(v___y_830_);
v___x_846_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(v_a_845_, v___x_843_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec_ref_known(v___x_843_, 2);
if (lean_obj_tag(v___x_846_) == 0)
{
size_t v___x_847_; size_t v___x_848_; 
lean_dec_ref_known(v___x_846_, 1);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_824_, v___x_847_);
v_i_824_ = v___x_848_;
v_b_825_ = v___x_835_;
goto _start;
}
else
{
lean_dec(v_a_821_);
return v___x_846_;
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref_known(v___x_843_, 2);
lean_dec(v_a_821_);
v_a_850_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_844_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_844_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_821_);
v_a_858_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_838_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_838_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___lam__0(lean_object* v_head_866_, lean_object* v___x_867_, lean_object* v_fields_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; 
v_sz_877_ = lean_array_size(v_fields_868_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3(v_head_866_, v_fields_868_, v_sz_877_, v___x_878_, v___x_867_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_879_, 0);
lean_dec(v_unused_887_);
v___x_881_ = v___x_879_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_879_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_867_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_867_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3___boxed(lean_object* v_a_888_, lean_object* v_as_889_, lean_object* v_sz_890_, lean_object* v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
size_t v_sz_boxed_900_; size_t v_i_boxed_901_; lean_object* v_res_902_; 
v_sz_boxed_900_ = lean_unbox_usize(v_sz_890_);
lean_dec(v_sz_890_);
v_i_boxed_901_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__3(v_a_888_, v_as_889_, v_sz_boxed_900_, v_i_boxed_901_, v_b_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec_ref(v_as_889_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive___boxed(lean_object* v_type_903_, lean_object* v_val_904_, lean_object* v_us_905_, lean_object* v_args_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive(v_type_903_, v_val_904_, v_us_905_, v_args_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg___boxed(lean_object* v___x_915_, lean_object* v_type_916_, lean_object* v_us_917_, lean_object* v_params_918_, lean_object* v_as_x27_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v___x_20017__boxed_928_; lean_object* v_res_929_; 
v___x_20017__boxed_928_ = lean_unbox(v___x_915_);
v_res_929_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg(v___x_20017__boxed_928_, v_type_916_, v_us_917_, v_params_918_, v_as_x27_919_, v_b_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v_as_x27_919_);
lean_dec_ref(v_params_918_);
lean_dec(v_us_917_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check___boxed(lean_object* v_type_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(v_type_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7(lean_object* v_00_u03b1_939_, lean_object* v_type_940_, lean_object* v_k_941_, uint8_t v_cleanupAnnotations_942_, uint8_t v_whnfType_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___redArg(v_type_940_, v_k_941_, v_cleanupAnnotations_942_, v_whnfType_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7___boxed(lean_object* v_00_u03b1_952_, lean_object* v_type_953_, lean_object* v_k_954_, lean_object* v_cleanupAnnotations_955_, lean_object* v_whnfType_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_964_; uint8_t v_whnfType_boxed_965_; lean_object* v_res_966_; 
v_cleanupAnnotations_boxed_964_ = lean_unbox(v_cleanupAnnotations_955_);
v_whnfType_boxed_965_ = lean_unbox(v_whnfType_956_);
v_res_966_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__7(v_00_u03b1_952_, v_type_953_, v_k_954_, v_cleanupAnnotations_boxed_964_, v_whnfType_boxed_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8(lean_object* v_00_u03b1_967_, lean_object* v_ref_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___redArg(v_ref_968_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8___boxed(lean_object* v_00_u03b1_977_, lean_object* v_ref_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_spec__8(v_00_u03b1_977_, v_ref_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0(lean_object* v_inst_987_, lean_object* v_R_988_, lean_object* v_a_989_, lean_object* v_b_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__0___redArg(v_a_989_, v_b_990_);
return v___x_991_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1(lean_object* v_00_u03b2_992_, lean_object* v_m_993_, lean_object* v_a_994_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___redArg(v_m_993_, v_a_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1___boxed(lean_object* v_00_u03b2_996_, lean_object* v_m_997_, lean_object* v_a_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1(v_00_u03b2_996_, v_m_997_, v_a_998_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_m_997_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2(lean_object* v_00_u03b2_1001_, lean_object* v_m_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2___redArg(v_m_1002_, v_a_1003_, v_b_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5(uint8_t v___x_1006_, lean_object* v_type_1007_, lean_object* v_us_1008_, lean_object* v_params_1009_, lean_object* v_as_1010_, lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v_a_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___redArg(v___x_1006_, v_type_1007_, v_us_1008_, v_params_1009_, v_as_x27_1011_, v_b_1012_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5___boxed(lean_object* v___x_1022_, lean_object* v_type_1023_, lean_object* v_us_1024_, lean_object* v_params_1025_, lean_object* v_as_1026_, lean_object* v_as_x27_1027_, lean_object* v_b_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v___x_20530__boxed_1037_; lean_object* v_res_1038_; 
v___x_20530__boxed_1037_ = lean_unbox(v___x_1022_);
v_res_1038_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__5(v___x_20530__boxed_1037_, v_type_1023_, v_us_1024_, v_params_1025_, v_as_1026_, v_as_x27_1027_, v_b_1028_, v_a_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v_as_x27_1027_);
lean_dec(v_as_1026_);
lean_dec_ref(v_params_1025_);
lean_dec(v_us_1024_);
return v_res_1038_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1(lean_object* v_00_u03b2_1039_, lean_object* v_a_1040_, lean_object* v_x_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___redArg(v_a_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_a_1044_, lean_object* v_x_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__1_spec__1(v_00_u03b2_1043_, v_a_1044_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec_ref(v_a_1044_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3(lean_object* v_00_u03b2_1048_, lean_object* v_data_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3___redArg(v_data_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8(lean_object* v_00_u03b2_1051_, lean_object* v_i_1052_, lean_object* v_source_1053_, lean_object* v_target_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8___redArg(v_i_1052_, v_source_1053_, v_target_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check_checkInductive_spec__2_spec__3_spec__8_spec__11___redArg(v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0(lean_object* v___x_1060_, lean_object* v_type_1061_, lean_object* v___x_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_st_mk_ref(v___x_1060_);
v___x_1069_ = l___private_Lean_Compiler_LCNF_WithPtrEq_0__Lean_Compiler_LCNF_WithPtrEq_check(v_type_1061_, v___x_1062_, v___x_1068_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_get(v___x_1068_);
lean_dec(v___x_1068_);
lean_dec(v___x_1074_);
if (v_isShared_1073_ == 0)
{
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1070_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_dec(v___x_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0___boxed(lean_object* v___x_1079_, lean_object* v_type_1080_, lean_object* v___x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0(v___x_1079_, v_type_1080_, v___x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec_ref(v___x_1081_);
return v_res_1087_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_unsigned_to_nat(16u);
v___x_1090_ = lean_mk_array(v___x_1089_, v___x_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_obj_once(&l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0, &l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0_once, _init_l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__0);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType(lean_object* v_type_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___y_1101_; lean_object* v___x_1118_; uint8_t v_transparency_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1118_ = l_Lean_Meta_Context_config(v_a_1095_);
v_transparency_1119_ = lean_ctor_get_uint8(v___x_1118_, 9);
lean_dec_ref(v___x_1118_);
v___x_1120_ = 0;
v___x_1121_ = lean_box(0);
lean_inc_ref(v_type_1094_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_type_1094_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_obj_once(&l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1, &l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1_once, _init_l_Lean_Compiler_LCNF_checkWithPtrEqType___closed__1);
v___x_1124_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1119_, v___x_1120_);
if (v___x_1124_ == 0)
{
lean_object* v_keyedConfig_1125_; uint8_t v_trackZetaDelta_1126_; lean_object* v_zetaDeltaSet_1127_; lean_object* v_lctx_1128_; lean_object* v_localInstances_1129_; lean_object* v_defEqCtx_x3f_1130_; lean_object* v_synthPendingDepth_1131_; lean_object* v_customCanUnfoldPredicate_x3f_1132_; uint8_t v_univApprox_1133_; uint8_t v_inTypeClassResolution_1134_; uint8_t v_cacheInferType_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_keyedConfig_1125_ = lean_ctor_get(v_a_1095_, 0);
v_trackZetaDelta_1126_ = lean_ctor_get_uint8(v_a_1095_, sizeof(void*)*7);
v_zetaDeltaSet_1127_ = lean_ctor_get(v_a_1095_, 1);
v_lctx_1128_ = lean_ctor_get(v_a_1095_, 2);
v_localInstances_1129_ = lean_ctor_get(v_a_1095_, 3);
v_defEqCtx_x3f_1130_ = lean_ctor_get(v_a_1095_, 4);
v_synthPendingDepth_1131_ = lean_ctor_get(v_a_1095_, 5);
v_customCanUnfoldPredicate_x3f_1132_ = lean_ctor_get(v_a_1095_, 6);
v_univApprox_1133_ = lean_ctor_get_uint8(v_a_1095_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1134_ = lean_ctor_get_uint8(v_a_1095_, sizeof(void*)*7 + 2);
v_cacheInferType_1135_ = lean_ctor_get_uint8(v_a_1095_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1125_);
v___x_1136_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1120_, v_keyedConfig_1125_);
lean_inc(v_customCanUnfoldPredicate_x3f_1132_);
lean_inc(v_synthPendingDepth_1131_);
lean_inc(v_defEqCtx_x3f_1130_);
lean_inc_ref(v_localInstances_1129_);
lean_inc_ref(v_lctx_1128_);
lean_inc(v_zetaDeltaSet_1127_);
v___x_1137_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_zetaDeltaSet_1127_);
lean_ctor_set(v___x_1137_, 2, v_lctx_1128_);
lean_ctor_set(v___x_1137_, 3, v_localInstances_1129_);
lean_ctor_set(v___x_1137_, 4, v_defEqCtx_x3f_1130_);
lean_ctor_set(v___x_1137_, 5, v_synthPendingDepth_1131_);
lean_ctor_set(v___x_1137_, 6, v_customCanUnfoldPredicate_x3f_1132_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7, v_trackZetaDelta_1126_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 1, v_univApprox_1133_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1134_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 3, v_cacheInferType_1135_);
lean_inc_ref(v_a_1097_);
v___x_1138_ = l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0(v___x_1123_, v_type_1094_, v___x_1122_, v___x_1137_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec_ref_known(v___x_1137_, 7);
lean_dec_ref_known(v___x_1122_, 2);
v___y_1101_ = v___x_1138_;
goto v___jp_1100_;
}
else
{
lean_object* v___x_1139_; 
lean_inc_ref(v_a_1097_);
v___x_1139_ = l_Lean_Compiler_LCNF_checkWithPtrEqType___lam__0(v___x_1123_, v_type_1094_, v___x_1122_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec_ref_known(v___x_1122_, 2);
v___y_1101_ = v___x_1139_;
goto v___jp_1100_;
}
v___jp_1100_:
{
if (lean_obj_tag(v___y_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___y_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___y_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___y_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___y_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___y_1101_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___y_1101_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___y_1101_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___y_1101_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkWithPtrEqType___boxed(lean_object* v_type_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Compiler_LCNF_checkWithPtrEqType(v_type_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1146_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_WithPtrEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_WithPtrEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_WithPtrEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_WithPtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_WithPtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_WithPtrEq(builtin);
}
#ifdef __cplusplus
}
#endif
