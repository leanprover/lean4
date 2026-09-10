// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.TacticContext
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_sat_solver;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_app_path();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "cadical"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_expr_def"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 227, 101, 23, 202, 228, 100, 227)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_cert_def"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 231, 4, 246, 116, 103, 142, 158)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "_reflection_def"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__4_value),LEAN_SCALAR_PTR_LITERAL(42, 138, 185, 107, 82, 210, 255, 77)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__6_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__8_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Using SAT solver at '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 0)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc_ref(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(lean_object* v_msg_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_13_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__3));
v___x_21_ = lean_unsigned_to_nat(14u);
v___x_22_ = lean_unsigned_to_nat(22u);
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__2));
v___x_24_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__1));
v___x_25_ = l_mkPanicMessageWithDecl(v___x_24_, v___x_23_, v___x_22_, v___x_21_, v___x_20_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(lean_object* v_a_26_){
_start:
{
lean_object* v_toCold_28_; lean_object* v_ref_29_; lean_object* v_options_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_toCold_28_ = lean_ctor_get(v_a_26_, 0);
v_ref_29_ = lean_ctor_get(v_a_26_, 2);
v_options_30_ = lean_ctor_get(v_toCold_28_, 2);
v___x_31_ = l_Lean_Meta_Tactic_BVDecide_sat_solver;
v___x_32_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(v_options_30_, v___x_31_);
v___x_33_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_34_ = lean_string_dec_eq(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_32_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; 
lean_dec_ref(v___x_32_);
v___x_36_ = lean_io_app_path();
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_58_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_58_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_58_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___y_42_; lean_object* v___x_54_; 
v___x_54_ = l_System_FilePath_parent(v_a_37_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4);
v___x_56_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(v___x_55_);
v___y_42_ = v___x_56_;
goto v___jp_41_;
}
else
{
lean_object* v_val_57_; 
v_val_57_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v___x_54_, 1);
v___y_42_ = v_val_57_;
goto v___jp_41_;
}
v___jp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_43_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0));
v___x_44_ = l_System_FilePath_join(v___y_42_, v___x_43_);
v___x_45_ = l_System_FilePath_exeExtension;
v___x_46_ = l_System_FilePath_withExtension(v___x_44_, v___x_45_);
v___x_47_ = l_System_FilePath_pathExists(v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_49_; 
lean_dec_ref(v___x_46_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_43_);
v___x_49_ = v___x_39_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_43_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
else
{
lean_object* v___x_52_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_46_);
v___x_52_ = v___x_39_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_46_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_70_; 
v_a_59_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_70_ == 0)
{
v___x_61_ = v___x_36_;
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_36_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_63_ = lean_io_error_to_string(v_a_59_);
v___x_64_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
v___x_65_ = l_Lean_MessageData_ofFormat(v___x_64_);
lean_inc(v_ref_29_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_ref_29_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_66_);
v___x_68_ = v___x_61_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___boxed(lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_71_);
lean_dec_ref(v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_toCold_91_; lean_object* v_mctx_92_; lean_object* v_lctx_93_; lean_object* v_options_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_env_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_env_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_84_);
v_toCold_91_ = lean_ctor_get(v___y_85_, 0);
v_mctx_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_92_);
lean_dec(v___x_90_);
v_lctx_93_ = lean_ctor_get(v___y_83_, 2);
v_options_94_ = lean_ctor_get(v_toCold_91_, 2);
lean_inc_ref(v_options_94_);
lean_inc_ref(v_lctx_93_);
v___x_95_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_95_, 0, v_env_89_);
lean_ctor_set(v___x_95_, 1, v_mctx_92_);
lean_ctor_set(v___x_95_, 2, v_lctx_93_);
lean_ctor_set(v___x_95_, 3, v_options_94_);
v___x_96_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_msgData_82_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0___boxed(lean_object* v_msgData_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msgData_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_105_; double v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_float_of_nat(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(lean_object* v_cls_109_, lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v___x_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_162_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 2);
v___x_117_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_162_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_162_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_162_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v_traceState_123_; lean_object* v_env_124_; lean_object* v_nextMacroScope_125_; lean_object* v_ngen_126_; lean_object* v_auxDeclNGen_127_; lean_object* v_cache_128_; lean_object* v_messages_129_; lean_object* v_infoState_130_; lean_object* v_snapshotTasks_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_161_; 
v___x_122_ = lean_st_ref_take(v___y_114_);
v_traceState_123_ = lean_ctor_get(v___x_122_, 4);
v_env_124_ = lean_ctor_get(v___x_122_, 0);
v_nextMacroScope_125_ = lean_ctor_get(v___x_122_, 1);
v_ngen_126_ = lean_ctor_get(v___x_122_, 2);
v_auxDeclNGen_127_ = lean_ctor_get(v___x_122_, 3);
v_cache_128_ = lean_ctor_get(v___x_122_, 5);
v_messages_129_ = lean_ctor_get(v___x_122_, 6);
v_infoState_130_ = lean_ctor_get(v___x_122_, 7);
v_snapshotTasks_131_ = lean_ctor_get(v___x_122_, 8);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_161_ == 0)
{
v___x_133_ = v___x_122_;
v_isShared_134_ = v_isSharedCheck_161_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_snapshotTasks_131_);
lean_inc(v_infoState_130_);
lean_inc(v_messages_129_);
lean_inc(v_cache_128_);
lean_inc(v_traceState_123_);
lean_inc(v_auxDeclNGen_127_);
lean_inc(v_ngen_126_);
lean_inc(v_nextMacroScope_125_);
lean_inc(v_env_124_);
lean_dec(v___x_122_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_161_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
uint64_t v_tid_135_; lean_object* v_traces_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_160_; 
v_tid_135_ = lean_ctor_get_uint64(v_traceState_123_, sizeof(void*)*1);
v_traces_136_ = lean_ctor_get(v_traceState_123_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_traceState_123_);
if (v_isSharedCheck_160_ == 0)
{
v___x_138_ = v_traceState_123_;
v_isShared_139_ = v_isSharedCheck_160_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_traces_136_);
lean_dec(v_traceState_123_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_160_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; double v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_140_ = lean_box(0);
v___x_141_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0);
v___x_142_ = 0;
v___x_143_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_144_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_144_, 0, v_cls_109_);
lean_ctor_set(v___x_144_, 1, v___x_140_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
lean_ctor_set_float(v___x_144_, sizeof(void*)*3, v___x_141_);
lean_ctor_set_float(v___x_144_, sizeof(void*)*3 + 8, v___x_141_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*3 + 16, v___x_142_);
v___x_145_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1));
v___x_146_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v_a_118_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_inc(v_ref_116_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_ref_116_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_Lean_PersistentArray_push___redArg(v_traces_136_, v___x_147_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_148_);
v___x_150_ = v___x_138_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_148_);
lean_ctor_set_uint64(v_reuseFailAlloc_159_, sizeof(void*)*1, v_tid_135_);
v___x_150_ = v_reuseFailAlloc_159_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v___x_150_);
v___x_152_ = v___x_133_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_env_124_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_nextMacroScope_125_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_ngen_126_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_auxDeclNGen_127_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 5, v_cache_128_);
lean_ctor_set(v_reuseFailAlloc_158_, 6, v_messages_129_);
lean_ctor_set(v_reuseFailAlloc_158_, 7, v_infoState_130_);
lean_ctor_set(v_reuseFailAlloc_158_, 8, v_snapshotTasks_131_);
v___x_152_ = v_reuseFailAlloc_158_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_153_ = lean_st_ref_put(v___y_114_, v___x_152_);
v___x_154_ = lean_box(0);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_154_);
v___x_156_ = v___x_120_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___boxed(lean_object* v_cls_163_, lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v_cls_163_, v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9));
v___x_191_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11));
v___x_192_ = l_Lean_Name_append(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object* v_lratPath_199_, lean_object* v_config_200_, lean_object* v_restrictedTypes_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1));
v___x_210_ = l_Lean_Elab_Term_mkAuxName(v___x_209_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3));
v___x_213_ = l_Lean_Elab_Term_mkAuxName(v___x_212_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5));
v___x_216_ = l_Lean_Elab_Term_mkAuxName(v___x_215_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_206_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_250_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_250_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_250_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_250_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_toCold_228_; lean_object* v_options_229_; uint8_t v_hasTrace_230_; 
v_toCold_228_ = lean_ctor_get(v_a_206_, 0);
v_options_229_ = lean_ctor_get(v_toCold_228_, 2);
v_hasTrace_230_ = lean_ctor_get_uint8(v_options_229_, sizeof(void*)*1);
if (v_hasTrace_230_ == 0)
{
goto v___jp_223_;
}
else
{
lean_object* v_inheritedTraceOptions_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_inheritedTraceOptions_231_ = lean_ctor_get(v_toCold_228_, 11);
v___x_232_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9));
v___x_233_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12);
v___x_234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_231_, v_options_229_, v___x_233_);
if (v___x_234_ == 0)
{
goto v___jp_223_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_235_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14);
lean_inc(v_a_219_);
v___x_236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_236_, 0, v_a_219_);
v___x_237_ = l_Lean_MessageData_ofFormat(v___x_236_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v___x_232_, v___x_240_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_dec_ref_known(v___x_241_, 1);
goto v___jp_223_;
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_221_);
lean_dec(v_a_219_);
lean_dec(v_a_217_);
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_restrictedTypes_201_);
lean_dec_ref(v_config_200_);
lean_dec_ref(v_lratPath_199_);
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
v___jp_223_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_224_, 0, v_a_211_);
lean_ctor_set(v___x_224_, 1, v_a_214_);
lean_ctor_set(v___x_224_, 2, v_a_217_);
lean_ctor_set(v___x_224_, 3, v_a_219_);
lean_ctor_set(v___x_224_, 4, v_lratPath_199_);
lean_ctor_set(v___x_224_, 5, v_config_200_);
lean_ctor_set(v___x_224_, 6, v_restrictedTypes_201_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_217_);
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_restrictedTypes_201_);
lean_dec_ref(v_config_200_);
lean_dec_ref(v_lratPath_199_);
v_a_251_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_218_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_218_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_restrictedTypes_201_);
lean_dec_ref(v_config_200_);
lean_dec_ref(v_lratPath_199_);
v_a_259_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_216_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_216_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_a_211_);
lean_dec(v_restrictedTypes_201_);
lean_dec_ref(v_config_200_);
lean_dec_ref(v_lratPath_199_);
v_a_267_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_213_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_213_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_restrictedTypes_201_);
lean_dec_ref(v_config_200_);
lean_dec_ref(v_lratPath_199_);
v_a_275_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_210_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_210_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___boxed(lean_object* v_lratPath_283_, lean_object* v_config_284_, lean_object* v_restrictedTypes_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratPath_283_, v_config_284_, v_restrictedTypes_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(lean_object* v_cls_294_, lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v_cls_294_, v_msg_295_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___boxed(lean_object* v_cls_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(v_cls_304_, v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_313_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
}
#ifdef __cplusplus
}
#endif
