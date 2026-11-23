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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_28_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_26_);
v___x_29_ = l_Lean_Meta_Tactic_BVDecide_sat_solver;
v___x_30_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__0(v___x_28_, v___x_29_);
lean_dec_ref(v___x_28_);
v___x_31_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_32_ = lean_string_dec_eq(v___x_30_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_30_);
return v___x_33_;
}
else
{
lean_object* v_ref_34_; lean_object* v___x_35_; 
lean_dec_ref(v___x_30_);
v_ref_34_ = lean_ctor_get(v_a_26_, 2);
v___x_35_ = lean_io_app_path();
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_57_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_57_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___y_41_; lean_object* v___x_53_; 
v___x_53_ = l_System_FilePath_parent(v_a_36_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__4);
v___x_55_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1(v___x_54_);
v___y_41_ = v___x_55_;
goto v___jp_40_;
}
else
{
lean_object* v_val_56_; 
v_val_56_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v___x_53_, 1);
v___y_41_ = v_val_56_;
goto v___jp_40_;
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___closed__0));
v___x_43_ = l_System_FilePath_join(v___y_41_, v___x_42_);
v___x_44_ = l_System_FilePath_exeExtension;
v___x_45_ = l_System_FilePath_withExtension(v___x_43_, v___x_44_);
v___x_46_ = l_System_FilePath_pathExists(v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_48_; 
lean_dec_ref(v___x_45_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_42_);
v___x_48_ = v___x_38_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_42_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
else
{
lean_object* v___x_51_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_45_);
v___x_51_ = v___x_38_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_45_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_69_; 
v_a_58_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_69_ == 0)
{
v___x_60_ = v___x_35_;
v_isShared_61_ = v_isSharedCheck_69_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_35_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_69_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_62_ = lean_io_error_to_string(v_a_58_);
v___x_63_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = l_Lean_MessageData_ofFormat(v___x_63_);
lean_inc(v_ref_34_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_ref_34_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_65_);
v___x_67_ = v___x_60_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg___boxed(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_70_);
lean_dec_ref(v_a_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___boxed(lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver(v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(lean_object* v_msgData_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_env_88_; uint8_t v___x_89_; lean_object* v_env_90_; lean_object* v___x_91_; lean_object* v_toCold_92_; lean_object* v_mctx_93_; lean_object* v_lctx_94_; lean_object* v_options_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_87_ = lean_st_ref_get(v___y_85_);
v_env_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_env_88_);
lean_dec(v___x_87_);
v___x_89_ = 0;
v_env_90_ = l_Lean_Environment_setRecordingDeps(v_env_88_, v___x_89_);
v___x_91_ = lean_st_ref_get(v___y_83_);
v_toCold_92_ = lean_ctor_get(v___y_84_, 0);
v_mctx_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_mctx_93_);
lean_dec(v___x_91_);
v_lctx_94_ = lean_ctor_get(v___y_82_, 2);
v_options_95_ = lean_ctor_get(v_toCold_92_, 2);
lean_inc_ref(v_options_95_);
lean_inc_ref(v_lctx_94_);
v___x_96_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_96_, 0, v_env_90_);
lean_ctor_set(v___x_96_, 1, v_mctx_93_);
lean_ctor_set(v___x_96_, 2, v_lctx_94_);
lean_ctor_set(v___x_96_, 3, v_options_95_);
v___x_97_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_msgData_81_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0___boxed(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msgData_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_106_; double v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_float_of_nat(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(lean_object* v_cls_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_ref_117_; lean_object* v___x_118_; lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_164_; 
v_ref_117_ = lean_ctor_get(v___y_114_, 2);
v___x_118_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0_spec__0(v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_164_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_164_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_164_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v_traceState_124_; lean_object* v_env_125_; lean_object* v_nextMacroScope_126_; lean_object* v_ngen_127_; lean_object* v_auxDeclNGen_128_; lean_object* v_cache_129_; lean_object* v_recordedDeps_130_; lean_object* v_messages_131_; lean_object* v_infoState_132_; lean_object* v_snapshotTasks_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_163_; 
v___x_123_ = lean_st_ref_take(v___y_115_);
v_traceState_124_ = lean_ctor_get(v___x_123_, 4);
v_env_125_ = lean_ctor_get(v___x_123_, 0);
v_nextMacroScope_126_ = lean_ctor_get(v___x_123_, 1);
v_ngen_127_ = lean_ctor_get(v___x_123_, 2);
v_auxDeclNGen_128_ = lean_ctor_get(v___x_123_, 3);
v_cache_129_ = lean_ctor_get(v___x_123_, 5);
v_recordedDeps_130_ = lean_ctor_get(v___x_123_, 6);
v_messages_131_ = lean_ctor_get(v___x_123_, 7);
v_infoState_132_ = lean_ctor_get(v___x_123_, 8);
v_snapshotTasks_133_ = lean_ctor_get(v___x_123_, 9);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_163_ == 0)
{
v___x_135_ = v___x_123_;
v_isShared_136_ = v_isSharedCheck_163_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snapshotTasks_133_);
lean_inc(v_infoState_132_);
lean_inc(v_messages_131_);
lean_inc(v_recordedDeps_130_);
lean_inc(v_cache_129_);
lean_inc(v_traceState_124_);
lean_inc(v_auxDeclNGen_128_);
lean_inc(v_ngen_127_);
lean_inc(v_nextMacroScope_126_);
lean_inc(v_env_125_);
lean_dec(v___x_123_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_163_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
uint64_t v_tid_137_; lean_object* v_traces_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_162_; 
v_tid_137_ = lean_ctor_get_uint64(v_traceState_124_, sizeof(void*)*1);
v_traces_138_ = lean_ctor_get(v_traceState_124_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v_traceState_124_);
if (v_isSharedCheck_162_ == 0)
{
v___x_140_ = v_traceState_124_;
v_isShared_141_ = v_isSharedCheck_162_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_traces_138_);
lean_dec(v_traceState_124_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_162_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; double v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_142_ = lean_box(0);
v___x_143_ = lean_box(0);
v___x_144_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__0);
v___x_145_ = 0;
v___x_146_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_147_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_147_, 0, v_cls_110_);
lean_ctor_set(v___x_147_, 1, v___x_143_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set_float(v___x_147_, sizeof(void*)*3, v___x_144_);
lean_ctor_set_float(v___x_147_, sizeof(void*)*3 + 8, v___x_144_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*3 + 16, v___x_145_);
v___x_148_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___closed__1));
v___x_149_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v_a_119_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
lean_inc(v_ref_117_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_ref_117_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_PersistentArray_push___redArg(v_traces_138_, v___x_150_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_151_);
v___x_153_ = v___x_140_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_151_);
lean_ctor_set_uint64(v_reuseFailAlloc_161_, sizeof(void*)*1, v_tid_137_);
v___x_153_ = v_reuseFailAlloc_161_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v___x_153_);
v___x_155_ = v___x_135_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_env_125_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_nextMacroScope_126_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_ngen_127_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_auxDeclNGen_128_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 5, v_cache_129_);
lean_ctor_set(v_reuseFailAlloc_160_, 6, v_recordedDeps_130_);
lean_ctor_set(v_reuseFailAlloc_160_, 7, v_messages_131_);
lean_ctor_set(v_reuseFailAlloc_160_, 8, v_infoState_132_);
lean_ctor_set(v_reuseFailAlloc_160_, 9, v_snapshotTasks_133_);
v___x_155_ = v_reuseFailAlloc_160_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_st_ref_put(v___y_115_, v___x_155_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_142_);
v___x_158_ = v___x_121_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_142_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg___boxed(lean_object* v_cls_165_, lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v_cls_165_, v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9));
v___x_193_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__11));
v___x_194_ = l_Lean_Name_append(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__13));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__15));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object* v_lratPath_201_, lean_object* v_config_202_, lean_object* v_restrictedTypes_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__1));
v___x_212_ = l_Lean_Elab_Term_mkAuxName(v___x_211_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__3));
v___x_215_ = l_Lean_Elab_Term_mkAuxName(v___x_214_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__5));
v___x_218_ = l_Lean_Elab_Term_mkAuxName(v___x_217_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = l___private_Lean_Meta_Tactic_BVDecide_TacticContext_0__Lean_Meta_Tactic_BVDecide_TacticContext_new_determineSolver___redArg(v_a_208_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_252_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_252_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_252_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_252_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_toCold_230_; lean_object* v_options_231_; uint8_t v_hasTrace_232_; 
v_toCold_230_ = lean_ctor_get(v_a_208_, 0);
v_options_231_ = lean_ctor_get(v_toCold_230_, 2);
v_hasTrace_232_ = lean_ctor_get_uint8(v_options_231_, sizeof(void*)*1);
if (v_hasTrace_232_ == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v_inheritedTraceOptions_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_inheritedTraceOptions_233_ = lean_ctor_get(v_toCold_230_, 11);
v___x_234_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__9));
v___x_235_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__12);
v___x_236_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_233_, v_options_231_, v___x_235_);
if (v___x_236_ == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_237_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__14);
lean_inc(v_a_221_);
v___x_238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_238_, 0, v_a_221_);
v___x_239_ = l_Lean_MessageData_ofFormat(v___x_238_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_237_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16, &l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_TacticContext_new___closed__16);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v___x_234_, v___x_242_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_dec_ref_known(v___x_243_, 1);
goto v___jp_225_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_del_object(v___x_223_);
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec(v_a_216_);
lean_dec(v_a_213_);
lean_dec(v_restrictedTypes_203_);
lean_dec_ref(v_config_202_);
lean_dec_ref(v_lratPath_201_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_226_, 0, v_a_213_);
lean_ctor_set(v___x_226_, 1, v_a_216_);
lean_ctor_set(v___x_226_, 2, v_a_219_);
lean_ctor_set(v___x_226_, 3, v_a_221_);
lean_ctor_set(v___x_226_, 4, v_lratPath_201_);
lean_ctor_set(v___x_226_, 5, v_config_202_);
lean_ctor_set(v___x_226_, 6, v_restrictedTypes_203_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_219_);
lean_dec(v_a_216_);
lean_dec(v_a_213_);
lean_dec(v_restrictedTypes_203_);
lean_dec_ref(v_config_202_);
lean_dec_ref(v_lratPath_201_);
v_a_253_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_220_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_220_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_a_216_);
lean_dec(v_a_213_);
lean_dec(v_restrictedTypes_203_);
lean_dec_ref(v_config_202_);
lean_dec_ref(v_lratPath_201_);
v_a_261_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_218_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_218_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_213_);
lean_dec(v_restrictedTypes_203_);
lean_dec_ref(v_config_202_);
lean_dec_ref(v_lratPath_201_);
v_a_269_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_215_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_215_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_restrictedTypes_203_);
lean_dec_ref(v_config_202_);
lean_dec_ref(v_lratPath_201_);
v_a_277_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_212_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_212_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new___boxed(lean_object* v_lratPath_285_, lean_object* v_config_286_, lean_object* v_restrictedTypes_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratPath_285_, v_config_286_, v_restrictedTypes_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(lean_object* v_cls_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___redArg(v_cls_296_, v_msg_297_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0___boxed(lean_object* v_cls_306_, lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_TacticContext_new_spec__0(v_cls_306_, v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_315_;
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
