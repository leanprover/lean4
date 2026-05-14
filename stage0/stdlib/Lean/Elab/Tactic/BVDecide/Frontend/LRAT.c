// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.LRAT
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Attr public import Lean.Elab.Tactic.BVDecide.LRAT.Trim public import Lean.Elab.Tactic.BVDecide.External public import Std.Tactic.BVDecide.LRAT.Checker
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprNat;
lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprInt;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_app_path();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "cadical"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_expr_def"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 227, 101, 23, 202, 228, 100, 227)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_cert_def"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__2_value),LEAN_SCALAR_PTR_LITERAL(231, 231, 4, 246, 116, 103, 142, 158)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "_reflection_def"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__4_value),LEAN_SCALAR_PTR_LITERAL(42, 138, 185, 107, 82, 210, 255, 77)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__6_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__8_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Using SAT solver at '"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LRAT"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Action"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "addEmpty"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(104, 109, 74, 91, 62, 109, 218, 23)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addRup"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(165, 250, 224, 102, 206, 35, 100, 254)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addRat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__37 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__37_value),LEAN_SCALAR_PTR_LITERAL(126, 188, 16, 206, 14, 241, 53, 87)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__43 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__43_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__44 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__43_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__44_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__43_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__53 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__53_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__56 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__40_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__56_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "del"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__59 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(252, 170, 87, 126, 210, 40, 34, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__59_value),LEAN_SCALAR_PTR_LITERAL(104, 230, 17, 1, 168, 25, 208, 83)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntAction"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 190, 57, 97, 43, 82, 204, 195)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 57, 146, 191, 99, 77, 0, 56)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Trimming LRAT proof"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Parsing LRAT file"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LRAT proof has "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " steps after trimming"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " steps before trimming"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "SAT solver produced invalid LRAT: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Running SAT solver"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Obtaining LRAT certificate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Serializing SAT problem to DIMACS file"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_7_) == 0)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc_ref(v_v_8_);
lean_dec_ref(v_val_7_);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1(lean_object* v_msg_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_13_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__3));
v___x_21_ = lean_unsigned_to_nat(14u);
v___x_22_ = lean_unsigned_to_nat(22u);
v___x_23_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__2));
v___x_24_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__1));
v___x_25_ = l_mkPanicMessageWithDecl(v___x_24_, v___x_23_, v___x_22_, v___x_21_, v___x_20_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(lean_object* v_a_26_){
_start:
{
lean_object* v_options_28_; lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_options_28_ = lean_ctor_get(v_a_26_, 2);
v_ref_29_ = lean_ctor_get(v_a_26_, 5);
v___x_30_ = l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
v___x_31_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__0(v_options_28_, v___x_30_);
v___x_32_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_33_ = lean_string_dec_eq(v___x_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_31_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec_ref(v___x_31_);
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
v___x_54_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__4);
v___x_55_ = l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1(v___x_54_);
v___y_41_ = v___x_55_;
goto v___jp_40_;
}
else
{
lean_object* v_val_56_; 
v_val_56_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_val_56_);
lean_dec_ref(v___x_53_);
v___y_41_ = v_val_56_;
goto v___jp_40_;
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___closed__0));
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
lean_inc(v_ref_29_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_ref_29_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg___boxed(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(v_a_70_);
lean_dec_ref(v_a_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(v_a_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___boxed(lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver(v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0(lean_object* v_msgData_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_env_88_; lean_object* v___x_89_; lean_object* v_mctx_90_; lean_object* v_lctx_91_; lean_object* v_options_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_87_ = lean_st_ref_get(v___y_85_);
v_env_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_env_88_);
lean_dec(v___x_87_);
v___x_89_ = lean_st_ref_get(v___y_83_);
v_mctx_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_mctx_90_);
lean_dec(v___x_89_);
v_lctx_91_ = lean_ctor_get(v___y_82_, 2);
v_options_92_ = lean_ctor_get(v___y_84_, 2);
lean_inc_ref(v_options_92_);
lean_inc_ref(v_lctx_91_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_env_88_);
lean_ctor_set(v___x_93_, 1, v_mctx_90_);
lean_ctor_set(v___x_93_, 2, v_lctx_91_);
lean_ctor_set(v___x_93_, 3, v_options_92_);
v___x_94_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v_msgData_81_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0___boxed(lean_object* v_msgData_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0(v_msgData_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_102_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_103_; double v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_float_of_nat(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(lean_object* v_cls_107_, lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_161_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_161_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_161_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_161_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v_traceState_121_; lean_object* v_env_122_; lean_object* v_nextMacroScope_123_; lean_object* v_ngen_124_; lean_object* v_auxDeclNGen_125_; lean_object* v_cache_126_; lean_object* v_messages_127_; lean_object* v_infoState_128_; lean_object* v_snapshotTasks_129_; lean_object* v_newDecls_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_160_; 
v___x_120_ = lean_st_ref_take(v___y_112_);
v_traceState_121_ = lean_ctor_get(v___x_120_, 4);
v_env_122_ = lean_ctor_get(v___x_120_, 0);
v_nextMacroScope_123_ = lean_ctor_get(v___x_120_, 1);
v_ngen_124_ = lean_ctor_get(v___x_120_, 2);
v_auxDeclNGen_125_ = lean_ctor_get(v___x_120_, 3);
v_cache_126_ = lean_ctor_get(v___x_120_, 5);
v_messages_127_ = lean_ctor_get(v___x_120_, 6);
v_infoState_128_ = lean_ctor_get(v___x_120_, 7);
v_snapshotTasks_129_ = lean_ctor_get(v___x_120_, 8);
v_newDecls_130_ = lean_ctor_get(v___x_120_, 9);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_160_ == 0)
{
v___x_132_ = v___x_120_;
v_isShared_133_ = v_isSharedCheck_160_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_newDecls_130_);
lean_inc(v_snapshotTasks_129_);
lean_inc(v_infoState_128_);
lean_inc(v_messages_127_);
lean_inc(v_cache_126_);
lean_inc(v_traceState_121_);
lean_inc(v_auxDeclNGen_125_);
lean_inc(v_ngen_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_env_122_);
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_160_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint64_t v_tid_134_; lean_object* v_traces_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_159_; 
v_tid_134_ = lean_ctor_get_uint64(v_traceState_121_, sizeof(void*)*1);
v_traces_135_ = lean_ctor_get(v_traceState_121_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_traceState_121_);
if (v_isSharedCheck_159_ == 0)
{
v___x_137_ = v_traceState_121_;
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_traces_135_);
lean_dec(v_traceState_121_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; double v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_139_ = lean_box(0);
v___x_140_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
v___x_141_ = 0;
v___x_142_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_143_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_143_, 0, v_cls_107_);
lean_ctor_set(v___x_143_, 1, v___x_139_);
lean_ctor_set(v___x_143_, 2, v___x_142_);
lean_ctor_set_float(v___x_143_, sizeof(void*)*3, v___x_140_);
lean_ctor_set_float(v___x_143_, sizeof(void*)*3 + 8, v___x_140_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*3 + 16, v___x_141_);
v___x_144_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_145_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v_a_116_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_inc(v_ref_114_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_ref_114_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_Lean_PersistentArray_push___redArg(v_traces_135_, v___x_146_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_147_);
v___x_149_ = v___x_137_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_147_);
lean_ctor_set_uint64(v_reuseFailAlloc_158_, sizeof(void*)*1, v_tid_134_);
v___x_149_ = v_reuseFailAlloc_158_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_149_);
v___x_151_ = v___x_132_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_env_122_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_ngen_124_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_auxDeclNGen_125_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_157_, 5, v_cache_126_);
lean_ctor_set(v_reuseFailAlloc_157_, 6, v_messages_127_);
lean_ctor_set(v_reuseFailAlloc_157_, 7, v_infoState_128_);
lean_ctor_set(v_reuseFailAlloc_157_, 8, v_snapshotTasks_129_);
lean_ctor_set(v_reuseFailAlloc_157_, 9, v_newDecls_130_);
v___x_151_ = v_reuseFailAlloc_157_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = lean_st_ref_set(v___y_112_, v___x_151_);
v___x_153_ = lean_box(0);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_153_);
v___x_155_ = v___x_118_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___boxed(lean_object* v_cls_162_, lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_162_, v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_190_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11));
v___x_191_ = l_Lean_Name_append(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__15));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object* v_lratPath_198_, lean_object* v_config_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1));
v___x_208_ = l_Lean_Elab_Term_mkAuxName(v___x_207_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3));
v___x_211_ = l_Lean_Elab_Term_mkAuxName(v___x_210_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5));
v___x_214_ = l_Lean_Elab_Term_mkAuxName(v___x_213_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_214_);
v___x_216_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(v_a_204_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_247_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_247_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_options_226_; uint8_t v_hasTrace_227_; 
v_options_226_ = lean_ctor_get(v_a_204_, 2);
v_hasTrace_227_ = lean_ctor_get_uint8(v_options_226_, sizeof(void*)*1);
if (v_hasTrace_227_ == 0)
{
goto v___jp_221_;
}
else
{
lean_object* v_inheritedTraceOptions_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_inheritedTraceOptions_228_ = lean_ctor_get(v_a_204_, 13);
v___x_229_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_230_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_228_, v_options_226_, v___x_230_);
if (v___x_231_ == 0)
{
goto v___jp_221_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_232_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14);
lean_inc(v_a_217_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v_a_217_);
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v___x_229_, v___x_237_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_dec_ref(v___x_238_);
goto v___jp_221_;
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_del_object(v___x_219_);
lean_dec(v_a_217_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
lean_dec(v_a_209_);
lean_dec_ref(v_config_199_);
lean_dec_ref(v_lratPath_198_);
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_222_, 0, v_a_209_);
lean_ctor_set(v___x_222_, 1, v_a_212_);
lean_ctor_set(v___x_222_, 2, v_a_215_);
lean_ctor_set(v___x_222_, 3, v_a_217_);
lean_ctor_set(v___x_222_, 4, v_lratPath_198_);
lean_ctor_set(v___x_222_, 5, v_config_199_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_215_);
lean_dec(v_a_212_);
lean_dec(v_a_209_);
lean_dec_ref(v_config_199_);
lean_dec_ref(v_lratPath_198_);
v_a_248_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_216_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_216_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_212_);
lean_dec(v_a_209_);
lean_dec_ref(v_config_199_);
lean_dec_ref(v_lratPath_198_);
v_a_256_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_214_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_214_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_209_);
lean_dec_ref(v_config_199_);
lean_dec_ref(v_lratPath_198_);
v_a_264_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_211_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_211_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v_config_199_);
lean_dec_ref(v_lratPath_198_);
v_a_272_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_208_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_208_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object* v_lratPath_280_, lean_object* v_config_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(v_lratPath_280_, v_config_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(lean_object* v_cls_290_, lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_290_, v_msg_291_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___boxed(lean_object* v_cls_300_, lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(v_cls_300_, v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_309_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_317_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1));
v___x_318_ = l_Lean_mkConst(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
v___x_323_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v___x_324_ = l_Lean_mkConst(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_beta_327_; 
v___x_325_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_beta_327_ = l_Lean_Expr_app___override(v___x_326_, v___x_325_);
return v_beta_327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_alpha_333_; 
v___x_331_ = lean_box(0);
v___x_332_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9));
v_alpha_333_ = l_Lean_mkConst(v___x_332_, v___x_331_);
return v_alpha_333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_350_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16));
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21));
v___x_359_ = l_Lean_mkConst(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_365_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24));
v___x_366_ = l_Lean_mkConst(v___x_365_, v___x_364_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26(void){
_start:
{
lean_object* v_alpha_367_; lean_object* v___x_368_; lean_object* v_nil_369_; 
v_alpha_367_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_368_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_369_ = l_Lean_Expr_app___override(v___x_368_, v_alpha_367_);
return v_nil_369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_375_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28));
v___x_376_ = l_Lean_mkConst(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30(void){
_start:
{
lean_object* v_alpha_377_; lean_object* v___x_378_; lean_object* v_cons_379_; 
v_alpha_377_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_379_ = l_Lean_Expr_app___override(v___x_378_, v_alpha_377_);
return v_cons_379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_389_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32));
v___x_390_ = l_Lean_mkConst(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_type_393_; 
v___x_391_ = lean_box(0);
v___x_392_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v_type_393_ = l_Lean_Expr_const___override(v___x_392_, v___x_391_);
return v_type_393_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35(void){
_start:
{
lean_object* v_type_394_; lean_object* v___x_395_; lean_object* v_nil_396_; 
v_type_394_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_395_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_396_ = l_Lean_Expr_app___override(v___x_395_, v_type_394_);
return v_nil_396_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36(void){
_start:
{
lean_object* v_type_397_; lean_object* v___x_398_; lean_object* v_cons_399_; 
v_type_397_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_398_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_399_ = l_Lean_Expr_app___override(v___x_398_, v_type_397_);
return v_cons_399_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_409_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38));
v___x_410_ = l_Lean_mkConst(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_00_u03b2Type_416_; 
v___x_414_ = lean_box(0);
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41));
v_00_u03b2Type_416_ = l_Lean_mkConst(v___x_415_, v___x_414_);
return v_00_u03b2Type_416_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45));
v___x_424_ = l_Lean_mkConst(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47(void){
_start:
{
lean_object* v_alpha_425_; lean_object* v___x_426_; lean_object* v_00_u03b2Type_427_; 
v_alpha_425_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_426_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_00_u03b2Type_427_ = l_Lean_Expr_app___override(v___x_426_, v_alpha_425_);
return v_00_u03b2Type_427_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_431_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48));
v___x_432_ = l_Lean_mkConst(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50(void){
_start:
{
lean_object* v_00_u03b2Type_433_; lean_object* v_alpha_434_; lean_object* v___x_435_; lean_object* v_type_436_; 
v_00_u03b2Type_433_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47);
v_alpha_434_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_435_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49);
v_type_436_ = l_Lean_mkAppB(v___x_435_, v_alpha_434_, v_00_u03b2Type_433_);
return v_type_436_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51(void){
_start:
{
lean_object* v_type_437_; lean_object* v___x_438_; lean_object* v_nil_439_; 
v_type_437_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_438_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_439_ = l_Lean_Expr_app___override(v___x_438_, v_type_437_);
return v_nil_439_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52(void){
_start:
{
lean_object* v_type_440_; lean_object* v___x_441_; lean_object* v_cons_442_; 
v_type_440_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_441_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_442_ = l_Lean_Expr_app___override(v___x_441_, v_type_440_);
return v_cons_442_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54));
v___x_449_ = l_Lean_mkConst(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57));
v___x_456_ = l_Lean_mkConst(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_action_471_){
_start:
{
lean_object* v_beta_472_; lean_object* v_alpha_473_; 
v_beta_472_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7);
v_alpha_473_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
switch(lean_obj_tag(v_action_471_))
{
case 0:
{
lean_object* v_id_474_; lean_object* v_rupHints_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_nil_479_; lean_object* v_cons_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
v_id_474_ = lean_ctor_get(v_action_471_, 0);
lean_inc(v_id_474_);
v_rupHints_475_ = lean_ctor_get(v_action_471_, 1);
lean_inc_ref(v_rupHints_475_);
lean_dec_ref(v_action_471_);
v___x_476_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18);
v___x_477_ = l_Lean_mkNatLit(v_id_474_);
v___x_478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_479_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_480_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_481_ = lean_array_to_list(v_rupHints_475_);
v___x_482_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_479_, v_cons_480_, v___x_481_);
v___x_483_ = l_Lean_mkAppB(v___x_478_, v_alpha_473_, v___x_482_);
v___x_484_ = l_Lean_mkApp4(v___x_476_, v_beta_472_, v_alpha_473_, v___x_477_, v___x_483_);
return v___x_484_;
}
case 1:
{
lean_object* v_id_485_; lean_object* v_c_486_; lean_object* v_rupHints_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_type_490_; lean_object* v___x_491_; lean_object* v_nil_492_; lean_object* v_cons_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_nil_497_; lean_object* v_cons_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v___x_470_);
v_id_485_ = lean_ctor_get(v_action_471_, 0);
lean_inc(v_id_485_);
v_c_486_ = lean_ctor_get(v_action_471_, 1);
lean_inc(v_c_486_);
v_rupHints_487_ = lean_ctor_get(v_action_471_, 2);
lean_inc_ref(v_rupHints_487_);
lean_dec_ref(v_action_471_);
v___x_488_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33);
v___x_489_ = l_Lean_mkNatLit(v_id_485_);
v_type_490_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_491_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_492_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_493_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_494_ = lean_array_to_list(v_c_486_);
v___x_495_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_469_, v_nil_492_, v_cons_493_, v___x_494_);
v___x_496_ = l_Lean_mkAppB(v___x_491_, v_type_490_, v___x_495_);
v_nil_497_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_498_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_499_ = lean_array_to_list(v_rupHints_487_);
v___x_500_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_497_, v_cons_498_, v___x_499_);
v___x_501_ = l_Lean_mkAppB(v___x_491_, v_alpha_473_, v___x_500_);
v___x_502_ = l_Lean_mkApp5(v___x_488_, v_beta_472_, v_alpha_473_, v___x_489_, v___x_496_, v___x_501_);
return v___x_502_;
}
case 2:
{
lean_object* v_id_503_; lean_object* v_c_504_; lean_object* v_pivot_505_; lean_object* v_rupHints_506_; lean_object* v_ratHints_507_; lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v_type_511_; lean_object* v_nil_512_; lean_object* v_cons_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_00_u03b2Type_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___y_523_; uint8_t v___x_537_; 
v_id_503_ = lean_ctor_get(v_action_471_, 0);
lean_inc(v_id_503_);
v_c_504_ = lean_ctor_get(v_action_471_, 1);
lean_inc(v_c_504_);
v_pivot_505_ = lean_ctor_get(v_action_471_, 2);
lean_inc_ref(v_pivot_505_);
v_rupHints_506_ = lean_ctor_get(v_action_471_, 3);
lean_inc_ref(v_rupHints_506_);
v_ratHints_507_ = lean_ctor_get(v_action_471_, 4);
lean_inc_ref(v_ratHints_507_);
lean_dec_ref(v_action_471_);
v___x_508_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_fst_509_ = lean_ctor_get(v_pivot_505_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v_pivot_505_, 1);
lean_inc(v_snd_510_);
lean_dec_ref(v_pivot_505_);
v_type_511_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v_nil_512_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_513_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_514_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39);
v___x_515_ = l_Lean_mkNatLit(v_id_503_);
v___x_516_ = lean_array_to_list(v_c_504_);
v___x_517_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_469_, v_nil_512_, v_cons_513_, v___x_516_);
v___x_518_ = l_Lean_mkAppB(v___x_508_, v_type_511_, v___x_517_);
v_00_u03b2Type_519_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42);
v___x_520_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46);
v___x_521_ = l_Lean_mkNatLit(v_fst_509_);
v___x_537_ = lean_unbox(v_snd_510_);
lean_dec(v_snd_510_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55);
v___y_523_ = v___x_538_;
goto v___jp_522_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58);
v___y_523_ = v___x_539_;
goto v___jp_522_;
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v_nil_525_; lean_object* v_cons_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_type_530_; lean_object* v_nil_531_; lean_object* v_cons_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_inc_ref(v___y_523_);
v___x_524_ = l_Lean_mkApp4(v___x_520_, v_alpha_473_, v_00_u03b2Type_519_, v___x_521_, v___y_523_);
v_nil_525_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_526_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_527_ = lean_array_to_list(v_rupHints_506_);
v___x_528_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_525_, v_cons_526_, v___x_527_);
v___x_529_ = l_Lean_mkAppB(v___x_508_, v_alpha_473_, v___x_528_);
v_type_530_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v_nil_531_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51);
v_cons_532_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52);
v___x_533_ = lean_array_to_list(v_ratHints_507_);
v___x_534_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_470_, v_nil_531_, v_cons_532_, v___x_533_);
v___x_535_ = l_Lean_mkAppB(v___x_508_, v_type_530_, v___x_534_);
v___x_536_ = l_Lean_mkApp7(v___x_514_, v_beta_472_, v_alpha_473_, v___x_515_, v___x_518_, v___x_524_, v___x_529_, v___x_535_);
return v___x_536_;
}
}
default: 
{
lean_object* v_ids_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_nil_543_; lean_object* v_cons_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
v_ids_540_ = lean_ctor_get(v_action_471_, 0);
lean_inc_ref(v_ids_540_);
lean_dec_ref(v_action_471_);
v___x_541_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61);
v___x_542_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_543_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_544_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_545_ = lean_array_to_list(v_ids_540_);
v___x_546_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_543_, v_cons_544_, v___x_545_);
v___x_547_ = l_Lean_mkAppB(v___x_542_, v_alpha_473_, v___x_546_);
v___x_548_ = l_Lean_mkApp3(v___x_541_, v_beta_472_, v_alpha_473_, v___x_547_);
return v___x_548_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_instToExprNat;
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_instToExprArrayOfToLevel___redArg(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0);
v___x_553_ = l_Lean_instToExprNat;
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_instToExprProdOfToLevel___redArg(v___x_554_, v___x_554_, v___x_553_, v___x_552_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___f_559_; 
v___x_556_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1);
v___x_557_ = l_Lean_instToExprInt;
v___x_558_ = l_Lean_instToExprNat;
v___f_559_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0), 4, 3);
lean_closure_set(v___f_559_, 0, v___x_558_);
lean_closure_set(v___f_559_, 1, v___x_557_);
lean_closure_set(v___f_559_, 2, v___x_556_);
return v___f_559_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_box(0);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4));
v___x_569_ = l_Lean_mkConst(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6(void){
_start:
{
lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5);
v___f_571_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___f_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction(void){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(32u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_577_ = ((size_t)5ULL);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_unsigned_to_nat(32u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0);
v___x_582_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
lean_ctor_set(v___x_582_, 2, v___x_578_);
lean_ctor_set(v___x_582_, 3, v___x_578_);
lean_ctor_set_usize(v___x_582_, 4, v___x_577_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_traceState_586_; lean_object* v_traces_587_; lean_object* v___x_588_; lean_object* v_traceState_589_; lean_object* v_env_590_; lean_object* v_nextMacroScope_591_; lean_object* v_ngen_592_; lean_object* v_auxDeclNGen_593_; lean_object* v_cache_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v_newDecls_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_617_; 
v___x_585_ = lean_st_ref_get(v___y_583_);
v_traceState_586_ = lean_ctor_get(v___x_585_, 4);
lean_inc_ref(v_traceState_586_);
lean_dec(v___x_585_);
v_traces_587_ = lean_ctor_get(v_traceState_586_, 0);
lean_inc_ref(v_traces_587_);
lean_dec_ref(v_traceState_586_);
v___x_588_ = lean_st_ref_take(v___y_583_);
v_traceState_589_ = lean_ctor_get(v___x_588_, 4);
v_env_590_ = lean_ctor_get(v___x_588_, 0);
v_nextMacroScope_591_ = lean_ctor_get(v___x_588_, 1);
v_ngen_592_ = lean_ctor_get(v___x_588_, 2);
v_auxDeclNGen_593_ = lean_ctor_get(v___x_588_, 3);
v_cache_594_ = lean_ctor_get(v___x_588_, 5);
v_messages_595_ = lean_ctor_get(v___x_588_, 6);
v_infoState_596_ = lean_ctor_get(v___x_588_, 7);
v_snapshotTasks_597_ = lean_ctor_get(v___x_588_, 8);
v_newDecls_598_ = lean_ctor_get(v___x_588_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_617_ == 0)
{
v___x_600_ = v___x_588_;
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_newDecls_598_);
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_cache_594_);
lean_inc(v_traceState_589_);
lean_inc(v_auxDeclNGen_593_);
lean_inc(v_ngen_592_);
lean_inc(v_nextMacroScope_591_);
lean_inc(v_env_590_);
lean_dec(v___x_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint64_t v_tid_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_615_; 
v_tid_602_ = lean_ctor_get_uint64(v_traceState_589_, sizeof(void*)*1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_traceState_589_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_traceState_589_, 0);
lean_dec(v_unused_616_);
v___x_604_ = v_traceState_589_;
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_traceState_589_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_606_);
lean_ctor_set_uint64(v_reuseFailAlloc_614_, sizeof(void*)*1, v_tid_602_);
v___x_608_ = v_reuseFailAlloc_614_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v___x_608_);
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_env_590_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_591_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_cache_594_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v_snapshotTasks_597_);
lean_ctor_set(v_reuseFailAlloc_613_, 9, v_newDecls_598_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_set(v___y_583_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_traces_587_);
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___boxed(lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_618_);
lean_dec(v___y_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_628_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(lean_object* v_opts_629_, lean_object* v_opt_630_){
_start:
{
lean_object* v_name_631_; lean_object* v_defValue_632_; lean_object* v_map_633_; lean_object* v___x_634_; 
v_name_631_ = lean_ctor_get(v_opt_630_, 0);
v_defValue_632_ = lean_ctor_get(v_opt_630_, 1);
v_map_633_ = lean_ctor_get(v_opts_629_, 0);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_633_, v_name_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
uint8_t v___x_635_; 
v___x_635_ = lean_unbox(v_defValue_632_);
return v___x_635_;
}
else
{
lean_object* v_val_636_; 
v_val_636_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_636_);
lean_dec_ref(v___x_634_);
if (lean_obj_tag(v_val_636_) == 1)
{
uint8_t v_v_637_; 
v_v_637_ = lean_ctor_get_uint8(v_val_636_, 0);
lean_dec_ref(v_val_636_);
return v_v_637_;
}
else
{
uint8_t v___x_638_; 
lean_dec(v_val_636_);
v___x_638_ = lean_unbox(v_defValue_632_);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___boxed(lean_object* v_opts_639_, lean_object* v_opt_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_639_, v_opt_640_);
lean_dec_ref(v_opt_640_);
lean_dec_ref(v_opts_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(lean_object* v_e_643_){
_start:
{
if (lean_obj_tag(v_e_643_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_a_645_ = lean_ctor_get(v_e_643_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_e_643_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v_e_643_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v_e_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_mk_io_user_error(v_a_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 1);
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_a_654_ = lean_ctor_get(v_e_643_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_e_643_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v_e_643_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v_e_643_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 0);
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg___boxed(lean_object* v_e_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_e_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(lean_object* v_00_u03b1_665_, lean_object* v_e_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_e_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___boxed(lean_object* v_00_u03b1_669_, lean_object* v_e_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_00_u03b1_669_, v_e_670_);
return v_res_672_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1));
v___x_677_ = l_Lean_MessageData_ofFormat(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(v_x_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_x_684_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object* v_a_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object* v_a_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_a_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(v_a_695_, v_x_696_);
lean_dec_ref(v_a_695_);
return v_res_697_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1));
v___x_702_ = l_Lean_MessageData_ofFormat(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(v_x_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_x_709_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_714_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
lean_ctor_set(v___x_719_, 3, v___x_718_);
lean_ctor_set(v___x_719_, 4, v___x_717_);
lean_ctor_set(v___x_719_, 5, v___x_717_);
lean_ctor_set(v___x_719_, 6, v___x_717_);
lean_ctor_set(v___x_719_, 7, v___x_717_);
lean_ctor_set(v___x_719_, 8, v___x_717_);
lean_ctor_set(v___x_719_, 9, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_unsigned_to_nat(32u);
v___x_721_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((size_t)5ULL);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_unsigned_to_nat(32u);
v___x_726_ = lean_mk_empty_array_with_capacity(v___x_725_);
v___x_727_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3);
v___x_728_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_724_);
lean_ctor_set(v___x_728_, 3, v___x_724_);
lean_ctor_set_usize(v___x_728_, 4, v___x_723_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_box(1);
v___x_730_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4);
v___x_731_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1);
v___x_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v_env_738_; lean_object* v_options_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_737_ = lean_st_ref_get(v___y_735_);
v_env_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc_ref(v_env_738_);
lean_dec(v___x_737_);
v_options_739_ = lean_ctor_get(v___y_734_, 2);
v___x_740_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2);
v___x_741_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_739_);
v___x_742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_742_, 0, v_env_738_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
lean_ctor_set(v___x_742_, 3, v_options_739_);
v___x_743_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_msgData_733_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msgData_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(size_t v_sz_750_, size_t v_i_751_, lean_object* v_bs_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_lt(v_i_751_, v_sz_750_);
if (v___x_753_ == 0)
{
return v_bs_752_;
}
else
{
lean_object* v_v_754_; lean_object* v_msg_755_; lean_object* v___x_756_; lean_object* v_bs_x27_757_; size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v_v_754_ = lean_array_uget_borrowed(v_bs_752_, v_i_751_);
v_msg_755_ = lean_ctor_get(v_v_754_, 1);
lean_inc_ref(v_msg_755_);
v___x_756_ = lean_unsigned_to_nat(0u);
v_bs_x27_757_ = lean_array_uset(v_bs_752_, v_i_751_, v___x_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_751_, v___x_758_);
v___x_760_ = lean_array_uset(v_bs_x27_757_, v_i_751_, v_msg_755_);
v_i_751_ = v___x_759_;
v_bs_752_ = v___x_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7___boxed(lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_bs_764_){
_start:
{
size_t v_sz_boxed_765_; size_t v_i_boxed_766_; lean_object* v_res_767_; 
v_sz_boxed_765_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_766_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(v_sz_boxed_765_, v_i_boxed_766_, v_bs_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(lean_object* v_oldTraces_768_, lean_object* v_data_769_, lean_object* v_ref_770_, lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_fileName_775_; lean_object* v_fileMap_776_; lean_object* v_options_777_; lean_object* v_currRecDepth_778_; lean_object* v_maxRecDepth_779_; lean_object* v_ref_780_; lean_object* v_currNamespace_781_; lean_object* v_openDecls_782_; lean_object* v_initHeartbeats_783_; lean_object* v_maxHeartbeats_784_; lean_object* v_quotContext_785_; lean_object* v_currMacroScope_786_; uint8_t v_diag_787_; lean_object* v_cancelTk_x3f_788_; uint8_t v_suppressElabErrors_789_; lean_object* v_inheritedTraceOptions_790_; lean_object* v___x_791_; lean_object* v_traceState_792_; lean_object* v_traces_793_; lean_object* v_ref_794_; lean_object* v___x_795_; lean_object* v___x_796_; size_t v_sz_797_; size_t v___x_798_; lean_object* v___x_799_; lean_object* v_msg_800_; lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_840_; 
v_fileName_775_ = lean_ctor_get(v___y_772_, 0);
v_fileMap_776_ = lean_ctor_get(v___y_772_, 1);
v_options_777_ = lean_ctor_get(v___y_772_, 2);
v_currRecDepth_778_ = lean_ctor_get(v___y_772_, 3);
v_maxRecDepth_779_ = lean_ctor_get(v___y_772_, 4);
v_ref_780_ = lean_ctor_get(v___y_772_, 5);
v_currNamespace_781_ = lean_ctor_get(v___y_772_, 6);
v_openDecls_782_ = lean_ctor_get(v___y_772_, 7);
v_initHeartbeats_783_ = lean_ctor_get(v___y_772_, 8);
v_maxHeartbeats_784_ = lean_ctor_get(v___y_772_, 9);
v_quotContext_785_ = lean_ctor_get(v___y_772_, 10);
v_currMacroScope_786_ = lean_ctor_get(v___y_772_, 11);
v_diag_787_ = lean_ctor_get_uint8(v___y_772_, sizeof(void*)*14);
v_cancelTk_x3f_788_ = lean_ctor_get(v___y_772_, 12);
v_suppressElabErrors_789_ = lean_ctor_get_uint8(v___y_772_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_790_ = lean_ctor_get(v___y_772_, 13);
v___x_791_ = lean_st_ref_get(v___y_773_);
v_traceState_792_ = lean_ctor_get(v___x_791_, 4);
lean_inc_ref(v_traceState_792_);
lean_dec(v___x_791_);
v_traces_793_ = lean_ctor_get(v_traceState_792_, 0);
lean_inc_ref(v_traces_793_);
lean_dec_ref(v_traceState_792_);
v_ref_794_ = l_Lean_replaceRef(v_ref_770_, v_ref_780_);
lean_inc_ref(v_inheritedTraceOptions_790_);
lean_inc(v_cancelTk_x3f_788_);
lean_inc(v_currMacroScope_786_);
lean_inc(v_quotContext_785_);
lean_inc(v_maxHeartbeats_784_);
lean_inc(v_initHeartbeats_783_);
lean_inc(v_openDecls_782_);
lean_inc(v_currNamespace_781_);
lean_inc(v_maxRecDepth_779_);
lean_inc(v_currRecDepth_778_);
lean_inc_ref(v_options_777_);
lean_inc_ref(v_fileMap_776_);
lean_inc_ref(v_fileName_775_);
v___x_795_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_795_, 0, v_fileName_775_);
lean_ctor_set(v___x_795_, 1, v_fileMap_776_);
lean_ctor_set(v___x_795_, 2, v_options_777_);
lean_ctor_set(v___x_795_, 3, v_currRecDepth_778_);
lean_ctor_set(v___x_795_, 4, v_maxRecDepth_779_);
lean_ctor_set(v___x_795_, 5, v_ref_794_);
lean_ctor_set(v___x_795_, 6, v_currNamespace_781_);
lean_ctor_set(v___x_795_, 7, v_openDecls_782_);
lean_ctor_set(v___x_795_, 8, v_initHeartbeats_783_);
lean_ctor_set(v___x_795_, 9, v_maxHeartbeats_784_);
lean_ctor_set(v___x_795_, 10, v_quotContext_785_);
lean_ctor_set(v___x_795_, 11, v_currMacroScope_786_);
lean_ctor_set(v___x_795_, 12, v_cancelTk_x3f_788_);
lean_ctor_set(v___x_795_, 13, v_inheritedTraceOptions_790_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*14, v_diag_787_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*14 + 1, v_suppressElabErrors_789_);
v___x_796_ = l_Lean_PersistentArray_toArray___redArg(v_traces_793_);
lean_dec_ref(v_traces_793_);
v_sz_797_ = lean_array_size(v___x_796_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(v_sz_797_, v___x_798_, v___x_796_);
v_msg_800_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_800_, 0, v_data_769_);
lean_ctor_set(v_msg_800_, 1, v_msg_771_);
lean_ctor_set(v_msg_800_, 2, v___x_799_);
v___x_801_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_800_, v___x_795_, v___y_773_);
lean_dec_ref(v___x_795_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_840_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_840_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_840_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v_traceState_807_; lean_object* v_env_808_; lean_object* v_nextMacroScope_809_; lean_object* v_ngen_810_; lean_object* v_auxDeclNGen_811_; lean_object* v_cache_812_; lean_object* v_messages_813_; lean_object* v_infoState_814_; lean_object* v_snapshotTasks_815_; lean_object* v_newDecls_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_839_; 
v___x_806_ = lean_st_ref_take(v___y_773_);
v_traceState_807_ = lean_ctor_get(v___x_806_, 4);
v_env_808_ = lean_ctor_get(v___x_806_, 0);
v_nextMacroScope_809_ = lean_ctor_get(v___x_806_, 1);
v_ngen_810_ = lean_ctor_get(v___x_806_, 2);
v_auxDeclNGen_811_ = lean_ctor_get(v___x_806_, 3);
v_cache_812_ = lean_ctor_get(v___x_806_, 5);
v_messages_813_ = lean_ctor_get(v___x_806_, 6);
v_infoState_814_ = lean_ctor_get(v___x_806_, 7);
v_snapshotTasks_815_ = lean_ctor_get(v___x_806_, 8);
v_newDecls_816_ = lean_ctor_get(v___x_806_, 9);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_839_ == 0)
{
v___x_818_ = v___x_806_;
v_isShared_819_ = v_isSharedCheck_839_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_newDecls_816_);
lean_inc(v_snapshotTasks_815_);
lean_inc(v_infoState_814_);
lean_inc(v_messages_813_);
lean_inc(v_cache_812_);
lean_inc(v_traceState_807_);
lean_inc(v_auxDeclNGen_811_);
lean_inc(v_ngen_810_);
lean_inc(v_nextMacroScope_809_);
lean_inc(v_env_808_);
lean_dec(v___x_806_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_839_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint64_t v_tid_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_837_; 
v_tid_820_ = lean_ctor_get_uint64(v_traceState_807_, sizeof(void*)*1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_traceState_807_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; 
v_unused_838_ = lean_ctor_get(v_traceState_807_, 0);
lean_dec(v_unused_838_);
v___x_822_ = v_traceState_807_;
v_isShared_823_ = v_isSharedCheck_837_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_traceState_807_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_837_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_ref_770_);
lean_ctor_set(v___x_824_, 1, v_a_802_);
v___x_825_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_768_, v___x_824_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_825_);
lean_ctor_set_uint64(v_reuseFailAlloc_836_, sizeof(void*)*1, v_tid_820_);
v___x_827_ = v_reuseFailAlloc_836_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 4, v___x_827_);
v___x_829_ = v___x_818_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_env_808_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_nextMacroScope_809_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ngen_810_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_auxDeclNGen_811_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 5, v_cache_812_);
lean_ctor_set(v_reuseFailAlloc_835_, 6, v_messages_813_);
lean_ctor_set(v_reuseFailAlloc_835_, 7, v_infoState_814_);
lean_ctor_set(v_reuseFailAlloc_835_, 8, v_snapshotTasks_815_);
lean_ctor_set(v_reuseFailAlloc_835_, 9, v_newDecls_816_);
v___x_829_ = v_reuseFailAlloc_835_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_st_ref_set(v___y_773_, v___x_829_);
v___x_831_ = lean_box(0);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_831_);
v___x_833_ = v___x_804_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5___boxed(lean_object* v_oldTraces_841_, lean_object* v_data_842_, lean_object* v_ref_843_, lean_object* v_msg_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_841_, v_data_842_, v_ref_843_, v_msg_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_848_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(lean_object* v_e_849_){
_start:
{
if (lean_obj_tag(v_e_849_) == 0)
{
uint8_t v___x_850_; 
v___x_850_ = 2;
return v___x_850_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = 0;
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4___boxed(lean_object* v_e_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(v_e_852_);
lean_dec_ref(v_e_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(lean_object* v_opts_855_, lean_object* v_opt_856_){
_start:
{
lean_object* v_name_857_; lean_object* v_defValue_858_; lean_object* v_map_859_; lean_object* v___x_860_; 
v_name_857_ = lean_ctor_get(v_opt_856_, 0);
v_defValue_858_ = lean_ctor_get(v_opt_856_, 1);
v_map_859_ = lean_ctor_get(v_opts_855_, 0);
v___x_860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_859_, v_name_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_inc(v_defValue_858_);
return v_defValue_858_;
}
else
{
lean_object* v_val_861_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref(v___x_860_);
if (lean_obj_tag(v_val_861_) == 3)
{
lean_object* v_v_862_; 
v_v_862_ = lean_ctor_get(v_val_861_, 0);
lean_inc(v_v_862_);
lean_dec_ref(v_val_861_);
return v_v_862_;
}
else
{
lean_dec(v_val_861_);
lean_inc(v_defValue_858_);
return v_defValue_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_863_, lean_object* v_opt_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_863_, v_opt_864_);
lean_dec_ref(v_opt_864_);
lean_dec_ref(v_opts_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v_x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v_x_866_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v_x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 1);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v_x_866_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v_x_866_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v_x_866_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 0);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg___boxed(lean_object* v_x_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_x_884_);
return v_res_886_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__2));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4(void){
_start:
{
lean_object* v___x_893_; double v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1000u);
v___x_894_ = lean_float_of_nat(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(lean_object* v_cls_895_, uint8_t v_collapsed_896_, lean_object* v_tag_897_, lean_object* v_opts_898_, uint8_t v_clsEnabled_899_, lean_object* v_oldTraces_900_, lean_object* v_msg_901_, lean_object* v_resStartStop_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1006_; 
v_fst_906_ = lean_ctor_get(v_resStartStop_902_, 0);
v_snd_907_ = lean_ctor_get(v_resStartStop_902_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_resStartStop_902_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_909_ = v_resStartStop_902_;
v_isShared_910_ = v_isSharedCheck_1006_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec(v_resStartStop_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1006_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v_data_914_; lean_object* v_fst_925_; lean_object* v_snd_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_1005_; 
v_fst_925_ = lean_ctor_get(v_snd_907_, 0);
v_snd_926_ = lean_ctor_get(v_snd_907_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_snd_907_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_928_ = v_snd_907_;
v_isShared_929_ = v_isSharedCheck_1005_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snd_926_);
lean_inc(v_fst_925_);
lean_dec(v_snd_907_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_1005_;
goto v_resetjp_927_;
}
v___jp_911_:
{
lean_object* v___x_915_; 
lean_inc(v___y_913_);
v___x_915_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_900_, v_data_914_, v___y_913_, v___y_912_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; 
lean_dec_ref(v___x_915_);
v___x_916_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_906_);
return v___x_916_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_fst_906_);
v_a_917_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
v_resetjp_927_:
{
lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___y_933_; lean_object* v_a_934_; uint8_t v___y_958_; double v___y_990_; 
v___x_930_ = l_Lean_trace_profiler;
v___x_931_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_898_, v___x_930_);
if (v___x_931_ == 0)
{
v___y_958_ = v___x_931_;
goto v___jp_957_;
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = l_Lean_trace_profiler_useHeartbeats;
v___x_996_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_898_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; double v___x_999_; double v___x_1000_; double v___x_1001_; 
v___x_997_ = l_Lean_trace_profiler_threshold;
v___x_998_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_898_, v___x_997_);
v___x_999_ = lean_float_of_nat(v___x_998_);
v___x_1000_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_1001_ = lean_float_div(v___x_999_, v___x_1000_);
v___y_990_ = v___x_1001_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; double v___x_1004_; 
v___x_1002_ = l_Lean_trace_profiler_threshold;
v___x_1003_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_898_, v___x_1002_);
v___x_1004_ = lean_float_of_nat(v___x_1003_);
v___y_990_ = v___x_1004_;
goto v___jp_989_;
}
}
v___jp_932_:
{
uint8_t v_result_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_result_935_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(v_fst_906_);
v___x_936_ = l_Lean_TraceResult_toEmoji(v_result_935_);
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
v___x_938_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 7);
lean_ctor_set(v___x_928_, 1, v___x_938_);
lean_ctor_set(v___x_928_, 0, v___x_937_);
v___x_940_ = v___x_928_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_951_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v_m_942_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 7);
lean_ctor_set(v___x_909_, 1, v_a_934_);
lean_ctor_set(v___x_909_, 0, v___x_940_);
v_m_942_ = v___x_909_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_a_934_);
v_m_942_ = v_reuseFailAlloc_950_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; double v___x_945_; lean_object* v_data_946_; 
v___x_943_ = lean_box(v_result_935_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___x_945_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_897_);
lean_inc_ref(v___x_944_);
lean_inc(v_cls_895_);
v_data_946_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_946_, 0, v_cls_895_);
lean_ctor_set(v_data_946_, 1, v___x_944_);
lean_ctor_set(v_data_946_, 2, v_tag_897_);
lean_ctor_set_float(v_data_946_, sizeof(void*)*3, v___x_945_);
lean_ctor_set_float(v_data_946_, sizeof(void*)*3 + 8, v___x_945_);
lean_ctor_set_uint8(v_data_946_, sizeof(void*)*3 + 16, v_collapsed_896_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_944_);
lean_dec(v_snd_926_);
lean_dec(v_fst_925_);
lean_dec_ref(v_tag_897_);
lean_dec(v_cls_895_);
v___y_912_ = v_m_942_;
v___y_913_ = v___y_933_;
v_data_914_ = v_data_946_;
goto v___jp_911_;
}
else
{
lean_object* v_data_947_; double v___x_948_; double v___x_949_; 
lean_dec_ref(v_data_946_);
v_data_947_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_947_, 0, v_cls_895_);
lean_ctor_set(v_data_947_, 1, v___x_944_);
lean_ctor_set(v_data_947_, 2, v_tag_897_);
v___x_948_ = lean_unbox_float(v_fst_925_);
lean_dec(v_fst_925_);
lean_ctor_set_float(v_data_947_, sizeof(void*)*3, v___x_948_);
v___x_949_ = lean_unbox_float(v_snd_926_);
lean_dec(v_snd_926_);
lean_ctor_set_float(v_data_947_, sizeof(void*)*3 + 8, v___x_949_);
lean_ctor_set_uint8(v_data_947_, sizeof(void*)*3 + 16, v_collapsed_896_);
v___y_912_ = v_m_942_;
v___y_913_ = v___y_933_;
v_data_914_ = v_data_947_;
goto v___jp_911_;
}
}
}
}
v___jp_952_:
{
lean_object* v_ref_953_; lean_object* v___x_954_; 
v_ref_953_ = lean_ctor_get(v___y_903_, 5);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v_fst_906_);
v___x_954_ = lean_apply_4(v_msg_901_, v_fst_906_, v___y_903_, v___y_904_, lean_box(0));
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref(v___x_954_);
v___y_933_ = v_ref_953_;
v_a_934_ = v_a_955_;
goto v___jp_932_;
}
else
{
lean_object* v___x_956_; 
lean_dec_ref(v___x_954_);
v___x_956_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_933_ = v_ref_953_;
v_a_934_ = v___x_956_;
goto v___jp_932_;
}
}
v___jp_957_:
{
if (v_clsEnabled_899_ == 0)
{
if (v___y_958_ == 0)
{
lean_object* v___x_959_; lean_object* v_traceState_960_; lean_object* v_env_961_; lean_object* v_nextMacroScope_962_; lean_object* v_ngen_963_; lean_object* v_auxDeclNGen_964_; lean_object* v_cache_965_; lean_object* v_messages_966_; lean_object* v_infoState_967_; lean_object* v_snapshotTasks_968_; lean_object* v_newDecls_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_988_; 
lean_del_object(v___x_928_);
lean_dec(v_snd_926_);
lean_dec(v_fst_925_);
lean_del_object(v___x_909_);
lean_dec_ref(v_msg_901_);
lean_dec_ref(v_tag_897_);
lean_dec(v_cls_895_);
v___x_959_ = lean_st_ref_take(v___y_904_);
v_traceState_960_ = lean_ctor_get(v___x_959_, 4);
v_env_961_ = lean_ctor_get(v___x_959_, 0);
v_nextMacroScope_962_ = lean_ctor_get(v___x_959_, 1);
v_ngen_963_ = lean_ctor_get(v___x_959_, 2);
v_auxDeclNGen_964_ = lean_ctor_get(v___x_959_, 3);
v_cache_965_ = lean_ctor_get(v___x_959_, 5);
v_messages_966_ = lean_ctor_get(v___x_959_, 6);
v_infoState_967_ = lean_ctor_get(v___x_959_, 7);
v_snapshotTasks_968_ = lean_ctor_get(v___x_959_, 8);
v_newDecls_969_ = lean_ctor_get(v___x_959_, 9);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_988_ == 0)
{
v___x_971_ = v___x_959_;
v_isShared_972_ = v_isSharedCheck_988_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_newDecls_969_);
lean_inc(v_snapshotTasks_968_);
lean_inc(v_infoState_967_);
lean_inc(v_messages_966_);
lean_inc(v_cache_965_);
lean_inc(v_traceState_960_);
lean_inc(v_auxDeclNGen_964_);
lean_inc(v_ngen_963_);
lean_inc(v_nextMacroScope_962_);
lean_inc(v_env_961_);
lean_dec(v___x_959_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_988_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
uint64_t v_tid_973_; lean_object* v_traces_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_tid_973_ = lean_ctor_get_uint64(v_traceState_960_, sizeof(void*)*1);
v_traces_974_ = lean_ctor_get(v_traceState_960_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_traceState_960_);
if (v_isSharedCheck_987_ == 0)
{
v___x_976_ = v_traceState_960_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_traces_974_);
lean_dec(v_traceState_960_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_900_, v_traces_974_);
lean_dec_ref(v_traces_974_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_978_);
lean_ctor_set_uint64(v_reuseFailAlloc_986_, sizeof(void*)*1, v_tid_973_);
v___x_980_ = v_reuseFailAlloc_986_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 4, v___x_980_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_env_961_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_nextMacroScope_962_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_ngen_963_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_auxDeclNGen_964_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 5, v_cache_965_);
lean_ctor_set(v_reuseFailAlloc_985_, 6, v_messages_966_);
lean_ctor_set(v_reuseFailAlloc_985_, 7, v_infoState_967_);
lean_ctor_set(v_reuseFailAlloc_985_, 8, v_snapshotTasks_968_);
lean_ctor_set(v_reuseFailAlloc_985_, 9, v_newDecls_969_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_st_ref_set(v___y_904_, v___x_982_);
v___x_984_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_906_);
return v___x_984_;
}
}
}
}
}
else
{
goto v___jp_952_;
}
}
else
{
goto v___jp_952_;
}
}
v___jp_989_:
{
double v___x_991_; double v___x_992_; double v___x_993_; uint8_t v___x_994_; 
v___x_991_ = lean_unbox_float(v_snd_926_);
v___x_992_ = lean_unbox_float(v_fst_925_);
v___x_993_ = lean_float_sub(v___x_991_, v___x_992_);
v___x_994_ = lean_float_decLt(v___y_990_, v___x_993_);
v___y_958_ = v___x_994_;
goto v___jp_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___boxed(lean_object* v_cls_1007_, lean_object* v_collapsed_1008_, lean_object* v_tag_1009_, lean_object* v_opts_1010_, lean_object* v_clsEnabled_1011_, lean_object* v_oldTraces_1012_, lean_object* v_msg_1013_, lean_object* v_resStartStop_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v_collapsed_boxed_1018_; uint8_t v_clsEnabled_boxed_1019_; lean_object* v_res_1020_; 
v_collapsed_boxed_1018_ = lean_unbox(v_collapsed_1008_);
v_clsEnabled_boxed_1019_ = lean_unbox(v_clsEnabled_1011_);
v_res_1020_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v_cls_1007_, v_collapsed_boxed_1018_, v_tag_1009_, v_opts_1010_, v_clsEnabled_boxed_1019_, v_oldTraces_1012_, v_msg_1013_, v_resStartStop_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_opts_1010_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(lean_object* v_cls_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_ref_1026_; lean_object* v___x_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1073_; 
v_ref_1026_ = lean_ctor_get(v___y_1023_, 5);
v___x_1027_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_1022_, v___y_1023_, v___y_1024_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1073_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1073_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v_traceState_1033_; lean_object* v_env_1034_; lean_object* v_nextMacroScope_1035_; lean_object* v_ngen_1036_; lean_object* v_auxDeclNGen_1037_; lean_object* v_cache_1038_; lean_object* v_messages_1039_; lean_object* v_infoState_1040_; lean_object* v_snapshotTasks_1041_; lean_object* v_newDecls_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1072_; 
v___x_1032_ = lean_st_ref_take(v___y_1024_);
v_traceState_1033_ = lean_ctor_get(v___x_1032_, 4);
v_env_1034_ = lean_ctor_get(v___x_1032_, 0);
v_nextMacroScope_1035_ = lean_ctor_get(v___x_1032_, 1);
v_ngen_1036_ = lean_ctor_get(v___x_1032_, 2);
v_auxDeclNGen_1037_ = lean_ctor_get(v___x_1032_, 3);
v_cache_1038_ = lean_ctor_get(v___x_1032_, 5);
v_messages_1039_ = lean_ctor_get(v___x_1032_, 6);
v_infoState_1040_ = lean_ctor_get(v___x_1032_, 7);
v_snapshotTasks_1041_ = lean_ctor_get(v___x_1032_, 8);
v_newDecls_1042_ = lean_ctor_get(v___x_1032_, 9);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1044_ = v___x_1032_;
v_isShared_1045_ = v_isSharedCheck_1072_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_newDecls_1042_);
lean_inc(v_snapshotTasks_1041_);
lean_inc(v_infoState_1040_);
lean_inc(v_messages_1039_);
lean_inc(v_cache_1038_);
lean_inc(v_traceState_1033_);
lean_inc(v_auxDeclNGen_1037_);
lean_inc(v_ngen_1036_);
lean_inc(v_nextMacroScope_1035_);
lean_inc(v_env_1034_);
lean_dec(v___x_1032_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1072_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint64_t v_tid_1046_; lean_object* v_traces_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1071_; 
v_tid_1046_ = lean_ctor_get_uint64(v_traceState_1033_, sizeof(void*)*1);
v_traces_1047_ = lean_ctor_get(v_traceState_1033_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_traceState_1033_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1049_ = v_traceState_1033_;
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_traces_1047_);
lean_dec(v_traceState_1033_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; double v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
v___x_1053_ = 0;
v___x_1054_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_1055_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1055_, 0, v_cls_1021_);
lean_ctor_set(v___x_1055_, 1, v___x_1051_);
lean_ctor_set(v___x_1055_, 2, v___x_1054_);
lean_ctor_set_float(v___x_1055_, sizeof(void*)*3, v___x_1052_);
lean_ctor_set_float(v___x_1055_, sizeof(void*)*3 + 8, v___x_1052_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3 + 16, v___x_1053_);
v___x_1056_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_1057_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v_a_1028_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
lean_inc(v_ref_1026_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_ref_1026_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = l_Lean_PersistentArray_push___redArg(v_traces_1047_, v___x_1058_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1059_);
v___x_1061_ = v___x_1049_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1059_);
lean_ctor_set_uint64(v_reuseFailAlloc_1070_, sizeof(void*)*1, v_tid_1046_);
v___x_1061_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v___x_1061_);
v___x_1063_ = v___x_1044_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_env_1034_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_nextMacroScope_1035_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_ngen_1036_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_auxDeclNGen_1037_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_cache_1038_);
lean_ctor_set(v_reuseFailAlloc_1069_, 6, v_messages_1039_);
lean_ctor_set(v_reuseFailAlloc_1069_, 7, v_infoState_1040_);
lean_ctor_set(v_reuseFailAlloc_1069_, 8, v_snapshotTasks_1041_);
lean_ctor_set(v_reuseFailAlloc_1069_, 9, v_newDecls_1042_);
v___x_1063_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = lean_st_ref_set(v___y_1024_, v___x_1063_);
v___x_1065_ = lean_box(0);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1065_);
v___x_1067_ = v___x_1030_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___boxed(lean_object* v_cls_1074_, lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v_cls_1074_, v_msg_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_ref_1084_; lean_object* v___x_1085_; lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_ref_1084_ = lean_ctor_get(v___y_1081_, 5);
v___x_1085_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_1080_, v___y_1081_, v___y_1082_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_inc(v_ref_1084_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_ref_1084_);
lean_ctor_set(v___x_1090_, 1, v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v_msg_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1099_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3(void){
_start:
{
lean_object* v___x_1103_; double v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1000000000u);
v___x_1104_ = lean_float_of_nat(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object* v_lratPath_1110_, uint8_t v_trimProofs_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_IO_FS_readBinFile(v_lratPath_1110_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_options_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1551_; 
v_options_1116_ = lean_ctor_get(v_a_1112_, 2);
v_a_1117_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1551_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1551_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_ref_1121_; lean_object* v_inheritedTraceOptions_1122_; uint8_t v_hasTrace_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v_proof_1128_; lean_object* v___y_1129_; lean_object* v_options_1130_; lean_object* v_inheritedTraceOptions_1131_; lean_object* v___y_1132_; lean_object* v_proof_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; lean_object* v_a_1185_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v_a_1201_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; lean_object* v_a_1210_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; uint8_t v___y_1228_; lean_object* v_a_1229_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v_a_1388_; lean_object* v___y_1410_; 
v_ref_1121_ = lean_ctor_get(v_a_1112_, 5);
v_inheritedTraceOptions_1122_ = lean_ctor_get(v_a_1112_, 13);
v_hasTrace_1123_ = lean_ctor_get_uint8(v_options_1116_, sizeof(void*)*1);
v___f_1124_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0));
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_1125_, 0, v_a_1117_);
v___x_1126_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_1176_ = 1;
v___x_1177_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_1123_ == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = l_IO_lazyPure___redArg(v___f_1125_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
if (lean_obj_tag(v_a_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_a_1414_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v_a_1413_);
v___x_1415_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1416_ = l_Lean_stringToMessageData(v_a_1414_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1417_, v_a_1112_, v_a_1113_);
v___y_1410_ = v___x_1418_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1419_; 
v_a_1419_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v_a_1413_);
v_a_1388_ = v_a_1419_;
goto v___jp_1387_;
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1431_; 
lean_del_object(v___x_1119_);
v_a_1420_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1422_ = v___x_1412_;
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1412_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1424_ = lean_io_error_to_string(v_a_1420_);
v___x_1425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
v___x_1426_ = l_Lean_MessageData_ofFormat(v___x_1425_);
lean_inc(v_ref_1121_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_ref_1121_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1427_);
v___x_1429_ = v___x_1422_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v___f_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v_a_1438_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v_a_1453_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v_a_1458_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v_a_1463_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v_a_1475_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v_a_1480_; 
v___f_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7));
v___x_1433_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1122_, v_options_1116_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = l_Lean_trace_profiler;
v___x_1530_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1116_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = l_IO_lazyPure___redArg(v___f_1125_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
if (lean_obj_tag(v_a_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_a_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v_a_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1535_ = l_Lean_stringToMessageData(v_a_1533_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1536_, v_a_1112_, v_a_1113_);
v___y_1410_ = v___x_1537_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v_a_1532_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v_a_1532_);
v_a_1388_ = v_a_1538_;
goto v___jp_1387_;
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1119_);
v_a_1539_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1541_ = v___x_1531_;
v_isShared_1542_ = v_isSharedCheck_1550_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1531_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1550_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1543_ = lean_io_error_to_string(v_a_1539_);
v___x_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
v___x_1545_ = l_Lean_MessageData_ofFormat(v___x_1544_);
lean_inc(v_ref_1121_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_ref_1121_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1546_);
v___x_1548_ = v___x_1541_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
goto v___jp_1482_;
}
}
else
{
goto v___jp_1482_;
}
v___jp_1435_:
{
lean_object* v___x_1439_; double v___x_1440_; double v___x_1441_; double v___x_1442_; double v___x_1443_; double v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1439_ = lean_io_mono_nanos_now();
v___x_1440_ = lean_float_of_nat(v___y_1437_);
v___x_1441_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1442_ = lean_float_div(v___x_1440_, v___x_1441_);
v___x_1443_ = lean_float_of_nat(v___x_1439_);
v___x_1444_ = lean_float_div(v___x_1443_, v___x_1441_);
v___x_1445_ = lean_box_float(v___x_1442_);
v___x_1446_ = lean_box_float(v___x_1444_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_a_1438_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1126_, v___x_1176_, v___x_1177_, v_options_1116_, v___x_1434_, v___y_1436_, v___f_1432_, v___x_1448_, v_a_1112_, v_a_1113_);
v___y_1410_ = v___x_1449_;
goto v___jp_1409_;
}
v___jp_1450_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1453_);
v___y_1436_ = v___y_1451_;
v___y_1437_ = v___y_1452_;
v_a_1438_ = v___x_1454_;
goto v___jp_1435_;
}
v___jp_1455_:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_a_1458_);
v___y_1436_ = v___y_1456_;
v___y_1437_ = v___y_1457_;
v_a_1438_ = v___x_1459_;
goto v___jp_1435_;
}
v___jp_1460_:
{
lean_object* v___x_1464_; double v___x_1465_; double v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1464_ = lean_io_get_num_heartbeats();
v___x_1465_ = lean_float_of_nat(v___y_1462_);
v___x_1466_ = lean_float_of_nat(v___x_1464_);
v___x_1467_ = lean_box_float(v___x_1465_);
v___x_1468_ = lean_box_float(v___x_1466_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1463_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1126_, v___x_1176_, v___x_1177_, v_options_1116_, v___x_1434_, v___y_1461_, v___f_1432_, v___x_1470_, v_a_1112_, v_a_1113_);
v___y_1410_ = v___x_1471_;
goto v___jp_1409_;
}
v___jp_1472_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1475_);
v___y_1461_ = v___y_1473_;
v___y_1462_ = v___y_1474_;
v_a_1463_ = v___x_1476_;
goto v___jp_1460_;
}
v___jp_1477_:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1480_);
v___y_1461_ = v___y_1478_;
v___y_1462_ = v___y_1479_;
v_a_1463_ = v___x_1481_;
goto v___jp_1460_;
}
v___jp_1482_:
{
lean_object* v___x_1483_; lean_object* v_a_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v_a_1113_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1486_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1116_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_io_mono_nanos_now();
v___x_1488_ = l_IO_lazyPure___redArg(v___f_1125_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v___x_1488_);
if (lean_obj_tag(v_a_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; 
v_a_1490_ = lean_ctor_get(v_a_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v_a_1489_);
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1492_ = l_Lean_stringToMessageData(v_a_1490_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1493_, v_a_1112_, v_a_1113_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___y_1451_ = v_a_1484_;
v___y_1452_ = v___x_1487_;
v_a_1453_ = v_a_1495_;
goto v___jp_1450_;
}
else
{
lean_object* v_a_1496_; 
v_a_1496_ = lean_ctor_get(v_a_1489_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v_a_1489_);
v___y_1456_ = v_a_1484_;
v___y_1457_ = v___x_1487_;
v_a_1458_ = v_a_1496_;
goto v___jp_1455_;
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1507_; 
v_a_1497_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1499_ = v___x_1488_;
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1488_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_io_error_to_string(v_a_1497_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 3);
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = l_Lean_MessageData_ofFormat(v___x_1503_);
lean_inc(v_ref_1121_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_ref_1121_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___y_1451_ = v_a_1484_;
v___y_1452_ = v___x_1487_;
v_a_1453_ = v___x_1505_;
goto v___jp_1450_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_io_get_num_heartbeats();
v___x_1509_ = l_IO_lazyPure___redArg(v___f_1125_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
if (lean_obj_tag(v_a_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_a_1516_; 
v_a_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v_a_1510_);
v___x_1512_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1513_ = l_Lean_stringToMessageData(v_a_1511_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1514_, v_a_1112_, v_a_1113_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
v___y_1473_ = v_a_1484_;
v___y_1474_ = v___x_1508_;
v_a_1475_ = v_a_1516_;
goto v___jp_1472_;
}
else
{
lean_object* v_a_1517_; 
v_a_1517_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v_a_1510_);
v___y_1478_ = v_a_1484_;
v___y_1479_ = v___x_1508_;
v_a_1480_ = v_a_1517_;
goto v___jp_1477_;
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1528_; 
v_a_1518_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1520_ = v___x_1509_;
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1509_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_io_error_to_string(v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 3);
lean_ctor_set(v___x_1520_, 0, v___x_1522_);
v___x_1524_ = v___x_1520_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = l_Lean_MessageData_ofFormat(v___x_1524_);
lean_inc(v_ref_1121_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_ref_1121_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___y_1473_ = v_a_1484_;
v___y_1474_ = v___x_1508_;
v_a_1475_ = v___x_1526_;
goto v___jp_1472_;
}
}
}
}
}
}
v___jp_1127_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1131_, v_options_1130_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1136_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v_proof_1128_);
v___x_1136_ = v___x_1119_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_proof_1128_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1119_);
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1139_ = lean_array_get_size(v_proof_1128_);
v___x_1140_ = l_Nat_reprFast(v___x_1139_);
v___x_1141_ = lean_string_append(v___x_1138_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_ofFormat(v___x_1144_);
v___x_1146_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v___x_1126_, v___x_1145_, v___y_1129_, v___y_1132_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_proof_1128_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_proof_1128_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_proof_1128_);
v_a_1155_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
v___jp_1163_:
{
lean_object* v_options_1167_; uint8_t v_hasTrace_1168_; 
v_options_1167_ = lean_ctor_get(v___y_1165_, 2);
v_hasTrace_1168_ = lean_ctor_get_uint8(v_options_1167_, sizeof(void*)*1);
if (v_hasTrace_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_del_object(v___x_1119_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_proof_1164_);
return v___x_1169_;
}
else
{
lean_object* v_inheritedTraceOptions_1170_; 
v_inheritedTraceOptions_1170_ = lean_ctor_get(v___y_1165_, 13);
v_proof_1128_ = v_proof_1164_;
v___y_1129_ = v___y_1165_;
v_options_1130_ = v_options_1167_;
v_inheritedTraceOptions_1131_ = v_inheritedTraceOptions_1170_;
v___y_1132_ = v___y_1166_;
goto v___jp_1127_;
}
}
v___jp_1171_:
{
if (lean_obj_tag(v___y_1174_) == 0)
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___y_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___y_1174_);
v_proof_1164_ = v_a_1175_;
v___y_1165_ = v___y_1173_;
v___y_1166_ = v___y_1172_;
goto v___jp_1163_;
}
else
{
lean_del_object(v___x_1119_);
return v___y_1174_;
}
}
v___jp_1178_:
{
lean_object* v___x_1186_; double v___x_1187_; double v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1186_ = lean_io_get_num_heartbeats();
v___x_1187_ = lean_float_of_nat(v___y_1181_);
v___x_1188_ = lean_float_of_nat(v___x_1186_);
v___x_1189_ = lean_box_float(v___x_1187_);
v___x_1190_ = lean_box_float(v___x_1188_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_a_1185_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1126_, v___x_1176_, v___x_1177_, v___y_1180_, v___y_1184_, v___y_1182_, v___f_1124_, v___x_1192_, v___y_1183_, v___y_1179_);
v___y_1172_ = v___y_1179_;
v___y_1173_ = v___y_1183_;
v___y_1174_ = v___x_1193_;
goto v___jp_1171_;
}
v___jp_1194_:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1201_);
v___y_1179_ = v___y_1195_;
v___y_1180_ = v___y_1196_;
v___y_1181_ = v___y_1197_;
v___y_1182_ = v___y_1198_;
v___y_1183_ = v___y_1199_;
v___y_1184_ = v___y_1200_;
v_a_1185_ = v___x_1202_;
goto v___jp_1178_;
}
v___jp_1203_:
{
lean_object* v___x_1211_; double v___x_1212_; double v___x_1213_; double v___x_1214_; double v___x_1215_; double v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1211_ = lean_io_mono_nanos_now();
v___x_1212_ = lean_float_of_nat(v___y_1206_);
v___x_1213_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1214_ = lean_float_div(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_float_of_nat(v___x_1211_);
v___x_1216_ = lean_float_div(v___x_1215_, v___x_1213_);
v___x_1217_ = lean_box_float(v___x_1214_);
v___x_1218_ = lean_box_float(v___x_1216_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1210_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1126_, v___x_1176_, v___x_1177_, v___y_1205_, v___y_1209_, v___y_1207_, v___f_1124_, v___x_1220_, v___y_1208_, v___y_1204_);
v___y_1172_ = v___y_1204_;
v___y_1173_ = v___y_1208_;
v___y_1174_ = v___x_1221_;
goto v___jp_1171_;
}
v___jp_1222_:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_a_1229_);
v___y_1204_ = v___y_1223_;
v___y_1205_ = v___y_1224_;
v___y_1206_ = v___y_1225_;
v___y_1207_ = v___y_1226_;
v___y_1208_ = v___y_1227_;
v___y_1209_ = v___y_1228_;
v_a_1210_ = v___x_1230_;
goto v___jp_1203_;
}
v___jp_1231_:
{
lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1238_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_1232_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1241_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_1233_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_io_mono_nanos_now();
v___x_1243_ = l_IO_lazyPure___redArg(v___y_1234_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 1);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v___y_1204_ = v___y_1232_;
v___y_1205_ = v___y_1233_;
v___y_1206_ = v___x_1242_;
v___y_1207_ = v_a_1239_;
v___y_1208_ = v___y_1236_;
v___y_1209_ = v___y_1237_;
v_a_1210_ = v___x_1251_;
goto v___jp_1203_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1264_; 
v_a_1254_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1256_ = v___x_1245_;
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1245_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_io_error_to_string(v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 3);
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = l_Lean_MessageData_ofFormat(v___x_1260_);
lean_inc(v___y_1235_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1235_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___y_1223_ = v___y_1232_;
v___y_1224_ = v___y_1233_;
v___y_1225_ = v___x_1242_;
v___y_1226_ = v_a_1239_;
v___y_1227_ = v___y_1236_;
v___y_1228_ = v___y_1237_;
v_a_1229_ = v___x_1262_;
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v_a_1265_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1267_ = v___x_1243_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1243_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_io_error_to_string(v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 3);
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
lean_inc(v___y_1235_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___y_1235_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___y_1223_ = v___y_1232_;
v___y_1224_ = v___y_1233_;
v___y_1225_ = v___x_1242_;
v___y_1226_ = v_a_1239_;
v___y_1227_ = v___y_1236_;
v___y_1228_ = v___y_1237_;
v_a_1229_ = v___x_1273_;
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_io_get_num_heartbeats();
v___x_1277_ = l_IO_lazyPure___redArg(v___y_1234_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 1);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v___y_1179_ = v___y_1232_;
v___y_1180_ = v___y_1233_;
v___y_1181_ = v___x_1276_;
v___y_1182_ = v_a_1239_;
v___y_1183_ = v___y_1236_;
v___y_1184_ = v___y_1237_;
v_a_1185_ = v___x_1285_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1298_; 
v_a_1288_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1290_ = v___x_1279_;
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1279_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_io_error_to_string(v_a_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 3);
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = l_Lean_MessageData_ofFormat(v___x_1294_);
lean_inc(v___y_1235_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1235_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___y_1195_ = v___y_1232_;
v___y_1196_ = v___y_1233_;
v___y_1197_ = v___x_1276_;
v___y_1198_ = v_a_1239_;
v___y_1199_ = v___y_1236_;
v___y_1200_ = v___y_1237_;
v_a_1201_ = v___x_1296_;
goto v___jp_1194_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1309_; 
v_a_1299_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1301_ = v___x_1277_;
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1277_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1309_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_io_error_to_string(v_a_1299_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set_tag(v___x_1301_, 3);
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = l_Lean_MessageData_ofFormat(v___x_1305_);
lean_inc(v___y_1235_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___y_1235_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___y_1195_ = v___y_1232_;
v___y_1196_ = v___y_1233_;
v___y_1197_ = v___x_1276_;
v___y_1198_ = v_a_1239_;
v___y_1199_ = v___y_1236_;
v___y_1200_ = v___y_1237_;
v_a_1201_ = v___x_1307_;
goto v___jp_1194_;
}
}
}
}
}
v___jp_1310_:
{
if (v_trimProofs_1111_ == 0)
{
lean_dec_ref(v___y_1311_);
v_proof_1164_ = v___y_1312_;
v___y_1165_ = v___y_1313_;
v___y_1166_ = v___y_1314_;
goto v___jp_1163_;
}
else
{
lean_object* v_options_1315_; uint8_t v_hasTrace_1316_; 
lean_dec_ref(v___y_1312_);
v_options_1315_ = lean_ctor_get(v___y_1313_, 2);
v_hasTrace_1316_ = lean_ctor_get_uint8(v_options_1315_, sizeof(void*)*1);
if (v_hasTrace_1316_ == 0)
{
lean_object* v_ref_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1119_);
v_ref_1317_ = lean_ctor_get(v___y_1313_, 5);
v___x_1318_ = l_IO_lazyPure___redArg(v___y_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
v___x_1320_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1340_; 
v_a_1329_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1331_ = v___x_1320_;
v_isShared_1332_ = v_isSharedCheck_1340_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1340_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1333_ = lean_io_error_to_string(v_a_1329_);
v___x_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = l_Lean_MessageData_ofFormat(v___x_1334_);
lean_inc(v_ref_1317_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_ref_1317_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1336_);
v___x_1338_ = v___x_1331_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1352_; 
v_a_1341_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1343_ = v___x_1318_;
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1318_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1345_ = lean_io_error_to_string(v_a_1341_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = l_Lean_MessageData_ofFormat(v___x_1346_);
lean_inc(v_ref_1317_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_ref_1317_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1348_);
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_ref_1353_; lean_object* v_inheritedTraceOptions_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_ref_1353_ = lean_ctor_get(v___y_1313_, 5);
v_inheritedTraceOptions_1354_ = lean_ctor_get(v___y_1313_, 13);
v___x_1355_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1356_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1354_, v_options_1315_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = l_Lean_trace_profiler;
v___x_1358_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1315_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = l_IO_lazyPure___redArg(v___y_1311_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v_proof_1128_ = v_a_1362_;
v___y_1129_ = v___y_1313_;
v_options_1130_ = v_options_1315_;
v_inheritedTraceOptions_1131_ = v_inheritedTraceOptions_1354_;
v___y_1132_ = v___y_1314_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1119_);
v_a_1363_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1374_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1374_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1367_ = lean_io_error_to_string(v_a_1363_);
v___x_1368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
v___x_1369_ = l_Lean_MessageData_ofFormat(v___x_1368_);
lean_inc(v_ref_1353_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_ref_1353_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1370_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1386_; 
lean_del_object(v___x_1119_);
v_a_1375_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1377_ = v___x_1359_;
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1359_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1379_ = lean_io_error_to_string(v_a_1375_);
v___x_1380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_ofFormat(v___x_1380_);
lean_inc(v_ref_1353_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_ref_1353_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1382_);
v___x_1384_ = v___x_1377_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
v___y_1232_ = v___y_1314_;
v___y_1233_ = v_options_1315_;
v___y_1234_ = v___y_1311_;
v___y_1235_ = v_ref_1353_;
v___y_1236_ = v___y_1313_;
v___y_1237_ = v___x_1356_;
goto v___jp_1231_;
}
}
else
{
v___y_1232_ = v___y_1314_;
v___y_1233_ = v_options_1315_;
v___y_1234_ = v___y_1311_;
v___y_1235_ = v_ref_1353_;
v___y_1236_ = v___y_1313_;
v___y_1237_ = v___x_1356_;
goto v___jp_1231_;
}
}
}
}
v___jp_1387_:
{
lean_object* v___f_1389_; 
lean_inc_ref(v_a_1388_);
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1389_, 0, v_a_1388_);
if (v_hasTrace_1123_ == 0)
{
v___y_1311_ = v___f_1389_;
v___y_1312_ = v_a_1388_;
v___y_1313_ = v_a_1112_;
v___y_1314_ = v_a_1113_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1391_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1122_, v_options_1116_, v___x_1390_);
if (v___x_1391_ == 0)
{
v___y_1311_ = v___f_1389_;
v___y_1312_ = v_a_1388_;
v___y_1313_ = v_a_1112_;
v___y_1314_ = v_a_1113_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1393_ = lean_array_get_size(v_a_1388_);
v___x_1394_ = l_Nat_reprFast(v___x_1393_);
v___x_1395_ = lean_string_append(v___x_1392_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4));
v___x_1397_ = lean_string_append(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___x_1399_ = l_Lean_MessageData_ofFormat(v___x_1398_);
v___x_1400_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v___x_1126_, v___x_1399_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_dec_ref(v___x_1400_);
v___y_1311_ = v___f_1389_;
v___y_1312_ = v_a_1388_;
v___y_1313_ = v_a_1112_;
v___y_1314_ = v_a_1113_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___f_1389_);
lean_dec_ref(v_a_1388_);
lean_del_object(v___x_1119_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
v___jp_1409_:
{
if (lean_obj_tag(v___y_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___y_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___y_1410_);
v_a_1388_ = v_a_1411_;
goto v___jp_1387_;
}
else
{
lean_del_object(v___x_1119_);
return v___y_1410_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1564_; 
v_a_1552_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1554_ = v___x_1115_;
v_isShared_1555_ = v_isSharedCheck_1564_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1115_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1564_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_ref_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v_ref_1556_ = lean_ctor_get(v_a_1112_, 5);
v___x_1557_ = lean_io_error_to_string(v_a_1552_);
v___x_1558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofFormat(v___x_1558_);
lean_inc(v_ref_1556_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_ref_1556_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1560_);
v___x_1562_ = v___x_1554_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object* v_lratPath_1565_, lean_object* v_trimProofs_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
uint8_t v_trimProofs_boxed_1570_; lean_object* v_res_1571_; 
v_trimProofs_boxed_1570_ = lean_unbox(v_trimProofs_1566_);
v_res_1571_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1565_, v_trimProofs_boxed_1570_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec_ref(v_lratPath_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6(lean_object* v_00_u03b1_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_x_1573_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6(v_00_u03b1_1578_, v_x_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object* v_00_u03b1_1584_, lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v_msg_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_msg_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v_00_u03b1_1590_, v_msg_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object* v_lratPath_1596_, uint8_t v_trimProofs_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1596_, v_trimProofs_1597_, v_a_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1602_);
lean_dec(v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object* v_lratPath_1619_, lean_object* v_trimProofs_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
uint8_t v_trimProofs_boxed_1624_; lean_object* v_res_1625_; 
v_trimProofs_boxed_1624_ = lean_unbox(v_trimProofs_1620_);
v_res_1625_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_1619_, v_trimProofs_boxed_1624_, v_a_1621_, v_a_1622_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec_ref(v_lratPath_1619_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1626_, lean_object* v___y_1627_, lean_object* v_a_x3f_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_io_remove_file(v_snd_1626_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1651_; 
v_a_1639_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1641_ = v___x_1630_;
v_isShared_1642_ = v_isSharedCheck_1651_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1630_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1651_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_ref_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_ref_1643_ = lean_ctor_get(v___y_1627_, 5);
v___x_1644_ = lean_io_error_to_string(v_a_1639_);
v___x_1645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___x_1646_ = l_Lean_MessageData_ofFormat(v___x_1645_);
lean_inc(v_ref_1643_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_ref_1643_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1647_);
v___x_1649_ = v___x_1641_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1652_, lean_object* v___y_1653_, lean_object* v_a_x3f_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1652_, v___y_1653_, v_a_x3f_1654_);
lean_dec(v_a_x3f_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_snd_1652_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(lean_object* v_f_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v_fst_1663_; lean_object* v_snd_1664_; lean_object* v_r_1665_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v_fst_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_fst_1663_);
v_snd_1664_ = lean_ctor_get(v_a_1662_, 1);
lean_inc_n(v_snd_1664_, 2);
lean_dec(v_a_1662_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
v_r_1665_ = lean_apply_5(v_f_1657_, v_fst_1663_, v_snd_1664_, v___y_1658_, v___y_1659_, lean_box(0));
if (lean_obj_tag(v_r_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1690_; 
v_a_1666_ = lean_ctor_get(v_r_1665_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_r_1665_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1668_ = v_r_1665_;
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v_r_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1690_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
lean_inc(v_a_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 1);
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1664_, v___y_1658_, v___x_1671_);
lean_dec_ref(v___x_1671_);
lean_dec(v_snd_1664_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1672_, 0);
lean_dec(v_unused_1680_);
v___x_1674_ = v___x_1672_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v___x_1672_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v_a_1666_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1666_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1666_);
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v_r_1665_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v_r_1665_);
v___x_1692_ = lean_box(0);
v___x_1693_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1664_, v___y_1658_, v___x_1692_);
lean_dec(v_snd_1664_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1701_);
v___x_1695_ = v___x_1693_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v___x_1693_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 0, v_a_1691_);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1691_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1691_);
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_f_1657_);
v_a_1710_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1712_ = v___x_1661_;
v_isShared_1713_ = v_isSharedCheck_1722_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1661_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1722_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_ref_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v_ref_1714_ = lean_ctor_get(v___y_1658_, 5);
v___x_1715_ = lean_io_error_to_string(v_a_1710_);
v___x_1716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
lean_inc(v_ref_1714_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_ref_1714_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1718_);
v___x_1720_ = v___x_1712_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___boxed(lean_object* v_f_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(lean_object* v_00_u03b1_1728_, lean_object* v_f_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1729_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_f_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(v_00_u03b1_1734_, v_f_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object* v_cnf_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_Sat_CNF_dimacs(v_cnf_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object* v_cnf_1743_, lean_object* v_x_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(v_cnf_1743_, v_x_1744_);
lean_dec_ref(v_cnf_1743_);
return v_res_1745_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1));
v___x_1750_ = l_Lean_MessageData_ofFormat(v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(v_x_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_x_1757_);
return v_res_1761_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1));
v___x_1766_ = l_Lean_MessageData_ofFormat(v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object* v_x_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object* v_x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(v_x_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_x_1773_);
return v_res_1777_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1));
v___x_1782_ = l_Lean_MessageData_ofFormat(v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object* v_x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(v_x_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_x_1789_);
return v_res_1793_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(lean_object* v_e_1794_){
_start:
{
if (lean_obj_tag(v_e_1794_) == 0)
{
uint8_t v___x_1795_; 
v___x_1795_ = 2;
return v___x_1795_;
}
else
{
uint8_t v___x_1796_; 
v___x_1796_ = 0;
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1797_){
_start:
{
uint8_t v_res_1798_; lean_object* v_r_1799_; 
v_res_1798_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_e_1797_);
lean_dec_ref(v_e_1797_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object* v_cls_1800_, uint8_t v_collapsed_1801_, lean_object* v_tag_1802_, lean_object* v_opts_1803_, uint8_t v_clsEnabled_1804_, lean_object* v_oldTraces_1805_, lean_object* v_msg_1806_, lean_object* v_resStartStop_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_fst_1811_; lean_object* v_snd_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1911_; 
v_fst_1811_ = lean_ctor_get(v_resStartStop_1807_, 0);
v_snd_1812_ = lean_ctor_get(v_resStartStop_1807_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_resStartStop_1807_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1814_ = v_resStartStop_1807_;
v_isShared_1815_ = v_isSharedCheck_1911_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_snd_1812_);
lean_inc(v_fst_1811_);
lean_dec(v_resStartStop_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1911_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v_data_1819_; lean_object* v_fst_1830_; lean_object* v_snd_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1910_; 
v_fst_1830_ = lean_ctor_get(v_snd_1812_, 0);
v_snd_1831_ = lean_ctor_get(v_snd_1812_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_snd_1812_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1833_ = v_snd_1812_;
v_isShared_1834_ = v_isSharedCheck_1910_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snd_1831_);
lean_inc(v_fst_1830_);
lean_dec(v_snd_1812_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1910_;
goto v_resetjp_1832_;
}
v___jp_1816_:
{
lean_object* v___x_1820_; 
lean_inc(v___y_1818_);
v___x_1820_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_1805_, v_data_1819_, v___y_1818_, v___y_1817_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1821_; 
lean_dec_ref(v___x_1820_);
v___x_1821_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1811_);
return v___x_1821_;
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_fst_1811_);
v_a_1822_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1820_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___y_1838_; lean_object* v_a_1839_; uint8_t v___y_1863_; double v___y_1895_; 
v___x_1835_ = l_Lean_trace_profiler;
v___x_1836_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1803_, v___x_1835_);
if (v___x_1836_ == 0)
{
v___y_1863_ = v___x_1836_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1901_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1803_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; double v___x_1904_; double v___x_1905_; double v___x_1906_; 
v___x_1902_ = l_Lean_trace_profiler_threshold;
v___x_1903_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1803_, v___x_1902_);
v___x_1904_ = lean_float_of_nat(v___x_1903_);
v___x_1905_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_1906_ = lean_float_div(v___x_1904_, v___x_1905_);
v___y_1895_ = v___x_1906_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; double v___x_1909_; 
v___x_1907_ = l_Lean_trace_profiler_threshold;
v___x_1908_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1803_, v___x_1907_);
v___x_1909_ = lean_float_of_nat(v___x_1908_);
v___y_1895_ = v___x_1909_;
goto v___jp_1894_;
}
}
v___jp_1837_:
{
uint8_t v_result_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v_result_1840_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_fst_1811_);
v___x_1841_ = l_Lean_TraceResult_toEmoji(v_result_1840_);
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
v___x_1843_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 7);
lean_ctor_set(v___x_1833_, 1, v___x_1843_);
lean_ctor_set(v___x_1833_, 0, v___x_1842_);
v___x_1845_ = v___x_1833_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v_m_1847_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v_a_1839_);
lean_ctor_set(v___x_1814_, 0, v___x_1845_);
v_m_1847_ = v___x_1814_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_a_1839_);
v_m_1847_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; double v___x_1850_; lean_object* v_data_1851_; 
v___x_1848_ = lean_box(v_result_1840_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
v___x_1850_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1802_);
lean_inc_ref(v___x_1849_);
lean_inc(v_cls_1800_);
v_data_1851_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1851_, 0, v_cls_1800_);
lean_ctor_set(v_data_1851_, 1, v___x_1849_);
lean_ctor_set(v_data_1851_, 2, v_tag_1802_);
lean_ctor_set_float(v_data_1851_, sizeof(void*)*3, v___x_1850_);
lean_ctor_set_float(v_data_1851_, sizeof(void*)*3 + 8, v___x_1850_);
lean_ctor_set_uint8(v_data_1851_, sizeof(void*)*3 + 16, v_collapsed_1801_);
if (v___x_1836_ == 0)
{
lean_dec_ref(v___x_1849_);
lean_dec(v_snd_1831_);
lean_dec(v_fst_1830_);
lean_dec_ref(v_tag_1802_);
lean_dec(v_cls_1800_);
v___y_1817_ = v_m_1847_;
v___y_1818_ = v___y_1838_;
v_data_1819_ = v_data_1851_;
goto v___jp_1816_;
}
else
{
lean_object* v_data_1852_; double v___x_1853_; double v___x_1854_; 
lean_dec_ref(v_data_1851_);
v_data_1852_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1852_, 0, v_cls_1800_);
lean_ctor_set(v_data_1852_, 1, v___x_1849_);
lean_ctor_set(v_data_1852_, 2, v_tag_1802_);
v___x_1853_ = lean_unbox_float(v_fst_1830_);
lean_dec(v_fst_1830_);
lean_ctor_set_float(v_data_1852_, sizeof(void*)*3, v___x_1853_);
v___x_1854_ = lean_unbox_float(v_snd_1831_);
lean_dec(v_snd_1831_);
lean_ctor_set_float(v_data_1852_, sizeof(void*)*3 + 8, v___x_1854_);
lean_ctor_set_uint8(v_data_1852_, sizeof(void*)*3 + 16, v_collapsed_1801_);
v___y_1817_ = v_m_1847_;
v___y_1818_ = v___y_1838_;
v_data_1819_ = v_data_1852_;
goto v___jp_1816_;
}
}
}
}
v___jp_1857_:
{
lean_object* v_ref_1858_; lean_object* v___x_1859_; 
v_ref_1858_ = lean_ctor_get(v___y_1808_, 5);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v_fst_1811_);
v___x_1859_ = lean_apply_4(v_msg_1806_, v_fst_1811_, v___y_1808_, v___y_1809_, lean_box(0));
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___y_1838_ = v_ref_1858_;
v_a_1839_ = v_a_1860_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_1838_ = v_ref_1858_;
v_a_1839_ = v___x_1861_;
goto v___jp_1837_;
}
}
v___jp_1862_:
{
if (v_clsEnabled_1804_ == 0)
{
if (v___y_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v_traceState_1865_; lean_object* v_env_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_cache_1870_; lean_object* v_messages_1871_; lean_object* v_infoState_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v_newDecls_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1893_; 
lean_del_object(v___x_1833_);
lean_dec(v_snd_1831_);
lean_dec(v_fst_1830_);
lean_del_object(v___x_1814_);
lean_dec_ref(v_msg_1806_);
lean_dec_ref(v_tag_1802_);
lean_dec(v_cls_1800_);
v___x_1864_ = lean_st_ref_take(v___y_1809_);
v_traceState_1865_ = lean_ctor_get(v___x_1864_, 4);
v_env_1866_ = lean_ctor_get(v___x_1864_, 0);
v_nextMacroScope_1867_ = lean_ctor_get(v___x_1864_, 1);
v_ngen_1868_ = lean_ctor_get(v___x_1864_, 2);
v_auxDeclNGen_1869_ = lean_ctor_get(v___x_1864_, 3);
v_cache_1870_ = lean_ctor_get(v___x_1864_, 5);
v_messages_1871_ = lean_ctor_get(v___x_1864_, 6);
v_infoState_1872_ = lean_ctor_get(v___x_1864_, 7);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1864_, 8);
v_newDecls_1874_ = lean_ctor_get(v___x_1864_, 9);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1876_ = v___x_1864_;
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_newDecls_1874_);
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1871_);
lean_inc(v_cache_1870_);
lean_inc(v_traceState_1865_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_inc(v_env_1866_);
lean_dec(v___x_1864_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint64_t v_tid_1878_; lean_object* v_traces_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1892_; 
v_tid_1878_ = lean_ctor_get_uint64(v_traceState_1865_, sizeof(void*)*1);
v_traces_1879_ = lean_ctor_get(v_traceState_1865_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_traceState_1865_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1881_ = v_traceState_1865_;
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_traces_1879_);
lean_dec(v_traceState_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1805_, v_traces_1879_);
lean_dec_ref(v_traces_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1891_, sizeof(void*)*1, v_tid_1878_);
v___x_1885_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 4, v___x_1885_);
v___x_1887_ = v___x_1876_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_env_1866_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_messages_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_infoState_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_snapshotTasks_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_newDecls_1874_);
v___x_1887_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_st_ref_set(v___y_1809_, v___x_1887_);
v___x_1889_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1811_);
return v___x_1889_;
}
}
}
}
}
else
{
goto v___jp_1857_;
}
}
else
{
goto v___jp_1857_;
}
}
v___jp_1894_:
{
double v___x_1896_; double v___x_1897_; double v___x_1898_; uint8_t v___x_1899_; 
v___x_1896_ = lean_unbox_float(v_snd_1831_);
v___x_1897_ = lean_unbox_float(v_fst_1830_);
v___x_1898_ = lean_float_sub(v___x_1896_, v___x_1897_);
v___x_1899_ = lean_float_decLt(v___y_1895_, v___x_1898_);
v___y_1863_ = v___x_1899_;
goto v___jp_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___boxed(lean_object* v_cls_1912_, lean_object* v_collapsed_1913_, lean_object* v_tag_1914_, lean_object* v_opts_1915_, lean_object* v_clsEnabled_1916_, lean_object* v_oldTraces_1917_, lean_object* v_msg_1918_, lean_object* v_resStartStop_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v_collapsed_boxed_1923_; uint8_t v_clsEnabled_boxed_1924_; lean_object* v_res_1925_; 
v_collapsed_boxed_1923_ = lean_unbox(v_collapsed_1913_);
v_clsEnabled_boxed_1924_ = lean_unbox(v_clsEnabled_1916_);
v_res_1925_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v_cls_1912_, v_collapsed_boxed_1923_, v_tag_1914_, v_opts_1915_, v_clsEnabled_boxed_1924_, v_oldTraces_1917_, v_msg_1918_, v_resStartStop_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v_opts_1915_);
return v_res_1925_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(lean_object* v_e_1926_){
_start:
{
if (lean_obj_tag(v_e_1926_) == 0)
{
uint8_t v___x_1927_; 
v___x_1927_ = 2;
return v___x_1927_;
}
else
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1929_){
_start:
{
uint8_t v_res_1930_; lean_object* v_r_1931_; 
v_res_1930_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_e_1929_);
lean_dec_ref(v_e_1929_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(lean_object* v_cls_1932_, uint8_t v_collapsed_1933_, lean_object* v_tag_1934_, lean_object* v_opts_1935_, uint8_t v_clsEnabled_1936_, lean_object* v_oldTraces_1937_, lean_object* v_msg_1938_, lean_object* v_resStartStop_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2043_; 
v_fst_1943_ = lean_ctor_get(v_resStartStop_1939_, 0);
v_snd_1944_ = lean_ctor_get(v_resStartStop_1939_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_resStartStop_1939_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_1946_ = v_resStartStop_1939_;
v_isShared_1947_ = v_isSharedCheck_2043_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snd_1944_);
lean_inc(v_fst_1943_);
lean_dec(v_resStartStop_1939_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2043_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_data_1951_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2042_; 
v_fst_1962_ = lean_ctor_get(v_snd_1944_, 0);
v_snd_1963_ = lean_ctor_get(v_snd_1944_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_snd_1944_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_1965_ = v_snd_1944_;
v_isShared_1966_ = v_isSharedCheck_2042_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_snd_1963_);
lean_inc(v_fst_1962_);
lean_dec(v_snd_1944_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2042_;
goto v_resetjp_1964_;
}
v___jp_1948_:
{
lean_object* v___x_1952_; 
lean_inc(v___y_1949_);
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_1937_, v_data_1951_, v___y_1949_, v___y_1950_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___x_1952_);
v___x_1953_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1943_);
return v___x_1953_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_fst_1943_);
v_a_1954_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1952_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___y_1970_; lean_object* v_a_1971_; uint8_t v___y_1995_; double v___y_2027_; 
v___x_1967_ = l_Lean_trace_profiler;
v___x_1968_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1935_, v___x_1967_);
if (v___x_1968_ == 0)
{
v___y_1995_ = v___x_1968_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2033_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1935_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; double v___x_2036_; double v___x_2037_; double v___x_2038_; 
v___x_2034_ = l_Lean_trace_profiler_threshold;
v___x_2035_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1935_, v___x_2034_);
v___x_2036_ = lean_float_of_nat(v___x_2035_);
v___x_2037_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_2038_ = lean_float_div(v___x_2036_, v___x_2037_);
v___y_2027_ = v___x_2038_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; double v___x_2041_; 
v___x_2039_ = l_Lean_trace_profiler_threshold;
v___x_2040_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1935_, v___x_2039_);
v___x_2041_ = lean_float_of_nat(v___x_2040_);
v___y_2027_ = v___x_2041_;
goto v___jp_2026_;
}
}
v___jp_1969_:
{
uint8_t v_result_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v_result_1972_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_fst_1943_);
v___x_1973_ = l_Lean_TraceResult_toEmoji(v_result_1972_);
v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
v___x_1975_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 7);
lean_ctor_set(v___x_1965_, 1, v___x_1975_);
lean_ctor_set(v___x_1965_, 0, v___x_1974_);
v___x_1977_ = v___x_1965_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v_m_1979_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 7);
lean_ctor_set(v___x_1946_, 1, v_a_1971_);
lean_ctor_set(v___x_1946_, 0, v___x_1977_);
v_m_1979_ = v___x_1946_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_a_1971_);
v_m_1979_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; double v___x_1982_; lean_object* v_data_1983_; 
v___x_1980_ = lean_box(v_result_1972_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
v___x_1982_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1934_);
lean_inc_ref(v___x_1981_);
lean_inc(v_cls_1932_);
v_data_1983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1983_, 0, v_cls_1932_);
lean_ctor_set(v_data_1983_, 1, v___x_1981_);
lean_ctor_set(v_data_1983_, 2, v_tag_1934_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3, v___x_1982_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3 + 8, v___x_1982_);
lean_ctor_set_uint8(v_data_1983_, sizeof(void*)*3 + 16, v_collapsed_1933_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v___x_1981_);
lean_dec(v_snd_1963_);
lean_dec(v_fst_1962_);
lean_dec_ref(v_tag_1934_);
lean_dec(v_cls_1932_);
v___y_1949_ = v___y_1970_;
v___y_1950_ = v_m_1979_;
v_data_1951_ = v_data_1983_;
goto v___jp_1948_;
}
else
{
lean_object* v_data_1984_; double v___x_1985_; double v___x_1986_; 
lean_dec_ref(v_data_1983_);
v_data_1984_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1984_, 0, v_cls_1932_);
lean_ctor_set(v_data_1984_, 1, v___x_1981_);
lean_ctor_set(v_data_1984_, 2, v_tag_1934_);
v___x_1985_ = lean_unbox_float(v_fst_1962_);
lean_dec(v_fst_1962_);
lean_ctor_set_float(v_data_1984_, sizeof(void*)*3, v___x_1985_);
v___x_1986_ = lean_unbox_float(v_snd_1963_);
lean_dec(v_snd_1963_);
lean_ctor_set_float(v_data_1984_, sizeof(void*)*3 + 8, v___x_1986_);
lean_ctor_set_uint8(v_data_1984_, sizeof(void*)*3 + 16, v_collapsed_1933_);
v___y_1949_ = v___y_1970_;
v___y_1950_ = v_m_1979_;
v_data_1951_ = v_data_1984_;
goto v___jp_1948_;
}
}
}
}
v___jp_1989_:
{
lean_object* v_ref_1990_; lean_object* v___x_1991_; 
v_ref_1990_ = lean_ctor_get(v___y_1940_, 5);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc(v_fst_1943_);
v___x_1991_ = lean_apply_4(v_msg_1938_, v_fst_1943_, v___y_1940_, v___y_1941_, lean_box(0));
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___y_1970_ = v_ref_1990_;
v_a_1971_ = v_a_1992_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_1993_; 
lean_dec_ref(v___x_1991_);
v___x_1993_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_1970_ = v_ref_1990_;
v_a_1971_ = v___x_1993_;
goto v___jp_1969_;
}
}
v___jp_1994_:
{
if (v_clsEnabled_1936_ == 0)
{
if (v___y_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v_traceState_1997_; lean_object* v_env_1998_; lean_object* v_nextMacroScope_1999_; lean_object* v_ngen_2000_; lean_object* v_auxDeclNGen_2001_; lean_object* v_cache_2002_; lean_object* v_messages_2003_; lean_object* v_infoState_2004_; lean_object* v_snapshotTasks_2005_; lean_object* v_newDecls_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2025_; 
lean_del_object(v___x_1965_);
lean_dec(v_snd_1963_);
lean_dec(v_fst_1962_);
lean_del_object(v___x_1946_);
lean_dec_ref(v_msg_1938_);
lean_dec_ref(v_tag_1934_);
lean_dec(v_cls_1932_);
v___x_1996_ = lean_st_ref_take(v___y_1941_);
v_traceState_1997_ = lean_ctor_get(v___x_1996_, 4);
v_env_1998_ = lean_ctor_get(v___x_1996_, 0);
v_nextMacroScope_1999_ = lean_ctor_get(v___x_1996_, 1);
v_ngen_2000_ = lean_ctor_get(v___x_1996_, 2);
v_auxDeclNGen_2001_ = lean_ctor_get(v___x_1996_, 3);
v_cache_2002_ = lean_ctor_get(v___x_1996_, 5);
v_messages_2003_ = lean_ctor_get(v___x_1996_, 6);
v_infoState_2004_ = lean_ctor_get(v___x_1996_, 7);
v_snapshotTasks_2005_ = lean_ctor_get(v___x_1996_, 8);
v_newDecls_2006_ = lean_ctor_get(v___x_1996_, 9);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2008_ = v___x_1996_;
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_newDecls_2006_);
lean_inc(v_snapshotTasks_2005_);
lean_inc(v_infoState_2004_);
lean_inc(v_messages_2003_);
lean_inc(v_cache_2002_);
lean_inc(v_traceState_1997_);
lean_inc(v_auxDeclNGen_2001_);
lean_inc(v_ngen_2000_);
lean_inc(v_nextMacroScope_1999_);
lean_inc(v_env_1998_);
lean_dec(v___x_1996_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
uint64_t v_tid_2010_; lean_object* v_traces_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2024_; 
v_tid_2010_ = lean_ctor_get_uint64(v_traceState_1997_, sizeof(void*)*1);
v_traces_2011_ = lean_ctor_get(v_traceState_1997_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_traceState_1997_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2013_ = v_traceState_1997_;
v_isShared_2014_ = v_isSharedCheck_2024_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_traces_2011_);
lean_dec(v_traceState_1997_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2024_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1937_, v_traces_2011_);
lean_dec_ref(v_traces_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2015_);
lean_ctor_set_uint64(v_reuseFailAlloc_2023_, sizeof(void*)*1, v_tid_2010_);
v___x_2017_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2017_);
v___x_2019_ = v___x_2008_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_env_1998_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_nextMacroScope_1999_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_ngen_2000_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_auxDeclNGen_2001_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_cache_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_messages_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_infoState_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_snapshotTasks_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 9, v_newDecls_2006_);
v___x_2019_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_st_ref_set(v___y_1941_, v___x_2019_);
v___x_2021_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1943_);
return v___x_2021_;
}
}
}
}
}
else
{
goto v___jp_1989_;
}
}
else
{
goto v___jp_1989_;
}
}
v___jp_2026_:
{
double v___x_2028_; double v___x_2029_; double v___x_2030_; uint8_t v___x_2031_; 
v___x_2028_ = lean_unbox_float(v_snd_1963_);
v___x_2029_ = lean_unbox_float(v_fst_1962_);
v___x_2030_ = lean_float_sub(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_float_decLt(v___y_2027_, v___x_2030_);
v___y_1995_ = v___x_2031_;
goto v___jp_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1___boxed(lean_object* v_cls_2044_, lean_object* v_collapsed_2045_, lean_object* v_tag_2046_, lean_object* v_opts_2047_, lean_object* v_clsEnabled_2048_, lean_object* v_oldTraces_2049_, lean_object* v_msg_2050_, lean_object* v_resStartStop_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v_collapsed_boxed_2055_; uint8_t v_clsEnabled_boxed_2056_; lean_object* v_res_2057_; 
v_collapsed_boxed_2055_ = lean_unbox(v_collapsed_2045_);
v_clsEnabled_boxed_2056_ = lean_unbox(v_clsEnabled_2048_);
v_res_2057_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v_cls_2044_, v_collapsed_boxed_2055_, v_tag_2046_, v_opts_2047_, v_clsEnabled_boxed_2056_, v_oldTraces_2049_, v_msg_2050_, v_resStartStop_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec_ref(v_opts_2047_);
return v_res_2057_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(lean_object* v_e_2058_){
_start:
{
if (lean_obj_tag(v_e_2058_) == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = 2;
return v___x_2059_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = 0;
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4___boxed(lean_object* v_e_2061_){
_start:
{
uint8_t v_res_2062_; lean_object* v_r_2063_; 
v_res_2062_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_e_2061_);
lean_dec_ref(v_e_2061_);
v_r_2063_ = lean_box(v_res_2062_);
return v_r_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(lean_object* v_cls_2064_, uint8_t v_collapsed_2065_, lean_object* v_tag_2066_, lean_object* v_opts_2067_, uint8_t v_clsEnabled_2068_, lean_object* v_oldTraces_2069_, lean_object* v_msg_2070_, lean_object* v_resStartStop_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2167_; 
v_fst_2075_ = lean_ctor_get(v_resStartStop_2071_, 0);
v_snd_2076_ = lean_ctor_get(v_resStartStop_2071_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_resStartStop_2071_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2078_ = v_resStartStop_2071_;
v_isShared_2079_ = v_isSharedCheck_2167_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_inc(v_fst_2075_);
lean_dec(v_resStartStop_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2167_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v_data_2083_; lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2166_; 
v_fst_2086_ = lean_ctor_get(v_snd_2076_, 0);
v_snd_2087_ = lean_ctor_get(v_snd_2076_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_snd_2076_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2089_ = v_snd_2076_;
v_isShared_2090_ = v_isSharedCheck_2166_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_snd_2087_);
lean_inc(v_fst_2086_);
lean_dec(v_snd_2076_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2166_;
goto v_resetjp_2088_;
}
v___jp_2080_:
{
lean_object* v___x_2084_; 
lean_inc(v___y_2081_);
v___x_2084_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_2069_, v_data_2083_, v___y_2081_, v___y_2082_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_2084_);
v___x_2085_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_2075_);
return v___x_2085_;
}
else
{
lean_dec(v_fst_2075_);
return v___x_2084_;
}
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___y_2094_; lean_object* v_a_2095_; uint8_t v___y_2119_; double v___y_2151_; 
v___x_2091_ = l_Lean_trace_profiler;
v___x_2092_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_2067_, v___x_2091_);
if (v___x_2092_ == 0)
{
v___y_2119_ = v___x_2092_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2157_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_2067_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; double v___x_2160_; double v___x_2161_; double v___x_2162_; 
v___x_2158_ = l_Lean_trace_profiler_threshold;
v___x_2159_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_2067_, v___x_2158_);
v___x_2160_ = lean_float_of_nat(v___x_2159_);
v___x_2161_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_2162_ = lean_float_div(v___x_2160_, v___x_2161_);
v___y_2151_ = v___x_2162_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; double v___x_2165_; 
v___x_2163_ = l_Lean_trace_profiler_threshold;
v___x_2164_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_2067_, v___x_2163_);
v___x_2165_ = lean_float_of_nat(v___x_2164_);
v___y_2151_ = v___x_2165_;
goto v___jp_2150_;
}
}
v___jp_2093_:
{
uint8_t v_result_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_result_2096_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_fst_2075_);
v___x_2097_ = l_Lean_TraceResult_toEmoji(v_result_2096_);
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
v___x_2099_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 7);
lean_ctor_set(v___x_2089_, 1, v___x_2099_);
lean_ctor_set(v___x_2089_, 0, v___x_2098_);
v___x_2101_ = v___x_2089_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v_m_2103_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 7);
lean_ctor_set(v___x_2078_, 1, v_a_2095_);
lean_ctor_set(v___x_2078_, 0, v___x_2101_);
v_m_2103_ = v___x_2078_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2095_);
v_m_2103_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; double v___x_2106_; lean_object* v_data_2107_; 
v___x_2104_ = lean_box(v_result_2096_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
v___x_2106_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2066_);
lean_inc_ref(v___x_2105_);
lean_inc(v_cls_2064_);
v_data_2107_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2107_, 0, v_cls_2064_);
lean_ctor_set(v_data_2107_, 1, v___x_2105_);
lean_ctor_set(v_data_2107_, 2, v_tag_2066_);
lean_ctor_set_float(v_data_2107_, sizeof(void*)*3, v___x_2106_);
lean_ctor_set_float(v_data_2107_, sizeof(void*)*3 + 8, v___x_2106_);
lean_ctor_set_uint8(v_data_2107_, sizeof(void*)*3 + 16, v_collapsed_2065_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec(v_snd_2087_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_tag_2066_);
lean_dec(v_cls_2064_);
v___y_2081_ = v___y_2094_;
v___y_2082_ = v_m_2103_;
v_data_2083_ = v_data_2107_;
goto v___jp_2080_;
}
else
{
lean_object* v_data_2108_; double v___x_2109_; double v___x_2110_; 
lean_dec_ref(v_data_2107_);
v_data_2108_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2108_, 0, v_cls_2064_);
lean_ctor_set(v_data_2108_, 1, v___x_2105_);
lean_ctor_set(v_data_2108_, 2, v_tag_2066_);
v___x_2109_ = lean_unbox_float(v_fst_2086_);
lean_dec(v_fst_2086_);
lean_ctor_set_float(v_data_2108_, sizeof(void*)*3, v___x_2109_);
v___x_2110_ = lean_unbox_float(v_snd_2087_);
lean_dec(v_snd_2087_);
lean_ctor_set_float(v_data_2108_, sizeof(void*)*3 + 8, v___x_2110_);
lean_ctor_set_uint8(v_data_2108_, sizeof(void*)*3 + 16, v_collapsed_2065_);
v___y_2081_ = v___y_2094_;
v___y_2082_ = v_m_2103_;
v_data_2083_ = v_data_2108_;
goto v___jp_2080_;
}
}
}
}
v___jp_2113_:
{
lean_object* v_ref_2114_; lean_object* v___x_2115_; 
v_ref_2114_ = lean_ctor_get(v___y_2072_, 5);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v_fst_2075_);
v___x_2115_ = lean_apply_4(v_msg_2070_, v_fst_2075_, v___y_2072_, v___y_2073_, lean_box(0));
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___y_2094_ = v_ref_2114_;
v_a_2095_ = v_a_2116_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2117_; 
lean_dec_ref(v___x_2115_);
v___x_2117_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_2094_ = v_ref_2114_;
v_a_2095_ = v___x_2117_;
goto v___jp_2093_;
}
}
v___jp_2118_:
{
if (v_clsEnabled_2068_ == 0)
{
if (v___y_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v_traceState_2121_; lean_object* v_env_2122_; lean_object* v_nextMacroScope_2123_; lean_object* v_ngen_2124_; lean_object* v_auxDeclNGen_2125_; lean_object* v_cache_2126_; lean_object* v_messages_2127_; lean_object* v_infoState_2128_; lean_object* v_snapshotTasks_2129_; lean_object* v_newDecls_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2089_);
lean_dec(v_snd_2087_);
lean_dec(v_fst_2086_);
lean_del_object(v___x_2078_);
lean_dec_ref(v_msg_2070_);
lean_dec_ref(v_tag_2066_);
lean_dec(v_cls_2064_);
v___x_2120_ = lean_st_ref_take(v___y_2073_);
v_traceState_2121_ = lean_ctor_get(v___x_2120_, 4);
v_env_2122_ = lean_ctor_get(v___x_2120_, 0);
v_nextMacroScope_2123_ = lean_ctor_get(v___x_2120_, 1);
v_ngen_2124_ = lean_ctor_get(v___x_2120_, 2);
v_auxDeclNGen_2125_ = lean_ctor_get(v___x_2120_, 3);
v_cache_2126_ = lean_ctor_get(v___x_2120_, 5);
v_messages_2127_ = lean_ctor_get(v___x_2120_, 6);
v_infoState_2128_ = lean_ctor_get(v___x_2120_, 7);
v_snapshotTasks_2129_ = lean_ctor_get(v___x_2120_, 8);
v_newDecls_2130_ = lean_ctor_get(v___x_2120_, 9);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2132_ = v___x_2120_;
v_isShared_2133_ = v_isSharedCheck_2149_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_newDecls_2130_);
lean_inc(v_snapshotTasks_2129_);
lean_inc(v_infoState_2128_);
lean_inc(v_messages_2127_);
lean_inc(v_cache_2126_);
lean_inc(v_traceState_2121_);
lean_inc(v_auxDeclNGen_2125_);
lean_inc(v_ngen_2124_);
lean_inc(v_nextMacroScope_2123_);
lean_inc(v_env_2122_);
lean_dec(v___x_2120_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2149_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
uint64_t v_tid_2134_; lean_object* v_traces_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2148_; 
v_tid_2134_ = lean_ctor_get_uint64(v_traceState_2121_, sizeof(void*)*1);
v_traces_2135_ = lean_ctor_get(v_traceState_2121_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_traceState_2121_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2137_ = v_traceState_2121_;
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_traces_2135_);
lean_dec(v_traceState_2121_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2148_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2069_, v_traces_2135_);
lean_dec_ref(v_traces_2135_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2139_);
lean_ctor_set_uint64(v_reuseFailAlloc_2147_, sizeof(void*)*1, v_tid_2134_);
v___x_2141_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2141_);
v___x_2143_ = v___x_2132_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_env_2122_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_nextMacroScope_2123_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_ngen_2124_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_auxDeclNGen_2125_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2146_, 5, v_cache_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 6, v_messages_2127_);
lean_ctor_set(v_reuseFailAlloc_2146_, 7, v_infoState_2128_);
lean_ctor_set(v_reuseFailAlloc_2146_, 8, v_snapshotTasks_2129_);
lean_ctor_set(v_reuseFailAlloc_2146_, 9, v_newDecls_2130_);
v___x_2143_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_st_ref_set(v___y_2073_, v___x_2143_);
v___x_2145_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_2075_);
return v___x_2145_;
}
}
}
}
}
else
{
goto v___jp_2113_;
}
}
else
{
goto v___jp_2113_;
}
}
v___jp_2150_:
{
double v___x_2152_; double v___x_2153_; double v___x_2154_; uint8_t v___x_2155_; 
v___x_2152_ = lean_unbox_float(v_snd_2087_);
v___x_2153_ = lean_unbox_float(v_fst_2086_);
v___x_2154_ = lean_float_sub(v___x_2152_, v___x_2153_);
v___x_2155_ = lean_float_decLt(v___y_2151_, v___x_2154_);
v___y_2119_ = v___x_2155_;
goto v___jp_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2___boxed(lean_object* v_cls_2168_, lean_object* v_collapsed_2169_, lean_object* v_tag_2170_, lean_object* v_opts_2171_, lean_object* v_clsEnabled_2172_, lean_object* v_oldTraces_2173_, lean_object* v_msg_2174_, lean_object* v_resStartStop_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v_collapsed_boxed_2179_; uint8_t v_clsEnabled_boxed_2180_; lean_object* v_res_2181_; 
v_collapsed_boxed_2179_ = lean_unbox(v_collapsed_2169_);
v_clsEnabled_boxed_2180_ = lean_unbox(v_clsEnabled_2172_);
v_res_2181_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v_cls_2168_, v_collapsed_boxed_2179_, v_tag_2170_, v_opts_2171_, v_clsEnabled_boxed_2180_, v_oldTraces_2173_, v_msg_2174_, v_resStartStop_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_opts_2171_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object* v___f_2182_, lean_object* v_lratPath_2183_, uint8_t v_trimProofs_2184_, lean_object* v___f_2185_, lean_object* v_solver_2186_, lean_object* v_timeout_2187_, uint8_t v_binaryProofs_2188_, uint8_t v_solverMode_2189_, lean_object* v___f_2190_, lean_object* v___f_2191_, lean_object* v_cnfHandle_2192_, lean_object* v_cnfPath_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___y_2198_; lean_object* v_options_2216_; lean_object* v_ref_2217_; lean_object* v_inheritedTraceOptions_2218_; uint8_t v_hasTrace_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___y_2224_; uint8_t v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v_a_2228_; lean_object* v___y_2241_; uint8_t v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v_a_2245_; lean_object* v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2298_; lean_object* v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; lean_object* v___y_2333_; lean_object* v_a_2334_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; lean_object* v___y_2350_; lean_object* v_a_2351_; uint8_t v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2411_; 
v_options_2216_ = lean_ctor_get(v___y_2194_, 2);
v_ref_2217_ = lean_ctor_get(v___y_2194_, 5);
v_inheritedTraceOptions_2218_ = lean_ctor_get(v___y_2194_, 13);
v_hasTrace_2219_ = lean_ctor_get_uint8(v_options_2216_, sizeof(void*)*1);
v___x_2220_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_2221_ = 1;
v___x_2222_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_2219_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v___f_2191_);
v___x_2420_ = l_IO_lazyPure___redArg(v___f_2190_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v___x_2422_ = lean_io_prim_handle_put_str(v_cnfHandle_2192_, v_a_2421_);
lean_dec(v_a_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; 
lean_dec_ref(v___x_2422_);
v___x_2423_ = lean_io_prim_handle_flush(v_cnfHandle_2192_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref(v___x_2423_);
goto v___jp_2403_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2435_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2435_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2428_ = lean_io_error_to_string(v_a_2424_);
v___x_2429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
v___x_2430_ = l_Lean_MessageData_ofFormat(v___x_2429_);
lean_inc(v_ref_2217_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_ref_2217_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2431_);
v___x_2433_ = v___x_2426_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2436_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2438_ = v___x_2422_;
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2422_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2440_ = lean_io_error_to_string(v_a_2436_);
v___x_2441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
v___x_2442_ = l_Lean_MessageData_ofFormat(v___x_2441_);
lean_inc(v_ref_2217_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v_ref_2217_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2443_);
v___x_2445_ = v___x_2438_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2448_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2450_ = v___x_2420_;
v_isShared_2451_ = v_isSharedCheck_2459_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2420_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2459_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2452_ = lean_io_error_to_string(v_a_2448_);
v___x_2453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
v___x_2454_ = l_Lean_MessageData_ofFormat(v___x_2453_);
lean_inc(v_ref_2217_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_ref_2217_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2455_);
v___x_2457_ = v___x_2450_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_a_2465_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v_a_2480_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v_a_2485_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v_a_2497_; 
v___x_2460_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2218_, v_options_2216_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = l_Lean_trace_profiler;
v___x_2597_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2216_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
lean_dec_ref(v___f_2191_);
v___x_2598_ = l_IO_lazyPure___redArg(v___f_2190_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
v___x_2600_ = lean_io_prim_handle_put_str(v_cnfHandle_2192_, v_a_2599_);
lean_dec(v_a_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v___x_2601_; 
lean_dec_ref(v___x_2600_);
v___x_2601_ = lean_io_prim_handle_flush(v_cnfHandle_2192_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref(v___x_2601_);
goto v___jp_2403_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2613_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2613_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2606_ = lean_io_error_to_string(v_a_2602_);
v___x_2607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
v___x_2608_ = l_Lean_MessageData_ofFormat(v___x_2607_);
lean_inc(v_ref_2217_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_ref_2217_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2609_);
v___x_2611_ = v___x_2604_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2614_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2616_ = v___x_2600_;
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2600_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2618_ = lean_io_error_to_string(v_a_2614_);
v___x_2619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofFormat(v___x_2619_);
lean_inc(v_ref_2217_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_ref_2217_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2621_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2626_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2628_ = v___x_2598_;
v_isShared_2629_ = v_isSharedCheck_2637_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2598_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2637_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2630_ = lean_io_error_to_string(v_a_2626_);
v___x_2631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = l_Lean_MessageData_ofFormat(v___x_2631_);
lean_inc(v_ref_2217_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_ref_2217_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2633_);
v___x_2635_ = v___x_2628_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
goto v___jp_2499_;
}
}
else
{
goto v___jp_2499_;
}
v___jp_2462_:
{
lean_object* v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2466_ = lean_io_mono_nanos_now();
v___x_2467_ = lean_float_of_nat(v___y_2464_);
v___x_2468_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2469_ = lean_float_div(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_float_of_nat(v___x_2466_);
v___x_2471_ = lean_float_div(v___x_2470_, v___x_2468_);
v___x_2472_ = lean_box_float(v___x_2469_);
v___x_2473_ = lean_box_float(v___x_2471_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2465_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2220_, v___x_2221_, v___x_2222_, v_options_2216_, v___x_2461_, v___y_2463_, v___f_2191_, v___x_2475_, v___y_2194_, v___y_2195_);
v___y_2411_ = v___x_2476_;
goto v___jp_2410_;
}
v___jp_2477_:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_a_2480_);
v___y_2463_ = v___y_2478_;
v___y_2464_ = v___y_2479_;
v_a_2465_ = v___x_2481_;
goto v___jp_2462_;
}
v___jp_2482_:
{
lean_object* v___x_2486_; double v___x_2487_; double v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2486_ = lean_io_get_num_heartbeats();
v___x_2487_ = lean_float_of_nat(v___y_2484_);
v___x_2488_ = lean_float_of_nat(v___x_2486_);
v___x_2489_ = lean_box_float(v___x_2487_);
v___x_2490_ = lean_box_float(v___x_2488_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2485_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2220_, v___x_2221_, v___x_2222_, v_options_2216_, v___x_2461_, v___y_2483_, v___f_2191_, v___x_2492_, v___y_2194_, v___y_2195_);
v___y_2411_ = v___x_2493_;
goto v___jp_2410_;
}
v___jp_2494_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2497_);
v___y_2483_ = v___y_2495_;
v___y_2484_ = v___y_2496_;
v_a_2485_ = v___x_2498_;
goto v___jp_2482_;
}
v___jp_2499_:
{
lean_object* v___x_2500_; lean_object* v_a_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2500_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2195_);
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2503_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2216_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_io_mono_nanos_now();
v___x_2505_ = l_IO_lazyPure___redArg(v___f_2190_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = lean_io_prim_handle_put_str(v_cnfHandle_2192_, v_a_2506_);
lean_dec(v_a_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; 
lean_dec_ref(v___x_2507_);
v___x_2508_ = lean_io_prim_handle_flush(v_cnfHandle_2192_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v___y_2463_ = v_a_2501_;
v___y_2464_ = v___x_2504_;
v_a_2465_ = v___x_2514_;
goto v___jp_2462_;
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2527_; 
v_a_2517_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2519_ = v___x_2508_;
v_isShared_2520_ = v_isSharedCheck_2527_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2527_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2521_ = lean_io_error_to_string(v_a_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 3);
lean_ctor_set(v___x_2519_, 0, v___x_2521_);
v___x_2523_ = v___x_2519_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = l_Lean_MessageData_ofFormat(v___x_2523_);
lean_inc(v_ref_2217_);
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_ref_2217_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___y_2478_ = v_a_2501_;
v___y_2479_ = v___x_2504_;
v_a_2480_ = v___x_2525_;
goto v___jp_2477_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2538_; 
v_a_2528_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2530_ = v___x_2507_;
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2507_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_io_error_to_string(v_a_2528_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set_tag(v___x_2530_, 3);
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = l_Lean_MessageData_ofFormat(v___x_2534_);
lean_inc(v_ref_2217_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_ref_2217_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___y_2478_ = v_a_2501_;
v___y_2479_ = v___x_2504_;
v_a_2480_ = v___x_2536_;
goto v___jp_2477_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2549_; 
v_a_2539_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2541_ = v___x_2505_;
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2505_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2549_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_io_error_to_string(v_a_2539_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 3);
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = l_Lean_MessageData_ofFormat(v___x_2545_);
lean_inc(v_ref_2217_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_ref_2217_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___y_2478_ = v_a_2501_;
v___y_2479_ = v___x_2504_;
v_a_2480_ = v___x_2547_;
goto v___jp_2477_;
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_io_get_num_heartbeats();
v___x_2551_ = l_IO_lazyPure___redArg(v___f_2190_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = lean_io_prim_handle_put_str(v_cnfHandle_2192_, v_a_2552_);
lean_dec(v_a_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v___x_2553_);
v___x_2554_ = lean_io_prim_handle_flush(v_cnfHandle_2192_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 1);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2483_ = v_a_2501_;
v___y_2484_ = v___x_2550_;
v_a_2485_ = v___x_2560_;
goto v___jp_2482_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2573_; 
v_a_2563_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2565_ = v___x_2554_;
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2554_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2573_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_io_error_to_string(v_a_2563_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 3);
lean_ctor_set(v___x_2565_, 0, v___x_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = l_Lean_MessageData_ofFormat(v___x_2569_);
lean_inc(v_ref_2217_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_ref_2217_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___y_2495_ = v_a_2501_;
v___y_2496_ = v___x_2550_;
v_a_2497_ = v___x_2571_;
goto v___jp_2494_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2584_; 
v_a_2574_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2576_ = v___x_2553_;
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2553_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_io_error_to_string(v_a_2574_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 3);
lean_ctor_set(v___x_2576_, 0, v___x_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = l_Lean_MessageData_ofFormat(v___x_2580_);
lean_inc(v_ref_2217_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_ref_2217_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___y_2495_ = v_a_2501_;
v___y_2496_ = v___x_2550_;
v_a_2497_ = v___x_2582_;
goto v___jp_2494_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2595_; 
v_a_2585_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2587_ = v___x_2551_;
v_isShared_2588_ = v_isSharedCheck_2595_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2551_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2595_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_io_error_to_string(v_a_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 3);
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = l_Lean_MessageData_ofFormat(v___x_2591_);
lean_inc(v_ref_2217_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_ref_2217_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___y_2495_ = v_a_2501_;
v___y_2496_ = v___x_2550_;
v_a_2497_ = v___x_2593_;
goto v___jp_2494_;
}
}
}
}
}
}
v___jp_2197_:
{
if (lean_obj_tag(v___y_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2207_; 
v_a_2199_ = lean_ctor_get(v___y_2198_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___y_2198_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2201_ = v___y_2198_;
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___y_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___y_2198_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___y_2198_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___y_2198_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___y_2198_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
v___jp_2223_:
{
lean_object* v___x_2229_; double v___x_2230_; double v___x_2231_; double v___x_2232_; double v___x_2233_; double v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2229_ = lean_io_mono_nanos_now();
v___x_2230_ = lean_float_of_nat(v___y_2226_);
v___x_2231_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2232_ = lean_float_div(v___x_2230_, v___x_2231_);
v___x_2233_ = lean_float_of_nat(v___x_2229_);
v___x_2234_ = lean_float_div(v___x_2233_, v___x_2231_);
v___x_2235_ = lean_box_float(v___x_2232_);
v___x_2236_ = lean_box_float(v___x_2234_);
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2228_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2220_, v___x_2221_, v___x_2222_, v___y_2224_, v___y_2225_, v___y_2227_, v___f_2182_, v___x_2238_, v___y_2194_, v___y_2195_);
v___y_2198_ = v___x_2239_;
goto v___jp_2197_;
}
v___jp_2240_:
{
lean_object* v___x_2246_; double v___x_2247_; double v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2246_ = lean_io_get_num_heartbeats();
v___x_2247_ = lean_float_of_nat(v___y_2243_);
v___x_2248_ = lean_float_of_nat(v___x_2246_);
v___x_2249_ = lean_box_float(v___x_2247_);
v___x_2250_ = lean_box_float(v___x_2248_);
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_a_2245_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2220_, v___x_2221_, v___x_2222_, v___y_2241_, v___y_2242_, v___y_2244_, v___f_2182_, v___x_2252_, v___y_2194_, v___y_2195_);
v___y_2198_ = v___x_2253_;
goto v___jp_2197_;
}
v___jp_2254_:
{
lean_object* v___x_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2257_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2195_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2260_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_2255_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_io_mono_nanos_now();
v___x_2262_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2183_, v_trimProofs_2184_, v___y_2194_, v___y_2195_);
lean_dec_ref(v_lratPath_2183_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 1);
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
v___y_2224_ = v___y_2255_;
v___y_2225_ = v___y_2256_;
v___y_2226_ = v___x_2261_;
v___y_2227_ = v_a_2258_;
v_a_2228_ = v___x_2268_;
goto v___jp_2223_;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
v_a_2271_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2262_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2262_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set_tag(v___x_2273_, 0);
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v___y_2224_ = v___y_2255_;
v___y_2225_ = v___y_2256_;
v___y_2226_ = v___x_2261_;
v___y_2227_ = v_a_2258_;
v_a_2228_ = v___x_2276_;
goto v___jp_2223_;
}
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_io_get_num_heartbeats();
v___x_2280_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2183_, v_trimProofs_2184_, v___y_2194_, v___y_2195_);
lean_dec_ref(v_lratPath_2183_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 1);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
v___y_2241_ = v___y_2255_;
v___y_2242_ = v___y_2256_;
v___y_2243_ = v___x_2279_;
v___y_2244_ = v_a_2258_;
v_a_2245_ = v___x_2286_;
goto v___jp_2240_;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2280_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2280_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set_tag(v___x_2291_, 0);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v___y_2241_ = v___y_2255_;
v___y_2242_ = v___y_2256_;
v___y_2243_ = v___x_2279_;
v___y_2244_ = v_a_2258_;
v_a_2245_ = v___x_2294_;
goto v___jp_2240_;
}
}
}
}
}
v___jp_2297_:
{
if (lean_obj_tag(v___y_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2320_; 
v_a_2299_ = lean_ctor_get(v___y_2298_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___y_2298_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2301_ = v___y_2298_;
v_isShared_2302_ = v_isSharedCheck_2320_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___y_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2320_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
if (lean_obj_tag(v_a_2299_) == 0)
{
lean_object* v_assignment_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_assignment_2303_ = lean_ctor_get(v_a_2299_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_a_2299_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2305_ = v_a_2299_;
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_assignment_2303_);
lean_dec(v_a_2299_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_assignment_2303_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2308_);
v___x_2310_ = v___x_2301_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_del_object(v___x_2301_);
lean_dec(v_a_2299_);
if (v_hasTrace_2219_ == 0)
{
lean_object* v___x_2314_; 
lean_dec_ref(v___f_2182_);
v___x_2314_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2183_, v_trimProofs_2184_, v___y_2194_, v___y_2195_);
lean_dec_ref(v_lratPath_2183_);
v___y_2198_ = v___x_2314_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2218_, v_options_2216_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = l_Lean_trace_profiler;
v___x_2318_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2216_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
lean_dec_ref(v___f_2182_);
v___x_2319_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2183_, v_trimProofs_2184_, v___y_2194_, v___y_2195_);
lean_dec_ref(v_lratPath_2183_);
v___y_2198_ = v___x_2319_;
goto v___jp_2197_;
}
else
{
v___y_2255_ = v_options_2216_;
v___y_2256_ = v___x_2316_;
goto v___jp_2254_;
}
}
else
{
v___y_2255_ = v_options_2216_;
v___y_2256_ = v___x_2316_;
goto v___jp_2254_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2321_ = lean_ctor_get(v___y_2298_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___y_2298_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___y_2298_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___y_2298_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
v___jp_2329_:
{
lean_object* v___x_2335_; double v___x_2336_; double v___x_2337_; double v___x_2338_; double v___x_2339_; double v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2335_ = lean_io_mono_nanos_now();
v___x_2336_ = lean_float_of_nat(v___y_2331_);
v___x_2337_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2338_ = lean_float_div(v___x_2336_, v___x_2337_);
v___x_2339_ = lean_float_of_nat(v___x_2335_);
v___x_2340_ = lean_float_div(v___x_2339_, v___x_2337_);
v___x_2341_ = lean_box_float(v___x_2338_);
v___x_2342_ = lean_box_float(v___x_2340_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2334_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2220_, v___x_2221_, v___x_2222_, v___y_2333_, v___y_2332_, v___y_2330_, v___f_2185_, v___x_2344_, v___y_2194_, v___y_2195_);
v___y_2298_ = v___x_2345_;
goto v___jp_2297_;
}
v___jp_2346_:
{
lean_object* v___x_2352_; double v___x_2353_; double v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2352_ = lean_io_get_num_heartbeats();
v___x_2353_ = lean_float_of_nat(v___y_2347_);
v___x_2354_ = lean_float_of_nat(v___x_2352_);
v___x_2355_ = lean_box_float(v___x_2353_);
v___x_2356_ = lean_box_float(v___x_2354_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_a_2351_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2220_, v___x_2221_, v___x_2222_, v___y_2350_, v___y_2349_, v___y_2348_, v___f_2185_, v___x_2358_, v___y_2194_, v___y_2195_);
v___y_2298_ = v___x_2359_;
goto v___jp_2297_;
}
v___jp_2360_:
{
lean_object* v___x_2363_; lean_object* v_a_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2363_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2195_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2366_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_2362_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_2183_);
v___x_2368_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2186_, v_cnfPath_2193_, v_lratPath_2183_, v_timeout_2187_, v_binaryProofs_2188_, v_solverMode_2189_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 1);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2330_ = v_a_2364_;
v___y_2331_ = v___x_2367_;
v___y_2332_ = v___y_2361_;
v___y_2333_ = v___y_2362_;
v_a_2334_ = v___x_2374_;
goto v___jp_2329_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2368_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2368_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 0);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
v___y_2330_ = v_a_2364_;
v___y_2331_ = v___x_2367_;
v___y_2332_ = v___y_2361_;
v___y_2333_ = v___y_2362_;
v_a_2334_ = v___x_2382_;
goto v___jp_2329_;
}
}
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_2183_);
v___x_2386_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2186_, v_cnfPath_2193_, v_lratPath_2183_, v_timeout_2187_, v_binaryProofs_2188_, v_solverMode_2189_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 1);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
v___y_2347_ = v___x_2385_;
v___y_2348_ = v_a_2364_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___y_2362_;
v_a_2351_ = v___x_2392_;
goto v___jp_2346_;
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2386_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2386_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 0);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
v___y_2347_ = v___x_2385_;
v___y_2348_ = v_a_2364_;
v___y_2349_ = v___y_2361_;
v___y_2350_ = v___y_2362_;
v_a_2351_ = v___x_2400_;
goto v___jp_2346_;
}
}
}
}
}
v___jp_2403_:
{
if (v_hasTrace_2219_ == 0)
{
lean_object* v___x_2404_; 
lean_dec_ref(v___f_2185_);
lean_inc_ref(v_lratPath_2183_);
v___x_2404_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2186_, v_cnfPath_2193_, v_lratPath_2183_, v_timeout_2187_, v_binaryProofs_2188_, v_solverMode_2189_, v___y_2194_, v___y_2195_);
v___y_2298_ = v___x_2404_;
goto v___jp_2297_;
}
else
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2218_, v_options_2216_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = l_Lean_trace_profiler;
v___x_2408_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2216_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec_ref(v___f_2185_);
lean_inc_ref(v_lratPath_2183_);
v___x_2409_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2186_, v_cnfPath_2193_, v_lratPath_2183_, v_timeout_2187_, v_binaryProofs_2188_, v_solverMode_2189_, v___y_2194_, v___y_2195_);
v___y_2298_ = v___x_2409_;
goto v___jp_2297_;
}
else
{
v___y_2361_ = v___x_2406_;
v___y_2362_ = v_options_2216_;
goto v___jp_2360_;
}
}
else
{
v___y_2361_ = v___x_2406_;
v___y_2362_ = v_options_2216_;
goto v___jp_2360_;
}
}
}
v___jp_2410_:
{
if (lean_obj_tag(v___y_2411_) == 0)
{
lean_dec_ref(v___y_2411_);
goto v___jp_2403_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_cnfPath_2193_);
lean_dec_ref(v_solver_2186_);
lean_dec_ref(v___f_2185_);
lean_dec_ref(v_lratPath_2183_);
lean_dec_ref(v___f_2182_);
v_a_2412_ = lean_ctor_get(v___y_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___y_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___y_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___y_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object* v___f_2638_, lean_object* v_lratPath_2639_, lean_object* v_trimProofs_2640_, lean_object* v___f_2641_, lean_object* v_solver_2642_, lean_object* v_timeout_2643_, lean_object* v_binaryProofs_2644_, lean_object* v_solverMode_2645_, lean_object* v___f_2646_, lean_object* v___f_2647_, lean_object* v_cnfHandle_2648_, lean_object* v_cnfPath_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_trimProofs_boxed_2653_; uint8_t v_binaryProofs_boxed_2654_; uint8_t v_solverMode_boxed_2655_; lean_object* v_res_2656_; 
v_trimProofs_boxed_2653_ = lean_unbox(v_trimProofs_2640_);
v_binaryProofs_boxed_2654_ = lean_unbox(v_binaryProofs_2644_);
v_solverMode_boxed_2655_ = lean_unbox(v_solverMode_2645_);
v_res_2656_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(v___f_2638_, v_lratPath_2639_, v_trimProofs_boxed_2653_, v___f_2641_, v_solver_2642_, v_timeout_2643_, v_binaryProofs_boxed_2654_, v_solverMode_boxed_2655_, v___f_2646_, v___f_2647_, v_cnfHandle_2648_, v_cnfPath_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v_cnfHandle_2648_);
lean_dec(v_timeout_2643_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object* v_cnf_2660_, lean_object* v_solver_2661_, lean_object* v_lratPath_2662_, uint8_t v_trimProofs_2663_, lean_object* v_timeout_2664_, uint8_t v_binaryProofs_2665_, uint8_t v_solverMode_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___f_2677_; lean_object* v___x_2678_; 
v___f_2670_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2670_, 0, v_cnf_2660_);
v___f_2671_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0));
v___f_2672_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1));
v___f_2673_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2));
v___x_2674_ = lean_box(v_trimProofs_2663_);
v___x_2675_ = lean_box(v_binaryProofs_2665_);
v___x_2676_ = lean_box(v_solverMode_2666_);
v___f_2677_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2677_, 0, v___f_2672_);
lean_closure_set(v___f_2677_, 1, v_lratPath_2662_);
lean_closure_set(v___f_2677_, 2, v___x_2674_);
lean_closure_set(v___f_2677_, 3, v___f_2671_);
lean_closure_set(v___f_2677_, 4, v_solver_2661_);
lean_closure_set(v___f_2677_, 5, v_timeout_2664_);
lean_closure_set(v___f_2677_, 6, v___x_2675_);
lean_closure_set(v___f_2677_, 7, v___x_2676_);
lean_closure_set(v___f_2677_, 8, v___f_2670_);
lean_closure_set(v___f_2677_, 9, v___f_2673_);
v___x_2678_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v___f_2677_, v_a_2667_, v_a_2668_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object* v_cnf_2679_, lean_object* v_solver_2680_, lean_object* v_lratPath_2681_, lean_object* v_trimProofs_2682_, lean_object* v_timeout_2683_, lean_object* v_binaryProofs_2684_, lean_object* v_solverMode_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
uint8_t v_trimProofs_boxed_2689_; uint8_t v_binaryProofs_boxed_2690_; uint8_t v_solverMode_boxed_2691_; lean_object* v_res_2692_; 
v_trimProofs_boxed_2689_ = lean_unbox(v_trimProofs_2682_);
v_binaryProofs_boxed_2690_ = lean_unbox(v_binaryProofs_2684_);
v_solverMode_boxed_2691_ = lean_unbox(v_solverMode_2685_);
v_res_2692_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(v_cnf_2679_, v_solver_2680_, v_lratPath_2681_, v_trimProofs_boxed_2689_, v_timeout_2683_, v_binaryProofs_boxed_2690_, v_solverMode_boxed_2691_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2692_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_External(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_External(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(builtin);
}
#ifdef __cplusplus
}
#endif
