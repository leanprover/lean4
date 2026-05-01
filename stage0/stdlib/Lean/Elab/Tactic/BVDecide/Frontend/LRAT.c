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
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_160_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_160_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_160_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_160_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v_traceState_121_; lean_object* v_env_122_; lean_object* v_nextMacroScope_123_; lean_object* v_ngen_124_; lean_object* v_auxDeclNGen_125_; lean_object* v_cache_126_; lean_object* v_messages_127_; lean_object* v_infoState_128_; lean_object* v_snapshotTasks_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_159_; 
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
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_159_ == 0)
{
v___x_131_ = v___x_120_;
v_isShared_132_ = v_isSharedCheck_159_;
goto v_resetjp_130_;
}
else
{
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
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_159_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
uint64_t v_tid_133_; lean_object* v_traces_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_158_; 
v_tid_133_ = lean_ctor_get_uint64(v_traceState_121_, sizeof(void*)*1);
v_traces_134_ = lean_ctor_get(v_traceState_121_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_traceState_121_);
if (v_isSharedCheck_158_ == 0)
{
v___x_136_ = v_traceState_121_;
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_traces_134_);
lean_dec(v_traceState_121_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_158_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; double v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_138_ = lean_box(0);
v___x_139_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
v___x_140_ = 0;
v___x_141_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_142_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_142_, 0, v_cls_107_);
lean_ctor_set(v___x_142_, 1, v___x_138_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
lean_ctor_set_float(v___x_142_, sizeof(void*)*3, v___x_139_);
lean_ctor_set_float(v___x_142_, sizeof(void*)*3 + 8, v___x_139_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*3 + 16, v___x_140_);
v___x_143_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_144_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v_a_116_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
lean_inc(v_ref_114_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_ref_114_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = l_Lean_PersistentArray_push___redArg(v_traces_134_, v___x_145_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_146_);
v___x_148_ = v___x_136_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_146_);
lean_ctor_set_uint64(v_reuseFailAlloc_157_, sizeof(void*)*1, v_tid_133_);
v___x_148_ = v_reuseFailAlloc_157_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_148_);
v___x_150_ = v___x_131_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_env_122_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_ngen_124_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_auxDeclNGen_125_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 5, v_cache_126_);
lean_ctor_set(v_reuseFailAlloc_156_, 6, v_messages_127_);
lean_ctor_set(v_reuseFailAlloc_156_, 7, v_infoState_128_);
lean_ctor_set(v_reuseFailAlloc_156_, 8, v_snapshotTasks_129_);
v___x_150_ = v_reuseFailAlloc_156_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_st_ref_set(v___y_112_, v___x_150_);
v___x_152_ = lean_box(0);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_152_);
v___x_154_ = v___x_118_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___boxed(lean_object* v_cls_161_, lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_161_, v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_189_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11));
v___x_190_ = l_Lean_Name_append(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__15));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object* v_lratPath_197_, lean_object* v_config_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1));
v___x_207_ = l_Lean_Elab_Term_mkAuxName(v___x_206_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3));
v___x_210_ = l_Lean_Elab_Term_mkAuxName(v___x_209_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref(v___x_210_);
v___x_212_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5));
v___x_213_ = l_Lean_Elab_Term_mkAuxName(v___x_212_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(v_a_203_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_246_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_246_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_246_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_options_225_; uint8_t v_hasTrace_226_; 
v_options_225_ = lean_ctor_get(v_a_203_, 2);
v_hasTrace_226_ = lean_ctor_get_uint8(v_options_225_, sizeof(void*)*1);
if (v_hasTrace_226_ == 0)
{
goto v___jp_220_;
}
else
{
lean_object* v_inheritedTraceOptions_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_inheritedTraceOptions_227_ = lean_ctor_get(v_a_203_, 13);
v___x_228_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_229_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_230_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_227_, v_options_225_, v___x_229_);
if (v___x_230_ == 0)
{
goto v___jp_220_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_231_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__14);
lean_inc(v_a_216_);
v___x_232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_232_, 0, v_a_216_);
v___x_233_ = l_Lean_MessageData_ofFormat(v___x_232_);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_231_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__16);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v___x_228_, v___x_236_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_dec_ref(v___x_237_);
goto v___jp_220_;
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_del_object(v___x_218_);
lean_dec(v_a_216_);
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_a_208_);
lean_dec_ref(v_config_198_);
lean_dec_ref(v_lratPath_197_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
v___jp_220_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_221_, 0, v_a_208_);
lean_ctor_set(v___x_221_, 1, v_a_211_);
lean_ctor_set(v___x_221_, 2, v_a_214_);
lean_ctor_set(v___x_221_, 3, v_a_216_);
lean_ctor_set(v___x_221_, 4, v_lratPath_197_);
lean_ctor_set(v___x_221_, 5, v_config_198_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v_a_214_);
lean_dec(v_a_211_);
lean_dec(v_a_208_);
lean_dec_ref(v_config_198_);
lean_dec_ref(v_lratPath_197_);
v_a_247_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_215_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_215_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_a_211_);
lean_dec(v_a_208_);
lean_dec_ref(v_config_198_);
lean_dec_ref(v_lratPath_197_);
v_a_255_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_213_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_213_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_a_208_);
lean_dec_ref(v_config_198_);
lean_dec_ref(v_lratPath_197_);
v_a_263_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_210_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_210_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_config_198_);
lean_dec_ref(v_lratPath_197_);
v_a_271_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_207_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_207_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object* v_lratPath_279_, lean_object* v_config_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(v_lratPath_279_, v_config_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(lean_object* v_cls_289_, lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_289_, v_msg_290_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___boxed(lean_object* v_cls_299_, lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(v_cls_299_, v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_308_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1));
v___x_317_ = l_Lean_mkConst(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_box(0);
v___x_322_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_beta_326_; 
v___x_324_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6);
v___x_325_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_beta_326_ = l_Lean_Expr_app___override(v___x_325_, v___x_324_);
return v_beta_326_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_alpha_332_; 
v___x_330_ = lean_box(0);
v___x_331_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9));
v_alpha_332_ = l_Lean_mkConst(v___x_331_, v___x_330_);
return v_alpha_332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_349_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16));
v___x_350_ = l_Lean_mkConst(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21));
v___x_358_ = l_Lean_mkConst(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_364_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24));
v___x_365_ = l_Lean_mkConst(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26(void){
_start:
{
lean_object* v_alpha_366_; lean_object* v___x_367_; lean_object* v_nil_368_; 
v_alpha_366_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_367_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_368_ = l_Lean_Expr_app___override(v___x_367_, v_alpha_366_);
return v_nil_368_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_374_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28));
v___x_375_ = l_Lean_mkConst(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30(void){
_start:
{
lean_object* v_alpha_376_; lean_object* v___x_377_; lean_object* v_cons_378_; 
v_alpha_376_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_377_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_378_ = l_Lean_Expr_app___override(v___x_377_, v_alpha_376_);
return v_cons_378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_388_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32));
v___x_389_ = l_Lean_mkConst(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_type_392_; 
v___x_390_ = lean_box(0);
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v_type_392_ = l_Lean_Expr_const___override(v___x_391_, v___x_390_);
return v_type_392_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35(void){
_start:
{
lean_object* v_type_393_; lean_object* v___x_394_; lean_object* v_nil_395_; 
v_type_393_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_394_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_395_ = l_Lean_Expr_app___override(v___x_394_, v_type_393_);
return v_nil_395_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36(void){
_start:
{
lean_object* v_type_396_; lean_object* v___x_397_; lean_object* v_cons_398_; 
v_type_396_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_397_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_398_ = l_Lean_Expr_app___override(v___x_397_, v_type_396_);
return v_cons_398_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38));
v___x_409_ = l_Lean_mkConst(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_00_u03b2Type_415_; 
v___x_413_ = lean_box(0);
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41));
v_00_u03b2Type_415_ = l_Lean_mkConst(v___x_414_, v___x_413_);
return v_00_u03b2Type_415_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45));
v___x_423_ = l_Lean_mkConst(v___x_422_, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47(void){
_start:
{
lean_object* v_alpha_424_; lean_object* v___x_425_; lean_object* v_00_u03b2Type_426_; 
v_alpha_424_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_425_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_00_u03b2Type_426_ = l_Lean_Expr_app___override(v___x_425_, v_alpha_424_);
return v_00_u03b2Type_426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_430_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48));
v___x_431_ = l_Lean_mkConst(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50(void){
_start:
{
lean_object* v_00_u03b2Type_432_; lean_object* v_alpha_433_; lean_object* v___x_434_; lean_object* v_type_435_; 
v_00_u03b2Type_432_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47);
v_alpha_433_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_434_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49);
v_type_435_ = l_Lean_mkAppB(v___x_434_, v_alpha_433_, v_00_u03b2Type_432_);
return v_type_435_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51(void){
_start:
{
lean_object* v_type_436_; lean_object* v___x_437_; lean_object* v_nil_438_; 
v_type_436_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_437_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_438_ = l_Lean_Expr_app___override(v___x_437_, v_type_436_);
return v_nil_438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52(void){
_start:
{
lean_object* v_type_439_; lean_object* v___x_440_; lean_object* v_cons_441_; 
v_type_439_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_440_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_441_ = l_Lean_Expr_app___override(v___x_440_, v_type_439_);
return v_cons_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54));
v___x_448_ = l_Lean_mkConst(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_465_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60));
v___x_466_ = l_Lean_mkConst(v___x_465_, v___x_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object* v___x_467_, lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v_action_470_){
_start:
{
lean_object* v_beta_471_; lean_object* v_alpha_472_; 
v_beta_471_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7);
v_alpha_472_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
switch(lean_obj_tag(v_action_470_))
{
case 0:
{
lean_object* v_id_473_; lean_object* v_rupHints_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_nil_478_; lean_object* v_cons_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
v_id_473_ = lean_ctor_get(v_action_470_, 0);
lean_inc(v_id_473_);
v_rupHints_474_ = lean_ctor_get(v_action_470_, 1);
lean_inc_ref(v_rupHints_474_);
lean_dec_ref(v_action_470_);
v___x_475_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18);
v___x_476_ = l_Lean_mkNatLit(v_id_473_);
v___x_477_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_479_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_480_ = lean_array_to_list(v_rupHints_474_);
v___x_481_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_467_, v_nil_478_, v_cons_479_, v___x_480_);
v___x_482_ = l_Lean_mkAppB(v___x_477_, v_alpha_472_, v___x_481_);
v___x_483_ = l_Lean_mkApp4(v___x_475_, v_beta_471_, v_alpha_472_, v___x_476_, v___x_482_);
return v___x_483_;
}
case 1:
{
lean_object* v_id_484_; lean_object* v_c_485_; lean_object* v_rupHints_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_type_489_; lean_object* v___x_490_; lean_object* v_nil_491_; lean_object* v_cons_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_nil_496_; lean_object* v_cons_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v___x_469_);
v_id_484_ = lean_ctor_get(v_action_470_, 0);
lean_inc(v_id_484_);
v_c_485_ = lean_ctor_get(v_action_470_, 1);
lean_inc(v_c_485_);
v_rupHints_486_ = lean_ctor_get(v_action_470_, 2);
lean_inc_ref(v_rupHints_486_);
lean_dec_ref(v_action_470_);
v___x_487_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33);
v___x_488_ = l_Lean_mkNatLit(v_id_484_);
v_type_489_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_490_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_491_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_492_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_493_ = lean_array_to_list(v_c_485_);
v___x_494_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_491_, v_cons_492_, v___x_493_);
v___x_495_ = l_Lean_mkAppB(v___x_490_, v_type_489_, v___x_494_);
v_nil_496_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_497_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_498_ = lean_array_to_list(v_rupHints_486_);
v___x_499_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_467_, v_nil_496_, v_cons_497_, v___x_498_);
v___x_500_ = l_Lean_mkAppB(v___x_490_, v_alpha_472_, v___x_499_);
v___x_501_ = l_Lean_mkApp5(v___x_487_, v_beta_471_, v_alpha_472_, v___x_488_, v___x_495_, v___x_500_);
return v___x_501_;
}
case 2:
{
lean_object* v_id_502_; lean_object* v_c_503_; lean_object* v_pivot_504_; lean_object* v_rupHints_505_; lean_object* v_ratHints_506_; lean_object* v___x_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v_type_510_; lean_object* v_nil_511_; lean_object* v_cons_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_00_u03b2Type_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___y_522_; uint8_t v___x_536_; 
v_id_502_ = lean_ctor_get(v_action_470_, 0);
lean_inc(v_id_502_);
v_c_503_ = lean_ctor_get(v_action_470_, 1);
lean_inc(v_c_503_);
v_pivot_504_ = lean_ctor_get(v_action_470_, 2);
lean_inc_ref(v_pivot_504_);
v_rupHints_505_ = lean_ctor_get(v_action_470_, 3);
lean_inc_ref(v_rupHints_505_);
v_ratHints_506_ = lean_ctor_get(v_action_470_, 4);
lean_inc_ref(v_ratHints_506_);
lean_dec_ref(v_action_470_);
v___x_507_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_fst_508_ = lean_ctor_get(v_pivot_504_, 0);
lean_inc(v_fst_508_);
v_snd_509_ = lean_ctor_get(v_pivot_504_, 1);
lean_inc(v_snd_509_);
lean_dec_ref(v_pivot_504_);
v_type_510_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v_nil_511_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_512_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_513_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39);
v___x_514_ = l_Lean_mkNatLit(v_id_502_);
v___x_515_ = lean_array_to_list(v_c_503_);
v___x_516_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_468_, v_nil_511_, v_cons_512_, v___x_515_);
v___x_517_ = l_Lean_mkAppB(v___x_507_, v_type_510_, v___x_516_);
v_00_u03b2Type_518_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42);
v___x_519_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46);
v___x_520_ = l_Lean_mkNatLit(v_fst_508_);
v___x_536_ = lean_unbox(v_snd_509_);
lean_dec(v_snd_509_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55);
v___y_522_ = v___x_537_;
goto v___jp_521_;
}
else
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58);
v___y_522_ = v___x_538_;
goto v___jp_521_;
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v_nil_524_; lean_object* v_cons_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_type_529_; lean_object* v_nil_530_; lean_object* v_cons_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc_ref(v___y_522_);
v___x_523_ = l_Lean_mkApp4(v___x_519_, v_alpha_472_, v_00_u03b2Type_518_, v___x_520_, v___y_522_);
v_nil_524_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_525_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_526_ = lean_array_to_list(v_rupHints_505_);
v___x_527_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_467_, v_nil_524_, v_cons_525_, v___x_526_);
v___x_528_ = l_Lean_mkAppB(v___x_507_, v_alpha_472_, v___x_527_);
v_type_529_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v_nil_530_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51);
v_cons_531_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52);
v___x_532_ = lean_array_to_list(v_ratHints_506_);
v___x_533_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_469_, v_nil_530_, v_cons_531_, v___x_532_);
v___x_534_ = l_Lean_mkAppB(v___x_507_, v_type_529_, v___x_533_);
v___x_535_ = l_Lean_mkApp7(v___x_513_, v_beta_471_, v_alpha_472_, v___x_514_, v___x_517_, v___x_523_, v___x_528_, v___x_534_);
return v___x_535_;
}
}
default: 
{
lean_object* v_ids_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_nil_542_; lean_object* v_cons_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
v_ids_539_ = lean_ctor_get(v_action_470_, 0);
lean_inc_ref(v_ids_539_);
lean_dec_ref(v_action_470_);
v___x_540_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61);
v___x_541_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_542_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_543_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_544_ = lean_array_to_list(v_ids_539_);
v___x_545_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_467_, v_nil_542_, v_cons_543_, v___x_544_);
v___x_546_ = l_Lean_mkAppB(v___x_541_, v_alpha_472_, v___x_545_);
v___x_547_ = l_Lean_mkApp3(v___x_540_, v_beta_471_, v_alpha_472_, v___x_546_);
return v___x_547_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = l_Lean_instToExprNat;
v___x_549_ = lean_box(0);
v___x_550_ = l_Lean_instToExprArrayOfToLevel___redArg(v___x_549_, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0);
v___x_552_ = l_Lean_instToExprNat;
v___x_553_ = lean_box(0);
v___x_554_ = l_Lean_instToExprProdOfToLevel___redArg(v___x_553_, v___x_553_, v___x_552_, v___x_551_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___f_558_; 
v___x_555_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1);
v___x_556_ = l_Lean_instToExprInt;
v___x_557_ = l_Lean_instToExprNat;
v___f_558_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0), 4, 3);
lean_closure_set(v___f_558_, 0, v___x_557_);
lean_closure_set(v___f_558_, 1, v___x_556_);
lean_closure_set(v___f_558_, 2, v___x_555_);
return v___f_558_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_box(0);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4));
v___x_568_ = l_Lean_mkConst(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6(void){
_start:
{
lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v___x_569_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5);
v___f_570_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___f_570_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__0);
v___x_581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_577_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_ctor_set_usize(v___x_581_, 4, v___x_576_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v_traceState_585_; lean_object* v_traces_586_; lean_object* v___x_587_; lean_object* v_traceState_588_; lean_object* v_env_589_; lean_object* v_nextMacroScope_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_cache_593_; lean_object* v_messages_594_; lean_object* v_infoState_595_; lean_object* v_snapshotTasks_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_615_; 
v___x_584_ = lean_st_ref_get(v___y_582_);
v_traceState_585_ = lean_ctor_get(v___x_584_, 4);
lean_inc_ref(v_traceState_585_);
lean_dec(v___x_584_);
v_traces_586_ = lean_ctor_get(v_traceState_585_, 0);
lean_inc_ref(v_traces_586_);
lean_dec_ref(v_traceState_585_);
v___x_587_ = lean_st_ref_take(v___y_582_);
v_traceState_588_ = lean_ctor_get(v___x_587_, 4);
v_env_589_ = lean_ctor_get(v___x_587_, 0);
v_nextMacroScope_590_ = lean_ctor_get(v___x_587_, 1);
v_ngen_591_ = lean_ctor_get(v___x_587_, 2);
v_auxDeclNGen_592_ = lean_ctor_get(v___x_587_, 3);
v_cache_593_ = lean_ctor_get(v___x_587_, 5);
v_messages_594_ = lean_ctor_get(v___x_587_, 6);
v_infoState_595_ = lean_ctor_get(v___x_587_, 7);
v_snapshotTasks_596_ = lean_ctor_get(v___x_587_, 8);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_615_ == 0)
{
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_615_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snapshotTasks_596_);
lean_inc(v_infoState_595_);
lean_inc(v_messages_594_);
lean_inc(v_cache_593_);
lean_inc(v_traceState_588_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_env_589_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_615_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint64_t v_tid_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_613_; 
v_tid_600_ = lean_ctor_get_uint64(v_traceState_588_, sizeof(void*)*1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_traceState_588_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_traceState_588_, 0);
lean_dec(v_unused_614_);
v___x_602_ = v_traceState_588_;
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
else
{
lean_dec(v_traceState_588_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___closed__1);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set_uint64(v_reuseFailAlloc_612_, sizeof(void*)*1, v_tid_600_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 4, v___x_606_);
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_env_589_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_messages_594_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_infoState_595_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_snapshotTasks_596_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_st_ref_set(v___y_582_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_traces_586_);
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg___boxed(lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_616_);
lean_dec(v___y_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(lean_object* v_opts_627_, lean_object* v_opt_628_){
_start:
{
lean_object* v_name_629_; lean_object* v_defValue_630_; lean_object* v_map_631_; lean_object* v___x_632_; 
v_name_629_ = lean_ctor_get(v_opt_628_, 0);
v_defValue_630_ = lean_ctor_get(v_opt_628_, 1);
v_map_631_ = lean_ctor_get(v_opts_627_, 0);
v___x_632_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_631_, v_name_629_);
if (lean_obj_tag(v___x_632_) == 0)
{
uint8_t v___x_633_; 
v___x_633_ = lean_unbox(v_defValue_630_);
return v___x_633_;
}
else
{
lean_object* v_val_634_; 
v_val_634_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_634_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v_val_634_) == 1)
{
uint8_t v_v_635_; 
v_v_635_ = lean_ctor_get_uint8(v_val_634_, 0);
lean_dec_ref(v_val_634_);
return v_v_635_;
}
else
{
uint8_t v___x_636_; 
lean_dec(v_val_634_);
v___x_636_ = lean_unbox(v_defValue_630_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___boxed(lean_object* v_opts_637_, lean_object* v_opt_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_637_, v_opt_638_);
lean_dec_ref(v_opt_638_);
lean_dec_ref(v_opts_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(lean_object* v_e_641_){
_start:
{
if (lean_obj_tag(v_e_641_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_a_643_ = lean_ctor_get(v_e_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_e_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_e_641_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v_e_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_mk_io_user_error(v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 1);
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v_e_641_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_e_641_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v_e_641_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v_e_641_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg___boxed(lean_object* v_e_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_e_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(lean_object* v_00_u03b1_663_, lean_object* v_e_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_e_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___boxed(lean_object* v_00_u03b1_667_, lean_object* v_e_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_00_u03b1_667_, v_e_668_);
return v_res_670_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1));
v___x_675_ = l_Lean_MessageData_ofFormat(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(v_x_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v_x_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object* v_a_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_a_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object* v_a_693_, lean_object* v_x_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(v_a_693_, v_x_694_);
lean_dec_ref(v_a_693_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1));
v___x_700_ = l_Lean_MessageData_ofFormat(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(v_x_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_x_707_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_712_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
lean_ctor_set(v___x_717_, 4, v___x_715_);
lean_ctor_set(v___x_717_, 5, v___x_715_);
lean_ctor_set(v___x_717_, 6, v___x_715_);
lean_ctor_set(v___x_717_, 7, v___x_715_);
lean_ctor_set(v___x_717_, 8, v___x_715_);
lean_ctor_set(v___x_717_, 9, v___x_715_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(32u);
v___x_719_ = lean_mk_empty_array_with_capacity(v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = ((size_t)5ULL);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_unsigned_to_nat(32u);
v___x_724_ = lean_mk_empty_array_with_capacity(v___x_723_);
v___x_725_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__3);
v___x_726_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_722_);
lean_ctor_set(v___x_726_, 3, v___x_722_);
lean_ctor_set_usize(v___x_726_, 4, v___x_721_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_box(1);
v___x_728_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__4);
v___x_729_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__1);
v___x_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(lean_object* v_msgData_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v_env_736_; lean_object* v_options_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_735_ = lean_st_ref_get(v___y_733_);
v_env_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc_ref(v_env_736_);
lean_dec(v___x_735_);
v_options_737_ = lean_ctor_get(v___y_732_, 2);
v___x_738_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__2);
v___x_739_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_737_);
v___x_740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_740_, 0, v_env_736_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
lean_ctor_set(v___x_740_, 3, v_options_737_);
v___x_741_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_msgData_731_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0___boxed(lean_object* v_msgData_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msgData_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(size_t v_sz_748_, size_t v_i_749_, lean_object* v_bs_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_751_ == 0)
{
return v_bs_750_;
}
else
{
lean_object* v_v_752_; lean_object* v_msg_753_; lean_object* v___x_754_; lean_object* v_bs_x27_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_v_752_ = lean_array_uget_borrowed(v_bs_750_, v_i_749_);
v_msg_753_ = lean_ctor_get(v_v_752_, 1);
lean_inc_ref(v_msg_753_);
v___x_754_ = lean_unsigned_to_nat(0u);
v_bs_x27_755_ = lean_array_uset(v_bs_750_, v_i_749_, v___x_754_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_749_, v___x_756_);
v___x_758_ = lean_array_uset(v_bs_x27_755_, v_i_749_, v_msg_753_);
v_i_749_ = v___x_757_;
v_bs_750_ = v___x_758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(lean_object* v_oldTraces_766_, lean_object* v_data_767_, lean_object* v_ref_768_, lean_object* v_msg_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_fileName_773_; lean_object* v_fileMap_774_; lean_object* v_options_775_; lean_object* v_currRecDepth_776_; lean_object* v_maxRecDepth_777_; lean_object* v_ref_778_; lean_object* v_currNamespace_779_; lean_object* v_openDecls_780_; lean_object* v_initHeartbeats_781_; lean_object* v_maxHeartbeats_782_; lean_object* v_quotContext_783_; lean_object* v_currMacroScope_784_; uint8_t v_diag_785_; lean_object* v_cancelTk_x3f_786_; uint8_t v_suppressElabErrors_787_; lean_object* v_inheritedTraceOptions_788_; lean_object* v___x_789_; lean_object* v_traceState_790_; lean_object* v_traces_791_; lean_object* v_ref_792_; lean_object* v___x_793_; lean_object* v___x_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v_msg_798_; lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_837_; 
v_fileName_773_ = lean_ctor_get(v___y_770_, 0);
v_fileMap_774_ = lean_ctor_get(v___y_770_, 1);
v_options_775_ = lean_ctor_get(v___y_770_, 2);
v_currRecDepth_776_ = lean_ctor_get(v___y_770_, 3);
v_maxRecDepth_777_ = lean_ctor_get(v___y_770_, 4);
v_ref_778_ = lean_ctor_get(v___y_770_, 5);
v_currNamespace_779_ = lean_ctor_get(v___y_770_, 6);
v_openDecls_780_ = lean_ctor_get(v___y_770_, 7);
v_initHeartbeats_781_ = lean_ctor_get(v___y_770_, 8);
v_maxHeartbeats_782_ = lean_ctor_get(v___y_770_, 9);
v_quotContext_783_ = lean_ctor_get(v___y_770_, 10);
v_currMacroScope_784_ = lean_ctor_get(v___y_770_, 11);
v_diag_785_ = lean_ctor_get_uint8(v___y_770_, sizeof(void*)*14);
v_cancelTk_x3f_786_ = lean_ctor_get(v___y_770_, 12);
v_suppressElabErrors_787_ = lean_ctor_get_uint8(v___y_770_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_788_ = lean_ctor_get(v___y_770_, 13);
v___x_789_ = lean_st_ref_get(v___y_771_);
v_traceState_790_ = lean_ctor_get(v___x_789_, 4);
lean_inc_ref(v_traceState_790_);
lean_dec(v___x_789_);
v_traces_791_ = lean_ctor_get(v_traceState_790_, 0);
lean_inc_ref(v_traces_791_);
lean_dec_ref(v_traceState_790_);
v_ref_792_ = l_Lean_replaceRef(v_ref_768_, v_ref_778_);
lean_inc_ref(v_inheritedTraceOptions_788_);
lean_inc(v_cancelTk_x3f_786_);
lean_inc(v_currMacroScope_784_);
lean_inc(v_quotContext_783_);
lean_inc(v_maxHeartbeats_782_);
lean_inc(v_initHeartbeats_781_);
lean_inc(v_openDecls_780_);
lean_inc(v_currNamespace_779_);
lean_inc(v_maxRecDepth_777_);
lean_inc(v_currRecDepth_776_);
lean_inc_ref(v_options_775_);
lean_inc_ref(v_fileMap_774_);
lean_inc_ref(v_fileName_773_);
v___x_793_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_793_, 0, v_fileName_773_);
lean_ctor_set(v___x_793_, 1, v_fileMap_774_);
lean_ctor_set(v___x_793_, 2, v_options_775_);
lean_ctor_set(v___x_793_, 3, v_currRecDepth_776_);
lean_ctor_set(v___x_793_, 4, v_maxRecDepth_777_);
lean_ctor_set(v___x_793_, 5, v_ref_792_);
lean_ctor_set(v___x_793_, 6, v_currNamespace_779_);
lean_ctor_set(v___x_793_, 7, v_openDecls_780_);
lean_ctor_set(v___x_793_, 8, v_initHeartbeats_781_);
lean_ctor_set(v___x_793_, 9, v_maxHeartbeats_782_);
lean_ctor_set(v___x_793_, 10, v_quotContext_783_);
lean_ctor_set(v___x_793_, 11, v_currMacroScope_784_);
lean_ctor_set(v___x_793_, 12, v_cancelTk_x3f_786_);
lean_ctor_set(v___x_793_, 13, v_inheritedTraceOptions_788_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*14, v_diag_785_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*14 + 1, v_suppressElabErrors_787_);
v___x_794_ = l_Lean_PersistentArray_toArray___redArg(v_traces_791_);
lean_dec_ref(v_traces_791_);
v_sz_795_ = lean_array_size(v___x_794_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5_spec__7(v_sz_795_, v___x_796_, v___x_794_);
v_msg_798_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_798_, 0, v_data_767_);
lean_ctor_set(v_msg_798_, 1, v_msg_769_);
lean_ctor_set(v_msg_798_, 2, v___x_797_);
v___x_799_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_798_, v___x_793_, v___y_771_);
lean_dec_ref(v___x_793_);
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_837_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_837_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_837_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v_traceState_805_; lean_object* v_env_806_; lean_object* v_nextMacroScope_807_; lean_object* v_ngen_808_; lean_object* v_auxDeclNGen_809_; lean_object* v_cache_810_; lean_object* v_messages_811_; lean_object* v_infoState_812_; lean_object* v_snapshotTasks_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_836_; 
v___x_804_ = lean_st_ref_take(v___y_771_);
v_traceState_805_ = lean_ctor_get(v___x_804_, 4);
v_env_806_ = lean_ctor_get(v___x_804_, 0);
v_nextMacroScope_807_ = lean_ctor_get(v___x_804_, 1);
v_ngen_808_ = lean_ctor_get(v___x_804_, 2);
v_auxDeclNGen_809_ = lean_ctor_get(v___x_804_, 3);
v_cache_810_ = lean_ctor_get(v___x_804_, 5);
v_messages_811_ = lean_ctor_get(v___x_804_, 6);
v_infoState_812_ = lean_ctor_get(v___x_804_, 7);
v_snapshotTasks_813_ = lean_ctor_get(v___x_804_, 8);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_836_ == 0)
{
v___x_815_ = v___x_804_;
v_isShared_816_ = v_isSharedCheck_836_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_snapshotTasks_813_);
lean_inc(v_infoState_812_);
lean_inc(v_messages_811_);
lean_inc(v_cache_810_);
lean_inc(v_traceState_805_);
lean_inc(v_auxDeclNGen_809_);
lean_inc(v_ngen_808_);
lean_inc(v_nextMacroScope_807_);
lean_inc(v_env_806_);
lean_dec(v___x_804_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_836_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint64_t v_tid_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_834_; 
v_tid_817_ = lean_ctor_get_uint64(v_traceState_805_, sizeof(void*)*1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_traceState_805_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_traceState_805_, 0);
lean_dec(v_unused_835_);
v___x_819_ = v_traceState_805_;
v_isShared_820_ = v_isSharedCheck_834_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_traceState_805_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_834_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_ref_768_);
lean_ctor_set(v___x_821_, 1, v_a_800_);
v___x_822_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_766_, v___x_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_822_);
lean_ctor_set_uint64(v_reuseFailAlloc_833_, sizeof(void*)*1, v_tid_817_);
v___x_824_ = v_reuseFailAlloc_833_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v___x_824_);
v___x_826_ = v___x_815_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_env_806_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_807_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_808_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_809_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_cache_810_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_messages_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_infoState_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_snapshotTasks_813_);
v___x_826_ = v_reuseFailAlloc_832_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_st_ref_set(v___y_771_, v___x_826_);
v___x_828_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_828_);
v___x_830_ = v___x_802_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5___boxed(lean_object* v_oldTraces_838_, lean_object* v_data_839_, lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_838_, v_data_839_, v_ref_840_, v_msg_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(lean_object* v_e_846_){
_start:
{
if (lean_obj_tag(v_e_846_) == 0)
{
uint8_t v___x_847_; 
v___x_847_ = 2;
return v___x_847_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4___boxed(lean_object* v_e_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(v_e_849_);
lean_dec_ref(v_e_849_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(lean_object* v_opts_852_, lean_object* v_opt_853_){
_start:
{
lean_object* v_name_854_; lean_object* v_defValue_855_; lean_object* v_map_856_; lean_object* v___x_857_; 
v_name_854_ = lean_ctor_get(v_opt_853_, 0);
v_defValue_855_ = lean_ctor_get(v_opt_853_, 1);
v_map_856_ = lean_ctor_get(v_opts_852_, 0);
v___x_857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_856_, v_name_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_inc(v_defValue_855_);
return v_defValue_855_;
}
else
{
lean_object* v_val_858_; 
v_val_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref(v___x_857_);
if (lean_obj_tag(v_val_858_) == 3)
{
lean_object* v_v_859_; 
v_v_859_ = lean_ctor_get(v_val_858_, 0);
lean_inc(v_v_859_);
lean_dec_ref(v_val_858_);
return v_v_859_;
}
else
{
lean_dec(v_val_858_);
lean_inc(v_defValue_855_);
return v_defValue_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7___boxed(lean_object* v_opts_860_, lean_object* v_opt_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_860_, v_opt_861_);
lean_dec_ref(v_opt_861_);
lean_dec_ref(v_opts_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v_x_863_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v_x_863_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v_x_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 1);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v_x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v_x_863_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_x_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 0);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg___boxed(lean_object* v_x_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_x_881_);
return v_res_883_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__0));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__2));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4(void){
_start:
{
lean_object* v___x_890_; double v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(1000u);
v___x_891_ = lean_float_of_nat(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(lean_object* v_cls_892_, uint8_t v_collapsed_893_, lean_object* v_tag_894_, lean_object* v_opts_895_, uint8_t v_clsEnabled_896_, lean_object* v_oldTraces_897_, lean_object* v_msg_898_, lean_object* v_resStartStop_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_1002_; 
v_fst_903_ = lean_ctor_get(v_resStartStop_899_, 0);
v_snd_904_ = lean_ctor_get(v_resStartStop_899_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_resStartStop_899_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_906_ = v_resStartStop_899_;
v_isShared_907_ = v_isSharedCheck_1002_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
lean_dec(v_resStartStop_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_1002_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v_data_911_; lean_object* v_fst_922_; lean_object* v_snd_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1001_; 
v_fst_922_ = lean_ctor_get(v_snd_904_, 0);
v_snd_923_ = lean_ctor_get(v_snd_904_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_snd_904_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_925_ = v_snd_904_;
v_isShared_926_ = v_isSharedCheck_1001_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snd_923_);
lean_inc(v_fst_922_);
lean_dec(v_snd_904_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1001_;
goto v_resetjp_924_;
}
v___jp_908_:
{
lean_object* v___x_912_; 
lean_inc(v___y_910_);
v___x_912_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_897_, v_data_911_, v___y_910_, v___y_909_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; 
lean_dec_ref(v___x_912_);
v___x_913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_903_);
return v___x_913_;
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_fst_903_);
v_a_914_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_912_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_912_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
v_resetjp_924_:
{
lean_object* v___x_927_; uint8_t v___x_928_; lean_object* v___y_930_; lean_object* v_a_931_; uint8_t v___y_955_; double v___y_986_; 
v___x_927_ = l_Lean_trace_profiler;
v___x_928_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_895_, v___x_927_);
if (v___x_928_ == 0)
{
v___y_955_ = v___x_928_;
goto v___jp_954_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_trace_profiler_useHeartbeats;
v___x_992_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_895_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; double v___x_995_; double v___x_996_; double v___x_997_; 
v___x_993_ = l_Lean_trace_profiler_threshold;
v___x_994_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_895_, v___x_993_);
v___x_995_ = lean_float_of_nat(v___x_994_);
v___x_996_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_997_ = lean_float_div(v___x_995_, v___x_996_);
v___y_986_ = v___x_997_;
goto v___jp_985_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; double v___x_1000_; 
v___x_998_ = l_Lean_trace_profiler_threshold;
v___x_999_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_895_, v___x_998_);
v___x_1000_ = lean_float_of_nat(v___x_999_);
v___y_986_ = v___x_1000_;
goto v___jp_985_;
}
}
v___jp_929_:
{
uint8_t v_result_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v_result_932_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__4(v_fst_903_);
v___x_933_ = l_Lean_TraceResult_toEmoji(v_result_932_);
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
v___x_935_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 7);
lean_ctor_set(v___x_925_, 1, v___x_935_);
lean_ctor_set(v___x_925_, 0, v___x_934_);
v___x_937_ = v___x_925_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_935_);
v___x_937_ = v_reuseFailAlloc_948_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v_m_939_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 7);
lean_ctor_set(v___x_906_, 1, v_a_931_);
lean_ctor_set(v___x_906_, 0, v___x_937_);
v_m_939_ = v___x_906_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_a_931_);
v_m_939_ = v_reuseFailAlloc_947_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; double v___x_942_; lean_object* v_data_943_; 
v___x_940_ = lean_box(v_result_932_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
v___x_942_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_894_);
lean_inc_ref(v___x_941_);
lean_inc(v_cls_892_);
v_data_943_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_943_, 0, v_cls_892_);
lean_ctor_set(v_data_943_, 1, v___x_941_);
lean_ctor_set(v_data_943_, 2, v_tag_894_);
lean_ctor_set_float(v_data_943_, sizeof(void*)*3, v___x_942_);
lean_ctor_set_float(v_data_943_, sizeof(void*)*3 + 8, v___x_942_);
lean_ctor_set_uint8(v_data_943_, sizeof(void*)*3 + 16, v_collapsed_893_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_941_);
lean_dec(v_snd_923_);
lean_dec(v_fst_922_);
lean_dec_ref(v_tag_894_);
lean_dec(v_cls_892_);
v___y_909_ = v_m_939_;
v___y_910_ = v___y_930_;
v_data_911_ = v_data_943_;
goto v___jp_908_;
}
else
{
lean_object* v_data_944_; double v___x_945_; double v___x_946_; 
lean_dec_ref(v_data_943_);
v_data_944_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_944_, 0, v_cls_892_);
lean_ctor_set(v_data_944_, 1, v___x_941_);
lean_ctor_set(v_data_944_, 2, v_tag_894_);
v___x_945_ = lean_unbox_float(v_fst_922_);
lean_dec(v_fst_922_);
lean_ctor_set_float(v_data_944_, sizeof(void*)*3, v___x_945_);
v___x_946_ = lean_unbox_float(v_snd_923_);
lean_dec(v_snd_923_);
lean_ctor_set_float(v_data_944_, sizeof(void*)*3 + 8, v___x_946_);
lean_ctor_set_uint8(v_data_944_, sizeof(void*)*3 + 16, v_collapsed_893_);
v___y_909_ = v_m_939_;
v___y_910_ = v___y_930_;
v_data_911_ = v_data_944_;
goto v___jp_908_;
}
}
}
}
v___jp_949_:
{
lean_object* v_ref_950_; lean_object* v___x_951_; 
v_ref_950_ = lean_ctor_get(v___y_900_, 5);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v_fst_903_);
v___x_951_ = lean_apply_4(v_msg_898_, v_fst_903_, v___y_900_, v___y_901_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___x_951_);
v___y_930_ = v_ref_950_;
v_a_931_ = v_a_952_;
goto v___jp_929_;
}
else
{
lean_object* v___x_953_; 
lean_dec_ref(v___x_951_);
v___x_953_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_930_ = v_ref_950_;
v_a_931_ = v___x_953_;
goto v___jp_929_;
}
}
v___jp_954_:
{
if (v_clsEnabled_896_ == 0)
{
if (v___y_955_ == 0)
{
lean_object* v___x_956_; lean_object* v_traceState_957_; lean_object* v_env_958_; lean_object* v_nextMacroScope_959_; lean_object* v_ngen_960_; lean_object* v_auxDeclNGen_961_; lean_object* v_cache_962_; lean_object* v_messages_963_; lean_object* v_infoState_964_; lean_object* v_snapshotTasks_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_984_; 
lean_del_object(v___x_925_);
lean_dec(v_snd_923_);
lean_dec(v_fst_922_);
lean_del_object(v___x_906_);
lean_dec_ref(v_msg_898_);
lean_dec_ref(v_tag_894_);
lean_dec(v_cls_892_);
v___x_956_ = lean_st_ref_take(v___y_901_);
v_traceState_957_ = lean_ctor_get(v___x_956_, 4);
v_env_958_ = lean_ctor_get(v___x_956_, 0);
v_nextMacroScope_959_ = lean_ctor_get(v___x_956_, 1);
v_ngen_960_ = lean_ctor_get(v___x_956_, 2);
v_auxDeclNGen_961_ = lean_ctor_get(v___x_956_, 3);
v_cache_962_ = lean_ctor_get(v___x_956_, 5);
v_messages_963_ = lean_ctor_get(v___x_956_, 6);
v_infoState_964_ = lean_ctor_get(v___x_956_, 7);
v_snapshotTasks_965_ = lean_ctor_get(v___x_956_, 8);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_984_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_984_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_snapshotTasks_965_);
lean_inc(v_infoState_964_);
lean_inc(v_messages_963_);
lean_inc(v_cache_962_);
lean_inc(v_traceState_957_);
lean_inc(v_auxDeclNGen_961_);
lean_inc(v_ngen_960_);
lean_inc(v_nextMacroScope_959_);
lean_inc(v_env_958_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_984_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint64_t v_tid_969_; lean_object* v_traces_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_983_; 
v_tid_969_ = lean_ctor_get_uint64(v_traceState_957_, sizeof(void*)*1);
v_traces_970_ = lean_ctor_get(v_traceState_957_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_traceState_957_);
if (v_isSharedCheck_983_ == 0)
{
v___x_972_ = v_traceState_957_;
v_isShared_973_ = v_isSharedCheck_983_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_traces_970_);
lean_dec(v_traceState_957_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_983_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_897_, v_traces_970_);
lean_dec_ref(v_traces_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_974_);
lean_ctor_set_uint64(v_reuseFailAlloc_982_, sizeof(void*)*1, v_tid_969_);
v___x_976_ = v_reuseFailAlloc_982_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___x_976_);
v___x_978_ = v___x_967_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_env_958_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_nextMacroScope_959_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_ngen_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_auxDeclNGen_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_cache_962_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_messages_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_infoState_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_snapshotTasks_965_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_st_ref_set(v___y_901_, v___x_978_);
v___x_980_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_903_);
return v___x_980_;
}
}
}
}
}
else
{
goto v___jp_949_;
}
}
else
{
goto v___jp_949_;
}
}
v___jp_985_:
{
double v___x_987_; double v___x_988_; double v___x_989_; uint8_t v___x_990_; 
v___x_987_ = lean_unbox_float(v_snd_923_);
v___x_988_ = lean_unbox_float(v_fst_922_);
v___x_989_ = lean_float_sub(v___x_987_, v___x_988_);
v___x_990_ = lean_float_decLt(v___y_986_, v___x_989_);
v___y_955_ = v___x_990_;
goto v___jp_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___boxed(lean_object* v_cls_1003_, lean_object* v_collapsed_1004_, lean_object* v_tag_1005_, lean_object* v_opts_1006_, lean_object* v_clsEnabled_1007_, lean_object* v_oldTraces_1008_, lean_object* v_msg_1009_, lean_object* v_resStartStop_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v_collapsed_boxed_1014_; uint8_t v_clsEnabled_boxed_1015_; lean_object* v_res_1016_; 
v_collapsed_boxed_1014_ = lean_unbox(v_collapsed_1004_);
v_clsEnabled_boxed_1015_ = lean_unbox(v_clsEnabled_1007_);
v_res_1016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v_cls_1003_, v_collapsed_boxed_1014_, v_tag_1005_, v_opts_1006_, v_clsEnabled_boxed_1015_, v_oldTraces_1008_, v_msg_1009_, v_resStartStop_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec_ref(v_opts_1006_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(lean_object* v_cls_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_ref_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1068_; 
v_ref_1022_ = lean_ctor_get(v___y_1019_, 5);
v___x_1023_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_1018_, v___y_1019_, v___y_1020_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1068_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1068_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v_traceState_1029_; lean_object* v_env_1030_; lean_object* v_nextMacroScope_1031_; lean_object* v_ngen_1032_; lean_object* v_auxDeclNGen_1033_; lean_object* v_cache_1034_; lean_object* v_messages_1035_; lean_object* v_infoState_1036_; lean_object* v_snapshotTasks_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1067_; 
v___x_1028_ = lean_st_ref_take(v___y_1020_);
v_traceState_1029_ = lean_ctor_get(v___x_1028_, 4);
v_env_1030_ = lean_ctor_get(v___x_1028_, 0);
v_nextMacroScope_1031_ = lean_ctor_get(v___x_1028_, 1);
v_ngen_1032_ = lean_ctor_get(v___x_1028_, 2);
v_auxDeclNGen_1033_ = lean_ctor_get(v___x_1028_, 3);
v_cache_1034_ = lean_ctor_get(v___x_1028_, 5);
v_messages_1035_ = lean_ctor_get(v___x_1028_, 6);
v_infoState_1036_ = lean_ctor_get(v___x_1028_, 7);
v_snapshotTasks_1037_ = lean_ctor_get(v___x_1028_, 8);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1039_ = v___x_1028_;
v_isShared_1040_ = v_isSharedCheck_1067_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snapshotTasks_1037_);
lean_inc(v_infoState_1036_);
lean_inc(v_messages_1035_);
lean_inc(v_cache_1034_);
lean_inc(v_traceState_1029_);
lean_inc(v_auxDeclNGen_1033_);
lean_inc(v_ngen_1032_);
lean_inc(v_nextMacroScope_1031_);
lean_inc(v_env_1030_);
lean_dec(v___x_1028_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1067_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint64_t v_tid_1041_; lean_object* v_traces_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1066_; 
v_tid_1041_ = lean_ctor_get_uint64(v_traceState_1029_, sizeof(void*)*1);
v_traces_1042_ = lean_ctor_get(v_traceState_1029_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_traceState_1029_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1044_ = v_traceState_1029_;
v_isShared_1045_ = v_isSharedCheck_1066_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_traces_1042_);
lean_dec(v_traceState_1029_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1066_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; double v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
v___x_1048_ = 0;
v___x_1049_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_1050_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1050_, 0, v_cls_1017_);
lean_ctor_set(v___x_1050_, 1, v___x_1046_);
lean_ctor_set(v___x_1050_, 2, v___x_1049_);
lean_ctor_set_float(v___x_1050_, sizeof(void*)*3, v___x_1047_);
lean_ctor_set_float(v___x_1050_, sizeof(void*)*3 + 8, v___x_1047_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*3 + 16, v___x_1048_);
v___x_1051_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_1052_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v_a_1024_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
lean_inc(v_ref_1022_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_ref_1022_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_PersistentArray_push___redArg(v_traces_1042_, v___x_1053_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1054_);
v___x_1056_ = v___x_1044_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1054_);
lean_ctor_set_uint64(v_reuseFailAlloc_1065_, sizeof(void*)*1, v_tid_1041_);
v___x_1056_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1056_);
v___x_1058_ = v___x_1039_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_env_1030_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_nextMacroScope_1031_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ngen_1032_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_auxDeclNGen_1033_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v_cache_1034_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_messages_1035_);
lean_ctor_set(v_reuseFailAlloc_1064_, 7, v_infoState_1036_);
lean_ctor_set(v_reuseFailAlloc_1064_, 8, v_snapshotTasks_1037_);
v___x_1058_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = lean_st_ref_set(v___y_1020_, v___x_1058_);
v___x_1060_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1060_);
v___x_1062_ = v___x_1026_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___boxed(lean_object* v_cls_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v_cls_1069_, v_msg_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_ref_1079_; lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_ref_1079_ = lean_ctor_get(v___y_1076_, 5);
v___x_1080_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0_spec__0(v_msg_1075_, v___y_1076_, v___y_1077_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_inc(v_ref_1079_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_ref_1079_);
lean_ctor_set(v___x_1085_, 1, v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg___boxed(lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v_msg_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1094_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3(void){
_start:
{
lean_object* v___x_1098_; double v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(1000000000u);
v___x_1099_ = lean_float_of_nat(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object* v_lratPath_1105_, uint8_t v_trimProofs_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_IO_FS_readBinFile(v_lratPath_1105_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_options_1111_; lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1546_; 
v_options_1111_ = lean_ctor_get(v_a_1107_, 2);
v_a_1112_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1546_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1546_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_ref_1116_; lean_object* v_inheritedTraceOptions_1117_; uint8_t v_hasTrace_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v_proof_1123_; lean_object* v___y_1124_; lean_object* v_options_1125_; lean_object* v_inheritedTraceOptions_1126_; lean_object* v___y_1127_; lean_object* v_proof_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; lean_object* v_a_1180_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v_a_1196_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v_a_1205_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v_a_1224_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v_a_1383_; lean_object* v___y_1405_; 
v_ref_1116_ = lean_ctor_get(v_a_1107_, 5);
v_inheritedTraceOptions_1117_ = lean_ctor_get(v_a_1107_, 13);
v_hasTrace_1118_ = lean_ctor_get_uint8(v_options_1111_, sizeof(void*)*1);
v___f_1119_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0));
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_1120_, 0, v_a_1112_);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_1171_ = 1;
v___x_1172_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_1118_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = l_IO_lazyPure___redArg(v___f_1120_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1407_);
if (lean_obj_tag(v_a_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1409_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref(v_a_1408_);
v___x_1410_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1411_ = l_Lean_stringToMessageData(v_a_1409_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1412_, v_a_1107_, v_a_1108_);
v___y_1405_ = v___x_1413_;
goto v___jp_1404_;
}
else
{
lean_object* v_a_1414_; 
v_a_1414_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v_a_1408_);
v_a_1383_ = v_a_1414_;
goto v___jp_1382_;
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1114_);
v_a_1415_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1417_ = v___x_1407_;
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1407_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1419_ = lean_io_error_to_string(v_a_1415_);
v___x_1420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
v___x_1421_ = l_Lean_MessageData_ofFormat(v___x_1420_);
lean_inc(v_ref_1116_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_ref_1116_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1422_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v___f_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v_a_1433_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v_a_1448_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v_a_1453_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v_a_1458_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v_a_1470_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v_a_1475_; 
v___f_1427_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7));
v___x_1428_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1429_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1117_, v_options_1111_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = l_Lean_trace_profiler;
v___x_1525_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1111_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = l_IO_lazyPure___redArg(v___f_1120_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
if (lean_obj_tag(v_a_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_a_1528_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v_a_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1530_ = l_Lean_stringToMessageData(v_a_1528_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1531_, v_a_1107_, v_a_1108_);
v___y_1405_ = v___x_1532_;
goto v___jp_1404_;
}
else
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v_a_1527_);
v_a_1383_ = v_a_1533_;
goto v___jp_1382_;
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1114_);
v_a_1534_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1536_ = v___x_1526_;
v_isShared_1537_ = v_isSharedCheck_1545_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1526_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1545_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1538_ = lean_io_error_to_string(v_a_1534_);
v___x_1539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
v___x_1540_ = l_Lean_MessageData_ofFormat(v___x_1539_);
lean_inc(v_ref_1116_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_ref_1116_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1541_);
v___x_1543_ = v___x_1536_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
goto v___jp_1477_;
}
}
else
{
goto v___jp_1477_;
}
v___jp_1430_:
{
lean_object* v___x_1434_; double v___x_1435_; double v___x_1436_; double v___x_1437_; double v___x_1438_; double v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1434_ = lean_io_mono_nanos_now();
v___x_1435_ = lean_float_of_nat(v___y_1432_);
v___x_1436_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1437_ = lean_float_div(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_float_of_nat(v___x_1434_);
v___x_1439_ = lean_float_div(v___x_1438_, v___x_1436_);
v___x_1440_ = lean_box_float(v___x_1437_);
v___x_1441_ = lean_box_float(v___x_1439_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_a_1433_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1121_, v___x_1171_, v___x_1172_, v_options_1111_, v___x_1429_, v___y_1431_, v___f_1427_, v___x_1443_, v_a_1107_, v_a_1108_);
v___y_1405_ = v___x_1444_;
goto v___jp_1404_;
}
v___jp_1445_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_a_1448_);
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1447_;
v_a_1433_ = v___x_1449_;
goto v___jp_1430_;
}
v___jp_1450_:
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1453_);
v___y_1431_ = v___y_1451_;
v___y_1432_ = v___y_1452_;
v_a_1433_ = v___x_1454_;
goto v___jp_1430_;
}
v___jp_1455_:
{
lean_object* v___x_1459_; double v___x_1460_; double v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1459_ = lean_io_get_num_heartbeats();
v___x_1460_ = lean_float_of_nat(v___y_1457_);
v___x_1461_ = lean_float_of_nat(v___x_1459_);
v___x_1462_ = lean_box_float(v___x_1460_);
v___x_1463_ = lean_box_float(v___x_1461_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1458_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1121_, v___x_1171_, v___x_1172_, v_options_1111_, v___x_1429_, v___y_1456_, v___f_1427_, v___x_1465_, v_a_1107_, v_a_1108_);
v___y_1405_ = v___x_1466_;
goto v___jp_1404_;
}
v___jp_1467_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1470_);
v___y_1456_ = v___y_1468_;
v___y_1457_ = v___y_1469_;
v_a_1458_ = v___x_1471_;
goto v___jp_1455_;
}
v___jp_1472_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1475_);
v___y_1456_ = v___y_1473_;
v___y_1457_ = v___y_1474_;
v_a_1458_ = v___x_1476_;
goto v___jp_1455_;
}
v___jp_1477_:
{
lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v_a_1108_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1481_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1111_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_io_mono_nanos_now();
v___x_1483_ = l_IO_lazyPure___redArg(v___f_1120_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
if (lean_obj_tag(v_a_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; 
v_a_1485_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v_a_1484_);
v___x_1486_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1487_ = l_Lean_stringToMessageData(v_a_1485_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1488_, v_a_1107_, v_a_1108_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
v___y_1446_ = v_a_1479_;
v___y_1447_ = v___x_1482_;
v_a_1448_ = v_a_1490_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v_a_1484_);
v___y_1451_ = v_a_1479_;
v___y_1452_ = v___x_1482_;
v_a_1453_ = v_a_1491_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1502_; 
v_a_1492_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1494_ = v___x_1483_;
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1483_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_io_error_to_string(v_a_1492_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 3);
lean_ctor_set(v___x_1494_, 0, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l_Lean_MessageData_ofFormat(v___x_1498_);
lean_inc(v_ref_1116_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_ref_1116_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___y_1446_ = v_a_1479_;
v___y_1447_ = v___x_1482_;
v_a_1448_ = v___x_1500_;
goto v___jp_1445_;
}
}
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_io_get_num_heartbeats();
v___x_1504_ = l_IO_lazyPure___redArg(v___f_1120_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
if (lean_obj_tag(v_a_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_a_1511_; 
v_a_1506_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v_a_1505_);
v___x_1507_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1508_ = l_Lean_stringToMessageData(v_a_1506_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v___x_1509_, v_a_1107_, v_a_1108_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
v___y_1468_ = v_a_1479_;
v___y_1469_ = v___x_1503_;
v_a_1470_ = v_a_1511_;
goto v___jp_1467_;
}
else
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v_a_1505_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v_a_1505_);
v___y_1473_ = v_a_1479_;
v___y_1474_ = v___x_1503_;
v_a_1475_ = v_a_1512_;
goto v___jp_1472_;
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_a_1513_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1515_ = v___x_1504_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1504_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_io_error_to_string(v_a_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 3);
lean_ctor_set(v___x_1515_, 0, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = l_Lean_MessageData_ofFormat(v___x_1519_);
lean_inc(v_ref_1116_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_ref_1116_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___y_1468_ = v_a_1479_;
v___y_1469_ = v___x_1503_;
v_a_1470_ = v___x_1521_;
goto v___jp_1467_;
}
}
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1126_, v_options_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1131_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_proof_1123_);
v___x_1131_ = v___x_1114_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_proof_1123_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_del_object(v___x_1114_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1134_ = lean_array_get_size(v_proof_1123_);
v___x_1135_ = l_Nat_reprFast(v___x_1134_);
v___x_1136_ = lean_string_append(v___x_1133_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2));
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_ofFormat(v___x_1139_);
v___x_1141_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v___x_1121_, v___x_1140_, v___y_1124_, v___y_1127_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1149_);
v___x_1143_ = v___x_1141_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_dec(v___x_1141_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_proof_1123_);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_proof_1123_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_proof_1123_);
v_a_1150_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
v___jp_1158_:
{
lean_object* v_options_1162_; uint8_t v_hasTrace_1163_; 
v_options_1162_ = lean_ctor_get(v___y_1160_, 2);
v_hasTrace_1163_ = lean_ctor_get_uint8(v_options_1162_, sizeof(void*)*1);
if (v_hasTrace_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_del_object(v___x_1114_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_proof_1159_);
return v___x_1164_;
}
else
{
lean_object* v_inheritedTraceOptions_1165_; 
v_inheritedTraceOptions_1165_ = lean_ctor_get(v___y_1160_, 13);
v_proof_1123_ = v_proof_1159_;
v___y_1124_ = v___y_1160_;
v_options_1125_ = v_options_1162_;
v_inheritedTraceOptions_1126_ = v_inheritedTraceOptions_1165_;
v___y_1127_ = v___y_1161_;
goto v___jp_1122_;
}
}
v___jp_1166_:
{
if (lean_obj_tag(v___y_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___y_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___y_1169_);
v_proof_1159_ = v_a_1170_;
v___y_1160_ = v___y_1168_;
v___y_1161_ = v___y_1167_;
goto v___jp_1158_;
}
else
{
lean_del_object(v___x_1114_);
return v___y_1169_;
}
}
v___jp_1173_:
{
lean_object* v___x_1181_; double v___x_1182_; double v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1181_ = lean_io_get_num_heartbeats();
v___x_1182_ = lean_float_of_nat(v___y_1175_);
v___x_1183_ = lean_float_of_nat(v___x_1181_);
v___x_1184_ = lean_box_float(v___x_1182_);
v___x_1185_ = lean_box_float(v___x_1183_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1180_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1121_, v___x_1171_, v___x_1172_, v___y_1176_, v___y_1178_, v___y_1177_, v___f_1119_, v___x_1187_, v___y_1179_, v___y_1174_);
v___y_1167_ = v___y_1174_;
v___y_1168_ = v___y_1179_;
v___y_1169_ = v___x_1188_;
goto v___jp_1166_;
}
v___jp_1189_:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1196_);
v___y_1174_ = v___y_1190_;
v___y_1175_ = v___y_1191_;
v___y_1176_ = v___y_1192_;
v___y_1177_ = v___y_1193_;
v___y_1178_ = v___y_1194_;
v___y_1179_ = v___y_1195_;
v_a_1180_ = v___x_1197_;
goto v___jp_1173_;
}
v___jp_1198_:
{
lean_object* v___x_1206_; double v___x_1207_; double v___x_1208_; double v___x_1209_; double v___x_1210_; double v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1206_ = lean_io_mono_nanos_now();
v___x_1207_ = lean_float_of_nat(v___y_1202_);
v___x_1208_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1209_ = lean_float_div(v___x_1207_, v___x_1208_);
v___x_1210_ = lean_float_of_nat(v___x_1206_);
v___x_1211_ = lean_float_div(v___x_1210_, v___x_1208_);
v___x_1212_ = lean_box_float(v___x_1209_);
v___x_1213_ = lean_box_float(v___x_1211_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1205_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___x_1121_, v___x_1171_, v___x_1172_, v___y_1200_, v___y_1203_, v___y_1201_, v___f_1119_, v___x_1215_, v___y_1204_, v___y_1199_);
v___y_1167_ = v___y_1199_;
v___y_1168_ = v___y_1204_;
v___y_1169_ = v___x_1216_;
goto v___jp_1166_;
}
v___jp_1217_:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1224_);
v___y_1199_ = v___y_1218_;
v___y_1200_ = v___y_1219_;
v___y_1201_ = v___y_1221_;
v___y_1202_ = v___y_1220_;
v___y_1203_ = v___y_1222_;
v___y_1204_ = v___y_1223_;
v_a_1205_ = v___x_1225_;
goto v___jp_1198_;
}
v___jp_1226_:
{
lean_object* v___x_1233_; lean_object* v_a_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_1228_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1236_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_1229_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_io_mono_nanos_now();
v___x_1238_ = l_IO_lazyPure___redArg(v___y_1227_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
v___y_1199_ = v___y_1228_;
v___y_1200_ = v___y_1229_;
v___y_1201_ = v_a_1234_;
v___y_1202_ = v___x_1237_;
v___y_1203_ = v___y_1230_;
v___y_1204_ = v___y_1231_;
v_a_1205_ = v___x_1246_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1259_; 
v_a_1249_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1251_ = v___x_1240_;
v_isShared_1252_ = v_isSharedCheck_1259_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1240_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1259_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_io_error_to_string(v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 3);
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_Lean_MessageData_ofFormat(v___x_1255_);
lean_inc(v___y_1232_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1232_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___y_1218_ = v___y_1228_;
v___y_1219_ = v___y_1229_;
v___y_1220_ = v___x_1237_;
v___y_1221_ = v_a_1234_;
v___y_1222_ = v___y_1230_;
v___y_1223_ = v___y_1231_;
v_a_1224_ = v___x_1257_;
goto v___jp_1217_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1270_; 
v_a_1260_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1262_ = v___x_1238_;
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1238_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_io_error_to_string(v_a_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 3);
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_Lean_MessageData_ofFormat(v___x_1266_);
lean_inc(v___y_1232_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1232_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___y_1218_ = v___y_1228_;
v___y_1219_ = v___y_1229_;
v___y_1220_ = v___x_1237_;
v___y_1221_ = v_a_1234_;
v___y_1222_ = v___y_1230_;
v___y_1223_ = v___y_1231_;
v_a_1224_ = v___x_1268_;
goto v___jp_1217_;
}
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_io_get_num_heartbeats();
v___x_1272_ = l_IO_lazyPure___redArg(v___y_1227_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v___y_1174_ = v___y_1228_;
v___y_1175_ = v___x_1271_;
v___y_1176_ = v___y_1229_;
v___y_1177_ = v_a_1234_;
v___y_1178_ = v___y_1230_;
v___y_1179_ = v___y_1231_;
v_a_1180_ = v___x_1280_;
goto v___jp_1173_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1293_; 
v_a_1283_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1285_ = v___x_1274_;
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1274_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_io_error_to_string(v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 3);
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = l_Lean_MessageData_ofFormat(v___x_1289_);
lean_inc(v___y_1232_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___y_1232_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___y_1190_ = v___y_1228_;
v___y_1191_ = v___x_1271_;
v___y_1192_ = v___y_1229_;
v___y_1193_ = v_a_1234_;
v___y_1194_ = v___y_1230_;
v___y_1195_ = v___y_1231_;
v_a_1196_ = v___x_1291_;
goto v___jp_1189_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1304_; 
v_a_1294_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1296_ = v___x_1272_;
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1272_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_io_error_to_string(v_a_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 3);
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = l_Lean_MessageData_ofFormat(v___x_1300_);
lean_inc(v___y_1232_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___y_1232_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___y_1190_ = v___y_1228_;
v___y_1191_ = v___x_1271_;
v___y_1192_ = v___y_1229_;
v___y_1193_ = v_a_1234_;
v___y_1194_ = v___y_1230_;
v___y_1195_ = v___y_1231_;
v_a_1196_ = v___x_1302_;
goto v___jp_1189_;
}
}
}
}
}
v___jp_1305_:
{
if (v_trimProofs_1106_ == 0)
{
lean_dec_ref(v___y_1306_);
v_proof_1159_ = v___y_1307_;
v___y_1160_ = v___y_1308_;
v___y_1161_ = v___y_1309_;
goto v___jp_1158_;
}
else
{
lean_object* v_options_1310_; uint8_t v_hasTrace_1311_; 
lean_dec_ref(v___y_1307_);
v_options_1310_ = lean_ctor_get(v___y_1308_, 2);
v_hasTrace_1311_ = lean_ctor_get_uint8(v_options_1310_, sizeof(void*)*1);
if (v_hasTrace_1311_ == 0)
{
lean_object* v_ref_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1114_);
v_ref_1312_ = lean_ctor_get(v___y_1308_, 5);
v___x_1313_ = l_IO_lazyPure___redArg(v___y_1306_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1335_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1326_ = v___x_1315_;
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1315_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1328_ = lean_io_error_to_string(v_a_1324_);
v___x_1329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_ofFormat(v___x_1329_);
lean_inc(v_ref_1312_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_ref_1312_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1331_);
v___x_1333_ = v___x_1326_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1347_; 
v_a_1336_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1338_ = v___x_1313_;
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1313_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1340_ = lean_io_error_to_string(v_a_1336_);
v___x_1341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
v___x_1342_ = l_Lean_MessageData_ofFormat(v___x_1341_);
lean_inc(v_ref_1312_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_ref_1312_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1343_);
v___x_1345_ = v___x_1338_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
else
{
lean_object* v_ref_1348_; lean_object* v_inheritedTraceOptions_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_ref_1348_ = lean_ctor_get(v___y_1308_, 5);
v_inheritedTraceOptions_1349_ = lean_ctor_get(v___y_1308_, 13);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1351_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1349_, v_options_1310_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = l_Lean_trace_profiler;
v___x_1353_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_1310_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = l_IO_lazyPure___redArg(v___y_1306_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___redArg(v_a_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v_proof_1123_ = v_a_1357_;
v___y_1124_ = v___y_1308_;
v_options_1125_ = v_options_1310_;
v_inheritedTraceOptions_1126_ = v_inheritedTraceOptions_1349_;
v___y_1127_ = v___y_1309_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
lean_del_object(v___x_1114_);
v_a_1358_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1360_ = v___x_1356_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1356_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1362_ = lean_io_error_to_string(v_a_1358_);
v___x_1363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = l_Lean_MessageData_ofFormat(v___x_1363_);
lean_inc(v_ref_1348_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_ref_1348_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1365_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1114_);
v_a_1370_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1372_ = v___x_1354_;
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1354_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1374_ = lean_io_error_to_string(v_a_1370_);
v___x_1375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = l_Lean_MessageData_ofFormat(v___x_1375_);
lean_inc(v_ref_1348_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_ref_1348_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1377_);
v___x_1379_ = v___x_1372_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
v___y_1227_ = v___y_1306_;
v___y_1228_ = v___y_1309_;
v___y_1229_ = v_options_1310_;
v___y_1230_ = v___x_1351_;
v___y_1231_ = v___y_1308_;
v___y_1232_ = v_ref_1348_;
goto v___jp_1226_;
}
}
else
{
v___y_1227_ = v___y_1306_;
v___y_1228_ = v___y_1309_;
v___y_1229_ = v_options_1310_;
v___y_1230_ = v___x_1351_;
v___y_1231_ = v___y_1308_;
v___y_1232_ = v_ref_1348_;
goto v___jp_1226_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___f_1384_; 
lean_inc_ref(v_a_1383_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1384_, 0, v_a_1383_);
if (v_hasTrace_1118_ == 0)
{
v___y_1306_ = v___f_1384_;
v___y_1307_ = v_a_1383_;
v___y_1308_ = v_a_1107_;
v___y_1309_ = v_a_1108_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_1386_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1117_, v_options_1111_, v___x_1385_);
if (v___x_1386_ == 0)
{
v___y_1306_ = v___f_1384_;
v___y_1307_ = v_a_1383_;
v___y_1308_ = v_a_1107_;
v___y_1309_ = v_a_1108_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1388_ = lean_array_get_size(v_a_1383_);
v___x_1389_ = l_Nat_reprFast(v___x_1388_);
v___x_1390_ = lean_string_append(v___x_1387_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___x_1394_ = l_Lean_MessageData_ofFormat(v___x_1393_);
v___x_1395_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v___x_1121_, v___x_1394_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_dec_ref(v___x_1395_);
v___y_1306_ = v___f_1384_;
v___y_1307_ = v_a_1383_;
v___y_1308_ = v_a_1107_;
v___y_1309_ = v_a_1108_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v___f_1384_);
lean_dec_ref(v_a_1383_);
lean_del_object(v___x_1114_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
v___jp_1404_:
{
if (lean_obj_tag(v___y_1405_) == 0)
{
lean_object* v_a_1406_; 
v_a_1406_ = lean_ctor_get(v___y_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref(v___y_1405_);
v_a_1383_ = v_a_1406_;
goto v___jp_1382_;
}
else
{
lean_del_object(v___x_1114_);
return v___y_1405_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1559_; 
v_a_1547_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1549_ = v___x_1110_;
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1110_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_ref_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_ref_1551_ = lean_ctor_get(v_a_1107_, 5);
v___x_1552_ = lean_io_error_to_string(v_a_1547_);
v___x_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = l_Lean_MessageData_ofFormat(v___x_1553_);
lean_inc(v_ref_1551_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_ref_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1555_);
v___x_1557_ = v___x_1549_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object* v_lratPath_1560_, lean_object* v_trimProofs_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
uint8_t v_trimProofs_boxed_1565_; lean_object* v_res_1566_; 
v_trimProofs_boxed_1565_ = lean_unbox(v_trimProofs_1561_);
v_res_1566_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1560_, v_trimProofs_boxed_1565_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec_ref(v_lratPath_1560_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6(lean_object* v_00_u03b1_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_x_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_x_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6(v_00_u03b1_1573_, v_x_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object* v_00_u03b1_1579_, lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___redArg(v_msg_1580_, v___y_1581_, v___y_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v_00_u03b1_1585_, v_msg_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object* v_lratPath_1591_, uint8_t v_trimProofs_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1591_, v_trimProofs_1592_, v_a_1593_, v_a_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1597_);
lean_dec(v_a_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1606_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1596_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1596_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object* v_lratPath_1614_, lean_object* v_trimProofs_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
uint8_t v_trimProofs_boxed_1619_; lean_object* v_res_1620_; 
v_trimProofs_boxed_1619_ = lean_unbox(v_trimProofs_1615_);
v_res_1620_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_1614_, v_trimProofs_boxed_1619_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec_ref(v_lratPath_1614_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1621_, lean_object* v___y_1622_, lean_object* v_a_x3f_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_io_remove_file(v_snd_1621_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1646_; 
v_a_1634_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1636_ = v___x_1625_;
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1625_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1646_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_ref_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v_ref_1638_ = lean_ctor_get(v___y_1622_, 5);
v___x_1639_ = lean_io_error_to_string(v_a_1634_);
v___x_1640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = l_Lean_MessageData_ofFormat(v___x_1640_);
lean_inc(v_ref_1638_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_ref_1638_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1642_);
v___x_1644_ = v___x_1636_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1647_, lean_object* v___y_1648_, lean_object* v_a_x3f_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1647_, v___y_1648_, v_a_x3f_1649_);
lean_dec(v_a_x3f_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v_snd_1647_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(lean_object* v_f_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v_fst_1658_; lean_object* v_snd_1659_; lean_object* v_r_1660_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v_fst_1658_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_fst_1658_);
v_snd_1659_ = lean_ctor_get(v_a_1657_, 1);
lean_inc_n(v_snd_1659_, 2);
lean_dec(v_a_1657_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
v_r_1660_ = lean_apply_5(v_f_1652_, v_fst_1658_, v_snd_1659_, v___y_1653_, v___y_1654_, lean_box(0));
if (lean_obj_tag(v_r_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1685_; 
v_a_1661_ = lean_ctor_get(v_r_1660_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_r_1660_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1663_ = v_r_1660_;
v_isShared_1664_ = v_isSharedCheck_1685_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v_r_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1685_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
lean_inc(v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 1);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1659_, v___y_1653_, v___x_1666_);
lean_dec_ref(v___x_1666_);
lean_dec(v_snd_1659_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v___x_1667_, 0);
lean_dec(v_unused_1675_);
v___x_1669_ = v___x_1667_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_dec(v___x_1667_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_a_1661_);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1661_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_a_1661_);
v_a_1676_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1667_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1667_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1686_ = lean_ctor_get(v_r_1660_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v_r_1660_);
v___x_1687_ = lean_box(0);
v___x_1688_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1659_, v___y_1653_, v___x_1687_);
lean_dec(v_snd_1659_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1688_, 0);
lean_dec(v_unused_1696_);
v___x_1690_ = v___x_1688_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v___x_1688_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
lean_ctor_set(v___x_1690_, 0, v_a_1686_);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1686_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_a_1686_);
v_a_1697_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1688_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v_f_1652_);
v_a_1705_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1707_ = v___x_1656_;
v_isShared_1708_ = v_isSharedCheck_1717_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1656_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1717_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_ref_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v_ref_1709_ = lean_ctor_get(v___y_1653_, 5);
v___x_1710_ = lean_io_error_to_string(v_a_1705_);
v___x_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
v___x_1712_ = l_Lean_MessageData_ofFormat(v___x_1711_);
lean_inc(v_ref_1709_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_ref_1709_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1713_);
v___x_1715_ = v___x_1707_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___boxed(lean_object* v_f_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(lean_object* v_00_u03b1_1723_, lean_object* v_f_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_f_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(v_00_u03b1_1729_, v_f_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object* v_cnf_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_Sat_CNF_dimacs(v_cnf_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object* v_cnf_1738_, lean_object* v_x_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(v_cnf_1738_, v_x_1739_);
lean_dec_ref(v_cnf_1738_);
return v_res_1740_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1));
v___x_1745_ = l_Lean_MessageData_ofFormat(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(v_x_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_x_1752_);
return v_res_1756_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1));
v___x_1761_ = l_Lean_MessageData_ofFormat(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object* v_x_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(v_x_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v_x_1768_);
return v_res_1772_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1));
v___x_1777_ = l_Lean_MessageData_ofFormat(v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object* v_x_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(v_x_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_x_1784_);
return v_res_1788_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(lean_object* v_e_1789_){
_start:
{
if (lean_obj_tag(v_e_1789_) == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = 2;
return v___x_1790_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1792_){
_start:
{
uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_res_1793_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_e_1792_);
lean_dec_ref(v_e_1792_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object* v_cls_1795_, uint8_t v_collapsed_1796_, lean_object* v_tag_1797_, lean_object* v_opts_1798_, uint8_t v_clsEnabled_1799_, lean_object* v_oldTraces_1800_, lean_object* v_msg_1801_, lean_object* v_resStartStop_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1905_; 
v_fst_1806_ = lean_ctor_get(v_resStartStop_1802_, 0);
v_snd_1807_ = lean_ctor_get(v_resStartStop_1802_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_resStartStop_1802_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1809_ = v_resStartStop_1802_;
v_isShared_1810_ = v_isSharedCheck_1905_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_inc(v_fst_1806_);
lean_dec(v_resStartStop_1802_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1905_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v_data_1814_; lean_object* v_fst_1825_; lean_object* v_snd_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1904_; 
v_fst_1825_ = lean_ctor_get(v_snd_1807_, 0);
v_snd_1826_ = lean_ctor_get(v_snd_1807_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_snd_1807_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1828_ = v_snd_1807_;
v_isShared_1829_ = v_isSharedCheck_1904_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snd_1826_);
lean_inc(v_fst_1825_);
lean_dec(v_snd_1807_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1904_;
goto v_resetjp_1827_;
}
v___jp_1811_:
{
lean_object* v___x_1815_; 
lean_inc(v___y_1813_);
v___x_1815_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_1800_, v_data_1814_, v___y_1813_, v___y_1812_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v___x_1816_; 
lean_dec_ref(v___x_1815_);
v___x_1816_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1806_);
return v___x_1816_;
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_fst_1806_);
v_a_1817_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1815_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1815_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___y_1833_; lean_object* v_a_1834_; uint8_t v___y_1858_; double v___y_1889_; 
v___x_1830_ = l_Lean_trace_profiler;
v___x_1831_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1798_, v___x_1830_);
if (v___x_1831_ == 0)
{
v___y_1858_ = v___x_1831_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1895_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1798_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; double v___x_1898_; double v___x_1899_; double v___x_1900_; 
v___x_1896_ = l_Lean_trace_profiler_threshold;
v___x_1897_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1798_, v___x_1896_);
v___x_1898_ = lean_float_of_nat(v___x_1897_);
v___x_1899_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_1900_ = lean_float_div(v___x_1898_, v___x_1899_);
v___y_1889_ = v___x_1900_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; double v___x_1903_; 
v___x_1901_ = l_Lean_trace_profiler_threshold;
v___x_1902_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1798_, v___x_1901_);
v___x_1903_ = lean_float_of_nat(v___x_1902_);
v___y_1889_ = v___x_1903_;
goto v___jp_1888_;
}
}
v___jp_1832_:
{
uint8_t v_result_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_result_1835_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_fst_1806_);
v___x_1836_ = l_Lean_TraceResult_toEmoji(v_result_1835_);
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
v___x_1838_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 7);
lean_ctor_set(v___x_1828_, 1, v___x_1838_);
lean_ctor_set(v___x_1828_, 0, v___x_1837_);
v___x_1840_ = v___x_1828_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v_m_1842_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 7);
lean_ctor_set(v___x_1809_, 1, v_a_1834_);
lean_ctor_set(v___x_1809_, 0, v___x_1840_);
v_m_1842_ = v___x_1809_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_a_1834_);
v_m_1842_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; double v___x_1845_; lean_object* v_data_1846_; 
v___x_1843_ = lean_box(v_result_1835_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1797_);
lean_inc_ref(v___x_1844_);
lean_inc(v_cls_1795_);
v_data_1846_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1846_, 0, v_cls_1795_);
lean_ctor_set(v_data_1846_, 1, v___x_1844_);
lean_ctor_set(v_data_1846_, 2, v_tag_1797_);
lean_ctor_set_float(v_data_1846_, sizeof(void*)*3, v___x_1845_);
lean_ctor_set_float(v_data_1846_, sizeof(void*)*3 + 8, v___x_1845_);
lean_ctor_set_uint8(v_data_1846_, sizeof(void*)*3 + 16, v_collapsed_1796_);
if (v___x_1831_ == 0)
{
lean_dec_ref(v___x_1844_);
lean_dec(v_snd_1826_);
lean_dec(v_fst_1825_);
lean_dec_ref(v_tag_1797_);
lean_dec(v_cls_1795_);
v___y_1812_ = v_m_1842_;
v___y_1813_ = v___y_1833_;
v_data_1814_ = v_data_1846_;
goto v___jp_1811_;
}
else
{
lean_object* v_data_1847_; double v___x_1848_; double v___x_1849_; 
lean_dec_ref(v_data_1846_);
v_data_1847_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1847_, 0, v_cls_1795_);
lean_ctor_set(v_data_1847_, 1, v___x_1844_);
lean_ctor_set(v_data_1847_, 2, v_tag_1797_);
v___x_1848_ = lean_unbox_float(v_fst_1825_);
lean_dec(v_fst_1825_);
lean_ctor_set_float(v_data_1847_, sizeof(void*)*3, v___x_1848_);
v___x_1849_ = lean_unbox_float(v_snd_1826_);
lean_dec(v_snd_1826_);
lean_ctor_set_float(v_data_1847_, sizeof(void*)*3 + 8, v___x_1849_);
lean_ctor_set_uint8(v_data_1847_, sizeof(void*)*3 + 16, v_collapsed_1796_);
v___y_1812_ = v_m_1842_;
v___y_1813_ = v___y_1833_;
v_data_1814_ = v_data_1847_;
goto v___jp_1811_;
}
}
}
}
v___jp_1852_:
{
lean_object* v_ref_1853_; lean_object* v___x_1854_; 
v_ref_1853_ = lean_ctor_get(v___y_1803_, 5);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v_fst_1806_);
v___x_1854_ = lean_apply_4(v_msg_1801_, v_fst_1806_, v___y_1803_, v___y_1804_, lean_box(0));
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v___y_1833_ = v_ref_1853_;
v_a_1834_ = v_a_1855_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1854_);
v___x_1856_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_1833_ = v_ref_1853_;
v_a_1834_ = v___x_1856_;
goto v___jp_1832_;
}
}
v___jp_1857_:
{
if (v_clsEnabled_1799_ == 0)
{
if (v___y_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v_traceState_1860_; lean_object* v_env_1861_; lean_object* v_nextMacroScope_1862_; lean_object* v_ngen_1863_; lean_object* v_auxDeclNGen_1864_; lean_object* v_cache_1865_; lean_object* v_messages_1866_; lean_object* v_infoState_1867_; lean_object* v_snapshotTasks_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1887_; 
lean_del_object(v___x_1828_);
lean_dec(v_snd_1826_);
lean_dec(v_fst_1825_);
lean_del_object(v___x_1809_);
lean_dec_ref(v_msg_1801_);
lean_dec_ref(v_tag_1797_);
lean_dec(v_cls_1795_);
v___x_1859_ = lean_st_ref_take(v___y_1804_);
v_traceState_1860_ = lean_ctor_get(v___x_1859_, 4);
v_env_1861_ = lean_ctor_get(v___x_1859_, 0);
v_nextMacroScope_1862_ = lean_ctor_get(v___x_1859_, 1);
v_ngen_1863_ = lean_ctor_get(v___x_1859_, 2);
v_auxDeclNGen_1864_ = lean_ctor_get(v___x_1859_, 3);
v_cache_1865_ = lean_ctor_get(v___x_1859_, 5);
v_messages_1866_ = lean_ctor_get(v___x_1859_, 6);
v_infoState_1867_ = lean_ctor_get(v___x_1859_, 7);
v_snapshotTasks_1868_ = lean_ctor_get(v___x_1859_, 8);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1887_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snapshotTasks_1868_);
lean_inc(v_infoState_1867_);
lean_inc(v_messages_1866_);
lean_inc(v_cache_1865_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1864_);
lean_inc(v_ngen_1863_);
lean_inc(v_nextMacroScope_1862_);
lean_inc(v_env_1861_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1887_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint64_t v_tid_1872_; lean_object* v_traces_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1886_; 
v_tid_1872_ = lean_ctor_get_uint64(v_traceState_1860_, sizeof(void*)*1);
v_traces_1873_ = lean_ctor_get(v_traceState_1860_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_traceState_1860_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1875_ = v_traceState_1860_;
v_isShared_1876_ = v_isSharedCheck_1886_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_traces_1873_);
lean_dec(v_traceState_1860_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1886_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1800_, v_traces_1873_);
lean_dec_ref(v_traces_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1877_);
lean_ctor_set_uint64(v_reuseFailAlloc_1885_, sizeof(void*)*1, v_tid_1872_);
v___x_1879_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 4, v___x_1879_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_env_1861_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_nextMacroScope_1862_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_ngen_1863_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_auxDeclNGen_1864_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1884_, 5, v_cache_1865_);
lean_ctor_set(v_reuseFailAlloc_1884_, 6, v_messages_1866_);
lean_ctor_set(v_reuseFailAlloc_1884_, 7, v_infoState_1867_);
lean_ctor_set(v_reuseFailAlloc_1884_, 8, v_snapshotTasks_1868_);
v___x_1881_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_st_ref_set(v___y_1804_, v___x_1881_);
v___x_1883_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1806_);
return v___x_1883_;
}
}
}
}
}
else
{
goto v___jp_1852_;
}
}
else
{
goto v___jp_1852_;
}
}
v___jp_1888_:
{
double v___x_1890_; double v___x_1891_; double v___x_1892_; uint8_t v___x_1893_; 
v___x_1890_ = lean_unbox_float(v_snd_1826_);
v___x_1891_ = lean_unbox_float(v_fst_1825_);
v___x_1892_ = lean_float_sub(v___x_1890_, v___x_1891_);
v___x_1893_ = lean_float_decLt(v___y_1889_, v___x_1892_);
v___y_1858_ = v___x_1893_;
goto v___jp_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___boxed(lean_object* v_cls_1906_, lean_object* v_collapsed_1907_, lean_object* v_tag_1908_, lean_object* v_opts_1909_, lean_object* v_clsEnabled_1910_, lean_object* v_oldTraces_1911_, lean_object* v_msg_1912_, lean_object* v_resStartStop_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v_collapsed_boxed_1917_; uint8_t v_clsEnabled_boxed_1918_; lean_object* v_res_1919_; 
v_collapsed_boxed_1917_ = lean_unbox(v_collapsed_1907_);
v_clsEnabled_boxed_1918_ = lean_unbox(v_clsEnabled_1910_);
v_res_1919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v_cls_1906_, v_collapsed_boxed_1917_, v_tag_1908_, v_opts_1909_, v_clsEnabled_boxed_1918_, v_oldTraces_1911_, v_msg_1912_, v_resStartStop_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v_opts_1909_);
return v_res_1919_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(lean_object* v_e_1920_){
_start:
{
if (lean_obj_tag(v_e_1920_) == 0)
{
uint8_t v___x_1921_; 
v___x_1921_ = 2;
return v___x_1921_;
}
else
{
uint8_t v___x_1922_; 
v___x_1922_ = 0;
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1923_){
_start:
{
uint8_t v_res_1924_; lean_object* v_r_1925_; 
v_res_1924_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_e_1923_);
lean_dec_ref(v_e_1923_);
v_r_1925_ = lean_box(v_res_1924_);
return v_r_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(lean_object* v_cls_1926_, uint8_t v_collapsed_1927_, lean_object* v_tag_1928_, lean_object* v_opts_1929_, uint8_t v_clsEnabled_1930_, lean_object* v_oldTraces_1931_, lean_object* v_msg_1932_, lean_object* v_resStartStop_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2036_; 
v_fst_1937_ = lean_ctor_get(v_resStartStop_1933_, 0);
v_snd_1938_ = lean_ctor_get(v_resStartStop_1933_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_resStartStop_1933_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1940_ = v_resStartStop_1933_;
v_isShared_1941_ = v_isSharedCheck_2036_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snd_1938_);
lean_inc(v_fst_1937_);
lean_dec(v_resStartStop_1933_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2036_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_data_1945_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2035_; 
v_fst_1956_ = lean_ctor_get(v_snd_1938_, 0);
v_snd_1957_ = lean_ctor_get(v_snd_1938_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_snd_1938_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1959_ = v_snd_1938_;
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_snd_1957_);
lean_inc(v_fst_1956_);
lean_dec(v_snd_1938_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2035_;
goto v_resetjp_1958_;
}
v___jp_1942_:
{
lean_object* v___x_1946_; 
lean_inc(v___y_1944_);
v___x_1946_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_1931_, v_data_1945_, v___y_1944_, v___y_1943_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref(v___x_1946_);
v___x_1947_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1937_);
return v___x_1947_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_fst_1937_);
v_a_1948_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; uint8_t v___x_1962_; lean_object* v___y_1964_; lean_object* v_a_1965_; uint8_t v___y_1989_; double v___y_2020_; 
v___x_1961_ = l_Lean_trace_profiler;
v___x_1962_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1929_, v___x_1961_);
if (v___x_1962_ == 0)
{
v___y_1989_ = v___x_1962_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2026_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_1929_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; double v___x_2029_; double v___x_2030_; double v___x_2031_; 
v___x_2027_ = l_Lean_trace_profiler_threshold;
v___x_2028_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1929_, v___x_2027_);
v___x_2029_ = lean_float_of_nat(v___x_2028_);
v___x_2030_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_2031_ = lean_float_div(v___x_2029_, v___x_2030_);
v___y_2020_ = v___x_2031_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; double v___x_2034_; 
v___x_2032_ = l_Lean_trace_profiler_threshold;
v___x_2033_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_1929_, v___x_2032_);
v___x_2034_ = lean_float_of_nat(v___x_2033_);
v___y_2020_ = v___x_2034_;
goto v___jp_2019_;
}
}
v___jp_1963_:
{
uint8_t v_result_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v_result_1966_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_fst_1937_);
v___x_1967_ = l_Lean_TraceResult_toEmoji(v_result_1966_);
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 7);
lean_ctor_set(v___x_1959_, 1, v___x_1969_);
lean_ctor_set(v___x_1959_, 0, v___x_1968_);
v___x_1971_ = v___x_1959_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v_m_1973_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v_a_1965_);
lean_ctor_set(v___x_1940_, 0, v___x_1971_);
v_m_1973_ = v___x_1940_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_a_1965_);
v_m_1973_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; double v___x_1976_; lean_object* v_data_1977_; 
v___x_1974_ = lean_box(v_result_1966_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1928_);
lean_inc_ref(v___x_1975_);
lean_inc(v_cls_1926_);
v_data_1977_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1977_, 0, v_cls_1926_);
lean_ctor_set(v_data_1977_, 1, v___x_1975_);
lean_ctor_set(v_data_1977_, 2, v_tag_1928_);
lean_ctor_set_float(v_data_1977_, sizeof(void*)*3, v___x_1976_);
lean_ctor_set_float(v_data_1977_, sizeof(void*)*3 + 8, v___x_1976_);
lean_ctor_set_uint8(v_data_1977_, sizeof(void*)*3 + 16, v_collapsed_1927_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v___x_1975_);
lean_dec(v_snd_1957_);
lean_dec(v_fst_1956_);
lean_dec_ref(v_tag_1928_);
lean_dec(v_cls_1926_);
v___y_1943_ = v_m_1973_;
v___y_1944_ = v___y_1964_;
v_data_1945_ = v_data_1977_;
goto v___jp_1942_;
}
else
{
lean_object* v_data_1978_; double v___x_1979_; double v___x_1980_; 
lean_dec_ref(v_data_1977_);
v_data_1978_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1978_, 0, v_cls_1926_);
lean_ctor_set(v_data_1978_, 1, v___x_1975_);
lean_ctor_set(v_data_1978_, 2, v_tag_1928_);
v___x_1979_ = lean_unbox_float(v_fst_1956_);
lean_dec(v_fst_1956_);
lean_ctor_set_float(v_data_1978_, sizeof(void*)*3, v___x_1979_);
v___x_1980_ = lean_unbox_float(v_snd_1957_);
lean_dec(v_snd_1957_);
lean_ctor_set_float(v_data_1978_, sizeof(void*)*3 + 8, v___x_1980_);
lean_ctor_set_uint8(v_data_1978_, sizeof(void*)*3 + 16, v_collapsed_1927_);
v___y_1943_ = v_m_1973_;
v___y_1944_ = v___y_1964_;
v_data_1945_ = v_data_1978_;
goto v___jp_1942_;
}
}
}
}
v___jp_1983_:
{
lean_object* v_ref_1984_; lean_object* v___x_1985_; 
v_ref_1984_ = lean_ctor_get(v___y_1934_, 5);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
lean_inc(v_fst_1937_);
v___x_1985_ = lean_apply_4(v_msg_1932_, v_fst_1937_, v___y_1934_, v___y_1935_, lean_box(0));
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v___x_1985_);
v___y_1964_ = v_ref_1984_;
v_a_1965_ = v_a_1986_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref(v___x_1985_);
v___x_1987_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_1964_ = v_ref_1984_;
v_a_1965_ = v___x_1987_;
goto v___jp_1963_;
}
}
v___jp_1988_:
{
if (v_clsEnabled_1930_ == 0)
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v_traceState_1991_; lean_object* v_env_1992_; lean_object* v_nextMacroScope_1993_; lean_object* v_ngen_1994_; lean_object* v_auxDeclNGen_1995_; lean_object* v_cache_1996_; lean_object* v_messages_1997_; lean_object* v_infoState_1998_; lean_object* v_snapshotTasks_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2018_; 
lean_del_object(v___x_1959_);
lean_dec(v_snd_1957_);
lean_dec(v_fst_1956_);
lean_del_object(v___x_1940_);
lean_dec_ref(v_msg_1932_);
lean_dec_ref(v_tag_1928_);
lean_dec(v_cls_1926_);
v___x_1990_ = lean_st_ref_take(v___y_1935_);
v_traceState_1991_ = lean_ctor_get(v___x_1990_, 4);
v_env_1992_ = lean_ctor_get(v___x_1990_, 0);
v_nextMacroScope_1993_ = lean_ctor_get(v___x_1990_, 1);
v_ngen_1994_ = lean_ctor_get(v___x_1990_, 2);
v_auxDeclNGen_1995_ = lean_ctor_get(v___x_1990_, 3);
v_cache_1996_ = lean_ctor_get(v___x_1990_, 5);
v_messages_1997_ = lean_ctor_get(v___x_1990_, 6);
v_infoState_1998_ = lean_ctor_get(v___x_1990_, 7);
v_snapshotTasks_1999_ = lean_ctor_get(v___x_1990_, 8);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snapshotTasks_1999_);
lean_inc(v_infoState_1998_);
lean_inc(v_messages_1997_);
lean_inc(v_cache_1996_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1995_);
lean_inc(v_ngen_1994_);
lean_inc(v_nextMacroScope_1993_);
lean_inc(v_env_1992_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
uint64_t v_tid_2003_; lean_object* v_traces_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2017_; 
v_tid_2003_ = lean_ctor_get_uint64(v_traceState_1991_, sizeof(void*)*1);
v_traces_2004_ = lean_ctor_get(v_traceState_1991_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_traceState_1991_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2006_ = v_traceState_1991_;
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_traces_2004_);
lean_dec(v_traceState_1991_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1931_, v_traces_2004_);
lean_dec_ref(v_traces_2004_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
lean_ctor_set_uint64(v_reuseFailAlloc_2016_, sizeof(void*)*1, v_tid_2003_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2010_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_env_1992_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_nextMacroScope_1993_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_ngen_1994_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_auxDeclNGen_1995_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v_cache_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_messages_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_infoState_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_snapshotTasks_1999_);
v___x_2012_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_st_ref_set(v___y_1935_, v___x_2012_);
v___x_2014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_1937_);
return v___x_2014_;
}
}
}
}
}
else
{
goto v___jp_1983_;
}
}
else
{
goto v___jp_1983_;
}
}
v___jp_2019_:
{
double v___x_2021_; double v___x_2022_; double v___x_2023_; uint8_t v___x_2024_; 
v___x_2021_ = lean_unbox_float(v_snd_1957_);
v___x_2022_ = lean_unbox_float(v_fst_1956_);
v___x_2023_ = lean_float_sub(v___x_2021_, v___x_2022_);
v___x_2024_ = lean_float_decLt(v___y_2020_, v___x_2023_);
v___y_1989_ = v___x_2024_;
goto v___jp_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1___boxed(lean_object* v_cls_2037_, lean_object* v_collapsed_2038_, lean_object* v_tag_2039_, lean_object* v_opts_2040_, lean_object* v_clsEnabled_2041_, lean_object* v_oldTraces_2042_, lean_object* v_msg_2043_, lean_object* v_resStartStop_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_collapsed_boxed_2048_; uint8_t v_clsEnabled_boxed_2049_; lean_object* v_res_2050_; 
v_collapsed_boxed_2048_ = lean_unbox(v_collapsed_2038_);
v_clsEnabled_boxed_2049_ = lean_unbox(v_clsEnabled_2041_);
v_res_2050_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v_cls_2037_, v_collapsed_boxed_2048_, v_tag_2039_, v_opts_2040_, v_clsEnabled_boxed_2049_, v_oldTraces_2042_, v_msg_2043_, v_resStartStop_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_opts_2040_);
return v_res_2050_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(lean_object* v_e_2051_){
_start:
{
if (lean_obj_tag(v_e_2051_) == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = 2;
return v___x_2052_;
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = 0;
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4___boxed(lean_object* v_e_2054_){
_start:
{
uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_res_2055_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_e_2054_);
lean_dec_ref(v_e_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(lean_object* v_cls_2057_, uint8_t v_collapsed_2058_, lean_object* v_tag_2059_, lean_object* v_opts_2060_, uint8_t v_clsEnabled_2061_, lean_object* v_oldTraces_2062_, lean_object* v_msg_2063_, lean_object* v_resStartStop_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2159_; 
v_fst_2068_ = lean_ctor_get(v_resStartStop_2064_, 0);
v_snd_2069_ = lean_ctor_get(v_resStartStop_2064_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_resStartStop_2064_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2071_ = v_resStartStop_2064_;
v_isShared_2072_ = v_isSharedCheck_2159_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v_resStartStop_2064_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2159_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v_data_2076_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2158_; 
v_fst_2079_ = lean_ctor_get(v_snd_2069_, 0);
v_snd_2080_ = lean_ctor_get(v_snd_2069_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_snd_2069_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2082_ = v_snd_2069_;
v_isShared_2083_ = v_isSharedCheck_2158_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_snd_2069_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2158_;
goto v_resetjp_2081_;
}
v___jp_2073_:
{
lean_object* v___x_2077_; 
lean_inc(v___y_2075_);
v___x_2077_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__5(v_oldTraces_2062_, v_data_2076_, v___y_2075_, v___y_2074_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2078_; 
lean_dec_ref(v___x_2077_);
v___x_2078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_2068_);
return v___x_2078_;
}
else
{
lean_dec(v_fst_2068_);
return v___x_2077_;
}
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; lean_object* v___y_2087_; lean_object* v_a_2088_; uint8_t v___y_2112_; double v___y_2143_; 
v___x_2084_ = l_Lean_trace_profiler;
v___x_2085_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_2060_, v___x_2084_);
if (v___x_2085_ == 0)
{
v___y_2112_ = v___x_2085_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2149_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_opts_2060_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; lean_object* v___x_2151_; double v___x_2152_; double v___x_2153_; double v___x_2154_; 
v___x_2150_ = l_Lean_trace_profiler_threshold;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_2060_, v___x_2150_);
v___x_2152_ = lean_float_of_nat(v___x_2151_);
v___x_2153_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__4);
v___x_2154_ = lean_float_div(v___x_2152_, v___x_2153_);
v___y_2143_ = v___x_2154_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; double v___x_2157_; 
v___x_2155_ = l_Lean_trace_profiler_threshold;
v___x_2156_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__7(v_opts_2060_, v___x_2155_);
v___x_2157_ = lean_float_of_nat(v___x_2156_);
v___y_2143_ = v___x_2157_;
goto v___jp_2142_;
}
}
v___jp_2086_:
{
uint8_t v_result_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v_result_2089_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_fst_2068_);
v___x_2090_ = l_Lean_TraceResult_toEmoji(v_result_2089_);
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
v___x_2092_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__1);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 7);
lean_ctor_set(v___x_2082_, 1, v___x_2092_);
lean_ctor_set(v___x_2082_, 0, v___x_2091_);
v___x_2094_ = v___x_2082_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v_m_2096_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 7);
lean_ctor_set(v___x_2071_, 1, v_a_2088_);
lean_ctor_set(v___x_2071_, 0, v___x_2094_);
v_m_2096_ = v___x_2071_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_a_2088_);
v_m_2096_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; double v___x_2099_; lean_object* v_data_2100_; 
v___x_2097_ = lean_box(v_result_2089_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2059_);
lean_inc_ref(v___x_2098_);
lean_inc(v_cls_2057_);
v_data_2100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2100_, 0, v_cls_2057_);
lean_ctor_set(v_data_2100_, 1, v___x_2098_);
lean_ctor_set(v_data_2100_, 2, v_tag_2059_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3, v___x_2099_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3 + 8, v___x_2099_);
lean_ctor_set_uint8(v_data_2100_, sizeof(void*)*3 + 16, v_collapsed_2058_);
if (v___x_2085_ == 0)
{
lean_dec_ref(v___x_2098_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec_ref(v_tag_2059_);
lean_dec(v_cls_2057_);
v___y_2074_ = v_m_2096_;
v___y_2075_ = v___y_2087_;
v_data_2076_ = v_data_2100_;
goto v___jp_2073_;
}
else
{
lean_object* v_data_2101_; double v___x_2102_; double v___x_2103_; 
lean_dec_ref(v_data_2100_);
v_data_2101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2101_, 0, v_cls_2057_);
lean_ctor_set(v_data_2101_, 1, v___x_2098_);
lean_ctor_set(v_data_2101_, 2, v_tag_2059_);
v___x_2102_ = lean_unbox_float(v_fst_2079_);
lean_dec(v_fst_2079_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3, v___x_2102_);
v___x_2103_ = lean_unbox_float(v_snd_2080_);
lean_dec(v_snd_2080_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3 + 8, v___x_2103_);
lean_ctor_set_uint8(v_data_2101_, sizeof(void*)*3 + 16, v_collapsed_2058_);
v___y_2074_ = v_m_2096_;
v___y_2075_ = v___y_2087_;
v_data_2076_ = v_data_2101_;
goto v___jp_2073_;
}
}
}
}
v___jp_2106_:
{
lean_object* v_ref_2107_; lean_object* v___x_2108_; 
v_ref_2107_ = lean_ctor_get(v___y_2065_, 5);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v_fst_2068_);
v___x_2108_ = lean_apply_4(v_msg_2063_, v_fst_2068_, v___y_2065_, v___y_2066_, lean_box(0));
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___y_2087_ = v_ref_2107_;
v_a_2088_ = v_a_2109_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2110_; 
lean_dec_ref(v___x_2108_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___closed__3);
v___y_2087_ = v_ref_2107_;
v_a_2088_ = v___x_2110_;
goto v___jp_2086_;
}
}
v___jp_2111_:
{
if (v_clsEnabled_2061_ == 0)
{
if (v___y_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v_traceState_2114_; lean_object* v_env_2115_; lean_object* v_nextMacroScope_2116_; lean_object* v_ngen_2117_; lean_object* v_auxDeclNGen_2118_; lean_object* v_cache_2119_; lean_object* v_messages_2120_; lean_object* v_infoState_2121_; lean_object* v_snapshotTasks_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2141_; 
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2071_);
lean_dec_ref(v_msg_2063_);
lean_dec_ref(v_tag_2059_);
lean_dec(v_cls_2057_);
v___x_2113_ = lean_st_ref_take(v___y_2066_);
v_traceState_2114_ = lean_ctor_get(v___x_2113_, 4);
v_env_2115_ = lean_ctor_get(v___x_2113_, 0);
v_nextMacroScope_2116_ = lean_ctor_get(v___x_2113_, 1);
v_ngen_2117_ = lean_ctor_get(v___x_2113_, 2);
v_auxDeclNGen_2118_ = lean_ctor_get(v___x_2113_, 3);
v_cache_2119_ = lean_ctor_get(v___x_2113_, 5);
v_messages_2120_ = lean_ctor_get(v___x_2113_, 6);
v_infoState_2121_ = lean_ctor_get(v___x_2113_, 7);
v_snapshotTasks_2122_ = lean_ctor_get(v___x_2113_, 8);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2141_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snapshotTasks_2122_);
lean_inc(v_infoState_2121_);
lean_inc(v_messages_2120_);
lean_inc(v_cache_2119_);
lean_inc(v_traceState_2114_);
lean_inc(v_auxDeclNGen_2118_);
lean_inc(v_ngen_2117_);
lean_inc(v_nextMacroScope_2116_);
lean_inc(v_env_2115_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2141_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
uint64_t v_tid_2126_; lean_object* v_traces_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v_tid_2126_ = lean_ctor_get_uint64(v_traceState_2114_, sizeof(void*)*1);
v_traces_2127_ = lean_ctor_get(v_traceState_2114_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_traceState_2114_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2129_ = v_traceState_2114_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_traces_2127_);
lean_dec(v_traceState_2114_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2062_, v_traces_2127_);
lean_dec_ref(v_traces_2127_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2131_);
lean_ctor_set_uint64(v_reuseFailAlloc_2139_, sizeof(void*)*1, v_tid_2126_);
v___x_2133_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 4, v___x_2133_);
v___x_2135_ = v___x_2124_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_env_2115_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_nextMacroScope_2116_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_ngen_2117_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_auxDeclNGen_2118_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2138_, 5, v_cache_2119_);
lean_ctor_set(v_reuseFailAlloc_2138_, 6, v_messages_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 7, v_infoState_2121_);
lean_ctor_set(v_reuseFailAlloc_2138_, 8, v_snapshotTasks_2122_);
v___x_2135_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_st_ref_set(v___y_2066_, v___x_2135_);
v___x_2137_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3_spec__6___redArg(v_fst_2068_);
return v___x_2137_;
}
}
}
}
}
else
{
goto v___jp_2106_;
}
}
else
{
goto v___jp_2106_;
}
}
v___jp_2142_:
{
double v___x_2144_; double v___x_2145_; double v___x_2146_; uint8_t v___x_2147_; 
v___x_2144_ = lean_unbox_float(v_snd_2080_);
v___x_2145_ = lean_unbox_float(v_fst_2079_);
v___x_2146_ = lean_float_sub(v___x_2144_, v___x_2145_);
v___x_2147_ = lean_float_decLt(v___y_2143_, v___x_2146_);
v___y_2112_ = v___x_2147_;
goto v___jp_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2___boxed(lean_object* v_cls_2160_, lean_object* v_collapsed_2161_, lean_object* v_tag_2162_, lean_object* v_opts_2163_, lean_object* v_clsEnabled_2164_, lean_object* v_oldTraces_2165_, lean_object* v_msg_2166_, lean_object* v_resStartStop_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v_collapsed_boxed_2171_; uint8_t v_clsEnabled_boxed_2172_; lean_object* v_res_2173_; 
v_collapsed_boxed_2171_ = lean_unbox(v_collapsed_2161_);
v_clsEnabled_boxed_2172_ = lean_unbox(v_clsEnabled_2164_);
v_res_2173_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v_cls_2160_, v_collapsed_boxed_2171_, v_tag_2162_, v_opts_2163_, v_clsEnabled_boxed_2172_, v_oldTraces_2165_, v_msg_2166_, v_resStartStop_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec_ref(v_opts_2163_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object* v___f_2174_, lean_object* v_lratPath_2175_, uint8_t v_trimProofs_2176_, lean_object* v___f_2177_, lean_object* v_solver_2178_, lean_object* v_timeout_2179_, uint8_t v_binaryProofs_2180_, uint8_t v_solverMode_2181_, lean_object* v___f_2182_, lean_object* v___f_2183_, lean_object* v_cnfHandle_2184_, lean_object* v_cnfPath_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___y_2190_; lean_object* v_options_2208_; lean_object* v_ref_2209_; lean_object* v_inheritedTraceOptions_2210_; uint8_t v_hasTrace_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; uint8_t v___y_2219_; lean_object* v_a_2220_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; lean_object* v_a_2237_; lean_object* v___y_2247_; uint8_t v___y_2248_; lean_object* v___y_2290_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v_a_2326_; lean_object* v___y_2339_; uint8_t v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v_a_2343_; lean_object* v___y_2353_; uint8_t v___y_2354_; lean_object* v___y_2403_; 
v_options_2208_ = lean_ctor_get(v___y_2186_, 2);
v_ref_2209_ = lean_ctor_get(v___y_2186_, 5);
v_inheritedTraceOptions_2210_ = lean_ctor_get(v___y_2186_, 13);
v_hasTrace_2211_ = lean_ctor_get_uint8(v_options_2208_, sizeof(void*)*1);
v___x_2212_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_2213_ = 1;
v___x_2214_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_2211_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___f_2183_);
v___x_2412_ = l_IO_lazyPure___redArg(v___f_2182_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = lean_io_prim_handle_put_str(v_cnfHandle_2184_, v_a_2413_);
lean_dec(v_a_2413_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v___x_2414_);
v___x_2415_ = lean_io_prim_handle_flush(v_cnfHandle_2184_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref(v___x_2415_);
goto v___jp_2395_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2420_ = lean_io_error_to_string(v_a_2416_);
v___x_2421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
v___x_2422_ = l_Lean_MessageData_ofFormat(v___x_2421_);
lean_inc(v_ref_2209_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v_ref_2209_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2423_);
v___x_2425_ = v___x_2418_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2428_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2430_ = v___x_2414_;
v_isShared_2431_ = v_isSharedCheck_2439_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2414_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2439_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2432_ = lean_io_error_to_string(v_a_2428_);
v___x_2433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
v___x_2434_ = l_Lean_MessageData_ofFormat(v___x_2433_);
lean_inc(v_ref_2209_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_ref_2209_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2435_);
v___x_2437_ = v___x_2430_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2440_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2442_ = v___x_2412_;
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2412_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2444_ = lean_io_error_to_string(v_a_2440_);
v___x_2445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
v___x_2446_ = l_Lean_MessageData_ofFormat(v___x_2445_);
lean_inc(v_ref_2209_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_ref_2209_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2447_);
v___x_2449_ = v___x_2442_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v_a_2457_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v_a_2472_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v_a_2477_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v_a_2489_; 
v___x_2452_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2210_, v_options_2208_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = l_Lean_trace_profiler;
v___x_2589_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2208_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v___f_2183_);
v___x_2590_ = l_IO_lazyPure___redArg(v___f_2182_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = lean_io_prim_handle_put_str(v_cnfHandle_2184_, v_a_2591_);
lean_dec(v_a_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v___x_2592_);
v___x_2593_ = lean_io_prim_handle_flush(v_cnfHandle_2184_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_dec_ref(v___x_2593_);
goto v___jp_2395_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2605_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2598_ = lean_io_error_to_string(v_a_2594_);
v___x_2599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
v___x_2600_ = l_Lean_MessageData_ofFormat(v___x_2599_);
lean_inc(v_ref_2209_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v_ref_2209_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2601_);
v___x_2603_ = v___x_2596_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2606_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2608_ = v___x_2592_;
v_isShared_2609_ = v_isSharedCheck_2617_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2592_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2617_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2610_ = lean_io_error_to_string(v_a_2606_);
v___x_2611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
v___x_2612_ = l_Lean_MessageData_ofFormat(v___x_2611_);
lean_inc(v_ref_2209_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_ref_2209_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2613_);
v___x_2615_ = v___x_2608_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2618_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2620_ = v___x_2590_;
v_isShared_2621_ = v_isSharedCheck_2629_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2590_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2629_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2622_ = lean_io_error_to_string(v_a_2618_);
v___x_2623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
v___x_2624_ = l_Lean_MessageData_ofFormat(v___x_2623_);
lean_inc(v_ref_2209_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_ref_2209_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2625_);
v___x_2627_ = v___x_2620_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
goto v___jp_2491_;
}
}
else
{
goto v___jp_2491_;
}
v___jp_2454_:
{
lean_object* v___x_2458_; double v___x_2459_; double v___x_2460_; double v___x_2461_; double v___x_2462_; double v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2458_ = lean_io_mono_nanos_now();
v___x_2459_ = lean_float_of_nat(v___y_2456_);
v___x_2460_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2461_ = lean_float_div(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_float_of_nat(v___x_2458_);
v___x_2463_ = lean_float_div(v___x_2462_, v___x_2460_);
v___x_2464_ = lean_box_float(v___x_2461_);
v___x_2465_ = lean_box_float(v___x_2463_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2457_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2212_, v___x_2213_, v___x_2214_, v_options_2208_, v___x_2453_, v___y_2455_, v___f_2183_, v___x_2467_, v___y_2186_, v___y_2187_);
v___y_2403_ = v___x_2468_;
goto v___jp_2402_;
}
v___jp_2469_:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2472_);
v___y_2455_ = v___y_2470_;
v___y_2456_ = v___y_2471_;
v_a_2457_ = v___x_2473_;
goto v___jp_2454_;
}
v___jp_2474_:
{
lean_object* v___x_2478_; double v___x_2479_; double v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2478_ = lean_io_get_num_heartbeats();
v___x_2479_ = lean_float_of_nat(v___y_2476_);
v___x_2480_ = lean_float_of_nat(v___x_2478_);
v___x_2481_ = lean_box_float(v___x_2479_);
v___x_2482_ = lean_box_float(v___x_2480_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_a_2477_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2212_, v___x_2213_, v___x_2214_, v_options_2208_, v___x_2453_, v___y_2475_, v___f_2183_, v___x_2484_, v___y_2186_, v___y_2187_);
v___y_2403_ = v___x_2485_;
goto v___jp_2402_;
}
v___jp_2486_:
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2489_);
v___y_2475_ = v___y_2487_;
v___y_2476_ = v___y_2488_;
v_a_2477_ = v___x_2490_;
goto v___jp_2474_;
}
v___jp_2491_:
{
lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2492_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2187_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2495_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2208_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_io_mono_nanos_now();
v___x_2497_ = l_IO_lazyPure___redArg(v___f_2182_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = lean_io_prim_handle_put_str(v_cnfHandle_2184_, v_a_2498_);
lean_dec(v_a_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2500_; 
lean_dec_ref(v___x_2499_);
v___x_2500_ = lean_io_prim_handle_flush(v_cnfHandle_2184_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set_tag(v___x_2503_, 1);
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
v___y_2455_ = v_a_2493_;
v___y_2456_ = v___x_2496_;
v_a_2457_ = v___x_2506_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2519_; 
v_a_2509_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2519_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_io_error_to_string(v_a_2509_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 3);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = l_Lean_MessageData_ofFormat(v___x_2515_);
lean_inc(v_ref_2209_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_ref_2209_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___y_2470_ = v_a_2493_;
v___y_2471_ = v___x_2496_;
v_a_2472_ = v___x_2517_;
goto v___jp_2469_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2530_; 
v_a_2520_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2522_ = v___x_2499_;
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2499_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = lean_io_error_to_string(v_a_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 3);
lean_ctor_set(v___x_2522_, 0, v___x_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = l_Lean_MessageData_ofFormat(v___x_2526_);
lean_inc(v_ref_2209_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_ref_2209_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___y_2470_ = v_a_2493_;
v___y_2471_ = v___x_2496_;
v_a_2472_ = v___x_2528_;
goto v___jp_2469_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2541_; 
v_a_2531_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2533_ = v___x_2497_;
v_isShared_2534_ = v_isSharedCheck_2541_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2497_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2541_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_io_error_to_string(v_a_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 3);
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = l_Lean_MessageData_ofFormat(v___x_2537_);
lean_inc(v_ref_2209_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_ref_2209_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___y_2470_ = v_a_2493_;
v___y_2471_ = v___x_2496_;
v_a_2472_ = v___x_2539_;
goto v___jp_2469_;
}
}
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_io_get_num_heartbeats();
v___x_2543_ = l_IO_lazyPure___redArg(v___f_2182_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = lean_io_prim_handle_put_str(v_cnfHandle_2184_, v_a_2544_);
lean_dec(v_a_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v___x_2546_; 
lean_dec_ref(v___x_2545_);
v___x_2546_ = lean_io_prim_handle_flush(v_cnfHandle_2184_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set_tag(v___x_2549_, 1);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
v___y_2475_ = v_a_2493_;
v___y_2476_ = v___x_2542_;
v_a_2477_ = v___x_2552_;
goto v___jp_2474_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2565_; 
v_a_2555_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2557_ = v___x_2546_;
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2546_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_io_error_to_string(v_a_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 3);
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = l_Lean_MessageData_ofFormat(v___x_2561_);
lean_inc(v_ref_2209_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_ref_2209_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___y_2487_ = v_a_2493_;
v___y_2488_ = v___x_2542_;
v_a_2489_ = v___x_2563_;
goto v___jp_2486_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2568_ = v___x_2545_;
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2545_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2576_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_io_error_to_string(v_a_2566_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 3);
lean_ctor_set(v___x_2568_, 0, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = l_Lean_MessageData_ofFormat(v___x_2572_);
lean_inc(v_ref_2209_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_ref_2209_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___y_2487_ = v_a_2493_;
v___y_2488_ = v___x_2542_;
v_a_2489_ = v___x_2574_;
goto v___jp_2486_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2587_; 
v_a_2577_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2579_ = v___x_2543_;
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2543_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_io_error_to_string(v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 3);
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = l_Lean_MessageData_ofFormat(v___x_2583_);
lean_inc(v_ref_2209_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v_ref_2209_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___y_2487_ = v_a_2493_;
v___y_2488_ = v___x_2542_;
v_a_2489_ = v___x_2585_;
goto v___jp_2486_;
}
}
}
}
}
}
v___jp_2189_:
{
if (lean_obj_tag(v___y_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
v_a_2191_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2193_ = v___y_2190_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___y_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_a_2191_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___y_2190_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___y_2190_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___y_2190_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___y_2190_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
v___jp_2215_:
{
lean_object* v___x_2221_; double v___x_2222_; double v___x_2223_; double v___x_2224_; double v___x_2225_; double v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2221_ = lean_io_mono_nanos_now();
v___x_2222_ = lean_float_of_nat(v___y_2216_);
v___x_2223_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2224_ = lean_float_div(v___x_2222_, v___x_2223_);
v___x_2225_ = lean_float_of_nat(v___x_2221_);
v___x_2226_ = lean_float_div(v___x_2225_, v___x_2223_);
v___x_2227_ = lean_box_float(v___x_2224_);
v___x_2228_ = lean_box_float(v___x_2226_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2220_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2212_, v___x_2213_, v___x_2214_, v___y_2218_, v___y_2219_, v___y_2217_, v___f_2174_, v___x_2230_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2231_;
goto v___jp_2189_;
}
v___jp_2232_:
{
lean_object* v___x_2238_; double v___x_2239_; double v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2238_ = lean_io_get_num_heartbeats();
v___x_2239_ = lean_float_of_nat(v___y_2234_);
v___x_2240_ = lean_float_of_nat(v___x_2238_);
v___x_2241_ = lean_box_float(v___x_2239_);
v___x_2242_ = lean_box_float(v___x_2240_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_a_2237_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2212_, v___x_2213_, v___x_2214_, v___y_2235_, v___y_2236_, v___y_2233_, v___f_2174_, v___x_2244_, v___y_2186_, v___y_2187_);
v___y_2190_ = v___x_2245_;
goto v___jp_2189_;
}
v___jp_2246_:
{
lean_object* v___x_2249_; lean_object* v_a_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2249_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2187_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2252_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_2247_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_io_mono_nanos_now();
v___x_2254_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2175_, v_trimProofs_2176_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_lratPath_2175_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set_tag(v___x_2257_, 1);
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
v___y_2216_ = v___x_2253_;
v___y_2217_ = v_a_2250_;
v___y_2218_ = v___y_2247_;
v___y_2219_ = v___y_2248_;
v_a_2220_ = v___x_2260_;
goto v___jp_2215_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2263_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2254_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2254_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set_tag(v___x_2265_, 0);
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
v___y_2216_ = v___x_2253_;
v___y_2217_ = v_a_2250_;
v___y_2218_ = v___y_2247_;
v___y_2219_ = v___y_2248_;
v_a_2220_ = v___x_2268_;
goto v___jp_2215_;
}
}
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_io_get_num_heartbeats();
v___x_2272_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2175_, v_trimProofs_2176_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_lratPath_2175_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 1);
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
v___y_2233_ = v_a_2250_;
v___y_2234_ = v___x_2271_;
v___y_2235_ = v___y_2247_;
v___y_2236_ = v___y_2248_;
v_a_2237_ = v___x_2278_;
goto v___jp_2232_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2272_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2272_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 0);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
v___y_2233_ = v_a_2250_;
v___y_2234_ = v___x_2271_;
v___y_2235_ = v___y_2247_;
v___y_2236_ = v___y_2248_;
v_a_2237_ = v___x_2286_;
goto v___jp_2232_;
}
}
}
}
}
v___jp_2289_:
{
if (lean_obj_tag(v___y_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2312_; 
v_a_2291_ = lean_ctor_get(v___y_2290_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___y_2290_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2293_ = v___y_2290_;
v_isShared_2294_ = v_isSharedCheck_2312_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___y_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2312_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
if (lean_obj_tag(v_a_2291_) == 0)
{
lean_object* v_assignment_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_assignment_2295_ = lean_ctor_get(v_a_2291_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_a_2291_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2297_ = v_a_2291_;
v_isShared_2298_ = v_isSharedCheck_2305_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_assignment_2295_);
lean_dec(v_a_2291_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2305_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_assignment_2295_);
v___x_2300_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2300_);
v___x_2302_ = v___x_2293_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_del_object(v___x_2293_);
lean_dec(v_a_2291_);
if (v_hasTrace_2211_ == 0)
{
lean_object* v___x_2306_; 
lean_dec_ref(v___f_2174_);
v___x_2306_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2175_, v_trimProofs_2176_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_lratPath_2175_);
v___y_2190_ = v___x_2306_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2308_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2210_, v_options_2208_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = l_Lean_trace_profiler;
v___x_2310_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2208_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; 
lean_dec_ref(v___f_2174_);
v___x_2311_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2175_, v_trimProofs_2176_, v___y_2186_, v___y_2187_);
lean_dec_ref(v_lratPath_2175_);
v___y_2190_ = v___x_2311_;
goto v___jp_2189_;
}
else
{
v___y_2247_ = v_options_2208_;
v___y_2248_ = v___x_2308_;
goto v___jp_2246_;
}
}
else
{
v___y_2247_ = v_options_2208_;
v___y_2248_ = v___x_2308_;
goto v___jp_2246_;
}
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2313_ = lean_ctor_get(v___y_2290_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___y_2290_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___y_2290_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___y_2290_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
v___jp_2321_:
{
lean_object* v___x_2327_; double v___x_2328_; double v___x_2329_; double v___x_2330_; double v___x_2331_; double v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2327_ = lean_io_mono_nanos_now();
v___x_2328_ = lean_float_of_nat(v___y_2324_);
v___x_2329_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2330_ = lean_float_div(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_float_of_nat(v___x_2327_);
v___x_2332_ = lean_float_div(v___x_2331_, v___x_2329_);
v___x_2333_ = lean_box_float(v___x_2330_);
v___x_2334_ = lean_box_float(v___x_2332_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2326_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2212_, v___x_2213_, v___x_2214_, v___y_2322_, v___y_2323_, v___y_2325_, v___f_2177_, v___x_2336_, v___y_2186_, v___y_2187_);
v___y_2290_ = v___x_2337_;
goto v___jp_2289_;
}
v___jp_2338_:
{
lean_object* v___x_2344_; double v___x_2345_; double v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2344_ = lean_io_get_num_heartbeats();
v___x_2345_ = lean_float_of_nat(v___y_2342_);
v___x_2346_ = lean_float_of_nat(v___x_2344_);
v___x_2347_ = lean_box_float(v___x_2345_);
v___x_2348_ = lean_box_float(v___x_2346_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2343_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2212_, v___x_2213_, v___x_2214_, v___y_2339_, v___y_2340_, v___y_2341_, v___f_2177_, v___x_2350_, v___y_2186_, v___y_2187_);
v___y_2290_ = v___x_2351_;
goto v___jp_2289_;
}
v___jp_2352_:
{
lean_object* v___x_2355_; lean_object* v_a_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2355_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___redArg(v___y_2187_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2358_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v___y_2353_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_2175_);
v___x_2360_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2178_, v_cnfPath_2185_, v_lratPath_2175_, v_timeout_2179_, v_binaryProofs_2180_, v_solverMode_2181_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
v___y_2322_ = v___y_2353_;
v___y_2323_ = v___y_2354_;
v___y_2324_ = v___x_2359_;
v___y_2325_ = v_a_2356_;
v_a_2326_ = v___x_2366_;
goto v___jp_2321_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2360_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2360_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2322_ = v___y_2353_;
v___y_2323_ = v___y_2354_;
v___y_2324_ = v___x_2359_;
v___y_2325_ = v_a_2356_;
v_a_2326_ = v___x_2374_;
goto v___jp_2321_;
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_2175_);
v___x_2378_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2178_, v_cnfPath_2185_, v_lratPath_2175_, v_timeout_2179_, v_binaryProofs_2180_, v_solverMode_2181_, v___y_2186_, v___y_2187_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 1);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2339_ = v___y_2353_;
v___y_2340_ = v___y_2354_;
v___y_2341_ = v_a_2356_;
v___y_2342_ = v___x_2377_;
v_a_2343_ = v___x_2384_;
goto v___jp_2338_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2378_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2378_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 0);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
v___y_2339_ = v___y_2353_;
v___y_2340_ = v___y_2354_;
v___y_2341_ = v_a_2356_;
v___y_2342_ = v___x_2377_;
v_a_2343_ = v___x_2392_;
goto v___jp_2338_;
}
}
}
}
}
v___jp_2395_:
{
if (v_hasTrace_2211_ == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v___f_2177_);
lean_inc_ref(v_lratPath_2175_);
v___x_2396_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2178_, v_cnfPath_2185_, v_lratPath_2175_, v_timeout_2179_, v_binaryProofs_2180_, v_solverMode_2181_, v___y_2186_, v___y_2187_);
v___y_2290_ = v___x_2396_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12);
v___x_2398_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2210_, v_options_2208_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = l_Lean_trace_profiler;
v___x_2400_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_options_2208_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___f_2177_);
lean_inc_ref(v_lratPath_2175_);
v___x_2401_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2178_, v_cnfPath_2185_, v_lratPath_2175_, v_timeout_2179_, v_binaryProofs_2180_, v_solverMode_2181_, v___y_2186_, v___y_2187_);
v___y_2290_ = v___x_2401_;
goto v___jp_2289_;
}
else
{
v___y_2353_ = v_options_2208_;
v___y_2354_ = v___x_2398_;
goto v___jp_2352_;
}
}
else
{
v___y_2353_ = v_options_2208_;
v___y_2354_ = v___x_2398_;
goto v___jp_2352_;
}
}
}
v___jp_2402_:
{
if (lean_obj_tag(v___y_2403_) == 0)
{
lean_dec_ref(v___y_2403_);
goto v___jp_2395_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v_cnfPath_2185_);
lean_dec_ref(v_solver_2178_);
lean_dec_ref(v___f_2177_);
lean_dec_ref(v_lratPath_2175_);
lean_dec_ref(v___f_2174_);
v_a_2404_ = lean_ctor_get(v___y_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___y_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___y_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___y_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object* v___f_2630_, lean_object* v_lratPath_2631_, lean_object* v_trimProofs_2632_, lean_object* v___f_2633_, lean_object* v_solver_2634_, lean_object* v_timeout_2635_, lean_object* v_binaryProofs_2636_, lean_object* v_solverMode_2637_, lean_object* v___f_2638_, lean_object* v___f_2639_, lean_object* v_cnfHandle_2640_, lean_object* v_cnfPath_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
uint8_t v_trimProofs_boxed_2645_; uint8_t v_binaryProofs_boxed_2646_; uint8_t v_solverMode_boxed_2647_; lean_object* v_res_2648_; 
v_trimProofs_boxed_2645_ = lean_unbox(v_trimProofs_2632_);
v_binaryProofs_boxed_2646_ = lean_unbox(v_binaryProofs_2636_);
v_solverMode_boxed_2647_ = lean_unbox(v_solverMode_2637_);
v_res_2648_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(v___f_2630_, v_lratPath_2631_, v_trimProofs_boxed_2645_, v___f_2633_, v_solver_2634_, v_timeout_2635_, v_binaryProofs_boxed_2646_, v_solverMode_boxed_2647_, v___f_2638_, v___f_2639_, v_cnfHandle_2640_, v_cnfPath_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v_cnfHandle_2640_);
lean_dec(v_timeout_2635_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object* v_cnf_2652_, lean_object* v_solver_2653_, lean_object* v_lratPath_2654_, uint8_t v_trimProofs_2655_, lean_object* v_timeout_2656_, uint8_t v_binaryProofs_2657_, uint8_t v_solverMode_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___f_2662_; lean_object* v___f_2663_; lean_object* v___f_2664_; lean_object* v___f_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___f_2669_; lean_object* v___x_2670_; 
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2662_, 0, v_cnf_2652_);
v___f_2663_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0));
v___f_2664_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1));
v___f_2665_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2));
v___x_2666_ = lean_box(v_trimProofs_2655_);
v___x_2667_ = lean_box(v_binaryProofs_2657_);
v___x_2668_ = lean_box(v_solverMode_2658_);
v___f_2669_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2669_, 0, v___f_2664_);
lean_closure_set(v___f_2669_, 1, v_lratPath_2654_);
lean_closure_set(v___f_2669_, 2, v___x_2666_);
lean_closure_set(v___f_2669_, 3, v___f_2663_);
lean_closure_set(v___f_2669_, 4, v_solver_2653_);
lean_closure_set(v___f_2669_, 5, v_timeout_2656_);
lean_closure_set(v___f_2669_, 6, v___x_2667_);
lean_closure_set(v___f_2669_, 7, v___x_2668_);
lean_closure_set(v___f_2669_, 8, v___f_2662_);
lean_closure_set(v___f_2669_, 9, v___f_2665_);
v___x_2670_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v___f_2669_, v_a_2659_, v_a_2660_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object* v_cnf_2671_, lean_object* v_solver_2672_, lean_object* v_lratPath_2673_, lean_object* v_trimProofs_2674_, lean_object* v_timeout_2675_, lean_object* v_binaryProofs_2676_, lean_object* v_solverMode_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
uint8_t v_trimProofs_boxed_2681_; uint8_t v_binaryProofs_boxed_2682_; uint8_t v_solverMode_boxed_2683_; lean_object* v_res_2684_; 
v_trimProofs_boxed_2681_ = lean_unbox(v_trimProofs_2674_);
v_binaryProofs_boxed_2682_ = lean_unbox(v_binaryProofs_2676_);
v_solverMode_boxed_2683_ = lean_unbox(v_solverMode_2677_);
v_res_2684_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(v_cnf_2671_, v_solver_2672_, v_lratPath_2673_, v_trimProofs_boxed_2681_, v_timeout_2675_, v_binaryProofs_boxed_2682_, v_solverMode_boxed_2683_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2684_;
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
