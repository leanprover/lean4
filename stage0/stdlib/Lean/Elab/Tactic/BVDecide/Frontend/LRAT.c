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
extern lean_object* l_Lean_instToExprNat;
lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Using SAT solver at '"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_15_ = lean_panic_fn(v___x_14_, v_msg_13_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(lean_object* v_cls_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_options_87_; uint8_t v_hasTrace_88_; 
v_options_87_ = lean_ctor_get(v___y_85_, 2);
v_hasTrace_88_ = lean_ctor_get_uint8(v_options_87_, sizeof(void*)*1);
if (v_hasTrace_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_cls_84_);
v___x_89_ = lean_box(v_hasTrace_88_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v_inheritedTraceOptions_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_inheritedTraceOptions_91_ = lean_ctor_get(v___y_85_, 13);
v___x_92_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_93_ = l_Lean_Name_append(v___x_92_, v_cls_84_);
v___x_94_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_91_, v_options_87_, v___x_93_);
lean_dec(v___x_93_);
v___x_95_ = lean_box(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___boxed(lean_object* v_cls_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_97_, v___y_98_);
lean_dec_ref(v___y_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(lean_object* v_cls_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v_cls_101_, v___y_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___boxed(lean_object* v_cls_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0(v_cls_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; lean_object* v_env_126_; lean_object* v___x_127_; lean_object* v_mctx_128_; lean_object* v_lctx_129_; lean_object* v_options_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_125_ = lean_st_ref_get(v___y_123_);
v_env_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc_ref(v_env_126_);
lean_dec(v___x_125_);
v___x_127_ = lean_st_ref_get(v___y_121_);
v_mctx_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref(v_mctx_128_);
lean_dec(v___x_127_);
v_lctx_129_ = lean_ctor_get(v___y_120_, 2);
v_options_130_ = lean_ctor_get(v___y_122_, 2);
lean_inc_ref(v_options_130_);
lean_inc_ref(v_lctx_129_);
v___x_131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_131_, 0, v_env_126_);
lean_ctor_set(v___x_131_, 1, v_mctx_128_);
lean_ctor_set(v___x_131_, 2, v_lctx_129_);
lean_ctor_set(v___x_131_, 3, v_options_130_);
v___x_132_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_msgData_119_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1___boxed(lean_object* v_msgData_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1(v_msgData_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; double v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_float_of_nat(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg(lean_object* v_cls_145_, lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_198_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 5);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1_spec__1(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_198_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_traceState_159_; lean_object* v_env_160_; lean_object* v_nextMacroScope_161_; lean_object* v_ngen_162_; lean_object* v_auxDeclNGen_163_; lean_object* v_cache_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v___x_158_ = lean_st_ref_take(v___y_150_);
v_traceState_159_ = lean_ctor_get(v___x_158_, 4);
v_env_160_ = lean_ctor_get(v___x_158_, 0);
v_nextMacroScope_161_ = lean_ctor_get(v___x_158_, 1);
v_ngen_162_ = lean_ctor_get(v___x_158_, 2);
v_auxDeclNGen_163_ = lean_ctor_get(v___x_158_, 3);
v_cache_164_ = lean_ctor_get(v___x_158_, 5);
v_messages_165_ = lean_ctor_get(v___x_158_, 6);
v_infoState_166_ = lean_ctor_get(v___x_158_, 7);
v_snapshotTasks_167_ = lean_ctor_get(v___x_158_, 8);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_197_ == 0)
{
v___x_169_ = v___x_158_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snapshotTasks_167_);
lean_inc(v_infoState_166_);
lean_inc(v_messages_165_);
lean_inc(v_cache_164_);
lean_inc(v_traceState_159_);
lean_inc(v_auxDeclNGen_163_);
lean_inc(v_ngen_162_);
lean_inc(v_nextMacroScope_161_);
lean_inc(v_env_160_);
lean_dec(v___x_158_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint64_t v_tid_171_; lean_object* v_traces_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_196_; 
v_tid_171_ = lean_ctor_get_uint64(v_traceState_159_, sizeof(void*)*1);
v_traces_172_ = lean_ctor_get(v_traceState_159_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_traceState_159_);
if (v_isSharedCheck_196_ == 0)
{
v___x_174_ = v_traceState_159_;
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_traces_172_);
lean_dec(v_traceState_159_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; double v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
v___x_178_ = 0;
v___x_179_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_180_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_180_, 0, v_cls_145_);
lean_ctor_set(v___x_180_, 1, v___x_176_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3, v___x_177_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3 + 8, v___x_177_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*3 + 16, v___x_178_);
v___x_181_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1));
v___x_182_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v_a_154_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_inc(v_ref_152_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_ref_152_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_PersistentArray_push___redArg(v_traces_172_, v___x_183_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_184_);
v___x_186_ = v___x_174_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_184_);
lean_ctor_set_uint64(v_reuseFailAlloc_195_, sizeof(void*)*1, v_tid_171_);
v___x_186_ = v_reuseFailAlloc_195_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 4, v___x_186_);
v___x_188_ = v___x_169_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_env_160_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_nextMacroScope_161_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_ngen_162_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_auxDeclNGen_163_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 5, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_194_, 6, v_messages_165_);
lean_ctor_set(v_reuseFailAlloc_194_, 7, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_194_, 8, v_snapshotTasks_167_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_st_ref_set(v___y_150_, v___x_188_);
v___x_190_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_190_);
v___x_192_ = v___x_156_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___boxed(lean_object* v_cls_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg(v_cls_199_, v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__10));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__12));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object* v_lratPath_229_, lean_object* v_config_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__1));
v___x_239_ = l_Lean_Elab_Term_mkAuxName(v___x_238_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__3));
v___x_242_ = l_Lean_Elab_Term_mkAuxName(v___x_241_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v___x_242_);
v___x_244_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__5));
v___x_245_ = l_Lean_Elab_Term_mkAuxName(v___x_244_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver___redArg(v_a_235_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_282_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_282_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_282_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_282_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_281_; 
v___x_257_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_258_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg(v___x_257_, v_a_235_);
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_281_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_281_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_281_;
goto v_resetjp_260_;
}
v___jp_252_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_253_, 0, v_a_240_);
lean_ctor_set(v___x_253_, 1, v_a_243_);
lean_ctor_set(v___x_253_, 2, v_a_246_);
lean_ctor_set(v___x_253_, 3, v_a_248_);
lean_ctor_set(v___x_253_, 4, v_lratPath_229_);
lean_ctor_set(v___x_253_, 5, v_config_230_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = lean_unbox(v_a_259_);
lean_dec(v_a_259_);
if (v___x_263_ == 0)
{
lean_del_object(v___x_261_);
goto v___jp_252_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__11);
lean_inc(v_a_248_);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 3);
lean_ctor_set(v___x_261_, 0, v_a_248_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_248_);
v___x_266_ = v_reuseFailAlloc_280_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_264_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__13);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg(v___x_257_, v___x_270_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_dec_ref(v___x_271_);
goto v___jp_252_;
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_del_object(v___x_250_);
lean_dec(v_a_248_);
lean_dec(v_a_246_);
lean_dec(v_a_243_);
lean_dec(v_a_240_);
lean_dec_ref(v_config_230_);
lean_dec_ref(v_lratPath_229_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
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
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_246_);
lean_dec(v_a_243_);
lean_dec(v_a_240_);
lean_dec_ref(v_config_230_);
lean_dec_ref(v_lratPath_229_);
v_a_283_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_247_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_247_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_243_);
lean_dec(v_a_240_);
lean_dec_ref(v_config_230_);
lean_dec_ref(v_lratPath_229_);
v_a_291_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_245_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_245_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_a_240_);
lean_dec_ref(v_config_230_);
lean_dec_ref(v_lratPath_229_);
v_a_299_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_242_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_242_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v_config_230_);
lean_dec_ref(v_lratPath_229_);
v_a_307_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_239_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_239_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___boxed(lean_object* v_lratPath_315_, lean_object* v_config_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(v_lratPath_315_, v_config_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1(lean_object* v_cls_325_, lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg(v_cls_325_, v_msg_326_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___boxed(lean_object* v_cls_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1(v_cls_335_, v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_352_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__1));
v___x_353_ = l_Lean_mkConst(v___x_352_, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_box(0);
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v___x_359_ = l_Lean_mkConst(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_beta_362_; 
v___x_360_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__6);
v___x_361_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_beta_362_ = l_Lean_Expr_app___override(v___x_361_, v___x_360_);
return v_beta_362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_alpha_368_; 
v___x_366_ = lean_box(0);
v___x_367_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__9));
v_alpha_368_ = l_Lean_mkConst(v___x_367_, v___x_366_);
return v_alpha_368_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_385_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__16));
v___x_386_ = l_Lean_mkConst(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__21));
v___x_394_ = l_Lean_mkConst(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__24));
v___x_401_ = l_Lean_mkConst(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26(void){
_start:
{
lean_object* v_alpha_402_; lean_object* v___x_403_; lean_object* v_nil_404_; 
v_alpha_402_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_403_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_404_ = l_Lean_Expr_app___override(v___x_403_, v_alpha_402_);
return v_nil_404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__2));
v___x_410_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__28));
v___x_411_ = l_Lean_mkConst(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30(void){
_start:
{
lean_object* v_alpha_412_; lean_object* v___x_413_; lean_object* v_cons_414_; 
v_alpha_412_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_414_ = l_Lean_Expr_app___override(v___x_413_, v_alpha_412_);
return v_cons_414_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_424_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__32));
v___x_425_ = l_Lean_mkConst(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_type_428_; 
v___x_426_ = lean_box(0);
v___x_427_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__5));
v_type_428_ = l_Lean_Expr_const___override(v___x_427_, v___x_426_);
return v_type_428_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35(void){
_start:
{
lean_object* v_type_429_; lean_object* v___x_430_; lean_object* v_nil_431_; 
v_type_429_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_431_ = l_Lean_Expr_app___override(v___x_430_, v_type_429_);
return v_nil_431_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36(void){
_start:
{
lean_object* v_type_432_; lean_object* v___x_433_; lean_object* v_cons_434_; 
v_type_432_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_433_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_434_ = l_Lean_Expr_app___override(v___x_433_, v_type_432_);
return v_cons_434_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_444_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__38));
v___x_445_ = l_Lean_mkConst(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_00_u03b2Type_451_; 
v___x_449_ = lean_box(0);
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__41));
v_00_u03b2Type_451_ = l_Lean_mkConst(v___x_450_, v___x_449_);
return v_00_u03b2Type_451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_458_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__45));
v___x_459_ = l_Lean_mkConst(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47(void){
_start:
{
lean_object* v_alpha_460_; lean_object* v___x_461_; lean_object* v_00_u03b2Type_462_; 
v_alpha_460_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_461_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__3);
v_00_u03b2Type_462_ = l_Lean_Expr_app___override(v___x_461_, v_alpha_460_);
return v_00_u03b2Type_462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__48));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50(void){
_start:
{
lean_object* v_00_u03b2Type_468_; lean_object* v_alpha_469_; lean_object* v___x_470_; lean_object* v_type_471_; 
v_00_u03b2Type_468_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__47);
v_alpha_469_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
v___x_470_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__49);
v_type_471_ = l_Lean_mkAppB(v___x_470_, v_alpha_469_, v_00_u03b2Type_468_);
return v_type_471_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51(void){
_start:
{
lean_object* v_type_472_; lean_object* v___x_473_; lean_object* v_nil_474_; 
v_type_472_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_473_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__25);
v_nil_474_ = l_Lean_Expr_app___override(v___x_473_, v_type_472_);
return v_nil_474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52(void){
_start:
{
lean_object* v_type_475_; lean_object* v___x_476_; lean_object* v_cons_477_; 
v_type_475_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v___x_476_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__29);
v_cons_477_ = l_Lean_Expr_app___override(v___x_476_, v_type_475_);
return v_cons_477_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_box(0);
v___x_483_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__54));
v___x_484_ = l_Lean_mkConst(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__57));
v___x_491_ = l_Lean_mkConst(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__17));
v___x_501_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__60));
v___x_502_ = l_Lean_mkConst(v___x_501_, v___x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0(lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v_action_506_){
_start:
{
lean_object* v_beta_507_; lean_object* v_alpha_508_; 
v_beta_507_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__7);
v_alpha_508_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__10);
switch(lean_obj_tag(v_action_506_))
{
case 0:
{
lean_object* v_id_509_; lean_object* v_rupHints_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_nil_514_; lean_object* v_cons_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec_ref(v___x_505_);
lean_dec_ref(v___x_504_);
v_id_509_ = lean_ctor_get(v_action_506_, 0);
lean_inc(v_id_509_);
v_rupHints_510_ = lean_ctor_get(v_action_506_, 1);
lean_inc_ref(v_rupHints_510_);
lean_dec_ref(v_action_506_);
v___x_511_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__18);
v___x_512_ = l_Lean_mkNatLit(v_id_509_);
v___x_513_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_514_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_515_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_516_ = lean_array_to_list(v_rupHints_510_);
v___x_517_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_503_, v_nil_514_, v_cons_515_, v___x_516_);
v___x_518_ = l_Lean_mkAppB(v___x_513_, v_alpha_508_, v___x_517_);
v___x_519_ = l_Lean_mkApp4(v___x_511_, v_beta_507_, v_alpha_508_, v___x_512_, v___x_518_);
return v___x_519_;
}
case 1:
{
lean_object* v_id_520_; lean_object* v_c_521_; lean_object* v_rupHints_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_type_525_; lean_object* v___x_526_; lean_object* v_nil_527_; lean_object* v_cons_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_nil_532_; lean_object* v_cons_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___x_505_);
v_id_520_ = lean_ctor_get(v_action_506_, 0);
lean_inc(v_id_520_);
v_c_521_ = lean_ctor_get(v_action_506_, 1);
lean_inc(v_c_521_);
v_rupHints_522_ = lean_ctor_get(v_action_506_, 2);
lean_inc_ref(v_rupHints_522_);
lean_dec_ref(v_action_506_);
v___x_523_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__33);
v___x_524_ = l_Lean_mkNatLit(v_id_520_);
v_type_525_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v___x_526_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_527_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_528_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_529_ = lean_array_to_list(v_c_521_);
v___x_530_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_504_, v_nil_527_, v_cons_528_, v___x_529_);
v___x_531_ = l_Lean_mkAppB(v___x_526_, v_type_525_, v___x_530_);
v_nil_532_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_533_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_534_ = lean_array_to_list(v_rupHints_522_);
v___x_535_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_503_, v_nil_532_, v_cons_533_, v___x_534_);
v___x_536_ = l_Lean_mkAppB(v___x_526_, v_alpha_508_, v___x_535_);
v___x_537_ = l_Lean_mkApp5(v___x_523_, v_beta_507_, v_alpha_508_, v___x_524_, v___x_531_, v___x_536_);
return v___x_537_;
}
case 2:
{
lean_object* v_id_538_; lean_object* v_c_539_; lean_object* v_pivot_540_; lean_object* v_rupHints_541_; lean_object* v_ratHints_542_; lean_object* v___x_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v_type_546_; lean_object* v_nil_547_; lean_object* v_cons_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_00_u03b2Type_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___y_558_; uint8_t v___x_572_; 
v_id_538_ = lean_ctor_get(v_action_506_, 0);
lean_inc(v_id_538_);
v_c_539_ = lean_ctor_get(v_action_506_, 1);
lean_inc(v_c_539_);
v_pivot_540_ = lean_ctor_get(v_action_506_, 2);
lean_inc_ref(v_pivot_540_);
v_rupHints_541_ = lean_ctor_get(v_action_506_, 3);
lean_inc_ref(v_rupHints_541_);
v_ratHints_542_ = lean_ctor_get(v_action_506_, 4);
lean_inc_ref(v_ratHints_542_);
lean_dec_ref(v_action_506_);
v___x_543_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_fst_544_ = lean_ctor_get(v_pivot_540_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v_pivot_540_, 1);
lean_inc(v_snd_545_);
lean_dec_ref(v_pivot_540_);
v_type_546_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__34);
v_nil_547_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__35);
v_cons_548_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__36);
v___x_549_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__39);
v___x_550_ = l_Lean_mkNatLit(v_id_538_);
v___x_551_ = lean_array_to_list(v_c_539_);
v___x_552_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_504_, v_nil_547_, v_cons_548_, v___x_551_);
v___x_553_ = l_Lean_mkAppB(v___x_543_, v_type_546_, v___x_552_);
v_00_u03b2Type_554_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__42);
v___x_555_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__46);
v___x_556_ = l_Lean_mkNatLit(v_fst_544_);
v___x_572_ = lean_unbox(v_snd_545_);
lean_dec(v_snd_545_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__55);
v___y_558_ = v___x_573_;
goto v___jp_557_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__58);
v___y_558_ = v___x_574_;
goto v___jp_557_;
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v_nil_560_; lean_object* v_cons_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_type_565_; lean_object* v_nil_566_; lean_object* v_cons_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_559_ = l_Lean_mkApp4(v___x_555_, v_alpha_508_, v_00_u03b2Type_554_, v___x_556_, v___y_558_);
v_nil_560_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_561_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_562_ = lean_array_to_list(v_rupHints_541_);
v___x_563_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_503_, v_nil_560_, v_cons_561_, v___x_562_);
v___x_564_ = l_Lean_mkAppB(v___x_543_, v_alpha_508_, v___x_563_);
v_type_565_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__50);
v_nil_566_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__51);
v_cons_567_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__52);
v___x_568_ = lean_array_to_list(v_ratHints_542_);
v___x_569_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_505_, v_nil_566_, v_cons_567_, v___x_568_);
v___x_570_ = l_Lean_mkAppB(v___x_543_, v_type_565_, v___x_569_);
v___x_571_ = l_Lean_mkApp7(v___x_549_, v_beta_507_, v_alpha_508_, v___x_550_, v___x_553_, v___x_559_, v___x_564_, v___x_570_);
return v___x_571_;
}
}
default: 
{
lean_object* v_ids_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_nil_578_; lean_object* v_cons_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v___x_505_);
lean_dec_ref(v___x_504_);
v_ids_575_ = lean_ctor_get(v_action_506_, 0);
lean_inc_ref(v_ids_575_);
lean_dec_ref(v_action_506_);
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__61);
v___x_577_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__22);
v_nil_578_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__26);
v_cons_579_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0___closed__30);
v___x_580_ = lean_array_to_list(v_ids_575_);
v___x_581_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_box(0), v___x_503_, v_nil_578_, v_cons_579_, v___x_580_);
v___x_582_ = l_Lean_mkAppB(v___x_577_, v_alpha_508_, v___x_581_);
v___x_583_ = l_Lean_mkApp3(v___x_576_, v_beta_507_, v_alpha_508_, v___x_582_);
return v___x_583_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = l_Lean_instToExprNat;
v___x_585_ = lean_box(0);
v___x_586_ = l_Lean_instToExprArrayOfToLevel___redArg(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__0);
v___x_588_ = l_Lean_instToExprNat;
v___x_589_ = lean_box(0);
v___x_590_ = l_Lean_instToExprProdOfToLevel___redArg(v___x_589_, v___x_589_, v___x_588_, v___x_587_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; 
v___x_591_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__1);
v___x_592_ = l_Lean_instToExprInt;
v___x_593_ = l_Lean_instToExprNat;
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___lam__0), 4, 3);
lean_closure_set(v___f_594_, 0, v___x_593_);
lean_closure_set(v___f_594_, 1, v___x_592_);
lean_closure_set(v___f_594_, 2, v___x_591_);
return v___f_594_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__4));
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6(void){
_start:
{
lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__5);
v___f_606_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__2);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___f_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_instToExprIntAction___closed__6);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(lean_object* v_cls_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_options_612_; uint8_t v_hasTrace_613_; 
v_options_612_ = lean_ctor_get(v___y_610_, 2);
v_hasTrace_613_ = lean_ctor_get_uint8(v_options_612_, sizeof(void*)*1);
if (v_hasTrace_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_cls_609_);
v___x_614_ = lean_box(v_hasTrace_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
else
{
lean_object* v_inheritedTraceOptions_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_inheritedTraceOptions_616_ = lean_ctor_get(v___y_610_, 13);
v___x_617_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__0___redArg___closed__1));
v___x_618_ = l_Lean_Name_append(v___x_617_, v_cls_609_);
v___x_619_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_616_, v_options_612_, v___x_618_);
lean_dec(v___x_618_);
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg___boxed(lean_object* v_cls_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v_cls_622_, v___y_623_);
lean_dec_ref(v___y_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(lean_object* v_cls_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v_cls_626_, v___y_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___boxed(lean_object* v_cls_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0(v_cls_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(lean_object* v_e_636_){
_start:
{
if (lean_obj_tag(v_e_636_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
v_a_638_ = lean_ctor_get(v_e_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_e_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v_e_636_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v_e_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_mk_io_user_error(v_a_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 1);
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v_e_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_e_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v_e_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v_e_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 0);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg___boxed(lean_object* v_e_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_e_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(lean_object* v_00_u03b1_658_, lean_object* v_e_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_e_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___boxed(lean_object* v_00_u03b1_662_, lean_object* v_e_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2(v_00_u03b1_662_, v_e_663_);
return v_res_665_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(32u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = ((size_t)5ULL);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_unsigned_to_nat(32u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__0);
v___x_674_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_670_);
lean_ctor_set(v___x_674_, 3, v___x_670_);
lean_ctor_set_usize(v___x_674_, 4, v___x_669_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v_traceState_678_; lean_object* v_traces_679_; lean_object* v___x_680_; lean_object* v_traceState_681_; lean_object* v_env_682_; lean_object* v_nextMacroScope_683_; lean_object* v_ngen_684_; lean_object* v_auxDeclNGen_685_; lean_object* v_cache_686_; lean_object* v_messages_687_; lean_object* v_infoState_688_; lean_object* v_snapshotTasks_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_708_; 
v___x_677_ = lean_st_ref_get(v___y_675_);
v_traceState_678_ = lean_ctor_get(v___x_677_, 4);
lean_inc_ref(v_traceState_678_);
lean_dec(v___x_677_);
v_traces_679_ = lean_ctor_get(v_traceState_678_, 0);
lean_inc_ref(v_traces_679_);
lean_dec_ref(v_traceState_678_);
v___x_680_ = lean_st_ref_take(v___y_675_);
v_traceState_681_ = lean_ctor_get(v___x_680_, 4);
v_env_682_ = lean_ctor_get(v___x_680_, 0);
v_nextMacroScope_683_ = lean_ctor_get(v___x_680_, 1);
v_ngen_684_ = lean_ctor_get(v___x_680_, 2);
v_auxDeclNGen_685_ = lean_ctor_get(v___x_680_, 3);
v_cache_686_ = lean_ctor_get(v___x_680_, 5);
v_messages_687_ = lean_ctor_get(v___x_680_, 6);
v_infoState_688_ = lean_ctor_get(v___x_680_, 7);
v_snapshotTasks_689_ = lean_ctor_get(v___x_680_, 8);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_708_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snapshotTasks_689_);
lean_inc(v_infoState_688_);
lean_inc(v_messages_687_);
lean_inc(v_cache_686_);
lean_inc(v_traceState_681_);
lean_inc(v_auxDeclNGen_685_);
lean_inc(v_ngen_684_);
lean_inc(v_nextMacroScope_683_);
lean_inc(v_env_682_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint64_t v_tid_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_706_; 
v_tid_693_ = lean_ctor_get_uint64(v_traceState_681_, sizeof(void*)*1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_traceState_681_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_traceState_681_, 0);
lean_dec(v_unused_707_);
v___x_695_ = v_traceState_681_;
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
else
{
lean_dec(v_traceState_681_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___closed__1);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_697_);
lean_ctor_set_uint64(v_reuseFailAlloc_705_, sizeof(void*)*1, v_tid_693_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 4, v___x_699_);
v___x_701_ = v___x_691_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_env_682_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_685_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v_cache_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_messages_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_infoState_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_snapshotTasks_689_);
v___x_701_ = v_reuseFailAlloc_704_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_st_ref_set(v___y_675_, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_traces_679_);
return v___x_703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg___boxed(lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_709_);
lean_dec(v___y_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___boxed(lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3(v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(lean_object* v_opts_720_, lean_object* v_opt_721_){
_start:
{
lean_object* v_name_722_; lean_object* v_defValue_723_; lean_object* v_map_724_; lean_object* v___x_725_; 
v_name_722_ = lean_ctor_get(v_opt_721_, 0);
v_defValue_723_ = lean_ctor_get(v_opt_721_, 1);
v_map_724_ = lean_ctor_get(v_opts_720_, 0);
v___x_725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_724_, v_name_722_);
if (lean_obj_tag(v___x_725_) == 0)
{
uint8_t v___x_726_; 
v___x_726_ = lean_unbox(v_defValue_723_);
return v___x_726_;
}
else
{
lean_object* v_val_727_; 
v_val_727_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_727_);
lean_dec_ref(v___x_725_);
if (lean_obj_tag(v_val_727_) == 1)
{
uint8_t v_v_728_; 
v_v_728_ = lean_ctor_get_uint8(v_val_727_, 0);
lean_dec_ref(v_val_727_);
return v_v_728_;
}
else
{
uint8_t v___x_729_; 
lean_dec(v_val_727_);
v___x_729_ = lean_unbox(v_defValue_723_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4___boxed(lean_object* v_opts_730_, lean_object* v_opt_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_730_, v_opt_731_);
lean_dec_ref(v_opt_731_);
lean_dec_ref(v_opts_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__1));
v___x_738_ = l_Lean_MessageData_ofFormat(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(lean_object* v_x_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___closed__2);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0___boxed(lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__0(v_x_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_x_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1(lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(lean_object* v_a_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed(lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2(v_a_756_, v_x_757_);
lean_dec_ref(v_a_756_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__1));
v___x_763_ = l_Lean_MessageData_ofFormat(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___closed__2);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3___boxed(lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__3(v_x_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v_x_770_);
return v_res_774_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_775_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__0);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
lean_ctor_set(v___x_780_, 2, v___x_779_);
lean_ctor_set(v___x_780_, 3, v___x_778_);
lean_ctor_set(v___x_780_, 4, v___x_778_);
lean_ctor_set(v___x_780_, 5, v___x_778_);
lean_ctor_set(v___x_780_, 6, v___x_778_);
lean_ctor_set(v___x_780_, 7, v___x_778_);
lean_ctor_set(v___x_780_, 8, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_unsigned_to_nat(32u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_784_ = ((size_t)5ULL);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_unsigned_to_nat(32u);
v___x_787_ = lean_mk_empty_array_with_capacity(v___x_786_);
v___x_788_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__3);
v___x_789_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
lean_ctor_set(v___x_789_, 2, v___x_785_);
lean_ctor_set(v___x_789_, 3, v___x_785_);
lean_ctor_set_usize(v___x_789_, 4, v___x_784_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_box(1);
v___x_791_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__4);
v___x_792_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__1);
v___x_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set(v___x_793_, 2, v___x_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(lean_object* v_msgData_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; lean_object* v_env_799_; lean_object* v_options_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_798_ = lean_st_ref_get(v___y_796_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc_ref(v_env_799_);
lean_dec(v___x_798_);
v_options_800_ = lean_ctor_get(v___y_795_, 2);
v___x_801_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__2);
v___x_802_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_800_);
v___x_803_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_803_, 0, v_env_799_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v___x_802_);
lean_ctor_set(v___x_803_, 3, v_options_800_);
v___x_804_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_msgData_794_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1___boxed(lean_object* v_msgData_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msgData_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_ref_815_; lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_ref_815_ = lean_ctor_get(v___y_812_, 5);
v___x_816_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msg_811_, v___y_812_, v___y_813_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_inc(v_ref_815_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_ref_815_);
lean_ctor_set(v___x_821_, 1, v_a_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 1);
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg___boxed(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v_msg_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6(lean_object* v_e_831_){
_start:
{
if (lean_obj_tag(v_e_831_) == 0)
{
uint8_t v___x_832_; 
v___x_832_ = 2;
return v___x_832_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = 0;
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6___boxed(lean_object* v_e_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6(v_e_834_);
lean_dec_ref(v_e_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(lean_object* v_x_837_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v_x_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v_x_837_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v_x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 1);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v_x_837_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v_x_837_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v_x_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 0);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg___boxed(lean_object* v_x_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_x_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8(size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_861_ == 0)
{
return v_bs_860_;
}
else
{
lean_object* v_v_862_; lean_object* v_msg_863_; lean_object* v___x_864_; lean_object* v_bs_x27_865_; size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v_v_862_ = lean_array_uget_borrowed(v_bs_860_, v_i_859_);
v_msg_863_ = lean_ctor_get(v_v_862_, 1);
lean_inc_ref(v_msg_863_);
v___x_864_ = lean_unsigned_to_nat(0u);
v_bs_x27_865_ = lean_array_uset(v_bs_860_, v_i_859_, v___x_864_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_859_, v___x_866_);
v___x_868_ = lean_array_uset(v_bs_x27_865_, v_i_859_, v_msg_863_);
v_i_859_ = v___x_867_;
v_bs_860_ = v___x_868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8___boxed(lean_object* v_sz_870_, lean_object* v_i_871_, lean_object* v_bs_872_){
_start:
{
size_t v_sz_boxed_873_; size_t v_i_boxed_874_; lean_object* v_res_875_; 
v_sz_boxed_873_ = lean_unbox_usize(v_sz_870_);
lean_dec(v_sz_870_);
v_i_boxed_874_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8(v_sz_boxed_873_, v_i_boxed_874_, v_bs_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(lean_object* v_oldTraces_876_, lean_object* v_data_877_, lean_object* v_ref_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_fileName_883_; lean_object* v_fileMap_884_; lean_object* v_options_885_; lean_object* v_currRecDepth_886_; lean_object* v_maxRecDepth_887_; lean_object* v_ref_888_; lean_object* v_currNamespace_889_; lean_object* v_openDecls_890_; lean_object* v_initHeartbeats_891_; lean_object* v_maxHeartbeats_892_; lean_object* v_quotContext_893_; lean_object* v_currMacroScope_894_; uint8_t v_diag_895_; lean_object* v_cancelTk_x3f_896_; uint8_t v_suppressElabErrors_897_; lean_object* v_inheritedTraceOptions_898_; lean_object* v___x_899_; lean_object* v_traceState_900_; lean_object* v_traces_901_; lean_object* v_ref_902_; lean_object* v___x_903_; lean_object* v___x_904_; size_t v_sz_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v_msg_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_947_; 
v_fileName_883_ = lean_ctor_get(v___y_880_, 0);
v_fileMap_884_ = lean_ctor_get(v___y_880_, 1);
v_options_885_ = lean_ctor_get(v___y_880_, 2);
v_currRecDepth_886_ = lean_ctor_get(v___y_880_, 3);
v_maxRecDepth_887_ = lean_ctor_get(v___y_880_, 4);
v_ref_888_ = lean_ctor_get(v___y_880_, 5);
v_currNamespace_889_ = lean_ctor_get(v___y_880_, 6);
v_openDecls_890_ = lean_ctor_get(v___y_880_, 7);
v_initHeartbeats_891_ = lean_ctor_get(v___y_880_, 8);
v_maxHeartbeats_892_ = lean_ctor_get(v___y_880_, 9);
v_quotContext_893_ = lean_ctor_get(v___y_880_, 10);
v_currMacroScope_894_ = lean_ctor_get(v___y_880_, 11);
v_diag_895_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*14);
v_cancelTk_x3f_896_ = lean_ctor_get(v___y_880_, 12);
v_suppressElabErrors_897_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_898_ = lean_ctor_get(v___y_880_, 13);
v___x_899_ = lean_st_ref_get(v___y_881_);
v_traceState_900_ = lean_ctor_get(v___x_899_, 4);
lean_inc_ref(v_traceState_900_);
lean_dec(v___x_899_);
v_traces_901_ = lean_ctor_get(v_traceState_900_, 0);
lean_inc_ref(v_traces_901_);
lean_dec_ref(v_traceState_900_);
v_ref_902_ = l_Lean_replaceRef(v_ref_878_, v_ref_888_);
lean_inc_ref(v_inheritedTraceOptions_898_);
lean_inc(v_cancelTk_x3f_896_);
lean_inc(v_currMacroScope_894_);
lean_inc(v_quotContext_893_);
lean_inc(v_maxHeartbeats_892_);
lean_inc(v_initHeartbeats_891_);
lean_inc(v_openDecls_890_);
lean_inc(v_currNamespace_889_);
lean_inc(v_maxRecDepth_887_);
lean_inc(v_currRecDepth_886_);
lean_inc_ref(v_options_885_);
lean_inc_ref(v_fileMap_884_);
lean_inc_ref(v_fileName_883_);
v___x_903_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_903_, 0, v_fileName_883_);
lean_ctor_set(v___x_903_, 1, v_fileMap_884_);
lean_ctor_set(v___x_903_, 2, v_options_885_);
lean_ctor_set(v___x_903_, 3, v_currRecDepth_886_);
lean_ctor_set(v___x_903_, 4, v_maxRecDepth_887_);
lean_ctor_set(v___x_903_, 5, v_ref_902_);
lean_ctor_set(v___x_903_, 6, v_currNamespace_889_);
lean_ctor_set(v___x_903_, 7, v_openDecls_890_);
lean_ctor_set(v___x_903_, 8, v_initHeartbeats_891_);
lean_ctor_set(v___x_903_, 9, v_maxHeartbeats_892_);
lean_ctor_set(v___x_903_, 10, v_quotContext_893_);
lean_ctor_set(v___x_903_, 11, v_currMacroScope_894_);
lean_ctor_set(v___x_903_, 12, v_cancelTk_x3f_896_);
lean_ctor_set(v___x_903_, 13, v_inheritedTraceOptions_898_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*14, v_diag_895_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*14 + 1, v_suppressElabErrors_897_);
v___x_904_ = l_Lean_PersistentArray_toArray___redArg(v_traces_901_);
lean_dec_ref(v_traces_901_);
v_sz_905_ = lean_array_size(v___x_904_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8(v_sz_905_, v___x_906_, v___x_904_);
v_msg_908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_908_, 0, v_data_877_);
lean_ctor_set(v_msg_908_, 1, v_msg_879_);
lean_ctor_set(v_msg_908_, 2, v___x_907_);
v___x_909_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msg_908_, v___x_903_, v___y_881_);
lean_dec_ref(v___x_903_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_947_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_947_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_947_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v_traceState_915_; lean_object* v_env_916_; lean_object* v_nextMacroScope_917_; lean_object* v_ngen_918_; lean_object* v_auxDeclNGen_919_; lean_object* v_cache_920_; lean_object* v_messages_921_; lean_object* v_infoState_922_; lean_object* v_snapshotTasks_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_946_; 
v___x_914_ = lean_st_ref_take(v___y_881_);
v_traceState_915_ = lean_ctor_get(v___x_914_, 4);
v_env_916_ = lean_ctor_get(v___x_914_, 0);
v_nextMacroScope_917_ = lean_ctor_get(v___x_914_, 1);
v_ngen_918_ = lean_ctor_get(v___x_914_, 2);
v_auxDeclNGen_919_ = lean_ctor_get(v___x_914_, 3);
v_cache_920_ = lean_ctor_get(v___x_914_, 5);
v_messages_921_ = lean_ctor_get(v___x_914_, 6);
v_infoState_922_ = lean_ctor_get(v___x_914_, 7);
v_snapshotTasks_923_ = lean_ctor_get(v___x_914_, 8);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_946_ == 0)
{
v___x_925_ = v___x_914_;
v_isShared_926_ = v_isSharedCheck_946_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snapshotTasks_923_);
lean_inc(v_infoState_922_);
lean_inc(v_messages_921_);
lean_inc(v_cache_920_);
lean_inc(v_traceState_915_);
lean_inc(v_auxDeclNGen_919_);
lean_inc(v_ngen_918_);
lean_inc(v_nextMacroScope_917_);
lean_inc(v_env_916_);
lean_dec(v___x_914_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_946_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint64_t v_tid_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_944_; 
v_tid_927_ = lean_ctor_get_uint64(v_traceState_915_, sizeof(void*)*1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_traceState_915_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_traceState_915_, 0);
lean_dec(v_unused_945_);
v___x_929_ = v_traceState_915_;
v_isShared_930_ = v_isSharedCheck_944_;
goto v_resetjp_928_;
}
else
{
lean_dec(v_traceState_915_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_944_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_ref_878_);
lean_ctor_set(v___x_931_, 1, v_a_910_);
v___x_932_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_876_, v___x_931_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_932_);
lean_ctor_set_uint64(v_reuseFailAlloc_943_, sizeof(void*)*1, v_tid_927_);
v___x_934_ = v_reuseFailAlloc_943_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 4, v___x_934_);
v___x_936_ = v___x_925_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_env_916_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_nextMacroScope_917_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_ngen_918_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_auxDeclNGen_919_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v_cache_920_);
lean_ctor_set(v_reuseFailAlloc_942_, 6, v_messages_921_);
lean_ctor_set(v_reuseFailAlloc_942_, 7, v_infoState_922_);
lean_ctor_set(v_reuseFailAlloc_942_, 8, v_snapshotTasks_923_);
v___x_936_ = v_reuseFailAlloc_942_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = lean_st_ref_set(v___y_881_, v___x_936_);
v___x_938_ = lean_box(0);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_938_);
v___x_940_ = v___x_912_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7___boxed(lean_object* v_oldTraces_948_, lean_object* v_data_949_, lean_object* v_ref_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_948_, v_data_949_, v_ref_950_, v_msg_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(lean_object* v_opts_956_, lean_object* v_opt_957_){
_start:
{
lean_object* v_name_958_; lean_object* v_defValue_959_; lean_object* v_map_960_; lean_object* v___x_961_; 
v_name_958_ = lean_ctor_get(v_opt_957_, 0);
v_defValue_959_ = lean_ctor_get(v_opt_957_, 1);
v_map_960_ = lean_ctor_get(v_opts_956_, 0);
v___x_961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_960_, v_name_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_inc(v_defValue_959_);
return v_defValue_959_;
}
else
{
lean_object* v_val_962_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref(v___x_961_);
if (lean_obj_tag(v_val_962_) == 3)
{
lean_object* v_v_963_; 
v_v_963_ = lean_ctor_get(v_val_962_, 0);
lean_inc(v_v_963_);
lean_dec_ref(v_val_962_);
return v_v_963_;
}
else
{
lean_dec(v_val_962_);
lean_inc(v_defValue_959_);
return v_defValue_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9___boxed(lean_object* v_opts_964_, lean_object* v_opt_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_964_, v_opt_965_);
lean_dec_ref(v_opt_965_);
lean_dec_ref(v_opts_964_);
return v_res_966_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__0));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__2));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4(void){
_start:
{
lean_object* v___x_973_; double v___x_974_; 
v___x_973_ = lean_unsigned_to_nat(1000u);
v___x_974_ = lean_float_of_nat(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object* v_cls_975_, uint8_t v_collapsed_976_, lean_object* v_tag_977_, lean_object* v_opts_978_, uint8_t v_clsEnabled_979_, lean_object* v_oldTraces_980_, lean_object* v_msg_981_, lean_object* v_resStartStop_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1085_; 
v_fst_986_ = lean_ctor_get(v_resStartStop_982_, 0);
v_snd_987_ = lean_ctor_get(v_resStartStop_982_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_resStartStop_982_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_989_ = v_resStartStop_982_;
v_isShared_990_ = v_isSharedCheck_1085_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_inc(v_fst_986_);
lean_dec(v_resStartStop_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1085_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v_data_994_; lean_object* v_fst_1005_; lean_object* v_snd_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1084_; 
v_fst_1005_ = lean_ctor_get(v_snd_987_, 0);
v_snd_1006_ = lean_ctor_get(v_snd_987_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_snd_987_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1008_ = v_snd_987_;
v_isShared_1009_ = v_isSharedCheck_1084_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_snd_1006_);
lean_inc(v_fst_1005_);
lean_dec(v_snd_987_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1084_;
goto v_resetjp_1007_;
}
v___jp_991_:
{
lean_object* v___x_995_; 
lean_inc(v___y_993_);
v___x_995_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_980_, v_data_994_, v___y_993_, v___y_992_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v___x_996_; 
lean_dec_ref(v___x_995_);
v___x_996_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_986_);
return v___x_996_;
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_fst_986_);
v_a_997_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_995_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___y_1013_; lean_object* v_a_1014_; uint8_t v___y_1038_; double v___y_1069_; 
v___x_1010_ = l_Lean_trace_profiler;
v___x_1011_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_978_, v___x_1010_);
if (v___x_1011_ == 0)
{
v___y_1038_ = v___x_1011_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1075_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_978_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; double v___x_1078_; double v___x_1079_; double v___x_1080_; 
v___x_1076_ = l_Lean_trace_profiler_threshold;
v___x_1077_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_978_, v___x_1076_);
v___x_1078_ = lean_float_of_nat(v___x_1077_);
v___x_1079_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_1080_ = lean_float_div(v___x_1078_, v___x_1079_);
v___y_1069_ = v___x_1080_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; double v___x_1083_; 
v___x_1081_ = l_Lean_trace_profiler_threshold;
v___x_1082_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_978_, v___x_1081_);
v___x_1083_ = lean_float_of_nat(v___x_1082_);
v___y_1069_ = v___x_1083_;
goto v___jp_1068_;
}
}
v___jp_1012_:
{
uint8_t v_result_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v_result_1015_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6(v_fst_986_);
v___x_1016_ = l_Lean_TraceResult_toEmoji(v_result_1015_);
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
v___x_1018_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 7);
lean_ctor_set(v___x_1008_, 1, v___x_1018_);
lean_ctor_set(v___x_1008_, 0, v___x_1017_);
v___x_1020_ = v___x_1008_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v_m_1022_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 7);
lean_ctor_set(v___x_989_, 1, v_a_1014_);
lean_ctor_set(v___x_989_, 0, v___x_1020_);
v_m_1022_ = v___x_989_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1014_);
v_m_1022_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; double v___x_1025_; lean_object* v_data_1026_; 
v___x_1023_ = lean_box(v_result_1015_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_977_);
lean_inc_ref(v___x_1024_);
lean_inc(v_cls_975_);
v_data_1026_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1026_, 0, v_cls_975_);
lean_ctor_set(v_data_1026_, 1, v___x_1024_);
lean_ctor_set(v_data_1026_, 2, v_tag_977_);
lean_ctor_set_float(v_data_1026_, sizeof(void*)*3, v___x_1025_);
lean_ctor_set_float(v_data_1026_, sizeof(void*)*3 + 8, v___x_1025_);
lean_ctor_set_uint8(v_data_1026_, sizeof(void*)*3 + 16, v_collapsed_976_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v___x_1024_);
lean_dec(v_snd_1006_);
lean_dec(v_fst_1005_);
lean_dec_ref(v_tag_977_);
lean_dec(v_cls_975_);
v___y_992_ = v_m_1022_;
v___y_993_ = v___y_1013_;
v_data_994_ = v_data_1026_;
goto v___jp_991_;
}
else
{
lean_object* v_data_1027_; double v___x_1028_; double v___x_1029_; 
lean_dec_ref(v_data_1026_);
v_data_1027_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1027_, 0, v_cls_975_);
lean_ctor_set(v_data_1027_, 1, v___x_1024_);
lean_ctor_set(v_data_1027_, 2, v_tag_977_);
v___x_1028_ = lean_unbox_float(v_fst_1005_);
lean_dec(v_fst_1005_);
lean_ctor_set_float(v_data_1027_, sizeof(void*)*3, v___x_1028_);
v___x_1029_ = lean_unbox_float(v_snd_1006_);
lean_dec(v_snd_1006_);
lean_ctor_set_float(v_data_1027_, sizeof(void*)*3 + 8, v___x_1029_);
lean_ctor_set_uint8(v_data_1027_, sizeof(void*)*3 + 16, v_collapsed_976_);
v___y_992_ = v_m_1022_;
v___y_993_ = v___y_1013_;
v_data_994_ = v_data_1027_;
goto v___jp_991_;
}
}
}
}
v___jp_1032_:
{
lean_object* v_ref_1033_; lean_object* v___x_1034_; 
v_ref_1033_ = lean_ctor_get(v___y_983_, 5);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v_fst_986_);
v___x_1034_ = lean_apply_4(v_msg_981_, v_fst_986_, v___y_983_, v___y_984_, lean_box(0));
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v___y_1013_ = v_ref_1033_;
v_a_1014_ = v_a_1035_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref(v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
v___y_1013_ = v_ref_1033_;
v_a_1014_ = v___x_1036_;
goto v___jp_1012_;
}
}
v___jp_1037_:
{
if (v_clsEnabled_979_ == 0)
{
if (v___y_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v_traceState_1040_; lean_object* v_env_1041_; lean_object* v_nextMacroScope_1042_; lean_object* v_ngen_1043_; lean_object* v_auxDeclNGen_1044_; lean_object* v_cache_1045_; lean_object* v_messages_1046_; lean_object* v_infoState_1047_; lean_object* v_snapshotTasks_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1067_; 
lean_del_object(v___x_1008_);
lean_dec(v_snd_1006_);
lean_dec(v_fst_1005_);
lean_del_object(v___x_989_);
lean_dec_ref(v_msg_981_);
lean_dec_ref(v_tag_977_);
lean_dec(v_cls_975_);
v___x_1039_ = lean_st_ref_take(v___y_984_);
v_traceState_1040_ = lean_ctor_get(v___x_1039_, 4);
v_env_1041_ = lean_ctor_get(v___x_1039_, 0);
v_nextMacroScope_1042_ = lean_ctor_get(v___x_1039_, 1);
v_ngen_1043_ = lean_ctor_get(v___x_1039_, 2);
v_auxDeclNGen_1044_ = lean_ctor_get(v___x_1039_, 3);
v_cache_1045_ = lean_ctor_get(v___x_1039_, 5);
v_messages_1046_ = lean_ctor_get(v___x_1039_, 6);
v_infoState_1047_ = lean_ctor_get(v___x_1039_, 7);
v_snapshotTasks_1048_ = lean_ctor_get(v___x_1039_, 8);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1050_ = v___x_1039_;
v_isShared_1051_ = v_isSharedCheck_1067_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snapshotTasks_1048_);
lean_inc(v_infoState_1047_);
lean_inc(v_messages_1046_);
lean_inc(v_cache_1045_);
lean_inc(v_traceState_1040_);
lean_inc(v_auxDeclNGen_1044_);
lean_inc(v_ngen_1043_);
lean_inc(v_nextMacroScope_1042_);
lean_inc(v_env_1041_);
lean_dec(v___x_1039_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1067_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint64_t v_tid_1052_; lean_object* v_traces_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1066_; 
v_tid_1052_ = lean_ctor_get_uint64(v_traceState_1040_, sizeof(void*)*1);
v_traces_1053_ = lean_ctor_get(v_traceState_1040_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_traceState_1040_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1055_ = v_traceState_1040_;
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_traces_1053_);
lean_dec(v_traceState_1040_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_980_, v_traces_1053_);
lean_dec_ref(v_traces_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1057_);
lean_ctor_set_uint64(v_reuseFailAlloc_1065_, sizeof(void*)*1, v_tid_1052_);
v___x_1059_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 4, v___x_1059_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_env_1041_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_nextMacroScope_1042_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ngen_1043_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_auxDeclNGen_1044_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v_cache_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_messages_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 7, v_infoState_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 8, v_snapshotTasks_1048_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_st_ref_set(v___y_984_, v___x_1061_);
v___x_1063_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_986_);
return v___x_1063_;
}
}
}
}
}
else
{
goto v___jp_1032_;
}
}
else
{
goto v___jp_1032_;
}
}
v___jp_1068_:
{
double v___x_1070_; double v___x_1071_; double v___x_1072_; uint8_t v___x_1073_; 
v___x_1070_ = lean_unbox_float(v_snd_1006_);
v___x_1071_ = lean_unbox_float(v_fst_1005_);
v___x_1072_ = lean_float_sub(v___x_1070_, v___x_1071_);
v___x_1073_ = lean_float_decLt(v___y_1069_, v___x_1072_);
v___y_1038_ = v___x_1073_;
goto v___jp_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object* v_cls_1086_, lean_object* v_collapsed_1087_, lean_object* v_tag_1088_, lean_object* v_opts_1089_, lean_object* v_clsEnabled_1090_, lean_object* v_oldTraces_1091_, lean_object* v_msg_1092_, lean_object* v_resStartStop_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_collapsed_boxed_1097_; uint8_t v_clsEnabled_boxed_1098_; lean_object* v_res_1099_; 
v_collapsed_boxed_1097_ = lean_unbox(v_collapsed_1087_);
v_clsEnabled_boxed_1098_ = lean_unbox(v_clsEnabled_1090_);
v_res_1099_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v_cls_1086_, v_collapsed_boxed_1097_, v_tag_1088_, v_opts_1089_, v_clsEnabled_boxed_1098_, v_oldTraces_1091_, v_msg_1092_, v_resStartStop_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v_opts_1089_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object* v_cls_1100_, lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_ref_1105_; lean_object* v___x_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1151_; 
v_ref_1105_ = lean_ctor_get(v___y_1102_, 5);
v___x_1106_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msg_1101_, v___y_1102_, v___y_1103_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1151_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1151_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v_traceState_1112_; lean_object* v_env_1113_; lean_object* v_nextMacroScope_1114_; lean_object* v_ngen_1115_; lean_object* v_auxDeclNGen_1116_; lean_object* v_cache_1117_; lean_object* v_messages_1118_; lean_object* v_infoState_1119_; lean_object* v_snapshotTasks_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1150_; 
v___x_1111_ = lean_st_ref_take(v___y_1103_);
v_traceState_1112_ = lean_ctor_get(v___x_1111_, 4);
v_env_1113_ = lean_ctor_get(v___x_1111_, 0);
v_nextMacroScope_1114_ = lean_ctor_get(v___x_1111_, 1);
v_ngen_1115_ = lean_ctor_get(v___x_1111_, 2);
v_auxDeclNGen_1116_ = lean_ctor_get(v___x_1111_, 3);
v_cache_1117_ = lean_ctor_get(v___x_1111_, 5);
v_messages_1118_ = lean_ctor_get(v___x_1111_, 6);
v_infoState_1119_ = lean_ctor_get(v___x_1111_, 7);
v_snapshotTasks_1120_ = lean_ctor_get(v___x_1111_, 8);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1122_ = v___x_1111_;
v_isShared_1123_ = v_isSharedCheck_1150_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snapshotTasks_1120_);
lean_inc(v_infoState_1119_);
lean_inc(v_messages_1118_);
lean_inc(v_cache_1117_);
lean_inc(v_traceState_1112_);
lean_inc(v_auxDeclNGen_1116_);
lean_inc(v_ngen_1115_);
lean_inc(v_nextMacroScope_1114_);
lean_inc(v_env_1113_);
lean_dec(v___x_1111_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1150_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint64_t v_tid_1124_; lean_object* v_traces_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1149_; 
v_tid_1124_ = lean_ctor_get_uint64(v_traceState_1112_, sizeof(void*)*1);
v_traces_1125_ = lean_ctor_get(v_traceState_1112_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_traceState_1112_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1127_ = v_traceState_1112_;
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_traces_1125_);
lean_dec(v_traceState_1112_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; double v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
v___x_1131_ = 0;
v___x_1132_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_1133_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1133_, 0, v_cls_1100_);
lean_ctor_set(v___x_1133_, 1, v___x_1129_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
lean_ctor_set_float(v___x_1133_, sizeof(void*)*3, v___x_1130_);
lean_ctor_set_float(v___x_1133_, sizeof(void*)*3 + 8, v___x_1130_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*3 + 16, v___x_1131_);
v___x_1134_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1));
v___x_1135_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v_a_1107_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
lean_inc(v_ref_1105_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_ref_1105_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_PersistentArray_push___redArg(v_traces_1125_, v___x_1136_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1137_);
v___x_1139_ = v___x_1127_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1137_);
lean_ctor_set_uint64(v_reuseFailAlloc_1148_, sizeof(void*)*1, v_tid_1124_);
v___x_1139_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v___x_1139_);
v___x_1141_ = v___x_1122_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_env_1113_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_nextMacroScope_1114_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_ngen_1115_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_auxDeclNGen_1116_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_cache_1117_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_messages_1118_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_infoState_1119_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_snapshotTasks_1120_);
v___x_1141_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_st_ref_set(v___y_1103_, v___x_1141_);
v___x_1143_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1143_);
v___x_1145_ = v___x_1109_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object* v_cls_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v_cls_1152_, v_msg_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1157_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3(void){
_start:
{
lean_object* v___x_1161_; double v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(1000000000u);
v___x_1162_ = lean_float_of_nat(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5));
v___x_1166_ = l_Lean_stringToMessageData(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object* v_lratPath_1168_, uint8_t v_trimProofs_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_IO_FS_readBinFile(v_lratPath_1168_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_options_1174_; lean_object* v_a_1175_; lean_object* v_ref_1176_; uint8_t v_hasTrace_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v_proof_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; uint8_t v___x_1225_; lean_object* v___x_1226_; uint8_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v_a_1234_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v_a_1250_; uint8_t v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v_a_1259_; uint8_t v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v_a_1278_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v_a_1440_; lean_object* v___y_1469_; 
v_options_1174_ = lean_ctor_get(v_a_1170_, 2);
v_a_1175_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1173_);
v_ref_1176_ = lean_ctor_get(v_a_1170_, 5);
v_hasTrace_1177_ = lean_ctor_get_uint8(v_options_1174_, sizeof(void*)*1);
v___f_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0));
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_1179_, 0, v_a_1175_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_1225_ = 1;
v___x_1226_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_1177_ == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = l_IO_lazyPure___redArg(v___f_1179_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
if (lean_obj_tag(v_a_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1473_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v_a_1472_);
v___x_1474_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1475_ = l_Lean_stringToMessageData(v_a_1473_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1476_, v_a_1170_, v_a_1171_);
v___y_1469_ = v___x_1477_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v_a_1472_);
v_a_1440_ = v_a_1478_;
goto v___jp_1439_;
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1490_; 
v_a_1479_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1481_ = v___x_1471_;
v_isShared_1482_ = v_isSharedCheck_1490_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1471_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1490_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1483_ = lean_io_error_to_string(v_a_1479_);
v___x_1484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___x_1485_ = l_Lean_MessageData_ofFormat(v___x_1484_);
lean_inc(v_ref_1176_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_ref_1176_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1486_);
v___x_1488_ = v___x_1481_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1618_; 
v___x_1491_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1180_, v_a_1170_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1618_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1618_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___f_1496_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_a_1500_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v_a_1516_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v_a_1523_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v_a_1528_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v_a_1541_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_a_1546_; uint8_t v___x_1595_; 
v___f_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7));
v___x_1595_ = lean_unbox(v_a_1492_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = l_Lean_trace_profiler;
v___x_1597_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1174_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_del_object(v___x_1494_);
lean_dec(v_a_1492_);
v___x_1598_ = l_IO_lazyPure___redArg(v___f_1179_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
if (lean_obj_tag(v_a_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v_a_1599_);
v___x_1601_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1602_ = l_Lean_stringToMessageData(v_a_1600_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1603_, v_a_1170_, v_a_1171_);
v___y_1469_ = v___x_1604_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v_a_1599_);
v_a_1440_ = v_a_1605_;
goto v___jp_1439_;
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1617_; 
v_a_1606_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1598_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1617_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1610_ = lean_io_error_to_string(v_a_1606_);
v___x_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
v___x_1612_ = l_Lean_MessageData_ofFormat(v___x_1611_);
lean_inc(v_ref_1176_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_ref_1176_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1613_);
v___x_1615_ = v___x_1608_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
goto v___jp_1548_;
}
}
else
{
goto v___jp_1548_;
}
v___jp_1497_:
{
lean_object* v___x_1501_; double v___x_1502_; double v___x_1503_; double v___x_1504_; double v___x_1505_; double v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1501_ = lean_io_mono_nanos_now();
v___x_1502_ = lean_float_of_nat(v___y_1498_);
v___x_1503_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1504_ = lean_float_div(v___x_1502_, v___x_1503_);
v___x_1505_ = lean_float_of_nat(v___x_1501_);
v___x_1506_ = lean_float_div(v___x_1505_, v___x_1503_);
v___x_1507_ = lean_box_float(v___x_1504_);
v___x_1508_ = lean_box_float(v___x_1506_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1500_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_unbox(v_a_1492_);
lean_dec(v_a_1492_);
v___x_1512_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1180_, v___x_1225_, v___x_1226_, v_options_1174_, v___x_1511_, v___y_1499_, v___f_1496_, v___x_1510_, v_a_1170_, v_a_1171_);
v___y_1469_ = v___x_1512_;
goto v___jp_1468_;
}
v___jp_1513_:
{
lean_object* v___x_1518_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_a_1516_);
v___x_1518_ = v___x_1494_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v___y_1498_ = v___y_1514_;
v___y_1499_ = v___y_1515_;
v_a_1500_ = v___x_1518_;
goto v___jp_1497_;
}
}
v___jp_1520_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_a_1523_);
v___y_1498_ = v___y_1521_;
v___y_1499_ = v___y_1522_;
v_a_1500_ = v___x_1524_;
goto v___jp_1497_;
}
v___jp_1525_:
{
lean_object* v___x_1529_; double v___x_1530_; double v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1529_ = lean_io_get_num_heartbeats();
v___x_1530_ = lean_float_of_nat(v___y_1526_);
v___x_1531_ = lean_float_of_nat(v___x_1529_);
v___x_1532_ = lean_box_float(v___x_1530_);
v___x_1533_ = lean_box_float(v___x_1531_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1528_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_unbox(v_a_1492_);
lean_dec(v_a_1492_);
v___x_1537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1180_, v___x_1225_, v___x_1226_, v_options_1174_, v___x_1536_, v___y_1527_, v___f_1496_, v___x_1535_, v_a_1170_, v_a_1171_);
v___y_1469_ = v___x_1537_;
goto v___jp_1468_;
}
v___jp_1538_:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_a_1541_);
v___y_1526_ = v___y_1539_;
v___y_1527_ = v___y_1540_;
v_a_1528_ = v___x_1542_;
goto v___jp_1525_;
}
v___jp_1543_:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1546_);
v___y_1526_ = v___y_1544_;
v___y_1527_ = v___y_1545_;
v_a_1528_ = v___x_1547_;
goto v___jp_1525_;
}
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v_a_1171_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1552_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1174_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_io_mono_nanos_now();
v___x_1554_ = l_IO_lazyPure___redArg(v___f_1179_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
if (lean_obj_tag(v_a_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_a_1561_; 
v_a_1556_ = lean_ctor_get(v_a_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v_a_1555_);
v___x_1557_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1558_ = l_Lean_stringToMessageData(v_a_1556_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1559_, v_a_1170_, v_a_1171_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v___y_1514_ = v___x_1553_;
v___y_1515_ = v_a_1550_;
v_a_1516_ = v_a_1561_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1562_; 
lean_del_object(v___x_1494_);
v_a_1562_ = lean_ctor_get(v_a_1555_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v_a_1555_);
v___y_1521_ = v___x_1553_;
v___y_1522_ = v_a_1550_;
v_a_1523_ = v_a_1562_;
goto v___jp_1520_;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1573_; 
v_a_1563_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1565_ = v___x_1554_;
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1554_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1573_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_io_error_to_string(v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 3);
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = l_Lean_MessageData_ofFormat(v___x_1569_);
lean_inc(v_ref_1176_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_ref_1176_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___y_1514_ = v___x_1553_;
v___y_1515_ = v_a_1550_;
v_a_1516_ = v___x_1571_;
goto v___jp_1513_;
}
}
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1494_);
v___x_1574_ = lean_io_get_num_heartbeats();
v___x_1575_ = l_IO_lazyPure___redArg(v___f_1179_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
if (lean_obj_tag(v_a_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_a_1582_; 
v_a_1577_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v_a_1576_);
v___x_1578_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1579_ = l_Lean_stringToMessageData(v_a_1577_);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1580_, v_a_1170_, v_a_1171_);
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1581_);
v___y_1539_ = v___x_1574_;
v___y_1540_ = v_a_1550_;
v_a_1541_ = v_a_1582_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1583_; 
v_a_1583_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v_a_1576_);
v___y_1544_ = v___x_1574_;
v___y_1545_ = v_a_1550_;
v_a_1546_ = v_a_1583_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1594_; 
v_a_1584_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1586_ = v___x_1575_;
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1575_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_io_error_to_string(v_a_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 3);
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = l_Lean_MessageData_ofFormat(v___x_1590_);
lean_inc(v_ref_1176_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_ref_1176_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___y_1539_ = v___x_1574_;
v___y_1540_ = v_a_1550_;
v_a_1541_ = v___x_1592_;
goto v___jp_1538_;
}
}
}
}
}
}
}
v___jp_1181_:
{
lean_object* v___x_1185_; lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1219_; 
v___x_1185_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1180_, v___y_1183_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1219_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1219_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1192_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_proof_1182_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_proof_1182_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1188_);
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1195_ = lean_array_get_size(v_proof_1182_);
v___x_1196_ = l_Nat_reprFast(v___x_1195_);
v___x_1197_ = lean_string_append(v___x_1194_, v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2));
v___x_1199_ = lean_string_append(v___x_1197_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
v___x_1201_ = l_Lean_MessageData_ofFormat(v___x_1200_);
v___x_1202_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___x_1180_, v___x_1201_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1202_, 0);
lean_dec(v_unused_1210_);
v___x_1204_ = v___x_1202_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v___x_1202_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_proof_1182_);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_proof_1182_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_proof_1182_);
v_a_1211_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1202_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1202_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
v___jp_1220_:
{
if (lean_obj_tag(v___y_1223_) == 0)
{
lean_object* v_a_1224_; 
v_a_1224_ = lean_ctor_get(v___y_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___y_1223_);
v_proof_1182_ = v_a_1224_;
v___y_1183_ = v___y_1222_;
v___y_1184_ = v___y_1221_;
goto v___jp_1181_;
}
else
{
return v___y_1223_;
}
}
v___jp_1227_:
{
lean_object* v___x_1235_; double v___x_1236_; double v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1235_ = lean_io_get_num_heartbeats();
v___x_1236_ = lean_float_of_nat(v___y_1232_);
v___x_1237_ = lean_float_of_nat(v___x_1235_);
v___x_1238_ = lean_box_float(v___x_1236_);
v___x_1239_ = lean_box_float(v___x_1237_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1234_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1180_, v___x_1225_, v___x_1226_, v___y_1233_, v___y_1228_, v___y_1230_, v___f_1178_, v___x_1241_, v___y_1231_, v___y_1229_);
v___y_1221_ = v___y_1229_;
v___y_1222_ = v___y_1231_;
v___y_1223_ = v___x_1242_;
goto v___jp_1220_;
}
v___jp_1243_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1250_);
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1246_;
v___y_1230_ = v___y_1245_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v___y_1248_;
v___y_1233_ = v___y_1249_;
v_a_1234_ = v___x_1251_;
goto v___jp_1227_;
}
v___jp_1252_:
{
lean_object* v___x_1260_; double v___x_1261_; double v___x_1262_; double v___x_1263_; double v___x_1264_; double v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1260_ = lean_io_mono_nanos_now();
v___x_1261_ = lean_float_of_nat(v___y_1254_);
v___x_1262_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1263_ = lean_float_div(v___x_1261_, v___x_1262_);
v___x_1264_ = lean_float_of_nat(v___x_1260_);
v___x_1265_ = lean_float_div(v___x_1264_, v___x_1262_);
v___x_1266_ = lean_box_float(v___x_1263_);
v___x_1267_ = lean_box_float(v___x_1265_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1259_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1180_, v___x_1225_, v___x_1226_, v___y_1258_, v___y_1253_, v___y_1256_, v___f_1178_, v___x_1269_, v___y_1257_, v___y_1255_);
v___y_1221_ = v___y_1255_;
v___y_1222_ = v___y_1257_;
v___y_1223_ = v___x_1270_;
goto v___jp_1220_;
}
v___jp_1271_:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1278_);
v___y_1253_ = v___y_1272_;
v___y_1254_ = v___y_1273_;
v___y_1255_ = v___y_1275_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1276_;
v___y_1258_ = v___y_1277_;
v_a_1259_ = v___x_1279_;
goto v___jp_1252_;
}
v___jp_1280_:
{
lean_object* v___x_1287_; lean_object* v_a_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1287_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_1283_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1290_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_io_mono_nanos_now();
v___x_1292_ = l_IO_lazyPure___redArg(v___y_1281_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 1);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
v___y_1253_ = v___y_1282_;
v___y_1254_ = v___x_1291_;
v___y_1255_ = v___y_1283_;
v___y_1256_ = v_a_1288_;
v___y_1257_ = v___y_1285_;
v___y_1258_ = v___y_1286_;
v_a_1259_ = v___x_1300_;
goto v___jp_1252_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1313_; 
v_a_1303_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1305_ = v___x_1294_;
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1294_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_io_error_to_string(v_a_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 3);
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = l_Lean_MessageData_ofFormat(v___x_1309_);
lean_inc(v___y_1284_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___y_1284_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___y_1272_ = v___y_1282_;
v___y_1273_ = v___x_1291_;
v___y_1274_ = v_a_1288_;
v___y_1275_ = v___y_1283_;
v___y_1276_ = v___y_1285_;
v___y_1277_ = v___y_1286_;
v_a_1278_ = v___x_1311_;
goto v___jp_1271_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1324_; 
v_a_1314_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1316_ = v___x_1292_;
v_isShared_1317_ = v_isSharedCheck_1324_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1292_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1324_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_io_error_to_string(v_a_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set_tag(v___x_1316_, 3);
lean_ctor_set(v___x_1316_, 0, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = l_Lean_MessageData_ofFormat(v___x_1320_);
lean_inc(v___y_1284_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___y_1284_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___y_1272_ = v___y_1282_;
v___y_1273_ = v___x_1291_;
v___y_1274_ = v_a_1288_;
v___y_1275_ = v___y_1283_;
v___y_1276_ = v___y_1285_;
v___y_1277_ = v___y_1286_;
v_a_1278_ = v___x_1322_;
goto v___jp_1271_;
}
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_io_get_num_heartbeats();
v___x_1326_ = l_IO_lazyPure___redArg(v___y_1281_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 1);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
v___y_1228_ = v___y_1282_;
v___y_1229_ = v___y_1283_;
v___y_1230_ = v_a_1288_;
v___y_1231_ = v___y_1285_;
v___y_1232_ = v___x_1325_;
v___y_1233_ = v___y_1286_;
v_a_1234_ = v___x_1334_;
goto v___jp_1227_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1347_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1347_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_io_error_to_string(v_a_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 3);
lean_ctor_set(v___x_1339_, 0, v___x_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_MessageData_ofFormat(v___x_1343_);
lean_inc(v___y_1284_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___y_1284_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___y_1244_ = v___y_1282_;
v___y_1245_ = v_a_1288_;
v___y_1246_ = v___y_1283_;
v___y_1247_ = v___y_1285_;
v___y_1248_ = v___x_1325_;
v___y_1249_ = v___y_1286_;
v_a_1250_ = v___x_1345_;
goto v___jp_1243_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1358_; 
v_a_1348_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1350_ = v___x_1326_;
v_isShared_1351_ = v_isSharedCheck_1358_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1326_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1358_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_io_error_to_string(v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 3);
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = l_Lean_MessageData_ofFormat(v___x_1354_);
lean_inc(v___y_1284_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___y_1284_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___y_1244_ = v___y_1282_;
v___y_1245_ = v_a_1288_;
v___y_1246_ = v___y_1283_;
v___y_1247_ = v___y_1285_;
v___y_1248_ = v___x_1325_;
v___y_1249_ = v___y_1286_;
v_a_1250_ = v___x_1356_;
goto v___jp_1243_;
}
}
}
}
}
v___jp_1359_:
{
if (v_trimProofs_1169_ == 0)
{
lean_dec_ref(v___y_1361_);
v_proof_1182_ = v___y_1360_;
v___y_1183_ = v___y_1362_;
v___y_1184_ = v___y_1363_;
goto v___jp_1181_;
}
else
{
lean_object* v_options_1364_; uint8_t v_hasTrace_1365_; 
lean_dec_ref(v___y_1360_);
v_options_1364_ = lean_ctor_get(v___y_1362_, 2);
v_hasTrace_1365_ = lean_ctor_get_uint8(v_options_1364_, sizeof(void*)*1);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_ref_1366_; lean_object* v___x_1367_; 
v_ref_1366_ = lean_ctor_get(v___y_1362_, 5);
v___x_1367_ = l_IO_lazyPure___redArg(v___y_1361_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v_proof_1182_ = v_a_1370_;
v___y_1183_ = v___y_1362_;
v___y_1184_ = v___y_1363_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1382_; 
v_a_1371_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1373_ = v___x_1369_;
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1382_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1375_ = lean_io_error_to_string(v_a_1371_);
v___x_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
v___x_1377_ = l_Lean_MessageData_ofFormat(v___x_1376_);
lean_inc(v_ref_1366_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_ref_1366_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1378_);
v___x_1380_ = v___x_1373_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1394_; 
v_a_1383_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1385_ = v___x_1367_;
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1367_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1387_ = lean_io_error_to_string(v_a_1383_);
v___x_1388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___x_1389_ = l_Lean_MessageData_ofFormat(v___x_1388_);
lean_inc(v_ref_1366_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_ref_1366_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1390_);
v___x_1392_ = v___x_1385_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_ref_1395_; lean_object* v___x_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1438_; 
v_ref_1395_ = lean_ctor_get(v___y_1362_, 5);
v___x_1396_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1180_, v___y_1362_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1438_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1438_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_unbox(v_a_1397_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = l_Lean_trace_profiler;
v___x_1403_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1364_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec(v_a_1397_);
v___x_1404_ = l_IO_lazyPure___redArg(v___y_1361_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1405_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; 
lean_del_object(v___x_1399_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v_proof_1182_ = v_a_1407_;
v___y_1183_ = v___y_1362_;
v___y_1184_ = v___y_1363_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_a_1408_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1410_ = v___x_1406_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_io_error_to_string(v_a_1408_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 3);
lean_ctor_set(v___x_1399_, 0, v___x_1412_);
v___x_1414_ = v___x_1399_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = l_Lean_MessageData_ofFormat(v___x_1414_);
lean_inc(v_ref_1395_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_ref_1395_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1416_);
v___x_1418_ = v___x_1410_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1435_; 
v_a_1422_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1424_ = v___x_1404_;
v_isShared_1425_ = v_isSharedCheck_1435_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1404_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1435_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_io_error_to_string(v_a_1422_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 3);
lean_ctor_set(v___x_1399_, 0, v___x_1426_);
v___x_1428_ = v___x_1399_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = l_Lean_MessageData_ofFormat(v___x_1428_);
lean_inc(v_ref_1395_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_ref_1395_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1430_);
v___x_1432_ = v___x_1424_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
else
{
uint8_t v___x_1436_; 
lean_del_object(v___x_1399_);
v___x_1436_ = lean_unbox(v_a_1397_);
lean_dec(v_a_1397_);
v___y_1281_ = v___y_1361_;
v___y_1282_ = v___x_1436_;
v___y_1283_ = v___y_1363_;
v___y_1284_ = v_ref_1395_;
v___y_1285_ = v___y_1362_;
v___y_1286_ = v_options_1364_;
goto v___jp_1280_;
}
}
else
{
uint8_t v___x_1437_; 
lean_del_object(v___x_1399_);
v___x_1437_ = lean_unbox(v_a_1397_);
lean_dec(v_a_1397_);
v___y_1281_ = v___y_1361_;
v___y_1282_ = v___x_1437_;
v___y_1283_ = v___y_1363_;
v___y_1284_ = v_ref_1395_;
v___y_1285_ = v___y_1362_;
v___y_1286_ = v_options_1364_;
goto v___jp_1280_;
}
}
}
}
}
v___jp_1439_:
{
lean_object* v___x_1441_; lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1467_; 
v___x_1441_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1180_, v_a_1170_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1467_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1467_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___f_1446_; uint8_t v___x_1447_; 
lean_inc_ref(v_a_1440_);
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1446_, 0, v_a_1440_);
v___x_1447_ = lean_unbox(v_a_1442_);
lean_dec(v_a_1442_);
if (v___x_1447_ == 0)
{
lean_del_object(v___x_1444_);
v___y_1360_ = v_a_1440_;
v___y_1361_ = v___f_1446_;
v___y_1362_ = v_a_1170_;
v___y_1363_ = v_a_1171_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1449_ = lean_array_get_size(v_a_1440_);
v___x_1450_ = l_Nat_reprFast(v___x_1449_);
v___x_1451_ = lean_string_append(v___x_1448_, v___x_1450_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4));
v___x_1453_ = lean_string_append(v___x_1451_, v___x_1452_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 3);
lean_ctor_set(v___x_1444_, 0, v___x_1453_);
v___x_1455_ = v___x_1444_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = l_Lean_MessageData_ofFormat(v___x_1455_);
v___x_1457_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___x_1180_, v___x_1456_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_dec_ref(v___x_1457_);
v___y_1360_ = v_a_1440_;
v___y_1361_ = v___f_1446_;
v___y_1362_ = v_a_1170_;
v___y_1363_ = v_a_1171_;
goto v___jp_1359_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___f_1446_);
lean_dec_ref(v_a_1440_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
}
}
v___jp_1468_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___y_1469_);
v_a_1440_ = v_a_1470_;
goto v___jp_1439_;
}
else
{
return v___y_1469_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1631_; 
v_a_1619_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1621_ = v___x_1173_;
v_isShared_1622_ = v_isSharedCheck_1631_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1173_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1631_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_ref_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v_ref_1623_ = lean_ctor_get(v_a_1170_, 5);
v___x_1624_ = lean_io_error_to_string(v_a_1619_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = l_Lean_MessageData_ofFormat(v___x_1625_);
lean_inc(v_ref_1623_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_ref_1623_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1627_);
v___x_1629_ = v___x_1621_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object* v_lratPath_1632_, lean_object* v_trimProofs_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
uint8_t v_trimProofs_boxed_1637_; lean_object* v_res_1638_; 
v_trimProofs_boxed_1637_ = lean_unbox(v_trimProofs_1633_);
v_res_1638_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1632_, v_trimProofs_boxed_1637_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec_ref(v_lratPath_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8(lean_object* v_00_u03b1_1639_, lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_x_1640_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8(v_00_u03b1_1645_, v_x_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6(lean_object* v_00_u03b1_1651_, lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v_msg_1652_, v___y_1653_, v___y_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___boxed(lean_object* v_00_u03b1_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6(v_00_u03b1_1657_, v_msg_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object* v_lratPath_1663_, uint8_t v_trimProofs_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1663_, v_trimProofs_1664_, v_a_1665_, v_a_1666_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1669_);
lean_dec(v_a_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1668_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1668_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object* v_lratPath_1686_, lean_object* v_trimProofs_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
uint8_t v_trimProofs_boxed_1691_; lean_object* v_res_1692_; 
v_trimProofs_boxed_1691_ = lean_unbox(v_trimProofs_1687_);
v_res_1692_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_1686_, v_trimProofs_boxed_1691_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec_ref(v_lratPath_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1693_, lean_object* v___y_1694_, lean_object* v_a_x3f_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_io_remove_file(v_snd_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1718_; 
v_a_1706_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1708_ = v___x_1697_;
v_isShared_1709_ = v_isSharedCheck_1718_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1697_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1718_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_ref_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v_ref_1710_ = lean_ctor_get(v___y_1694_, 5);
v___x_1711_ = lean_io_error_to_string(v_a_1706_);
v___x_1712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
v___x_1713_ = l_Lean_MessageData_ofFormat(v___x_1712_);
lean_inc(v_ref_1710_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_ref_1710_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1714_);
v___x_1716_ = v___x_1708_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1719_, lean_object* v___y_1720_, lean_object* v_a_x3f_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1719_, v___y_1720_, v_a_x3f_1721_);
lean_dec(v_a_x3f_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_snd_1719_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(lean_object* v_f_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_fst_1730_; lean_object* v_snd_1731_; lean_object* v_r_1732_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v_fst_1730_ = lean_ctor_get(v_a_1729_, 0);
lean_inc(v_fst_1730_);
v_snd_1731_ = lean_ctor_get(v_a_1729_, 1);
lean_inc(v_snd_1731_);
lean_dec(v_a_1729_);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v_snd_1731_);
v_r_1732_ = lean_apply_5(v_f_1724_, v_fst_1730_, v_snd_1731_, v___y_1725_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v_r_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1757_; 
v_a_1733_ = lean_ctor_get(v_r_1732_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_r_1732_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1735_ = v_r_1732_;
v_isShared_1736_ = v_isSharedCheck_1757_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v_r_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1757_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
lean_inc(v_a_1733_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 1);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1731_, v___y_1725_, v___x_1738_);
lean_dec_ref(v___x_1738_);
lean_dec(v_snd_1731_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1739_, 0);
lean_dec(v_unused_1747_);
v___x_1741_ = v___x_1739_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_dec(v___x_1739_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_a_1733_);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1733_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1733_);
v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1739_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1758_ = lean_ctor_get(v_r_1732_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v_r_1732_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1731_, v___y_1725_, v___x_1759_);
lean_dec(v_snd_1731_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v___x_1760_, 0);
lean_dec(v_unused_1768_);
v___x_1762_ = v___x_1760_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_dec(v___x_1760_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v_a_1758_);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1758_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1758_);
v_a_1769_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_f_1724_);
v_a_1777_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1779_ = v___x_1728_;
v_isShared_1780_ = v_isSharedCheck_1789_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1728_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1789_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_ref_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v_ref_1781_ = lean_ctor_get(v___y_1725_, 5);
v___x_1782_ = lean_io_error_to_string(v_a_1777_);
v___x_1783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
lean_inc(v_ref_1781_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_ref_1781_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1785_);
v___x_1787_ = v___x_1779_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___boxed(lean_object* v_f_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(lean_object* v_00_u03b1_1795_, lean_object* v_f_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_f_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(v_00_u03b1_1801_, v_f_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object* v_cnf_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_Sat_CNF_dimacs(v_cnf_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object* v_cnf_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(v_cnf_1810_, v_x_1811_);
lean_dec_ref(v_cnf_1810_);
return v_res_1812_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1));
v___x_1817_ = l_Lean_MessageData_ofFormat(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(v_x_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_x_1824_);
return v_res_1828_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1));
v___x_1833_ = l_Lean_MessageData_ofFormat(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object* v_x_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(v_x_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_x_1840_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1));
v___x_1849_ = l_Lean_MessageData_ofFormat(v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(v_x_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec_ref(v_x_1856_);
return v_res_1860_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(lean_object* v_e_1861_){
_start:
{
if (lean_obj_tag(v_e_1861_) == 0)
{
uint8_t v___x_1862_; 
v___x_1862_ = 2;
return v___x_1862_;
}
else
{
uint8_t v___x_1863_; 
v___x_1863_ = 0;
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_e_1864_);
lean_dec_ref(v_e_1864_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object* v_cls_1867_, uint8_t v_collapsed_1868_, lean_object* v_tag_1869_, lean_object* v_opts_1870_, uint8_t v_clsEnabled_1871_, lean_object* v_oldTraces_1872_, lean_object* v_msg_1873_, lean_object* v_resStartStop_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1977_; 
v_fst_1878_ = lean_ctor_get(v_resStartStop_1874_, 0);
v_snd_1879_ = lean_ctor_get(v_resStartStop_1874_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_resStartStop_1874_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1881_ = v_resStartStop_1874_;
v_isShared_1882_ = v_isSharedCheck_1977_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_inc(v_fst_1878_);
lean_dec(v_resStartStop_1874_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1977_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_data_1886_; lean_object* v_fst_1897_; lean_object* v_snd_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1976_; 
v_fst_1897_ = lean_ctor_get(v_snd_1879_, 0);
v_snd_1898_ = lean_ctor_get(v_snd_1879_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_snd_1879_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1900_ = v_snd_1879_;
v_isShared_1901_ = v_isSharedCheck_1976_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snd_1898_);
lean_inc(v_fst_1897_);
lean_dec(v_snd_1879_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1976_;
goto v_resetjp_1899_;
}
v___jp_1883_:
{
lean_object* v___x_1887_; 
lean_inc(v___y_1884_);
v___x_1887_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_1872_, v_data_1886_, v___y_1884_, v___y_1885_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v___x_1887_);
v___x_1888_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_1878_);
return v___x_1888_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_fst_1878_);
v_a_1889_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1887_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___y_1905_; lean_object* v_a_1906_; uint8_t v___y_1930_; double v___y_1961_; 
v___x_1902_ = l_Lean_trace_profiler;
v___x_1903_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_1870_, v___x_1902_);
if (v___x_1903_ == 0)
{
v___y_1930_ = v___x_1903_;
goto v___jp_1929_;
}
else
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1967_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_1870_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; double v___x_1970_; double v___x_1971_; double v___x_1972_; 
v___x_1968_ = l_Lean_trace_profiler_threshold;
v___x_1969_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_1870_, v___x_1968_);
v___x_1970_ = lean_float_of_nat(v___x_1969_);
v___x_1971_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_1972_ = lean_float_div(v___x_1970_, v___x_1971_);
v___y_1961_ = v___x_1972_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; double v___x_1975_; 
v___x_1973_ = l_Lean_trace_profiler_threshold;
v___x_1974_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_1870_, v___x_1973_);
v___x_1975_ = lean_float_of_nat(v___x_1974_);
v___y_1961_ = v___x_1975_;
goto v___jp_1960_;
}
}
v___jp_1904_:
{
uint8_t v_result_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v_result_1907_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_fst_1878_);
v___x_1908_ = l_Lean_TraceResult_toEmoji(v_result_1907_);
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
v___x_1910_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 7);
lean_ctor_set(v___x_1900_, 1, v___x_1910_);
lean_ctor_set(v___x_1900_, 0, v___x_1909_);
v___x_1912_ = v___x_1900_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v_m_1914_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 7);
lean_ctor_set(v___x_1881_, 1, v_a_1906_);
lean_ctor_set(v___x_1881_, 0, v___x_1912_);
v_m_1914_ = v___x_1881_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_a_1906_);
v_m_1914_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; double v___x_1917_; lean_object* v_data_1918_; 
v___x_1915_ = lean_box(v_result_1907_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
v___x_1917_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_1869_);
lean_inc_ref(v___x_1916_);
lean_inc(v_cls_1867_);
v_data_1918_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1918_, 0, v_cls_1867_);
lean_ctor_set(v_data_1918_, 1, v___x_1916_);
lean_ctor_set(v_data_1918_, 2, v_tag_1869_);
lean_ctor_set_float(v_data_1918_, sizeof(void*)*3, v___x_1917_);
lean_ctor_set_float(v_data_1918_, sizeof(void*)*3 + 8, v___x_1917_);
lean_ctor_set_uint8(v_data_1918_, sizeof(void*)*3 + 16, v_collapsed_1868_);
if (v___x_1903_ == 0)
{
lean_dec_ref(v___x_1916_);
lean_dec(v_snd_1898_);
lean_dec(v_fst_1897_);
lean_dec_ref(v_tag_1869_);
lean_dec(v_cls_1867_);
v___y_1884_ = v___y_1905_;
v___y_1885_ = v_m_1914_;
v_data_1886_ = v_data_1918_;
goto v___jp_1883_;
}
else
{
lean_object* v_data_1919_; double v___x_1920_; double v___x_1921_; 
lean_dec_ref(v_data_1918_);
v_data_1919_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1919_, 0, v_cls_1867_);
lean_ctor_set(v_data_1919_, 1, v___x_1916_);
lean_ctor_set(v_data_1919_, 2, v_tag_1869_);
v___x_1920_ = lean_unbox_float(v_fst_1897_);
lean_dec(v_fst_1897_);
lean_ctor_set_float(v_data_1919_, sizeof(void*)*3, v___x_1920_);
v___x_1921_ = lean_unbox_float(v_snd_1898_);
lean_dec(v_snd_1898_);
lean_ctor_set_float(v_data_1919_, sizeof(void*)*3 + 8, v___x_1921_);
lean_ctor_set_uint8(v_data_1919_, sizeof(void*)*3 + 16, v_collapsed_1868_);
v___y_1884_ = v___y_1905_;
v___y_1885_ = v_m_1914_;
v_data_1886_ = v_data_1919_;
goto v___jp_1883_;
}
}
}
}
v___jp_1924_:
{
lean_object* v_ref_1925_; lean_object* v___x_1926_; 
v_ref_1925_ = lean_ctor_get(v___y_1875_, 5);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc(v_fst_1878_);
v___x_1926_ = lean_apply_4(v_msg_1873_, v_fst_1878_, v___y_1875_, v___y_1876_, lean_box(0));
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v___y_1905_ = v_ref_1925_;
v_a_1906_ = v_a_1927_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1928_; 
lean_dec_ref(v___x_1926_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
v___y_1905_ = v_ref_1925_;
v_a_1906_ = v___x_1928_;
goto v___jp_1904_;
}
}
v___jp_1929_:
{
if (v_clsEnabled_1871_ == 0)
{
if (v___y_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v_traceState_1932_; lean_object* v_env_1933_; lean_object* v_nextMacroScope_1934_; lean_object* v_ngen_1935_; lean_object* v_auxDeclNGen_1936_; lean_object* v_cache_1937_; lean_object* v_messages_1938_; lean_object* v_infoState_1939_; lean_object* v_snapshotTasks_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1959_; 
lean_del_object(v___x_1900_);
lean_dec(v_snd_1898_);
lean_dec(v_fst_1897_);
lean_del_object(v___x_1881_);
lean_dec_ref(v_msg_1873_);
lean_dec_ref(v_tag_1869_);
lean_dec(v_cls_1867_);
v___x_1931_ = lean_st_ref_take(v___y_1876_);
v_traceState_1932_ = lean_ctor_get(v___x_1931_, 4);
v_env_1933_ = lean_ctor_get(v___x_1931_, 0);
v_nextMacroScope_1934_ = lean_ctor_get(v___x_1931_, 1);
v_ngen_1935_ = lean_ctor_get(v___x_1931_, 2);
v_auxDeclNGen_1936_ = lean_ctor_get(v___x_1931_, 3);
v_cache_1937_ = lean_ctor_get(v___x_1931_, 5);
v_messages_1938_ = lean_ctor_get(v___x_1931_, 6);
v_infoState_1939_ = lean_ctor_get(v___x_1931_, 7);
v_snapshotTasks_1940_ = lean_ctor_get(v___x_1931_, 8);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1942_ = v___x_1931_;
v_isShared_1943_ = v_isSharedCheck_1959_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_snapshotTasks_1940_);
lean_inc(v_infoState_1939_);
lean_inc(v_messages_1938_);
lean_inc(v_cache_1937_);
lean_inc(v_traceState_1932_);
lean_inc(v_auxDeclNGen_1936_);
lean_inc(v_ngen_1935_);
lean_inc(v_nextMacroScope_1934_);
lean_inc(v_env_1933_);
lean_dec(v___x_1931_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1959_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint64_t v_tid_1944_; lean_object* v_traces_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1958_; 
v_tid_1944_ = lean_ctor_get_uint64(v_traceState_1932_, sizeof(void*)*1);
v_traces_1945_ = lean_ctor_get(v_traceState_1932_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_traceState_1932_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1947_ = v_traceState_1932_;
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_traces_1945_);
lean_dec(v_traceState_1932_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1872_, v_traces_1945_);
lean_dec_ref(v_traces_1945_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1949_);
v___x_1951_ = v___x_1947_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1949_);
lean_ctor_set_uint64(v_reuseFailAlloc_1957_, sizeof(void*)*1, v_tid_1944_);
v___x_1951_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_1951_);
v___x_1953_ = v___x_1942_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_env_1933_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_nextMacroScope_1934_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_ngen_1935_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_auxDeclNGen_1936_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1956_, 5, v_cache_1937_);
lean_ctor_set(v_reuseFailAlloc_1956_, 6, v_messages_1938_);
lean_ctor_set(v_reuseFailAlloc_1956_, 7, v_infoState_1939_);
lean_ctor_set(v_reuseFailAlloc_1956_, 8, v_snapshotTasks_1940_);
v___x_1953_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_st_ref_set(v___y_1876_, v___x_1953_);
v___x_1955_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_1878_);
return v___x_1955_;
}
}
}
}
}
else
{
goto v___jp_1924_;
}
}
else
{
goto v___jp_1924_;
}
}
v___jp_1960_:
{
double v___x_1962_; double v___x_1963_; double v___x_1964_; uint8_t v___x_1965_; 
v___x_1962_ = lean_unbox_float(v_snd_1898_);
v___x_1963_ = lean_unbox_float(v_fst_1897_);
v___x_1964_ = lean_float_sub(v___x_1962_, v___x_1963_);
v___x_1965_ = lean_float_decLt(v___y_1961_, v___x_1964_);
v___y_1930_ = v___x_1965_;
goto v___jp_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___boxed(lean_object* v_cls_1978_, lean_object* v_collapsed_1979_, lean_object* v_tag_1980_, lean_object* v_opts_1981_, lean_object* v_clsEnabled_1982_, lean_object* v_oldTraces_1983_, lean_object* v_msg_1984_, lean_object* v_resStartStop_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v_collapsed_boxed_1989_; uint8_t v_clsEnabled_boxed_1990_; lean_object* v_res_1991_; 
v_collapsed_boxed_1989_ = lean_unbox(v_collapsed_1979_);
v_clsEnabled_boxed_1990_ = lean_unbox(v_clsEnabled_1982_);
v_res_1991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v_cls_1978_, v_collapsed_boxed_1989_, v_tag_1980_, v_opts_1981_, v_clsEnabled_boxed_1990_, v_oldTraces_1983_, v_msg_1984_, v_resStartStop_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec_ref(v_opts_1981_);
return v_res_1991_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(lean_object* v_e_1992_){
_start:
{
if (lean_obj_tag(v_e_1992_) == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = 2;
return v___x_1993_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = 0;
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2___boxed(lean_object* v_e_1995_){
_start:
{
uint8_t v_res_1996_; lean_object* v_r_1997_; 
v_res_1996_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_e_1995_);
lean_dec_ref(v_e_1995_);
v_r_1997_ = lean_box(v_res_1996_);
return v_r_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(lean_object* v_cls_1998_, uint8_t v_collapsed_1999_, lean_object* v_tag_2000_, lean_object* v_opts_2001_, uint8_t v_clsEnabled_2002_, lean_object* v_oldTraces_2003_, lean_object* v_msg_2004_, lean_object* v_resStartStop_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2108_; 
v_fst_2009_ = lean_ctor_get(v_resStartStop_2005_, 0);
v_snd_2010_ = lean_ctor_get(v_resStartStop_2005_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_resStartStop_2005_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2012_ = v_resStartStop_2005_;
v_isShared_2013_ = v_isSharedCheck_2108_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2010_);
lean_inc(v_fst_2009_);
lean_dec(v_resStartStop_2005_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2108_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v_data_2017_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2107_; 
v_fst_2028_ = lean_ctor_get(v_snd_2010_, 0);
v_snd_2029_ = lean_ctor_get(v_snd_2010_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_snd_2010_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2031_ = v_snd_2010_;
v_isShared_2032_ = v_isSharedCheck_2107_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_snd_2010_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2107_;
goto v_resetjp_2030_;
}
v___jp_2014_:
{
lean_object* v___x_2018_; 
lean_inc(v___y_2016_);
v___x_2018_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_2003_, v_data_2017_, v___y_2016_, v___y_2015_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref(v___x_2018_);
v___x_2019_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2009_);
return v___x_2019_;
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_fst_2009_);
v_a_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___y_2036_; lean_object* v_a_2037_; uint8_t v___y_2061_; double v___y_2092_; 
v___x_2033_ = l_Lean_trace_profiler;
v___x_2034_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2001_, v___x_2033_);
if (v___x_2034_ == 0)
{
v___y_2061_ = v___x_2034_;
goto v___jp_2060_;
}
else
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2098_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2001_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; double v___x_2101_; double v___x_2102_; double v___x_2103_; 
v___x_2099_ = l_Lean_trace_profiler_threshold;
v___x_2100_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2001_, v___x_2099_);
v___x_2101_ = lean_float_of_nat(v___x_2100_);
v___x_2102_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_2103_ = lean_float_div(v___x_2101_, v___x_2102_);
v___y_2092_ = v___x_2103_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; double v___x_2106_; 
v___x_2104_ = l_Lean_trace_profiler_threshold;
v___x_2105_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2001_, v___x_2104_);
v___x_2106_ = lean_float_of_nat(v___x_2105_);
v___y_2092_ = v___x_2106_;
goto v___jp_2091_;
}
}
v___jp_2035_:
{
uint8_t v_result_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v_result_2038_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_fst_2009_);
v___x_2039_ = l_Lean_TraceResult_toEmoji(v_result_2038_);
v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
v___x_2041_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 7);
lean_ctor_set(v___x_2031_, 1, v___x_2041_);
lean_ctor_set(v___x_2031_, 0, v___x_2040_);
v___x_2043_ = v___x_2031_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v_m_2045_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 7);
lean_ctor_set(v___x_2012_, 1, v_a_2037_);
lean_ctor_set(v___x_2012_, 0, v___x_2043_);
v_m_2045_ = v___x_2012_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2037_);
v_m_2045_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; double v___x_2048_; lean_object* v_data_2049_; 
v___x_2046_ = lean_box(v_result_2038_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2000_);
lean_inc_ref(v___x_2047_);
lean_inc(v_cls_1998_);
v_data_2049_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2049_, 0, v_cls_1998_);
lean_ctor_set(v_data_2049_, 1, v___x_2047_);
lean_ctor_set(v_data_2049_, 2, v_tag_2000_);
lean_ctor_set_float(v_data_2049_, sizeof(void*)*3, v___x_2048_);
lean_ctor_set_float(v_data_2049_, sizeof(void*)*3 + 8, v___x_2048_);
lean_ctor_set_uint8(v_data_2049_, sizeof(void*)*3 + 16, v_collapsed_1999_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v___x_2047_);
lean_dec(v_snd_2029_);
lean_dec(v_fst_2028_);
lean_dec_ref(v_tag_2000_);
lean_dec(v_cls_1998_);
v___y_2015_ = v_m_2045_;
v___y_2016_ = v___y_2036_;
v_data_2017_ = v_data_2049_;
goto v___jp_2014_;
}
else
{
lean_object* v_data_2050_; double v___x_2051_; double v___x_2052_; 
lean_dec_ref(v_data_2049_);
v_data_2050_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2050_, 0, v_cls_1998_);
lean_ctor_set(v_data_2050_, 1, v___x_2047_);
lean_ctor_set(v_data_2050_, 2, v_tag_2000_);
v___x_2051_ = lean_unbox_float(v_fst_2028_);
lean_dec(v_fst_2028_);
lean_ctor_set_float(v_data_2050_, sizeof(void*)*3, v___x_2051_);
v___x_2052_ = lean_unbox_float(v_snd_2029_);
lean_dec(v_snd_2029_);
lean_ctor_set_float(v_data_2050_, sizeof(void*)*3 + 8, v___x_2052_);
lean_ctor_set_uint8(v_data_2050_, sizeof(void*)*3 + 16, v_collapsed_1999_);
v___y_2015_ = v_m_2045_;
v___y_2016_ = v___y_2036_;
v_data_2017_ = v_data_2050_;
goto v___jp_2014_;
}
}
}
}
v___jp_2055_:
{
lean_object* v_ref_2056_; lean_object* v___x_2057_; 
v_ref_2056_ = lean_ctor_get(v___y_2006_, 5);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v_fst_2009_);
v___x_2057_ = lean_apply_4(v_msg_2004_, v_fst_2009_, v___y_2006_, v___y_2007_, lean_box(0));
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___y_2036_ = v_ref_2056_;
v_a_2037_ = v_a_2058_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2059_; 
lean_dec_ref(v___x_2057_);
v___x_2059_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
v___y_2036_ = v_ref_2056_;
v_a_2037_ = v___x_2059_;
goto v___jp_2035_;
}
}
v___jp_2060_:
{
if (v_clsEnabled_2002_ == 0)
{
if (v___y_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v_traceState_2063_; lean_object* v_env_2064_; lean_object* v_nextMacroScope_2065_; lean_object* v_ngen_2066_; lean_object* v_auxDeclNGen_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2090_; 
lean_del_object(v___x_2031_);
lean_dec(v_snd_2029_);
lean_dec(v_fst_2028_);
lean_del_object(v___x_2012_);
lean_dec_ref(v_msg_2004_);
lean_dec_ref(v_tag_2000_);
lean_dec(v_cls_1998_);
v___x_2062_ = lean_st_ref_take(v___y_2007_);
v_traceState_2063_ = lean_ctor_get(v___x_2062_, 4);
v_env_2064_ = lean_ctor_get(v___x_2062_, 0);
v_nextMacroScope_2065_ = lean_ctor_get(v___x_2062_, 1);
v_ngen_2066_ = lean_ctor_get(v___x_2062_, 2);
v_auxDeclNGen_2067_ = lean_ctor_get(v___x_2062_, 3);
v_cache_2068_ = lean_ctor_get(v___x_2062_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2062_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2062_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2062_, 8);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2073_ = v___x_2062_;
v_isShared_2074_ = v_isSharedCheck_2090_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2063_);
lean_inc(v_auxDeclNGen_2067_);
lean_inc(v_ngen_2066_);
lean_inc(v_nextMacroScope_2065_);
lean_inc(v_env_2064_);
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2090_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint64_t v_tid_2075_; lean_object* v_traces_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2089_; 
v_tid_2075_ = lean_ctor_get_uint64(v_traceState_2063_, sizeof(void*)*1);
v_traces_2076_ = lean_ctor_get(v_traceState_2063_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_traceState_2063_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2078_ = v_traceState_2063_;
v_isShared_2079_ = v_isSharedCheck_2089_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_traces_2076_);
lean_dec(v_traceState_2063_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2089_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2003_, v_traces_2076_);
lean_dec_ref(v_traces_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2080_);
lean_ctor_set_uint64(v_reuseFailAlloc_2088_, sizeof(void*)*1, v_tid_2075_);
v___x_2082_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v___x_2082_);
v___x_2084_ = v___x_2073_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_env_2064_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_nextMacroScope_2065_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_ngen_2066_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_auxDeclNGen_2067_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2087_, 6, v_messages_2069_);
lean_ctor_set(v_reuseFailAlloc_2087_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2087_, 8, v_snapshotTasks_2071_);
v___x_2084_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_st_ref_set(v___y_2007_, v___x_2084_);
v___x_2086_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2009_);
return v___x_2086_;
}
}
}
}
}
else
{
goto v___jp_2055_;
}
}
else
{
goto v___jp_2055_;
}
}
v___jp_2091_:
{
double v___x_2093_; double v___x_2094_; double v___x_2095_; uint8_t v___x_2096_; 
v___x_2093_ = lean_unbox_float(v_snd_2029_);
v___x_2094_ = lean_unbox_float(v_fst_2028_);
v___x_2095_ = lean_float_sub(v___x_2093_, v___x_2094_);
v___x_2096_ = lean_float_decLt(v___y_2092_, v___x_2095_);
v___y_2061_ = v___x_2096_;
goto v___jp_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1___boxed(lean_object* v_cls_2109_, lean_object* v_collapsed_2110_, lean_object* v_tag_2111_, lean_object* v_opts_2112_, lean_object* v_clsEnabled_2113_, lean_object* v_oldTraces_2114_, lean_object* v_msg_2115_, lean_object* v_resStartStop_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
uint8_t v_collapsed_boxed_2120_; uint8_t v_clsEnabled_boxed_2121_; lean_object* v_res_2122_; 
v_collapsed_boxed_2120_ = lean_unbox(v_collapsed_2110_);
v_clsEnabled_boxed_2121_ = lean_unbox(v_clsEnabled_2113_);
v_res_2122_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v_cls_2109_, v_collapsed_boxed_2120_, v_tag_2111_, v_opts_2112_, v_clsEnabled_boxed_2121_, v_oldTraces_2114_, v_msg_2115_, v_resStartStop_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_opts_2112_);
return v_res_2122_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(lean_object* v_e_2123_){
_start:
{
if (lean_obj_tag(v_e_2123_) == 0)
{
uint8_t v___x_2124_; 
v___x_2124_ = 2;
return v___x_2124_;
}
else
{
uint8_t v___x_2125_; 
v___x_2125_ = 0;
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4___boxed(lean_object* v_e_2126_){
_start:
{
uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_res_2127_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_e_2126_);
lean_dec_ref(v_e_2126_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(lean_object* v_cls_2129_, uint8_t v_collapsed_2130_, lean_object* v_tag_2131_, lean_object* v_opts_2132_, uint8_t v_clsEnabled_2133_, lean_object* v_oldTraces_2134_, lean_object* v_msg_2135_, lean_object* v_resStartStop_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2231_; 
v_fst_2140_ = lean_ctor_get(v_resStartStop_2136_, 0);
v_snd_2141_ = lean_ctor_get(v_resStartStop_2136_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_resStartStop_2136_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2143_ = v_resStartStop_2136_;
v_isShared_2144_ = v_isSharedCheck_2231_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snd_2141_);
lean_inc(v_fst_2140_);
lean_dec(v_resStartStop_2136_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2231_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v_data_2148_; lean_object* v_fst_2151_; lean_object* v_snd_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2230_; 
v_fst_2151_ = lean_ctor_get(v_snd_2141_, 0);
v_snd_2152_ = lean_ctor_get(v_snd_2141_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_snd_2141_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2154_ = v_snd_2141_;
v_isShared_2155_ = v_isSharedCheck_2230_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_snd_2152_);
lean_inc(v_fst_2151_);
lean_dec(v_snd_2141_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2230_;
goto v_resetjp_2153_;
}
v___jp_2145_:
{
lean_object* v___x_2149_; 
lean_inc(v___y_2147_);
v___x_2149_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_2134_, v_data_2148_, v___y_2147_, v___y_2146_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; 
lean_dec_ref(v___x_2149_);
v___x_2150_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2140_);
return v___x_2150_;
}
else
{
lean_dec(v_fst_2140_);
return v___x_2149_;
}
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___y_2159_; lean_object* v_a_2160_; uint8_t v___y_2184_; double v___y_2215_; 
v___x_2156_ = l_Lean_trace_profiler;
v___x_2157_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2132_, v___x_2156_);
if (v___x_2157_ == 0)
{
v___y_2184_ = v___x_2157_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2221_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2132_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; double v___x_2224_; double v___x_2225_; double v___x_2226_; 
v___x_2222_ = l_Lean_trace_profiler_threshold;
v___x_2223_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2132_, v___x_2222_);
v___x_2224_ = lean_float_of_nat(v___x_2223_);
v___x_2225_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_2226_ = lean_float_div(v___x_2224_, v___x_2225_);
v___y_2215_ = v___x_2226_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; double v___x_2229_; 
v___x_2227_ = l_Lean_trace_profiler_threshold;
v___x_2228_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2132_, v___x_2227_);
v___x_2229_ = lean_float_of_nat(v___x_2228_);
v___y_2215_ = v___x_2229_;
goto v___jp_2214_;
}
}
v___jp_2158_:
{
uint8_t v_result_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v_result_2161_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_fst_2140_);
v___x_2162_ = l_Lean_TraceResult_toEmoji(v_result_2161_);
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
v___x_2164_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_2155_ == 0)
{
lean_ctor_set_tag(v___x_2154_, 7);
lean_ctor_set(v___x_2154_, 1, v___x_2164_);
lean_ctor_set(v___x_2154_, 0, v___x_2163_);
v___x_2166_ = v___x_2154_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v_m_2168_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 7);
lean_ctor_set(v___x_2143_, 1, v_a_2160_);
lean_ctor_set(v___x_2143_, 0, v___x_2166_);
v_m_2168_ = v___x_2143_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_a_2160_);
v_m_2168_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; double v___x_2171_; lean_object* v_data_2172_; 
v___x_2169_ = lean_box(v_result_2161_);
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
v___x_2171_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2131_);
lean_inc_ref(v___x_2170_);
lean_inc(v_cls_2129_);
v_data_2172_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2172_, 0, v_cls_2129_);
lean_ctor_set(v_data_2172_, 1, v___x_2170_);
lean_ctor_set(v_data_2172_, 2, v_tag_2131_);
lean_ctor_set_float(v_data_2172_, sizeof(void*)*3, v___x_2171_);
lean_ctor_set_float(v_data_2172_, sizeof(void*)*3 + 8, v___x_2171_);
lean_ctor_set_uint8(v_data_2172_, sizeof(void*)*3 + 16, v_collapsed_2130_);
if (v___x_2157_ == 0)
{
lean_dec_ref(v___x_2170_);
lean_dec(v_snd_2152_);
lean_dec(v_fst_2151_);
lean_dec_ref(v_tag_2131_);
lean_dec(v_cls_2129_);
v___y_2146_ = v_m_2168_;
v___y_2147_ = v___y_2159_;
v_data_2148_ = v_data_2172_;
goto v___jp_2145_;
}
else
{
lean_object* v_data_2173_; double v___x_2174_; double v___x_2175_; 
lean_dec_ref(v_data_2172_);
v_data_2173_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2173_, 0, v_cls_2129_);
lean_ctor_set(v_data_2173_, 1, v___x_2170_);
lean_ctor_set(v_data_2173_, 2, v_tag_2131_);
v___x_2174_ = lean_unbox_float(v_fst_2151_);
lean_dec(v_fst_2151_);
lean_ctor_set_float(v_data_2173_, sizeof(void*)*3, v___x_2174_);
v___x_2175_ = lean_unbox_float(v_snd_2152_);
lean_dec(v_snd_2152_);
lean_ctor_set_float(v_data_2173_, sizeof(void*)*3 + 8, v___x_2175_);
lean_ctor_set_uint8(v_data_2173_, sizeof(void*)*3 + 16, v_collapsed_2130_);
v___y_2146_ = v_m_2168_;
v___y_2147_ = v___y_2159_;
v_data_2148_ = v_data_2173_;
goto v___jp_2145_;
}
}
}
}
v___jp_2178_:
{
lean_object* v_ref_2179_; lean_object* v___x_2180_; 
v_ref_2179_ = lean_ctor_get(v___y_2137_, 5);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc(v_fst_2140_);
v___x_2180_ = lean_apply_4(v_msg_2135_, v_fst_2140_, v___y_2137_, v___y_2138_, lean_box(0));
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v___y_2159_ = v_ref_2179_;
v_a_2160_ = v_a_2181_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2180_);
v___x_2182_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
v___y_2159_ = v_ref_2179_;
v_a_2160_ = v___x_2182_;
goto v___jp_2158_;
}
}
v___jp_2183_:
{
if (v_clsEnabled_2133_ == 0)
{
if (v___y_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v_traceState_2186_; lean_object* v_env_2187_; lean_object* v_nextMacroScope_2188_; lean_object* v_ngen_2189_; lean_object* v_auxDeclNGen_2190_; lean_object* v_cache_2191_; lean_object* v_messages_2192_; lean_object* v_infoState_2193_; lean_object* v_snapshotTasks_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
lean_dec(v_fst_2151_);
lean_del_object(v___x_2143_);
lean_dec_ref(v_msg_2135_);
lean_dec_ref(v_tag_2131_);
lean_dec(v_cls_2129_);
v___x_2185_ = lean_st_ref_take(v___y_2138_);
v_traceState_2186_ = lean_ctor_get(v___x_2185_, 4);
v_env_2187_ = lean_ctor_get(v___x_2185_, 0);
v_nextMacroScope_2188_ = lean_ctor_get(v___x_2185_, 1);
v_ngen_2189_ = lean_ctor_get(v___x_2185_, 2);
v_auxDeclNGen_2190_ = lean_ctor_get(v___x_2185_, 3);
v_cache_2191_ = lean_ctor_get(v___x_2185_, 5);
v_messages_2192_ = lean_ctor_get(v___x_2185_, 6);
v_infoState_2193_ = lean_ctor_get(v___x_2185_, 7);
v_snapshotTasks_2194_ = lean_ctor_get(v___x_2185_, 8);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2196_ = v___x_2185_;
v_isShared_2197_ = v_isSharedCheck_2213_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_snapshotTasks_2194_);
lean_inc(v_infoState_2193_);
lean_inc(v_messages_2192_);
lean_inc(v_cache_2191_);
lean_inc(v_traceState_2186_);
lean_inc(v_auxDeclNGen_2190_);
lean_inc(v_ngen_2189_);
lean_inc(v_nextMacroScope_2188_);
lean_inc(v_env_2187_);
lean_dec(v___x_2185_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2213_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
uint64_t v_tid_2198_; lean_object* v_traces_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2212_; 
v_tid_2198_ = lean_ctor_get_uint64(v_traceState_2186_, sizeof(void*)*1);
v_traces_2199_ = lean_ctor_get(v_traceState_2186_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_traceState_2186_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2201_ = v_traceState_2186_;
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_traces_2199_);
lean_dec(v_traceState_2186_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2212_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2134_, v_traces_2199_);
lean_dec_ref(v_traces_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2203_);
lean_ctor_set_uint64(v_reuseFailAlloc_2211_, sizeof(void*)*1, v_tid_2198_);
v___x_2205_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v___x_2205_);
v___x_2207_ = v___x_2196_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_env_2187_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_nextMacroScope_2188_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_ngen_2189_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_auxDeclNGen_2190_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2210_, 5, v_cache_2191_);
lean_ctor_set(v_reuseFailAlloc_2210_, 6, v_messages_2192_);
lean_ctor_set(v_reuseFailAlloc_2210_, 7, v_infoState_2193_);
lean_ctor_set(v_reuseFailAlloc_2210_, 8, v_snapshotTasks_2194_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_st_ref_set(v___y_2138_, v___x_2207_);
v___x_2209_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2140_);
return v___x_2209_;
}
}
}
}
}
else
{
goto v___jp_2178_;
}
}
else
{
goto v___jp_2178_;
}
}
v___jp_2214_:
{
double v___x_2216_; double v___x_2217_; double v___x_2218_; uint8_t v___x_2219_; 
v___x_2216_ = lean_unbox_float(v_snd_2152_);
v___x_2217_ = lean_unbox_float(v_fst_2151_);
v___x_2218_ = lean_float_sub(v___x_2216_, v___x_2217_);
v___x_2219_ = lean_float_decLt(v___y_2215_, v___x_2218_);
v___y_2184_ = v___x_2219_;
goto v___jp_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2___boxed(lean_object* v_cls_2232_, lean_object* v_collapsed_2233_, lean_object* v_tag_2234_, lean_object* v_opts_2235_, lean_object* v_clsEnabled_2236_, lean_object* v_oldTraces_2237_, lean_object* v_msg_2238_, lean_object* v_resStartStop_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_collapsed_boxed_2243_; uint8_t v_clsEnabled_boxed_2244_; lean_object* v_res_2245_; 
v_collapsed_boxed_2243_ = lean_unbox(v_collapsed_2233_);
v_clsEnabled_boxed_2244_ = lean_unbox(v_clsEnabled_2236_);
v_res_2245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v_cls_2232_, v_collapsed_boxed_2243_, v_tag_2234_, v_opts_2235_, v_clsEnabled_boxed_2244_, v_oldTraces_2237_, v_msg_2238_, v_resStartStop_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_opts_2235_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object* v___f_2246_, lean_object* v_lratPath_2247_, uint8_t v_trimProofs_2248_, lean_object* v___f_2249_, lean_object* v_solver_2250_, lean_object* v_timeout_2251_, uint8_t v_binaryProofs_2252_, uint8_t v_solverMode_2253_, lean_object* v___f_2254_, lean_object* v___f_2255_, lean_object* v_cnfHandle_2256_, lean_object* v_cnfPath_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___y_2262_; lean_object* v_options_2280_; lean_object* v_ref_2281_; uint8_t v_hasTrace_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___y_2287_; uint8_t v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v_a_2291_; lean_object* v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v_a_2308_; uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2361_; uint8_t v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v_a_2400_; uint8_t v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v_a_2417_; uint8_t v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2480_; 
v_options_2280_ = lean_ctor_get(v___y_2258_, 2);
v_ref_2281_ = lean_ctor_get(v___y_2258_, 5);
v_hasTrace_2282_ = lean_ctor_get_uint8(v_options_2280_, sizeof(void*)*1);
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_2284_ = 1;
v___x_2285_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_2282_ == 0)
{
lean_object* v___x_2489_; 
lean_dec_ref(v___f_2255_);
v___x_2489_ = l_IO_lazyPure___redArg(v___f_2254_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2491_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = lean_io_prim_handle_put_str(v_cnfHandle_2256_, v_a_2490_);
lean_dec(v_a_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v___x_2491_);
v___x_2492_ = lean_io_prim_handle_flush(v_cnfHandle_2256_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_dec_ref(v___x_2492_);
goto v___jp_2469_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2497_ = lean_io_error_to_string(v_a_2493_);
v___x_2498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
v___x_2499_ = l_Lean_MessageData_ofFormat(v___x_2498_);
lean_inc(v_ref_2281_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_ref_2281_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2500_);
v___x_2502_ = v___x_2495_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2505_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2507_ = v___x_2491_;
v_isShared_2508_ = v_isSharedCheck_2516_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2491_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2516_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2509_ = lean_io_error_to_string(v_a_2505_);
v___x_2510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
v___x_2511_ = l_Lean_MessageData_ofFormat(v___x_2510_);
lean_inc(v_ref_2281_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_ref_2281_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2512_);
v___x_2514_ = v___x_2507_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2517_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2519_ = v___x_2489_;
v_isShared_2520_ = v_isSharedCheck_2528_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2489_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2528_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2521_ = lean_io_error_to_string(v_a_2517_);
v___x_2522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
v___x_2523_ = l_Lean_MessageData_ofFormat(v___x_2522_);
lean_inc(v_ref_2281_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_ref_2281_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2524_);
v___x_2526_ = v___x_2519_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2715_; 
v___x_2529_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2283_, v___y_2258_);
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2715_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2715_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v_a_2537_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v_a_2553_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v_a_2560_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v_a_2573_; uint8_t v___x_2672_; 
v___x_2672_ = lean_unbox(v_a_2530_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = l_Lean_trace_profiler;
v___x_2674_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2280_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_del_object(v___x_2532_);
lean_dec(v_a_2530_);
lean_dec_ref(v___f_2255_);
v___x_2675_ = l_IO_lazyPure___redArg(v___f_2254_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = lean_io_prim_handle_put_str(v_cnfHandle_2256_, v_a_2676_);
lean_dec(v_a_2676_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2677_);
v___x_2678_ = lean_io_prim_handle_flush(v_cnfHandle_2256_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_dec_ref(v___x_2678_);
goto v___jp_2469_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2690_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2690_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2683_ = lean_io_error_to_string(v_a_2679_);
v___x_2684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
v___x_2685_ = l_Lean_MessageData_ofFormat(v___x_2684_);
lean_inc(v_ref_2281_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_ref_2281_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2686_);
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2691_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2693_ = v___x_2677_;
v_isShared_2694_ = v_isSharedCheck_2702_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2677_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2702_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2695_ = lean_io_error_to_string(v_a_2691_);
v___x_2696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
v___x_2697_ = l_Lean_MessageData_ofFormat(v___x_2696_);
lean_inc(v_ref_2281_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_ref_2281_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2698_);
v___x_2700_ = v___x_2693_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2703_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2705_ = v___x_2675_;
v_isShared_2706_ = v_isSharedCheck_2714_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2675_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2714_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2707_ = lean_io_error_to_string(v_a_2703_);
v___x_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
lean_inc(v_ref_2281_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_ref_2281_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2710_);
v___x_2712_ = v___x_2705_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
else
{
goto v___jp_2575_;
}
}
else
{
goto v___jp_2575_;
}
v___jp_2534_:
{
lean_object* v___x_2538_; double v___x_2539_; double v___x_2540_; double v___x_2541_; double v___x_2542_; double v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2538_ = lean_io_mono_nanos_now();
v___x_2539_ = lean_float_of_nat(v___y_2535_);
v___x_2540_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2541_ = lean_float_div(v___x_2539_, v___x_2540_);
v___x_2542_ = lean_float_of_nat(v___x_2538_);
v___x_2543_ = lean_float_div(v___x_2542_, v___x_2540_);
v___x_2544_ = lean_box_float(v___x_2541_);
v___x_2545_ = lean_box_float(v___x_2543_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_a_2537_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_unbox(v_a_2530_);
lean_dec(v_a_2530_);
v___x_2549_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2283_, v___x_2284_, v___x_2285_, v_options_2280_, v___x_2548_, v___y_2536_, v___f_2255_, v___x_2547_, v___y_2258_, v___y_2259_);
v___y_2480_ = v___x_2549_;
goto v___jp_2479_;
}
v___jp_2550_:
{
lean_object* v___x_2555_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_a_2553_);
v___x_2555_ = v___x_2532_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2535_ = v___y_2551_;
v___y_2536_ = v___y_2552_;
v_a_2537_ = v___x_2555_;
goto v___jp_2534_;
}
}
v___jp_2557_:
{
lean_object* v___x_2561_; double v___x_2562_; double v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; 
v___x_2561_ = lean_io_get_num_heartbeats();
v___x_2562_ = lean_float_of_nat(v___y_2559_);
v___x_2563_ = lean_float_of_nat(v___x_2561_);
v___x_2564_ = lean_box_float(v___x_2562_);
v___x_2565_ = lean_box_float(v___x_2563_);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2560_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_unbox(v_a_2530_);
lean_dec(v_a_2530_);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2283_, v___x_2284_, v___x_2285_, v_options_2280_, v___x_2568_, v___y_2558_, v___f_2255_, v___x_2567_, v___y_2258_, v___y_2259_);
v___y_2480_ = v___x_2569_;
goto v___jp_2479_;
}
v___jp_2570_:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2573_);
v___y_2558_ = v___y_2571_;
v___y_2559_ = v___y_2572_;
v_a_2560_ = v___x_2574_;
goto v___jp_2557_;
}
v___jp_2575_:
{
lean_object* v___x_2576_; lean_object* v_a_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2576_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2259_);
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2579_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2280_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_io_mono_nanos_now();
v___x_2581_ = l_IO_lazyPure___redArg(v___f_2254_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
v___x_2583_ = lean_io_prim_handle_put_str(v_cnfHandle_2256_, v_a_2582_);
lean_dec(v_a_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v___x_2583_);
v___x_2584_ = lean_io_prim_handle_flush(v_cnfHandle_2256_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_del_object(v___x_2532_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 1);
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
v___y_2535_ = v___x_2580_;
v___y_2536_ = v_a_2577_;
v_a_2537_ = v___x_2590_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2603_; 
v_a_2593_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2595_ = v___x_2584_;
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2584_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2603_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_io_error_to_string(v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 3);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = l_Lean_MessageData_ofFormat(v___x_2599_);
lean_inc(v_ref_2281_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v_ref_2281_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___y_2551_ = v___x_2580_;
v___y_2552_ = v_a_2577_;
v_a_2553_ = v___x_2601_;
goto v___jp_2550_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2614_; 
v_a_2604_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2606_ = v___x_2583_;
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2583_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2608_ = lean_io_error_to_string(v_a_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 3);
lean_ctor_set(v___x_2606_, 0, v___x_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_Lean_MessageData_ofFormat(v___x_2610_);
lean_inc(v_ref_2281_);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_ref_2281_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___y_2551_ = v___x_2580_;
v___y_2552_ = v_a_2577_;
v_a_2553_ = v___x_2612_;
goto v___jp_2550_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2625_; 
v_a_2615_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2617_ = v___x_2581_;
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2581_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_io_error_to_string(v_a_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set_tag(v___x_2617_, 3);
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = l_Lean_MessageData_ofFormat(v___x_2621_);
lean_inc(v_ref_2281_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_ref_2281_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___y_2551_ = v___x_2580_;
v___y_2552_ = v_a_2577_;
v_a_2553_ = v___x_2623_;
goto v___jp_2550_;
}
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_del_object(v___x_2532_);
v___x_2626_ = lean_io_get_num_heartbeats();
v___x_2627_ = l_IO_lazyPure___redArg(v___f_2254_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = lean_io_prim_handle_put_str(v_cnfHandle_2256_, v_a_2628_);
lean_dec(v_a_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v___x_2629_);
v___x_2630_ = lean_io_prim_handle_flush(v_cnfHandle_2256_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set_tag(v___x_2633_, 1);
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
v___y_2558_ = v_a_2577_;
v___y_2559_ = v___x_2626_;
v_a_2560_ = v___x_2636_;
goto v___jp_2557_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2649_; 
v_a_2639_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2641_ = v___x_2630_;
v_isShared_2642_ = v_isSharedCheck_2649_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2630_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2649_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_io_error_to_string(v_a_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 3);
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = l_Lean_MessageData_ofFormat(v___x_2645_);
lean_inc(v_ref_2281_);
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_ref_2281_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___y_2571_ = v_a_2577_;
v___y_2572_ = v___x_2626_;
v_a_2573_ = v___x_2647_;
goto v___jp_2570_;
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2660_; 
v_a_2650_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2652_ = v___x_2629_;
v_isShared_2653_ = v_isSharedCheck_2660_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2629_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2660_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2654_ = lean_io_error_to_string(v_a_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 3);
lean_ctor_set(v___x_2652_, 0, v___x_2654_);
v___x_2656_ = v___x_2652_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
lean_inc(v_ref_2281_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_ref_2281_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___y_2571_ = v_a_2577_;
v___y_2572_ = v___x_2626_;
v_a_2573_ = v___x_2658_;
goto v___jp_2570_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2671_; 
v_a_2661_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2663_ = v___x_2627_;
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2627_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = lean_io_error_to_string(v_a_2661_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 3);
lean_ctor_set(v___x_2663_, 0, v___x_2665_);
v___x_2667_ = v___x_2663_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = l_Lean_MessageData_ofFormat(v___x_2667_);
lean_inc(v_ref_2281_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_ref_2281_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___y_2571_ = v_a_2577_;
v___y_2572_ = v___x_2626_;
v_a_2573_ = v___x_2669_;
goto v___jp_2570_;
}
}
}
}
}
}
}
v___jp_2261_:
{
if (lean_obj_tag(v___y_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_a_2263_ = lean_ctor_get(v___y_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___y_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v___y_2262_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___y_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2263_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___y_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___y_2262_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___y_2262_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___y_2262_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2292_; double v___x_2293_; double v___x_2294_; double v___x_2295_; double v___x_2296_; double v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2292_ = lean_io_mono_nanos_now();
v___x_2293_ = lean_float_of_nat(v___y_2289_);
v___x_2294_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2295_ = lean_float_div(v___x_2293_, v___x_2294_);
v___x_2296_ = lean_float_of_nat(v___x_2292_);
v___x_2297_ = lean_float_div(v___x_2296_, v___x_2294_);
v___x_2298_ = lean_box_float(v___x_2295_);
v___x_2299_ = lean_box_float(v___x_2297_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2291_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2283_, v___x_2284_, v___x_2285_, v___y_2290_, v___y_2288_, v___y_2287_, v___f_2246_, v___x_2301_, v___y_2258_, v___y_2259_);
v___y_2262_ = v___x_2302_;
goto v___jp_2261_;
}
v___jp_2303_:
{
lean_object* v___x_2309_; double v___x_2310_; double v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2309_ = lean_io_get_num_heartbeats();
v___x_2310_ = lean_float_of_nat(v___y_2306_);
v___x_2311_ = lean_float_of_nat(v___x_2309_);
v___x_2312_ = lean_box_float(v___x_2310_);
v___x_2313_ = lean_box_float(v___x_2311_);
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2308_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2283_, v___x_2284_, v___x_2285_, v___y_2307_, v___y_2305_, v___y_2304_, v___f_2246_, v___x_2315_, v___y_2258_, v___y_2259_);
v___y_2262_ = v___x_2316_;
goto v___jp_2261_;
}
v___jp_2317_:
{
lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2320_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2259_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2323_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_2319_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_io_mono_nanos_now();
v___x_2325_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2247_, v_trimProofs_2248_, v___y_2258_, v___y_2259_);
lean_dec_ref(v_lratPath_2247_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 1);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
v___y_2287_ = v_a_2321_;
v___y_2288_ = v___y_2318_;
v___y_2289_ = v___x_2324_;
v___y_2290_ = v___y_2319_;
v_a_2291_ = v___x_2331_;
goto v___jp_2286_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2325_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2325_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set_tag(v___x_2336_, 0);
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
v___y_2287_ = v_a_2321_;
v___y_2288_ = v___y_2318_;
v___y_2289_ = v___x_2324_;
v___y_2290_ = v___y_2319_;
v_a_2291_ = v___x_2339_;
goto v___jp_2286_;
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_io_get_num_heartbeats();
v___x_2343_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2247_, v_trimProofs_2248_, v___y_2258_, v___y_2259_);
lean_dec_ref(v_lratPath_2247_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
v___y_2304_ = v_a_2321_;
v___y_2305_ = v___y_2318_;
v___y_2306_ = v___x_2342_;
v___y_2307_ = v___y_2319_;
v_a_2308_ = v___x_2349_;
goto v___jp_2303_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2343_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2343_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 0);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
v___y_2304_ = v_a_2321_;
v___y_2305_ = v___y_2318_;
v___y_2306_ = v___x_2342_;
v___y_2307_ = v___y_2319_;
v_a_2308_ = v___x_2357_;
goto v___jp_2303_;
}
}
}
}
}
v___jp_2360_:
{
if (lean_obj_tag(v___y_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2386_; 
v_a_2362_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2364_ = v___y_2361_;
v_isShared_2365_ = v_isSharedCheck_2386_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___y_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2386_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
if (lean_obj_tag(v_a_2362_) == 0)
{
lean_object* v_assignment_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_assignment_2366_ = lean_ctor_get(v_a_2362_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_a_2362_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2368_ = v_a_2362_;
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_assignment_2366_);
lean_dec(v_a_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2376_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_assignment_2366_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2371_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_del_object(v___x_2364_);
lean_dec(v_a_2362_);
if (v_hasTrace_2282_ == 0)
{
lean_object* v___x_2377_; 
lean_dec_ref(v___f_2246_);
v___x_2377_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2247_, v_trimProofs_2248_, v___y_2258_, v___y_2259_);
lean_dec_ref(v_lratPath_2247_);
v___y_2262_ = v___x_2377_;
goto v___jp_2261_;
}
else
{
lean_object* v___x_2378_; lean_object* v_a_2379_; uint8_t v___x_2380_; 
v___x_2378_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2283_, v___y_2258_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_unbox(v_a_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = l_Lean_trace_profiler;
v___x_2382_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2280_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_dec(v_a_2379_);
lean_dec_ref(v___f_2246_);
v___x_2383_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2247_, v_trimProofs_2248_, v___y_2258_, v___y_2259_);
lean_dec_ref(v_lratPath_2247_);
v___y_2262_ = v___x_2383_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_unbox(v_a_2379_);
lean_dec(v_a_2379_);
v___y_2318_ = v___x_2384_;
v___y_2319_ = v_options_2280_;
goto v___jp_2317_;
}
}
else
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_unbox(v_a_2379_);
lean_dec(v_a_2379_);
v___y_2318_ = v___x_2385_;
v___y_2319_ = v_options_2280_;
goto v___jp_2317_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2387_ = lean_ctor_get(v___y_2361_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___y_2361_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___y_2361_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___y_2361_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
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
return v___x_2392_;
}
}
}
}
v___jp_2395_:
{
lean_object* v___x_2401_; double v___x_2402_; double v___x_2403_; double v___x_2404_; double v___x_2405_; double v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2401_ = lean_io_mono_nanos_now();
v___x_2402_ = lean_float_of_nat(v___y_2399_);
v___x_2403_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2404_ = lean_float_div(v___x_2402_, v___x_2403_);
v___x_2405_ = lean_float_of_nat(v___x_2401_);
v___x_2406_ = lean_float_div(v___x_2405_, v___x_2403_);
v___x_2407_ = lean_box_float(v___x_2404_);
v___x_2408_ = lean_box_float(v___x_2406_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_a_2400_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2283_, v___x_2284_, v___x_2285_, v___y_2397_, v___y_2396_, v___y_2398_, v___f_2249_, v___x_2410_, v___y_2258_, v___y_2259_);
v___y_2361_ = v___x_2411_;
goto v___jp_2360_;
}
v___jp_2412_:
{
lean_object* v___x_2418_; double v___x_2419_; double v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2418_ = lean_io_get_num_heartbeats();
v___x_2419_ = lean_float_of_nat(v___y_2414_);
v___x_2420_ = lean_float_of_nat(v___x_2418_);
v___x_2421_ = lean_box_float(v___x_2419_);
v___x_2422_ = lean_box_float(v___x_2420_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2417_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2283_, v___x_2284_, v___x_2285_, v___y_2415_, v___y_2413_, v___y_2416_, v___f_2249_, v___x_2424_, v___y_2258_, v___y_2259_);
v___y_2361_ = v___x_2425_;
goto v___jp_2360_;
}
v___jp_2426_:
{
lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2429_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2259_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2432_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_2428_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_io_mono_nanos_now();
lean_inc_ref(v_lratPath_2247_);
v___x_2434_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2250_, v_cnfPath_2257_, v_lratPath_2247_, v_timeout_2251_, v_binaryProofs_2252_, v_solverMode_2253_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 1);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
v___y_2396_ = v___y_2427_;
v___y_2397_ = v___y_2428_;
v___y_2398_ = v_a_2430_;
v___y_2399_ = v___x_2433_;
v_a_2400_ = v___x_2440_;
goto v___jp_2395_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2434_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2434_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
v___y_2396_ = v___y_2427_;
v___y_2397_ = v___y_2428_;
v___y_2398_ = v_a_2430_;
v___y_2399_ = v___x_2433_;
v_a_2400_ = v___x_2448_;
goto v___jp_2395_;
}
}
}
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_lratPath_2247_);
v___x_2452_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2250_, v_cnfPath_2257_, v_lratPath_2247_, v_timeout_2251_, v_binaryProofs_2252_, v_solverMode_2253_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
v___y_2413_ = v___y_2427_;
v___y_2414_ = v___x_2451_;
v___y_2415_ = v___y_2428_;
v___y_2416_ = v_a_2430_;
v_a_2417_ = v___x_2458_;
goto v___jp_2412_;
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_a_2461_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2452_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2452_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 0);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
v___y_2413_ = v___y_2427_;
v___y_2414_ = v___x_2451_;
v___y_2415_ = v___y_2428_;
v___y_2416_ = v_a_2430_;
v_a_2417_ = v___x_2466_;
goto v___jp_2412_;
}
}
}
}
}
v___jp_2469_:
{
if (v_hasTrace_2282_ == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v___f_2249_);
lean_inc_ref(v_lratPath_2247_);
v___x_2470_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2250_, v_cnfPath_2257_, v_lratPath_2247_, v_timeout_2251_, v_binaryProofs_2252_, v_solverMode_2253_, v___y_2258_, v___y_2259_);
v___y_2361_ = v___x_2470_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2471_; lean_object* v_a_2472_; uint8_t v___x_2473_; 
v___x_2471_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2283_, v___y_2258_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = lean_unbox(v_a_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = l_Lean_trace_profiler;
v___x_2475_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2280_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
lean_dec(v_a_2472_);
lean_dec_ref(v___f_2249_);
lean_inc_ref(v_lratPath_2247_);
v___x_2476_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2250_, v_cnfPath_2257_, v_lratPath_2247_, v_timeout_2251_, v_binaryProofs_2252_, v_solverMode_2253_, v___y_2258_, v___y_2259_);
v___y_2361_ = v___x_2476_;
goto v___jp_2360_;
}
else
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
v___y_2427_ = v___x_2477_;
v___y_2428_ = v_options_2280_;
goto v___jp_2426_;
}
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
v___y_2427_ = v___x_2478_;
v___y_2428_ = v_options_2280_;
goto v___jp_2426_;
}
}
}
v___jp_2479_:
{
if (lean_obj_tag(v___y_2480_) == 0)
{
lean_dec_ref(v___y_2480_);
goto v___jp_2469_;
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_cnfPath_2257_);
lean_dec_ref(v_solver_2250_);
lean_dec_ref(v___f_2249_);
lean_dec_ref(v_lratPath_2247_);
lean_dec_ref(v___f_2246_);
v_a_2481_ = lean_ctor_get(v___y_2480_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___y_2480_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___y_2480_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___y_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object* v___f_2716_, lean_object* v_lratPath_2717_, lean_object* v_trimProofs_2718_, lean_object* v___f_2719_, lean_object* v_solver_2720_, lean_object* v_timeout_2721_, lean_object* v_binaryProofs_2722_, lean_object* v_solverMode_2723_, lean_object* v___f_2724_, lean_object* v___f_2725_, lean_object* v_cnfHandle_2726_, lean_object* v_cnfPath_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v_trimProofs_boxed_2731_; uint8_t v_binaryProofs_boxed_2732_; uint8_t v_solverMode_boxed_2733_; lean_object* v_res_2734_; 
v_trimProofs_boxed_2731_ = lean_unbox(v_trimProofs_2718_);
v_binaryProofs_boxed_2732_ = lean_unbox(v_binaryProofs_2722_);
v_solverMode_boxed_2733_ = lean_unbox(v_solverMode_2723_);
v_res_2734_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(v___f_2716_, v_lratPath_2717_, v_trimProofs_boxed_2731_, v___f_2719_, v_solver_2720_, v_timeout_2721_, v_binaryProofs_boxed_2732_, v_solverMode_boxed_2733_, v___f_2724_, v___f_2725_, v_cnfHandle_2726_, v_cnfPath_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v_cnfHandle_2726_);
lean_dec(v_timeout_2721_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object* v_cnf_2738_, lean_object* v_solver_2739_, lean_object* v_lratPath_2740_, uint8_t v_trimProofs_2741_, lean_object* v_timeout_2742_, uint8_t v_binaryProofs_2743_, uint8_t v_solverMode_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___f_2748_; lean_object* v___f_2749_; lean_object* v___f_2750_; lean_object* v___f_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; 
v___f_2748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2748_, 0, v_cnf_2738_);
v___f_2749_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0));
v___f_2750_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1));
v___f_2751_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2));
v___x_2752_ = lean_box(v_trimProofs_2741_);
v___x_2753_ = lean_box(v_binaryProofs_2743_);
v___x_2754_ = lean_box(v_solverMode_2744_);
v___f_2755_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2755_, 0, v___f_2750_);
lean_closure_set(v___f_2755_, 1, v_lratPath_2740_);
lean_closure_set(v___f_2755_, 2, v___x_2752_);
lean_closure_set(v___f_2755_, 3, v___f_2749_);
lean_closure_set(v___f_2755_, 4, v_solver_2739_);
lean_closure_set(v___f_2755_, 5, v_timeout_2742_);
lean_closure_set(v___f_2755_, 6, v___x_2753_);
lean_closure_set(v___f_2755_, 7, v___x_2754_);
lean_closure_set(v___f_2755_, 8, v___f_2748_);
lean_closure_set(v___f_2755_, 9, v___f_2751_);
v___x_2756_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v___f_2755_, v_a_2745_, v_a_2746_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object* v_cnf_2757_, lean_object* v_solver_2758_, lean_object* v_lratPath_2759_, lean_object* v_trimProofs_2760_, lean_object* v_timeout_2761_, lean_object* v_binaryProofs_2762_, lean_object* v_solverMode_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_trimProofs_boxed_2767_; uint8_t v_binaryProofs_boxed_2768_; uint8_t v_solverMode_boxed_2769_; lean_object* v_res_2770_; 
v_trimProofs_boxed_2767_ = lean_unbox(v_trimProofs_2760_);
v_binaryProofs_boxed_2768_ = lean_unbox(v_binaryProofs_2762_);
v_solverMode_boxed_2769_ = lean_unbox(v_solverMode_2763_);
v_res_2770_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(v_cnf_2757_, v_solver_2758_, v_lratPath_2759_, v_trimProofs_boxed_2767_, v_timeout_2761_, v_binaryProofs_boxed_2768_, v_solverMode_boxed_2769_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
return v_res_2770_;
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
