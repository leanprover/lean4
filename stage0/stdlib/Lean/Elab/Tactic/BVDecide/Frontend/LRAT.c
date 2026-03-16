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
lean_object* v_fileName_883_; lean_object* v_fileMap_884_; lean_object* v_options_885_; lean_object* v_currRecDepth_886_; lean_object* v_maxRecDepth_887_; lean_object* v_ref_888_; lean_object* v_currNamespace_889_; lean_object* v_openDecls_890_; lean_object* v_initHeartbeats_891_; lean_object* v_maxHeartbeats_892_; lean_object* v_quotContext_893_; lean_object* v_currMacroScope_894_; uint8_t v_diag_895_; lean_object* v_cancelTk_x3f_896_; uint8_t v_suppressElabErrors_897_; lean_object* v_inheritedTraceOptions_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_953_; 
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
v_isSharedCheck_953_ = !lean_is_exclusive(v___y_880_);
if (v_isSharedCheck_953_ == 0)
{
v___x_900_ = v___y_880_;
v_isShared_901_ = v_isSharedCheck_953_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_inheritedTraceOptions_898_);
lean_inc(v_cancelTk_x3f_896_);
lean_inc(v_currMacroScope_894_);
lean_inc(v_quotContext_893_);
lean_inc(v_maxHeartbeats_892_);
lean_inc(v_initHeartbeats_891_);
lean_inc(v_openDecls_890_);
lean_inc(v_currNamespace_889_);
lean_inc(v_ref_888_);
lean_inc(v_maxRecDepth_887_);
lean_inc(v_currRecDepth_886_);
lean_inc(v_options_885_);
lean_inc(v_fileMap_884_);
lean_inc(v_fileName_883_);
lean_dec(v___y_880_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_953_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v_traceState_903_; lean_object* v_traces_904_; lean_object* v_ref_905_; lean_object* v___x_907_; 
v___x_902_ = lean_st_ref_get(v___y_881_);
v_traceState_903_ = lean_ctor_get(v___x_902_, 4);
lean_inc_ref(v_traceState_903_);
lean_dec(v___x_902_);
v_traces_904_ = lean_ctor_get(v_traceState_903_, 0);
lean_inc_ref(v_traces_904_);
lean_dec_ref(v_traceState_903_);
v_ref_905_ = l_Lean_replaceRef(v_ref_878_, v_ref_888_);
lean_dec(v_ref_888_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 5, v_ref_905_);
v___x_907_ = v___x_900_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fileName_883_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_fileMap_884_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_options_885_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_currRecDepth_886_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_maxRecDepth_887_);
lean_ctor_set(v_reuseFailAlloc_952_, 5, v_ref_905_);
lean_ctor_set(v_reuseFailAlloc_952_, 6, v_currNamespace_889_);
lean_ctor_set(v_reuseFailAlloc_952_, 7, v_openDecls_890_);
lean_ctor_set(v_reuseFailAlloc_952_, 8, v_initHeartbeats_891_);
lean_ctor_set(v_reuseFailAlloc_952_, 9, v_maxHeartbeats_892_);
lean_ctor_set(v_reuseFailAlloc_952_, 10, v_quotContext_893_);
lean_ctor_set(v_reuseFailAlloc_952_, 11, v_currMacroScope_894_);
lean_ctor_set(v_reuseFailAlloc_952_, 12, v_cancelTk_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_952_, 13, v_inheritedTraceOptions_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_952_, sizeof(void*)*14, v_diag_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_952_, sizeof(void*)*14 + 1, v_suppressElabErrors_897_);
v___x_907_ = v_reuseFailAlloc_952_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; size_t v_sz_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v_msg_912_; lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_951_; 
v___x_908_ = l_Lean_PersistentArray_toArray___redArg(v_traces_904_);
lean_dec_ref(v_traces_904_);
v_sz_909_ = lean_array_size(v___x_908_);
v___x_910_ = ((size_t)0ULL);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7_spec__8(v_sz_909_, v___x_910_, v___x_908_);
v_msg_912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_912_, 0, v_data_877_);
lean_ctor_set(v_msg_912_, 1, v_msg_879_);
lean_ctor_set(v_msg_912_, 2, v___x_911_);
v___x_913_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msg_912_, v___x_907_, v___y_881_);
lean_dec_ref(v___x_907_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_951_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_951_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_951_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_traceState_919_; lean_object* v_env_920_; lean_object* v_nextMacroScope_921_; lean_object* v_ngen_922_; lean_object* v_auxDeclNGen_923_; lean_object* v_cache_924_; lean_object* v_messages_925_; lean_object* v_infoState_926_; lean_object* v_snapshotTasks_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_950_; 
v___x_918_ = lean_st_ref_take(v___y_881_);
v_traceState_919_ = lean_ctor_get(v___x_918_, 4);
v_env_920_ = lean_ctor_get(v___x_918_, 0);
v_nextMacroScope_921_ = lean_ctor_get(v___x_918_, 1);
v_ngen_922_ = lean_ctor_get(v___x_918_, 2);
v_auxDeclNGen_923_ = lean_ctor_get(v___x_918_, 3);
v_cache_924_ = lean_ctor_get(v___x_918_, 5);
v_messages_925_ = lean_ctor_get(v___x_918_, 6);
v_infoState_926_ = lean_ctor_get(v___x_918_, 7);
v_snapshotTasks_927_ = lean_ctor_get(v___x_918_, 8);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_950_ == 0)
{
v___x_929_ = v___x_918_;
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snapshotTasks_927_);
lean_inc(v_infoState_926_);
lean_inc(v_messages_925_);
lean_inc(v_cache_924_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_923_);
lean_inc(v_ngen_922_);
lean_inc(v_nextMacroScope_921_);
lean_inc(v_env_920_);
lean_dec(v___x_918_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint64_t v_tid_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_948_; 
v_tid_931_ = lean_ctor_get_uint64(v_traceState_919_, sizeof(void*)*1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_traceState_919_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_traceState_919_, 0);
lean_dec(v_unused_949_);
v___x_933_ = v_traceState_919_;
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
else
{
lean_dec(v_traceState_919_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_ref_878_);
lean_ctor_set(v___x_935_, 1, v_a_914_);
v___x_936_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_876_, v___x_935_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_936_);
lean_ctor_set_uint64(v_reuseFailAlloc_947_, sizeof(void*)*1, v_tid_931_);
v___x_938_ = v_reuseFailAlloc_947_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 4, v___x_938_);
v___x_940_ = v___x_929_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_env_920_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_nextMacroScope_921_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_ngen_922_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_auxDeclNGen_923_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_messages_925_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_infoState_926_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v_snapshotTasks_927_);
v___x_940_ = v_reuseFailAlloc_946_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_st_ref_set(v___y_881_, v___x_940_);
v___x_942_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_942_);
v___x_944_ = v___x_916_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7___boxed(lean_object* v_oldTraces_954_, lean_object* v_data_955_, lean_object* v_ref_956_, lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_954_, v_data_955_, v_ref_956_, v_msg_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(lean_object* v_opts_962_, lean_object* v_opt_963_){
_start:
{
lean_object* v_name_964_; lean_object* v_defValue_965_; lean_object* v_map_966_; lean_object* v___x_967_; 
v_name_964_ = lean_ctor_get(v_opt_963_, 0);
v_defValue_965_ = lean_ctor_get(v_opt_963_, 1);
v_map_966_ = lean_ctor_get(v_opts_962_, 0);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_966_, v_name_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_inc(v_defValue_965_);
return v_defValue_965_;
}
else
{
lean_object* v_val_968_; 
v_val_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_968_);
lean_dec_ref(v___x_967_);
if (lean_obj_tag(v_val_968_) == 3)
{
lean_object* v_v_969_; 
v_v_969_ = lean_ctor_get(v_val_968_, 0);
lean_inc(v_v_969_);
lean_dec_ref(v_val_968_);
return v_v_969_;
}
else
{
lean_dec(v_val_968_);
lean_inc(v_defValue_965_);
return v_defValue_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9___boxed(lean_object* v_opts_970_, lean_object* v_opt_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_970_, v_opt_971_);
lean_dec_ref(v_opt_971_);
lean_dec_ref(v_opts_970_);
return v_res_972_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__2));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4(void){
_start:
{
lean_object* v___x_979_; double v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(1000u);
v___x_980_ = lean_float_of_nat(v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(lean_object* v_cls_981_, uint8_t v_collapsed_982_, lean_object* v_tag_983_, lean_object* v_opts_984_, uint8_t v_clsEnabled_985_, lean_object* v_oldTraces_986_, lean_object* v_msg_987_, lean_object* v_resStartStop_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1091_; 
v_fst_992_ = lean_ctor_get(v_resStartStop_988_, 0);
v_snd_993_ = lean_ctor_get(v_resStartStop_988_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_resStartStop_988_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_995_ = v_resStartStop_988_;
v_isShared_996_ = v_isSharedCheck_1091_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_resStartStop_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1091_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v_data_1000_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1090_; 
v_fst_1011_ = lean_ctor_get(v_snd_993_, 0);
v_snd_1012_ = lean_ctor_get(v_snd_993_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_snd_993_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1014_ = v_snd_993_;
v_isShared_1015_ = v_isSharedCheck_1090_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_inc(v_fst_1011_);
lean_dec(v_snd_993_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1090_;
goto v_resetjp_1013_;
}
v___jp_997_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_986_, v_data_1000_, v___y_998_, v___y_999_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1002_; 
lean_dec_ref(v___x_1001_);
v___x_1002_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_992_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_fst_992_);
v_a_1003_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1001_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___y_1019_; lean_object* v_a_1020_; uint8_t v___y_1044_; double v___y_1075_; 
v___x_1016_ = l_Lean_trace_profiler;
v___x_1017_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_984_, v___x_1016_);
if (v___x_1017_ == 0)
{
v___y_1044_ = v___x_1017_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1081_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_984_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; double v___x_1084_; double v___x_1085_; double v___x_1086_; 
v___x_1082_ = l_Lean_trace_profiler_threshold;
v___x_1083_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_984_, v___x_1082_);
v___x_1084_ = lean_float_of_nat(v___x_1083_);
v___x_1085_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_1086_ = lean_float_div(v___x_1084_, v___x_1085_);
v___y_1075_ = v___x_1086_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; double v___x_1089_; 
v___x_1087_ = l_Lean_trace_profiler_threshold;
v___x_1088_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_984_, v___x_1087_);
v___x_1089_ = lean_float_of_nat(v___x_1088_);
v___y_1075_ = v___x_1089_;
goto v___jp_1074_;
}
}
v___jp_1018_:
{
uint8_t v_result_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_result_1021_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__6(v_fst_992_);
v___x_1022_ = l_Lean_TraceResult_toEmoji(v_result_1021_);
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
v___x_1024_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 7);
lean_ctor_set(v___x_1014_, 1, v___x_1024_);
lean_ctor_set(v___x_1014_, 0, v___x_1023_);
v___x_1026_ = v___x_1014_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v_m_1028_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 7);
lean_ctor_set(v___x_995_, 1, v_a_1020_);
lean_ctor_set(v___x_995_, 0, v___x_1026_);
v_m_1028_ = v___x_995_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_a_1020_);
v_m_1028_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; double v___x_1031_; lean_object* v_data_1032_; 
v___x_1029_ = lean_box(v_result_1021_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
v___x_1031_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_983_);
lean_inc_ref(v___x_1030_);
lean_inc(v_cls_981_);
v_data_1032_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1032_, 0, v_cls_981_);
lean_ctor_set(v_data_1032_, 1, v___x_1030_);
lean_ctor_set(v_data_1032_, 2, v_tag_983_);
lean_ctor_set_float(v_data_1032_, sizeof(void*)*3, v___x_1031_);
lean_ctor_set_float(v_data_1032_, sizeof(void*)*3 + 8, v___x_1031_);
lean_ctor_set_uint8(v_data_1032_, sizeof(void*)*3 + 16, v_collapsed_982_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v___x_1030_);
lean_dec(v_snd_1012_);
lean_dec(v_fst_1011_);
lean_dec_ref(v_tag_983_);
lean_dec(v_cls_981_);
v___y_998_ = v___y_1019_;
v___y_999_ = v_m_1028_;
v_data_1000_ = v_data_1032_;
goto v___jp_997_;
}
else
{
lean_object* v_data_1033_; double v___x_1034_; double v___x_1035_; 
lean_dec_ref(v_data_1032_);
v_data_1033_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1033_, 0, v_cls_981_);
lean_ctor_set(v_data_1033_, 1, v___x_1030_);
lean_ctor_set(v_data_1033_, 2, v_tag_983_);
v___x_1034_ = lean_unbox_float(v_fst_1011_);
lean_dec(v_fst_1011_);
lean_ctor_set_float(v_data_1033_, sizeof(void*)*3, v___x_1034_);
v___x_1035_ = lean_unbox_float(v_snd_1012_);
lean_dec(v_snd_1012_);
lean_ctor_set_float(v_data_1033_, sizeof(void*)*3 + 8, v___x_1035_);
lean_ctor_set_uint8(v_data_1033_, sizeof(void*)*3 + 16, v_collapsed_982_);
v___y_998_ = v___y_1019_;
v___y_999_ = v_m_1028_;
v_data_1000_ = v_data_1033_;
goto v___jp_997_;
}
}
}
}
v___jp_1038_:
{
lean_object* v_ref_1039_; lean_object* v___x_1040_; 
v_ref_1039_ = lean_ctor_get(v___y_989_, 5);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v_fst_992_);
v___x_1040_ = lean_apply_4(v_msg_987_, v_fst_992_, v___y_989_, v___y_990_, lean_box(0));
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
lean_inc(v_ref_1039_);
v___y_1019_ = v_ref_1039_;
v_a_1020_ = v_a_1041_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
lean_inc(v_ref_1039_);
v___y_1019_ = v_ref_1039_;
v_a_1020_ = v___x_1042_;
goto v___jp_1018_;
}
}
v___jp_1043_:
{
if (v_clsEnabled_985_ == 0)
{
if (v___y_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v_traceState_1046_; lean_object* v_env_1047_; lean_object* v_nextMacroScope_1048_; lean_object* v_ngen_1049_; lean_object* v_auxDeclNGen_1050_; lean_object* v_cache_1051_; lean_object* v_messages_1052_; lean_object* v_infoState_1053_; lean_object* v_snapshotTasks_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1073_; 
lean_del_object(v___x_1014_);
lean_dec(v_snd_1012_);
lean_dec(v_fst_1011_);
lean_del_object(v___x_995_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_msg_987_);
lean_dec_ref(v_tag_983_);
lean_dec(v_cls_981_);
v___x_1045_ = lean_st_ref_take(v___y_990_);
v_traceState_1046_ = lean_ctor_get(v___x_1045_, 4);
v_env_1047_ = lean_ctor_get(v___x_1045_, 0);
v_nextMacroScope_1048_ = lean_ctor_get(v___x_1045_, 1);
v_ngen_1049_ = lean_ctor_get(v___x_1045_, 2);
v_auxDeclNGen_1050_ = lean_ctor_get(v___x_1045_, 3);
v_cache_1051_ = lean_ctor_get(v___x_1045_, 5);
v_messages_1052_ = lean_ctor_get(v___x_1045_, 6);
v_infoState_1053_ = lean_ctor_get(v___x_1045_, 7);
v_snapshotTasks_1054_ = lean_ctor_get(v___x_1045_, 8);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1056_ = v___x_1045_;
v_isShared_1057_ = v_isSharedCheck_1073_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snapshotTasks_1054_);
lean_inc(v_infoState_1053_);
lean_inc(v_messages_1052_);
lean_inc(v_cache_1051_);
lean_inc(v_traceState_1046_);
lean_inc(v_auxDeclNGen_1050_);
lean_inc(v_ngen_1049_);
lean_inc(v_nextMacroScope_1048_);
lean_inc(v_env_1047_);
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1073_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
uint64_t v_tid_1058_; lean_object* v_traces_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1072_; 
v_tid_1058_ = lean_ctor_get_uint64(v_traceState_1046_, sizeof(void*)*1);
v_traces_1059_ = lean_ctor_get(v_traceState_1046_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_traceState_1046_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1061_ = v_traceState_1046_;
v_isShared_1062_ = v_isSharedCheck_1072_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_traces_1059_);
lean_dec(v_traceState_1046_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1072_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_986_, v_traces_1059_);
lean_dec_ref(v_traces_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1063_);
lean_ctor_set_uint64(v_reuseFailAlloc_1071_, sizeof(void*)*1, v_tid_1058_);
v___x_1065_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1065_);
v___x_1067_ = v___x_1056_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_env_1047_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_nextMacroScope_1048_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_ngen_1049_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_auxDeclNGen_1050_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v_cache_1051_);
lean_ctor_set(v_reuseFailAlloc_1070_, 6, v_messages_1052_);
lean_ctor_set(v_reuseFailAlloc_1070_, 7, v_infoState_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 8, v_snapshotTasks_1054_);
v___x_1067_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_st_ref_set(v___y_990_, v___x_1067_);
lean_dec(v___y_990_);
v___x_1069_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_992_);
return v___x_1069_;
}
}
}
}
}
else
{
goto v___jp_1038_;
}
}
else
{
goto v___jp_1038_;
}
}
v___jp_1074_:
{
double v___x_1076_; double v___x_1077_; double v___x_1078_; uint8_t v___x_1079_; 
v___x_1076_ = lean_unbox_float(v_snd_1012_);
v___x_1077_ = lean_unbox_float(v_fst_1011_);
v___x_1078_ = lean_float_sub(v___x_1076_, v___x_1077_);
v___x_1079_ = lean_float_decLt(v___y_1075_, v___x_1078_);
v___y_1044_ = v___x_1079_;
goto v___jp_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___boxed(lean_object* v_cls_1092_, lean_object* v_collapsed_1093_, lean_object* v_tag_1094_, lean_object* v_opts_1095_, lean_object* v_clsEnabled_1096_, lean_object* v_oldTraces_1097_, lean_object* v_msg_1098_, lean_object* v_resStartStop_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v_collapsed_boxed_1103_; uint8_t v_clsEnabled_boxed_1104_; lean_object* v_res_1105_; 
v_collapsed_boxed_1103_ = lean_unbox(v_collapsed_1093_);
v_clsEnabled_boxed_1104_ = lean_unbox(v_clsEnabled_1096_);
v_res_1105_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v_cls_1092_, v_collapsed_boxed_1103_, v_tag_1094_, v_opts_1095_, v_clsEnabled_boxed_1104_, v_oldTraces_1097_, v_msg_1098_, v_resStartStop_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v_opts_1095_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(lean_object* v_cls_1106_, lean_object* v_msg_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1157_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 5);
v___x_1112_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1_spec__1(v_msg_1107_, v___y_1108_, v___y_1109_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_traceState_1118_; lean_object* v_env_1119_; lean_object* v_nextMacroScope_1120_; lean_object* v_ngen_1121_; lean_object* v_auxDeclNGen_1122_; lean_object* v_cache_1123_; lean_object* v_messages_1124_; lean_object* v_infoState_1125_; lean_object* v_snapshotTasks_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1156_; 
v___x_1117_ = lean_st_ref_take(v___y_1109_);
v_traceState_1118_ = lean_ctor_get(v___x_1117_, 4);
v_env_1119_ = lean_ctor_get(v___x_1117_, 0);
v_nextMacroScope_1120_ = lean_ctor_get(v___x_1117_, 1);
v_ngen_1121_ = lean_ctor_get(v___x_1117_, 2);
v_auxDeclNGen_1122_ = lean_ctor_get(v___x_1117_, 3);
v_cache_1123_ = lean_ctor_get(v___x_1117_, 5);
v_messages_1124_ = lean_ctor_get(v___x_1117_, 6);
v_infoState_1125_ = lean_ctor_get(v___x_1117_, 7);
v_snapshotTasks_1126_ = lean_ctor_get(v___x_1117_, 8);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snapshotTasks_1126_);
lean_inc(v_infoState_1125_);
lean_inc(v_messages_1124_);
lean_inc(v_cache_1123_);
lean_inc(v_traceState_1118_);
lean_inc(v_auxDeclNGen_1122_);
lean_inc(v_ngen_1121_);
lean_inc(v_nextMacroScope_1120_);
lean_inc(v_env_1119_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint64_t v_tid_1130_; lean_object* v_traces_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_tid_1130_ = lean_ctor_get_uint64(v_traceState_1118_, sizeof(void*)*1);
v_traces_1131_ = lean_ctor_get(v_traceState_1118_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_traceState_1118_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_traceState_1118_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_traces_1131_);
lean_dec(v_traceState_1118_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; double v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
v___x_1139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1139_, 0, v_cls_1106_);
lean_ctor_set(v___x_1139_, 1, v___x_1135_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3, v___x_1136_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3 + 8, v___x_1136_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3 + 16, v___x_1137_);
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__1));
v___x_1141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v_a_1113_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
lean_inc(v_ref_1111_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_ref_1111_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_PersistentArray_push___redArg(v_traces_1131_, v___x_1142_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1143_);
v___x_1145_ = v___x_1133_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1143_);
lean_ctor_set_uint64(v_reuseFailAlloc_1154_, sizeof(void*)*1, v_tid_1130_);
v___x_1145_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1145_);
v___x_1147_ = v___x_1128_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_env_1119_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_nextMacroScope_1120_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_ngen_1121_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_auxDeclNGen_1122_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 5, v_cache_1123_);
lean_ctor_set(v_reuseFailAlloc_1153_, 6, v_messages_1124_);
lean_ctor_set(v_reuseFailAlloc_1153_, 7, v_infoState_1125_);
lean_ctor_set(v_reuseFailAlloc_1153_, 8, v_snapshotTasks_1126_);
v___x_1147_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_st_ref_set(v___y_1109_, v___x_1147_);
v___x_1149_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1149_);
v___x_1151_ = v___x_1115_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1___boxed(lean_object* v_cls_1158_, lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v_cls_1158_, v_msg_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1163_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3(void){
_start:
{
lean_object* v___x_1167_; double v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1000000000u);
v___x_1168_ = lean_float_of_nat(v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__5));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(lean_object* v_lratPath_1174_, uint8_t v_trimProofs_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_IO_FS_readBinFile(v_lratPath_1174_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_options_1180_; lean_object* v_a_1181_; lean_object* v_ref_1182_; uint8_t v_hasTrace_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v_proof_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v_a_1240_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v_a_1256_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v_a_1265_; lean_object* v___y_1278_; lean_object* v___y_1279_; uint8_t v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v_a_1284_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v_a_1446_; lean_object* v___y_1475_; 
v_options_1180_ = lean_ctor_get(v_a_1176_, 2);
v_a_1181_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1179_);
v_ref_1182_ = lean_ctor_get(v_a_1176_, 5);
v_hasTrace_1183_ = lean_ctor_get_uint8(v_options_1180_, sizeof(void*)*1);
v___f_1184_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__0));
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__1), 2, 1);
lean_closure_set(v___f_1185_, 0, v_a_1181_);
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_1231_ = 1;
v___x_1232_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_1183_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = l_IO_lazyPure___redArg(v___f_1185_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
if (lean_obj_tag(v_a_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1479_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v_a_1478_);
v___x_1480_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1481_ = l_Lean_stringToMessageData(v_a_1479_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1482_, v_a_1176_, v_a_1177_);
v___y_1475_ = v___x_1483_;
goto v___jp_1474_;
}
else
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v_a_1478_);
v_a_1446_ = v_a_1484_;
goto v___jp_1445_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1496_; 
lean_inc(v_ref_1182_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
v_a_1485_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1487_ = v___x_1477_;
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1477_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1489_ = lean_io_error_to_string(v_a_1485_);
v___x_1490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
v___x_1491_ = l_Lean_MessageData_ofFormat(v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_ref_1182_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1492_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1624_; 
v___x_1497_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1186_, v_a_1176_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1624_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1624_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___f_1502_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v_a_1506_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v_a_1522_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v_a_1529_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_a_1534_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_a_1547_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_a_1552_; uint8_t v___x_1601_; 
v___f_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__7));
v___x_1601_ = lean_unbox(v_a_1498_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = l_Lean_trace_profiler;
v___x_1603_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1180_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_del_object(v___x_1500_);
lean_dec(v_a_1498_);
v___x_1604_ = l_IO_lazyPure___redArg(v___f_1185_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
if (lean_obj_tag(v_a_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1606_ = lean_ctor_get(v_a_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v_a_1605_);
v___x_1607_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1608_ = l_Lean_stringToMessageData(v_a_1606_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1609_, v_a_1176_, v_a_1177_);
v___y_1475_ = v___x_1610_;
goto v___jp_1474_;
}
else
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v_a_1605_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v_a_1605_);
v_a_1446_ = v_a_1611_;
goto v___jp_1445_;
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1623_; 
lean_inc(v_ref_1182_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
v_a_1612_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1614_ = v___x_1604_;
v_isShared_1615_ = v_isSharedCheck_1623_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1623_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1616_ = lean_io_error_to_string(v_a_1612_);
v___x_1617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = l_Lean_MessageData_ofFormat(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_ref_1182_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1619_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
goto v___jp_1554_;
}
}
else
{
goto v___jp_1554_;
}
v___jp_1503_:
{
lean_object* v___x_1507_; double v___x_1508_; double v___x_1509_; double v___x_1510_; double v___x_1511_; double v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1507_ = lean_io_mono_nanos_now();
v___x_1508_ = lean_float_of_nat(v___y_1504_);
v___x_1509_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1510_ = lean_float_div(v___x_1508_, v___x_1509_);
v___x_1511_ = lean_float_of_nat(v___x_1507_);
v___x_1512_ = lean_float_div(v___x_1511_, v___x_1509_);
v___x_1513_ = lean_box_float(v___x_1510_);
v___x_1514_ = lean_box_float(v___x_1512_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_a_1506_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
lean_inc(v_a_1177_);
lean_inc_ref(v_a_1176_);
v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1186_, v___x_1231_, v___x_1232_, v_options_1180_, v___x_1517_, v___y_1505_, v___f_1502_, v___x_1516_, v_a_1176_, v_a_1177_);
v___y_1475_ = v___x_1518_;
goto v___jp_1474_;
}
v___jp_1519_:
{
lean_object* v___x_1524_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_a_1522_);
v___x_1524_ = v___x_1500_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v___y_1504_ = v___y_1520_;
v___y_1505_ = v___y_1521_;
v_a_1506_ = v___x_1524_;
goto v___jp_1503_;
}
}
v___jp_1526_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1529_);
v___y_1504_ = v___y_1527_;
v___y_1505_ = v___y_1528_;
v_a_1506_ = v___x_1530_;
goto v___jp_1503_;
}
v___jp_1531_:
{
lean_object* v___x_1535_; double v___x_1536_; double v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1535_ = lean_io_get_num_heartbeats();
v___x_1536_ = lean_float_of_nat(v___y_1532_);
v___x_1537_ = lean_float_of_nat(v___x_1535_);
v___x_1538_ = lean_box_float(v___x_1536_);
v___x_1539_ = lean_box_float(v___x_1537_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1534_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
lean_inc(v_a_1177_);
lean_inc_ref(v_a_1176_);
v___x_1543_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1186_, v___x_1231_, v___x_1232_, v_options_1180_, v___x_1542_, v___y_1533_, v___f_1502_, v___x_1541_, v_a_1176_, v_a_1177_);
v___y_1475_ = v___x_1543_;
goto v___jp_1474_;
}
v___jp_1544_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1547_);
v___y_1532_ = v___y_1545_;
v___y_1533_ = v___y_1546_;
v_a_1534_ = v___x_1548_;
goto v___jp_1531_;
}
v___jp_1549_:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1552_);
v___y_1532_ = v___y_1550_;
v___y_1533_ = v___y_1551_;
v_a_1534_ = v___x_1553_;
goto v___jp_1531_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v_a_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1555_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v_a_1177_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1558_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1180_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_io_mono_nanos_now();
v___x_1560_ = l_IO_lazyPure___redArg(v___f_1185_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v_a_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_a_1567_; 
v_a_1562_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v_a_1561_);
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1564_ = l_Lean_stringToMessageData(v_a_1562_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1565_, v_a_1176_, v_a_1177_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___y_1520_ = v___x_1559_;
v___y_1521_ = v_a_1556_;
v_a_1522_ = v_a_1567_;
goto v___jp_1519_;
}
else
{
lean_object* v_a_1568_; 
lean_del_object(v___x_1500_);
v_a_1568_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v_a_1561_);
v___y_1527_ = v___x_1559_;
v___y_1528_ = v_a_1556_;
v_a_1529_ = v_a_1568_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_a_1569_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v___x_1560_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1560_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_io_error_to_string(v_a_1569_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 3);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = l_Lean_MessageData_ofFormat(v___x_1575_);
lean_inc(v_ref_1182_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_ref_1182_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___y_1520_ = v___x_1559_;
v___y_1521_ = v_a_1556_;
v_a_1522_ = v___x_1577_;
goto v___jp_1519_;
}
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_del_object(v___x_1500_);
v___x_1580_ = lean_io_get_num_heartbeats();
v___x_1581_ = l_IO_lazyPure___redArg(v___f_1185_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1581_);
if (lean_obj_tag(v_a_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_a_1588_; 
v_a_1583_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v_a_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__6);
v___x_1585_ = l_Lean_stringToMessageData(v_a_1583_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v___x_1586_, v_a_1176_, v_a_1177_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v___y_1545_ = v___x_1580_;
v___y_1546_ = v_a_1556_;
v_a_1547_ = v_a_1588_;
goto v___jp_1544_;
}
else
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v_a_1582_);
v___y_1550_ = v___x_1580_;
v___y_1551_ = v_a_1556_;
v_a_1552_ = v_a_1589_;
goto v___jp_1549_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_a_1590_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v___x_1581_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1581_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_io_error_to_string(v_a_1590_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 3);
lean_ctor_set(v___x_1592_, 0, v___x_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = l_Lean_MessageData_ofFormat(v___x_1596_);
lean_inc(v_ref_1182_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_ref_1182_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___y_1545_ = v___x_1580_;
v___y_1546_ = v_a_1556_;
v_a_1547_ = v___x_1598_;
goto v___jp_1544_;
}
}
}
}
}
}
}
v___jp_1187_:
{
lean_object* v___x_1191_; lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1225_; 
v___x_1191_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1186_, v___y_1189_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1225_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1225_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_unbox(v_a_1192_);
lean_dec(v_a_1192_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_proof_1188_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_proof_1188_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_del_object(v___x_1194_);
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1201_ = lean_array_get_size(v_proof_1188_);
v___x_1202_ = l_Nat_reprFast(v___x_1201_);
v___x_1203_ = lean_string_append(v___x_1200_, v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__2));
v___x_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___x_1207_ = l_Lean_MessageData_ofFormat(v___x_1206_);
v___x_1208_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___x_1186_, v___x_1207_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1208_, 0);
lean_dec(v_unused_1216_);
v___x_1210_ = v___x_1208_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1208_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_proof_1188_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_proof_1188_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_proof_1188_);
v_a_1217_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1208_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1208_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
v___jp_1226_:
{
if (lean_obj_tag(v___y_1229_) == 0)
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___y_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___y_1229_);
v_proof_1188_ = v_a_1230_;
v___y_1189_ = v___y_1228_;
v___y_1190_ = v___y_1227_;
goto v___jp_1187_;
}
else
{
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
return v___y_1229_;
}
}
v___jp_1233_:
{
lean_object* v___x_1241_; double v___x_1242_; double v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1241_ = lean_io_get_num_heartbeats();
v___x_1242_ = lean_float_of_nat(v___y_1236_);
v___x_1243_ = lean_float_of_nat(v___x_1241_);
v___x_1244_ = lean_box_float(v___x_1242_);
v___x_1245_ = lean_box_float(v___x_1243_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1240_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1238_);
v___x_1248_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1186_, v___x_1231_, v___x_1232_, v___y_1237_, v___y_1235_, v___y_1239_, v___f_1184_, v___x_1247_, v___y_1238_, v___y_1234_);
lean_dec_ref(v___y_1237_);
v___y_1227_ = v___y_1234_;
v___y_1228_ = v___y_1238_;
v___y_1229_ = v___x_1248_;
goto v___jp_1226_;
}
v___jp_1249_:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1256_);
v___y_1234_ = v___y_1250_;
v___y_1235_ = v___y_1251_;
v___y_1236_ = v___y_1252_;
v___y_1237_ = v___y_1253_;
v___y_1238_ = v___y_1254_;
v___y_1239_ = v___y_1255_;
v_a_1240_ = v___x_1257_;
goto v___jp_1233_;
}
v___jp_1258_:
{
lean_object* v___x_1266_; double v___x_1267_; double v___x_1268_; double v___x_1269_; double v___x_1270_; double v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1266_ = lean_io_mono_nanos_now();
v___x_1267_ = lean_float_of_nat(v___y_1259_);
v___x_1268_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_1269_ = lean_float_div(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_float_of_nat(v___x_1266_);
v___x_1271_ = lean_float_div(v___x_1270_, v___x_1268_);
v___x_1272_ = lean_box_float(v___x_1269_);
v___x_1273_ = lean_box_float(v___x_1271_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1265_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1263_);
v___x_1276_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5(v___x_1186_, v___x_1231_, v___x_1232_, v___y_1262_, v___y_1261_, v___y_1264_, v___f_1184_, v___x_1275_, v___y_1263_, v___y_1260_);
lean_dec_ref(v___y_1262_);
v___y_1227_ = v___y_1260_;
v___y_1228_ = v___y_1263_;
v___y_1229_ = v___x_1276_;
goto v___jp_1226_;
}
v___jp_1277_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1284_);
v___y_1259_ = v___y_1278_;
v___y_1260_ = v___y_1279_;
v___y_1261_ = v___y_1280_;
v___y_1262_ = v___y_1281_;
v___y_1263_ = v___y_1282_;
v___y_1264_ = v___y_1283_;
v_a_1265_ = v___x_1285_;
goto v___jp_1258_;
}
v___jp_1286_:
{
lean_object* v___x_1293_; lean_object* v_a_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1293_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_1288_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1296_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_1290_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_io_mono_nanos_now();
v___x_1298_ = l_IO_lazyPure___redArg(v___y_1287_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v___y_1292_);
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 1);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
v___y_1259_ = v___x_1297_;
v___y_1260_ = v___y_1288_;
v___y_1261_ = v___y_1289_;
v___y_1262_ = v___y_1290_;
v___y_1263_ = v___y_1291_;
v___y_1264_ = v_a_1294_;
v_a_1265_ = v___x_1306_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1311_ = v___x_1300_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_io_error_to_string(v_a_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 3);
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_Lean_MessageData_ofFormat(v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1292_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___y_1278_ = v___x_1297_;
v___y_1279_ = v___y_1288_;
v___y_1280_ = v___y_1289_;
v___y_1281_ = v___y_1290_;
v___y_1282_ = v___y_1291_;
v___y_1283_ = v_a_1294_;
v_a_1284_ = v___x_1317_;
goto v___jp_1277_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1330_; 
v_a_1320_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1322_ = v___x_1298_;
v_isShared_1323_ = v_isSharedCheck_1330_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1298_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1330_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_io_error_to_string(v_a_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 3);
lean_ctor_set(v___x_1322_, 0, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = l_Lean_MessageData_ofFormat(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___y_1292_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___y_1278_ = v___x_1297_;
v___y_1279_ = v___y_1288_;
v___y_1280_ = v___y_1289_;
v___y_1281_ = v___y_1290_;
v___y_1282_ = v___y_1291_;
v___y_1283_ = v_a_1294_;
v_a_1284_ = v___x_1328_;
goto v___jp_1277_;
}
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_io_get_num_heartbeats();
v___x_1332_ = l_IO_lazyPure___redArg(v___y_1287_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v___y_1292_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v___y_1234_ = v___y_1288_;
v___y_1235_ = v___y_1289_;
v___y_1236_ = v___x_1331_;
v___y_1237_ = v___y_1290_;
v___y_1238_ = v___y_1291_;
v___y_1239_ = v_a_1294_;
v_a_1240_ = v___x_1340_;
goto v___jp_1233_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1353_; 
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1345_ = v___x_1334_;
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_io_error_to_string(v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 3);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = l_Lean_MessageData_ofFormat(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___y_1292_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___y_1250_ = v___y_1288_;
v___y_1251_ = v___y_1289_;
v___y_1252_ = v___x_1331_;
v___y_1253_ = v___y_1290_;
v___y_1254_ = v___y_1291_;
v___y_1255_ = v_a_1294_;
v_a_1256_ = v___x_1351_;
goto v___jp_1249_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1364_; 
v_a_1354_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1356_ = v___x_1332_;
v_isShared_1357_ = v_isSharedCheck_1364_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1332_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1364_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_io_error_to_string(v_a_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 3);
lean_ctor_set(v___x_1356_, 0, v___x_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = l_Lean_MessageData_ofFormat(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1292_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___y_1250_ = v___y_1288_;
v___y_1251_ = v___y_1289_;
v___y_1252_ = v___x_1331_;
v___y_1253_ = v___y_1290_;
v___y_1254_ = v___y_1291_;
v___y_1255_ = v_a_1294_;
v_a_1256_ = v___x_1362_;
goto v___jp_1249_;
}
}
}
}
}
v___jp_1365_:
{
if (v_trimProofs_1175_ == 0)
{
lean_dec_ref(v___y_1366_);
v_proof_1188_ = v___y_1367_;
v___y_1189_ = v___y_1368_;
v___y_1190_ = v___y_1369_;
goto v___jp_1187_;
}
else
{
lean_object* v_options_1370_; uint8_t v_hasTrace_1371_; 
lean_dec_ref(v___y_1367_);
v_options_1370_ = lean_ctor_get(v___y_1368_, 2);
v_hasTrace_1371_ = lean_ctor_get_uint8(v_options_1370_, sizeof(void*)*1);
if (v_hasTrace_1371_ == 0)
{
lean_object* v_ref_1372_; lean_object* v___x_1373_; 
v_ref_1372_ = lean_ctor_get(v___y_1368_, 5);
v___x_1373_ = l_IO_lazyPure___redArg(v___y_1366_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v_proof_1188_ = v_a_1376_;
v___y_1189_ = v___y_1368_;
v___y_1190_ = v___y_1369_;
goto v___jp_1187_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1388_; 
lean_inc(v_ref_1372_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
v_a_1377_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1381_ = lean_io_error_to_string(v_a_1377_);
v___x_1382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = l_Lean_MessageData_ofFormat(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_ref_1372_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1384_);
v___x_1386_ = v___x_1379_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1400_; 
lean_inc(v_ref_1372_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
v_a_1389_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1391_ = v___x_1373_;
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1373_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1393_ = lean_io_error_to_string(v_a_1389_);
v___x_1394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = l_Lean_MessageData_ofFormat(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_ref_1372_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1396_);
v___x_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_ref_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1444_; 
v_ref_1401_ = lean_ctor_get(v___y_1368_, 5);
v___x_1402_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1186_, v___y_1368_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1444_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1444_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_unbox(v_a_1403_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = l_Lean_trace_profiler;
v___x_1409_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_1370_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_a_1403_);
v___x_1410_ = l_IO_lazyPure___redArg(v___y_1366_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__2___redArg(v_a_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; 
lean_del_object(v___x_1405_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v_proof_1188_ = v_a_1413_;
v___y_1189_ = v___y_1368_;
v___y_1190_ = v___y_1369_;
goto v___jp_1187_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1427_; 
lean_inc(v_ref_1401_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
v_a_1414_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1427_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1427_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_io_error_to_string(v_a_1414_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 3);
lean_ctor_set(v___x_1405_, 0, v___x_1418_);
v___x_1420_ = v___x_1405_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = l_Lean_MessageData_ofFormat(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_ref_1401_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1422_);
v___x_1424_ = v___x_1416_;
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
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1441_; 
lean_inc(v_ref_1401_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
v_a_1428_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1430_ = v___x_1410_;
v_isShared_1431_ = v_isSharedCheck_1441_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1410_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1441_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_io_error_to_string(v_a_1428_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 3);
lean_ctor_set(v___x_1405_, 0, v___x_1432_);
v___x_1434_ = v___x_1405_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1435_ = l_Lean_MessageData_ofFormat(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_ref_1401_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1436_);
v___x_1438_ = v___x_1430_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
uint8_t v___x_1442_; 
lean_inc(v_ref_1401_);
lean_inc_ref(v_options_1370_);
lean_del_object(v___x_1405_);
v___x_1442_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
v___y_1287_ = v___y_1366_;
v___y_1288_ = v___y_1369_;
v___y_1289_ = v___x_1442_;
v___y_1290_ = v_options_1370_;
v___y_1291_ = v___y_1368_;
v___y_1292_ = v_ref_1401_;
goto v___jp_1286_;
}
}
else
{
uint8_t v___x_1443_; 
lean_inc(v_ref_1401_);
lean_inc_ref(v_options_1370_);
lean_del_object(v___x_1405_);
v___x_1443_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
v___y_1287_ = v___y_1366_;
v___y_1288_ = v___y_1369_;
v___y_1289_ = v___x_1443_;
v___y_1290_ = v_options_1370_;
v___y_1291_ = v___y_1368_;
v___y_1292_ = v_ref_1401_;
goto v___jp_1286_;
}
}
}
}
}
v___jp_1445_:
{
lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1473_; 
v___x_1447_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_1186_, v_a_1176_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1473_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1473_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___f_1452_; uint8_t v___x_1453_; 
lean_inc_ref(v_a_1446_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1452_, 0, v_a_1446_);
v___x_1453_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1453_ == 0)
{
lean_del_object(v___x_1450_);
v___y_1366_ = v___f_1452_;
v___y_1367_ = v_a_1446_;
v___y_1368_ = v_a_1176_;
v___y_1369_ = v_a_1177_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1454_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__1));
v___x_1455_ = lean_array_get_size(v_a_1446_);
v___x_1456_ = l_Nat_reprFast(v___x_1455_);
v___x_1457_ = lean_string_append(v___x_1454_, v___x_1456_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__4));
v___x_1459_ = lean_string_append(v___x_1457_, v___x_1458_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 3);
lean_ctor_set(v___x_1450_, 0, v___x_1459_);
v___x_1461_ = v___x_1450_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l_Lean_MessageData_ofFormat(v___x_1461_);
v___x_1463_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__1(v___x_1186_, v___x_1462_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref(v___x_1463_);
v___y_1366_ = v___f_1452_;
v___y_1367_ = v_a_1446_;
v___y_1368_ = v_a_1176_;
v___y_1369_ = v_a_1177_;
goto v___jp_1365_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v___f_1452_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
}
v___jp_1474_:
{
if (lean_obj_tag(v___y_1475_) == 0)
{
lean_object* v_a_1476_; 
v_a_1476_ = lean_ctor_get(v___y_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___y_1475_);
v_a_1446_ = v_a_1476_;
goto v___jp_1445_;
}
else
{
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v___y_1475_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1177_);
v_a_1625_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1627_ = v___x_1179_;
v_isShared_1628_ = v_isSharedCheck_1637_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1179_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1637_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_ref_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v_ref_1629_ = lean_ctor_get(v_a_1176_, 5);
lean_inc(v_ref_1629_);
lean_dec_ref(v_a_1176_);
v___x_1630_ = lean_io_error_to_string(v_a_1625_);
v___x_1631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
v___x_1632_ = l_Lean_MessageData_ofFormat(v___x_1631_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_ref_1629_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1633_);
v___x_1635_ = v___x_1627_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___boxed(lean_object* v_lratPath_1638_, lean_object* v_trimProofs_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
uint8_t v_trimProofs_boxed_1643_; lean_object* v_res_1644_; 
v_trimProofs_boxed_1643_ = lean_unbox(v_trimProofs_1639_);
v_res_1644_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1638_, v_trimProofs_boxed_1643_, v_a_1640_, v_a_1641_);
lean_dec_ref(v_lratPath_1638_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8(lean_object* v_00_u03b1_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_x_1646_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8(v_00_u03b1_1651_, v_x_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6(lean_object* v_00_u03b1_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___redArg(v_msg_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__6(v_00_u03b1_1663_, v_msg_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object* v_lratPath_1669_, uint8_t v_trimProofs_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load(v_lratPath_1669_, v_trimProofs_1670_, v_a_1671_, v_a_1672_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_1675_);
lean_dec(v_a_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_a_1684_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1674_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1674_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___boxed(lean_object* v_lratPath_1692_, lean_object* v_trimProofs_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
uint8_t v_trimProofs_boxed_1697_; lean_object* v_res_1698_; 
v_trimProofs_boxed_1697_ = lean_unbox(v_trimProofs_1693_);
v_res_1698_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_1692_, v_trimProofs_boxed_1697_, v_a_1694_, v_a_1695_);
lean_dec_ref(v_lratPath_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(lean_object* v_snd_1699_, lean_object* v___y_1700_, lean_object* v_a_x3f_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_io_remove_file(v_snd_1699_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1724_; 
v_a_1712_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1714_ = v___x_1703_;
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1703_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1724_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_ref_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v_ref_1716_ = lean_ctor_get(v___y_1700_, 5);
v___x_1717_ = lean_io_error_to_string(v_a_1712_);
v___x_1718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
v___x_1719_ = l_Lean_MessageData_ofFormat(v___x_1718_);
lean_inc(v_ref_1716_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_ref_1716_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1720_);
v___x_1722_ = v___x_1714_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0___boxed(lean_object* v_snd_1725_, lean_object* v___y_1726_, lean_object* v_a_x3f_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1725_, v___y_1726_, v_a_x3f_1727_);
lean_dec(v_a_x3f_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v_snd_1725_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(lean_object* v_f_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v_fst_1736_; lean_object* v_snd_1737_; lean_object* v_r_1738_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v_fst_1736_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_fst_1736_);
v_snd_1737_ = lean_ctor_get(v_a_1735_, 1);
lean_inc(v_snd_1737_);
lean_dec(v_a_1735_);
lean_inc_ref(v___y_1731_);
lean_inc(v_snd_1737_);
v_r_1738_ = lean_apply_5(v_f_1730_, v_fst_1736_, v_snd_1737_, v___y_1731_, v___y_1732_, lean_box(0));
if (lean_obj_tag(v_r_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1763_; 
v_a_1739_ = lean_ctor_get(v_r_1738_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_r_1738_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1741_ = v_r_1738_;
v_isShared_1742_ = v_isSharedCheck_1763_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v_r_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1763_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
lean_inc(v_a_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1737_, v___y_1731_, v___x_1744_);
lean_dec_ref(v___x_1744_);
lean_dec_ref(v___y_1731_);
lean_dec(v_snd_1737_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1745_, 0);
lean_dec(v_unused_1753_);
v___x_1747_ = v___x_1745_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_dec(v___x_1745_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v_a_1739_);
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1739_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1739_);
v_a_1754_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1745_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1745_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1764_ = lean_ctor_get(v_r_1738_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v_r_1738_);
v___x_1765_ = lean_box(0);
v___x_1766_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___lam__0(v_snd_1737_, v___y_1731_, v___x_1765_);
lean_dec_ref(v___y_1731_);
lean_dec(v_snd_1737_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1774_);
v___x_1768_ = v___x_1766_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___x_1766_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 1);
lean_ctor_set(v___x_1768_, 0, v_a_1764_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1764_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_a_1764_);
v_a_1775_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1766_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1766_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v___y_1732_);
lean_dec_ref(v_f_1730_);
v_a_1783_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1785_ = v___x_1734_;
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1734_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_ref_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v_ref_1787_ = lean_ctor_get(v___y_1731_, 5);
lean_inc(v_ref_1787_);
lean_dec_ref(v___y_1731_);
v___x_1788_ = lean_io_error_to_string(v_a_1783_);
v___x_1789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___x_1790_ = l_Lean_MessageData_ofFormat(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_ref_1787_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1791_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg___boxed(lean_object* v_f_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1796_, v___y_1797_, v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(lean_object* v_00_u03b1_1801_, lean_object* v_f_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v_f_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_f_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3(v_00_u03b1_1807_, v_f_1808_, v___y_1809_, v___y_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(lean_object* v_cnf_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_Sat_CNF_dimacs(v_cnf_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed(lean_object* v_cnf_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0(v_cnf_1816_, v_x_1817_);
lean_dec_ref(v_cnf_1816_);
return v_res_1818_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__1));
v___x_1823_ = l_Lean_MessageData_ofFormat(v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___closed__2);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1___boxed(lean_object* v_x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__1(v_x_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v_x_1830_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__1));
v___x_1839_ = l_Lean_MessageData_ofFormat(v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___closed__2);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2___boxed(lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__2(v_x_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v_x_1846_);
return v_res_1850_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__1));
v___x_1855_ = l_Lean_MessageData_ofFormat(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___closed__2);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3___boxed(lean_object* v_x_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__3(v_x_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v_x_1862_);
return v_res_1866_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(lean_object* v_e_1867_){
_start:
{
if (lean_obj_tag(v_e_1867_) == 0)
{
uint8_t v___x_1868_; 
v___x_1868_ = 2;
return v___x_1868_;
}
else
{
uint8_t v___x_1869_; 
v___x_1869_ = 0;
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0___boxed(lean_object* v_e_1870_){
_start:
{
uint8_t v_res_1871_; lean_object* v_r_1872_; 
v_res_1871_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_e_1870_);
lean_dec_ref(v_e_1870_);
v_r_1872_ = lean_box(v_res_1871_);
return v_r_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(lean_object* v_cls_1873_, uint8_t v_collapsed_1874_, lean_object* v_tag_1875_, lean_object* v_opts_1876_, uint8_t v_clsEnabled_1877_, lean_object* v_oldTraces_1878_, lean_object* v_msg_1879_, lean_object* v_resStartStop_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1983_; 
v_fst_1884_ = lean_ctor_get(v_resStartStop_1880_, 0);
v_snd_1885_ = lean_ctor_get(v_resStartStop_1880_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_resStartStop_1880_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1887_ = v_resStartStop_1880_;
v_isShared_1888_ = v_isSharedCheck_1983_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_snd_1885_);
lean_inc(v_fst_1884_);
lean_dec(v_resStartStop_1880_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1983_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v_data_1892_; lean_object* v_fst_1903_; lean_object* v_snd_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1982_; 
v_fst_1903_ = lean_ctor_get(v_snd_1885_, 0);
v_snd_1904_ = lean_ctor_get(v_snd_1885_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_snd_1885_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1906_ = v_snd_1885_;
v_isShared_1907_ = v_isSharedCheck_1982_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_snd_1904_);
lean_inc(v_fst_1903_);
lean_dec(v_snd_1885_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1982_;
goto v_resetjp_1905_;
}
v___jp_1889_:
{
lean_object* v___x_1893_; 
v___x_1893_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_1878_, v_data_1892_, v___y_1890_, v___y_1891_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref(v___x_1893_);
v___x_1894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_1884_);
return v___x_1894_;
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_fst_1884_);
v_a_1895_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1893_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___y_1911_; lean_object* v_a_1912_; uint8_t v___y_1936_; double v___y_1967_; 
v___x_1908_ = l_Lean_trace_profiler;
v___x_1909_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_1876_, v___x_1908_);
if (v___x_1909_ == 0)
{
v___y_1936_ = v___x_1909_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1973_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_1876_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; double v___x_1976_; double v___x_1977_; double v___x_1978_; 
v___x_1974_ = l_Lean_trace_profiler_threshold;
v___x_1975_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_1876_, v___x_1974_);
v___x_1976_ = lean_float_of_nat(v___x_1975_);
v___x_1977_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_1978_ = lean_float_div(v___x_1976_, v___x_1977_);
v___y_1967_ = v___x_1978_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; double v___x_1981_; 
v___x_1979_ = l_Lean_trace_profiler_threshold;
v___x_1980_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_1876_, v___x_1979_);
v___x_1981_ = lean_float_of_nat(v___x_1980_);
v___y_1967_ = v___x_1981_;
goto v___jp_1966_;
}
}
v___jp_1910_:
{
uint8_t v_result_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v_result_1913_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0_spec__0(v_fst_1884_);
v___x_1914_ = l_Lean_TraceResult_toEmoji(v_result_1913_);
v___x_1915_ = l_Lean_stringToMessageData(v___x_1914_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 7);
lean_ctor_set(v___x_1906_, 1, v___x_1916_);
lean_ctor_set(v___x_1906_, 0, v___x_1915_);
v___x_1918_ = v___x_1906_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v_m_1920_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 7);
lean_ctor_set(v___x_1887_, 1, v_a_1912_);
lean_ctor_set(v___x_1887_, 0, v___x_1918_);
v_m_1920_ = v___x_1887_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_a_1912_);
v_m_1920_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; double v___x_1923_; lean_object* v_data_1924_; 
v___x_1921_ = lean_box(v_result_1913_);
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
v___x_1923_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_1875_);
lean_inc_ref(v___x_1922_);
lean_inc(v_cls_1873_);
v_data_1924_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1924_, 0, v_cls_1873_);
lean_ctor_set(v_data_1924_, 1, v___x_1922_);
lean_ctor_set(v_data_1924_, 2, v_tag_1875_);
lean_ctor_set_float(v_data_1924_, sizeof(void*)*3, v___x_1923_);
lean_ctor_set_float(v_data_1924_, sizeof(void*)*3 + 8, v___x_1923_);
lean_ctor_set_uint8(v_data_1924_, sizeof(void*)*3 + 16, v_collapsed_1874_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v___x_1922_);
lean_dec(v_snd_1904_);
lean_dec(v_fst_1903_);
lean_dec_ref(v_tag_1875_);
lean_dec(v_cls_1873_);
v___y_1890_ = v___y_1911_;
v___y_1891_ = v_m_1920_;
v_data_1892_ = v_data_1924_;
goto v___jp_1889_;
}
else
{
lean_object* v_data_1925_; double v___x_1926_; double v___x_1927_; 
lean_dec_ref(v_data_1924_);
v_data_1925_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1925_, 0, v_cls_1873_);
lean_ctor_set(v_data_1925_, 1, v___x_1922_);
lean_ctor_set(v_data_1925_, 2, v_tag_1875_);
v___x_1926_ = lean_unbox_float(v_fst_1903_);
lean_dec(v_fst_1903_);
lean_ctor_set_float(v_data_1925_, sizeof(void*)*3, v___x_1926_);
v___x_1927_ = lean_unbox_float(v_snd_1904_);
lean_dec(v_snd_1904_);
lean_ctor_set_float(v_data_1925_, sizeof(void*)*3 + 8, v___x_1927_);
lean_ctor_set_uint8(v_data_1925_, sizeof(void*)*3 + 16, v_collapsed_1874_);
v___y_1890_ = v___y_1911_;
v___y_1891_ = v_m_1920_;
v_data_1892_ = v_data_1925_;
goto v___jp_1889_;
}
}
}
}
v___jp_1930_:
{
lean_object* v_ref_1931_; lean_object* v___x_1932_; 
v_ref_1931_ = lean_ctor_get(v___y_1881_, 5);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v_fst_1884_);
v___x_1932_ = lean_apply_4(v_msg_1879_, v_fst_1884_, v___y_1881_, v___y_1882_, lean_box(0));
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
lean_inc(v_ref_1931_);
v___y_1911_ = v_ref_1931_;
v_a_1912_ = v_a_1933_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1934_; 
lean_dec_ref(v___x_1932_);
v___x_1934_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
lean_inc(v_ref_1931_);
v___y_1911_ = v_ref_1931_;
v_a_1912_ = v___x_1934_;
goto v___jp_1910_;
}
}
v___jp_1935_:
{
if (v_clsEnabled_1877_ == 0)
{
if (v___y_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v_traceState_1938_; lean_object* v_env_1939_; lean_object* v_nextMacroScope_1940_; lean_object* v_ngen_1941_; lean_object* v_auxDeclNGen_1942_; lean_object* v_cache_1943_; lean_object* v_messages_1944_; lean_object* v_infoState_1945_; lean_object* v_snapshotTasks_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1965_; 
lean_del_object(v___x_1906_);
lean_dec(v_snd_1904_);
lean_dec(v_fst_1903_);
lean_del_object(v___x_1887_);
lean_dec_ref(v___y_1881_);
lean_dec_ref(v_msg_1879_);
lean_dec_ref(v_tag_1875_);
lean_dec(v_cls_1873_);
v___x_1937_ = lean_st_ref_take(v___y_1882_);
v_traceState_1938_ = lean_ctor_get(v___x_1937_, 4);
v_env_1939_ = lean_ctor_get(v___x_1937_, 0);
v_nextMacroScope_1940_ = lean_ctor_get(v___x_1937_, 1);
v_ngen_1941_ = lean_ctor_get(v___x_1937_, 2);
v_auxDeclNGen_1942_ = lean_ctor_get(v___x_1937_, 3);
v_cache_1943_ = lean_ctor_get(v___x_1937_, 5);
v_messages_1944_ = lean_ctor_get(v___x_1937_, 6);
v_infoState_1945_ = lean_ctor_get(v___x_1937_, 7);
v_snapshotTasks_1946_ = lean_ctor_get(v___x_1937_, 8);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1948_ = v___x_1937_;
v_isShared_1949_ = v_isSharedCheck_1965_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snapshotTasks_1946_);
lean_inc(v_infoState_1945_);
lean_inc(v_messages_1944_);
lean_inc(v_cache_1943_);
lean_inc(v_traceState_1938_);
lean_inc(v_auxDeclNGen_1942_);
lean_inc(v_ngen_1941_);
lean_inc(v_nextMacroScope_1940_);
lean_inc(v_env_1939_);
lean_dec(v___x_1937_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1965_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
uint64_t v_tid_1950_; lean_object* v_traces_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1964_; 
v_tid_1950_ = lean_ctor_get_uint64(v_traceState_1938_, sizeof(void*)*1);
v_traces_1951_ = lean_ctor_get(v_traceState_1938_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_traceState_1938_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1953_ = v_traceState_1938_;
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_traces_1951_);
lean_dec(v_traceState_1938_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1964_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1878_, v_traces_1951_);
lean_dec_ref(v_traces_1951_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1955_);
lean_ctor_set_uint64(v_reuseFailAlloc_1963_, sizeof(void*)*1, v_tid_1950_);
v___x_1957_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 4, v___x_1957_);
v___x_1959_ = v___x_1948_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_env_1939_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_nextMacroScope_1940_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_ngen_1941_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_auxDeclNGen_1942_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1962_, 5, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1962_, 6, v_messages_1944_);
lean_ctor_set(v_reuseFailAlloc_1962_, 7, v_infoState_1945_);
lean_ctor_set(v_reuseFailAlloc_1962_, 8, v_snapshotTasks_1946_);
v___x_1959_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_st_ref_set(v___y_1882_, v___x_1959_);
lean_dec(v___y_1882_);
v___x_1961_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_1884_);
return v___x_1961_;
}
}
}
}
}
else
{
goto v___jp_1930_;
}
}
else
{
goto v___jp_1930_;
}
}
v___jp_1966_:
{
double v___x_1968_; double v___x_1969_; double v___x_1970_; uint8_t v___x_1971_; 
v___x_1968_ = lean_unbox_float(v_snd_1904_);
v___x_1969_ = lean_unbox_float(v_fst_1903_);
v___x_1970_ = lean_float_sub(v___x_1968_, v___x_1969_);
v___x_1971_ = lean_float_decLt(v___y_1967_, v___x_1970_);
v___y_1936_ = v___x_1971_;
goto v___jp_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0___boxed(lean_object* v_cls_1984_, lean_object* v_collapsed_1985_, lean_object* v_tag_1986_, lean_object* v_opts_1987_, lean_object* v_clsEnabled_1988_, lean_object* v_oldTraces_1989_, lean_object* v_msg_1990_, lean_object* v_resStartStop_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
uint8_t v_collapsed_boxed_1995_; uint8_t v_clsEnabled_boxed_1996_; lean_object* v_res_1997_; 
v_collapsed_boxed_1995_ = lean_unbox(v_collapsed_1985_);
v_clsEnabled_boxed_1996_ = lean_unbox(v_clsEnabled_1988_);
v_res_1997_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v_cls_1984_, v_collapsed_boxed_1995_, v_tag_1986_, v_opts_1987_, v_clsEnabled_boxed_1996_, v_oldTraces_1989_, v_msg_1990_, v_resStartStop_1991_, v___y_1992_, v___y_1993_);
lean_dec_ref(v_opts_1987_);
return v_res_1997_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(lean_object* v_e_1998_){
_start:
{
if (lean_obj_tag(v_e_1998_) == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = 2;
return v___x_1999_;
}
else
{
uint8_t v___x_2000_; 
v___x_2000_ = 0;
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2___boxed(lean_object* v_e_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_e_2001_);
lean_dec_ref(v_e_2001_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(lean_object* v_cls_2004_, uint8_t v_collapsed_2005_, lean_object* v_tag_2006_, lean_object* v_opts_2007_, uint8_t v_clsEnabled_2008_, lean_object* v_oldTraces_2009_, lean_object* v_msg_2010_, lean_object* v_resStartStop_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2114_; 
v_fst_2015_ = lean_ctor_get(v_resStartStop_2011_, 0);
v_snd_2016_ = lean_ctor_get(v_resStartStop_2011_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_resStartStop_2011_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2018_ = v_resStartStop_2011_;
v_isShared_2019_ = v_isSharedCheck_2114_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v_resStartStop_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2114_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v_data_2023_; lean_object* v_fst_2034_; lean_object* v_snd_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2113_; 
v_fst_2034_ = lean_ctor_get(v_snd_2016_, 0);
v_snd_2035_ = lean_ctor_get(v_snd_2016_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_snd_2016_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2037_ = v_snd_2016_;
v_isShared_2038_ = v_isSharedCheck_2113_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_snd_2035_);
lean_inc(v_fst_2034_);
lean_dec(v_snd_2016_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2113_;
goto v_resetjp_2036_;
}
v___jp_2020_:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_2009_, v_data_2023_, v___y_2022_, v___y_2021_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2025_; 
lean_dec_ref(v___x_2024_);
v___x_2025_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2015_);
return v___x_2025_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_fst_2015_);
v_a_2026_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2024_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___y_2042_; lean_object* v_a_2043_; uint8_t v___y_2067_; double v___y_2098_; 
v___x_2039_ = l_Lean_trace_profiler;
v___x_2040_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2007_, v___x_2039_);
if (v___x_2040_ == 0)
{
v___y_2067_ = v___x_2040_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2104_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2007_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; double v___x_2107_; double v___x_2108_; double v___x_2109_; 
v___x_2105_ = l_Lean_trace_profiler_threshold;
v___x_2106_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2007_, v___x_2105_);
v___x_2107_ = lean_float_of_nat(v___x_2106_);
v___x_2108_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_2109_ = lean_float_div(v___x_2107_, v___x_2108_);
v___y_2098_ = v___x_2109_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; double v___x_2112_; 
v___x_2110_ = l_Lean_trace_profiler_threshold;
v___x_2111_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2007_, v___x_2110_);
v___x_2112_ = lean_float_of_nat(v___x_2111_);
v___y_2098_ = v___x_2112_;
goto v___jp_2097_;
}
}
v___jp_2041_:
{
uint8_t v_result_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v_result_2044_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1_spec__2(v_fst_2015_);
v___x_2045_ = l_Lean_TraceResult_toEmoji(v_result_2044_);
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
v___x_2047_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 7);
lean_ctor_set(v___x_2037_, 1, v___x_2047_);
lean_ctor_set(v___x_2037_, 0, v___x_2046_);
v___x_2049_ = v___x_2037_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v_m_2051_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 7);
lean_ctor_set(v___x_2018_, 1, v_a_2043_);
lean_ctor_set(v___x_2018_, 0, v___x_2049_);
v_m_2051_ = v___x_2018_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2043_);
v_m_2051_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; double v___x_2054_; lean_object* v_data_2055_; 
v___x_2052_ = lean_box(v_result_2044_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2006_);
lean_inc_ref(v___x_2053_);
lean_inc(v_cls_2004_);
v_data_2055_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2055_, 0, v_cls_2004_);
lean_ctor_set(v_data_2055_, 1, v___x_2053_);
lean_ctor_set(v_data_2055_, 2, v_tag_2006_);
lean_ctor_set_float(v_data_2055_, sizeof(void*)*3, v___x_2054_);
lean_ctor_set_float(v_data_2055_, sizeof(void*)*3 + 8, v___x_2054_);
lean_ctor_set_uint8(v_data_2055_, sizeof(void*)*3 + 16, v_collapsed_2005_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v___x_2053_);
lean_dec(v_snd_2035_);
lean_dec(v_fst_2034_);
lean_dec_ref(v_tag_2006_);
lean_dec(v_cls_2004_);
v___y_2021_ = v_m_2051_;
v___y_2022_ = v___y_2042_;
v_data_2023_ = v_data_2055_;
goto v___jp_2020_;
}
else
{
lean_object* v_data_2056_; double v___x_2057_; double v___x_2058_; 
lean_dec_ref(v_data_2055_);
v_data_2056_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2056_, 0, v_cls_2004_);
lean_ctor_set(v_data_2056_, 1, v___x_2053_);
lean_ctor_set(v_data_2056_, 2, v_tag_2006_);
v___x_2057_ = lean_unbox_float(v_fst_2034_);
lean_dec(v_fst_2034_);
lean_ctor_set_float(v_data_2056_, sizeof(void*)*3, v___x_2057_);
v___x_2058_ = lean_unbox_float(v_snd_2035_);
lean_dec(v_snd_2035_);
lean_ctor_set_float(v_data_2056_, sizeof(void*)*3 + 8, v___x_2058_);
lean_ctor_set_uint8(v_data_2056_, sizeof(void*)*3 + 16, v_collapsed_2005_);
v___y_2021_ = v_m_2051_;
v___y_2022_ = v___y_2042_;
v_data_2023_ = v_data_2056_;
goto v___jp_2020_;
}
}
}
}
v___jp_2061_:
{
lean_object* v_ref_2062_; lean_object* v___x_2063_; 
v_ref_2062_ = lean_ctor_get(v___y_2012_, 5);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v_fst_2015_);
v___x_2063_ = lean_apply_4(v_msg_2010_, v_fst_2015_, v___y_2012_, v___y_2013_, lean_box(0));
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
lean_inc(v_ref_2062_);
v___y_2042_ = v_ref_2062_;
v_a_2043_ = v_a_2064_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
lean_inc(v_ref_2062_);
v___y_2042_ = v_ref_2062_;
v_a_2043_ = v___x_2065_;
goto v___jp_2041_;
}
}
v___jp_2066_:
{
if (v_clsEnabled_2008_ == 0)
{
if (v___y_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v_traceState_2069_; lean_object* v_env_2070_; lean_object* v_nextMacroScope_2071_; lean_object* v_ngen_2072_; lean_object* v_auxDeclNGen_2073_; lean_object* v_cache_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2096_; 
lean_del_object(v___x_2037_);
lean_dec(v_snd_2035_);
lean_dec(v_fst_2034_);
lean_del_object(v___x_2018_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v_msg_2010_);
lean_dec_ref(v_tag_2006_);
lean_dec(v_cls_2004_);
v___x_2068_ = lean_st_ref_take(v___y_2013_);
v_traceState_2069_ = lean_ctor_get(v___x_2068_, 4);
v_env_2070_ = lean_ctor_get(v___x_2068_, 0);
v_nextMacroScope_2071_ = lean_ctor_get(v___x_2068_, 1);
v_ngen_2072_ = lean_ctor_get(v___x_2068_, 2);
v_auxDeclNGen_2073_ = lean_ctor_get(v___x_2068_, 3);
v_cache_2074_ = lean_ctor_get(v___x_2068_, 5);
v_messages_2075_ = lean_ctor_get(v___x_2068_, 6);
v_infoState_2076_ = lean_ctor_get(v___x_2068_, 7);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2068_, 8);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snapshotTasks_2077_);
lean_inc(v_infoState_2076_);
lean_inc(v_messages_2075_);
lean_inc(v_cache_2074_);
lean_inc(v_traceState_2069_);
lean_inc(v_auxDeclNGen_2073_);
lean_inc(v_ngen_2072_);
lean_inc(v_nextMacroScope_2071_);
lean_inc(v_env_2070_);
lean_dec(v___x_2068_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint64_t v_tid_2081_; lean_object* v_traces_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2095_; 
v_tid_2081_ = lean_ctor_get_uint64(v_traceState_2069_, sizeof(void*)*1);
v_traces_2082_ = lean_ctor_get(v_traceState_2069_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_traceState_2069_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2084_ = v_traceState_2069_;
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_traces_2082_);
lean_dec(v_traceState_2069_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2009_, v_traces_2082_);
lean_dec_ref(v_traces_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2086_);
lean_ctor_set_uint64(v_reuseFailAlloc_2094_, sizeof(void*)*1, v_tid_2081_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 4, v___x_2088_);
v___x_2090_ = v___x_2079_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_env_2070_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_nextMacroScope_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_ngen_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_auxDeclNGen_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_cache_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_messages_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_infoState_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 8, v_snapshotTasks_2077_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_st_ref_set(v___y_2013_, v___x_2090_);
lean_dec(v___y_2013_);
v___x_2092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2015_);
return v___x_2092_;
}
}
}
}
}
else
{
goto v___jp_2061_;
}
}
else
{
goto v___jp_2061_;
}
}
v___jp_2097_:
{
double v___x_2099_; double v___x_2100_; double v___x_2101_; uint8_t v___x_2102_; 
v___x_2099_ = lean_unbox_float(v_snd_2035_);
v___x_2100_ = lean_unbox_float(v_fst_2034_);
v___x_2101_ = lean_float_sub(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_float_decLt(v___y_2098_, v___x_2101_);
v___y_2067_ = v___x_2102_;
goto v___jp_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1___boxed(lean_object* v_cls_2115_, lean_object* v_collapsed_2116_, lean_object* v_tag_2117_, lean_object* v_opts_2118_, lean_object* v_clsEnabled_2119_, lean_object* v_oldTraces_2120_, lean_object* v_msg_2121_, lean_object* v_resStartStop_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
uint8_t v_collapsed_boxed_2126_; uint8_t v_clsEnabled_boxed_2127_; lean_object* v_res_2128_; 
v_collapsed_boxed_2126_ = lean_unbox(v_collapsed_2116_);
v_clsEnabled_boxed_2127_ = lean_unbox(v_clsEnabled_2119_);
v_res_2128_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v_cls_2115_, v_collapsed_boxed_2126_, v_tag_2117_, v_opts_2118_, v_clsEnabled_boxed_2127_, v_oldTraces_2120_, v_msg_2121_, v_resStartStop_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v_opts_2118_);
return v_res_2128_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(lean_object* v_e_2129_){
_start:
{
if (lean_obj_tag(v_e_2129_) == 0)
{
uint8_t v___x_2130_; 
v___x_2130_ = 2;
return v___x_2130_;
}
else
{
uint8_t v___x_2131_; 
v___x_2131_ = 0;
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4___boxed(lean_object* v_e_2132_){
_start:
{
uint8_t v_res_2133_; lean_object* v_r_2134_; 
v_res_2133_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_e_2132_);
lean_dec_ref(v_e_2132_);
v_r_2134_ = lean_box(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(lean_object* v_cls_2135_, uint8_t v_collapsed_2136_, lean_object* v_tag_2137_, lean_object* v_opts_2138_, uint8_t v_clsEnabled_2139_, lean_object* v_oldTraces_2140_, lean_object* v_msg_2141_, lean_object* v_resStartStop_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_fst_2146_; lean_object* v_snd_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2237_; 
v_fst_2146_ = lean_ctor_get(v_resStartStop_2142_, 0);
v_snd_2147_ = lean_ctor_get(v_resStartStop_2142_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_resStartStop_2142_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2149_ = v_resStartStop_2142_;
v_isShared_2150_ = v_isSharedCheck_2237_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_snd_2147_);
lean_inc(v_fst_2146_);
lean_dec(v_resStartStop_2142_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2237_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v_data_2154_; lean_object* v_fst_2157_; lean_object* v_snd_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2236_; 
v_fst_2157_ = lean_ctor_get(v_snd_2147_, 0);
v_snd_2158_ = lean_ctor_get(v_snd_2147_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_snd_2147_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2160_ = v_snd_2147_;
v_isShared_2161_ = v_isSharedCheck_2236_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_snd_2158_);
lean_inc(v_fst_2157_);
lean_dec(v_snd_2147_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2236_;
goto v_resetjp_2159_;
}
v___jp_2151_:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__7(v_oldTraces_2140_, v_data_2154_, v___y_2153_, v___y_2152_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref(v___x_2155_);
v___x_2156_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2146_);
return v___x_2156_;
}
else
{
lean_dec(v_fst_2146_);
return v___x_2155_;
}
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___y_2165_; lean_object* v_a_2166_; uint8_t v___y_2190_; double v___y_2221_; 
v___x_2162_ = l_Lean_trace_profiler;
v___x_2163_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2138_, v___x_2162_);
if (v___x_2163_ == 0)
{
v___y_2190_ = v___x_2163_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2227_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_opts_2138_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; double v___x_2230_; double v___x_2231_; double v___x_2232_; 
v___x_2228_ = l_Lean_trace_profiler_threshold;
v___x_2229_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2138_, v___x_2228_);
v___x_2230_ = lean_float_of_nat(v___x_2229_);
v___x_2231_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__4);
v___x_2232_ = lean_float_div(v___x_2230_, v___x_2231_);
v___y_2221_ = v___x_2232_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; double v___x_2235_; 
v___x_2233_ = l_Lean_trace_profiler_threshold;
v___x_2234_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__9(v_opts_2138_, v___x_2233_);
v___x_2235_ = lean_float_of_nat(v___x_2234_);
v___y_2221_ = v___x_2235_;
goto v___jp_2220_;
}
}
v___jp_2164_:
{
uint8_t v_result_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v_result_2167_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2_spec__4(v_fst_2146_);
v___x_2168_ = l_Lean_TraceResult_toEmoji(v_result_2167_);
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
v___x_2170_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__1);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 7);
lean_ctor_set(v___x_2160_, 1, v___x_2170_);
lean_ctor_set(v___x_2160_, 0, v___x_2169_);
v___x_2172_ = v___x_2160_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v_m_2174_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set_tag(v___x_2149_, 7);
lean_ctor_set(v___x_2149_, 1, v_a_2166_);
lean_ctor_set(v___x_2149_, 0, v___x_2172_);
v_m_2174_ = v___x_2149_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2166_);
v_m_2174_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; double v___x_2177_; lean_object* v_data_2178_; 
v___x_2175_ = lean_box(v_result_2167_);
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
v___x_2177_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2137_);
lean_inc_ref(v___x_2176_);
lean_inc(v_cls_2135_);
v_data_2178_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2178_, 0, v_cls_2135_);
lean_ctor_set(v_data_2178_, 1, v___x_2176_);
lean_ctor_set(v_data_2178_, 2, v_tag_2137_);
lean_ctor_set_float(v_data_2178_, sizeof(void*)*3, v___x_2177_);
lean_ctor_set_float(v_data_2178_, sizeof(void*)*3 + 8, v___x_2177_);
lean_ctor_set_uint8(v_data_2178_, sizeof(void*)*3 + 16, v_collapsed_2136_);
if (v___x_2163_ == 0)
{
lean_dec_ref(v___x_2176_);
lean_dec(v_snd_2158_);
lean_dec(v_fst_2157_);
lean_dec_ref(v_tag_2137_);
lean_dec(v_cls_2135_);
v___y_2152_ = v_m_2174_;
v___y_2153_ = v___y_2165_;
v_data_2154_ = v_data_2178_;
goto v___jp_2151_;
}
else
{
lean_object* v_data_2179_; double v___x_2180_; double v___x_2181_; 
lean_dec_ref(v_data_2178_);
v_data_2179_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2179_, 0, v_cls_2135_);
lean_ctor_set(v_data_2179_, 1, v___x_2176_);
lean_ctor_set(v_data_2179_, 2, v_tag_2137_);
v___x_2180_ = lean_unbox_float(v_fst_2157_);
lean_dec(v_fst_2157_);
lean_ctor_set_float(v_data_2179_, sizeof(void*)*3, v___x_2180_);
v___x_2181_ = lean_unbox_float(v_snd_2158_);
lean_dec(v_snd_2158_);
lean_ctor_set_float(v_data_2179_, sizeof(void*)*3 + 8, v___x_2181_);
lean_ctor_set_uint8(v_data_2179_, sizeof(void*)*3 + 16, v_collapsed_2136_);
v___y_2152_ = v_m_2174_;
v___y_2153_ = v___y_2165_;
v_data_2154_ = v_data_2179_;
goto v___jp_2151_;
}
}
}
}
v___jp_2184_:
{
lean_object* v_ref_2185_; lean_object* v___x_2186_; 
v_ref_2185_ = lean_ctor_get(v___y_2143_, 5);
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
lean_inc(v_fst_2146_);
v___x_2186_ = lean_apply_4(v_msg_2141_, v_fst_2146_, v___y_2143_, v___y_2144_, lean_box(0));
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
lean_inc(v_ref_2185_);
v___y_2165_ = v_ref_2185_;
v_a_2166_ = v_a_2187_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v___x_2186_);
v___x_2188_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5___closed__3);
lean_inc(v_ref_2185_);
v___y_2165_ = v_ref_2185_;
v_a_2166_ = v___x_2188_;
goto v___jp_2164_;
}
}
v___jp_2189_:
{
if (v_clsEnabled_2139_ == 0)
{
if (v___y_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v_traceState_2192_; lean_object* v_env_2193_; lean_object* v_nextMacroScope_2194_; lean_object* v_ngen_2195_; lean_object* v_auxDeclNGen_2196_; lean_object* v_cache_2197_; lean_object* v_messages_2198_; lean_object* v_infoState_2199_; lean_object* v_snapshotTasks_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2160_);
lean_dec(v_snd_2158_);
lean_dec(v_fst_2157_);
lean_del_object(v___x_2149_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v_msg_2141_);
lean_dec_ref(v_tag_2137_);
lean_dec(v_cls_2135_);
v___x_2191_ = lean_st_ref_take(v___y_2144_);
v_traceState_2192_ = lean_ctor_get(v___x_2191_, 4);
v_env_2193_ = lean_ctor_get(v___x_2191_, 0);
v_nextMacroScope_2194_ = lean_ctor_get(v___x_2191_, 1);
v_ngen_2195_ = lean_ctor_get(v___x_2191_, 2);
v_auxDeclNGen_2196_ = lean_ctor_get(v___x_2191_, 3);
v_cache_2197_ = lean_ctor_get(v___x_2191_, 5);
v_messages_2198_ = lean_ctor_get(v___x_2191_, 6);
v_infoState_2199_ = lean_ctor_get(v___x_2191_, 7);
v_snapshotTasks_2200_ = lean_ctor_get(v___x_2191_, 8);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2202_ = v___x_2191_;
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_snapshotTasks_2200_);
lean_inc(v_infoState_2199_);
lean_inc(v_messages_2198_);
lean_inc(v_cache_2197_);
lean_inc(v_traceState_2192_);
lean_inc(v_auxDeclNGen_2196_);
lean_inc(v_ngen_2195_);
lean_inc(v_nextMacroScope_2194_);
lean_inc(v_env_2193_);
lean_dec(v___x_2191_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint64_t v_tid_2204_; lean_object* v_traces_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2218_; 
v_tid_2204_ = lean_ctor_get_uint64(v_traceState_2192_, sizeof(void*)*1);
v_traces_2205_ = lean_ctor_get(v_traceState_2192_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_traceState_2192_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2207_ = v_traceState_2192_;
v_isShared_2208_ = v_isSharedCheck_2218_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_traces_2205_);
lean_dec(v_traceState_2192_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2218_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2140_, v_traces_2205_);
lean_dec_ref(v_traces_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2209_);
lean_ctor_set_uint64(v_reuseFailAlloc_2217_, sizeof(void*)*1, v_tid_2204_);
v___x_2211_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 4, v___x_2211_);
v___x_2213_ = v___x_2202_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_env_2193_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_nextMacroScope_2194_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_ngen_2195_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_auxDeclNGen_2196_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2216_, 5, v_cache_2197_);
lean_ctor_set(v_reuseFailAlloc_2216_, 6, v_messages_2198_);
lean_ctor_set(v_reuseFailAlloc_2216_, 7, v_infoState_2199_);
lean_ctor_set(v_reuseFailAlloc_2216_, 8, v_snapshotTasks_2200_);
v___x_2213_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_st_ref_set(v___y_2144_, v___x_2213_);
lean_dec(v___y_2144_);
v___x_2215_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__5_spec__8___redArg(v_fst_2146_);
return v___x_2215_;
}
}
}
}
}
else
{
goto v___jp_2184_;
}
}
else
{
goto v___jp_2184_;
}
}
v___jp_2220_:
{
double v___x_2222_; double v___x_2223_; double v___x_2224_; uint8_t v___x_2225_; 
v___x_2222_ = lean_unbox_float(v_snd_2158_);
v___x_2223_ = lean_unbox_float(v_fst_2157_);
v___x_2224_ = lean_float_sub(v___x_2222_, v___x_2223_);
v___x_2225_ = lean_float_decLt(v___y_2221_, v___x_2224_);
v___y_2190_ = v___x_2225_;
goto v___jp_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2___boxed(lean_object* v_cls_2238_, lean_object* v_collapsed_2239_, lean_object* v_tag_2240_, lean_object* v_opts_2241_, lean_object* v_clsEnabled_2242_, lean_object* v_oldTraces_2243_, lean_object* v_msg_2244_, lean_object* v_resStartStop_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_collapsed_boxed_2249_; uint8_t v_clsEnabled_boxed_2250_; lean_object* v_res_2251_; 
v_collapsed_boxed_2249_ = lean_unbox(v_collapsed_2239_);
v_clsEnabled_boxed_2250_ = lean_unbox(v_clsEnabled_2242_);
v_res_2251_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v_cls_2238_, v_collapsed_boxed_2249_, v_tag_2240_, v_opts_2241_, v_clsEnabled_boxed_2250_, v_oldTraces_2243_, v_msg_2244_, v_resStartStop_2245_, v___y_2246_, v___y_2247_);
lean_dec_ref(v_opts_2241_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(lean_object* v___f_2252_, lean_object* v_lratPath_2253_, uint8_t v_trimProofs_2254_, lean_object* v___f_2255_, lean_object* v_solver_2256_, lean_object* v_timeout_2257_, uint8_t v_binaryProofs_2258_, uint8_t v_solverMode_2259_, lean_object* v___f_2260_, lean_object* v___f_2261_, lean_object* v_cnfHandle_2262_, lean_object* v_cnfPath_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___y_2268_; lean_object* v_options_2286_; lean_object* v_ref_2287_; uint8_t v_hasTrace_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___y_2293_; lean_object* v___y_2294_; uint8_t v___y_2295_; lean_object* v___y_2296_; lean_object* v_a_2297_; lean_object* v___y_2310_; lean_object* v___y_2311_; uint8_t v___y_2312_; lean_object* v___y_2313_; lean_object* v_a_2314_; lean_object* v___y_2324_; uint8_t v___y_2325_; lean_object* v___y_2367_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v_a_2406_; uint8_t v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v_a_2423_; uint8_t v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2486_; 
v_options_2286_ = lean_ctor_get(v___y_2264_, 2);
v_ref_2287_ = lean_ctor_get(v___y_2264_, 5);
v_hasTrace_2288_ = lean_ctor_get_uint8(v_options_2286_, sizeof(void*)*1);
v___x_2289_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new___closed__9));
v___x_2290_ = 1;
v___x_2291_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_LRAT_0__Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new_determineSolver_spec__1___closed__0));
if (v_hasTrace_2288_ == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref(v___f_2261_);
v___x_2495_ = l_IO_lazyPure___redArg(v___f_2260_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = lean_io_prim_handle_put_str(v_cnfHandle_2262_, v_a_2496_);
lean_dec(v_a_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v___x_2497_);
v___x_2498_ = lean_io_prim_handle_flush(v_cnfHandle_2262_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_dec_ref(v___x_2498_);
goto v___jp_2475_;
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2510_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2510_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2510_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2503_ = lean_io_error_to_string(v_a_2499_);
v___x_2504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
v___x_2505_ = l_Lean_MessageData_ofFormat(v___x_2504_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_ref_2287_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2506_);
v___x_2508_ = v___x_2501_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2522_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2511_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2513_ = v___x_2497_;
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2497_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2522_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2515_ = lean_io_error_to_string(v_a_2511_);
v___x_2516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
v___x_2517_ = l_Lean_MessageData_ofFormat(v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_ref_2287_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2518_);
v___x_2520_ = v___x_2513_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2534_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2523_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2525_ = v___x_2495_;
v_isShared_2526_ = v_isSharedCheck_2534_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2495_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2534_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2527_ = lean_io_error_to_string(v_a_2523_);
v___x_2528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
v___x_2529_ = l_Lean_MessageData_ofFormat(v___x_2528_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_ref_2287_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2530_);
v___x_2532_ = v___x_2525_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2721_; 
v___x_2535_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2289_, v___y_2264_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2721_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2721_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v_a_2543_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v_a_2559_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; uint8_t v___x_2678_; 
v___x_2678_ = lean_unbox(v_a_2536_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = l_Lean_trace_profiler;
v___x_2680_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2286_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_del_object(v___x_2538_);
lean_dec(v_a_2536_);
lean_dec_ref(v___f_2261_);
v___x_2681_ = l_IO_lazyPure___redArg(v___f_2260_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = lean_io_prim_handle_put_str(v_cnfHandle_2262_, v_a_2682_);
lean_dec(v_a_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v___x_2683_);
v___x_2684_ = lean_io_prim_handle_flush(v_cnfHandle_2262_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref(v___x_2684_);
goto v___jp_2475_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2696_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2689_ = lean_io_error_to_string(v_a_2685_);
v___x_2690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = l_Lean_MessageData_ofFormat(v___x_2690_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_ref_2287_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2692_);
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2708_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2697_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2699_ = v___x_2683_;
v_isShared_2700_ = v_isSharedCheck_2708_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2683_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2708_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2701_ = lean_io_error_to_string(v_a_2697_);
v___x_2702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
v___x_2703_ = l_Lean_MessageData_ofFormat(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_ref_2287_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2704_);
v___x_2706_ = v___x_2699_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2720_; 
lean_inc(v_ref_2287_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2709_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2711_ = v___x_2681_;
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2681_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2713_ = lean_io_error_to_string(v_a_2709_);
v___x_2714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
v___x_2715_ = l_Lean_MessageData_ofFormat(v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_ref_2287_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2716_);
v___x_2718_ = v___x_2711_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
goto v___jp_2581_;
}
}
else
{
goto v___jp_2581_;
}
v___jp_2540_:
{
lean_object* v___x_2544_; double v___x_2545_; double v___x_2546_; double v___x_2547_; double v___x_2548_; double v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2544_ = lean_io_mono_nanos_now();
v___x_2545_ = lean_float_of_nat(v___y_2542_);
v___x_2546_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2547_ = lean_float_div(v___x_2545_, v___x_2546_);
v___x_2548_ = lean_float_of_nat(v___x_2544_);
v___x_2549_ = lean_float_div(v___x_2548_, v___x_2546_);
v___x_2550_ = lean_box_float(v___x_2547_);
v___x_2551_ = lean_box_float(v___x_2549_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2543_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2555_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2289_, v___x_2290_, v___x_2291_, v_options_2286_, v___x_2554_, v___y_2541_, v___f_2261_, v___x_2553_, v___y_2264_, v___y_2265_);
v___y_2486_ = v___x_2555_;
goto v___jp_2485_;
}
v___jp_2556_:
{
lean_object* v___x_2561_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v_a_2559_);
v___x_2561_ = v___x_2538_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
v___y_2541_ = v___y_2557_;
v___y_2542_ = v___y_2558_;
v_a_2543_ = v___x_2561_;
goto v___jp_2540_;
}
}
v___jp_2563_:
{
lean_object* v___x_2567_; double v___x_2568_; double v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2567_ = lean_io_get_num_heartbeats();
v___x_2568_ = lean_float_of_nat(v___y_2565_);
v___x_2569_ = lean_float_of_nat(v___x_2567_);
v___x_2570_ = lean_box_float(v___x_2568_);
v___x_2571_ = lean_box_float(v___x_2569_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v_a_2566_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__2(v___x_2289_, v___x_2290_, v___x_2291_, v_options_2286_, v___x_2574_, v___y_2564_, v___f_2261_, v___x_2573_, v___y_2264_, v___y_2265_);
v___y_2486_ = v___x_2575_;
goto v___jp_2485_;
}
v___jp_2576_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2579_);
v___y_2564_ = v___y_2577_;
v___y_2565_ = v___y_2578_;
v_a_2566_ = v___x_2580_;
goto v___jp_2563_;
}
v___jp_2581_:
{
lean_object* v___x_2582_; lean_object* v_a_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2582_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2265_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2585_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2286_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_io_mono_nanos_now();
v___x_2587_ = l_IO_lazyPure___redArg(v___f_2260_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref(v___x_2587_);
v___x_2589_ = lean_io_prim_handle_put_str(v_cnfHandle_2262_, v_a_2588_);
lean_dec(v_a_2588_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v___x_2589_);
v___x_2590_ = lean_io_prim_handle_flush(v_cnfHandle_2262_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_del_object(v___x_2538_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
v___y_2541_ = v_a_2583_;
v___y_2542_ = v___x_2586_;
v_a_2543_ = v___x_2596_;
goto v___jp_2540_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2609_; 
v_a_2599_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2601_ = v___x_2590_;
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2590_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = lean_io_error_to_string(v_a_2599_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 3);
lean_ctor_set(v___x_2601_, 0, v___x_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = l_Lean_MessageData_ofFormat(v___x_2605_);
lean_inc(v_ref_2287_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_ref_2287_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___y_2557_ = v_a_2583_;
v___y_2558_ = v___x_2586_;
v_a_2559_ = v___x_2607_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2620_; 
v_a_2610_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2612_ = v___x_2589_;
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2589_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2614_ = lean_io_error_to_string(v_a_2610_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 3);
lean_ctor_set(v___x_2612_, 0, v___x_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = l_Lean_MessageData_ofFormat(v___x_2616_);
lean_inc(v_ref_2287_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_ref_2287_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___y_2557_ = v_a_2583_;
v___y_2558_ = v___x_2586_;
v_a_2559_ = v___x_2618_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2631_; 
v_a_2621_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2623_ = v___x_2587_;
v_isShared_2624_ = v_isSharedCheck_2631_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2587_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2631_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_io_error_to_string(v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 3);
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = l_Lean_MessageData_ofFormat(v___x_2627_);
lean_inc(v_ref_2287_);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_ref_2287_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___y_2557_ = v_a_2583_;
v___y_2558_ = v___x_2586_;
v_a_2559_ = v___x_2629_;
goto v___jp_2556_;
}
}
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_del_object(v___x_2538_);
v___x_2632_ = lean_io_get_num_heartbeats();
v___x_2633_ = l_IO_lazyPure___redArg(v___f_2260_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = lean_io_prim_handle_put_str(v_cnfHandle_2262_, v_a_2634_);
lean_dec(v_a_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref(v___x_2635_);
v___x_2636_ = lean_io_prim_handle_flush(v_cnfHandle_2262_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set_tag(v___x_2639_, 1);
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v___y_2564_ = v_a_2583_;
v___y_2565_ = v___x_2632_;
v_a_2566_ = v___x_2642_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2655_; 
v_a_2645_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2647_ = v___x_2636_;
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2636_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_io_error_to_string(v_a_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set_tag(v___x_2647_, 3);
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = l_Lean_MessageData_ofFormat(v___x_2651_);
lean_inc(v_ref_2287_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_ref_2287_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___y_2577_ = v_a_2583_;
v___y_2578_ = v___x_2632_;
v_a_2579_ = v___x_2653_;
goto v___jp_2576_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2666_; 
v_a_2656_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2658_ = v___x_2635_;
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2635_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2666_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_io_error_to_string(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set_tag(v___x_2658_, 3);
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = l_Lean_MessageData_ofFormat(v___x_2662_);
lean_inc(v_ref_2287_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_ref_2287_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___y_2577_ = v_a_2583_;
v___y_2578_ = v___x_2632_;
v_a_2579_ = v___x_2664_;
goto v___jp_2576_;
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2677_; 
v_a_2667_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2669_ = v___x_2633_;
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2633_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2677_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = lean_io_error_to_string(v_a_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 3);
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = l_Lean_MessageData_ofFormat(v___x_2673_);
lean_inc(v_ref_2287_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_ref_2287_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___y_2577_ = v_a_2583_;
v___y_2578_ = v___x_2632_;
v_a_2579_ = v___x_2675_;
goto v___jp_2576_;
}
}
}
}
}
}
}
v___jp_2267_:
{
if (lean_obj_tag(v___y_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2277_; 
v_a_2269_ = lean_ctor_get(v___y_2268_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___y_2268_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2271_ = v___y_2268_;
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___y_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2269_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___y_2268_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___y_2268_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___y_2268_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___y_2268_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2292_:
{
lean_object* v___x_2298_; double v___x_2299_; double v___x_2300_; double v___x_2301_; double v___x_2302_; double v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2298_ = lean_io_mono_nanos_now();
v___x_2299_ = lean_float_of_nat(v___y_2293_);
v___x_2300_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2301_ = lean_float_div(v___x_2299_, v___x_2300_);
v___x_2302_ = lean_float_of_nat(v___x_2298_);
v___x_2303_ = lean_float_div(v___x_2302_, v___x_2300_);
v___x_2304_ = lean_box_float(v___x_2301_);
v___x_2305_ = lean_box_float(v___x_2303_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_a_2297_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2289_, v___x_2290_, v___x_2291_, v___y_2294_, v___y_2295_, v___y_2296_, v___f_2252_, v___x_2307_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2294_);
v___y_2268_ = v___x_2308_;
goto v___jp_2267_;
}
v___jp_2309_:
{
lean_object* v___x_2315_; double v___x_2316_; double v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2315_ = lean_io_get_num_heartbeats();
v___x_2316_ = lean_float_of_nat(v___y_2310_);
v___x_2317_ = lean_float_of_nat(v___x_2315_);
v___x_2318_ = lean_box_float(v___x_2316_);
v___x_2319_ = lean_box_float(v___x_2317_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2314_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__0(v___x_2289_, v___x_2290_, v___x_2291_, v___y_2311_, v___y_2312_, v___y_2313_, v___f_2252_, v___x_2321_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2311_);
v___y_2268_ = v___x_2322_;
goto v___jp_2267_;
}
v___jp_2323_:
{
lean_object* v___x_2326_; lean_object* v_a_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2326_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2265_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2329_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_2324_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_io_mono_nanos_now();
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2331_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2253_, v_trimProofs_2254_, v___y_2264_, v___y_2265_);
lean_dec_ref(v_lratPath_2253_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v___y_2293_ = v___x_2330_;
v___y_2294_ = v___y_2324_;
v___y_2295_ = v___y_2325_;
v___y_2296_ = v_a_2327_;
v_a_2297_ = v___x_2337_;
goto v___jp_2292_;
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_a_2340_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2331_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2331_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 0);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v___y_2293_ = v___x_2330_;
v___y_2294_ = v___y_2324_;
v___y_2295_ = v___y_2325_;
v___y_2296_ = v_a_2327_;
v_a_2297_ = v___x_2345_;
goto v___jp_2292_;
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2349_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2253_, v_trimProofs_2254_, v___y_2264_, v___y_2265_);
lean_dec_ref(v_lratPath_2253_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
v___y_2310_ = v___x_2348_;
v___y_2311_ = v___y_2324_;
v___y_2312_ = v___y_2325_;
v___y_2313_ = v_a_2327_;
v_a_2314_ = v___x_2355_;
goto v___jp_2309_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2349_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2349_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 0);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v___y_2310_ = v___x_2348_;
v___y_2311_ = v___y_2324_;
v___y_2312_ = v___y_2325_;
v___y_2313_ = v_a_2327_;
v_a_2314_ = v___x_2363_;
goto v___jp_2309_;
}
}
}
}
}
v___jp_2366_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2392_; 
v_a_2368_ = lean_ctor_get(v___y_2367_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2370_ = v___y_2367_;
v_isShared_2371_ = v_isSharedCheck_2392_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___y_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2392_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
if (lean_obj_tag(v_a_2368_) == 0)
{
lean_object* v_assignment_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_assignment_2372_ = lean_ctor_get(v_a_2368_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_a_2368_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2374_ = v_a_2368_;
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_assignment_2372_);
lean_dec(v_a_2368_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2382_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_assignment_2372_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2377_);
v___x_2379_ = v___x_2370_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_del_object(v___x_2370_);
lean_dec(v_a_2368_);
if (v_hasTrace_2288_ == 0)
{
lean_object* v___x_2383_; 
lean_dec_ref(v___f_2252_);
v___x_2383_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2253_, v_trimProofs_2254_, v___y_2264_, v___y_2265_);
lean_dec_ref(v_lratPath_2253_);
v___y_2268_ = v___x_2383_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2384_; lean_object* v_a_2385_; uint8_t v___x_2386_; 
v___x_2384_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2289_, v___y_2264_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref(v___x_2384_);
v___x_2386_ = lean_unbox(v_a_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = l_Lean_trace_profiler;
v___x_2388_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2286_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_dec(v_a_2385_);
lean_dec_ref(v___f_2252_);
v___x_2389_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_2253_, v_trimProofs_2254_, v___y_2264_, v___y_2265_);
lean_dec_ref(v_lratPath_2253_);
v___y_2268_ = v___x_2389_;
goto v___jp_2267_;
}
else
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_unbox(v_a_2385_);
lean_dec(v_a_2385_);
lean_inc_ref(v_options_2286_);
v___y_2324_ = v_options_2286_;
v___y_2325_ = v___x_2390_;
goto v___jp_2323_;
}
}
else
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_unbox(v_a_2385_);
lean_dec(v_a_2385_);
lean_inc_ref(v_options_2286_);
v___y_2324_ = v_options_2286_;
v___y_2325_ = v___x_2391_;
goto v___jp_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2393_ = lean_ctor_get(v___y_2367_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___y_2367_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___y_2367_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
v___jp_2401_:
{
lean_object* v___x_2407_; double v___x_2408_; double v___x_2409_; double v___x_2410_; double v___x_2411_; double v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2407_ = lean_io_mono_nanos_now();
v___x_2408_ = lean_float_of_nat(v___y_2405_);
v___x_2409_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___closed__3);
v___x_2410_ = lean_float_div(v___x_2408_, v___x_2409_);
v___x_2411_ = lean_float_of_nat(v___x_2407_);
v___x_2412_ = lean_float_div(v___x_2411_, v___x_2409_);
v___x_2413_ = lean_box_float(v___x_2410_);
v___x_2414_ = lean_box_float(v___x_2412_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v_a_2406_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2417_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2289_, v___x_2290_, v___x_2291_, v___y_2404_, v___y_2402_, v___y_2403_, v___f_2255_, v___x_2416_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2404_);
v___y_2367_ = v___x_2417_;
goto v___jp_2366_;
}
v___jp_2418_:
{
lean_object* v___x_2424_; double v___x_2425_; double v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2424_ = lean_io_get_num_heartbeats();
v___x_2425_ = lean_float_of_nat(v___y_2422_);
v___x_2426_ = lean_float_of_nat(v___x_2424_);
v___x_2427_ = lean_box_float(v___x_2425_);
v___x_2428_ = lean_box_float(v___x_2426_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2423_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
v___x_2431_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__1(v___x_2289_, v___x_2290_, v___x_2291_, v___y_2421_, v___y_2419_, v___y_2420_, v___f_2255_, v___x_2430_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___y_2421_);
v___y_2367_ = v___x_2431_;
goto v___jp_2366_;
}
v___jp_2432_:
{
lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2435_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__3___redArg(v___y_2265_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref(v___x_2435_);
v___x_2437_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2438_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v___y_2434_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_io_mono_nanos_now();
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v_lratPath_2253_);
v___x_2440_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2256_, v_cnfPath_2263_, v_lratPath_2253_, v_timeout_2257_, v_binaryProofs_2258_, v_solverMode_2259_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set_tag(v___x_2443_, 1);
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
v___y_2402_ = v___y_2433_;
v___y_2403_ = v_a_2436_;
v___y_2404_ = v___y_2434_;
v___y_2405_ = v___x_2439_;
v_a_2406_ = v___x_2446_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2440_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2440_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 0);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
v___y_2402_ = v___y_2433_;
v___y_2403_ = v_a_2436_;
v___y_2404_ = v___y_2434_;
v___y_2405_ = v___x_2439_;
v_a_2406_ = v___x_2454_;
goto v___jp_2401_;
}
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v_lratPath_2253_);
v___x_2458_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2256_, v_cnfPath_2263_, v_lratPath_2253_, v_timeout_2257_, v_binaryProofs_2258_, v_solverMode_2259_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 1);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
v___y_2419_ = v___y_2433_;
v___y_2420_ = v_a_2436_;
v___y_2421_ = v___y_2434_;
v___y_2422_ = v___x_2457_;
v_a_2423_ = v___x_2464_;
goto v___jp_2418_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2458_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2458_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 0);
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
v___y_2419_ = v___y_2433_;
v___y_2420_ = v_a_2436_;
v___y_2421_ = v___y_2434_;
v___y_2422_ = v___x_2457_;
v_a_2423_ = v___x_2472_;
goto v___jp_2418_;
}
}
}
}
}
v___jp_2475_:
{
if (v_hasTrace_2288_ == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref(v___f_2255_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v_lratPath_2253_);
v___x_2476_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2256_, v_cnfPath_2263_, v_lratPath_2253_, v_timeout_2257_, v_binaryProofs_2258_, v_solverMode_2259_, v___y_2264_, v___y_2265_);
v___y_2367_ = v___x_2476_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2477_; lean_object* v_a_2478_; uint8_t v___x_2479_; 
v___x_2477_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__0___redArg(v___x_2289_, v___y_2264_);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = lean_unbox(v_a_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = l_Lean_trace_profiler;
v___x_2481_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load_spec__4(v_options_2286_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_dec(v_a_2478_);
lean_dec_ref(v___f_2255_);
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc_ref(v_lratPath_2253_);
v___x_2482_ = l_Lean_Elab_Tactic_BVDecide_External_satQuery(v_solver_2256_, v_cnfPath_2263_, v_lratPath_2253_, v_timeout_2257_, v_binaryProofs_2258_, v_solverMode_2259_, v___y_2264_, v___y_2265_);
v___y_2367_ = v___x_2482_;
goto v___jp_2366_;
}
else
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_unbox(v_a_2478_);
lean_dec(v_a_2478_);
lean_inc_ref(v_options_2286_);
v___y_2433_ = v___x_2483_;
v___y_2434_ = v_options_2286_;
goto v___jp_2432_;
}
}
else
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_unbox(v_a_2478_);
lean_dec(v_a_2478_);
lean_inc_ref(v_options_2286_);
v___y_2433_ = v___x_2484_;
v___y_2434_ = v_options_2286_;
goto v___jp_2432_;
}
}
}
v___jp_2485_:
{
if (lean_obj_tag(v___y_2486_) == 0)
{
lean_dec_ref(v___y_2486_);
goto v___jp_2475_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_cnfPath_2263_);
lean_dec_ref(v_solver_2256_);
lean_dec_ref(v___f_2255_);
lean_dec_ref(v_lratPath_2253_);
lean_dec_ref(v___f_2252_);
v_a_2487_ = lean_ctor_get(v___y_2486_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___y_2486_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___y_2486_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___y_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed(lean_object* v___f_2722_, lean_object* v_lratPath_2723_, lean_object* v_trimProofs_2724_, lean_object* v___f_2725_, lean_object* v_solver_2726_, lean_object* v_timeout_2727_, lean_object* v_binaryProofs_2728_, lean_object* v_solverMode_2729_, lean_object* v___f_2730_, lean_object* v___f_2731_, lean_object* v_cnfHandle_2732_, lean_object* v_cnfPath_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
uint8_t v_trimProofs_boxed_2737_; uint8_t v_binaryProofs_boxed_2738_; uint8_t v_solverMode_boxed_2739_; lean_object* v_res_2740_; 
v_trimProofs_boxed_2737_ = lean_unbox(v_trimProofs_2724_);
v_binaryProofs_boxed_2738_ = lean_unbox(v_binaryProofs_2728_);
v_solverMode_boxed_2739_ = lean_unbox(v_solverMode_2729_);
v_res_2740_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4(v___f_2722_, v_lratPath_2723_, v_trimProofs_boxed_2737_, v___f_2725_, v_solver_2726_, v_timeout_2727_, v_binaryProofs_boxed_2738_, v_solverMode_boxed_2739_, v___f_2730_, v___f_2731_, v_cnfHandle_2732_, v_cnfPath_2733_, v___y_2734_, v___y_2735_);
lean_dec(v_cnfHandle_2732_);
lean_dec(v_timeout_2727_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object* v_cnf_2744_, lean_object* v_solver_2745_, lean_object* v_lratPath_2746_, uint8_t v_trimProofs_2747_, lean_object* v_timeout_2748_, uint8_t v_binaryProofs_2749_, uint8_t v_solverMode_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___f_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; 
v___f_2754_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2754_, 0, v_cnf_2744_);
v___f_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__0));
v___f_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__1));
v___f_2757_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___closed__2));
v___x_2758_ = lean_box(v_trimProofs_2747_);
v___x_2759_ = lean_box(v_binaryProofs_2749_);
v___x_2760_ = lean_box(v_solverMode_2750_);
v___f_2761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___lam__4___boxed), 15, 10);
lean_closure_set(v___f_2761_, 0, v___f_2756_);
lean_closure_set(v___f_2761_, 1, v_lratPath_2746_);
lean_closure_set(v___f_2761_, 2, v___x_2758_);
lean_closure_set(v___f_2761_, 3, v___f_2755_);
lean_closure_set(v___f_2761_, 4, v_solver_2745_);
lean_closure_set(v___f_2761_, 5, v_timeout_2748_);
lean_closure_set(v___f_2761_, 6, v___x_2759_);
lean_closure_set(v___f_2761_, 7, v___x_2760_);
lean_closure_set(v___f_2761_, 8, v___f_2754_);
lean_closure_set(v___f_2761_, 9, v___f_2757_);
v___x_2762_ = l_IO_FS_withTempFile___at___00Lean_Elab_Tactic_BVDecide_Frontend_runExternal_spec__3___redArg(v___f_2761_, v_a_2751_, v_a_2752_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal___boxed(lean_object* v_cnf_2763_, lean_object* v_solver_2764_, lean_object* v_lratPath_2765_, lean_object* v_trimProofs_2766_, lean_object* v_timeout_2767_, lean_object* v_binaryProofs_2768_, lean_object* v_solverMode_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
uint8_t v_trimProofs_boxed_2773_; uint8_t v_binaryProofs_boxed_2774_; uint8_t v_solverMode_boxed_2775_; lean_object* v_res_2776_; 
v_trimProofs_boxed_2773_ = lean_unbox(v_trimProofs_2766_);
v_binaryProofs_boxed_2774_ = lean_unbox(v_binaryProofs_2768_);
v_solverMode_boxed_2775_ = lean_unbox(v_solverMode_2769_);
v_res_2776_ = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(v_cnf_2763_, v_solver_2764_, v_lratPath_2765_, v_trimProofs_boxed_2773_, v_timeout_2767_, v_binaryProofs_boxed_2774_, v_solverMode_boxed_2775_, v_a_2770_, v_a_2771_);
return v_res_2776_;
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
