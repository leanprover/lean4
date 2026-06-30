// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: public import Init.Data.Sum public import Lean.LabelAttribute public import Lean.Meta.Tactic.Backtrack public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Repeat public import Lean.Meta.Tactic.Symm public import Lean.Elab.Term
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 179, 43, 63, 49, 24, 32, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SolveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 124, 130, 51, 187, 220, 69, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(217, 20, 184, 114, 46, 152, 175, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 70, 43, 38, 54, 221, 118, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 139, 182, 61, 70, 53, 35, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 96, 167, 3, 193, 174, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 99, 190, 156, 65, 10, 108, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 198, 193, 11, 27, 150, 253, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 168, 148, 157, 214, 227, 227, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 34, 196, 227, 75, 22, 166, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 42, 156, 241, 147, 248, 49, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 159, 244, 240, 243, 215, 3, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1979843508) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 117, 78, 143, 26, 177, 227, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 86, 236, 87, 154, 213, 60, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 78, 242, 178, 10, 32, 62, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 116, 242, 130, 86, 112, 31, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "trying to apply: "};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value;
static const lean_array_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`repeat1'` made no progress"};
static const lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 32, .m_data = "⏮️ starting over using `exfalso`"};
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "It doesn't make sense to remove local hypotheses when using `only` without `*`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 57, 166, 49, 41, 228, 20)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value;
static const lean_array_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "It doesn't make sense to use `*` without `only`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_74_ = 0;
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_76_ = l_Lean_registerTraceClass(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
return v_res_78_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_traceState_91_; lean_object* v_traces_92_; lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_env_95_; lean_object* v_nextMacroScope_96_; lean_object* v_ngen_97_; lean_object* v_auxDeclNGen_98_; lean_object* v_cache_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_121_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_traceState_91_ = lean_ctor_get(v___x_90_, 4);
lean_inc_ref(v_traceState_91_);
lean_dec(v___x_90_);
v_traces_92_ = lean_ctor_get(v_traceState_91_, 0);
lean_inc_ref(v_traces_92_);
lean_dec_ref(v_traceState_91_);
v___x_93_ = lean_st_ref_take(v___y_88_);
v_traceState_94_ = lean_ctor_get(v___x_93_, 4);
v_env_95_ = lean_ctor_get(v___x_93_, 0);
v_nextMacroScope_96_ = lean_ctor_get(v___x_93_, 1);
v_ngen_97_ = lean_ctor_get(v___x_93_, 2);
v_auxDeclNGen_98_ = lean_ctor_get(v___x_93_, 3);
v_cache_99_ = lean_ctor_get(v___x_93_, 5);
v_messages_100_ = lean_ctor_get(v___x_93_, 6);
v_infoState_101_ = lean_ctor_get(v___x_93_, 7);
v_snapshotTasks_102_ = lean_ctor_get(v___x_93_, 8);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_121_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snapshotTasks_102_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_100_);
lean_inc(v_cache_99_);
lean_inc(v_traceState_94_);
lean_inc(v_auxDeclNGen_98_);
lean_inc(v_ngen_97_);
lean_inc(v_nextMacroScope_96_);
lean_inc(v_env_95_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint64_t v_tid_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_119_; 
v_tid_106_ = lean_ctor_get_uint64(v_traceState_94_, sizeof(void*)*1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_traceState_94_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_traceState_94_, 0);
lean_dec(v_unused_120_);
v___x_108_ = v_traceState_94_;
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_traceState_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_110_);
lean_ctor_set_uint64(v_reuseFailAlloc_118_, sizeof(void*)*1, v_tid_106_);
v___x_112_ = v_reuseFailAlloc_118_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 4, v___x_112_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_env_95_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_nextMacroScope_96_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_auxDeclNGen_98_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_117_, 5, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_117_, 6, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_117_, 7, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_117_, 8, v_snapshotTasks_102_);
v___x_114_ = v_reuseFailAlloc_117_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_st_ref_set(v___y_88_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_traces_92_);
return v___x_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_122_);
lean_dec(v___y_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_name_139_; lean_object* v_defValue_140_; lean_object* v_map_141_; lean_object* v___x_142_; 
v_name_139_ = lean_ctor_get(v_opt_138_, 0);
v_defValue_140_ = lean_ctor_get(v_opt_138_, 1);
v_map_141_ = lean_ctor_get(v_opts_137_, 0);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_141_, v_name_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v_defValue_140_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_142_, 1);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref_known(v_val_144_, 0);
return v_v_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec(v_val_144_);
v___x_146_ = lean_unbox(v_defValue_140_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_147_, v_opt_148_);
lean_dec_ref(v_opt_148_);
lean_dec_ref(v_opts_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_saveState___redArg(v___y_153_, v___y_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
v___x_159_ = lean_apply_5(v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_a_158_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_198_; 
v_a_169_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_198_ == 0)
{
v___x_171_ = v___x_159_;
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___y_174_; uint8_t v___x_196_; 
v___x_196_ = l_Lean_Exception_isInterrupt(v_a_169_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_inc(v_a_169_);
v___x_197_ = l_Lean_Exception_isRuntime(v_a_169_);
v___y_174_ = v___x_197_;
goto v___jp_173_;
}
else
{
v___y_174_ = v___x_196_;
goto v___jp_173_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; 
lean_del_object(v___x_171_);
lean_dec(v_a_169_);
v___x_175_ = l_Lean_Meta_SavedState_restore___redArg(v_a_158_, v___y_153_, v___y_155_);
lean_dec(v_a_158_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_175_, 0);
lean_dec(v_unused_184_);
v___x_177_ = v___x_175_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_a_158_);
if (v_isShared_172_ == 0)
{
v___x_194_ = v___x_171_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_169_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_x_151_);
v_a_199_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_157_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_157_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_222_, v_x_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_233_, lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_241_ = l_Lean_MessageData_ofExpr(v_e_233_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_x_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_252_, uint8_t v___x_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_x_255_);
return v___x_261_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_287_; 
v_head_262_ = lean_ctor_get(v_x_254_, 0);
v_tail_263_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_287_ == 0)
{
v___x_265_ = v_x_254_;
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_head_262_);
lean_dec(v_x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v_a_268_; lean_object* v___x_274_; 
lean_inc(v_head_262_);
v___x_274_ = l_Lean_MVarId_inferInstance(v_head_262_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref_known(v___x_274_, 1);
v_a_268_ = v___x_252_;
goto v___jp_267_;
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_286_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_286_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___y_280_; uint8_t v___x_284_; 
v___x_284_ = l_Lean_Exception_isInterrupt(v_a_275_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v_a_275_);
v___x_285_ = l_Lean_Exception_isRuntime(v_a_275_);
v___y_280_ = v___x_285_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_del_object(v___x_277_);
lean_dec(v_a_275_);
v_a_268_ = v___x_253_;
goto v___jp_267_;
}
else
{
lean_object* v___x_282_; 
lean_del_object(v___x_265_);
lean_dec(v_tail_263_);
lean_dec(v_head_262_);
lean_dec(v_x_255_);
if (v_isShared_278_ == 0)
{
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_275_);
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
v___jp_267_:
{
if (v_a_268_ == 0)
{
lean_del_object(v___x_265_);
lean_dec(v_head_262_);
v_x_254_ = v_tail_263_;
goto _start;
}
else
{
lean_object* v___x_271_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_x_255_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_head_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_x_255_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v_x_254_ = v_tail_263_;
v_x_255_ = v___x_271_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_14151__boxed_297_; uint8_t v___x_14152__boxed_298_; lean_object* v_res_299_; 
v___x_14151__boxed_297_ = lean_unbox(v___x_288_);
v___x_14152__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14151__boxed_297_, v___x_14152__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_mctx_309_; lean_object* v_lctx_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_mctx_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_309_);
lean_dec(v___x_308_);
v_lctx_310_ = lean_ctor_get(v___y_301_, 2);
v_options_311_ = lean_ctor_get(v___y_303_, 2);
lean_inc_ref(v_options_311_);
lean_inc_ref(v_lctx_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_307_);
lean_ctor_set(v___x_312_, 1, v_mctx_309_);
lean_ctor_set(v___x_312_, 2, v_lctx_310_);
lean_ctor_set(v___x_312_, 3, v_options_311_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_300_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_325_ == 0)
{
return v_bs_324_;
}
else
{
lean_object* v_v_326_; lean_object* v_msg_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_326_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
v_msg_327_ = lean_ctor_get(v_v_326_, 1);
lean_inc_ref(v_msg_327_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_323_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_329_, v_i_323_, v_msg_327_);
v_i_323_ = v___x_331_;
v_bs_324_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_bs_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_337_, v_i_boxed_338_, v_bs_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_340_, lean_object* v_data_341_, lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_fileName_349_; lean_object* v_fileMap_350_; lean_object* v_options_351_; lean_object* v_currRecDepth_352_; lean_object* v_maxRecDepth_353_; lean_object* v_ref_354_; lean_object* v_currNamespace_355_; lean_object* v_openDecls_356_; lean_object* v_initHeartbeats_357_; lean_object* v_maxHeartbeats_358_; lean_object* v_quotContext_359_; lean_object* v_currMacroScope_360_; uint8_t v_diag_361_; lean_object* v_cancelTk_x3f_362_; uint8_t v_suppressElabErrors_363_; lean_object* v_inheritedTraceOptions_364_; lean_object* v___x_365_; lean_object* v_traceState_366_; lean_object* v_traces_367_; lean_object* v_ref_368_; lean_object* v___x_369_; lean_object* v___x_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v_msg_374_; lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_413_; 
v_fileName_349_ = lean_ctor_get(v___y_346_, 0);
v_fileMap_350_ = lean_ctor_get(v___y_346_, 1);
v_options_351_ = lean_ctor_get(v___y_346_, 2);
v_currRecDepth_352_ = lean_ctor_get(v___y_346_, 3);
v_maxRecDepth_353_ = lean_ctor_get(v___y_346_, 4);
v_ref_354_ = lean_ctor_get(v___y_346_, 5);
v_currNamespace_355_ = lean_ctor_get(v___y_346_, 6);
v_openDecls_356_ = lean_ctor_get(v___y_346_, 7);
v_initHeartbeats_357_ = lean_ctor_get(v___y_346_, 8);
v_maxHeartbeats_358_ = lean_ctor_get(v___y_346_, 9);
v_quotContext_359_ = lean_ctor_get(v___y_346_, 10);
v_currMacroScope_360_ = lean_ctor_get(v___y_346_, 11);
v_diag_361_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14);
v_cancelTk_x3f_362_ = lean_ctor_get(v___y_346_, 12);
v_suppressElabErrors_363_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_364_ = lean_ctor_get(v___y_346_, 13);
v___x_365_ = lean_st_ref_get(v___y_347_);
v_traceState_366_ = lean_ctor_get(v___x_365_, 4);
lean_inc_ref(v_traceState_366_);
lean_dec(v___x_365_);
v_traces_367_ = lean_ctor_get(v_traceState_366_, 0);
lean_inc_ref(v_traces_367_);
lean_dec_ref(v_traceState_366_);
v_ref_368_ = l_Lean_replaceRef(v_ref_342_, v_ref_354_);
lean_inc_ref(v_inheritedTraceOptions_364_);
lean_inc(v_cancelTk_x3f_362_);
lean_inc(v_currMacroScope_360_);
lean_inc(v_quotContext_359_);
lean_inc(v_maxHeartbeats_358_);
lean_inc(v_initHeartbeats_357_);
lean_inc(v_openDecls_356_);
lean_inc(v_currNamespace_355_);
lean_inc(v_maxRecDepth_353_);
lean_inc(v_currRecDepth_352_);
lean_inc_ref(v_options_351_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___x_369_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_369_, 0, v_fileName_349_);
lean_ctor_set(v___x_369_, 1, v_fileMap_350_);
lean_ctor_set(v___x_369_, 2, v_options_351_);
lean_ctor_set(v___x_369_, 3, v_currRecDepth_352_);
lean_ctor_set(v___x_369_, 4, v_maxRecDepth_353_);
lean_ctor_set(v___x_369_, 5, v_ref_368_);
lean_ctor_set(v___x_369_, 6, v_currNamespace_355_);
lean_ctor_set(v___x_369_, 7, v_openDecls_356_);
lean_ctor_set(v___x_369_, 8, v_initHeartbeats_357_);
lean_ctor_set(v___x_369_, 9, v_maxHeartbeats_358_);
lean_ctor_set(v___x_369_, 10, v_quotContext_359_);
lean_ctor_set(v___x_369_, 11, v_currMacroScope_360_);
lean_ctor_set(v___x_369_, 12, v_cancelTk_x3f_362_);
lean_ctor_set(v___x_369_, 13, v_inheritedTraceOptions_364_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14, v_diag_361_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14 + 1, v_suppressElabErrors_363_);
v___x_370_ = l_Lean_PersistentArray_toArray___redArg(v_traces_367_);
lean_dec_ref(v_traces_367_);
v_sz_371_ = lean_array_size(v___x_370_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_371_, v___x_372_, v___x_370_);
v_msg_374_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_374_, 0, v_data_341_);
lean_ctor_set(v_msg_374_, 1, v_msg_343_);
lean_ctor_set(v_msg_374_, 2, v___x_373_);
v___x_375_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_374_, v___y_344_, v___y_345_, v___x_369_, v___y_347_);
lean_dec_ref_known(v___x_369_, 14);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_413_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v_traceState_381_; lean_object* v_env_382_; lean_object* v_nextMacroScope_383_; lean_object* v_ngen_384_; lean_object* v_auxDeclNGen_385_; lean_object* v_cache_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v___x_380_ = lean_st_ref_take(v___y_347_);
v_traceState_381_ = lean_ctor_get(v___x_380_, 4);
v_env_382_ = lean_ctor_get(v___x_380_, 0);
v_nextMacroScope_383_ = lean_ctor_get(v___x_380_, 1);
v_ngen_384_ = lean_ctor_get(v___x_380_, 2);
v_auxDeclNGen_385_ = lean_ctor_get(v___x_380_, 3);
v_cache_386_ = lean_ctor_get(v___x_380_, 5);
v_messages_387_ = lean_ctor_get(v___x_380_, 6);
v_infoState_388_ = lean_ctor_get(v___x_380_, 7);
v_snapshotTasks_389_ = lean_ctor_get(v___x_380_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v___x_380_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_cache_386_);
lean_inc(v_traceState_381_);
lean_inc(v_auxDeclNGen_385_);
lean_inc(v_ngen_384_);
lean_inc(v_nextMacroScope_383_);
lean_inc(v_env_382_);
lean_dec(v___x_380_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_381_, sizeof(void*)*1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_381_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_traceState_381_, 0);
lean_dec(v_unused_411_);
v___x_395_ = v_traceState_381_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_traceState_381_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_ref_342_);
lean_ctor_set(v___x_397_, 1, v_a_376_);
v___x_398_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_340_, v___x_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_398_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_393_);
v___x_400_ = v_reuseFailAlloc_409_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_400_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_snapshotTasks_389_);
v___x_402_ = v_reuseFailAlloc_408_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_set(v___y_347_, v___x_402_);
v___x_404_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_404_);
v___x_406_ = v___x_378_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_414_, lean_object* v_data_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_414_, v_data_415_, v_ref_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_424_){
_start:
{
if (lean_obj_tag(v_e_424_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 2;
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_427_);
lean_dec_ref(v_e_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_430_, lean_object* v_opt_431_){
_start:
{
lean_object* v_name_432_; lean_object* v_defValue_433_; lean_object* v_map_434_; lean_object* v___x_435_; 
v_name_432_ = lean_ctor_get(v_opt_431_, 0);
v_defValue_433_ = lean_ctor_get(v_opt_431_, 1);
v_map_434_ = lean_ctor_get(v_opts_430_, 0);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_434_, v_name_432_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
if (lean_obj_tag(v_val_436_) == 3)
{
lean_object* v_v_437_; 
v_v_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc(v_v_437_);
lean_dec_ref_known(v_val_436_, 1);
return v_v_437_;
}
else
{
lean_dec(v_val_436_);
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_438_, lean_object* v_opt_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_438_, v_opt_439_);
lean_dec_ref(v_opt_439_);
lean_dec_ref(v_opts_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v_x_441_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v_x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v_x_441_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 0);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_459_);
return v_res_461_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_462_; double v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_float_of_nat(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1000u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_469_, uint8_t v_collapsed_470_, lean_object* v_tag_471_, lean_object* v_opts_472_, uint8_t v_clsEnabled_473_, lean_object* v_oldTraces_474_, lean_object* v_msg_475_, lean_object* v_resStartStop_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v_data_487_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___y_503_; lean_object* v_a_504_; uint8_t v___y_519_; double v___y_550_; 
v_fst_482_ = lean_ctor_get(v_resStartStop_476_, 0);
lean_inc(v_fst_482_);
v_snd_483_ = lean_ctor_get(v_resStartStop_476_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v_resStartStop_476_);
v_fst_498_ = lean_ctor_get(v_snd_483_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_snd_483_, 1);
lean_inc(v_snd_499_);
lean_dec(v_snd_483_);
v___x_500_ = l_Lean_trace_profiler;
v___x_501_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_519_ = v___x_501_;
goto v___jp_518_;
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = l_Lean_trace_profiler_useHeartbeats;
v___x_556_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; double v___x_559_; double v___x_560_; double v___x_561_; 
v___x_557_ = l_Lean_trace_profiler_threshold;
v___x_558_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_557_);
v___x_559_ = lean_float_of_nat(v___x_558_);
v___x_560_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_561_ = lean_float_div(v___x_559_, v___x_560_);
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; double v___x_564_; 
v___x_562_ = l_Lean_trace_profiler_threshold;
v___x_563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_562_);
v___x_564_ = lean_float_of_nat(v___x_563_);
v___y_550_ = v___x_564_;
goto v___jp_549_;
}
}
v___jp_484_:
{
lean_object* v___x_488_; 
lean_inc(v___y_486_);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_474_, v_data_487_, v___y_486_, v___y_485_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
lean_dec_ref_known(v___x_488_, 1);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_fst_482_);
v_a_490_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_488_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
v___jp_502_:
{
uint8_t v_result_505_; lean_object* v___x_506_; lean_object* v___x_507_; double v___x_508_; lean_object* v_data_509_; 
v_result_505_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_482_);
v___x_506_ = lean_box(v_result_505_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
v___x_508_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_471_);
lean_inc_ref(v___x_507_);
lean_inc(v_cls_469_);
v_data_509_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_509_, 0, v_cls_469_);
lean_ctor_set(v_data_509_, 1, v___x_507_);
lean_ctor_set(v_data_509_, 2, v_tag_471_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3, v___x_508_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3 + 8, v___x_508_);
lean_ctor_set_uint8(v_data_509_, sizeof(void*)*3 + 16, v_collapsed_470_);
if (v___x_501_ == 0)
{
lean_dec_ref_known(v___x_507_, 1);
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_509_;
goto v___jp_484_;
}
else
{
lean_object* v_data_510_; double v___x_511_; double v___x_512_; 
lean_dec_ref_known(v_data_509_, 3);
v_data_510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_510_, 0, v_cls_469_);
lean_ctor_set(v_data_510_, 1, v___x_507_);
lean_ctor_set(v_data_510_, 2, v_tag_471_);
v___x_511_ = lean_unbox_float(v_fst_498_);
lean_dec(v_fst_498_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3, v___x_511_);
v___x_512_ = lean_unbox_float(v_snd_499_);
lean_dec(v_snd_499_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3 + 8, v___x_512_);
lean_ctor_set_uint8(v_data_510_, sizeof(void*)*3 + 16, v_collapsed_470_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_510_;
goto v___jp_484_;
}
}
v___jp_513_:
{
lean_object* v_ref_514_; lean_object* v___x_515_; 
v_ref_514_ = lean_ctor_get(v___y_479_, 5);
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v_fst_482_);
v___x_515_ = lean_apply_6(v_msg_475_, v_fst_482_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, lean_box(0));
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___y_503_ = v_ref_514_;
v_a_504_ = v_a_516_;
goto v___jp_502_;
}
else
{
lean_object* v___x_517_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_503_ = v_ref_514_;
v_a_504_ = v___x_517_;
goto v___jp_502_;
}
}
v___jp_518_:
{
if (v_clsEnabled_473_ == 0)
{
if (v___y_519_ == 0)
{
lean_object* v___x_520_; lean_object* v_traceState_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_cache_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_msg_475_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___x_520_ = lean_st_ref_take(v___y_480_);
v_traceState_521_ = lean_ctor_get(v___x_520_, 4);
v_env_522_ = lean_ctor_get(v___x_520_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_520_, 1);
v_ngen_524_ = lean_ctor_get(v___x_520_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_520_, 3);
v_cache_526_ = lean_ctor_get(v___x_520_, 5);
v_messages_527_ = lean_ctor_get(v___x_520_, 6);
v_infoState_528_ = lean_ctor_get(v___x_520_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_520_, 8);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_548_ == 0)
{
v___x_531_ = v___x_520_;
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_520_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint64_t v_tid_533_; lean_object* v_traces_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_547_; 
v_tid_533_ = lean_ctor_get_uint64(v_traceState_521_, sizeof(void*)*1);
v_traces_534_ = lean_ctor_get(v_traceState_521_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_traceState_521_);
if (v_isSharedCheck_547_ == 0)
{
v___x_536_ = v_traceState_521_;
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_traces_534_);
lean_dec(v_traceState_521_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_474_, v_traces_534_);
lean_dec_ref(v_traces_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_538_);
lean_ctor_set_uint64(v_reuseFailAlloc_546_, sizeof(void*)*1, v_tid_533_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v___x_540_);
v___x_542_ = v___x_531_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_snapshotTasks_529_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_set(v___y_480_, v___x_542_);
v___x_544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_544_;
}
}
}
}
}
else
{
goto v___jp_513_;
}
}
else
{
goto v___jp_513_;
}
}
v___jp_549_:
{
double v___x_551_; double v___x_552_; double v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_unbox_float(v_snd_499_);
v___x_552_ = lean_unbox_float(v_fst_498_);
v___x_553_ = lean_float_sub(v___x_551_, v___x_552_);
v___x_554_ = lean_float_decLt(v___y_550_, v___x_553_);
v___y_519_ = v___x_554_;
goto v___jp_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_565_, lean_object* v_collapsed_566_, lean_object* v_tag_567_, lean_object* v_opts_568_, lean_object* v_clsEnabled_569_, lean_object* v_oldTraces_570_, lean_object* v_msg_571_, lean_object* v_resStartStop_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_collapsed_boxed_578_; uint8_t v_clsEnabled_boxed_579_; lean_object* v_res_580_; 
v_collapsed_boxed_578_ = lean_unbox(v_collapsed_566_);
v_clsEnabled_boxed_579_ = lean_unbox(v_clsEnabled_569_);
v_res_580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_565_, v_collapsed_boxed_578_, v_tag_567_, v_opts_568_, v_clsEnabled_boxed_579_, v_oldTraces_570_, v_msg_571_, v_resStartStop_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_opts_568_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_x_583_);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_head_590_ = lean_ctor_get(v_x_582_, 0);
v_tail_591_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v_x_582_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v_head_590_);
v___x_595_ = l_Lean_MVarId_inferInstance(v_head_590_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_dec_ref_known(v___x_595_, 1);
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_613_; 
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_613_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___y_602_; uint8_t v___x_611_; 
v___x_611_ = l_Lean_Exception_isInterrupt(v_a_597_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
lean_inc(v_a_597_);
v___x_612_ = l_Lean_Exception_isRuntime(v_a_597_);
v___y_602_ = v___x_612_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
if (v___x_581_ == 0)
{
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_x_583_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_head_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_x_583_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_x_582_ = v_tail_591_;
v_x_583_ = v___x_605_;
goto _start;
}
}
}
else
{
lean_object* v___x_609_; 
lean_del_object(v___x_593_);
lean_dec(v_tail_591_);
lean_dec(v_head_590_);
lean_dec(v_x_583_);
if (v_isShared_600_ == 0)
{
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_597_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_14576__boxed_623_; lean_object* v_res_624_; 
v___x_14576__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14576__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_x_627_);
return v___x_633_;
}
else
{
lean_object* v_head_634_; lean_object* v_tail_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_658_; 
v_head_634_ = lean_ctor_get(v_x_626_, 0);
v_tail_635_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_637_ = v_x_626_;
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_tail_635_);
lean_inc(v_head_634_);
lean_dec(v_x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_644_; 
lean_inc(v_head_634_);
v___x_644_ = l_Lean_MVarId_inferInstance(v_head_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
if (v___x_625_ == 0)
{
lean_del_object(v___x_637_);
lean_dec(v_head_634_);
v_x_626_ = v_tail_635_;
goto _start;
}
else
{
goto v___jp_639_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___y_651_; uint8_t v___x_655_; 
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_646_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v_a_646_);
v___x_656_ = l_Lean_Exception_isRuntime(v_a_646_);
v___y_651_ = v___x_656_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___x_655_;
goto v___jp_650_;
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
lean_del_object(v___x_648_);
lean_dec(v_a_646_);
goto v___jp_639_;
}
else
{
lean_object* v___x_653_; 
lean_del_object(v___x_637_);
lean_dec(v_tail_635_);
lean_dec(v_head_634_);
lean_dec(v_x_627_);
if (v_isShared_649_ == 0)
{
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_646_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_627_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_head_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_x_627_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_x_626_ = v_tail_635_;
v_x_627_ = v___x_641_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_14653__boxed_667_; lean_object* v_res_668_; 
v___x_14653__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14653__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_668_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_672_; double v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1000000000u);
v___x_673_ = lean_float_of_nat(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_674_, lean_object* v_g_675_, lean_object* v_e_676_, lean_object* v_cfg_677_, lean_object* v___x_678_, lean_object* v___x_679_, uint8_t v___x_680_, lean_object* v___x_681_, lean_object* v___f_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_options_688_; uint8_t v_hasTrace_689_; 
v_options_688_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_689_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
if (v_hasTrace_689_ == 0)
{
lean_object* v___x_690_; uint8_t v_foApprox_691_; uint8_t v_ctxApprox_692_; uint8_t v_quasiPatternApprox_693_; uint8_t v_constApprox_694_; uint8_t v_isDefEqStuckEx_695_; uint8_t v_unificationHints_696_; uint8_t v_proofIrrelevance_697_; uint8_t v_assignSyntheticOpaque_698_; uint8_t v_offsetCnstrs_699_; uint8_t v_etaStruct_700_; uint8_t v_univApprox_701_; uint8_t v_iota_702_; uint8_t v_beta_703_; uint8_t v_proj_704_; uint8_t v_zeta_705_; uint8_t v_zetaDelta_706_; uint8_t v_zetaUnused_707_; uint8_t v_zetaHave_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_690_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_691_ = lean_ctor_get_uint8(v___x_690_, 0);
v_ctxApprox_692_ = lean_ctor_get_uint8(v___x_690_, 1);
v_quasiPatternApprox_693_ = lean_ctor_get_uint8(v___x_690_, 2);
v_constApprox_694_ = lean_ctor_get_uint8(v___x_690_, 3);
v_isDefEqStuckEx_695_ = lean_ctor_get_uint8(v___x_690_, 4);
v_unificationHints_696_ = lean_ctor_get_uint8(v___x_690_, 5);
v_proofIrrelevance_697_ = lean_ctor_get_uint8(v___x_690_, 6);
v_assignSyntheticOpaque_698_ = lean_ctor_get_uint8(v___x_690_, 7);
v_offsetCnstrs_699_ = lean_ctor_get_uint8(v___x_690_, 8);
v_etaStruct_700_ = lean_ctor_get_uint8(v___x_690_, 10);
v_univApprox_701_ = lean_ctor_get_uint8(v___x_690_, 11);
v_iota_702_ = lean_ctor_get_uint8(v___x_690_, 12);
v_beta_703_ = lean_ctor_get_uint8(v___x_690_, 13);
v_proj_704_ = lean_ctor_get_uint8(v___x_690_, 14);
v_zeta_705_ = lean_ctor_get_uint8(v___x_690_, 15);
v_zetaDelta_706_ = lean_ctor_get_uint8(v___x_690_, 16);
v_zetaUnused_707_ = lean_ctor_get_uint8(v___x_690_, 17);
v_zetaHave_708_ = lean_ctor_get_uint8(v___x_690_, 18);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_746_ == 0)
{
v___x_710_ = v___x_690_;
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_690_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_746_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v_trackZetaDelta_712_; lean_object* v_zetaDeltaSet_713_; lean_object* v_lctx_714_; lean_object* v_localInstances_715_; lean_object* v_defEqCtx_x3f_716_; lean_object* v_synthPendingDepth_717_; lean_object* v_canUnfold_x3f_718_; uint8_t v_univApprox_719_; uint8_t v_inTypeClassResolution_720_; uint8_t v_cacheInferType_721_; lean_object* v_config_723_; 
v_trackZetaDelta_712_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_713_ = lean_ctor_get(v___y_683_, 1);
v_lctx_714_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_715_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_716_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_717_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_718_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_719_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_720_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_721_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_711_ == 0)
{
v_config_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 0, v_foApprox_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 1, v_ctxApprox_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 2, v_quasiPatternApprox_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 3, v_constApprox_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 4, v_isDefEqStuckEx_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 5, v_unificationHints_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 6, v_proofIrrelevance_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 7, v_assignSyntheticOpaque_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 8, v_offsetCnstrs_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 10, v_etaStruct_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 11, v_univApprox_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 12, v_iota_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 13, v_beta_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 14, v_proj_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 15, v_zeta_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 16, v_zetaDelta_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 17, v_zetaUnused_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, 18, v_zetaHave_708_);
v_config_723_ = v_reuseFailAlloc_745_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_key_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_ctor_set_uint8(v_config_723_, 9, v_transparency_674_);
v___x_724_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_725_ = 3ULL;
v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
v___x_727_ = lean_uint64_shift_left(v___x_726_, v___x_725_);
v___x_728_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_729_ = lean_uint64_lor(v___x_727_, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_730_, 0, v_config_723_);
lean_ctor_set_uint64(v___x_730_, sizeof(void*)*1, v_key_729_);
lean_inc(v_canUnfold_x3f_718_);
lean_inc(v_synthPendingDepth_717_);
lean_inc(v_defEqCtx_x3f_716_);
lean_inc_ref(v_localInstances_715_);
lean_inc_ref(v_lctx_714_);
lean_inc(v_zetaDeltaSet_713_);
v___x_731_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_zetaDeltaSet_713_);
lean_ctor_set(v___x_731_, 2, v_lctx_714_);
lean_ctor_set(v___x_731_, 3, v_localInstances_715_);
lean_ctor_set(v___x_731_, 4, v_defEqCtx_x3f_716_);
lean_ctor_set(v___x_731_, 5, v_synthPendingDepth_717_);
lean_ctor_set(v___x_731_, 6, v_canUnfold_x3f_718_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7, v_trackZetaDelta_712_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 1, v_univApprox_719_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 2, v_inTypeClassResolution_720_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*7 + 3, v_cacheInferType_721_);
v___x_732_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_731_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_731_, 7);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = lean_box(0);
v___x_735_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_689_, v_a_733_, v___x_734_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_744_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_744_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_740_ = l_List_reverse___redArg(v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
return v___x_735_;
}
}
else
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_a_754_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v_a_769_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_a_787_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v_a_799_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; 
v_inheritedTraceOptions_747_ = lean_ctor_get(v___y_685_, 13);
v___x_748_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_679_);
v___x_749_ = l_Lean_Name_append(v___x_748_, v___x_679_);
v___x_750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_747_, v_options_688_, v___x_749_);
lean_dec(v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = l_Lean_trace_profiler;
v___x_922_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; uint8_t v_foApprox_924_; uint8_t v_ctxApprox_925_; uint8_t v_quasiPatternApprox_926_; uint8_t v_constApprox_927_; uint8_t v_isDefEqStuckEx_928_; uint8_t v_unificationHints_929_; uint8_t v_proofIrrelevance_930_; uint8_t v_assignSyntheticOpaque_931_; uint8_t v_offsetCnstrs_932_; uint8_t v_etaStruct_933_; uint8_t v_univApprox_934_; uint8_t v_iota_935_; uint8_t v_beta_936_; uint8_t v_proj_937_; uint8_t v_zeta_938_; uint8_t v_zetaDelta_939_; uint8_t v_zetaUnused_940_; uint8_t v_zetaHave_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v___x_923_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_924_ = lean_ctor_get_uint8(v___x_923_, 0);
v_ctxApprox_925_ = lean_ctor_get_uint8(v___x_923_, 1);
v_quasiPatternApprox_926_ = lean_ctor_get_uint8(v___x_923_, 2);
v_constApprox_927_ = lean_ctor_get_uint8(v___x_923_, 3);
v_isDefEqStuckEx_928_ = lean_ctor_get_uint8(v___x_923_, 4);
v_unificationHints_929_ = lean_ctor_get_uint8(v___x_923_, 5);
v_proofIrrelevance_930_ = lean_ctor_get_uint8(v___x_923_, 6);
v_assignSyntheticOpaque_931_ = lean_ctor_get_uint8(v___x_923_, 7);
v_offsetCnstrs_932_ = lean_ctor_get_uint8(v___x_923_, 8);
v_etaStruct_933_ = lean_ctor_get_uint8(v___x_923_, 10);
v_univApprox_934_ = lean_ctor_get_uint8(v___x_923_, 11);
v_iota_935_ = lean_ctor_get_uint8(v___x_923_, 12);
v_beta_936_ = lean_ctor_get_uint8(v___x_923_, 13);
v_proj_937_ = lean_ctor_get_uint8(v___x_923_, 14);
v_zeta_938_ = lean_ctor_get_uint8(v___x_923_, 15);
v_zetaDelta_939_ = lean_ctor_get_uint8(v___x_923_, 16);
v_zetaUnused_940_ = lean_ctor_get_uint8(v___x_923_, 17);
v_zetaHave_941_ = lean_ctor_get_uint8(v___x_923_, 18);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_979_ == 0)
{
v___x_943_ = v___x_923_;
v_isShared_944_ = v_isSharedCheck_979_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_923_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_979_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v_trackZetaDelta_945_; lean_object* v_zetaDeltaSet_946_; lean_object* v_lctx_947_; lean_object* v_localInstances_948_; lean_object* v_defEqCtx_x3f_949_; lean_object* v_synthPendingDepth_950_; lean_object* v_canUnfold_x3f_951_; uint8_t v_univApprox_952_; uint8_t v_inTypeClassResolution_953_; uint8_t v_cacheInferType_954_; lean_object* v_config_956_; 
v_trackZetaDelta_945_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_946_ = lean_ctor_get(v___y_683_, 1);
v_lctx_947_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_948_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_949_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_950_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_951_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_952_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_953_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_954_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_944_ == 0)
{
v_config_956_ = v___x_943_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 0, v_foApprox_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 1, v_ctxApprox_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 2, v_quasiPatternApprox_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 3, v_constApprox_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 4, v_isDefEqStuckEx_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 5, v_unificationHints_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 6, v_proofIrrelevance_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 7, v_assignSyntheticOpaque_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 8, v_offsetCnstrs_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 10, v_etaStruct_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 11, v_univApprox_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 12, v_iota_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 13, v_beta_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 14, v_proj_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 15, v_zeta_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 16, v_zetaDelta_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 17, v_zetaUnused_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, 18, v_zetaHave_941_);
v_config_956_ = v_reuseFailAlloc_978_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v_key_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_ctor_set_uint8(v_config_956_, 9, v_transparency_674_);
v___x_957_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_958_ = 3ULL;
v___x_959_ = lean_uint64_shift_right(v___x_957_, v___x_958_);
v___x_960_ = lean_uint64_shift_left(v___x_959_, v___x_958_);
v___x_961_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_962_ = lean_uint64_lor(v___x_960_, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_963_, 0, v_config_956_);
lean_ctor_set_uint64(v___x_963_, sizeof(void*)*1, v_key_962_);
lean_inc(v_canUnfold_x3f_951_);
lean_inc(v_synthPendingDepth_950_);
lean_inc(v_defEqCtx_x3f_949_);
lean_inc_ref(v_localInstances_948_);
lean_inc_ref(v_lctx_947_);
lean_inc(v_zetaDeltaSet_946_);
v___x_964_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_zetaDeltaSet_946_);
lean_ctor_set(v___x_964_, 2, v_lctx_947_);
lean_ctor_set(v___x_964_, 3, v_localInstances_948_);
lean_ctor_set(v___x_964_, 4, v_defEqCtx_x3f_949_);
lean_ctor_set(v___x_964_, 5, v_synthPendingDepth_950_);
lean_ctor_set(v___x_964_, 6, v_canUnfold_x3f_951_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7, v_trackZetaDelta_945_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 1, v_univApprox_952_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 2, v_inTypeClassResolution_953_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*7 + 3, v_cacheInferType_954_);
v___x_965_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_964_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_964_, 7);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = lean_box(0);
v___x_968_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_922_, v_hasTrace_689_, v_a_966_, v___x_967_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = l_List_reverse___redArg(v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
return v___x_968_;
}
}
else
{
return v___x_965_;
}
}
}
}
else
{
goto v___jp_814_;
}
}
else
{
goto v___jp_814_;
}
v___jp_751_:
{
lean_object* v___x_755_; double v___x_756_; double v___x_757_; double v___x_758_; double v___x_759_; double v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_755_ = lean_io_mono_nanos_now();
v___x_756_ = lean_float_of_nat(v___y_753_);
v___x_757_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_758_ = lean_float_div(v___x_756_, v___x_757_);
v___x_759_ = lean_float_of_nat(v___x_755_);
v___x_760_ = lean_float_div(v___x_759_, v___x_757_);
v___x_761_ = lean_box_float(v___x_758_);
v___x_762_ = lean_box_float(v___x_760_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_a_754_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_750_, v___y_752_, v___f_682_, v___x_764_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_765_;
}
v___jp_766_:
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_a_769_);
v___y_752_ = v___y_768_;
v___y_753_ = v___y_767_;
v_a_754_ = v___x_770_;
goto v___jp_751_;
}
v___jp_771_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___y_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___y_774_, 1);
v___y_767_ = v___y_773_;
v___y_768_ = v___y_772_;
v_a_769_ = v_a_775_;
goto v___jp_766_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___y_774_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___y_774_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___y_774_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___y_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 0);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_752_ = v___y_772_;
v___y_753_ = v___y_773_;
v_a_754_ = v___x_781_;
goto v___jp_751_;
}
}
}
}
v___jp_784_:
{
lean_object* v___x_788_; double v___x_789_; double v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_788_ = lean_io_get_num_heartbeats();
v___x_789_ = lean_float_of_nat(v___y_785_);
v___x_790_ = lean_float_of_nat(v___x_788_);
v___x_791_ = lean_box_float(v___x_789_);
v___x_792_ = lean_box_float(v___x_790_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_a_787_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_750_, v___y_786_, v___f_682_, v___x_794_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_795_;
}
v___jp_796_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v_a_799_);
v___y_785_ = v___y_797_;
v___y_786_ = v___y_798_;
v_a_787_ = v___x_800_;
goto v___jp_784_;
}
v___jp_801_:
{
if (lean_obj_tag(v___y_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___y_804_, 1);
v___y_797_ = v___y_802_;
v___y_798_ = v___y_803_;
v_a_799_ = v_a_805_;
goto v___jp_796_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___y_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___y_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___y_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___y_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_785_ = v___y_802_;
v___y_786_ = v___y_803_;
v_a_787_ = v___x_811_;
goto v___jp_784_;
}
}
}
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_818_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v_foApprox_821_; uint8_t v_ctxApprox_822_; uint8_t v_quasiPatternApprox_823_; uint8_t v_constApprox_824_; uint8_t v_isDefEqStuckEx_825_; uint8_t v_unificationHints_826_; uint8_t v_proofIrrelevance_827_; uint8_t v_assignSyntheticOpaque_828_; uint8_t v_offsetCnstrs_829_; uint8_t v_etaStruct_830_; uint8_t v_univApprox_831_; uint8_t v_iota_832_; uint8_t v_beta_833_; uint8_t v_proj_834_; uint8_t v_zeta_835_; uint8_t v_zetaDelta_836_; uint8_t v_zetaUnused_837_; uint8_t v_zetaHave_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_869_; 
v___x_819_ = lean_io_mono_nanos_now();
v___x_820_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_821_ = lean_ctor_get_uint8(v___x_820_, 0);
v_ctxApprox_822_ = lean_ctor_get_uint8(v___x_820_, 1);
v_quasiPatternApprox_823_ = lean_ctor_get_uint8(v___x_820_, 2);
v_constApprox_824_ = lean_ctor_get_uint8(v___x_820_, 3);
v_isDefEqStuckEx_825_ = lean_ctor_get_uint8(v___x_820_, 4);
v_unificationHints_826_ = lean_ctor_get_uint8(v___x_820_, 5);
v_proofIrrelevance_827_ = lean_ctor_get_uint8(v___x_820_, 6);
v_assignSyntheticOpaque_828_ = lean_ctor_get_uint8(v___x_820_, 7);
v_offsetCnstrs_829_ = lean_ctor_get_uint8(v___x_820_, 8);
v_etaStruct_830_ = lean_ctor_get_uint8(v___x_820_, 10);
v_univApprox_831_ = lean_ctor_get_uint8(v___x_820_, 11);
v_iota_832_ = lean_ctor_get_uint8(v___x_820_, 12);
v_beta_833_ = lean_ctor_get_uint8(v___x_820_, 13);
v_proj_834_ = lean_ctor_get_uint8(v___x_820_, 14);
v_zeta_835_ = lean_ctor_get_uint8(v___x_820_, 15);
v_zetaDelta_836_ = lean_ctor_get_uint8(v___x_820_, 16);
v_zetaUnused_837_ = lean_ctor_get_uint8(v___x_820_, 17);
v_zetaHave_838_ = lean_ctor_get_uint8(v___x_820_, 18);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_869_ == 0)
{
v___x_840_ = v___x_820_;
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
else
{
lean_dec(v___x_820_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v_trackZetaDelta_842_; lean_object* v_zetaDeltaSet_843_; lean_object* v_lctx_844_; lean_object* v_localInstances_845_; lean_object* v_defEqCtx_x3f_846_; lean_object* v_synthPendingDepth_847_; lean_object* v_canUnfold_x3f_848_; uint8_t v_univApprox_849_; uint8_t v_inTypeClassResolution_850_; uint8_t v_cacheInferType_851_; lean_object* v_config_853_; 
v_trackZetaDelta_842_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_843_ = lean_ctor_get(v___y_683_, 1);
v_lctx_844_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_845_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_846_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_847_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_848_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_849_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_850_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_851_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_841_ == 0)
{
v_config_853_ = v___x_840_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 0, v_foApprox_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 1, v_ctxApprox_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 2, v_quasiPatternApprox_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 3, v_constApprox_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 4, v_isDefEqStuckEx_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 5, v_unificationHints_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 6, v_proofIrrelevance_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 7, v_assignSyntheticOpaque_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 8, v_offsetCnstrs_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 10, v_etaStruct_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 11, v_univApprox_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 12, v_iota_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 13, v_beta_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 14, v_proj_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 15, v_zeta_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 16, v_zetaDelta_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 17, v_zetaUnused_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_868_, 18, v_zetaHave_838_);
v_config_853_ = v_reuseFailAlloc_868_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v_key_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_ctor_set_uint8(v_config_853_, 9, v_transparency_674_);
v___x_854_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_855_ = 3ULL;
v___x_856_ = lean_uint64_shift_right(v___x_854_, v___x_855_);
v___x_857_ = lean_uint64_shift_left(v___x_856_, v___x_855_);
v___x_858_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_859_ = lean_uint64_lor(v___x_857_, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_860_, 0, v_config_853_);
lean_ctor_set_uint64(v___x_860_, sizeof(void*)*1, v_key_859_);
lean_inc(v_canUnfold_x3f_848_);
lean_inc(v_synthPendingDepth_847_);
lean_inc(v_defEqCtx_x3f_846_);
lean_inc_ref(v_localInstances_845_);
lean_inc_ref(v_lctx_844_);
lean_inc(v_zetaDeltaSet_843_);
v___x_861_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_zetaDeltaSet_843_);
lean_ctor_set(v___x_861_, 2, v_lctx_844_);
lean_ctor_set(v___x_861_, 3, v_localInstances_845_);
lean_ctor_set(v___x_861_, 4, v_defEqCtx_x3f_846_);
lean_ctor_set(v___x_861_, 5, v_synthPendingDepth_847_);
lean_ctor_set(v___x_861_, 6, v_canUnfold_x3f_848_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7, v_trackZetaDelta_842_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 1, v_univApprox_849_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 2, v_inTypeClassResolution_850_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*7 + 3, v_cacheInferType_851_);
v___x_862_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_861_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_861_, 7);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_box(0);
v___x_865_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_818_, v_hasTrace_689_, v_a_863_, v___x_864_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = l_List_reverse___redArg(v_a_866_);
v___y_767_ = v___x_819_;
v___y_768_ = v_a_816_;
v_a_769_ = v___x_867_;
goto v___jp_766_;
}
else
{
v___y_772_ = v_a_816_;
v___y_773_ = v___x_819_;
v___y_774_ = v___x_865_;
goto v___jp_771_;
}
}
else
{
v___y_772_ = v_a_816_;
v___y_773_ = v___x_819_;
v___y_774_ = v___x_862_;
goto v___jp_771_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v_foApprox_872_; uint8_t v_ctxApprox_873_; uint8_t v_quasiPatternApprox_874_; uint8_t v_constApprox_875_; uint8_t v_isDefEqStuckEx_876_; uint8_t v_unificationHints_877_; uint8_t v_proofIrrelevance_878_; uint8_t v_assignSyntheticOpaque_879_; uint8_t v_offsetCnstrs_880_; uint8_t v_etaStruct_881_; uint8_t v_univApprox_882_; uint8_t v_iota_883_; uint8_t v_beta_884_; uint8_t v_proj_885_; uint8_t v_zeta_886_; uint8_t v_zetaDelta_887_; uint8_t v_zetaUnused_888_; uint8_t v_zetaHave_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_920_; 
v___x_870_ = lean_io_get_num_heartbeats();
v___x_871_ = l_Lean_Meta_Context_config(v___y_683_);
v_foApprox_872_ = lean_ctor_get_uint8(v___x_871_, 0);
v_ctxApprox_873_ = lean_ctor_get_uint8(v___x_871_, 1);
v_quasiPatternApprox_874_ = lean_ctor_get_uint8(v___x_871_, 2);
v_constApprox_875_ = lean_ctor_get_uint8(v___x_871_, 3);
v_isDefEqStuckEx_876_ = lean_ctor_get_uint8(v___x_871_, 4);
v_unificationHints_877_ = lean_ctor_get_uint8(v___x_871_, 5);
v_proofIrrelevance_878_ = lean_ctor_get_uint8(v___x_871_, 6);
v_assignSyntheticOpaque_879_ = lean_ctor_get_uint8(v___x_871_, 7);
v_offsetCnstrs_880_ = lean_ctor_get_uint8(v___x_871_, 8);
v_etaStruct_881_ = lean_ctor_get_uint8(v___x_871_, 10);
v_univApprox_882_ = lean_ctor_get_uint8(v___x_871_, 11);
v_iota_883_ = lean_ctor_get_uint8(v___x_871_, 12);
v_beta_884_ = lean_ctor_get_uint8(v___x_871_, 13);
v_proj_885_ = lean_ctor_get_uint8(v___x_871_, 14);
v_zeta_886_ = lean_ctor_get_uint8(v___x_871_, 15);
v_zetaDelta_887_ = lean_ctor_get_uint8(v___x_871_, 16);
v_zetaUnused_888_ = lean_ctor_get_uint8(v___x_871_, 17);
v_zetaHave_889_ = lean_ctor_get_uint8(v___x_871_, 18);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_920_ == 0)
{
v___x_891_ = v___x_871_;
v_isShared_892_ = v_isSharedCheck_920_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_871_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_920_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v_trackZetaDelta_893_; lean_object* v_zetaDeltaSet_894_; lean_object* v_lctx_895_; lean_object* v_localInstances_896_; lean_object* v_defEqCtx_x3f_897_; lean_object* v_synthPendingDepth_898_; lean_object* v_canUnfold_x3f_899_; uint8_t v_univApprox_900_; uint8_t v_inTypeClassResolution_901_; uint8_t v_cacheInferType_902_; lean_object* v_config_904_; 
v_trackZetaDelta_893_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_894_ = lean_ctor_get(v___y_683_, 1);
v_lctx_895_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_896_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_897_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_898_ = lean_ctor_get(v___y_683_, 5);
v_canUnfold_x3f_899_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_900_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_901_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_902_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
if (v_isShared_892_ == 0)
{
v_config_904_ = v___x_891_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 0, v_foApprox_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 1, v_ctxApprox_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 2, v_quasiPatternApprox_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 3, v_constApprox_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 4, v_isDefEqStuckEx_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 5, v_unificationHints_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 6, v_proofIrrelevance_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 7, v_assignSyntheticOpaque_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 8, v_offsetCnstrs_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 10, v_etaStruct_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 11, v_univApprox_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 12, v_iota_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 13, v_beta_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 14, v_proj_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 15, v_zeta_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 16, v_zetaDelta_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 17, v_zetaUnused_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, 18, v_zetaHave_889_);
v_config_904_ = v_reuseFailAlloc_919_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_key_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_ctor_set_uint8(v_config_904_, 9, v_transparency_674_);
v___x_905_ = l_Lean_Meta_Context_configKey(v___y_683_);
v___x_906_ = 3ULL;
v___x_907_ = lean_uint64_shift_right(v___x_905_, v___x_906_);
v___x_908_ = lean_uint64_shift_left(v___x_907_, v___x_906_);
v___x_909_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_674_);
v_key_910_ = lean_uint64_lor(v___x_908_, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_911_, 0, v_config_904_);
lean_ctor_set_uint64(v___x_911_, sizeof(void*)*1, v_key_910_);
lean_inc(v_canUnfold_x3f_899_);
lean_inc(v_synthPendingDepth_898_);
lean_inc(v_defEqCtx_x3f_897_);
lean_inc_ref(v_localInstances_896_);
lean_inc_ref(v_lctx_895_);
lean_inc(v_zetaDeltaSet_894_);
v___x_912_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_zetaDeltaSet_894_);
lean_ctor_set(v___x_912_, 2, v_lctx_895_);
lean_ctor_set(v___x_912_, 3, v_localInstances_896_);
lean_ctor_set(v___x_912_, 4, v_defEqCtx_x3f_897_);
lean_ctor_set(v___x_912_, 5, v_synthPendingDepth_898_);
lean_ctor_set(v___x_912_, 6, v_canUnfold_x3f_899_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7, v_trackZetaDelta_893_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 1, v_univApprox_900_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 2, v_inTypeClassResolution_901_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*7 + 3, v_cacheInferType_902_);
v___x_913_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_912_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_912_, 7);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_box(0);
v___x_916_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_818_, v_a_914_, v___x_915_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_List_reverse___redArg(v_a_917_);
v___y_797_ = v___x_870_;
v___y_798_ = v_a_816_;
v_a_799_ = v___x_918_;
goto v___jp_796_;
}
else
{
v___y_802_ = v___x_870_;
v___y_803_ = v_a_816_;
v___y_804_ = v___x_916_;
goto v___jp_801_;
}
}
else
{
v___y_802_ = v___x_870_;
v___y_803_ = v_a_816_;
v___y_804_ = v___x_913_;
goto v___jp_801_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_980_, lean_object* v_g_981_, lean_object* v_e_982_, lean_object* v_cfg_983_, lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v___f_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v_transparency_boxed_994_; uint8_t v___x_14741__boxed_995_; lean_object* v_res_996_; 
v_transparency_boxed_994_ = lean_unbox(v_transparency_980_);
v___x_14741__boxed_995_ = lean_unbox(v___x_986_);
v_res_996_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_994_, v_g_981_, v_e_982_, v_cfg_983_, v___x_984_, v___x_985_, v___x_14741__boxed_995_, v___x_987_, v___f_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_998_, lean_object* v_g_999_, lean_object* v_cfg_1000_, lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
lean_inc_ref(v_e_1001_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1007_, 0, v_e_1001_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1009_ = lean_box(0);
v___x_1010_ = 1;
v___x_1011_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1012_ = lean_box(v_transparency_998_);
v___x_1013_ = lean_box(v___x_1010_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1014_, 0, v___x_1012_);
lean_closure_set(v___f_1014_, 1, v_g_999_);
lean_closure_set(v___f_1014_, 2, v_e_1001_);
lean_closure_set(v___f_1014_, 3, v_cfg_1000_);
lean_closure_set(v___f_1014_, 4, v___x_1009_);
lean_closure_set(v___f_1014_, 5, v___x_1008_);
lean_closure_set(v___f_1014_, 6, v___x_1013_);
lean_closure_set(v___f_1014_, 7, v___x_1011_);
lean_closure_set(v___f_1014_, 8, v___f_1007_);
v___x_1015_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1014_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1016_, lean_object* v_g_1017_, lean_object* v_cfg_1018_, lean_object* v_e_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v_transparency_boxed_1025_; lean_object* v_res_1026_; 
v_transparency_boxed_1025_ = lean_unbox(v_transparency_1016_);
v_res_1026_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1025_, v_g_1017_, v_cfg_1018_, v_e_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1027_, uint8_t v_transparency_1028_, lean_object* v_lemmas_1029_, lean_object* v_g_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1029_, v_a_1031_, v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1039_ = lean_box(v_transparency_1028_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1040_, 0, v___x_1039_);
lean_closure_set(v___f_1040_, 1, v_g_1030_);
lean_closure_set(v___f_1040_, 2, v_cfg_1027_);
v___x_1041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1041_, 0, lean_box(0));
lean_closure_set(v___x_1041_, 1, lean_box(0));
lean_closure_set(v___x_1041_, 2, v___f_1040_);
lean_closure_set(v___x_1041_, 3, v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1041_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_g_1030_);
lean_dec_ref(v_cfg_1027_);
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1054_, lean_object* v_transparency_1055_, lean_object* v_lemmas_1056_, lean_object* v_g_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v_transparency_boxed_1061_; lean_object* v_res_1062_; 
v_transparency_boxed_1061_ = lean_unbox(v_transparency_1055_);
v_res_1062_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1054_, v_transparency_boxed_1061_, v_lemmas_1056_, v_g_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec(v_a_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1063_, uint8_t v_transparency_1064_, lean_object* v_lemmas_1065_, lean_object* v_g_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1063_, v_transparency_1064_, v_lemmas_1065_, v_g_1066_, v_a_1068_, v_a_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1073_, lean_object* v_transparency_1074_, lean_object* v_lemmas_1075_, lean_object* v_g_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v_transparency_boxed_1082_; lean_object* v_res_1083_; 
v_transparency_boxed_1082_ = lean_unbox(v_transparency_1074_);
v_res_1083_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1073_, v_transparency_boxed_1082_, v_lemmas_1075_, v_g_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_1084_, lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_1085_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_1092_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1100_, uint8_t v_transparency_1101_, lean_object* v_lemmas_1102_, lean_object* v_g_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1100_, v_transparency_1101_, v_lemmas_1102_, v_g_1103_, v_a_1105_, v_a_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = l_Lean_Meta_Iterator_head___redArg(v_a_1110_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1109_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1120_, lean_object* v_transparency_1121_, lean_object* v_lemmas_1122_, lean_object* v_g_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_transparency_boxed_1129_; lean_object* v_res_1130_; 
v_transparency_boxed_1129_ = lean_unbox(v_transparency_1121_);
v_res_1130_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1120_, v_transparency_boxed_1129_, v_lemmas_1122_, v_g_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1131_){
_start:
{
lean_object* v_toApplyRulesConfig_1132_; lean_object* v_toBacktrackConfig_1133_; 
v_toApplyRulesConfig_1132_ = lean_ctor_get(v_x_1131_, 0);
v_toBacktrackConfig_1133_ = lean_ctor_get(v_toApplyRulesConfig_1132_, 0);
lean_inc_ref(v_toBacktrackConfig_1133_);
return v_toBacktrackConfig_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1134_);
lean_dec_ref(v_x_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1138_, lean_object* v_discharge_1139_, lean_object* v_g_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v_g_1140_);
v___x_1146_ = lean_apply_6(v_test_1138_, v_g_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1157_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1157_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_del_object(v___x_1149_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
v___x_1152_ = lean_apply_6(v_discharge_1139_, v_g_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v_g_1140_);
lean_dec_ref(v_discharge_1139_);
v___x_1153_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1153_);
v___x_1155_ = v___x_1149_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
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
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_g_1140_);
lean_dec_ref(v_discharge_1139_);
v_a_1158_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1146_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1146_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1166_, lean_object* v_discharge_1167_, lean_object* v_g_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1166_, v_discharge_1167_, v_g_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1175_, lean_object* v_test_1176_){
_start:
{
lean_object* v_toApplyRulesConfig_1177_; lean_object* v_toBacktrackConfig_1178_; uint8_t v_backtracking_1179_; uint8_t v_intro_1180_; uint8_t v_constructor_1181_; uint8_t v_suggestions_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1214_; 
v_toApplyRulesConfig_1177_ = lean_ctor_get(v_cfg_1175_, 0);
lean_inc_ref(v_toApplyRulesConfig_1177_);
v_toBacktrackConfig_1178_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 0);
lean_inc_ref(v_toBacktrackConfig_1178_);
v_backtracking_1179_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1);
v_intro_1180_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 1);
v_constructor_1181_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 2);
v_suggestions_1182_ = lean_ctor_get_uint8(v_cfg_1175_, sizeof(void*)*1 + 3);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_cfg_1175_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_cfg_1175_, 0);
lean_dec(v_unused_1215_);
v___x_1184_ = v_cfg_1175_;
v_isShared_1185_ = v_isSharedCheck_1214_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_cfg_1175_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1214_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_toApplyConfig_1186_; uint8_t v_transparency_1187_; uint8_t v_symm_1188_; uint8_t v_exfalso_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1212_; 
v_toApplyConfig_1186_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 1);
v_transparency_1187_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2);
v_symm_1188_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2 + 1);
v_exfalso_1189_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1177_, sizeof(void*)*2 + 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_toApplyRulesConfig_1177_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_toApplyRulesConfig_1177_, 0);
lean_dec(v_unused_1213_);
v___x_1191_ = v_toApplyRulesConfig_1177_;
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_toApplyConfig_1186_);
lean_dec(v_toApplyRulesConfig_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_maxDepth_1193_; lean_object* v_proc_1194_; lean_object* v_suspend_1195_; lean_object* v_discharge_1196_; uint8_t v_commitIndependentGoals_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1211_; 
v_maxDepth_1193_ = lean_ctor_get(v_toBacktrackConfig_1178_, 0);
v_proc_1194_ = lean_ctor_get(v_toBacktrackConfig_1178_, 1);
v_suspend_1195_ = lean_ctor_get(v_toBacktrackConfig_1178_, 2);
v_discharge_1196_ = lean_ctor_get(v_toBacktrackConfig_1178_, 3);
v_commitIndependentGoals_1197_ = lean_ctor_get_uint8(v_toBacktrackConfig_1178_, sizeof(void*)*4);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_toBacktrackConfig_1178_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1199_ = v_toBacktrackConfig_1178_;
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_discharge_1196_);
lean_inc(v_suspend_1195_);
lean_inc(v_proc_1194_);
lean_inc(v_maxDepth_1193_);
lean_dec(v_toBacktrackConfig_1178_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___f_1201_; lean_object* v___x_1203_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1201_, 0, v_test_1176_);
lean_closure_set(v___f_1201_, 1, v_discharge_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 3, v___f_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_maxDepth_1193_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_proc_1194_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_suspend_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v___f_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*4, v_commitIndependentGoals_1197_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1203_);
v___x_1205_ = v___x_1191_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_toApplyConfig_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2, v_transparency_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2 + 1, v_symm_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2 + 2, v_exfalso_1189_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1205_);
v___x_1207_ = v___x_1184_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1, v_backtracking_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 1, v_intro_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 2, v_constructor_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*1 + 3, v_suggestions_1182_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1216_, lean_object* v_proc_1217_, lean_object* v_orig_1218_, lean_object* v_goals_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
if (lean_obj_tag(v_goals_1219_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_proc_1217_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1225_ = lean_apply_7(v_proc_1216_, v_orig_1218_, v_goals_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
return v___x_1225_;
}
else
{
lean_object* v_head_1226_; lean_object* v_tail_1227_; lean_object* v___x_1228_; 
v_head_1226_ = lean_ctor_get(v_goals_1219_, 0);
v_tail_1227_ = lean_ctor_get(v_goals_1219_, 1);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v_head_1226_);
v___x_1228_ = lean_apply_6(v_proc_1217_, v_head_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1238_; 
lean_inc(v_tail_1227_);
lean_dec_ref_known(v_goals_1219_, 2);
lean_dec(v_orig_1218_);
lean_dec_ref(v_proc_1216_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = l_List_appendTR___redArg(v_a_1229_, v_tail_1227_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1251_; 
v_a_1239_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1241_ = v___x_1228_;
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1228_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
uint8_t v___y_1244_; uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_Exception_isInterrupt(v_a_1239_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; 
lean_inc(v_a_1239_);
v___x_1250_ = l_Lean_Exception_isRuntime(v_a_1239_);
v___y_1244_ = v___x_1250_;
goto v___jp_1243_;
}
else
{
v___y_1244_ = v___x_1249_;
goto v___jp_1243_;
}
v___jp_1243_:
{
if (v___y_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_del_object(v___x_1241_);
lean_dec(v_a_1239_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
v___x_1245_ = lean_apply_7(v_proc_1216_, v_orig_1218_, v_goals_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, lean_box(0));
return v___x_1245_;
}
else
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v_goals_1219_, 2);
lean_dec(v_orig_1218_);
lean_dec_ref(v_proc_1216_);
if (v_isShared_1242_ == 0)
{
v___x_1247_ = v___x_1241_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1239_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1252_, lean_object* v_proc_1253_, lean_object* v_orig_1254_, lean_object* v_goals_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1252_, v_proc_1253_, v_orig_1254_, v_goals_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1262_, lean_object* v_proc_1263_){
_start:
{
lean_object* v_toApplyRulesConfig_1264_; lean_object* v_toBacktrackConfig_1265_; uint8_t v_backtracking_1266_; uint8_t v_intro_1267_; uint8_t v_constructor_1268_; uint8_t v_suggestions_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1301_; 
v_toApplyRulesConfig_1264_ = lean_ctor_get(v_cfg_1262_, 0);
lean_inc_ref(v_toApplyRulesConfig_1264_);
v_toBacktrackConfig_1265_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 0);
lean_inc_ref(v_toBacktrackConfig_1265_);
v_backtracking_1266_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1);
v_intro_1267_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 1);
v_constructor_1268_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 2);
v_suggestions_1269_ = lean_ctor_get_uint8(v_cfg_1262_, sizeof(void*)*1 + 3);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_cfg_1262_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_cfg_1262_, 0);
lean_dec(v_unused_1302_);
v___x_1271_ = v_cfg_1262_;
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v_cfg_1262_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1301_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_toApplyConfig_1273_; uint8_t v_transparency_1274_; uint8_t v_symm_1275_; uint8_t v_exfalso_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1299_; 
v_toApplyConfig_1273_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 1);
v_transparency_1274_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2);
v_symm_1275_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2 + 1);
v_exfalso_1276_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1264_, sizeof(void*)*2 + 2);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_toApplyRulesConfig_1264_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_toApplyRulesConfig_1264_, 0);
lean_dec(v_unused_1300_);
v___x_1278_ = v_toApplyRulesConfig_1264_;
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_toApplyConfig_1273_);
lean_dec(v_toApplyRulesConfig_1264_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1299_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_maxDepth_1280_; lean_object* v_proc_1281_; lean_object* v_suspend_1282_; lean_object* v_discharge_1283_; uint8_t v_commitIndependentGoals_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1298_; 
v_maxDepth_1280_ = lean_ctor_get(v_toBacktrackConfig_1265_, 0);
v_proc_1281_ = lean_ctor_get(v_toBacktrackConfig_1265_, 1);
v_suspend_1282_ = lean_ctor_get(v_toBacktrackConfig_1265_, 2);
v_discharge_1283_ = lean_ctor_get(v_toBacktrackConfig_1265_, 3);
v_commitIndependentGoals_1284_ = lean_ctor_get_uint8(v_toBacktrackConfig_1265_, sizeof(void*)*4);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_toBacktrackConfig_1265_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1286_ = v_toBacktrackConfig_1265_;
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_discharge_1283_);
lean_inc(v_suspend_1282_);
lean_inc(v_proc_1281_);
lean_inc(v_maxDepth_1280_);
lean_dec(v_toBacktrackConfig_1265_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___f_1288_; lean_object* v___x_1290_; 
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1288_, 0, v_proc_1281_);
lean_closure_set(v___f_1288_, 1, v_proc_1263_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___f_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_maxDepth_1280_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___f_1288_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_suspend_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_discharge_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*4, v_commitIndependentGoals_1284_);
v___x_1290_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1290_);
v___x_1292_ = v___x_1278_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_toApplyConfig_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2, v_transparency_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2 + 1, v_symm_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*2 + 2, v_exfalso_1276_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1292_);
v___x_1294_ = v___x_1271_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1, v_backtracking_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 1, v_intro_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 2, v_constructor_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1295_, sizeof(void*)*1 + 3, v_suggestions_1269_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = 1;
v___x_1310_ = l_Lean_Meta_intro1Core(v_g_1303_, v___x_1309_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1328_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1328_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1328_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_snd_1315_ = lean_ctor_get(v_a_1311_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1311_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_a_1311_, 0);
lean_dec(v_unused_1327_);
v___x_1317_ = v_a_1311_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_dec(v_a_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 1);
lean_ctor_set(v___x_1317_, 1, v___x_1319_);
lean_ctor_set(v___x_1317_, 0, v_snd_1315_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_snd_1315_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1321_);
v___x_1323_ = v___x_1313_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1310_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1310_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
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
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1345_){
_start:
{
lean_object* v___f_1346_; lean_object* v___x_1347_; 
v___f_1346_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1347_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1345_, v___f_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_ks_1352_; lean_object* v_vs_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1377_; 
v_ks_1352_ = lean_ctor_get(v_x_1348_, 0);
v_vs_1353_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1355_ = v_x_1348_;
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_vs_1353_);
lean_inc(v_ks_1352_);
lean_dec(v_x_1348_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_array_get_size(v_ks_1352_);
v___x_1358_ = lean_nat_dec_lt(v_x_1349_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_dec(v_x_1349_);
v___x_1359_ = lean_array_push(v_ks_1352_, v_x_1350_);
v___x_1360_ = lean_array_push(v_vs_1353_, v_x_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1362_ = v___x_1355_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v_k_x27_1364_; uint8_t v___x_1365_; 
v_k_x27_1364_ = lean_array_fget_borrowed(v_ks_1352_, v_x_1349_);
v___x_1365_ = l_Lean_instBEqMVarId_beq(v_x_1350_, v_k_x27_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1367_; 
if (v_isShared_1356_ == 0)
{
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_ks_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_vs_1353_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_add(v_x_1349_, v___x_1368_);
lean_dec(v_x_1349_);
v_x_1348_ = v___x_1367_;
v_x_1349_ = v___x_1369_;
goto _start;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_array_fset(v_ks_1352_, v_x_1349_, v_x_1350_);
v___x_1373_ = lean_array_fset(v_vs_1353_, v_x_1349_, v_x_1351_);
lean_dec(v_x_1349_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1373_);
lean_ctor_set(v___x_1355_, 0, v___x_1372_);
v___x_1375_ = v___x_1355_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1378_, lean_object* v_k_1379_, lean_object* v_v_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1378_, v___x_1381_, v_k_1379_, v_v_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1384_, size_t v_x_1385_, size_t v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v_es_1389_; size_t v___x_1390_; size_t v___x_1391_; lean_object* v_j_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_es_1389_ = lean_ctor_get(v_x_1384_, 0);
v___x_1390_ = ((size_t)31ULL);
v___x_1391_ = lean_usize_land(v_x_1385_, v___x_1390_);
v_j_1392_ = lean_usize_to_nat(v___x_1391_);
v___x_1393_ = lean_array_get_size(v_es_1389_);
v___x_1394_ = lean_nat_dec_lt(v_j_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec(v_j_1392_);
lean_dec(v_x_1388_);
lean_dec(v_x_1387_);
return v_x_1384_;
}
else
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1433_; 
lean_inc_ref(v_es_1389_);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1434_);
v___x_1396_ = v_x_1384_;
v_isShared_1397_ = v_isSharedCheck_1433_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_x_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1433_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_v_1398_; lean_object* v___x_1399_; lean_object* v_xs_x27_1400_; lean_object* v___y_1402_; 
v_v_1398_ = lean_array_fget(v_es_1389_, v_j_1392_);
v___x_1399_ = lean_box(0);
v_xs_x27_1400_ = lean_array_fset(v_es_1389_, v_j_1392_, v___x_1399_);
switch(lean_obj_tag(v_v_1398_))
{
case 0:
{
lean_object* v_key_1407_; lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1418_; 
v_key_1407_ = lean_ctor_get(v_v_1398_, 0);
v_val_1408_ = lean_ctor_get(v_v_1398_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1410_ = v_v_1398_;
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_inc(v_key_1407_);
lean_dec(v_v_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1418_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_instBEqMVarId_beq(v_x_1387_, v_key_1407_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_del_object(v___x_1410_);
v___x_1413_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1407_, v_val_1408_, v_x_1387_, v_x_1388_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
v___y_1402_ = v___x_1414_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_val_1408_);
lean_dec(v_key_1407_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_x_1388_);
lean_ctor_set(v___x_1410_, 0, v_x_1387_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_x_1387_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_x_1388_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v___y_1402_ = v___x_1416_;
goto v___jp_1401_;
}
}
}
}
case 1:
{
lean_object* v_node_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1431_; 
v_node_1419_ = lean_ctor_get(v_v_1398_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_v_1398_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1421_ = v_v_1398_;
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_node_1419_);
lean_dec(v_v_1398_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1423_ = ((size_t)5ULL);
v___x_1424_ = lean_usize_shift_right(v_x_1385_, v___x_1423_);
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_x_1386_, v___x_1425_);
v___x_1427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1419_, v___x_1424_, v___x_1426_, v_x_1387_, v_x_1388_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1427_);
v___x_1429_ = v___x_1421_;
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
v___y_1402_ = v___x_1429_;
goto v___jp_1401_;
}
}
}
default: 
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_x_1387_);
lean_ctor_set(v___x_1432_, 1, v_x_1388_);
v___y_1402_ = v___x_1432_;
goto v___jp_1401_;
}
}
v___jp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_array_fset(v_xs_x27_1400_, v_j_1392_, v___y_1402_);
lean_dec(v_j_1392_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1403_);
v___x_1405_ = v___x_1396_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_ks_1435_; lean_object* v_vs_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1456_; 
v_ks_1435_ = lean_ctor_get(v_x_1384_, 0);
v_vs_1436_ = lean_ctor_get(v_x_1384_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1438_ = v_x_1384_;
v_isShared_1439_ = v_isSharedCheck_1456_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_vs_1436_);
lean_inc(v_ks_1435_);
lean_dec(v_x_1384_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1456_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_ks_1435_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_vs_1436_);
v___x_1441_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v_newNode_1442_; uint8_t v___y_1444_; size_t v___x_1450_; uint8_t v___x_1451_; 
v_newNode_1442_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1441_, v_x_1387_, v_x_1388_);
v___x_1450_ = ((size_t)7ULL);
v___x_1451_ = lean_usize_dec_le(v___x_1450_, v_x_1386_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1452_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1442_);
v___x_1453_ = lean_unsigned_to_nat(4u);
v___x_1454_ = lean_nat_dec_lt(v___x_1452_, v___x_1453_);
lean_dec(v___x_1452_);
v___y_1444_ = v___x_1454_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v___x_1451_;
goto v___jp_1443_;
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
lean_object* v_ks_1445_; lean_object* v_vs_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_ks_1445_ = lean_ctor_get(v_newNode_1442_, 0);
lean_inc_ref(v_ks_1445_);
v_vs_1446_ = lean_ctor_get(v_newNode_1442_, 1);
lean_inc_ref(v_vs_1446_);
lean_dec_ref(v_newNode_1442_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1449_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1386_, v_ks_1445_, v_vs_1446_, v___x_1447_, v___x_1448_);
lean_dec_ref(v_vs_1446_);
lean_dec_ref(v_ks_1445_);
return v___x_1449_;
}
else
{
return v_newNode_1442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_i_1460_, lean_object* v_entries_1461_){
_start:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = lean_array_get_size(v_keys_1458_);
v___x_1463_ = lean_nat_dec_lt(v_i_1460_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_dec(v_i_1460_);
return v_entries_1461_;
}
else
{
lean_object* v_k_1464_; lean_object* v_v_1465_; uint64_t v___x_1466_; size_t v_h_1467_; size_t v___x_1468_; lean_object* v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; size_t v_h_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_k_1464_ = lean_array_fget_borrowed(v_keys_1458_, v_i_1460_);
v_v_1465_ = lean_array_fget_borrowed(v_vals_1459_, v_i_1460_);
v___x_1466_ = l_Lean_instHashableMVarId_hash(v_k_1464_);
v_h_1467_ = lean_uint64_to_usize(v___x_1466_);
v___x_1468_ = ((size_t)5ULL);
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_sub(v_depth_1457_, v___x_1470_);
v___x_1472_ = lean_usize_mul(v___x_1468_, v___x_1471_);
v_h_1473_ = lean_usize_shift_right(v_h_1467_, v___x_1472_);
v___x_1474_ = lean_nat_add(v_i_1460_, v___x_1469_);
lean_dec(v_i_1460_);
lean_inc(v_v_1465_);
lean_inc(v_k_1464_);
v___x_1475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1461_, v_h_1473_, v_depth_1457_, v_k_1464_, v_v_1465_);
v_i_1460_ = v___x_1474_;
v_entries_1461_ = v___x_1475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1477_, lean_object* v_keys_1478_, lean_object* v_vals_1479_, lean_object* v_i_1480_, lean_object* v_entries_1481_){
_start:
{
size_t v_depth_boxed_1482_; lean_object* v_res_1483_; 
v_depth_boxed_1482_ = lean_unbox_usize(v_depth_1477_);
lean_dec(v_depth_1477_);
v_res_1483_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1482_, v_keys_1478_, v_vals_1479_, v_i_1480_, v_entries_1481_);
lean_dec_ref(v_vals_1479_);
lean_dec_ref(v_keys_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
size_t v_x_824__boxed_1489_; size_t v_x_825__boxed_1490_; lean_object* v_res_1491_; 
v_x_824__boxed_1489_ = lean_unbox_usize(v_x_1485_);
lean_dec(v_x_1485_);
v_x_825__boxed_1490_ = lean_unbox_usize(v_x_1486_);
lean_dec(v_x_1486_);
v_res_1491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1484_, v_x_824__boxed_1489_, v_x_825__boxed_1490_, v_x_1487_, v_x_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
uint64_t v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = l_Lean_instHashableMVarId_hash(v_x_1493_);
v___x_1496_ = lean_uint64_to_usize(v___x_1495_);
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1492_, v___x_1496_, v___x_1497_, v_x_1493_, v_x_1494_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1499_, lean_object* v_val_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v_mctx_1504_; lean_object* v_cache_1505_; lean_object* v_zetaDeltaFVarIds_1506_; lean_object* v_postponed_1507_; lean_object* v_diag_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1536_; 
v___x_1503_ = lean_st_ref_take(v___y_1501_);
v_mctx_1504_ = lean_ctor_get(v___x_1503_, 0);
v_cache_1505_ = lean_ctor_get(v___x_1503_, 1);
v_zetaDeltaFVarIds_1506_ = lean_ctor_get(v___x_1503_, 2);
v_postponed_1507_ = lean_ctor_get(v___x_1503_, 3);
v_diag_1508_ = lean_ctor_get(v___x_1503_, 4);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1510_ = v___x_1503_;
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_diag_1508_);
lean_inc(v_postponed_1507_);
lean_inc(v_zetaDeltaFVarIds_1506_);
lean_inc(v_cache_1505_);
lean_inc(v_mctx_1504_);
lean_dec(v___x_1503_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_depth_1512_; lean_object* v_levelAssignDepth_1513_; lean_object* v_lmvarCounter_1514_; lean_object* v_mvarCounter_1515_; lean_object* v_lDecls_1516_; lean_object* v_decls_1517_; lean_object* v_userNames_1518_; lean_object* v_lAssignment_1519_; lean_object* v_eAssignment_1520_; lean_object* v_dAssignment_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v_depth_1512_ = lean_ctor_get(v_mctx_1504_, 0);
v_levelAssignDepth_1513_ = lean_ctor_get(v_mctx_1504_, 1);
v_lmvarCounter_1514_ = lean_ctor_get(v_mctx_1504_, 2);
v_mvarCounter_1515_ = lean_ctor_get(v_mctx_1504_, 3);
v_lDecls_1516_ = lean_ctor_get(v_mctx_1504_, 4);
v_decls_1517_ = lean_ctor_get(v_mctx_1504_, 5);
v_userNames_1518_ = lean_ctor_get(v_mctx_1504_, 6);
v_lAssignment_1519_ = lean_ctor_get(v_mctx_1504_, 7);
v_eAssignment_1520_ = lean_ctor_get(v_mctx_1504_, 8);
v_dAssignment_1521_ = lean_ctor_get(v_mctx_1504_, 9);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_mctx_1504_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1523_ = v_mctx_1504_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_dAssignment_1521_);
lean_inc(v_eAssignment_1520_);
lean_inc(v_lAssignment_1519_);
lean_inc(v_userNames_1518_);
lean_inc(v_decls_1517_);
lean_inc(v_lDecls_1516_);
lean_inc(v_mvarCounter_1515_);
lean_inc(v_lmvarCounter_1514_);
lean_inc(v_levelAssignDepth_1513_);
lean_inc(v_depth_1512_);
lean_dec(v_mctx_1504_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1520_, v_mvarId_1499_, v_val_1500_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 8, v___x_1525_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_depth_1512_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_levelAssignDepth_1513_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_lmvarCounter_1514_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_mvarCounter_1515_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_lDecls_1516_);
lean_ctor_set(v_reuseFailAlloc_1534_, 5, v_decls_1517_);
lean_ctor_set(v_reuseFailAlloc_1534_, 6, v_userNames_1518_);
lean_ctor_set(v_reuseFailAlloc_1534_, 7, v_lAssignment_1519_);
lean_ctor_set(v_reuseFailAlloc_1534_, 8, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1534_, 9, v_dAssignment_1521_);
v___x_1527_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1527_);
v___x_1529_ = v___x_1510_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_cache_1505_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_zetaDeltaFVarIds_1506_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_postponed_1507_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_diag_1508_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_st_ref_set(v___y_1501_, v___x_1529_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1537_, lean_object* v_val_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1537_, v_val_1538_, v___y_1539_);
lean_dec(v___y_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
lean_inc(v_g_1542_);
v___x_1548_ = l_Lean_MVarId_getType(v_g_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Lean_Meta_synthInstance(v_a_1549_, v___x_1550_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1542_, v_a_1552_, v___y_1544_);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1562_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_g_1542_);
v_a_1563_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1551_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1551_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_g_1542_);
v_a_1571_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1548_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1548_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1587_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; 
v___f_1588_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1589_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1587_, v___f_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1590_, lean_object* v_val_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1590_, v_val_1591_, v___y_1593_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1598_, lean_object* v_val_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1598_, v_val_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1607_, v_x_1608_, v_x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1611_, lean_object* v_x_1612_, size_t v_x_1613_, size_t v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1612_, v_x_1613_, v_x_1614_, v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
size_t v_x_1149__boxed_1624_; size_t v_x_1150__boxed_1625_; lean_object* v_res_1626_; 
v_x_1149__boxed_1624_ = lean_unbox_usize(v_x_1620_);
lean_dec(v_x_1620_);
v_x_1150__boxed_1625_ = lean_unbox_usize(v_x_1621_);
lean_dec(v_x_1621_);
v_res_1626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1618_, v_x_1619_, v_x_1149__boxed_1624_, v_x_1150__boxed_1625_, v_x_1622_, v_x_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1627_, lean_object* v_n_1628_, lean_object* v_k_1629_, lean_object* v_v_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1628_, v_k_1629_, v_v_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1632_, size_t v_depth_1633_, lean_object* v_keys_1634_, lean_object* v_vals_1635_, lean_object* v_heq_1636_, lean_object* v_i_1637_, lean_object* v_entries_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1633_, v_keys_1634_, v_vals_1635_, v_i_1637_, v_entries_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1640_, lean_object* v_depth_1641_, lean_object* v_keys_1642_, lean_object* v_vals_1643_, lean_object* v_heq_1644_, lean_object* v_i_1645_, lean_object* v_entries_1646_){
_start:
{
size_t v_depth_boxed_1647_; lean_object* v_res_1648_; 
v_depth_boxed_1647_ = lean_unbox_usize(v_depth_1641_);
lean_dec(v_depth_1641_);
v_res_1648_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1640_, v_depth_boxed_1647_, v_keys_1642_, v_vals_1643_, v_heq_1644_, v_i_1645_, v_entries_1646_);
lean_dec_ref(v_vals_1643_);
lean_dec_ref(v_keys_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1650_, v_x_1651_, v_x_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1655_, lean_object* v_discharge_1656_, lean_object* v_g_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v_g_1657_);
v___x_1663_ = lean_apply_6(v_discharge_1655_, v_g_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec(v_g_1657_);
lean_dec_ref(v_discharge_1656_);
return v___x_1663_;
}
else
{
lean_object* v_a_1664_; uint8_t v___y_1666_; uint8_t v___x_1668_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
v___x_1668_ = l_Lean_Exception_isInterrupt(v_a_1664_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; 
v___x_1669_ = l_Lean_Exception_isRuntime(v_a_1664_);
v___y_1666_ = v___x_1669_;
goto v___jp_1665_;
}
else
{
lean_dec(v_a_1664_);
v___y_1666_ = v___x_1668_;
goto v___jp_1665_;
}
v___jp_1665_:
{
if (v___y_1666_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref_known(v___x_1663_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
v___x_1667_ = lean_apply_6(v_discharge_1656_, v_g_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1667_;
}
else
{
lean_dec(v_g_1657_);
lean_dec_ref(v_discharge_1656_);
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1670_, lean_object* v_discharge_1671_, lean_object* v_g_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1670_, v_discharge_1671_, v_g_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1679_, lean_object* v_discharge_1680_){
_start:
{
lean_object* v_toApplyRulesConfig_1681_; lean_object* v_toBacktrackConfig_1682_; uint8_t v_backtracking_1683_; uint8_t v_intro_1684_; uint8_t v_constructor_1685_; uint8_t v_suggestions_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1718_; 
v_toApplyRulesConfig_1681_ = lean_ctor_get(v_cfg_1679_, 0);
lean_inc_ref(v_toApplyRulesConfig_1681_);
v_toBacktrackConfig_1682_ = lean_ctor_get(v_toApplyRulesConfig_1681_, 0);
lean_inc_ref(v_toBacktrackConfig_1682_);
v_backtracking_1683_ = lean_ctor_get_uint8(v_cfg_1679_, sizeof(void*)*1);
v_intro_1684_ = lean_ctor_get_uint8(v_cfg_1679_, sizeof(void*)*1 + 1);
v_constructor_1685_ = lean_ctor_get_uint8(v_cfg_1679_, sizeof(void*)*1 + 2);
v_suggestions_1686_ = lean_ctor_get_uint8(v_cfg_1679_, sizeof(void*)*1 + 3);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_cfg_1679_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v_cfg_1679_, 0);
lean_dec(v_unused_1719_);
v___x_1688_ = v_cfg_1679_;
v_isShared_1689_ = v_isSharedCheck_1718_;
goto v_resetjp_1687_;
}
else
{
lean_dec(v_cfg_1679_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1718_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_toApplyConfig_1690_; uint8_t v_transparency_1691_; uint8_t v_symm_1692_; uint8_t v_exfalso_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1716_; 
v_toApplyConfig_1690_ = lean_ctor_get(v_toApplyRulesConfig_1681_, 1);
v_transparency_1691_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1681_, sizeof(void*)*2);
v_symm_1692_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1681_, sizeof(void*)*2 + 1);
v_exfalso_1693_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1681_, sizeof(void*)*2 + 2);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_toApplyRulesConfig_1681_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_toApplyRulesConfig_1681_, 0);
lean_dec(v_unused_1717_);
v___x_1695_ = v_toApplyRulesConfig_1681_;
v_isShared_1696_ = v_isSharedCheck_1716_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_toApplyConfig_1690_);
lean_dec(v_toApplyRulesConfig_1681_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1716_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_maxDepth_1697_; lean_object* v_proc_1698_; lean_object* v_suspend_1699_; lean_object* v_discharge_1700_; uint8_t v_commitIndependentGoals_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1715_; 
v_maxDepth_1697_ = lean_ctor_get(v_toBacktrackConfig_1682_, 0);
v_proc_1698_ = lean_ctor_get(v_toBacktrackConfig_1682_, 1);
v_suspend_1699_ = lean_ctor_get(v_toBacktrackConfig_1682_, 2);
v_discharge_1700_ = lean_ctor_get(v_toBacktrackConfig_1682_, 3);
v_commitIndependentGoals_1701_ = lean_ctor_get_uint8(v_toBacktrackConfig_1682_, sizeof(void*)*4);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_toBacktrackConfig_1682_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1703_ = v_toBacktrackConfig_1682_;
v_isShared_1704_ = v_isSharedCheck_1715_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_discharge_1700_);
lean_inc(v_suspend_1699_);
lean_inc(v_proc_1698_);
lean_inc(v_maxDepth_1697_);
lean_dec(v_toBacktrackConfig_1682_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1715_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___f_1705_; lean_object* v___x_1707_; 
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1705_, 0, v_discharge_1680_);
lean_closure_set(v___f_1705_, 1, v_discharge_1700_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 3, v___f_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_maxDepth_1697_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_proc_1698_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_suspend_1699_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v___f_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*4, v_commitIndependentGoals_1701_);
v___x_1707_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1707_);
v___x_1709_ = v___x_1695_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_toApplyConfig_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*2, v_transparency_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*2 + 1, v_symm_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*2 + 2, v_exfalso_1693_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1709_);
v___x_1711_ = v___x_1688_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*1, v_backtracking_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*1 + 1, v_intro_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*1 + 2, v_constructor_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*1 + 3, v_suggestions_1686_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = 1;
v___x_1727_ = l_Lean_Meta_intro1Core(v_g_1720_, v___x_1726_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1746_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1746_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1746_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1744_; 
v_snd_1732_ = lean_ctor_get(v_a_1728_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_a_1728_, 0);
lean_dec(v_unused_1745_);
v___x_1734_ = v_a_1728_;
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_dec(v_a_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(0);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 1);
lean_ctor_set(v___x_1734_, 1, v___x_1736_);
lean_ctor_set(v___x_1734_, 0, v_snd_1732_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_snd_1732_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1739_);
v___x_1741_ = v___x_1730_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1727_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1727_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1763_){
_start:
{
lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___f_1764_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1765_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1763_, v___f_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1777_ = l_Lean_MVarId_constructor(v_g_1770_, v___x_1776_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1777_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1803_){
_start:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; 
v___f_1804_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1805_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1803_, v___f_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
lean_inc(v_g_1808_);
v___x_1814_ = l_Lean_MVarId_getType(v_g_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Lean_Meta_synthInstance(v_a_1815_, v___x_1816_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1819_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1808_, v_a_1818_, v___y_1810_);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1828_);
v___x_1821_ = v___x_1819_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1819_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_g_1808_);
v_a_1829_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1817_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1817_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_g_1808_);
v_a_1837_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1814_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1814_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1853_){
_start:
{
lean_object* v___f_1854_; lean_object* v___x_1855_; 
v___f_1854_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1855_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1853_, v___f_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_hasMVar(v_e_1856_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_e_1856_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v_mctx_1862_; lean_object* v___x_1863_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1866_; lean_object* v_cache_1867_; lean_object* v_zetaDeltaFVarIds_1868_; lean_object* v_postponed_1869_; lean_object* v_diag_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v___x_1861_ = lean_st_ref_get(v___y_1857_);
v_mctx_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc_ref(v_mctx_1862_);
lean_dec(v___x_1861_);
v___x_1863_ = l_Lean_instantiateMVarsCore(v_mctx_1862_, v_e_1856_);
v_fst_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_fst_1864_);
v_snd_1865_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_snd_1865_);
lean_dec_ref(v___x_1863_);
v___x_1866_ = lean_st_ref_take(v___y_1857_);
v_cache_1867_ = lean_ctor_get(v___x_1866_, 1);
v_zetaDeltaFVarIds_1868_ = lean_ctor_get(v___x_1866_, 2);
v_postponed_1869_ = lean_ctor_get(v___x_1866_, 3);
v_diag_1870_ = lean_ctor_get(v___x_1866_, 4);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1866_, 0);
lean_dec(v_unused_1880_);
v___x_1872_ = v___x_1866_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_diag_1870_);
lean_inc(v_postponed_1869_);
lean_inc(v_zetaDeltaFVarIds_1868_);
lean_inc(v_cache_1867_);
lean_dec(v___x_1866_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v_snd_1865_);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_snd_1865_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_cache_1867_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_zetaDeltaFVarIds_1868_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_postponed_1869_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v_diag_1870_);
v___x_1875_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_st_ref_set(v___y_1857_, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_fst_1864_);
return v___x_1877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1881_, v___y_1882_);
lean_dec(v___y_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1885_, v___y_1887_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1899_, v_x_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1923_, v_x_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1931_, lean_object* v_mvarId_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1932_, v_x_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_mvarId_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1940_, v_mvarId_1941_, v_x_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_ref_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_ref_1955_ = lean_ctor_get(v___y_1952_, 5);
v___x_1956_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc(v_ref_1955_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_ref_1955_);
lean_ctor_set(v___x_1961_, 1, v_a_1957_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = l_List_reverse___redArg(v_x_1974_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
else
{
lean_object* v_head_1982_; lean_object* v_tail_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2003_; 
v_head_1982_ = lean_ctor_get(v_x_1973_, 0);
v_tail_1983_ = lean_ctor_get(v_x_1973_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_x_1973_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1985_ = v_x_1973_;
v_isShared_1986_ = v_isSharedCheck_2003_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_tail_1983_);
lean_inc(v_head_1982_);
lean_dec(v_x_1973_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2003_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_inc(v_head_1982_);
v___x_1987_ = l_Lean_Expr_mvar___override(v_head_1982_);
v___x_1988_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1982_, v___x_1988_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v_x_1974_);
lean_ctor_set(v___x_1985_, 0, v_a_1990_);
v___x_1992_ = v___x_1985_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_x_1974_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_x_1973_ = v_tail_1983_;
v_x_1974_ = v___x_1992_;
goto _start;
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_del_object(v___x_1985_);
lean_dec(v_tail_1983_);
lean_dec(v_x_1974_);
v_a_1995_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1989_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1989_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2011_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2014_ = l_Lean_stringToMessageData(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2015_, lean_object* v_proc_2016_, lean_object* v_orig_2017_, lean_object* v_goals_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_box(0);
lean_inc(v_orig_2017_);
v___x_2025_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2017_, v___x_2024_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
v___x_2027_ = lean_apply_6(v_test_2015_, v_a_2026_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, lean_box(0));
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; uint8_t v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_goals_2018_);
lean_dec(v_orig_2017_);
lean_dec_ref(v_proc_2016_);
v___x_2030_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2031_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2030_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v___x_2040_; 
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
v___x_2040_ = lean_apply_7(v_proc_2016_, v_orig_2017_, v_goals_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, lean_box(0));
return v___x_2040_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_goals_2018_);
lean_dec(v_orig_2017_);
lean_dec_ref(v_proc_2016_);
v_a_2041_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2027_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2027_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_goals_2018_);
lean_dec(v_orig_2017_);
lean_dec_ref(v_proc_2016_);
lean_dec_ref(v_test_2015_);
v_a_2049_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2025_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2025_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2057_, lean_object* v_proc_2058_, lean_object* v_orig_2059_, lean_object* v_goals_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2057_, v_proc_2058_, v_orig_2059_, v_goals_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2067_, lean_object* v_test_2068_){
_start:
{
lean_object* v_toApplyRulesConfig_2069_; lean_object* v_toBacktrackConfig_2070_; uint8_t v_backtracking_2071_; uint8_t v_intro_2072_; uint8_t v_constructor_2073_; uint8_t v_suggestions_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2106_; 
v_toApplyRulesConfig_2069_ = lean_ctor_get(v_cfg_2067_, 0);
lean_inc_ref(v_toApplyRulesConfig_2069_);
v_toBacktrackConfig_2070_ = lean_ctor_get(v_toApplyRulesConfig_2069_, 0);
lean_inc_ref(v_toBacktrackConfig_2070_);
v_backtracking_2071_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*1);
v_intro_2072_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*1 + 1);
v_constructor_2073_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*1 + 2);
v_suggestions_2074_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*1 + 3);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_cfg_2067_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; 
v_unused_2107_ = lean_ctor_get(v_cfg_2067_, 0);
lean_dec(v_unused_2107_);
v___x_2076_ = v_cfg_2067_;
v_isShared_2077_ = v_isSharedCheck_2106_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_cfg_2067_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2106_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_toApplyConfig_2078_; uint8_t v_transparency_2079_; uint8_t v_symm_2080_; uint8_t v_exfalso_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2104_; 
v_toApplyConfig_2078_ = lean_ctor_get(v_toApplyRulesConfig_2069_, 1);
v_transparency_2079_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2069_, sizeof(void*)*2);
v_symm_2080_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2069_, sizeof(void*)*2 + 1);
v_exfalso_2081_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2069_, sizeof(void*)*2 + 2);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_toApplyRulesConfig_2069_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_toApplyRulesConfig_2069_, 0);
lean_dec(v_unused_2105_);
v___x_2083_ = v_toApplyRulesConfig_2069_;
v_isShared_2084_ = v_isSharedCheck_2104_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_toApplyConfig_2078_);
lean_dec(v_toApplyRulesConfig_2069_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2104_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_maxDepth_2085_; lean_object* v_proc_2086_; lean_object* v_suspend_2087_; lean_object* v_discharge_2088_; uint8_t v_commitIndependentGoals_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2103_; 
v_maxDepth_2085_ = lean_ctor_get(v_toBacktrackConfig_2070_, 0);
v_proc_2086_ = lean_ctor_get(v_toBacktrackConfig_2070_, 1);
v_suspend_2087_ = lean_ctor_get(v_toBacktrackConfig_2070_, 2);
v_discharge_2088_ = lean_ctor_get(v_toBacktrackConfig_2070_, 3);
v_commitIndependentGoals_2089_ = lean_ctor_get_uint8(v_toBacktrackConfig_2070_, sizeof(void*)*4);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_toBacktrackConfig_2070_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2091_ = v_toBacktrackConfig_2070_;
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_discharge_2088_);
lean_inc(v_suspend_2087_);
lean_inc(v_proc_2086_);
lean_inc(v_maxDepth_2085_);
lean_dec(v_toBacktrackConfig_2070_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___f_2093_; lean_object* v___x_2095_; 
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2093_, 0, v_test_2068_);
lean_closure_set(v___f_2093_, 1, v_proc_2086_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___f_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_maxDepth_2085_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___f_2093_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_suspend_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_discharge_2088_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*4, v_commitIndependentGoals_2089_);
v___x_2095_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2095_);
v___x_2097_ = v___x_2083_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_toApplyConfig_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*2, v_transparency_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*2 + 1, v_symm_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*2 + 2, v_exfalso_2081_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2097_);
v___x_2099_ = v___x_2076_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*1, v_backtracking_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*1 + 1, v_intro_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*1 + 2, v_constructor_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2100_, sizeof(void*)*1 + 3, v_suggestions_2074_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2108_, lean_object* v_msg_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2116_, v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = 0;
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; uint8_t v___x_2128_; 
v_head_2126_ = lean_ctor_get(v_x_2124_, 0);
v_tail_2127_ = lean_ctor_get(v_x_2124_, 1);
v___x_2128_ = l_Lean_Expr_hasMVar(v_head_2126_);
if (v___x_2128_ == 0)
{
v_x_2124_ = v_tail_2127_;
goto _start;
}
else
{
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2130_);
lean_dec(v_x_2130_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2133_, lean_object* v_sols_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2134_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
v___x_2141_ = lean_apply_6(v_test_2133_, v_sols_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, lean_box(0));
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_sols_2134_);
lean_dec_ref(v_test_2133_);
v___x_2142_ = lean_box(v___x_2140_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2144_, lean_object* v_sols_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2144_, v_sols_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2152_, lean_object* v_test_2153_){
_start:
{
lean_object* v___f_2154_; lean_object* v___x_2155_; 
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2154_, 0, v_test_2153_);
v___x_2155_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2152_, v___f_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2156_, lean_object* v_x_2157_){
_start:
{
if (lean_obj_tag(v_x_2157_) == 0)
{
uint8_t v___x_2158_; 
lean_dec_ref(v_e_2156_);
v___x_2158_ = 0;
return v___x_2158_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; uint8_t v___x_2161_; 
v_head_2159_ = lean_ctor_get(v_x_2157_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2157_, 1);
lean_inc_ref(v_e_2156_);
v___x_2161_ = l_Lean_Expr_occurs(v_e_2156_, v_head_2159_);
if (v___x_2161_ == 0)
{
v_x_2157_ = v_tail_2160_;
goto _start;
}
else
{
lean_dec_ref(v_e_2156_);
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2163_, lean_object* v_x_2164_){
_start:
{
uint8_t v_res_2165_; lean_object* v_r_2166_; 
v_res_2165_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2163_, v_x_2164_);
lean_dec(v_x_2164_);
v_r_2166_ = lean_box(v_res_2165_);
return v_r_2166_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2167_, lean_object* v_x_2168_){
_start:
{
if (lean_obj_tag(v_x_2168_) == 0)
{
uint8_t v___x_2169_; 
v___x_2169_ = 1;
return v___x_2169_;
}
else
{
lean_object* v_head_2170_; lean_object* v_tail_2171_; uint8_t v___x_2172_; 
v_head_2170_ = lean_ctor_get(v_x_2168_, 0);
lean_inc(v_head_2170_);
v_tail_2171_ = lean_ctor_get(v_x_2168_, 1);
lean_inc(v_tail_2171_);
lean_dec_ref_known(v_x_2168_, 2);
v___x_2172_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2170_, v_sols_2167_);
if (v___x_2172_ == 0)
{
lean_dec(v_tail_2171_);
return v___x_2172_;
}
else
{
v_x_2168_ = v_tail_2171_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2174_, lean_object* v_x_2175_){
_start:
{
uint8_t v_res_2176_; lean_object* v_r_2177_; 
v_res_2176_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2174_, v_x_2175_);
lean_dec(v_sols_2174_);
v_r_2177_ = lean_box(v_res_2176_);
return v_r_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2178_, lean_object* v_sols_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2179_, v_use_2178_);
v___x_2186_ = lean_box(v___x_2185_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2188_, lean_object* v_sols_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2188_, v_sols_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v_sols_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2196_, lean_object* v_use_2197_){
_start:
{
lean_object* v___f_2198_; lean_object* v___x_2199_; 
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2198_, 0, v_use_2197_);
v___x_2199_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2196_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2200_){
_start:
{
lean_object* v___y_2202_; lean_object* v_toApplyRulesConfig_2203_; uint8_t v_backtracking_2204_; uint8_t v_intro_2205_; uint8_t v_constructor_2206_; uint8_t v_suggestions_2207_; uint8_t v_intro_2211_; 
v_intro_2211_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1 + 1);
if (v_intro_2211_ == 0)
{
lean_object* v_toApplyRulesConfig_2212_; uint8_t v_backtracking_2213_; uint8_t v_constructor_2214_; uint8_t v_suggestions_2215_; 
v_toApplyRulesConfig_2212_ = lean_ctor_get(v_cfg_2200_, 0);
lean_inc_ref(v_toApplyRulesConfig_2212_);
v_backtracking_2213_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1);
v_constructor_2214_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1 + 2);
v_suggestions_2215_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1 + 3);
v___y_2202_ = v_cfg_2200_;
v_toApplyRulesConfig_2203_ = v_toApplyRulesConfig_2212_;
v_backtracking_2204_ = v_backtracking_2213_;
v_intro_2205_ = v_intro_2211_;
v_constructor_2206_ = v_constructor_2214_;
v_suggestions_2207_ = v_suggestions_2215_;
goto v___jp_2201_;
}
else
{
lean_object* v_toApplyRulesConfig_2216_; uint8_t v_backtracking_2217_; uint8_t v_constructor_2218_; uint8_t v_suggestions_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2233_; 
v_toApplyRulesConfig_2216_ = lean_ctor_get(v_cfg_2200_, 0);
v_backtracking_2217_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1);
v_constructor_2218_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1 + 2);
v_suggestions_2219_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*1 + 3);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_cfg_2200_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2221_ = v_cfg_2200_;
v_isShared_2222_ = v_isSharedCheck_2233_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_toApplyRulesConfig_2216_);
lean_dec(v_cfg_2200_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2233_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
uint8_t v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = 0;
if (v_isShared_2222_ == 0)
{
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_toApplyRulesConfig_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*1, v_backtracking_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*1 + 2, v_constructor_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*1 + 3, v_suggestions_2219_);
v___x_2225_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v_toApplyRulesConfig_2227_; uint8_t v_backtracking_2228_; uint8_t v_intro_2229_; uint8_t v_constructor_2230_; uint8_t v_suggestions_2231_; 
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*1 + 1, v___x_2223_);
v___x_2226_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2225_);
v_toApplyRulesConfig_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc_ref(v_toApplyRulesConfig_2227_);
v_backtracking_2228_ = lean_ctor_get_uint8(v___x_2226_, sizeof(void*)*1);
v_intro_2229_ = lean_ctor_get_uint8(v___x_2226_, sizeof(void*)*1 + 1);
v_constructor_2230_ = lean_ctor_get_uint8(v___x_2226_, sizeof(void*)*1 + 2);
v_suggestions_2231_ = lean_ctor_get_uint8(v___x_2226_, sizeof(void*)*1 + 3);
v___y_2202_ = v___x_2226_;
v_toApplyRulesConfig_2203_ = v_toApplyRulesConfig_2227_;
v_backtracking_2204_ = v_backtracking_2228_;
v_intro_2205_ = v_intro_2229_;
v_constructor_2206_ = v_constructor_2230_;
v_suggestions_2207_ = v_suggestions_2231_;
goto v___jp_2201_;
}
}
}
v___jp_2201_:
{
if (v_constructor_2206_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2203_);
return v___y_2202_;
}
else
{
uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref(v___y_2202_);
v___x_2208_ = 0;
v___x_2209_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2209_, 0, v_toApplyRulesConfig_2203_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*1, v_backtracking_2204_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*1 + 1, v_intro_2205_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*1 + 2, v___x_2208_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*1 + 3, v_suggestions_2207_);
v___x_2210_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2209_);
return v___x_2210_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
if (lean_obj_tag(v_x_2234_) == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = l_List_reverse___redArg(v_x_2235_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
else
{
lean_object* v_head_2245_; lean_object* v_tail_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2264_; 
v_head_2245_ = lean_ctor_get(v_x_2234_, 0);
v_tail_2246_ = lean_ctor_get(v_x_2234_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_x_2234_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2248_ = v_x_2234_;
v_isShared_2249_ = v_isSharedCheck_2264_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_tail_2246_);
lean_inc(v_head_2245_);
lean_dec(v_x_2234_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2264_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; 
lean_inc(v___y_2241_);
lean_inc_ref(v___y_2240_);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
v___x_2250_ = lean_apply_7(v_head_2245_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, lean_box(0));
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v_x_2235_);
lean_ctor_set(v___x_2248_, 0, v_a_2251_);
v___x_2253_ = v___x_2248_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_x_2235_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v_x_2234_ = v_tail_2246_;
v_x_2235_ = v___x_2253_;
goto _start;
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_del_object(v___x_2248_);
lean_dec(v_tail_2246_);
lean_dec(v_x_2235_);
v_a_2256_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2250_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2250_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2265_, v_x_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2275_, lean_object* v_cfg_2276_, lean_object* v_lemmas_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
v___x_2285_ = lean_apply_8(v_ctx_2275_, v_cfg_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, lean_box(0));
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_box(0);
v___x_2288_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2277_, v___x_2287_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = l_List_appendTR___redArg(v_a_2286_, v_a_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_dec(v_a_2286_);
return v___x_2288_;
}
}
else
{
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v_lemmas_2277_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2298_, lean_object* v_cfg_2299_, lean_object* v_lemmas_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2298_, v_cfg_2299_, v_lemmas_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2309_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = 0;
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2311_){
_start:
{
uint8_t v_res_2312_; lean_object* v_r_2313_; 
v_res_2312_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2311_);
lean_dec(v_x_2311_);
v_r_2313_ = lean_box(v_res_2312_);
return v_r_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2314_, lean_object* v___x_2315_, lean_object* v___x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2314_, v___x_2315_, v___x_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2331_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_fst_2327_; lean_object* v___x_2329_; 
v_fst_2327_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_fst_2327_);
lean_dec(v_a_2323_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v_fst_2327_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2322_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2322_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
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
return v___x_2337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2340_, lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2340_, v___x_2341_, v___x_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2363_, lean_object* v_g_2364_, lean_object* v_lemmas_2365_, lean_object* v_ctx_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; 
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2372_, 0, v_ctx_2366_);
lean_closure_set(v___f_2372_, 1, v_cfg_2363_);
lean_closure_set(v___f_2372_, 2, v_lemmas_2365_);
v___x_2373_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2374_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2375_, 0, v___f_2372_);
lean_closure_set(v___f_2375_, 1, v___x_2373_);
lean_closure_set(v___f_2375_, 2, v___x_2374_);
v___x_2376_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2364_, v___f_2375_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2377_, lean_object* v_g_2378_, lean_object* v_lemmas_2379_, lean_object* v_ctx_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2377_, v_g_2378_, v_lemmas_2379_, v_ctx_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2387_, lean_object* v_lemmas_2388_, lean_object* v_ctx_2389_, lean_object* v_g_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; 
lean_inc(v_g_2390_);
lean_inc_ref(v_cfg_2387_);
v___x_2396_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2387_, v_g_2390_, v_lemmas_2388_, v_ctx_2389_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_toApplyRulesConfig_2397_; lean_object* v_a_2398_; lean_object* v_toApplyConfig_2399_; uint8_t v_transparency_2400_; lean_object* v___x_2401_; 
v_toApplyRulesConfig_2397_ = lean_ctor_get(v_cfg_2387_, 0);
lean_inc_ref(v_toApplyRulesConfig_2397_);
lean_dec_ref(v_cfg_2387_);
v_a_2398_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2396_, 1);
v_toApplyConfig_2399_ = lean_ctor_get(v_toApplyRulesConfig_2397_, 1);
lean_inc_ref(v_toApplyConfig_2399_);
v_transparency_2400_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2397_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2397_);
v___x_2401_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2399_, v_transparency_2400_, v_a_2398_, v_g_2390_, v_a_2392_, v_a_2394_);
return v___x_2401_;
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_g_2390_);
lean_dec_ref(v_cfg_2387_);
v_a_2402_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2396_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2396_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2410_, lean_object* v_lemmas_2411_, lean_object* v_ctx_2412_, lean_object* v_g_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2410_, v_lemmas_2411_, v_ctx_2412_, v_g_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2420_, lean_object* v_lemmas_2421_, lean_object* v_ctx_2422_, lean_object* v_g_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
lean_inc(v_g_2423_);
lean_inc_ref(v_cfg_2420_);
v___x_2429_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2420_, v_g_2423_, v_lemmas_2421_, v_ctx_2422_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_toApplyRulesConfig_2430_; lean_object* v_a_2431_; lean_object* v_toApplyConfig_2432_; uint8_t v_transparency_2433_; lean_object* v___x_2434_; 
v_toApplyRulesConfig_2430_ = lean_ctor_get(v_cfg_2420_, 0);
lean_inc_ref(v_toApplyRulesConfig_2430_);
lean_dec_ref(v_cfg_2420_);
v_a_2431_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2429_, 1);
v_toApplyConfig_2432_ = lean_ctor_get(v_toApplyRulesConfig_2430_, 1);
lean_inc_ref(v_toApplyConfig_2432_);
v_transparency_2433_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2430_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2430_);
v___x_2434_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2432_, v_transparency_2433_, v_a_2431_, v_g_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2434_;
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_g_2423_);
lean_dec_ref(v_cfg_2420_);
v_a_2435_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2429_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2429_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
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
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2443_, lean_object* v_lemmas_2444_, lean_object* v_ctx_2445_, lean_object* v_g_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2443_, v_lemmas_2444_, v_ctx_2445_, v_g_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2453_, lean_object* v_i_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_array_get_size(v_keys_2453_);
v___x_2457_ = lean_nat_dec_lt(v_i_2454_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_dec(v_i_2454_);
return v___x_2457_;
}
else
{
lean_object* v_k_x27_2458_; uint8_t v___x_2459_; 
v_k_x27_2458_ = lean_array_fget_borrowed(v_keys_2453_, v_i_2454_);
v___x_2459_ = l_Lean_instBEqMVarId_beq(v_k_2455_, v_k_x27_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_unsigned_to_nat(1u);
v___x_2461_ = lean_nat_add(v_i_2454_, v___x_2460_);
lean_dec(v_i_2454_);
v_i_2454_ = v___x_2461_;
goto _start;
}
else
{
lean_dec(v_i_2454_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2463_, lean_object* v_i_2464_, lean_object* v_k_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2463_, v_i_2464_, v_k_2465_);
lean_dec(v_k_2465_);
lean_dec_ref(v_keys_2463_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2468_, size_t v_x_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2468_) == 0)
{
lean_object* v_es_2471_; lean_object* v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; lean_object* v_j_2475_; lean_object* v___x_2476_; 
v_es_2471_ = lean_ctor_get(v_x_2468_, 0);
v___x_2472_ = lean_box(2);
v___x_2473_ = ((size_t)31ULL);
v___x_2474_ = lean_usize_land(v_x_2469_, v___x_2473_);
v_j_2475_ = lean_usize_to_nat(v___x_2474_);
v___x_2476_ = lean_array_get_borrowed(v___x_2472_, v_es_2471_, v_j_2475_);
lean_dec(v_j_2475_);
switch(lean_obj_tag(v___x_2476_))
{
case 0:
{
lean_object* v_key_2477_; uint8_t v___x_2478_; 
v_key_2477_ = lean_ctor_get(v___x_2476_, 0);
v___x_2478_ = l_Lean_instBEqMVarId_beq(v_x_2470_, v_key_2477_);
return v___x_2478_;
}
case 1:
{
lean_object* v_node_2479_; size_t v___x_2480_; size_t v___x_2481_; 
v_node_2479_ = lean_ctor_get(v___x_2476_, 0);
v___x_2480_ = ((size_t)5ULL);
v___x_2481_ = lean_usize_shift_right(v_x_2469_, v___x_2480_);
v_x_2468_ = v_node_2479_;
v_x_2469_ = v___x_2481_;
goto _start;
}
default: 
{
uint8_t v___x_2483_; 
v___x_2483_ = 0;
return v___x_2483_;
}
}
}
else
{
lean_object* v_ks_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_ks_2484_ = lean_ctor_get(v_x_2468_, 0);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2484_, v___x_2485_, v_x_2470_);
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2487_, lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
size_t v_x_2208__boxed_2490_; uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_x_2208__boxed_2490_ = lean_unbox_usize(v_x_2488_);
lean_dec(v_x_2488_);
v_res_2491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2487_, v_x_2208__boxed_2490_, v_x_2489_);
lean_dec(v_x_2489_);
lean_dec_ref(v_x_2487_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
uint64_t v___x_2495_; size_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = l_Lean_instHashableMVarId_hash(v_x_2494_);
v___x_2496_ = lean_uint64_to_usize(v___x_2495_);
v___x_2497_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2493_, v___x_2496_, v_x_2494_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2498_, v_x_2499_);
lean_dec(v_x_2499_);
lean_dec_ref(v_x_2498_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; lean_object* v_mctx_2506_; lean_object* v_eAssignment_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2505_ = lean_st_ref_get(v___y_2503_);
v_mctx_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc_ref(v_mctx_2506_);
lean_dec(v___x_2505_);
v_eAssignment_2507_ = lean_ctor_get(v_mctx_2506_, 8);
lean_inc_ref(v_eAssignment_2507_);
lean_dec_ref(v_mctx_2506_);
v___x_2508_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2507_, v_mvarId_2502_);
lean_dec_ref(v_eAssignment_2507_);
v___x_2509_ = lean_box(v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec(v_mvarId_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2515_, lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
return v_x_2515_;
}
else
{
lean_object* v_head_2517_; lean_object* v_tail_2518_; lean_object* v___x_2519_; 
v_head_2517_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_head_2517_);
v_tail_2518_ = lean_ctor_get(v_x_2516_, 1);
lean_inc(v_tail_2518_);
lean_dec_ref_known(v_x_2516_, 2);
v___x_2519_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2515_, v_head_2517_);
v_x_2515_ = v___x_2519_;
v_x_2516_ = v_tail_2518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2521_, lean_object* v_a_2522_, uint8_t v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
if (lean_obj_tag(v_a_2524_) == 0)
{
if (lean_obj_tag(v_a_2525_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_a_2522_);
lean_dec_ref(v_f_2521_);
v___x_2532_ = lean_box(v_a_2523_);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_a_2526_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
else
{
lean_object* v_head_2535_; lean_object* v_tail_2536_; 
v_head_2535_ = lean_ctor_get(v_a_2525_, 0);
lean_inc(v_head_2535_);
v_tail_2536_ = lean_ctor_get(v_a_2525_, 1);
lean_inc(v_tail_2536_);
lean_dec_ref_known(v_a_2525_, 2);
v_a_2524_ = v_head_2535_;
v_a_2525_ = v_tail_2536_;
goto _start;
}
}
else
{
lean_object* v_head_2538_; lean_object* v_tail_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2582_; 
v_head_2538_ = lean_ctor_get(v_a_2524_, 0);
v_tail_2539_ = lean_ctor_get(v_a_2524_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2541_ = v_a_2524_;
v_isShared_2542_ = v_isSharedCheck_2582_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_tail_2539_);
lean_inc(v_head_2538_);
lean_dec(v_a_2524_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2582_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2581_; 
v___x_2543_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2538_, v___y_2528_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2581_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2581_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_unbox(v_a_2544_);
lean_dec(v_a_2544_);
if (v___x_2548_ == 0)
{
lean_object* v_zero_2549_; uint8_t v_isZero_2550_; 
v_zero_2549_ = lean_unsigned_to_nat(0u);
v_isZero_2550_ = lean_nat_dec_eq(v_a_2522_, v_zero_2549_);
if (v_isZero_2550_ == 1)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
lean_del_object(v___x_2541_);
lean_dec(v_a_2522_);
lean_dec_ref(v_f_2521_);
v___x_2551_ = lean_array_push(v_a_2526_, v_head_2538_);
v___x_2552_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2551_, v_tail_2539_);
v___x_2553_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2552_, v_a_2525_);
v___x_2554_ = lean_box(v_a_2523_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2555_);
v___x_2557_ = v___x_2546_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_del_object(v___x_2546_);
lean_inc_ref(v_f_2521_);
lean_inc(v_head_2538_);
v___x_2559_ = lean_apply_1(v_f_2521_, v_head_2538_);
v___x_2560_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2559_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v_one_2562_; lean_object* v_n_2563_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v_one_2562_ = lean_unsigned_to_nat(1u);
v_n_2563_ = lean_nat_sub(v_a_2522_, v_one_2562_);
lean_dec(v_a_2522_);
if (lean_obj_tag(v_a_2561_) == 0)
{
lean_object* v___x_2564_; 
lean_del_object(v___x_2541_);
v___x_2564_ = lean_array_push(v_a_2526_, v_head_2538_);
v_a_2522_ = v_n_2563_;
v_a_2524_ = v_tail_2539_;
v_a_2526_ = v___x_2564_;
goto _start;
}
else
{
lean_object* v_val_2566_; uint8_t v___x_2567_; lean_object* v___x_2569_; 
lean_dec(v_head_2538_);
v_val_2566_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_val_2566_);
lean_dec_ref_known(v_a_2561_, 1);
v___x_2567_ = 1;
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v_a_2525_);
lean_ctor_set(v___x_2541_, 0, v_tail_2539_);
v___x_2569_ = v___x_2541_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_tail_2539_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_a_2525_);
v___x_2569_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
v_a_2522_ = v_n_2563_;
v_a_2523_ = v___x_2567_;
v_a_2524_ = v_val_2566_;
v_a_2525_ = v___x_2569_;
goto _start;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_del_object(v___x_2541_);
lean_dec(v_tail_2539_);
lean_dec(v_head_2538_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec(v_a_2522_);
lean_dec_ref(v_f_2521_);
v_a_2572_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2560_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2560_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_del_object(v___x_2546_);
lean_del_object(v___x_2541_);
lean_dec(v_head_2538_);
v_a_2524_ = v_tail_2539_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v_a_2287__boxed_2594_; lean_object* v_res_2595_; 
v_a_2287__boxed_2594_ = lean_unbox(v_a_2585_);
v_res_2595_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2583_, v_a_2584_, v_a_2287__boxed_2594_, v_a_2586_, v_a_2587_, v_a_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2596_, size_t v_i_2597_, size_t v_stop_2598_, lean_object* v_b_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_a_2606_; uint8_t v___x_2610_; 
v___x_2610_ = lean_usize_dec_eq(v_i_2597_, v_stop_2598_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2614_; 
v___x_2611_ = lean_array_uget_borrowed(v_as_2596_, v_i_2597_);
v___x_2614_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2611_, v___y_2601_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; uint8_t v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = lean_unbox(v_a_2615_);
lean_dec(v_a_2615_);
if (v___x_2616_ == 0)
{
goto v___jp_2612_;
}
else
{
v_a_2606_ = v_b_2599_;
goto v___jp_2605_;
}
}
else
{
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2618_ = lean_unbox(v_a_2617_);
lean_dec(v_a_2617_);
if (v___x_2618_ == 0)
{
v_a_2606_ = v_b_2599_;
goto v___jp_2605_;
}
else
{
goto v___jp_2612_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_b_2599_);
v_a_2619_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2614_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2614_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
v___jp_2612_:
{
lean_object* v___x_2613_; 
lean_inc(v___x_2611_);
v___x_2613_ = lean_array_push(v_b_2599_, v___x_2611_);
v_a_2606_ = v___x_2613_;
goto v___jp_2605_;
}
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_b_2599_);
return v___x_2627_;
}
v___jp_2605_:
{
size_t v___x_2607_; size_t v___x_2608_; 
v___x_2607_ = ((size_t)1ULL);
v___x_2608_ = lean_usize_add(v_i_2597_, v___x_2607_);
v_i_2597_ = v___x_2608_;
v_b_2599_ = v_a_2606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2628_, lean_object* v_i_2629_, lean_object* v_stop_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_i_boxed_2637_; size_t v_stop_boxed_2638_; lean_object* v_res_2639_; 
v_i_boxed_2637_ = lean_unbox_usize(v_i_2629_);
lean_dec(v_i_2629_);
v_stop_boxed_2638_ = lean_unbox_usize(v_stop_2630_);
lean_dec(v_stop_2630_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2628_, v_i_boxed_2637_, v_stop_boxed_2638_, v_b_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec_ref(v_as_2628_);
return v_res_2639_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2643_ = lean_array_to_list(v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2644_, lean_object* v_goals_2645_, lean_object* v_maxIters_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2652_ = 0;
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2656_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2644_, v_maxIters_2646_, v___x_2652_, v_goals_2645_, v___x_2653_, v___x_2655_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2706_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2706_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2706_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2705_; 
v_fst_2661_ = lean_ctor_get(v_a_2657_, 0);
v_snd_2662_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2664_ = v_a_2657_;
v_isShared_2665_ = v_isSharedCheck_2705_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2662_);
lean_inc(v_fst_2661_);
lean_dec(v_a_2657_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2705_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_____do__lift_2667_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_array_get_size(v_snd_2662_);
v___x_2676_ = lean_nat_dec_lt(v___x_2654_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2664_);
lean_dec(v_snd_2662_);
lean_del_object(v___x_2659_);
v___x_2677_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_fst_2661_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
return v___x_2679_;
}
else
{
uint8_t v___x_2680_; 
v___x_2680_ = lean_nat_dec_le(v___x_2675_, v___x_2675_);
if (v___x_2680_ == 0)
{
if (v___x_2676_ == 0)
{
lean_dec(v_snd_2662_);
v_____do__lift_2667_ = v___x_2655_;
goto v___jp_2666_;
}
else
{
size_t v___x_2681_; size_t v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = lean_usize_of_nat(v___x_2675_);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2662_, v___x_2681_, v___x_2682_, v___x_2655_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v_snd_2662_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v_____do__lift_2667_ = v_a_2684_;
goto v___jp_2666_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2664_);
lean_dec(v_fst_2661_);
lean_del_object(v___x_2659_);
v_a_2685_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2683_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2683_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
else
{
size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = lean_usize_of_nat(v___x_2675_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2662_, v___x_2693_, v___x_2694_, v___x_2655_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v_snd_2662_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v_____do__lift_2667_ = v_a_2696_;
goto v___jp_2666_;
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_del_object(v___x_2664_);
lean_dec(v_fst_2661_);
lean_del_object(v___x_2659_);
v_a_2697_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2695_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2695_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_array_to_list(v_____do__lift_2667_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2668_);
v___x_2670_ = v___x_2664_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_fst_2661_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2670_);
v___x_2672_ = v___x_2659_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2656_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2656_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2715_, lean_object* v_goals_2716_, lean_object* v_maxIters_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2715_, v_goals_2716_, v_maxIters_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2727_, lean_object* v_goals_2728_, lean_object* v_maxIters_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2727_, v_goals_2728_, v_maxIters_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2748_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2748_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2748_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_fst_2740_; uint8_t v___x_2741_; 
v_fst_2740_ = lean_ctor_get(v_a_2736_, 0);
v___x_2741_ = lean_unbox(v_fst_2740_);
if (v___x_2741_ == 1)
{
lean_object* v_snd_2742_; lean_object* v___x_2744_; 
v_snd_2742_ = lean_ctor_get(v_a_2736_, 1);
lean_inc(v_snd_2742_);
lean_dec(v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v_snd_2742_);
v___x_2744_ = v___x_2738_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_snd_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2738_);
lean_dec(v_a_2736_);
v___x_2746_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2747_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2746_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2735_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2735_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2757_, lean_object* v_goals_2758_, lean_object* v_maxIters_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2757_, v_goals_2758_, v_maxIters_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2766_, lean_object* v_ctx_2767_, lean_object* v_cfg_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
uint8_t v_backtracking_2775_; 
v_backtracking_2775_ = lean_ctor_get_uint8(v_cfg_2768_, sizeof(void*)*1);
if (v_backtracking_2775_ == 0)
{
lean_object* v_toApplyRulesConfig_2776_; lean_object* v_toBacktrackConfig_2777_; lean_object* v_maxDepth_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_toApplyRulesConfig_2776_ = lean_ctor_get(v_cfg_2768_, 0);
v_toBacktrackConfig_2777_ = lean_ctor_get(v_toApplyRulesConfig_2776_, 0);
v_maxDepth_2778_ = lean_ctor_get(v_toBacktrackConfig_2777_, 0);
lean_inc(v_maxDepth_2778_);
v___x_2779_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2779_, 0, v_cfg_2768_);
lean_closure_set(v___x_2779_, 1, v_lemmas_2766_);
lean_closure_set(v___x_2779_, 2, v_ctx_2767_);
v___x_2780_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2779_, v_a_2769_, v_maxDepth_2778_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
return v___x_2780_;
}
else
{
lean_object* v_toApplyRulesConfig_2781_; lean_object* v_toBacktrackConfig_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_toApplyRulesConfig_2781_ = lean_ctor_get(v_cfg_2768_, 0);
v_toBacktrackConfig_2782_ = lean_ctor_get(v_toApplyRulesConfig_2781_, 0);
lean_inc_ref(v_toBacktrackConfig_2782_);
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2784_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2784_, 0, v_cfg_2768_);
lean_closure_set(v___x_2784_, 1, v_lemmas_2766_);
lean_closure_set(v___x_2784_, 2, v_ctx_2767_);
v___x_2785_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2782_, v___x_2783_, v___x_2784_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2786_, lean_object* v_ctx_2787_, lean_object* v_cfg_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2786_, v_ctx_2787_, v_cfg_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2796_, v___y_2798_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_mvarId_2803_);
return v_res_2809_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2811_, v_x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
uint8_t v_res_2817_; lean_object* v_r_2818_; 
v_res_2817_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2814_, v_x_2815_, v_x_2816_);
lean_dec(v_x_2816_);
lean_dec_ref(v_x_2815_);
v_r_2818_ = lean_box(v_res_2817_);
return v_r_2818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2819_, lean_object* v_x_2820_, size_t v_x_2821_, lean_object* v_x_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2820_, v_x_2821_, v_x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_){
_start:
{
size_t v_x_2747__boxed_2828_; uint8_t v_res_2829_; lean_object* v_r_2830_; 
v_x_2747__boxed_2828_ = lean_unbox_usize(v_x_2826_);
lean_dec(v_x_2826_);
v_res_2829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2824_, v_x_2825_, v_x_2747__boxed_2828_, v_x_2827_);
lean_dec(v_x_2827_);
lean_dec_ref(v_x_2825_);
v_r_2830_ = lean_box(v_res_2829_);
return v_r_2830_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2831_, lean_object* v_keys_2832_, lean_object* v_vals_2833_, lean_object* v_heq_2834_, lean_object* v_i_2835_, lean_object* v_k_2836_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2832_, v_i_2835_, v_k_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2838_, lean_object* v_keys_2839_, lean_object* v_vals_2840_, lean_object* v_heq_2841_, lean_object* v_i_2842_, lean_object* v_k_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2838_, v_keys_2839_, v_vals_2840_, v_heq_2841_, v_i_2842_, v_k_2843_);
lean_dec(v_k_2843_);
lean_dec_ref(v_vals_2840_);
lean_dec_ref(v_keys_2839_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_x_2857_);
return v_res_2863_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2866_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2867_ = l_Lean_Name_append(v___x_2866_, v___x_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2868_, lean_object* v_lemmas_2869_, lean_object* v_ctx_2870_, lean_object* v_goals_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_cfg_2877_; lean_object* v___x_2878_; 
v_cfg_2877_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2868_);
lean_inc(v_goals_2871_);
lean_inc_ref(v_cfg_2877_);
lean_inc_ref(v_ctx_2870_);
lean_inc(v_lemmas_2869_);
v___x_2878_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2869_, v_ctx_2870_, v_cfg_2877_, v_goals_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_dec_ref(v_cfg_2877_);
lean_dec(v_goals_2871_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v___f_2880_; lean_object* v___y_2882_; lean_object* v___y_2883_; uint8_t v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; lean_object* v_a_2889_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; lean_object* v___y_2908_; lean_object* v_a_2909_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; uint8_t v___y_2917_; lean_object* v___y_2918_; lean_object* v_a_2919_; lean_object* v___y_2929_; lean_object* v___y_2930_; uint8_t v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; uint8_t v___y_2934_; lean_object* v___y_2935_; lean_object* v_a_2936_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; uint8_t v___y_2981_; uint8_t v___x_3034_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
v___f_2880_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3034_ = l_Lean_Exception_isInterrupt(v_a_2879_);
if (v___x_3034_ == 0)
{
uint8_t v___x_3035_; 
v___x_3035_ = l_Lean_Exception_isRuntime(v_a_2879_);
v___y_2981_ = v___x_3035_;
goto v___jp_2980_;
}
else
{
lean_dec(v_a_2879_);
v___y_2981_ = v___x_3034_;
goto v___jp_2980_;
}
v___jp_2881_:
{
lean_object* v___x_2890_; double v___x_2891_; double v___x_2892_; double v___x_2893_; double v___x_2894_; double v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2890_ = lean_io_mono_nanos_now();
v___x_2891_ = lean_float_of_nat(v___y_2886_);
v___x_2892_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2893_ = lean_float_div(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_float_of_nat(v___x_2890_);
v___x_2895_ = lean_float_div(v___x_2894_, v___x_2892_);
v___x_2896_ = lean_box_float(v___x_2893_);
v___x_2897_ = lean_box_float(v___x_2895_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2889_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2885_);
v___x_2900_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2885_, v___y_2887_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2888_, v___f_2880_, v___x_2899_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2900_;
}
v___jp_2901_:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2909_);
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2903_;
v___y_2884_ = v___y_2904_;
v___y_2885_ = v___y_2905_;
v___y_2886_ = v___y_2906_;
v___y_2887_ = v___y_2907_;
v___y_2888_ = v___y_2908_;
v_a_2889_ = v___x_2910_;
goto v___jp_2881_;
}
v___jp_2911_:
{
lean_object* v___x_2920_; double v___x_2921_; double v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2920_ = lean_io_get_num_heartbeats();
v___x_2921_ = lean_float_of_nat(v___y_2916_);
v___x_2922_ = lean_float_of_nat(v___x_2920_);
v___x_2923_ = lean_box_float(v___x_2921_);
v___x_2924_ = lean_box_float(v___x_2922_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_a_2919_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2915_);
v___x_2927_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2915_, v___y_2917_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2918_, v___f_2880_, v___x_2926_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2927_;
}
v___jp_2928_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2936_);
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2930_;
v___y_2914_ = v___y_2931_;
v___y_2915_ = v___y_2932_;
v___y_2916_ = v___y_2933_;
v___y_2917_ = v___y_2934_;
v___y_2918_ = v___y_2935_;
v_a_2919_ = v___x_2937_;
goto v___jp_2911_;
}
v___jp_2938_:
{
lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2875_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v___x_2948_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2949_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2941_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_io_mono_nanos_now();
v___x_2951_ = l_Lean_MVarId_exfalso(v___y_2939_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_a_2952_);
lean_ctor_set(v___x_2953_, 1, v___y_2944_);
v___x_2954_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2869_, v_ctx_2870_, v_cfg_2877_, v___x_2953_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 1);
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v___y_2882_ = v___y_2940_;
v___y_2883_ = v___y_2941_;
v___y_2884_ = v___y_2942_;
v___y_2885_ = v___y_2943_;
v___y_2886_ = v___x_2950_;
v___y_2887_ = v___y_2945_;
v___y_2888_ = v_a_2947_;
v_a_2889_ = v___x_2960_;
goto v___jp_2881_;
}
}
}
else
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2954_, 1);
v___y_2902_ = v___y_2940_;
v___y_2903_ = v___y_2941_;
v___y_2904_ = v___y_2942_;
v___y_2905_ = v___y_2943_;
v___y_2906_ = v___x_2950_;
v___y_2907_ = v___y_2945_;
v___y_2908_ = v_a_2947_;
v_a_2909_ = v_a_2963_;
goto v___jp_2901_;
}
}
else
{
lean_object* v_a_2964_; 
lean_dec(v___y_2944_);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
v_a_2964_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2951_, 1);
v___y_2902_ = v___y_2940_;
v___y_2903_ = v___y_2941_;
v___y_2904_ = v___y_2942_;
v___y_2905_ = v___y_2943_;
v___y_2906_ = v___x_2950_;
v___y_2907_ = v___y_2945_;
v___y_2908_ = v_a_2947_;
v_a_2909_ = v_a_2964_;
goto v___jp_2901_;
}
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_io_get_num_heartbeats();
v___x_2966_ = l_Lean_MVarId_exfalso(v___y_2939_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2968_, 0, v_a_2967_);
lean_ctor_set(v___x_2968_, 1, v___y_2944_);
v___x_2969_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2869_, v_ctx_2870_, v_cfg_2877_, v___x_2968_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 1);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2912_ = v___y_2940_;
v___y_2913_ = v___y_2941_;
v___y_2914_ = v___y_2942_;
v___y_2915_ = v___y_2943_;
v___y_2916_ = v___x_2965_;
v___y_2917_ = v___y_2945_;
v___y_2918_ = v_a_2947_;
v_a_2919_ = v___x_2975_;
goto v___jp_2911_;
}
}
}
else
{
lean_object* v_a_2978_; 
v_a_2978_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2969_, 1);
v___y_2929_ = v___y_2940_;
v___y_2930_ = v___y_2941_;
v___y_2931_ = v___y_2942_;
v___y_2932_ = v___y_2943_;
v___y_2933_ = v___x_2965_;
v___y_2934_ = v___y_2945_;
v___y_2935_ = v_a_2947_;
v_a_2936_ = v_a_2978_;
goto v___jp_2928_;
}
}
else
{
lean_object* v_a_2979_; 
lean_dec(v___y_2944_);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
v_a_2979_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2966_, 1);
v___y_2929_ = v___y_2940_;
v___y_2930_ = v___y_2941_;
v___y_2931_ = v___y_2942_;
v___y_2932_ = v___y_2943_;
v___y_2933_ = v___x_2965_;
v___y_2934_ = v___y_2945_;
v___y_2935_ = v_a_2947_;
v_a_2936_ = v_a_2979_;
goto v___jp_2928_;
}
}
}
v___jp_2980_:
{
if (v___y_2981_ == 0)
{
if (lean_obj_tag(v_goals_2871_) == 1)
{
lean_object* v_tail_2982_; 
v_tail_2982_ = lean_ctor_get(v_goals_2871_, 1);
lean_inc(v_tail_2982_);
if (lean_obj_tag(v_tail_2982_) == 0)
{
lean_object* v_toApplyRulesConfig_2983_; uint8_t v_exfalso_2984_; 
v_toApplyRulesConfig_2983_ = lean_ctor_get(v_cfg_2877_, 0);
lean_inc_ref(v_toApplyRulesConfig_2983_);
v_exfalso_2984_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2983_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2983_);
if (v_exfalso_2984_ == 1)
{
lean_object* v_options_2985_; uint8_t v_hasTrace_2986_; 
lean_dec_ref_known(v___x_2878_, 1);
v_options_2985_ = lean_ctor_get(v_a_2874_, 2);
v_hasTrace_2986_ = lean_ctor_get_uint8(v_options_2985_, sizeof(void*)*1);
if (v_hasTrace_2986_ == 0)
{
lean_object* v_head_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3005_; 
v_head_2987_ = lean_ctor_get(v_goals_2871_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_goals_2871_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; 
v_unused_3006_ = lean_ctor_get(v_goals_2871_, 1);
lean_dec(v_unused_3006_);
v___x_2989_ = v_goals_2871_;
v_isShared_2990_ = v_isSharedCheck_3005_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_head_2987_);
lean_dec(v_goals_2871_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3005_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_MVarId_exfalso(v_head_2987_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v_a_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2992_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_tail_2982_);
v___x_2994_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2869_, v_ctx_2870_, v_cfg_2877_, v___x_2994_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2995_;
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_del_object(v___x_2989_);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
v_a_2997_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2991_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2991_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_object* v_head_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3032_; 
v_head_3007_ = lean_ctor_get(v_goals_2871_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_goals_2871_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v_goals_2871_, 1);
lean_dec(v_unused_3033_);
v___x_3009_ = v_goals_2871_;
v_isShared_3010_ = v_isSharedCheck_3032_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_head_3007_);
lean_dec(v_goals_2871_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3032_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_inheritedTraceOptions_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_inheritedTraceOptions_3011_ = lean_ctor_get(v_a_2874_, 13);
v___x_3012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3013_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3014_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3011_, v_options_2985_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = l_Lean_trace_profiler;
v___x_3017_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2985_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_MVarId_exfalso(v_head_3007_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_a_3019_);
v___x_3021_ = v___x_3009_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3019_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_tail_2982_);
v___x_3021_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2869_, v_ctx_2870_, v_cfg_2877_, v___x_3021_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_3022_;
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_del_object(v___x_3009_);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
v_a_3024_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3018_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3018_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_del_object(v___x_3009_);
v___y_2939_ = v_head_3007_;
v___y_2940_ = v___x_3013_;
v___y_2941_ = v_options_2985_;
v___y_2942_ = v___x_3015_;
v___y_2943_ = v___x_3012_;
v___y_2944_ = v_tail_2982_;
v___y_2945_ = v_exfalso_2984_;
goto v___jp_2938_;
}
}
else
{
lean_del_object(v___x_3009_);
v___y_2939_ = v_head_3007_;
v___y_2940_ = v___x_3013_;
v___y_2941_ = v_options_2985_;
v___y_2942_ = v___x_3015_;
v___y_2943_ = v___x_3012_;
v___y_2944_ = v_tail_2982_;
v___y_2945_ = v_exfalso_2984_;
goto v___jp_2938_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2871_, 2);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
return v___x_2878_;
}
}
else
{
lean_dec(v_tail_2982_);
lean_dec_ref_known(v_goals_2871_, 2);
lean_dec_ref(v_cfg_2877_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
return v___x_2878_;
}
}
else
{
lean_dec_ref(v_cfg_2877_);
lean_dec(v_goals_2871_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
return v___x_2878_;
}
}
else
{
lean_dec_ref(v_cfg_2877_);
lean_dec(v_goals_2871_);
lean_dec_ref(v_ctx_2870_);
lean_dec(v_lemmas_2869_);
return v___x_2878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3036_, lean_object* v_lemmas_3037_, lean_object* v_ctx_3038_, lean_object* v_goals_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3036_, v_lemmas_3037_, v_ctx_3038_, v_goals_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = l_List_reverse___redArg(v_x_3047_);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
else
{
lean_object* v_head_3055_; lean_object* v_tail_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3079_; 
v_head_3055_ = lean_ctor_get(v_x_3046_, 0);
v_tail_3056_ = lean_ctor_get(v_x_3046_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_x_3046_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3058_ = v_x_3046_;
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_tail_3056_);
lean_inc(v_head_3055_);
lean_dec(v_x_3046_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3079_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Expr_applySymm(v_head_3055_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v_x_3047_);
lean_ctor_set(v___x_3058_, 0, v_a_3061_);
v___x_3063_ = v___x_3058_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3061_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_x_3047_);
v___x_3063_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
v_x_3046_ = v_tail_3056_;
v_x_3047_ = v___x_3063_;
goto _start;
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3078_; 
lean_del_object(v___x_3058_);
v_a_3066_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3068_ = v___x_3060_;
v_isShared_3069_ = v_isSharedCheck_3078_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3060_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3078_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
uint8_t v___y_3071_; uint8_t v___x_3076_; 
v___x_3076_ = l_Lean_Exception_isInterrupt(v_a_3066_);
if (v___x_3076_ == 0)
{
uint8_t v___x_3077_; 
lean_inc(v_a_3066_);
v___x_3077_ = l_Lean_Exception_isRuntime(v_a_3066_);
v___y_3071_ = v___x_3077_;
goto v___jp_3070_;
}
else
{
v___y_3071_ = v___x_3076_;
goto v___jp_3070_;
}
v___jp_3070_:
{
if (v___y_3071_ == 0)
{
lean_del_object(v___x_3068_);
lean_dec(v_a_3066_);
v_x_3046_ = v_tail_3056_;
goto _start;
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_tail_3056_);
lean_dec(v_x_3047_);
if (v_isShared_3069_ == 0)
{
v___x_3074_ = v___x_3068_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3066_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3080_, v_x_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3088_, lean_object* v_hyps_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
if (v_symm_3088_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_hyps_3089_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_box(0);
lean_inc(v_hyps_3089_);
v___x_3097_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3089_, v___x_3096_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3106_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = l_List_appendTR___redArg(v_hyps_3089_, v_a_3098_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_dec(v_hyps_3089_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3107_, lean_object* v_hyps_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_symm_boxed_3114_; lean_object* v_res_3115_; 
v_symm_boxed_3114_ = lean_unbox(v_symm_3107_);
v_res_3115_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3114_, v_hyps_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3116_, size_t v_sz_3117_, size_t v_i_3118_, lean_object* v_b_3119_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_usize_dec_lt(v_i_3118_, v_sz_3117_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_b_3119_);
return v___x_3122_;
}
else
{
lean_object* v_snd_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3141_; 
v_snd_3123_ = lean_ctor_get(v_b_3119_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_b_3119_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v_b_3119_, 0);
lean_dec(v_unused_3142_);
v___x_3125_ = v_b_3119_;
v_isShared_3126_ = v_isSharedCheck_3141_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_snd_3123_);
lean_dec(v_b_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3141_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v_a_3129_; lean_object* v_a_3136_; 
v___x_3127_ = lean_box(0);
v_a_3136_ = lean_array_uget_borrowed(v_as_3116_, v_i_3118_);
if (lean_obj_tag(v_a_3136_) == 0)
{
v_a_3129_ = v_snd_3123_;
goto v___jp_3128_;
}
else
{
lean_object* v_val_3137_; uint8_t v___x_3138_; 
v_val_3137_ = lean_ctor_get(v_a_3136_, 0);
v___x_3138_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_inc(v_val_3137_);
v___x_3139_ = l_Lean_LocalDecl_toExpr(v_val_3137_);
v___x_3140_ = lean_array_push(v_snd_3123_, v___x_3139_);
v_a_3129_ = v___x_3140_;
goto v___jp_3128_;
}
else
{
v_a_3129_ = v_snd_3123_;
goto v___jp_3128_;
}
}
v___jp_3128_:
{
lean_object* v___x_3131_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v_a_3129_);
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3131_ = v___x_3125_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_a_3129_);
v___x_3131_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
size_t v___x_3132_; size_t v___x_3133_; 
v___x_3132_ = ((size_t)1ULL);
v___x_3133_ = lean_usize_add(v_i_3118_, v___x_3132_);
v_i_3118_ = v___x_3133_;
v_b_3119_ = v___x_3131_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3143_, lean_object* v_sz_3144_, lean_object* v_i_3145_, lean_object* v_b_3146_, lean_object* v___y_3147_){
_start:
{
size_t v_sz_boxed_3148_; size_t v_i_boxed_3149_; lean_object* v_res_3150_; 
v_sz_boxed_3148_ = lean_unbox_usize(v_sz_3144_);
lean_dec(v_sz_3144_);
v_i_boxed_3149_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3143_, v_sz_boxed_3148_, v_i_boxed_3149_, v_b_3146_);
lean_dec_ref(v_as_3143_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3151_, size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_b_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_b_3154_);
return v___x_3163_;
}
else
{
lean_object* v_snd_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3182_; 
v_snd_3164_ = lean_ctor_get(v_b_3154_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_b_3154_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_b_3154_, 0);
lean_dec(v_unused_3183_);
v___x_3166_ = v_b_3154_;
v_isShared_3167_ = v_isSharedCheck_3182_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_snd_3164_);
lean_dec(v_b_3154_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3182_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v_a_3170_; lean_object* v_a_3177_; 
v___x_3168_ = lean_box(0);
v_a_3177_ = lean_array_uget_borrowed(v_as_3151_, v_i_3153_);
if (lean_obj_tag(v_a_3177_) == 0)
{
v_a_3170_ = v_snd_3164_;
goto v___jp_3169_;
}
else
{
lean_object* v_val_3178_; uint8_t v___x_3179_; 
v_val_3178_ = lean_ctor_get(v_a_3177_, 0);
v___x_3179_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc(v_val_3178_);
v___x_3180_ = l_Lean_LocalDecl_toExpr(v_val_3178_);
v___x_3181_ = lean_array_push(v_snd_3164_, v___x_3180_);
v_a_3170_ = v___x_3181_;
goto v___jp_3169_;
}
else
{
v_a_3170_ = v_snd_3164_;
goto v___jp_3169_;
}
}
v___jp_3169_:
{
lean_object* v___x_3172_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 1, v_a_3170_);
lean_ctor_set(v___x_3166_, 0, v___x_3168_);
v___x_3172_ = v___x_3166_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_a_3170_);
v___x_3172_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((size_t)1ULL);
v___x_3174_ = lean_usize_add(v_i_3153_, v___x_3173_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3151_, v_sz_3152_, v___x_3174_, v___x_3172_);
return v___x_3175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3184_, lean_object* v_sz_3185_, lean_object* v_i_3186_, lean_object* v_b_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
size_t v_sz_boxed_3195_; size_t v_i_boxed_3196_; lean_object* v_res_3197_; 
v_sz_boxed_3195_ = lean_unbox_usize(v_sz_3185_);
lean_dec(v_sz_3185_);
v_i_boxed_3196_ = lean_unbox_usize(v_i_3186_);
lean_dec(v_i_3186_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3184_, v_sz_boxed_3195_, v_i_boxed_3196_, v_b_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_as_3184_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3198_, size_t v_sz_3199_, size_t v_i_3200_, lean_object* v_b_3201_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_lt(v_i_3200_, v_sz_3199_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_b_3201_);
return v___x_3204_;
}
else
{
lean_object* v_snd_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3223_; 
v_snd_3205_ = lean_ctor_get(v_b_3201_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_b_3201_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_b_3201_, 0);
lean_dec(v_unused_3224_);
v___x_3207_ = v_b_3201_;
v_isShared_3208_ = v_isSharedCheck_3223_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snd_3205_);
lean_dec(v_b_3201_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3223_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v_a_3211_; lean_object* v_a_3218_; 
v___x_3209_ = lean_box(0);
v_a_3218_ = lean_array_uget_borrowed(v_as_3198_, v_i_3200_);
if (lean_obj_tag(v_a_3218_) == 0)
{
v_a_3211_ = v_snd_3205_;
goto v___jp_3210_;
}
else
{
lean_object* v_val_3219_; uint8_t v___x_3220_; 
v_val_3219_ = lean_ctor_get(v_a_3218_, 0);
v___x_3220_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_val_3219_);
v___x_3221_ = l_Lean_LocalDecl_toExpr(v_val_3219_);
v___x_3222_ = lean_array_push(v_snd_3205_, v___x_3221_);
v_a_3211_ = v___x_3222_;
goto v___jp_3210_;
}
else
{
v_a_3211_ = v_snd_3205_;
goto v___jp_3210_;
}
}
v___jp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v_a_3211_);
lean_ctor_set(v___x_3207_, 0, v___x_3209_);
v___x_3213_ = v___x_3207_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_a_3211_);
v___x_3213_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
size_t v___x_3214_; size_t v___x_3215_; 
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_add(v_i_3200_, v___x_3214_);
v_i_3200_ = v___x_3215_;
v_b_3201_ = v___x_3213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_){
_start:
{
size_t v_sz_boxed_3230_; size_t v_i_boxed_3231_; lean_object* v_res_3232_; 
v_sz_boxed_3230_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3231_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3225_, v_sz_boxed_3230_, v_i_boxed_3231_, v_b_3228_);
lean_dec_ref(v_as_3225_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3233_, size_t v_sz_3234_, size_t v_i_3235_, lean_object* v_b_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3235_, v_sz_3234_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_b_3236_);
return v___x_3245_;
}
else
{
lean_object* v_snd_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3264_; 
v_snd_3246_ = lean_ctor_get(v_b_3236_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_b_3236_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_b_3236_, 0);
lean_dec(v_unused_3265_);
v___x_3248_ = v_b_3236_;
v_isShared_3249_ = v_isSharedCheck_3264_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snd_3246_);
lean_dec(v_b_3236_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3264_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v_a_3252_; lean_object* v_a_3259_; 
v___x_3250_ = lean_box(0);
v_a_3259_ = lean_array_uget_borrowed(v_as_3233_, v_i_3235_);
if (lean_obj_tag(v_a_3259_) == 0)
{
v_a_3252_ = v_snd_3246_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3260_; uint8_t v___x_3261_; 
v_val_3260_ = lean_ctor_get(v_a_3259_, 0);
v___x_3261_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_inc(v_val_3260_);
v___x_3262_ = l_Lean_LocalDecl_toExpr(v_val_3260_);
v___x_3263_ = lean_array_push(v_snd_3246_, v___x_3262_);
v_a_3252_ = v___x_3263_;
goto v___jp_3251_;
}
else
{
v_a_3252_ = v_snd_3246_;
goto v___jp_3251_;
}
}
v___jp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v_a_3252_);
lean_ctor_set(v___x_3248_, 0, v___x_3250_);
v___x_3254_ = v___x_3248_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_a_3252_);
v___x_3254_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((size_t)1ULL);
v___x_3256_ = lean_usize_add(v_i_3235_, v___x_3255_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3233_, v_sz_3234_, v___x_3256_, v___x_3254_);
return v___x_3257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3266_, lean_object* v_sz_3267_, lean_object* v_i_3268_, lean_object* v_b_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
size_t v_sz_boxed_3277_; size_t v_i_boxed_3278_; lean_object* v_res_3279_; 
v_sz_boxed_3277_ = lean_unbox_usize(v_sz_3267_);
lean_dec(v_sz_3267_);
v_i_boxed_3278_ = lean_unbox_usize(v_i_3268_);
lean_dec(v_i_3268_);
v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3266_, v_sz_boxed_3277_, v_i_boxed_3278_, v_b_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec_ref(v_as_3266_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3280_, lean_object* v_n_3281_, lean_object* v_b_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
if (lean_obj_tag(v_n_3281_) == 0)
{
lean_object* v_cs_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; size_t v_sz_3293_; size_t v___x_3294_; lean_object* v___x_3295_; 
v_cs_3290_ = lean_ctor_get(v_n_3281_, 0);
v___x_3291_ = lean_box(0);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
lean_ctor_set(v___x_3292_, 1, v_b_3282_);
v_sz_3293_ = lean_array_size(v_cs_3290_);
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3280_, v_cs_3290_, v_sz_3293_, v___x_3294_, v___x_3292_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3310_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3310_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3310_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v_fst_3300_; 
v_fst_3300_ = lean_ctor_get(v_a_3296_, 0);
if (lean_obj_tag(v_fst_3300_) == 0)
{
lean_object* v_snd_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v_snd_3301_ = lean_ctor_get(v_a_3296_, 1);
lean_inc(v_snd_3301_);
lean_dec(v_a_3296_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v_snd_3301_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3302_);
v___x_3304_ = v___x_3298_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
else
{
lean_object* v_val_3306_; lean_object* v___x_3308_; 
lean_inc_ref(v_fst_3300_);
lean_dec(v_a_3296_);
v_val_3306_ = lean_ctor_get(v_fst_3300_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v_fst_3300_, 1);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v_val_3306_);
v___x_3308_ = v___x_3298_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_val_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
v_a_3311_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3295_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3295_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_vs_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; size_t v_sz_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
v_vs_3319_ = lean_ctor_get(v_n_3281_, 0);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v_b_3282_);
v_sz_3322_ = lean_array_size(v_vs_3319_);
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3319_, v_sz_3322_, v___x_3323_, v___x_3321_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3339_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3339_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3339_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_fst_3329_; 
v_fst_3329_ = lean_ctor_get(v_a_3325_, 0);
if (lean_obj_tag(v_fst_3329_) == 0)
{
lean_object* v_snd_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v_snd_3330_ = lean_ctor_get(v_a_3325_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_a_3325_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_snd_3330_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3331_);
v___x_3333_ = v___x_3327_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
lean_object* v_val_3335_; lean_object* v___x_3337_; 
lean_inc_ref(v_fst_3329_);
lean_dec(v_a_3325_);
v_val_3335_ = lean_ctor_get(v_fst_3329_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v_fst_3329_, 1);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v_val_3335_);
v___x_3337_ = v___x_3327_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_val_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3324_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3324_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3348_, lean_object* v_as_3349_, size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_b_3352_);
return v___x_3361_;
}
else
{
lean_object* v_snd_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3396_; 
v_snd_3362_ = lean_ctor_get(v_b_3352_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_b_3352_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v_b_3352_, 0);
lean_dec(v_unused_3397_);
v___x_3364_ = v_b_3352_;
v_isShared_3365_ = v_isSharedCheck_3396_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_snd_3362_);
lean_dec(v_b_3352_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3396_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_a_3366_; lean_object* v___x_3367_; 
v_a_3366_ = lean_array_uget_borrowed(v_as_3349_, v_i_3351_);
lean_inc(v_snd_3362_);
v___x_3367_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3348_, v_a_3366_, v_snd_3362_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3387_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3387_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3387_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
if (lean_obj_tag(v_a_3368_) == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_a_3368_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3372_);
v___x_3374_ = v___x_3364_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_snd_3362_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3376_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3374_);
v___x_3376_ = v___x_3370_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
lean_del_object(v___x_3370_);
lean_dec(v_snd_3362_);
v_a_3379_ = lean_ctor_get(v_a_3368_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v_a_3368_, 1);
v___x_3380_ = lean_box(0);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v_a_3379_);
lean_ctor_set(v___x_3364_, 0, v___x_3380_);
v___x_3382_ = v___x_3364_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_a_3379_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
size_t v___x_3383_; size_t v___x_3384_; 
v___x_3383_ = ((size_t)1ULL);
v___x_3384_ = lean_usize_add(v_i_3351_, v___x_3383_);
v_i_3351_ = v___x_3384_;
v_b_3352_ = v___x_3382_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_del_object(v___x_3364_);
lean_dec(v_snd_3362_);
v_a_3388_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3367_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3367_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3398_, lean_object* v_as_3399_, lean_object* v_sz_3400_, lean_object* v_i_3401_, lean_object* v_b_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
size_t v_sz_boxed_3410_; size_t v_i_boxed_3411_; lean_object* v_res_3412_; 
v_sz_boxed_3410_ = lean_unbox_usize(v_sz_3400_);
lean_dec(v_sz_3400_);
v_i_boxed_3411_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_res_3412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3398_, v_as_3399_, v_sz_boxed_3410_, v_i_boxed_3411_, v_b_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec_ref(v_as_3399_);
lean_dec_ref(v_init_3398_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3413_, lean_object* v_n_3414_, lean_object* v_b_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3413_, v_n_3414_, v_b_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v_n_3414_);
lean_dec_ref(v_init_3413_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3424_, lean_object* v_init_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_root_3433_; lean_object* v_tail_3434_; lean_object* v___x_3435_; 
v_root_3433_ = lean_ctor_get(v_t_3424_, 0);
v_tail_3434_ = lean_ctor_get(v_t_3424_, 1);
lean_inc_ref(v_init_3425_);
v___x_3435_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3425_, v_root_3433_, v_init_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec_ref(v_init_3425_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3472_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3472_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3472_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_a_3436_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; 
v_a_3440_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v_a_3436_, 1);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v_a_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v_sz_3447_; size_t v___x_3448_; lean_object* v___x_3449_; 
lean_del_object(v___x_3438_);
v_a_3444_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v_a_3436_, 1);
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v_a_3444_);
v_sz_3447_ = lean_array_size(v_tail_3434_);
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3434_, v_sz_3447_, v___x_3448_, v___x_3446_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3463_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_fst_3454_; 
v_fst_3454_ = lean_ctor_get(v_a_3450_, 0);
if (lean_obj_tag(v_fst_3454_) == 0)
{
lean_object* v_snd_3455_; lean_object* v___x_3457_; 
v_snd_3455_ = lean_ctor_get(v_a_3450_, 1);
lean_inc(v_snd_3455_);
lean_dec(v_a_3450_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_snd_3455_);
v___x_3457_ = v___x_3452_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_snd_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v_val_3459_; lean_object* v___x_3461_; 
lean_inc_ref(v_fst_3454_);
lean_dec(v_a_3450_);
v_val_3459_ = lean_ctor_get(v_fst_3454_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v_fst_3454_, 1);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v_val_3459_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_val_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3449_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3449_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
v_a_3473_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3435_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3435_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3481_, lean_object* v_init_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3481_, v_init_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v_t_3481_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_lctx_3500_; lean_object* v_decls_3501_; lean_object* v_hs_3502_; lean_object* v___x_3503_; 
v_lctx_3500_ = lean_ctor_get(v___y_3495_, 2);
v_decls_3501_ = lean_ctor_get(v_lctx_3500_, 1);
v_hs_3502_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3503_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3501_, v_hs_3502_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3512_, lean_object* v_cfg_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
if (v_only_3512_ == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_toApplyRulesConfig_3522_; lean_object* v_a_3523_; uint8_t v_symm_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_toApplyRulesConfig_3522_ = lean_ctor_get(v_cfg_3513_, 0);
v_a_3523_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3521_, 1);
v_symm_3524_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3522_, sizeof(void*)*2 + 1);
v___x_3525_ = lean_array_to_list(v_a_3523_);
v___x_3526_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3524_, v___x_3525_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3526_;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
v_a_3527_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3521_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3521_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_box(0);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3537_, lean_object* v_cfg_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v_only_boxed_3546_; lean_object* v_res_3547_; 
v_only_boxed_3546_ = lean_unbox(v_only_3537_);
v_res_3547_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3546_, v_cfg_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v_cfg_3538_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3548_, lean_object* v_lemmas_3549_, uint8_t v_only_3550_, lean_object* v_g_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_toApplyRulesConfig_3557_; uint8_t v_intro_3558_; uint8_t v_constructor_3559_; uint8_t v_suggestions_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3573_; 
v_toApplyRulesConfig_3557_ = lean_ctor_get(v_cfg_3548_, 0);
v_intro_3558_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*1 + 1);
v_constructor_3559_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*1 + 2);
v_suggestions_3560_ = lean_ctor_get_uint8(v_cfg_3548_, sizeof(void*)*1 + 3);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_cfg_3548_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3562_ = v_cfg_3548_;
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_toApplyRulesConfig_3557_);
lean_dec(v_cfg_3548_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3573_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v_ctx_3565_; uint8_t v___x_3566_; lean_object* v___x_3568_; 
v___x_3564_ = lean_box(v_only_3550_);
v_ctx_3565_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3565_, 0, v___x_3564_);
v___x_3566_ = 0;
if (v_isShared_3563_ == 0)
{
v___x_3568_ = v___x_3562_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_toApplyRulesConfig_3557_);
lean_ctor_set_uint8(v_reuseFailAlloc_3572_, sizeof(void*)*1 + 1, v_intro_3558_);
lean_ctor_set_uint8(v_reuseFailAlloc_3572_, sizeof(void*)*1 + 2, v_constructor_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3572_, sizeof(void*)*1 + 3, v_suggestions_3560_);
v___x_3568_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*1, v___x_3566_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_g_3551_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3568_, v_lemmas_3549_, v_ctx_3565_, v___x_3570_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3574_, lean_object* v_lemmas_3575_, lean_object* v_only_3576_, lean_object* v_g_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
uint8_t v_only_boxed_3583_; lean_object* v_res_3584_; 
v_only_boxed_3583_ = lean_unbox(v_only_3576_);
v_res_3584_ = l_Lean_MVarId_applyRules(v_cfg_3574_, v_lemmas_3575_, v_only_boxed_3583_, v_g_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3585_, size_t v_sz_3586_, size_t v_i_3587_, lean_object* v_b_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3585_, v_sz_3586_, v_i_3587_, v_b_3588_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3597_, lean_object* v_sz_3598_, lean_object* v_i_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
size_t v_sz_boxed_3608_; size_t v_i_boxed_3609_; lean_object* v_res_3610_; 
v_sz_boxed_3608_ = lean_unbox_usize(v_sz_3598_);
lean_dec(v_sz_3598_);
v_i_boxed_3609_ = lean_unbox_usize(v_i_3599_);
lean_dec(v_i_3599_);
v_res_3610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3597_, v_sz_boxed_3608_, v_i_boxed_3609_, v_b_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v_as_3597_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3611_, size_t v_sz_3612_, size_t v_i_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3611_, v_sz_3612_, v_i_3613_, v_b_3614_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3623_, lean_object* v_sz_3624_, lean_object* v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_sz_boxed_3634_; size_t v_i_boxed_3635_; lean_object* v_res_3636_; 
v_sz_boxed_3634_ = lean_unbox_usize(v_sz_3624_);
lean_dec(v_sz_3624_);
v_i_boxed_3635_ = lean_unbox_usize(v_i_3625_);
lean_dec(v_i_3625_);
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3623_, v_sz_boxed_3634_, v_i_boxed_3635_, v_b_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_as_3623_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___x_3645_; uint8_t v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_box(0);
v___x_3646_ = 1;
v___x_3647_ = l_Lean_Elab_Term_elabTerm(v_t_3637_, v___x_3645_, v___x_3646_, v___x_3646_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_ref_3662_; uint8_t v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v_ref_3662_ = lean_ctor_get(v___y_3659_, 5);
v___x_3663_ = 0;
v___x_3664_ = l_Lean_SourceInfo_fromRef(v_ref_3662_, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3671_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3672_, lean_object* v_x_3673_){
_start:
{
if (lean_obj_tag(v_x_3673_) == 0)
{
uint8_t v___x_3674_; 
v___x_3674_ = 0;
return v___x_3674_;
}
else
{
lean_object* v_head_3675_; lean_object* v_tail_3676_; uint8_t v___x_3677_; 
v_head_3675_ = lean_ctor_get(v_x_3673_, 0);
v_tail_3676_ = lean_ctor_get(v_x_3673_, 1);
v___x_3677_ = lean_expr_eqv(v_a_3672_, v_head_3675_);
if (v___x_3677_ == 0)
{
v_x_3673_ = v_tail_3676_;
goto _start;
}
else
{
return v___x_3677_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3679_, lean_object* v_x_3680_){
_start:
{
uint8_t v_res_3681_; lean_object* v_r_3682_; 
v_res_3681_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3679_, v_x_3680_);
lean_dec(v_x_3680_);
lean_dec_ref(v_a_3679_);
v_r_3682_ = lean_box(v_res_3681_);
return v_r_3682_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3683_, lean_object* v_x_3684_){
_start:
{
uint8_t v___x_3685_; 
v___x_3685_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3684_, v_ys_3683_);
if (v___x_3685_ == 0)
{
uint8_t v___x_3686_; 
v___x_3686_ = 1;
return v___x_3686_;
}
else
{
uint8_t v___x_3687_; 
v___x_3687_ = 0;
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3688_, lean_object* v_x_3689_){
_start:
{
uint8_t v_res_3690_; lean_object* v_r_3691_; 
v_res_3690_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3688_, v_x_3689_);
lean_dec_ref(v_x_3689_);
lean_dec(v_ys_3688_);
v_r_3691_ = lean_box(v_res_3690_);
return v_r_3691_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3692_, lean_object* v_ys_3693_){
_start:
{
lean_object* v___f_3694_; lean_object* v___x_3695_; 
v___f_3694_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3694_, 0, v_ys_3693_);
v___x_3695_ = l_List_filter___redArg(v___f_3694_, v_xs_3692_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3696_, lean_object* v_x_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
if (lean_obj_tag(v_x_3696_) == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = l_List_reverse___redArg(v_x_3697_);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
else
{
lean_object* v_head_3707_; lean_object* v_tail_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3726_; 
v_head_3707_ = lean_ctor_get(v_x_3696_, 0);
v_tail_3708_ = lean_ctor_get(v_x_3696_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_x_3696_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3710_ = v_x_3696_;
v_isShared_3711_ = v_isSharedCheck_3726_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_tail_3708_);
lean_inc(v_head_3707_);
lean_dec(v_x_3696_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3726_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; 
v___x_3712_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3707_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v_x_3697_);
lean_ctor_set(v___x_3710_, 0, v_a_3713_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3713_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_x_3697_);
v___x_3715_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
v_x_3696_ = v_tail_3708_;
v_x_3697_ = v___x_3715_;
goto _start;
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3710_);
lean_dec(v_tail_3708_);
lean_dec(v_x_3697_);
v_a_3718_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3712_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3712_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3727_, lean_object* v_x_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3727_, v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3737_, uint8_t v_noDefaults_3738_, uint8_t v_star_3739_, lean_object* v_cfg_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
if (v_noDefaults_3738_ == 0)
{
goto v___jp_3748_;
}
else
{
if (v_star_3739_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec(v_remove_3737_);
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
else
{
goto v___jp_3748_;
}
}
v___jp_3748_:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
v___x_3751_ = lean_box(0);
v___x_3752_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3737_, v___x_3751_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_toApplyRulesConfig_3753_; lean_object* v_a_3754_; uint8_t v_symm_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_toApplyRulesConfig_3753_ = lean_ctor_get(v_cfg_3740_, 0);
v_a_3754_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3752_, 1);
v_symm_3755_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3753_, sizeof(void*)*2 + 1);
v___x_3756_ = lean_array_to_list(v_a_3750_);
v___x_3757_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3756_, v_a_3754_);
v___x_3758_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3755_, v___x_3757_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3758_;
}
else
{
lean_dec(v_a_3750_);
return v___x_3752_;
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v_remove_3737_);
v_a_3759_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3749_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3749_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3769_, lean_object* v_noDefaults_3770_, lean_object* v_star_3771_, lean_object* v_cfg_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
uint8_t v_noDefaults_boxed_3780_; uint8_t v_star_boxed_3781_; lean_object* v_res_3782_; 
v_noDefaults_boxed_3780_ = lean_unbox(v_noDefaults_3770_);
v_star_boxed_3781_ = lean_unbox(v_star_3771_);
v_res_3782_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3769_, v_noDefaults_boxed_3780_, v_star_boxed_3781_, v_cfg_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec_ref(v_cfg_3772_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3783_, size_t v_i_3784_, size_t v_stop_3785_, lean_object* v_b_3786_){
_start:
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_usize_dec_eq(v_i_3784_, v_stop_3785_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; size_t v___x_3790_; size_t v___x_3791_; 
v___x_3788_ = lean_array_uget_borrowed(v_as_3783_, v_i_3784_);
v___x_3789_ = l_Array_append___redArg(v_b_3786_, v___x_3788_);
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3784_, v___x_3790_);
v_i_3784_ = v___x_3791_;
v_b_3786_ = v___x_3789_;
goto _start;
}
else
{
return v_b_3786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3793_, lean_object* v_i_3794_, lean_object* v_stop_3795_, lean_object* v_b_3796_){
_start:
{
size_t v_i_boxed_3797_; size_t v_stop_boxed_3798_; lean_object* v_res_3799_; 
v_i_boxed_3797_ = lean_unbox_usize(v_i_3794_);
lean_dec(v_i_3794_);
v_stop_boxed_3798_ = lean_unbox_usize(v_stop_3795_);
lean_dec(v_stop_3795_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3793_, v_i_boxed_3797_, v_stop_boxed_3798_, v_b_3796_);
lean_dec_ref(v_as_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
if (lean_obj_tag(v_a_3800_) == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = l_List_reverse___redArg(v_a_3801_);
return v___x_3802_;
}
else
{
lean_object* v_head_3803_; lean_object* v_tail_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3813_; 
v_head_3803_ = lean_ctor_get(v_a_3800_, 0);
v_tail_3804_ = lean_ctor_get(v_a_3800_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3806_ = v_a_3800_;
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_tail_3804_);
lean_inc(v_head_3803_);
lean_dec(v_a_3800_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3808_, 0, v_head_3803_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v_a_3801_);
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_a_3801_);
v___x_3810_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v_a_3800_ = v_tail_3804_;
v_a_3801_ = v___x_3810_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3814_, size_t v_i_3815_, lean_object* v_bs_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
uint8_t v___x_3820_; 
v___x_3820_ = lean_usize_dec_lt(v_i_3815_, v_sz_3814_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_bs_3816_);
return v___x_3821_;
}
else
{
lean_object* v_v_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_v_3822_ = lean_array_uget_borrowed(v_bs_3816_, v_i_3815_);
v___x_3823_ = l_Lean_Syntax_getId(v_v_3822_);
v___x_3824_ = l_Lean_labelled(v___x_3823_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v_bs_x27_3827_; size_t v___x_3828_; size_t v___x_3829_; lean_object* v___x_3830_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = lean_unsigned_to_nat(0u);
v_bs_x27_3827_ = lean_array_uset(v_bs_3816_, v_i_3815_, v___x_3826_);
v___x_3828_ = ((size_t)1ULL);
v___x_3829_ = lean_usize_add(v_i_3815_, v___x_3828_);
v___x_3830_ = lean_array_uset(v_bs_x27_3827_, v_i_3815_, v_a_3825_);
v_i_3815_ = v___x_3829_;
v_bs_3816_ = v___x_3830_;
goto _start;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v_bs_3816_);
v_a_3832_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3824_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3824_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3840_, lean_object* v_i_3841_, lean_object* v_bs_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
size_t v_sz_boxed_3846_; size_t v_i_boxed_3847_; lean_object* v_res_3848_; 
v_sz_boxed_3846_ = lean_unbox_usize(v_sz_3840_);
lean_dec(v_sz_3840_);
v_i_boxed_3847_ = lean_unbox_usize(v_i_3841_);
lean_dec(v_i_3841_);
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3846_, v_i_boxed_3847_, v_bs_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3849_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
if (lean_obj_tag(v_a_3867_) == 0)
{
lean_object* v___x_3869_; 
v___x_3869_ = l_List_reverse___redArg(v_a_3868_);
return v___x_3869_;
}
else
{
lean_object* v_head_3870_; lean_object* v_tail_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3880_; 
v_head_3870_ = lean_ctor_get(v_a_3867_, 0);
v_tail_3871_ = lean_ctor_get(v_a_3867_, 1);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_a_3867_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3873_ = v_a_3867_;
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_tail_3871_);
lean_inc(v_head_3870_);
lean_dec(v_a_3867_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___f_3875_; lean_object* v___x_3877_; 
v___f_3875_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3875_, 0, v_head_3870_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v_a_3868_);
lean_ctor_set(v___x_3873_, 0, v___f_3875_);
v___x_3877_ = v___x_3873_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___f_3875_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_a_3868_);
v___x_3877_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
v_a_3867_ = v_tail_3871_;
v_a_3868_ = v___x_3877_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3883_ = l_Lean_stringToMessageData(v___x_3882_);
return v___x_3883_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3886_ = l_String_toRawSubstring_x27(v___x_3885_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3891_ = l_String_toRawSubstring_x27(v___x_3890_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3896_ = l_String_toRawSubstring_x27(v___x_3895_);
return v___x_3896_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3901_ = l_String_toRawSubstring_x27(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3933_, uint8_t v_star_3934_, lean_object* v_add_3935_, lean_object* v_remove_3936_, lean_object* v_use_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; 
v___x_3966_ = lean_box(v_noDefaults_3933_);
v___x_3967_ = lean_box(v_star_3934_);
lean_inc(v_remove_3936_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3968_, 0, v_remove_3936_);
lean_closure_set(v___f_3968_, 1, v___x_3966_);
lean_closure_set(v___f_3968_, 2, v___x_3967_);
if (v_star_3934_ == 0)
{
v___y_3985_ = v_a_3938_;
v___y_3986_ = v_a_3939_;
v___y_3987_ = v_a_3940_;
v___y_3988_ = v_a_3941_;
goto v___jp_3984_;
}
else
{
if (v_noDefaults_3933_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v___f_3968_);
lean_dec_ref(v_use_3937_);
lean_dec(v_remove_3936_);
lean_dec(v_add_3935_);
v___x_4047_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4048_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4047_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
else
{
v___y_3985_ = v_a_3938_;
v___y_3986_ = v_a_3939_;
v___y_3987_ = v_a_3940_;
v___y_3988_ = v_a_3941_;
goto v___jp_3984_;
}
}
v___jp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___y_3945_);
lean_ctor_set(v___x_3946_, 1, v___y_3944_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
v___jp_3948_:
{
uint8_t v___x_3955_; 
v___x_3955_ = l_List_isEmpty___redArg(v_remove_3936_);
lean_dec(v_remove_3936_);
if (v___x_3955_ == 0)
{
if (v_noDefaults_3933_ == 0)
{
v___y_3944_ = v___y_3951_;
v___y_3945_ = v___y_3954_;
goto v___jp_3943_;
}
else
{
if (v_star_3934_ == 0)
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3951_);
v___x_3956_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3957_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3956_, v___y_3953_, v___y_3952_, v___y_3950_, v___y_3949_);
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
else
{
v___y_3944_ = v___y_3951_;
v___y_3945_ = v___y_3954_;
goto v___jp_3943_;
}
}
}
else
{
v___y_3944_ = v___y_3951_;
v___y_3945_ = v___y_3954_;
goto v___jp_3943_;
}
}
v___jp_3969_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_array_to_list(v___y_3976_);
lean_inc(v___y_3975_);
v___x_3978_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3977_, v___y_3975_);
if (v_noDefaults_3933_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3935_, v___y_3975_);
v___x_3980_ = l_List_appendTR___redArg(v___x_3979_, v___x_3978_);
v___x_3981_ = l_List_appendTR___redArg(v___x_3980_, v___y_3972_);
v___y_3949_ = v___y_3971_;
v___y_3950_ = v___y_3970_;
v___y_3951_ = v___f_3968_;
v___y_3952_ = v___y_3973_;
v___y_3953_ = v___y_3974_;
v___y_3954_ = v___x_3981_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_dec(v___y_3972_);
v___x_3982_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3935_, v___y_3975_);
v___x_3983_ = l_List_appendTR___redArg(v___x_3982_, v___x_3978_);
v___y_3949_ = v___y_3971_;
v___y_3950_ = v___y_3970_;
v___y_3951_ = v___f_3968_;
v___y_3952_ = v___y_3973_;
v___y_3953_ = v___y_3974_;
v___y_3954_ = v___x_3983_;
goto v___jp_3948_;
}
}
v___jp_3984_:
{
lean_object* v_ref_3989_; lean_object* v_quotContext_3990_; lean_object* v_currMacroScope_3991_; lean_object* v___x_3992_; lean_object* v_a_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v_a_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; size_t v_sz_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
v_ref_3989_ = lean_ctor_get(v___y_3987_, 5);
v_quotContext_3990_ = lean_ctor_get(v___y_3987_, 10);
v_currMacroScope_3991_ = lean_ctor_get(v___y_3987_, 11);
v___x_3992_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_a_3993_);
lean_dec_ref(v___x_3992_);
v___x_3994_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3995_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref(v___x_3995_);
v___x_3997_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3991_, 2);
lean_inc_n(v_quotContext_3990_, 2);
v___x_3998_ = l_Lean_addMacroScope(v_quotContext_3990_, v___x_3997_, v_currMacroScope_3991_);
v___x_3999_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4000_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v___x_4002_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4003_ = l_Lean_addMacroScope(v_quotContext_3990_, v___x_4002_, v_currMacroScope_3991_);
v___x_4004_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4005_ = lean_array_size(v_use_3937_);
v___x_4006_ = ((size_t)0ULL);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4005_, v___x_4006_, v_use_3937_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v___x_4009_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3991_, 2);
lean_inc_n(v_quotContext_3990_, 2);
v___x_4010_ = l_Lean_addMacroScope(v_quotContext_3990_, v___x_4009_, v_currMacroScope_3991_);
v___x_4011_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4012_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4013_ = l_Lean_addMacroScope(v_quotContext_3990_, v___x_4012_, v_currMacroScope_3991_);
v___x_4014_ = 0;
v___x_4015_ = l_Lean_SourceInfo_fromRef(v_ref_3989_, v___x_4014_);
v___x_4016_ = lean_box(0);
v___x_4017_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4018_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4015_);
lean_ctor_set(v___x_4018_, 1, v___x_3994_);
lean_ctor_set(v___x_4018_, 2, v___x_3998_);
lean_ctor_set(v___x_4018_, 3, v___x_4017_);
v___x_4019_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4020_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4020_, 0, v_a_3993_);
lean_ctor_set(v___x_4020_, 1, v___x_3999_);
lean_ctor_set(v___x_4020_, 2, v___x_4003_);
lean_ctor_set(v___x_4020_, 3, v___x_4019_);
v___x_4021_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4022_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4022_, 0, v_a_3996_);
lean_ctor_set(v___x_4022_, 1, v___x_4004_);
lean_ctor_set(v___x_4022_, 2, v___x_4010_);
lean_ctor_set(v___x_4022_, 3, v___x_4021_);
v___x_4023_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4024_, 0, v_a_4001_);
lean_ctor_set(v___x_4024_, 1, v___x_4011_);
lean_ctor_set(v___x_4024_, 2, v___x_4013_);
lean_ctor_set(v___x_4024_, 3, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v___x_4016_);
v___x_4026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4022_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4020_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4018_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4028_, v___x_4016_);
v___x_4030_ = lean_unsigned_to_nat(0u);
v___x_4031_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4032_ = lean_array_get_size(v_a_4008_);
v___x_4033_ = lean_nat_dec_lt(v___x_4030_, v___x_4032_);
if (v___x_4033_ == 0)
{
lean_dec(v_a_4008_);
v___y_3970_ = v___y_3987_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___x_4029_;
v___y_3973_ = v___y_3986_;
v___y_3974_ = v___y_3985_;
v___y_3975_ = v___x_4016_;
v___y_3976_ = v___x_4031_;
goto v___jp_3969_;
}
else
{
uint8_t v___x_4034_; 
v___x_4034_ = lean_nat_dec_le(v___x_4032_, v___x_4032_);
if (v___x_4034_ == 0)
{
if (v___x_4033_ == 0)
{
lean_dec(v_a_4008_);
v___y_3970_ = v___y_3987_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___x_4029_;
v___y_3973_ = v___y_3986_;
v___y_3974_ = v___y_3985_;
v___y_3975_ = v___x_4016_;
v___y_3976_ = v___x_4031_;
goto v___jp_3969_;
}
else
{
size_t v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_usize_of_nat(v___x_4032_);
v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4008_, v___x_4006_, v___x_4035_, v___x_4031_);
lean_dec(v_a_4008_);
v___y_3970_ = v___y_3987_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___x_4029_;
v___y_3973_ = v___y_3986_;
v___y_3974_ = v___y_3985_;
v___y_3975_ = v___x_4016_;
v___y_3976_ = v___x_4036_;
goto v___jp_3969_;
}
}
else
{
size_t v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_usize_of_nat(v___x_4032_);
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4008_, v___x_4006_, v___x_4037_, v___x_4031_);
lean_dec(v_a_4008_);
v___y_3970_ = v___y_3987_;
v___y_3971_ = v___y_3988_;
v___y_3972_ = v___x_4029_;
v___y_3973_ = v___y_3986_;
v___y_3974_ = v___y_3985_;
v___y_3975_ = v___x_4016_;
v___y_3976_ = v___x_4038_;
goto v___jp_3969_;
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v___x_4003_);
lean_dec(v_a_4001_);
lean_dec(v___x_3998_);
lean_dec(v_a_3996_);
lean_dec(v_a_3993_);
lean_dec_ref(v___f_3968_);
lean_dec(v_remove_3936_);
lean_dec(v_add_3935_);
v_a_4039_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4007_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4007_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4057_, lean_object* v_star_4058_, lean_object* v_add_4059_, lean_object* v_remove_4060_, lean_object* v_use_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
uint8_t v_noDefaults_boxed_4067_; uint8_t v_star_boxed_4068_; lean_object* v_res_4069_; 
v_noDefaults_boxed_4067_ = lean_unbox(v_noDefaults_4057_);
v_star_boxed_4068_ = lean_unbox(v_star_4058_);
v_res_4069_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4067_, v_star_boxed_4068_, v_add_4059_, v_remove_4060_, v_use_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4070_, size_t v_i_4071_, lean_object* v_bs_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4070_, v_i_4071_, v_bs_4072_, v___y_4075_, v___y_4076_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4079_, lean_object* v_i_4080_, lean_object* v_bs_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
size_t v_sz_boxed_4087_; size_t v_i_boxed_4088_; lean_object* v_res_4089_; 
v_sz_boxed_4087_ = lean_unbox_usize(v_sz_4079_);
lean_dec(v_sz_4079_);
v_i_boxed_4088_ = lean_unbox_usize(v_i_4080_);
lean_dec(v_i_4080_);
v_res_4089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4087_, v_i_boxed_4088_, v_bs_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4089_;
}
}
lean_object* runtime_initialize_Init_Data_Sum(uint8_t builtin);
lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Sum(uint8_t builtin);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_SolveByElim(builtin);
}
#ifdef __cplusplus
}
#endif
